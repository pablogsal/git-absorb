//! `--rewrite`: put staged changes straight into the commits that own the
//! changed lines, instead of creating fixup commits for a later rebase.

use anyhow::{anyhow, Result};
use std::path::Path;

use crate::weave::Weave;
use crate::{announce, owned, Announcement};

/// The new content of some files of one commit, and whether any staged
/// change was absorbed into that commit.
type Plan<'a> = (Vec<(&'a [u8], Vec<u8>)>, bool);

/// Returns how many patches are not modifications, and how many hunks belong
/// to no commit of the stack. Moves `head_tree` along with HEAD. `stack` is
/// ordered from the newest commit to the oldest.
pub fn run<'r>(
    repo: &'r git2::Repository,
    stack: &[(git2::Commit, owned::Diff)],
    index: &owned::Diff,
    head_tree: &mut git2::Tree<'r>,
    dry_run: bool,
    logger: &slog::Logger,
) -> Result<(usize, usize)> {
    // a signed commit cannot be rewritten, and neither can one whose parent
    // a shallow clone hides: the stack ends above the newest of those
    let fixed = |(commit, _): &(git2::Commit, owned::Diff)| {
        let shallow = commit.parent_count() == 0 && commit.header_field_bytes("parent").is_ok();
        shallow || commit.header_field_bytes("gpgsig").is_ok()
    };
    let stack = &stack[..stack.iter().position(fixed).unwrap_or(stack.len())];

    let (mut non_modified, mut without_target, mut ambiguous) = (0, 0, 0);
    // oldest commit first
    let mut plan = vec![Plan::default(); stack.len()];
    for patch in index.iter() {
        if patch.status != git2::Delta::Modified {
            non_modified += 1;
        } else if let Some(unabsorbed) = absorb_file(repo, stack, patch, &mut plan)? {
            without_target += unabsorbed.0;
            ambiguous += unabsorbed.1;
        } else {
            // a file whose history cannot be followed line by line
            ambiguous += 1;
        }
    }
    if ambiguous > 0 {
        announce(logger, Announcement::FileModificationsWithoutSingleOwner);
    }

    // every commit from the oldest one that changes has to be written again
    let Some(first) = plan.iter().position(|(files, _)| !files.is_empty()) else {
        return Ok((non_modified, without_target));
    };
    let commits = stack.iter().rev().map(|(commit, _)| commit).zip(&plan);
    // ask git for the committer, so that the environment and the config are
    // honoured as they are for any other commit
    let mut git = std::process::Command::new("git");
    let ident = git.arg("--git-dir").arg(repo.path());
    let ident = ident.args(["var", "GIT_COMMITTER_IDENT"]).output()?;
    if !ident.status.success() {
        return Err(anyhow!("{}", String::from_utf8_lossy(&ident.stderr)));
    }
    let stamp = [b"committer ", &ident.stdout[..]].concat();

    let (mut parent, mut rewrote) = (None, Vec::new());
    for (commit, (files, absorbed)) in commits.skip(first) {
        if dry_run {
            if *absorbed {
                announce(logger, Announcement::WouldHaveRewritten(commit));
            }
            continue;
        }
        let tree = commit.tree()?;
        let mut update = git2::build::TreeUpdateBuilder::new();
        for (path, content) in files {
            let mode = match file(&tree, path).map(|entry| entry.filemode()) {
                Some(0o100755) => git2::FileMode::BlobExecutable,
                Some(0o100664) => git2::FileMode::BlobGroupWritable,
                Some(_) => git2::FileMode::Blob,
                None => return Err(anyhow!("{} has no file to rewrite", commit.id())),
            };
            update.upsert(*path, repo.blob(content)?, mode);
        }
        let tree = update.create_updated(repo, &tree)?;

        // only the tree, the parent and the committer change: the author, the
        // message and any other header are kept byte for byte
        let mut raw = Vec::new();
        for line in commit.raw_header_bytes().split_inclusive(|&b| b == b'\n') {
            match (line.split(|&b| b == b' ').next(), parent) {
                (Some(b"tree"), _) => raw.extend(format!("tree {tree}\n").bytes()),
                (Some(b"parent"), Some(parent)) => raw.extend(format!("parent {parent}\n").bytes()),
                (Some(b"committer"), _) => raw.extend_from_slice(&stamp),
                _ => raw.extend_from_slice(line),
            }
        }
        raw.push(b'\n');
        raw.extend_from_slice(commit.message_raw_bytes());
        let new = repo.odb()?.write(git2::ObjectType::Commit, &raw)?;
        rewrote.extend(absorbed.then_some((commit, new)));
        parent = Some(new);
    }

    if let Some(new_head) = parent {
        let head = repo.head()?;
        let name = head.name().ok_or_else(|| anyhow!("HEAD is not utf8"))?;
        // fails, without changing anything, if HEAD moved in the meantime
        repo.reference_matching(name, new_head, true, stack[0].0.id(), "absorb: rewrite")?;
        *head_tree = repo.find_commit(new_head)?.tree()?;
    }
    for (commit, new) in rewrote {
        announce(logger, Announcement::Rewrote(commit, new));
    }
    Ok((non_modified, without_target))
}

/// The regular file at `path`, if there is one.
fn file(tree: &git2::Tree, path: &[u8]) -> Option<git2::TreeEntry<'static>> {
    let entry = tree.get_path(Path::new(std::str::from_utf8(path).ok()?));
    entry
        .ok()
        .filter(|entry| entry.filemode() & 0o170000 == 0o100000)
}

/// Add to `plan` the new content of the file in each commit where it
/// changes. Returns how many hunks belong to no commit of the stack and how
/// many do not clearly belong to one, or None if the file cannot be absorbed
/// into at all.
fn absorb_file<'a>(
    repo: &git2::Repository,
    stack: &[(git2::Commit, owned::Diff)],
    patch: &'a owned::Patch,
    plan: &mut [Plan<'a>],
) -> Result<Option<(usize, usize)>> {
    let path = &patch.new_path[..];
    let blob = |tree: git2::Tree| file(&tree, path).map(|entry| repo.find_blob(entry.id()));
    let Some((oldest, _)) = stack.last() else {
        return Ok(Some((patch.hunks.len(), 0)));
    };
    let base = match oldest.parents().next() {
        Some(parent) => blob(parent.tree()?).transpose()?,
        None => None,
    };
    let mut weave = Weave::new(base.as_ref().map_or(&[], |blob| blob.content()));

    // replay the stack, and insist that every commit reads back exactly
    for (n, (commit, diff)) in stack.iter().rev().enumerate() {
        let rev = 2 * n + 1;
        let hunks = diff.by_new(path).map_or(&[][..], |patch| &patch.hunks);
        let file = blob(commit.tree()?).transpose()?;
        let content = file.as_ref().map_or(&[][..], |blob| blob.content());
        if weave.commit(rev, hunks).is_none() || weave.text(rev).as_deref() != Some(content) {
            return Ok(None);
        }
    }

    let head = 2 * stack.len() - 1;
    let Some((edits, without_target, ambiguous)) = weave.attribute(head, &patch.hunks) else {
        return Ok(None);
    };
    weave.apply(head, &edits);

    // the file changes in the oldest commit that absorbs, and from there on
    let first = edits.iter().map(|edit| edit.rev / 2 - 1).min();
    let changed = first.unwrap_or(stack.len())..stack.len();
    let texts: Option<Vec<_>> = changed.clone().map(|n| weave.text(2 * n + 2)).collect();
    let Some(texts) = texts else {
        return Ok(None);
    };
    for (n, after) in changed.zip(texts) {
        plan[n].0.push((path, after));
    }
    for edit in edits {
        plan[edit.rev / 2 - 1].1 = true;
    }
    Ok(Some((without_target, ambiguous)))
}
