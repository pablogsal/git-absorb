//! Line ownership for `--rewrite`.
//!
//! A weave holds every line that one file ever had across the stack, in file
//! order. Each line records the revision that added it and the revision that
//! removed it, so any revision can be read back out, and editing an old
//! revision shows up in every later one without anything being rebased.

use crate::owned;

/// The base is 0. The n-th oldest commit of the stack (counting from 1) is
/// `2n - 1`, and that same commit after absorbing is `2n`.
pub type Rev = usize;
const BASE: Rev = 0;
const LIVE: Rev = usize::MAX;

struct Line<'a> {
    data: &'a [u8],
    born: Rev,
    died: Rev,
}

/// Replace lines `a1..a2` of the newest revision with `new`, as of `rev`.
pub struct Edit<'a> {
    pub rev: Rev,
    pub a1: usize,
    pub a2: usize,
    pub new: &'a [Vec<u8>],
}

pub struct Weave<'a> {
    lines: Vec<Line<'a>>,
}

/// The hunks of a diff of a file of `len` lines, as edits. Fails unless they
/// are in order, with an unchanged line between any two of them: everything
/// below relies on that.
fn edits(hunks: &[owned::Hunk], len: usize, rev: Rev) -> Option<Vec<Edit<'_>>> {
    let mut edits = Vec::with_capacity(hunks.len());
    let mut floor = 0;
    for hunk in hunks {
        let removed = hunk.removed.lines.len();
        // an empty block starts at the line that it follows
        let a1 = hunk.removed.start.checked_sub((removed > 0) as usize)?;
        let (a2, new) = (a1 + removed, &hunk.added.lines[..]);
        (floor <= a1 && a2 <= len).then_some(())?;
        floor = a2 + 1;
        edits.push(Edit { rev, a1, a2, new });
    }
    Some(edits)
}

impl<'a> Weave<'a> {
    pub fn new(base: &'a [u8]) -> Self {
        let (born, died) = (BASE, LIVE);
        let lines = base.split_inclusive(|&b| b == b'\n');
        let lines = lines.map(|data| Line { data, born, died }).collect();
        Weave { lines }
    }

    /// The lines of `rev`, with their positions in the weave.
    fn at(&self, rev: Rev) -> impl Iterator<Item = (usize, &Line<'a>)> {
        let lines = self.lines.iter().enumerate();
        lines.filter(move |(_, line)| line.born <= rev && rev < line.died)
    }

    /// The content of `rev`, unless it is not a well formed text file: only
    /// the last line of a file may lack its newline.
    pub fn text(&self, rev: Rev) -> Option<Vec<u8>> {
        let mut text = Vec::with_capacity(self.at(rev).map(|(_, line)| line.data.len()).sum());
        for (_, line) in self.at(rev) {
            if text.last().is_some_and(|&last| last != b'\n') {
                return None;
            }
            text.extend_from_slice(line.data);
        }
        Some(text)
    }

    /// Apply `edits`, which are sorted and address the lines of `rev`. New
    /// lines go right before the line they displace.
    pub fn apply(&mut self, rev: Rev, edits: &[Edit<'a>]) {
        let slots: Vec<_> = self.at(rev).map(|(slot, _)| slot).collect();
        for edit in edits {
            for &slot in &slots[edit.a1..edit.a2] {
                self.lines[slot].died = edit.rev;
            }
        }
        let end = self.lines.len();
        let added: usize = edits.iter().map(|edit| edit.new.len()).sum();
        let old = std::mem::replace(&mut self.lines, Vec::with_capacity(end + added));
        let mut edits = edits.iter().peekable();
        for (slot, line) in old.into_iter().map(Some).chain([None]).enumerate() {
            let here = |edit: &&Edit| slots.get(edit.a1).copied().unwrap_or(end) == slot;
            while let Some(&Edit { rev: born, new, .. }) = edits.next_if(here) {
                let died = LIVE;
                let new = new.iter().map(|data| Line { data, born, died });
                self.lines.extend(new);
            }
            self.lines.extend(line);
        }
    }

    /// Record the hunks of the next commit, `rev`. Fails if they do not fit.
    pub fn commit(&mut self, rev: Rev, hunks: &'a [owned::Hunk]) -> Option<()> {
        let edits = edits(hunks, self.at(rev).count(), rev)?;
        self.apply(rev, &edits);
        Some(())
    }

    /// Decide which commit each staged hunk belongs to. `head` is the newest
    /// commit, which the hunks are relative to. Returns the edits to `apply`,
    /// then how many hunks belong to no commit of the stack, then how many
    /// do not clearly belong to one.
    ///
    /// A change is only absorbed when it means the same thing in every commit
    /// that it will be written into:
    ///
    /// - replaced lines must all come from one commit of the stack, and must
    ///   have been next to each other ever since
    /// - added lines go with their neighbours, if those come from one commit
    ///   of the stack and have been next to each other ever since
    /// - deleted lines each leave the commit that they came from
    pub fn attribute(
        &self,
        head: Rev,
        hunks: &'a [owned::Hunk],
    ) -> Option<(Vec<Edit<'a>>, usize, usize)> {
        let slots: Vec<_> = self.at(head).map(|(slot, _)| slot).collect();
        let owner = |line: usize| self.lines[slots[line]].born;
        // whatever sits between these lines was already gone by `rev`, so it
        // is in none of the commits that are about to change
        let together = |from: usize, to: usize, rev: Rev| {
            let between = &self.lines[from..to];
            between.iter().all(|l| l.died == LIVE || l.died <= rev)
        };

        let (mut absorbed, mut without_target, mut ambiguous) = (Vec::new(), 0, 0);
        for Edit { a1, a2, new, .. } in edits(hunks, slots.len(), head)? {
            let (mut owners, from, to): (Vec<Rev>, _, _) = if a1 < a2 {
                let owners = (a1..a2).map(owner).collect();
                (owners, slots[a1], slots[a2 - 1] + 1)
            } else {
                let before = a1.checked_sub(1);
                let after = Some(a1).filter(|&line| line < slots.len());
                let near = [before, after].into_iter().flatten();
                (
                    near.map(owner).filter(|&rev| rev != BASE).collect(),
                    before.map_or(0, |line| slots[line] + 1),
                    after.map_or(self.lines.len(), |line| slots[line]),
                )
            };
            owners.sort_unstable();
            owners.dedup();

            match owners[..] {
                [rev] if rev != BASE && together(from, to, rev) => {
                    let rev = rev + 1;
                    absorbed.push(Edit { rev, a1, a2, new });
                }
                _ if a1 < a2 && new.is_empty() => {
                    let mine = (a1..a2).filter(|&line| owner(line) != BASE);
                    absorbed.extend(mine.map(|line| Edit {
                        rev: owner(line) + 1,
                        a1: line,
                        a2: line + 1,
                        new,
                    }));
                    without_target += owners.contains(&BASE) as usize;
                }
                [] | [BASE] => without_target += 1,
                _ => ambiguous += 1,
            }
        }
        Some((absorbed, without_target, ambiguous))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::rc::Rc;
    use std::sync::atomic::{AtomicUsize, Ordering};

    type Text = Vec<Vec<u8>>;
    /// Replace lines `a1..a2` with a number of new lines.
    type Hunk = (usize, usize, usize);

    fn text(weave: &Weave, rev: Rev) -> Text {
        let text = weave.text(rev).unwrap();
        text.split_inclusive(|&b| b == b'\n')
            .map(Vec::from)
            .collect()
    }

    /// `count` lines that are unlike any other line.
    fn fresh(count: usize) -> Text {
        static NEXT: AtomicUsize = AtomicUsize::new(0);
        let line = |_| format!("{}\n", NEXT.fetch_add(1, Ordering::Relaxed)).into();
        (0..count).map(line).collect()
    }

    fn hunks(diff: &[Hunk]) -> Vec<owned::Hunk> {
        let block = |start, lines| owned::Block {
            start,
            lines: Rc::new(lines),
        };
        let hunk = |&(a1, a2, added): &Hunk| owned::Hunk {
            added: block(0, fresh(added)),
            removed: block(a1 + (a1 < a2) as usize, vec![Vec::new(); a2 - a1]),
        };
        diff.iter().map(hunk).collect()
    }

    /// What `edit` means for the text of one commit, worked out from that
    /// text alone: the replaced lines must be together in it, and added lines
    /// must find the two lines they were put between next to each other.
    fn replay(mut text: Text, head: &Text, edit: &Edit) -> Text {
        let at = if edit.a1 < edit.a2 {
            let block = &head[edit.a1..edit.a2];
            let at = text.iter().position(|line| *line == block[0]).unwrap();
            assert_eq!(&text[at..at + block.len()], block);
            at
        } else {
            let before = edit.a1.checked_sub(1).map(|line| &head[line]);
            let at = before.map_or(0, |line| text.iter().position(|l| l == line).unwrap() + 1);
            assert_eq!(text.get(at), head.get(edit.a1));
            at
        };
        text.splice(at..at + (edit.a2 - edit.a1), edit.new.iter().cloned());
        text
    }

    /// Build a stack with one commit per entry of `commits` on a base of
    /// `base` lines, absorb `staged`, and check the properties that the TLA+
    /// model of this module is checked for. Returns how much was absorbed.
    fn check(base: usize, commits: &[Vec<Hunk>], staged: &[Hunk]) -> usize {
        let base = fresh(base);
        let content = base.concat();
        let commits: Vec<_> = commits.iter().map(|diff| hunks(diff)).collect();
        let staged = hunks(staged);

        let mut weave = Weave::new(&content);
        let mut old = Vec::new();
        for (n, hunks) in commits.iter().enumerate() {
            weave.commit(2 * n + 1, hunks).unwrap();
            old.push(text(&weave, 2 * n + 1));
        }
        let (head, rev) = (old.last().unwrap().clone(), 2 * old.len() - 1);
        let (absorbed, without_target, ambiguous) = weave.attribute(rev, &staged).unwrap();
        weave.apply(rev, &absorbed);

        // an edit only goes into the commit that added the lines it touches
        let born = |line: &Vec<u8>| match old.iter().position(|text| text.contains(line)) {
            _ if base.contains(line) => BASE,
            first => 2 * first.unwrap() + 1,
        };
        for edit in &absorbed {
            // the lines replaced, or else the two lines added between
            let added = (edit.a1 == edit.a2) as usize;
            let near = edit.a1.saturating_sub(added)..head.len().min(edit.a2 + added);
            let mut owners: Vec<_> = head[near].iter().map(born).collect();
            owners.retain(|&rev| added == 0 || rev != BASE);
            assert!(!owners.is_empty() && owners.iter().all(|&rev| rev + 1 == edit.rev));
        }
        // the base never changes
        assert_eq!(text(&weave, BASE), base);
        // every commit is its old text with exactly the edits that were
        // attributed to it or to an older commit
        for (n, old) in old.iter().enumerate() {
            let mine = absorbed.iter().filter(|edit| edit.rev <= 2 * n + 2);
            let expected = mine.fold(old.clone(), |text, edit| replay(text, &head, edit));
            assert_eq!(text(&weave, 2 * n + 2), expected);
        }
        // if everything was absorbed, the new head is what was staged
        if without_target + ambiguous == 0 {
            let mut index = head;
            for edit in edits(&staged, index.len(), rev).unwrap().iter().rev() {
                index.splice(edit.a1..edit.a2, edit.new.iter().cloned());
            }
            assert_eq!(text(&weave, rev + 1), index);
        }
        absorbed.len()
    }

    /// The length of a `len` line file after `diff`.
    fn resized(len: usize, diff: &[Hunk]) -> usize {
        let resize = |len, &(a1, a2, added): &Hunk| len + a1 + added - a2;
        diff.iter().fold(len, resize)
    }

    /// Every way for a diff to change a file of `len` lines with at most two
    /// hunks that add at most two lines each, without growing past `limit`.
    fn diffs(len: usize, limit: usize) -> Vec<Vec<Hunk>> {
        let mut diffs = vec![Vec::new()];
        for first in 0..2 {
            for diff in diffs.clone().iter().filter(|diff| diff.len() == first) {
                let floor = diff.last().map_or(0, |&(_, a2, _)| a2 + 1);
                for a1 in floor..=len {
                    for a2 in a1..=len {
                        for added in ((a1 == a2) as usize)..=2 {
                            let diff = [&diff[..], &[(a1, a2, added)]].concat();
                            if resized(len, &diff) <= limit {
                                diffs.push(diff);
                            }
                        }
                    }
                }
            }
        }
        diffs
    }

    /// Check every stack of up to `depth` commits on a base of up to two
    /// lines, with files of up to `limit` lines, and every staged edit.
    fn check_small_stacks(depth: usize, limit: usize) {
        fn stacks(
            base: usize,
            commits: &mut Vec<Vec<Hunk>>,
            len: usize,
            bounds: (usize, usize),
        ) -> usize {
            let staged = diffs(len, usize::MAX);
            let staged = staged.iter().filter(|_| !commits.is_empty());
            let mut absorbed: usize = staged.map(|staged| check(base, commits, staged)).sum();
            for diff in diffs(len, bounds.1) {
                if commits.len() < bounds.0 {
                    let len = resized(len, &diff);
                    commits.push(diff);
                    absorbed += stacks(base, commits, len, bounds);
                    commits.pop();
                }
            }
            absorbed
        }
        let absorbed = (0..=2).map(|base| stacks(base, &mut Vec::new(), base, (depth, limit)));
        assert!(absorbed.sum::<usize>() > 0);
    }

    #[test]
    fn absorbed_edits_replay_in_every_small_stack() {
        check_small_stacks(3, 2);
        // hunks that touch are not what a diff gives
        assert!(edits(&hunks(&[(0, 1, 1), (1, 2, 1)]), 2, 1).is_none());
    }
}
