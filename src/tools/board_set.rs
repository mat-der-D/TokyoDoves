use crate::prelude::{Board, BoardBuilder};
use std::collections::{HashMap, HashSet};

#[derive(Debug, Clone, Default)]
pub struct BoardSet {
    top2bottoms: HashMap<u32, HashSet<u32>>,
}

impl FromIterator<u64> for BoardSet {
    fn from_iter<T: IntoIterator<Item = u64>>(iter: T) -> Self {
        let mut set = Self::new();
        for item in iter {
            set.insert(item);
        }
        set
    }
}

impl IntoIterator for BoardSet {
    type Item = u64;
    type IntoIter = IntoIter;
    fn into_iter(self) -> Self::IntoIter {
        Self::IntoIter::new(self)
    }
}

impl BoardSet {
    fn new() -> Self {
        Self::default()
    }

    fn trim(&mut self) {
        self.top2bottoms.retain(|_, v| !v.is_empty());
    }

    pub fn iter(&self) -> Iter {
        Iter::new(self)
    }

    pub fn board_iter(&self) -> BoardIter {
        BoardIter::new(self)
    }

    pub fn board_into_iter(self) -> BoardIntoIter {
        BoardIntoIter::new(self)
    }

    fn u64_to_u32_u32(n: u64) -> (u32, u32) {
        ((n >> 32) as u32, n as u32)
    }

    fn u32_u32_to_u64(top: u32, bottom: u32) -> u64 {
        ((top as u64) << 32) | (bottom as u64)
    }

    pub fn len(&self) -> usize {
        self.top2bottoms.values().map(|s| s.len()).sum()
    }

    pub fn is_empty(&self) -> bool {
        self.top2bottoms.values().all(|s| s.is_empty())
    }

    pub fn drain(&mut self) -> Drain {
        Drain::new(self)
    }

    pub fn board_drain(&mut self) -> BoardDrain {
        BoardDrain::new(self)
    }

    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&u64) -> bool,
    {
        for (&top, bottoms) in self.top2bottoms.iter_mut() {
            bottoms.retain(|&b| {
                let hash = BoardSet::u32_u32_to_u64(top, b);
                f(&hash)
            });
        }
        self.trim();
    }

    pub fn clear(&mut self) {
        self.top2bottoms.clear()
    }

    pub fn difference<'a>(&'a self, other: &'a BoardSet) -> Difference<'a> {
        Difference::new(self, other)
    }

    pub fn board_difference<'a>(&'a self, other: &'a BoardSet) -> BoardDifference<'a> {
        BoardDifference::new(self, other)
    }

    pub fn symmetric_difference<'a>(&'a self, other: &'a BoardSet) -> SymmetricDifference<'a> {
        SymmetricDifference::new(self, other)
    }

    pub fn board_symmetric_difference<'a>(
        &'a self,
        other: &'a BoardSet,
    ) -> BoardSymmetricDifference<'a> {
        BoardSymmetricDifference::new(self, other)
    }

    pub fn intersection<'a>(&'a self, other: &'a BoardSet) -> Intersection<'a> {
        Intersection::new(self, other)
    }

    pub fn board_intersection<'a>(&'a self, other: &'a BoardSet) -> BoardIntersection<'a> {
        BoardIntersection::new(self, other)
    }

    pub fn union<'a>(&'a self, other: &'a BoardSet) -> Union<'a> {
        Union::new(self, other)
    }

    pub fn board_union<'a>(&'a self, other: &'a BoardSet) -> BoardUnion<'a> {
        BoardUnion::new(self, other)
    }

    pub fn contains(&self, hash: &u64) -> bool {
        let (k, v) = Self::u64_to_u32_u32(*hash);
        self.top2bottoms.get(&k).map_or(false, |x| x.contains(&v))
    }

    pub fn is_disjoint(&self, other: &BoardSet) -> bool {
        if self.len() <= other.len() {
            self.iter().all(|v| !other.contains(&v))
        } else {
            other.iter().all(|v| !self.contains(&v))
        }
    }

    pub fn is_subset(&self, other: &BoardSet) -> bool {
        if self.len() <= other.len() {
            self.iter().all(|v| other.contains(&v))
        } else {
            false
        }
    }

    pub fn is_superset(&self, other: &BoardSet) -> bool {
        other.is_subset(self)
    }

    pub fn insert(&mut self, hash: u64) {
        let (k, v) = Self::u64_to_u32_u32(hash);
        self.top2bottoms
            .entry(k)
            .or_insert_with(HashSet::new)
            .insert(v);
    }

    pub fn insert_board(&mut self, board: Board) {
        self.insert(board.to_u64())
    }

    pub fn remove(&mut self, hash: &u64) -> bool {
        let (k, v) = Self::u64_to_u32_u32(*hash);
        let Some(set) = self.top2bottoms.get_mut(&k) else {
            return false;
        };
        let removed = set.remove(&v);
        if set.is_empty() {
            self.top2bottoms.remove(&k);
        }
        removed
    }

    pub fn remove_board(&mut self, board: &Board) -> bool {
        self.remove(&board.to_u64())
    }

    pub fn take(&mut self, hash: &u64) -> Option<u64> {
        let (k, v) = Self::u64_to_u32_u32(*hash);
        let set = self.top2bottoms.get_mut(&k)?;
        let taken = set.take(&v).map(|bottom| Self::u32_u32_to_u64(k, bottom));
        if set.is_empty() {
            self.top2bottoms.remove(&k);
        }
        taken
    }

    pub fn take_board(&mut self, board: &Board) -> Option<Board> {
        self.take(&board.to_u64()).map(u64_to_board)
    }
}

impl std::ops::BitAnd<&BoardSet> for &BoardSet {
    type Output = BoardSet;
    fn bitand(self, rhs: &BoardSet) -> Self::Output {
        self.intersection(rhs).collect()
    }
}

impl std::ops::BitOr<&BoardSet> for &BoardSet {
    type Output = BoardSet;
    fn bitor(self, rhs: &BoardSet) -> Self::Output {
        self.union(rhs).collect()
    }
}

impl std::ops::BitXor<&BoardSet> for &BoardSet {
    type Output = BoardSet;
    fn bitxor(self, rhs: &BoardSet) -> Self::Output {
        self.symmetric_difference(rhs).collect()
    }
}

// **************************************************************
//  Iterators Returned
// **************************************************************
fn u64_to_board(hash: u64) -> Board {
    BoardBuilder::from(hash).build_unchecked()
}

type MapIter<'a> = std::collections::hash_map::Iter<'a, u32, HashSet<u32>>;
type SetIter<'a> = std::collections::hash_set::Iter<'a, u32>;

pub struct Iter<'a> {
    set: &'a BoardSet,
    state: Option<(
        MapIter<'a>, // iterator of top2bottoms
        u32,         // key of top2bottoms
        SetIter<'a>, // iterator of value of top2bottoms
    )>,
}

impl<'a> Iter<'a> {
    fn new(set: &'a BoardSet) -> Self {
        Self { set, state: None }
    }
}

impl<'a> Iterator for Iter<'a> {
    type Item = u64;
    fn next(&mut self) -> Option<Self::Item> {
        let Some((map_iter, top, set_iter)) = self.state.as_mut() else {
            let mut map_iter_raw = self.set.top2bottoms.iter();
            let (top, set) = map_iter_raw.next()?;
            self.state = Some((map_iter_raw, *top, set.iter()));
            return self.next();
        };

        let Some(bottom) = set_iter.next() else {
            let (next_top, next_set) = map_iter.next()?;
            *top = *next_top;
            *set_iter = next_set.iter();
            return self.next();
        };
        Some(BoardSet::u32_u32_to_u64(*top, *bottom))
    }
}

pub struct BoardIter<'a>(Iter<'a>);

impl<'a> BoardIter<'a> {
    fn new(set: &'a BoardSet) -> Self {
        Self(Iter::new(set))
    }
}

impl<'a> Iterator for BoardIter<'a> {
    type Item = Board;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(u64_to_board)
    }
}

type MapIntoIter = std::collections::hash_map::IntoIter<u32, HashSet<u32>>;
type SetIntoIter = std::collections::hash_set::IntoIter<u32>;

pub struct IntoIter {
    set: Option<BoardSet>,
    state: Option<(
        MapIntoIter, // iterator of set.top2bottoms
        u32,         // key of set.top2bottoms
        SetIntoIter, // iterator of value of set.top2bottoms
    )>,
}

impl IntoIter {
    fn new(set: BoardSet) -> Self {
        Self {
            set: Some(set),
            state: None,
        }
    }
}

impl Iterator for IntoIter {
    type Item = u64;
    fn next(&mut self) -> Option<Self::Item> {
        let Some((map_iter, top, set_iter)) = self.state.as_mut() else {
            let set = std::mem::replace(&mut self.set, None)?;
            let mut map_iter_raw = set.top2bottoms.into_iter();
            let (top, set) = map_iter_raw.next()?;
            self.state = Some((map_iter_raw, top, set.into_iter()));
            return self.next();
        };

        let Some(bottom) = set_iter.next() else {
            let (next_top, next_set) = map_iter.next()?;
            *top = next_top;
            *set_iter = next_set.into_iter();
            return self.next();
        };
        Some(BoardSet::u32_u32_to_u64(*top, bottom))
    }
}

pub struct BoardIntoIter(IntoIter);

impl BoardIntoIter {
    fn new(set: BoardSet) -> Self {
        Self(IntoIter::new(set))
    }
}

impl Iterator for BoardIntoIter {
    type Item = Board;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(u64_to_board)
    }
}

pub struct Drain(IntoIter);

impl Drain {
    fn new(set: &mut BoardSet) -> Self {
        let original = std::mem::replace(set, BoardSet::new());
        Self(original.into_iter())
    }
}

impl Iterator for Drain {
    type Item = u64;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }
}

pub struct BoardDrain(Drain);

impl BoardDrain {
    fn new(set: &mut BoardSet) -> Self {
        Self(Drain::new(set))
    }
}

impl Iterator for BoardDrain {
    type Item = Board;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(u64_to_board)
    }
}

pub struct Difference<'a> {
    left: Iter<'a>,
    right: &'a BoardSet,
}

impl<'a> Difference<'a> {
    fn new(left: &'a BoardSet, right: &'a BoardSet) -> Self {
        Self {
            left: left.iter(),
            right,
        }
    }
}

impl<'a> Iterator for Difference<'a> {
    type Item = u64;
    fn next(&mut self) -> Option<Self::Item> {
        let item = self.left.next()?;
        if self.right.contains(&item) {
            self.next()
        } else {
            Some(item)
        }
    }
}

pub struct BoardDifference<'a>(Difference<'a>);

impl<'a> BoardDifference<'a> {
    fn new(left: &'a BoardSet, right: &'a BoardSet) -> Self {
        Self(Difference::new(left, right))
    }
}

impl<'a> Iterator for BoardDifference<'a> {
    type Item = Board;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(u64_to_board)
    }
}

pub struct SymmetricDifference<'a> {
    left: &'a BoardSet,
    left_iter: Iter<'a>,
    right: &'a BoardSet,
    right_iter: Iter<'a>,
}

impl<'a> SymmetricDifference<'a> {
    fn new(left: &'a BoardSet, right: &'a BoardSet) -> Self {
        Self {
            left,
            left_iter: left.iter(),
            right,
            right_iter: right.iter(),
        }
    }
}

impl<'a> Iterator for SymmetricDifference<'a> {
    type Item = u64;
    fn next(&mut self) -> Option<Self::Item> {
        if let Some(item_left) = self.left_iter.next() {
            if self.right.contains(&item_left) {
                self.next()
            } else {
                Some(item_left)
            }
        } else {
            let item_right = self.right_iter.next()?;
            if self.left.contains(&item_right) {
                self.next()
            } else {
                Some(item_right)
            }
        }
    }
}

pub struct BoardSymmetricDifference<'a>(SymmetricDifference<'a>);

impl<'a> BoardSymmetricDifference<'a> {
    fn new(left: &'a BoardSet, right: &'a BoardSet) -> Self {
        Self(SymmetricDifference::new(left, right))
    }
}

impl<'a> Iterator for BoardSymmetricDifference<'a> {
    type Item = Board;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(u64_to_board)
    }
}

pub struct Intersection<'a> {
    left_iter: Iter<'a>,
    right: &'a BoardSet,
}

impl<'a> Intersection<'a> {
    fn new(left: &'a BoardSet, right: &'a BoardSet) -> Self {
        Self {
            left_iter: left.iter(),
            right,
        }
    }
}

impl<'a> Iterator for Intersection<'a> {
    type Item = u64;
    fn next(&mut self) -> Option<Self::Item> {
        let item = self.left_iter.next()?;
        if self.right.contains(&item) {
            Some(item)
        } else {
            self.next()
        }
    }
}

pub struct BoardIntersection<'a>(Intersection<'a>);

impl<'a> BoardIntersection<'a> {
    fn new(left: &'a BoardSet, right: &'a BoardSet) -> Self {
        Self(Intersection::new(left, right))
    }
}

impl<'a> Iterator for BoardIntersection<'a> {
    type Item = Board;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(u64_to_board)
    }
}

pub struct Union<'a> {
    left_iter: Iter<'a>,
    right: &'a BoardSet,
    right_iter: Iter<'a>,
}

impl<'a> Union<'a> {
    fn new(left: &'a BoardSet, right: &'a BoardSet) -> Self {
        Self {
            left_iter: left.iter(),
            right,
            right_iter: right.iter(),
        }
    }
}

impl<'a> Iterator for Union<'a> {
    type Item = u64;
    fn next(&mut self) -> Option<Self::Item> {
        let Some(item) = self.left_iter.next() else {
            return self.right_iter.next();
        };
        if self.right.contains(&item) {
            self.next()
        } else {
            Some(item)
        }
    }
}

pub struct BoardUnion<'a>(Union<'a>);

impl<'a> BoardUnion<'a> {
    fn new(left: &'a BoardSet, right: &'a BoardSet) -> Self {
        Self(Union::new(left, right))
    }
}

impl<'a> Iterator for BoardUnion<'a> {
    type Item = Board;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(u64_to_board)
    }
}
