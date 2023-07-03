use crate::prelude::{Board, BoardBuilder};
use std::collections::{HashMap, HashSet};

fn u64_to_board(hash: u64) -> Board {
    BoardBuilder::from(hash).build_unchecked()
}

#[derive(Debug, Clone, Default)]
pub struct BoardSet {
    top2bottoms: HashMap<u32, HashSet<u32>>,
}

impl FromIterator<u64> for BoardSet {
    fn from_iter<T: IntoIterator<Item = u64>>(iter: T) -> Self {
        let mut set = Self::new();
        for item in iter {
            set.insert_u64(item);
        }
        set
    }
}

impl FromIterator<Board> for BoardSet {
    fn from_iter<T: IntoIterator<Item = Board>>(iter: T) -> Self {
        Self::from_iter(iter.into_iter().map(|b| b.to_u64()))
    }
}

impl IntoIterator for BoardSet {
    type Item = Board;
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

    pub fn iter_u64(&self) -> IterU64 {
        IterU64::new(self)
    }

    pub fn into_iter_u64(self) -> IntoIterU64 {
        IntoIterU64::new(self)
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

    pub fn drain_u64(&mut self) -> DrainU64 {
        DrainU64::new(self)
    }

    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&Board) -> bool,
    {
        self.retain_u64(|&h| f(&u64_to_board(h)))
    }

    pub fn retain_u64<F>(&mut self, mut f: F)
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

    pub fn difference_u64<'a>(&'a self, other: &'a BoardSet) -> DifferenceU64<'a> {
        DifferenceU64::new(self, other)
    }

    pub fn symmetric_difference<'a>(&'a self, other: &'a BoardSet) -> SymmetricDifference<'a> {
        SymmetricDifference::new(self, other)
    }

    pub fn symmetric_difference_u64<'a>(
        &'a self,
        other: &'a BoardSet,
    ) -> SymmetricDifferenceU64<'a> {
        SymmetricDifferenceU64::new(self, other)
    }

    pub fn intersection<'a>(&'a self, other: &'a BoardSet) -> Intersection<'a> {
        Intersection::new(self, other)
    }

    pub fn intersection_u64<'a>(&'a self, other: &'a BoardSet) -> IntersectionU64<'a> {
        IntersectionU64::new(self, other)
    }

    pub fn union<'a>(&'a self, other: &'a BoardSet) -> Union<'a> {
        Union::new(self, other)
    }

    pub fn union_u64<'a>(&'a self, other: &'a BoardSet) -> UnionU64<'a> {
        UnionU64::new(self, other)
    }

    pub fn contains(&self, board: &Board) -> bool {
        self.contains_u64(&board.to_u64())
    }

    pub fn contains_u64(&self, hash: &u64) -> bool {
        let (k, v) = Self::u64_to_u32_u32(*hash);
        self.top2bottoms.get(&k).map_or(false, |x| x.contains(&v))
    }

    pub fn is_disjoint(&self, other: &BoardSet) -> bool {
        if self.len() <= other.len() {
            self.iter_u64().all(|v| !other.contains_u64(&v))
        } else {
            other.iter_u64().all(|v| !self.contains_u64(&v))
        }
    }

    pub fn is_subset(&self, other: &BoardSet) -> bool {
        if self.len() <= other.len() {
            self.iter_u64().all(|v| other.contains_u64(&v))
        } else {
            false
        }
    }

    pub fn is_superset(&self, other: &BoardSet) -> bool {
        other.is_subset(self)
    }

    pub fn insert(&mut self, board: Board) {
        self.insert_u64(board.to_u64())
    }

    pub fn insert_u64(&mut self, hash: u64) {
        let (k, v) = Self::u64_to_u32_u32(hash);
        self.top2bottoms
            .entry(k)
            .or_insert_with(HashSet::new)
            .insert(v);
    }

    pub fn remove(&mut self, board: &Board) -> bool {
        self.remove_u64(&board.to_u64())
    }

    pub fn remove_u64(&mut self, hash: &u64) -> bool {
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

    pub fn take(&mut self, board: &Board) -> Option<Board> {
        self.take_u64(&board.to_u64()).map(u64_to_board)
    }

    pub fn take_u64(&mut self, hash: &u64) -> Option<u64> {
        let (k, v) = Self::u64_to_u32_u32(*hash);
        let set = self.top2bottoms.get_mut(&k)?;
        let taken = set.take(&v).map(|bottom| Self::u32_u32_to_u64(k, bottom));
        if set.is_empty() {
            self.top2bottoms.remove(&k);
        }
        taken
    }
}

impl std::ops::BitAnd<&BoardSet> for &BoardSet {
    type Output = BoardSet;
    fn bitand(self, rhs: &BoardSet) -> Self::Output {
        self.intersection_u64(rhs).collect()
    }
}

impl std::ops::BitOr<&BoardSet> for &BoardSet {
    type Output = BoardSet;
    fn bitor(self, rhs: &BoardSet) -> Self::Output {
        self.union_u64(rhs).collect()
    }
}

impl std::ops::BitXor<&BoardSet> for &BoardSet {
    type Output = BoardSet;
    fn bitxor(self, rhs: &BoardSet) -> Self::Output {
        self.symmetric_difference_u64(rhs).collect()
    }
}

// **************************************************************
//  Iterators Returned
// **************************************************************
type MapIter<'a> = std::collections::hash_map::Iter<'a, u32, HashSet<u32>>;
type SetIter<'a> = std::collections::hash_set::Iter<'a, u32>;

pub struct IterU64<'a> {
    set: &'a BoardSet,
    state: Option<(
        MapIter<'a>, // iterator of top2bottoms
        u32,         // key of top2bottoms
        SetIter<'a>, // iterator of value of top2bottoms
    )>,
}

impl<'a> IterU64<'a> {
    fn new(set: &'a BoardSet) -> Self {
        Self { set, state: None }
    }
}

impl<'a> Iterator for IterU64<'a> {
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

pub struct Iter<'a>(IterU64<'a>);

impl<'a> Iter<'a> {
    fn new(set: &'a BoardSet) -> Self {
        Self(IterU64::new(set))
    }
}

impl<'a> Iterator for Iter<'a> {
    type Item = Board;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(u64_to_board)
    }
}

type MapIntoIter = std::collections::hash_map::IntoIter<u32, HashSet<u32>>;
type SetIntoIter = std::collections::hash_set::IntoIter<u32>;

pub struct IntoIterU64 {
    set: Option<BoardSet>,
    state: Option<(
        MapIntoIter, // iterator of set.top2bottoms
        u32,         // key of set.top2bottoms
        SetIntoIter, // iterator of value of set.top2bottoms
    )>,
}

impl IntoIterU64 {
    fn new(set: BoardSet) -> Self {
        Self {
            set: Some(set),
            state: None,
        }
    }
}

impl Iterator for IntoIterU64 {
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

pub struct IntoIter(IntoIterU64);

impl IntoIter {
    fn new(set: BoardSet) -> Self {
        Self(IntoIterU64::new(set))
    }
}

impl Iterator for IntoIter {
    type Item = Board;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(u64_to_board)
    }
}

pub struct DrainU64(IntoIterU64);

impl DrainU64 {
    fn new(set: &mut BoardSet) -> Self {
        let original = std::mem::replace(set, BoardSet::new());
        Self(original.into_iter_u64())
    }
}

impl Iterator for DrainU64 {
    type Item = u64;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }
}

pub struct Drain(DrainU64);

impl Drain {
    fn new(set: &mut BoardSet) -> Self {
        Self(DrainU64::new(set))
    }
}

impl Iterator for Drain {
    type Item = Board;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(u64_to_board)
    }
}

pub struct DifferenceU64<'a> {
    left: IterU64<'a>,
    right: &'a BoardSet,
}

impl<'a> DifferenceU64<'a> {
    fn new(left: &'a BoardSet, right: &'a BoardSet) -> Self {
        Self {
            left: left.iter_u64(),
            right,
        }
    }
}

impl<'a> Iterator for DifferenceU64<'a> {
    type Item = u64;
    fn next(&mut self) -> Option<Self::Item> {
        let item = self.left.next()?;
        if self.right.contains_u64(&item) {
            self.next()
        } else {
            Some(item)
        }
    }
}

pub struct Difference<'a>(DifferenceU64<'a>);

impl<'a> Difference<'a> {
    fn new(left: &'a BoardSet, right: &'a BoardSet) -> Self {
        Self(DifferenceU64::new(left, right))
    }
}

impl<'a> Iterator for Difference<'a> {
    type Item = Board;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(u64_to_board)
    }
}

pub struct SymmetricDifferenceU64<'a> {
    left: &'a BoardSet,
    left_iter: IterU64<'a>,
    right: &'a BoardSet,
    right_iter: IterU64<'a>,
}

impl<'a> SymmetricDifferenceU64<'a> {
    fn new(left: &'a BoardSet, right: &'a BoardSet) -> Self {
        Self {
            left,
            left_iter: left.iter_u64(),
            right,
            right_iter: right.iter_u64(),
        }
    }
}

impl<'a> Iterator for SymmetricDifferenceU64<'a> {
    type Item = u64;
    fn next(&mut self) -> Option<Self::Item> {
        if let Some(item_left) = self.left_iter.next() {
            if self.right.contains_u64(&item_left) {
                self.next()
            } else {
                Some(item_left)
            }
        } else {
            let item_right = self.right_iter.next()?;
            if self.left.contains_u64(&item_right) {
                self.next()
            } else {
                Some(item_right)
            }
        }
    }
}

pub struct SymmetricDifference<'a>(SymmetricDifferenceU64<'a>);

impl<'a> SymmetricDifference<'a> {
    fn new(left: &'a BoardSet, right: &'a BoardSet) -> Self {
        Self(SymmetricDifferenceU64::new(left, right))
    }
}

impl<'a> Iterator for SymmetricDifference<'a> {
    type Item = Board;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(u64_to_board)
    }
}

pub struct IntersectionU64<'a> {
    left_iter: IterU64<'a>,
    right: &'a BoardSet,
}

impl<'a> IntersectionU64<'a> {
    fn new(left: &'a BoardSet, right: &'a BoardSet) -> Self {
        Self {
            left_iter: left.iter_u64(),
            right,
        }
    }
}

impl<'a> Iterator for IntersectionU64<'a> {
    type Item = u64;
    fn next(&mut self) -> Option<Self::Item> {
        let item = self.left_iter.next()?;
        if self.right.contains_u64(&item) {
            Some(item)
        } else {
            self.next()
        }
    }
}

pub struct Intersection<'a>(IntersectionU64<'a>);

impl<'a> Intersection<'a> {
    fn new(left: &'a BoardSet, right: &'a BoardSet) -> Self {
        Self(IntersectionU64::new(left, right))
    }
}

impl<'a> Iterator for Intersection<'a> {
    type Item = Board;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(u64_to_board)
    }
}

pub struct UnionU64<'a> {
    left_iter: IterU64<'a>,
    right: &'a BoardSet,
    right_iter: IterU64<'a>,
}

impl<'a> UnionU64<'a> {
    fn new(left: &'a BoardSet, right: &'a BoardSet) -> Self {
        Self {
            left_iter: left.iter_u64(),
            right,
            right_iter: right.iter_u64(),
        }
    }
}

impl<'a> Iterator for UnionU64<'a> {
    type Item = u64;
    fn next(&mut self) -> Option<Self::Item> {
        let Some(item) = self.left_iter.next() else {
            return self.right_iter.next();
        };
        if self.right.contains_u64(&item) {
            self.next()
        } else {
            Some(item)
        }
    }
}

pub struct Union<'a>(UnionU64<'a>);

impl<'a> Union<'a> {
    fn new(left: &'a BoardSet, right: &'a BoardSet) -> Self {
        Self(UnionU64::new(left, right))
    }
}

impl<'a> Iterator for Union<'a> {
    type Item = Board;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(u64_to_board)
    }
}
