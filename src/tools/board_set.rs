use super::io::{Fragment, FragmentIter};
use crate::prelude::{Board, BoardBuilder};
use std::{
    collections::{HashMap, HashSet},
    io::{BufWriter, Read, Write},
};

fn u64_to_board(hash: u64) -> Board {
    BoardBuilder::from(hash).build_unchecked()
}

// ********************************************************************
//  BoardSet
// ********************************************************************
#[derive(Debug, Clone, Default)]
pub struct BoardSet {
    raw: RawBoardSet,
}

impl FromIterator<Board> for BoardSet {
    fn from_iter<T: IntoIterator<Item = Board>>(iter: T) -> Self {
        Self {
            raw: iter.into_iter().map(|b| b.to_u64()).collect(),
        }
    }
}

impl IntoIterator for BoardSet {
    type Item = Board;
    type IntoIter = IntoIter;
    fn into_iter(self) -> Self::IntoIter {
        IntoIter(RawIntoIter::new(self.raw))
    }
}

impl From<RawBoardSet> for BoardSet {
    fn from(raw: RawBoardSet) -> Self {
        Self { raw }
    }
}

impl BoardSet {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn raw(&self) -> &RawBoardSet {
        &self.raw
    }

    pub fn raw_mut(&mut self) -> &mut RawBoardSet {
        &mut self.raw
    }

    pub fn into_raw(self) -> RawBoardSet {
        self.raw
    }

    pub fn required_capacity<R>(raw_reader: R) -> HashMap<u32, usize>
    where
        R: Read,
    {
        RawBoardSet::required_capacity(raw_reader)
    }

    pub fn with_capacity(capacity: HashMap<u32, usize>) -> Self {
        Self {
            raw: RawBoardSet::with_capacity(capacity),
        }
    }

    pub fn capacity(&self) -> HashMap<u32, usize> {
        self.raw.capacity()
    }

    pub fn iter(&self) -> Iter {
        Iter(RawIter::new(&self.raw))
    }

    pub fn len(&self) -> usize {
        self.raw.len()
    }

    pub fn is_empty(&self) -> bool {
        self.raw.is_empty()
    }

    pub fn drain(&mut self) -> Drain {
        Drain(RawDrain::new(&mut self.raw))
    }

    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&Board) -> bool,
    {
        self.raw.retain(|&h| f(&u64_to_board(h)))
    }

    pub fn clear(&mut self) {
        self.raw.clear()
    }

    pub fn reserve(&mut self, additional: HashMap<u32, usize>) {
        self.raw.reserve(additional)
    }

    pub fn difference<'a>(&'a self, other: &'a BoardSet) -> Difference<'a> {
        Difference(RawDifference::new(&self.raw, &other.raw))
    }

    pub fn symmetric_difference<'a>(&'a self, other: &'a BoardSet) -> SymmetricDifference<'a> {
        SymmetricDifference(RawSymmetricDifference::new(&self.raw, &other.raw))
    }

    pub fn intersection<'a>(&'a self, other: &'a BoardSet) -> Intersection<'a> {
        Intersection(RawIntersection::new(&self.raw, &other.raw))
    }

    pub fn union<'a>(&'a self, other: &'a BoardSet) -> Union<'a> {
        Union(RawUnion::new(&self.raw, &other.raw))
    }

    pub fn contains(&self, board: &Board) -> bool {
        self.raw.contains(&board.to_u64())
    }

    pub fn is_disjoint(&self, other: &BoardSet) -> bool {
        self.raw.is_disjoint(&other.raw)
    }

    pub fn is_subset(&self, other: &BoardSet) -> bool {
        self.raw.is_subset(&other.raw)
    }

    pub fn is_superset(&self, other: &BoardSet) -> bool {
        self.raw.is_superset(&other.raw)
    }

    pub fn insert(&mut self, board: Board) {
        self.raw.insert(board.to_u64())
    }

    pub fn remove(&mut self, board: &Board) -> bool {
        self.raw.remove(&board.to_u64())
    }

    pub fn take(&mut self, board: &Board) -> Option<Board> {
        self.raw.take(&board.to_u64()).map(u64_to_board)
    }

    pub fn load<R>(&mut self, reader: R) -> std::io::Result<()>
    where
        R: Read,
    {
        self.raw.load(reader)
    }

    pub fn save<W>(&self, writer: W) -> std::io::Result<()>
    where
        W: Write,
    {
        self.raw.save(writer)
    }
}

impl std::ops::BitAnd<&BoardSet> for &BoardSet {
    type Output = BoardSet;
    fn bitand(self, rhs: &BoardSet) -> Self::Output {
        Self::Output {
            raw: self.raw.bitand(&rhs.raw),
        }
    }
}

impl std::ops::BitOr<&BoardSet> for &BoardSet {
    type Output = BoardSet;
    fn bitor(self, rhs: &BoardSet) -> Self::Output {
        Self::Output {
            raw: self.raw.bitor(&rhs.raw),
        }
    }
}

impl std::ops::BitXor<&BoardSet> for &BoardSet {
    type Output = BoardSet;
    fn bitxor(self, rhs: &BoardSet) -> Self::Output {
        Self::Output {
            raw: self.raw.bitxor(&rhs.raw),
        }
    }
}

macro_rules! impl_iterators {
    ({$iter:ident => $raw:ident}) => {
        pub struct $iter($raw);

        impl Iterator for $iter {
            type Item = Board;
            fn next(&mut self) -> Option<Self::Item> {
                self.0.next().map(u64_to_board)
            }
        }
    };

    (<$iter:ident => $raw:ident>) => {
        pub struct $iter<'a>($raw<'a>);

        impl<'a> Iterator for $iter<'a> {
            type Item = Board;
            fn next(&mut self) -> Option<Self::Item> {
                self.0.next().map(u64_to_board)
            }
        }
    };

    ($({$iters1:ident => $raws1:ident})* $(<$iters2:ident => $raws2:ident>)*) => {
        $(impl_iterators!({$iters1 => $raws1});)*
        $(impl_iterators!(<$iters2 => $raws2>);)*
    };
}

impl_iterators!(
    { IntoIter => RawIntoIter }
    { Drain => RawDrain }
    < Iter => RawIter >
    < Difference => RawDifference >
    < SymmetricDifference => RawSymmetricDifference >
    < Intersection => RawIntersection >
    < Union => RawUnion >
);

// ********************************************************************
//  BoardSet
// ********************************************************************
#[derive(Debug, Clone, Default)]
pub struct RawBoardSet {
    top2bottoms: HashMap<u32, HashSet<u32>>,
}

impl FromIterator<u64> for RawBoardSet {
    fn from_iter<T: IntoIterator<Item = u64>>(iter: T) -> Self {
        let mut set = Self::new();
        for item in iter {
            set.insert(item);
        }
        set
    }
}

impl IntoIterator for RawBoardSet {
    type Item = u64;
    type IntoIter = RawIntoIter;
    fn into_iter(self) -> Self::IntoIter {
        Self::IntoIter::new(self)
    }
}

impl RawBoardSet {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn required_capacity<R>(raw_reader: R) -> HashMap<u32, usize>
    where
        R: Read,
    {
        let mut count = HashMap::new();
        let mut head = 0;
        for fragment in FragmentIter::new(raw_reader) {
            use Fragment::*;
            match fragment {
                Delimiter => continue,
                Head(h) => head = h,
                Tail(_) => *count.entry(head).or_default() += 1,
            }
        }
        count
    }

    pub fn with_capacity(capacity: HashMap<u32, usize>) -> Self {
        let mut top2bottoms = HashMap::with_capacity(capacity.len());
        for (top, num_bottoms) in capacity.into_iter() {
            top2bottoms.insert(top, HashSet::with_capacity(num_bottoms));
        }
        Self { top2bottoms }
    }

    pub fn capacity(&self) -> HashMap<u32, usize> {
        let mut capacity = HashMap::with_capacity(self.top2bottoms.len());
        for (k, v) in self.top2bottoms.iter() {
            capacity.insert(*k, v.capacity());
        }
        capacity
    }

    fn trim(&mut self) {
        self.top2bottoms.retain(|_, v| !v.is_empty());
    }

    pub fn iter(&self) -> RawIter {
        RawIter::new(self)
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

    pub fn drain(&mut self) -> RawDrain {
        RawDrain::new(self)
    }

    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&u64) -> bool,
    {
        for (&top, bottoms) in self.top2bottoms.iter_mut() {
            bottoms.retain(|&b| {
                let hash = RawBoardSet::u32_u32_to_u64(top, b);
                f(&hash)
            });
        }
        self.trim();
    }

    pub fn clear(&mut self) {
        self.top2bottoms.clear()
    }

    pub fn reserve(&mut self, additional: HashMap<u32, usize>) {
        for (top, additional_len) in additional.into_iter() {
            match self.top2bottoms.get_mut(&top) {
                Some(bottoms) => {
                    bottoms.reserve(additional_len);
                }
                None => {
                    self.top2bottoms
                        .insert(top, HashSet::with_capacity(additional_len));
                }
            };
        }
    }

    pub fn difference<'a>(&'a self, other: &'a RawBoardSet) -> RawDifference<'a> {
        RawDifference::new(self, other)
    }

    pub fn symmetric_difference<'a>(
        &'a self,
        other: &'a RawBoardSet,
    ) -> RawSymmetricDifference<'a> {
        RawSymmetricDifference::new(self, other)
    }

    pub fn intersection<'a>(&'a self, other: &'a RawBoardSet) -> RawIntersection<'a> {
        RawIntersection::new(self, other)
    }

    pub fn union<'a>(&'a self, other: &'a RawBoardSet) -> RawUnion<'a> {
        RawUnion::new(self, other)
    }

    pub fn contains(&self, hash: &u64) -> bool {
        let (k, v) = Self::u64_to_u32_u32(*hash);
        self.top2bottoms.get(&k).map_or(false, |x| x.contains(&v))
    }

    pub fn is_disjoint(&self, other: &RawBoardSet) -> bool {
        if self.len() <= other.len() {
            self.iter().all(|v| !other.contains(&v))
        } else {
            other.iter().all(|v| !self.contains(&v))
        }
    }

    pub fn is_subset(&self, other: &RawBoardSet) -> bool {
        if self.len() <= other.len() {
            self.iter().all(|v| other.contains(&v))
        } else {
            false
        }
    }

    pub fn is_superset(&self, other: &RawBoardSet) -> bool {
        other.is_subset(self)
    }

    pub fn insert(&mut self, hash: u64) {
        let (k, v) = Self::u64_to_u32_u32(hash);
        self.top2bottoms
            .entry(k)
            .or_insert_with(HashSet::new)
            .insert(v);
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

    pub fn take(&mut self, hash: &u64) -> Option<u64> {
        let (k, v) = Self::u64_to_u32_u32(*hash);
        let set = self.top2bottoms.get_mut(&k)?;
        let taken = set.take(&v).map(|bottom| Self::u32_u32_to_u64(k, bottom));
        if set.is_empty() {
            self.top2bottoms.remove(&k);
        }
        taken
    }

    pub fn load<R>(&mut self, reader: R) -> std::io::Result<()>
    where
        R: Read,
    {
        let mut iter = FragmentIter::new(reader);
        let mut dummy = HashSet::new();
        let mut set = &mut dummy;
        loop {
            let Some(next) = iter.try_next()? else {
                return Ok(());
            };

            use Fragment::*;
            match next {
                Delimiter => continue,
                Head(n) => set = self.top2bottoms.entry(n).or_insert_with(HashSet::new),
                Tail(n) => {
                    set.insert(n);
                }
            }
        }
    }

    pub fn save<W>(&self, writer: W) -> std::io::Result<()>
    where
        W: Write,
    {
        let mut writer = BufWriter::new(writer);
        for (top, bottoms) in self.top2bottoms.iter() {
            writer.write_all(&top.to_be_bytes())?;
            for bottom in bottoms.iter() {
                writer.write_all(&bottom.to_be_bytes())?;
            }
            writer.write_all(&u32::MAX.to_be_bytes())?;
        }
        writer.flush()?;
        Ok(())
    }
}

impl std::ops::BitAnd<&RawBoardSet> for &RawBoardSet {
    type Output = RawBoardSet;
    fn bitand(self, rhs: &RawBoardSet) -> Self::Output {
        self.intersection(rhs).collect()
    }
}

impl std::ops::BitOr<&RawBoardSet> for &RawBoardSet {
    type Output = RawBoardSet;
    fn bitor(self, rhs: &RawBoardSet) -> Self::Output {
        self.union(rhs).collect()
    }
}

impl std::ops::BitXor<&RawBoardSet> for &RawBoardSet {
    type Output = RawBoardSet;
    fn bitxor(self, rhs: &RawBoardSet) -> Self::Output {
        self.symmetric_difference(rhs).collect()
    }
}

type MapIter<'a> = std::collections::hash_map::Iter<'a, u32, HashSet<u32>>;
type SetIter<'a> = std::collections::hash_set::Iter<'a, u32>;

pub struct RawIter<'a> {
    set: &'a RawBoardSet,
    state: Option<(
        MapIter<'a>, // iterator of top2bottoms
        u32,         // key of top2bottoms
        SetIter<'a>, // iterator of value of top2bottoms
    )>,
}

impl<'a> RawIter<'a> {
    fn new(set: &'a RawBoardSet) -> Self {
        Self { set, state: None }
    }
}

impl<'a> Iterator for RawIter<'a> {
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
        Some(RawBoardSet::u32_u32_to_u64(*top, *bottom))
    }
}

type MapIntoIter = std::collections::hash_map::IntoIter<u32, HashSet<u32>>;
type SetIntoIter = std::collections::hash_set::IntoIter<u32>;

pub struct RawIntoIter {
    set: Option<RawBoardSet>,
    state: Option<(
        MapIntoIter, // iterator of set.top2bottoms
        u32,         // key of set.top2bottoms
        SetIntoIter, // iterator of value of set.top2bottoms
    )>,
}

impl RawIntoIter {
    fn new(set: RawBoardSet) -> Self {
        Self {
            set: Some(set),
            state: None,
        }
    }
}

impl Iterator for RawIntoIter {
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
        Some(RawBoardSet::u32_u32_to_u64(*top, bottom))
    }
}

pub struct RawDrain(RawIntoIter);

impl RawDrain {
    fn new(set: &mut RawBoardSet) -> Self {
        let original = std::mem::replace(set, RawBoardSet::new());
        Self(original.into_iter())
    }
}

impl Iterator for RawDrain {
    type Item = u64;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }
}

pub struct RawDifference<'a> {
    left: RawIter<'a>,
    right: &'a RawBoardSet,
}

impl<'a> RawDifference<'a> {
    fn new(left: &'a RawBoardSet, right: &'a RawBoardSet) -> Self {
        Self {
            left: left.iter(),
            right,
        }
    }
}

impl<'a> Iterator for RawDifference<'a> {
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

pub struct RawSymmetricDifference<'a> {
    left: &'a RawBoardSet,
    left_iter: RawIter<'a>,
    right: &'a RawBoardSet,
    right_iter: RawIter<'a>,
}

impl<'a> RawSymmetricDifference<'a> {
    fn new(left: &'a RawBoardSet, right: &'a RawBoardSet) -> Self {
        Self {
            left,
            left_iter: left.iter(),
            right,
            right_iter: right.iter(),
        }
    }
}

impl<'a> Iterator for RawSymmetricDifference<'a> {
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

pub struct RawIntersection<'a> {
    left_iter: RawIter<'a>,
    right: &'a RawBoardSet,
}

impl<'a> RawIntersection<'a> {
    fn new(left: &'a RawBoardSet, right: &'a RawBoardSet) -> Self {
        Self {
            left_iter: left.iter(),
            right,
        }
    }
}

impl<'a> Iterator for RawIntersection<'a> {
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

pub struct RawUnion<'a> {
    left_iter: RawIter<'a>,
    right: &'a RawBoardSet,
    right_iter: RawIter<'a>,
}

impl<'a> RawUnion<'a> {
    fn new(left: &'a RawBoardSet, right: &'a RawBoardSet) -> Self {
        Self {
            left_iter: left.iter(),
            right,
            right_iter: right.iter(),
        }
    }
}

impl<'a> Iterator for RawUnion<'a> {
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
