use crate::analysis::io::{Fragment, FragmentIter};
use crate::prelude::{Board, BoardBuilder};
use std::{
    collections::{HashMap, HashSet},
    io::{BufWriter, Read, Write},
};

fn u64_to_board(hash: u64) -> Board {
    BoardBuilder::from(hash).build_unchecked()
}

// ********************************************************************
//  Capacity
// ********************************************************************
#[derive(Debug, Clone, Default)]
pub struct Capacity(HashMap<u32, usize>);

impl Capacity {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn len(&self) -> usize {
        self.0.values().sum()
    }

    pub fn is_empty(&self) -> bool {
        self.0.values().all(|&n| n == 0)
    }
}

impl std::ops::Add for Capacity {
    type Output = Capacity;
    fn add(mut self, rhs: Self) -> Self::Output {
        self += rhs;
        self
    }
}

impl std::ops::AddAssign for Capacity {
    fn add_assign(&mut self, rhs: Self) {
        for (top, num_bottoms) in rhs.0.into_iter() {
            *self.0.entry(top).or_default() += num_bottoms;
        }
    }
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

impl Extend<Board> for BoardSet {
    fn extend<T: IntoIterator<Item = Board>>(&mut self, iter: T) {
        iter.into_iter().for_each(|b| self.insert(b));
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

    pub fn required_capacity<R>(reader: R) -> Capacity
    where
        R: Read,
    {
        RawBoardSet::required_capacity(reader)
    }

    pub fn required_capacity_filter<R, F>(reader: R, f: F) -> Capacity
    where
        R: Read,
        F: FnMut(&u64) -> bool,
    {
        RawBoardSet::required_capacity_filter(reader, f)
    }

    pub fn with_capacity(capacity: Capacity) -> Self {
        Self {
            raw: RawBoardSet::with_capacity(capacity),
        }
    }

    pub fn capacity(&self) -> Capacity {
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

    pub fn reserve(&mut self, additional: Capacity) {
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

    pub fn absorb(&mut self, set: BoardSet) {
        self.raw.absorb(set.raw);
    }

    pub fn load<R>(&mut self, reader: R) -> std::io::Result<()>
    where
        R: Read,
    {
        self.raw.load(reader)
    }

    pub fn load_filter<R, F>(&mut self, reader: R, f: F) -> std::io::Result<()>
    where
        R: Read,
        F: FnMut(&u64) -> bool,
    {
        self.raw.load_filter(reader, f)
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

impl Extend<u64> for RawBoardSet {
    fn extend<T: IntoIterator<Item = u64>>(&mut self, iter: T) {
        iter.into_iter().for_each(|h| self.insert(h));
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

    pub fn required_capacity<R>(reader: R) -> Capacity
    where
        R: Read,
    {
        let mut count = HashMap::new();
        let mut top = 0;
        for fragment in FragmentIter::new(reader) {
            use Fragment::*;
            match fragment {
                Delimiter => continue,
                Top(top_) => top = top_,
                Bottom(_) => *count.entry(top).or_default() += 1,
            }
        }
        Capacity(count)
    }

    pub fn required_capacity_filter<R, F>(reader: R, mut f: F) -> Capacity
    where
        R: Read,
        F: FnMut(&u64) -> bool,
    {
        let mut count = HashMap::new();
        let mut top = 0;
        for fragment in FragmentIter::new(reader) {
            use Fragment::*;
            match fragment {
                Delimiter => continue,
                Top(top_) => top = top_,
                Bottom(bottom) => {
                    let hash = Self::u32_u32_to_u64(top, bottom);
                    if f(&hash) {
                        *count.entry(top).or_default() += 1;
                    }
                }
            }
        }
        Capacity(count)
    }

    pub fn with_capacity(capacity: Capacity) -> Self {
        let mut top2bottoms = HashMap::with_capacity(capacity.0.len());
        for (top, num_bottoms) in capacity.0.into_iter() {
            top2bottoms.insert(top, HashSet::with_capacity(num_bottoms));
        }
        Self { top2bottoms }
    }

    pub fn capacity(&self) -> Capacity {
        let mut count = HashMap::with_capacity(self.top2bottoms.len());
        for (k, v) in self.top2bottoms.iter() {
            count.insert(*k, v.capacity());
        }
        Capacity(count)
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

    pub fn reserve(&mut self, additional: Capacity) {
        for (top, additional_len) in additional.0.into_iter() {
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
        self.top2bottoms.entry(k).or_default().insert(v);
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

    pub fn absorb(&mut self, set: RawBoardSet) {
        for (top, bottoms) in set.top2bottoms.into_iter() {
            if bottoms.is_empty() {
                continue;
            }
            self.top2bottoms
                .entry(top)
                .or_default()
                .extend(bottoms.into_iter());
        }
    }

    pub fn load<R>(&mut self, reader: R) -> std::io::Result<()>
    where
        R: Read,
    {
        let mut iter = FragmentIter::new(reader);
        let mut dummy = HashSet::new();
        let mut set = &mut dummy;
        let mut top = 0;
        loop {
            let Some(next) = iter.try_next()? else {
                return Ok(());
            };

            use Fragment::*;
            match next {
                Delimiter => {
                    if set.is_empty() {
                        set = &mut dummy;
                        self.top2bottoms.remove(&top);
                    }
                }
                Top(top_) => {
                    set = self.top2bottoms.entry(top_).or_default();
                    top = top_;
                }
                Bottom(bottom_) => {
                    set.insert(bottom_);
                }
            }
        }
    }

    pub fn load_filter<R, F>(&mut self, reader: R, mut f: F) -> std::io::Result<()>
    where
        R: Read,
        F: FnMut(&u64) -> bool,
    {
        let mut iter = FragmentIter::new(reader);
        let mut dummy = HashSet::new();
        let mut set = &mut dummy;
        let mut top = 0;
        loop {
            let Some(next) = iter.try_next()? else {
                return Ok(());
            };

            use Fragment::*;
            match next {
                Delimiter => {
                    if set.is_empty() {
                        set = &mut dummy;
                        self.top2bottoms.remove(&top);
                    }
                }
                Top(top_) => {
                    set = self.top2bottoms.entry(top_).or_default();
                    top = top_;
                }
                Bottom(bottom) => {
                    let hash = Self::u32_u32_to_u64(top, bottom);
                    if f(&hash) {
                        set.insert(bottom);
                    }
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
        loop {
            let Some((map_iter, top, set_iter)) = self.state.as_mut() else {
                let mut map_iter_raw = self.set.top2bottoms.iter();
                let (top, set) = map_iter_raw.next()?;
                self.state = Some((map_iter_raw, *top, set.iter()));
                continue;
            };

            let Some(bottom) = set_iter.next() else {
                let (next_top, next_set) = map_iter.next()?;
                *top = *next_top;
                *set_iter = next_set.iter();
                continue;
            };
            return Some(RawBoardSet::u32_u32_to_u64(*top, *bottom));
        }
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
        loop {
            let Some((map_iter, top, set_iter)) = self.state.as_mut() else {
                let set = std::mem::replace(&mut self.set, None)?;
                let mut map_iter_raw = set.top2bottoms.into_iter();
                let (top, set) = map_iter_raw.next()?;
                self.state = Some((map_iter_raw, top, set.into_iter()));
                continue;
            };

            let Some(bottom) = set_iter.next() else {
                let (next_top, next_set) = map_iter.next()?;
                *top = next_top;
                *set_iter = next_set.into_iter();
                continue;
            };
            return Some(RawBoardSet::u32_u32_to_u64(*top, bottom));
        }
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
        loop {
            let item = self.left.next()?;
            if !self.right.contains(&item) {
                return Some(item);
            }
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
        loop {
            if let Some(item_left) = self.left_iter.next() {
                if !self.right.contains(&item_left) {
                    return Some(item_left);
                }
            } else {
                let item_right = self.right_iter.next()?;
                if !self.left.contains(&item_right) {
                    return Some(item_right);
                }
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
        loop {
            let item = self.left_iter.next()?;
            if self.right.contains(&item) {
                return Some(item);
            }
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
        loop {
            match self.left_iter.next() {
                Some(item) => {
                    if !self.right.contains(&item) {
                        return Some(item);
                    }
                }
                None => return self.right_iter.next(),
            }
        }
    }
}
