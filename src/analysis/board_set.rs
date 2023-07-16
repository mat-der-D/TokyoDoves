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
#[derive(Debug, Clone, Default, PartialEq, Eq)]
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
        for (top, num_bottoms) in rhs.0 {
            *self.0.entry(top).or_default() += num_bottoms;
        }
    }
}

// ********************************************************************
//  BoardSet
// ********************************************************************
/// A light implementation of set of [`Board`]s.
///
/// Its methods are similar to those of [`std::collections::HashSet`].
/// Read their documentations for quick understanding.
///
/// It has [`RawBoardSet`] internally, which is a set of `u64` expressions of
/// [`Board`]s created by [`Board::to_u64`].
/// [`RawBoardSet`] also has similar methods to `BoardSet`
/// except that the elements are `u64`, not [`Board`].
///
/// In general, the memory size of the set is smaller than `HashSet<Board>`,
/// when they have the same number of elements.
///
/// It supports i/o utilities [`BoardSet::load`], [`BoardSet::load_filter`]
/// and [`BoardSet::save`].
/// A binary file will be saved when [`BoardSet::save`] is called,
/// which can be reloaded by [`BoardSet::load`].
/// [`BoardSet::load_filter`] gives a way to load a part satisfying a criterion.
/// For efficient loading, the following process is better:
/// 1. Calculate [`Capacity`] required to load the file by [`BoardSet::required_capacity`].
/// 2. Allocate memories by [`BoardSet::reserve`] or create new `BoardSet` by [`BoardSet::with_capacity`].
/// 3. Call [`BoardSet::load`] to load elements in the file.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct BoardSet {
    raw: RawBoardSet,
}

impl<const N: usize> From<[Board; N]> for BoardSet {
    fn from(value: [Board; N]) -> Self {
        Self::from_iter(value)
    }
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
        self.raw.extend(iter.into_iter().map(|b| b.to_u64()))
    }
}

impl<'a> Extend<&'a Board> for BoardSet {
    fn extend<T: IntoIterator<Item = &'a Board>>(&mut self, iter: T) {
        self.raw.extend(iter.into_iter().map(|b| b.to_u64()))
    }
}

impl IntoIterator for BoardSet {
    type Item = Board;
    type IntoIter = IntoIter;
    fn into_iter(self) -> Self::IntoIter {
        IntoIter(RawIntoIter::new(self.raw))
    }
}

impl<'a> IntoIterator for &'a BoardSet {
    type Item = Board;
    type IntoIter = Iter<'a>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl From<RawBoardSet> for BoardSet {
    fn from(raw: RawBoardSet) -> Self {
        Self { raw }
    }
}

impl BoardSet {
    /// Creates an empty `BoardSet`.
    ///
    /// # Examples
    /// ```rust
    /// use tokyodoves::analysis::BoardSet;
    /// let set = BoardSet::new();
    /// ```
    pub fn new() -> Self {
        Self::default()
    }

    /// Returns a reference to the internal [`RawBoardSet`]
    pub fn raw(&self) -> &RawBoardSet {
        &self.raw
    }

    /// Returns a mutable reference to the internal [`RawBoardSet`]
    pub fn raw_mut(&mut self) -> &mut RawBoardSet {
        &mut self.raw
    }

    /// Returns the internal [`RawBoardSet`].
    /// The set loses its ownership.
    pub fn into_raw(self) -> RawBoardSet {
        self.raw
    }

    /// Returns [`Capacity`] required to load all elements specified by `reader`.
    pub fn required_capacity<R>(reader: R) -> Capacity
    where
        R: Read,
    {
        RawBoardSet::required_capacity(reader)
    }

    /// Returns [`Capacity`] required to load all elements (`e`) specified by `reader`,
    /// under the condition of `f` (where `f(&e)` returns `true`).
    pub fn required_capacity_filter<R, F>(reader: R, f: F) -> Capacity
    where
        R: Read,
        F: FnMut(&u64) -> bool,
    {
        RawBoardSet::required_capacity_filter(reader, f)
    }

    /// Creates an empty `BoardSet` with at least the specified capacity.
    ///
    /// The set will be able to hold sufficient elements required by `capacity`
    /// without reallocating.
    ///
    /// # Examples
    /// ```rust
    /// use tokyodoves::Board;
    /// use tokyodoves::analysis::BoardSet;
    /// let mut set0 = BoardSet::new();
    /// set0.insert(Board::new());
    /// let capacity = set0.capacity();
    /// let set1 = BoardSet::with_capacity(capacity);
    /// ```
    pub fn with_capacity(capacity: Capacity) -> Self {
        Self {
            raw: RawBoardSet::with_capacity(capacity),
        }
    }

    /// Returns the [`Capacity`] of the set.
    ///
    /// # Examples
    /// ```rust
    /// use tokyodoves::analysis::BoardSet;
    /// let set = BoardSet::new();
    /// let capacity = set.capacity();
    /// ```
    pub fn capacity(&self) -> Capacity {
        self.raw.capacity()
    }

    /// An iterator visiting all elements in arbitrary order.
    /// The iterator element type is [`Board`].
    ///
    /// # Examples
    /// ```rust
    /// use tokyodoves::Board;
    /// use tokyodoves::analysis::BoardSet;
    /// let mut set = BoardSet::new();
    /// set.insert(Board::new());
    /// for x in set.iter() {
    ///     println!("{}", x);
    /// }
    /// ```
    pub fn iter(&self) -> Iter {
        Iter(RawIter::new(&self.raw))
    }

    /// Returns the number of elements in the set.
    ///
    /// # Examples
    /// ```rust
    /// use tokyodoves::Board;
    /// use tokyodoves::analysis::BoardSet;
    /// let mut set = BoardSet::new();
    /// assert_eq!(set.len(), 0);
    /// set.insert(Board::new());
    /// assert_eq!(set.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        self.raw.len()
    }

    /// Returns `true` if the set contains no elements.
    ///
    /// # Examples
    /// ```rust
    /// use tokyodoves::Board;
    /// use tokyodoves::analysis::BoardSet;
    /// let mut set = BoardSet::new();
    /// assert!(set.is_empty());
    /// set.insert(Board::new());
    /// assert!(!set.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.raw.is_empty()
    }

    /// Clears the set, returning all elements as an iterator.
    pub fn drain(&mut self) -> Drain {
        Drain(RawDrain::new(&mut self.raw))
    }

    /// Retains only the elements specified by the predicate.
    ///
    /// In other words, remove all elements `e` for which `f(&e)` returns `false`.
    /// The elements are visited in unsorted (and unspecified) order.
    ///
    /// # Examples
    /// ```rust
    /// use std::str::FromStr;
    /// use tokyodoves::{Board, BoardBuilder};
    /// use tokyodoves::analysis::BoardSet;
    ///
    /// let mut set = BoardSet::new();
    /// set.insert(Board::new());
    /// let set1 = set.clone();
    /// set.insert(BoardBuilder::from_str("BbA").unwrap().build_unchecked());
    /// set.retain(|b| b.count_doves_on_field() == 2);
    /// assert_eq!(set1, set);
    /// ```
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&Board) -> bool,
    {
        self.raw.retain(|&h| f(&u64_to_board(h)))
    }

    /// Clears the set, removing all values
    ///
    /// # Examples
    /// ```rust
    /// use tokyodoves::Board;
    /// use tokyodoves::analysis::BoardSet;
    ///
    /// let mut set = BoardSet::new();
    /// set.insert(Board::new());
    /// set.clear();
    /// assert!(set.is_empty());
    /// ```
    pub fn clear(&mut self) {
        self.raw.clear()
    }

    /// Reserves capacity for at least `additional` more elements
    /// to be inserted in the `BoardSet` without reallocating.
    pub fn reserve(&mut self, additional: Capacity) {
        self.raw.reserve(additional)
    }

    /// Shrinks the capacity of the set as much as possible.
    pub fn shrink_to_fit(&mut self) {
        self.raw.shrink_to_fit()
    }

    /// Visits the boards representing the difference, i.e.,
    /// the boards that are in `self` but not in `other`.
    pub fn difference<'a>(&'a self, other: &'a BoardSet) -> Difference<'a> {
        Difference(RawDifference::new(&self.raw, &other.raw))
    }

    /// Visits the boards representing the symmetric difference, i.e.,
    /// the boards that are in `self` or in `other` but not in both.
    pub fn symmetric_difference<'a>(&'a self, other: &'a BoardSet) -> SymmetricDifference<'a> {
        SymmetricDifference(RawSymmetricDifference::new(&self.raw, &other.raw))
    }

    /// Visits the boards representing the intersection, i.e.,
    /// the boards that are both in `self` and `other`.
    pub fn intersection<'a>(&'a self, other: &'a BoardSet) -> Intersection<'a> {
        Intersection(RawIntersection::new(&self.raw, &other.raw))
    }

    /// Visits the boards representing the union, i.e.,
    /// all the boards in `self` or `other`, without duplicates.
    pub fn union<'a>(&'a self, other: &'a BoardSet) -> Union<'a> {
        Union(RawUnion::new(&self.raw, &other.raw))
    }

    /// Returns `true` if the set contains a board.
    pub fn contains(&self, board: &Board) -> bool {
        self.raw.contains(&board.to_u64())
    }

    /// Returns `true` if `self` has no elements in common with `other`.
    /// This is equivalent to checking for an empty intersection.
    pub fn is_disjoint(&self, other: &BoardSet) -> bool {
        self.raw.is_disjoint(&other.raw)
    }

    /// Returns `true` if the set is a subset of another, i.e.,
    /// `other` contains at least all the boards in `self`.
    pub fn is_subset(&self, other: &BoardSet) -> bool {
        self.raw.is_subset(&other.raw)
    }

    /// Returns `true` if the set is a superset of another, i.e.,
    /// `self` contains at least all the boards in `other`.
    pub fn is_superset(&self, other: &BoardSet) -> bool {
        self.raw.is_superset(&other.raw)
    }

    /// Adds a board to the set.
    ///
    /// Returns whether the board was newly inserted. That is:
    /// - If the set did not previously contain this board, `true` is returned.
    /// - If the set already contained this board, `false` is returned.
    pub fn insert(&mut self, board: Board) -> bool {
        self.raw.insert(board.to_u64())
    }

    /// Removes a board from the set.
    /// Returns whether the board was present in the set.
    pub fn remove(&mut self, board: &Board) -> bool {
        self.raw.remove(&board.to_u64())
    }

    /// Removes and returns the board in the set, if any,
    /// that is equal to the given one.
    pub fn take(&mut self, board: &Board) -> Option<Board> {
        self.raw.take(&board.to_u64()).map(u64_to_board)
    }

    /// Absorbs all elements in the given set.
    /// The given set loses its ownership.
    pub fn absorb(&mut self, set: BoardSet) {
        self.raw.absorb(set.raw);
    }

    /// Inserts all elements given by `reader` into `self`.
    pub fn load<R>(&mut self, reader: R) -> std::io::Result<()>
    where
        R: Read,
    {
        self.raw.load(reader)
    }

    /// Inserts all elements (`e`) given by `reader` under the condition of `f`
    /// (where `f(&e)` is `true`) into `self`.
    pub fn load_filter<R, F>(&mut self, reader: R, f: F) -> std::io::Result<()>
    where
        R: Read,
        F: FnMut(&u64) -> bool,
    {
        self.raw.load_filter(reader, f)
    }

    /// Writes all elements in the set to `writer`.
    /// The saved data can be loaded both by [`BoardSet::load`] and [`RawBoardSet::load`].
    pub fn save<W>(&self, writer: W) -> std::io::Result<()>
    where
        W: Write,
    {
        self.raw.save(writer)
    }
}

impl std::ops::BitAnd<&BoardSet> for &BoardSet {
    type Output = BoardSet;
    /// Returns the intersection of `self` and `rhs` as a new `BoardSet`.
    fn bitand(self, rhs: &BoardSet) -> Self::Output {
        Self::Output {
            raw: self.raw.bitand(&rhs.raw),
        }
    }
}

impl std::ops::BitOr<&BoardSet> for &BoardSet {
    type Output = BoardSet;
    /// Returns the union of `self` and `rhs` as a new `BoardSet`.
    fn bitor(self, rhs: &BoardSet) -> Self::Output {
        Self::Output {
            raw: self.raw.bitor(&rhs.raw),
        }
    }
}

impl std::ops::BitXor<&BoardSet> for &BoardSet {
    type Output = BoardSet;
    /// Returns the symmetric difference of `self` and `rhs` as a new `BoardSet`.
    fn bitxor(self, rhs: &BoardSet) -> Self::Output {
        Self::Output {
            raw: self.raw.bitxor(&rhs.raw),
        }
    }
}

impl std::ops::Sub<&BoardSet> for &BoardSet {
    type Output = BoardSet;
    /// Returns the difference of `self` and `rhs` as a new `BoardSet`.
    fn sub(self, rhs: &BoardSet) -> Self::Output {
        Self::Output {
            raw: self.raw.sub(&rhs.raw),
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
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct RawBoardSet {
    pub(crate) top2bottoms: HashMap<u32, HashSet<u32>>,
}

impl From<BoardSet> for RawBoardSet {
    fn from(value: BoardSet) -> Self {
        value.into_raw()
    }
}

impl<const N: usize> From<[u64; N]> for RawBoardSet {
    fn from(value: [u64; N]) -> Self {
        Self::from_iter(value)
    }
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
        iter.into_iter().for_each(|h| {
            self.insert(h);
        });
    }
}

impl<'a> Extend<&'a u64> for RawBoardSet {
    fn extend<T: IntoIterator<Item = &'a u64>>(&mut self, iter: T) {
        self.extend(iter.into_iter().cloned())
    }
}

impl IntoIterator for RawBoardSet {
    type Item = u64;
    type IntoIter = RawIntoIter;
    fn into_iter(self) -> Self::IntoIter {
        Self::IntoIter::new(self)
    }
}

impl<'a> IntoIterator for &'a RawBoardSet {
    type Item = u64;
    type IntoIter = RawIter<'a>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl RawBoardSet {
    /// Creates an empty `BoardSet`.
    ///
    /// # Examples
    /// ```rust
    /// use tokyodoves::analysis::board_set::RawBoardSet;
    /// let set = RawBoardSet::new();
    /// ```
    pub fn new() -> Self {
        Self::default()
    }

    /// Returns [`Capacity`] required to load all elements specified by `reader`.
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

    /// Returns [`Capacity`] required to load all elements (`e`) specified by `reader`,
    /// under the condition of `f` (where `f(&e)` returns `true`).
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

    /// Creates an empty `BoardSet` with at least the specified capacity.
    ///
    /// The set will be able to hold sufficient elements required by `capacity`
    /// without reallocating.
    ///
    /// # Examples
    /// ```rust
    /// use tokyodoves::Board;
    /// use tokyodoves::analysis::board_set::RawBoardSet;
    /// let mut set0 = RawBoardSet::new();
    /// set0.insert(Board::new().to_u64());
    /// let capacity = set0.capacity();
    /// let set1 = RawBoardSet::with_capacity(capacity);
    /// ```
    pub fn with_capacity(capacity: Capacity) -> Self {
        let mut top2bottoms = HashMap::with_capacity(capacity.0.len());
        for (top, num_bottoms) in capacity.0 {
            top2bottoms.insert(top, HashSet::with_capacity(num_bottoms));
        }
        Self { top2bottoms }
    }

    /// Returns the [`Capacity`] of the set.
    ///
    /// # Examples
    /// ```rust
    /// use tokyodoves::analysis::board_set::RawBoardSet;
    /// let set = RawBoardSet::new();
    /// let capacity = set.capacity();
    /// ```
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

    /// An iterator visiting all elements in arbitrary order.
    /// The iterator element type is [`Board`].
    ///
    /// # Examples
    /// ```rust
    /// use tokyodoves::Board;
    /// use tokyodoves::analysis::board_set::RawBoardSet;
    /// let mut set = RawBoardSet::new();
    /// set.insert(Board::new().to_u64());
    /// for x in set.iter() {
    ///     println!("{}", x);
    /// }
    /// ```
    pub fn iter(&self) -> RawIter {
        RawIter::new(self)
    }

    pub(crate) fn u64_to_u32_u32(n: u64) -> (u32, u32) {
        ((n >> 32) as u32, n as u32)
    }

    pub(crate) fn u32_u32_to_u64(top: u32, bottom: u32) -> u64 {
        ((top as u64) << 32) | (bottom as u64)
    }

    /// Returns the number of elements in the set.
    ///
    /// # Examples
    /// ```rust
    /// use tokyodoves::Board;
    /// use tokyodoves::analysis::board_set::RawBoardSet;
    /// let mut set = RawBoardSet::new();
    /// assert_eq!(set.len(), 0);
    /// set.insert(Board::new().to_u64());
    /// assert_eq!(set.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        self.top2bottoms.values().map(|s| s.len()).sum()
    }

    /// Returns `true` if the set contains no elements.
    ///
    /// # Examples
    /// ```rust
    /// use tokyodoves::Board;
    /// use tokyodoves::analysis::board_set::RawBoardSet;
    /// let mut set = RawBoardSet::new();
    /// assert!(set.is_empty());
    /// set.insert(Board::new().to_u64());
    /// assert!(!set.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.top2bottoms.values().all(|s| s.is_empty())
    }

    /// Clears the set, returning all elements as an iterator.
    pub fn drain(&mut self) -> RawDrain {
        RawDrain::new(self)
    }

    /// Retains only the elements specified by the predicate.
    ///
    /// In other words, remove all elements `e` for which `f(&e)` returns `false`.
    /// The elements are visited in unsorted (and unspecified) order.
    ///
    /// # Examples
    /// ```rust
    /// use std::str::FromStr;
    /// use tokyodoves::{Board, BoardBuilder};
    /// use tokyodoves::analysis::board_set::RawBoardSet;
    ///
    /// let mut set = RawBoardSet::new();
    /// set.insert(Board::new().to_u64());
    /// let set1 = set.clone();
    /// set.insert(BoardBuilder::from_str("BbA").unwrap().build_unchecked().to_u64());
    /// set.retain(|b| (b & 0xfff << 48).count_ones() == 2);
    /// assert_eq!(set1, set);
    /// ```
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

    /// Clears the set, removing all values
    ///
    /// # Examples
    /// ```rust
    /// use tokyodoves::Board;
    /// use tokyodoves::analysis::board_set::RawBoardSet;
    ///
    /// let mut set = RawBoardSet::new();
    /// set.insert(Board::new().to_u64());
    /// set.clear();
    /// assert!(set.is_empty());
    /// ```
    pub fn clear(&mut self) {
        self.top2bottoms.clear()
    }

    /// Reserves capacity for at least `additional` more elements
    /// to be inserted in the `RawBoardSet` without reallocating.
    pub fn reserve(&mut self, additional: Capacity) {
        for (top, additional_len) in additional.0 {
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

    /// Shrinks the capacity of the set as much as possible.
    pub fn shrink_to_fit(&mut self) {
        self.top2bottoms.shrink_to_fit();
        self.top2bottoms
            .values_mut()
            .for_each(|b| b.shrink_to_fit());
    }

    /// Visits the values representing the difference, i.e.,
    /// the values that are in `self` but not in `other`.
    pub fn difference<'a>(&'a self, other: &'a RawBoardSet) -> RawDifference<'a> {
        RawDifference::new(self, other)
    }

    /// Visits the values representing the symmetric difference, i.e.,
    /// the values that are in `self` or in `other` but not in both.
    pub fn symmetric_difference<'a>(
        &'a self,
        other: &'a RawBoardSet,
    ) -> RawSymmetricDifference<'a> {
        RawSymmetricDifference::new(self, other)
    }

    /// Visits the values representing the intersection, i.e.,
    /// the values that are both in `self` and `other`.
    pub fn intersection<'a>(&'a self, other: &'a RawBoardSet) -> RawIntersection<'a> {
        RawIntersection::new(self, other)
    }

    /// Visits the values representing the union, i.e.,
    /// all the values in `self` or `other`, without duplicates.
    pub fn union<'a>(&'a self, other: &'a RawBoardSet) -> RawUnion<'a> {
        RawUnion::new(self, other)
    }

    /// Returns `true` if the set contains a value.
    pub fn contains(&self, hash: &u64) -> bool {
        let (k, v) = Self::u64_to_u32_u32(*hash);
        self.top2bottoms.get(&k).map_or(false, |x| x.contains(&v))
    }

    /// Returns `true` if `self` has no elements in common with `other`.
    /// This is equivalent to checking for an empty intersection.
    pub fn is_disjoint(&self, other: &RawBoardSet) -> bool {
        if self.len() <= other.len() {
            self.iter().all(|v| !other.contains(&v))
        } else {
            other.iter().all(|v| !self.contains(&v))
        }
    }

    /// Returns `true` if the set is a subset of another, i.e.,
    /// `other` contains at least all the boards in `self`.
    pub fn is_subset(&self, other: &RawBoardSet) -> bool {
        if self.len() <= other.len() {
            self.iter().all(|v| other.contains(&v))
        } else {
            false
        }
    }

    /// Returns `true` if the set is a superset of another, i.e.,
    /// `self` contains at least all the boards in `other`.
    pub fn is_superset(&self, other: &RawBoardSet) -> bool {
        other.is_subset(self)
    }

    /// Adds a value to the set.
    ///
    /// Returns whether the value was newly inserted. That is:
    /// - If the set did not previously contain this value, `true` is returned.
    /// - If the set already contained this value, `false` is returned.
    pub fn insert(&mut self, hash: u64) -> bool {
        let (k, v) = Self::u64_to_u32_u32(hash);
        self.top2bottoms.entry(k).or_default().insert(v)
    }

    /// Removes a value from the set.
    /// Returns whether the value was present in the set.
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

    /// Removes and returns the value in the set, if any,
    /// that is equal to the given one.
    pub fn take(&mut self, hash: &u64) -> Option<u64> {
        let (k, v) = Self::u64_to_u32_u32(*hash);
        let set = self.top2bottoms.get_mut(&k)?;
        let taken = set.take(&v).map(|bottom| Self::u32_u32_to_u64(k, bottom));
        if set.is_empty() {
            self.top2bottoms.remove(&k);
        }
        taken
    }

    /// Absorbs all elements in the given set.
    /// The given set loses its ownership.
    pub fn absorb(&mut self, set: RawBoardSet) {
        self.reserve(set.capacity());
        for (top, bottoms) in set.top2bottoms {
            if bottoms.is_empty() {
                continue;
            }
            self.top2bottoms.entry(top).or_default().extend(bottoms);
        }
    }

    /// Inserts all elements given by `reader` into `self`.
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

    /// Inserts all elements (`e`) given by `reader` under the condition of `f`
    /// (where `f(&e)` is `true`) into `self`.
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

    /// Writes all elements in the set to `writer`.
    /// The saved data can be loaded both by [`BoardSet::load`] and [`RawBoardSet::load`].
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
    /// Returns the intersection of `self` and `rhs` as a new `RawBoardSet`.
    fn bitand(self, rhs: &RawBoardSet) -> Self::Output {
        self.intersection(rhs).collect()
    }
}

impl std::ops::BitOr<&RawBoardSet> for &RawBoardSet {
    type Output = RawBoardSet;
    /// Returns the union of `self` and `rhs` as a new `RawBoardSet`.
    fn bitor(self, rhs: &RawBoardSet) -> Self::Output {
        self.union(rhs).collect()
    }
}

impl std::ops::BitXor<&RawBoardSet> for &RawBoardSet {
    type Output = RawBoardSet;
    /// Returns the symmetric difference of `self` and `rhs` as a new `RawBoardSet`.
    fn bitxor(self, rhs: &RawBoardSet) -> Self::Output {
        self.symmetric_difference(rhs).collect()
    }
}

impl std::ops::Sub<&RawBoardSet> for &RawBoardSet {
    type Output = RawBoardSet;
    /// Returns the difference of `self` and `rhs` as a new `RawBoardSet`.
    fn sub(self, rhs: &RawBoardSet) -> Self::Output {
        self.difference(rhs).collect()
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

#[cfg(test)]
mod tests {
    use std::str::FromStr;

    use crate::{analysis::*, *};

    fn create_from_strs(strs: &[&str]) -> BoardSet {
        let mut set = BoardSet::new();
        for board_str in strs {
            let board = BoardBuilder::from_str(board_str).unwrap().build_unchecked();
            set.insert(board);
        }
        set
    }

    #[test]
    fn test_set_calculation() {
        let set1 = create_from_strs(&["Bb", "Bbh", "Bba"]);
        let set2 = create_from_strs(&["Bb", "BbH", "BbA"]);
        let set1and2 = create_from_strs(&["Bb"]);
        let set1or2 = create_from_strs(&["Bb", "Bbh", "Bba", "BbH", "BbA"]);
        let set1xor2 = create_from_strs(&["Bbh", "Bba", "BbH", "BbA"]);
        let set1minus2 = create_from_strs(&["Bbh", "Bba"]);

        assert_eq!(&set1 & &set2, set1and2);
        assert_eq!(set1.raw() & set2.raw(), *set1and2.raw());

        assert_eq!(&set1 | &set2, set1or2);
        assert_eq!(set1.raw() | set2.raw(), *set1or2.raw());

        assert_eq!(&set1 ^ &set2, set1xor2);
        assert_eq!(set1.raw() ^ set2.raw(), *set1xor2.raw());

        assert_eq!(&set1 - &set2, set1minus2);
        assert_eq!(set1.raw() - set2.raw(), *set1minus2.raw());

        assert!(set1or2.is_superset(&set1));
        assert!(set1or2.raw().is_superset(set1.raw()));

        assert!(set1.is_subset(&set1or2));
        assert!(set1.raw().is_subset(set1or2.raw()));

        assert!(set1xor2.is_disjoint(&set1and2));
        assert!(set1xor2.raw().is_disjoint(set1and2.raw()));
    }

    #[test]
    fn test_absorb_extend() {
        let set1 = create_from_strs(&["Bb", "Bbh", "Bba"]);
        let set2 = create_from_strs(&["Bb", "BbH", "BbA"]);
        let set1or2 = create_from_strs(&["Bb", "Bbh", "Bba", "BbH", "BbA"]);

        let mut set1absorb2 = set1.clone();
        set1absorb2.absorb(set2.clone());
        assert_eq!(set1absorb2, set1or2);

        let mut set1absorb2_raw = set1.raw().clone();
        set1absorb2_raw.absorb(set2.raw().clone());
        assert_eq!(set1absorb2_raw, *set1or2.raw());

        let mut set1extend2 = set1.clone();
        set1extend2.extend(set2.iter());
        assert_eq!(set1absorb2, set1extend2);

        let mut set1extend2_raw = set1.raw().clone();
        set1extend2_raw.extend(set2.raw().iter());
        assert_eq!(set1absorb2_raw, set1extend2_raw);
    }
}
