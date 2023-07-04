//! Container structs of some objects

use crate::prelude::pieces::{dove_to_index, try_index_to_dove};
use crate::prelude::{Action, Dove};

// *******************************************************************
//  Action Container
// *******************************************************************
/// Read-only [`Sized`] container of [`Action`]s.
pub trait ActionContainer:
    Clone + IntoIterator<Item = Action> + std::ops::Index<usize, Output = Action>
{
    /// Returns the number of elements.
    fn len(&self) -> usize;

    /// Returns `true` if it is empty.
    fn is_empty(&self) -> bool;

    /// Returns `true` if it contains the specified [`Action`].
    fn contains(&self, action: Action) -> bool;
}

/// An [`ActionContainer`] with a finite capacity.
///
/// The generic constant `N` is the maximum number of items
/// it can hold.
#[derive(Debug, Clone)]
pub struct FiniteActionContainer<const N: usize> {
    container: [Option<Action>; N],
    cursor: usize,
}

impl<const N: usize> IntoIterator for FiniteActionContainer<N> {
    type Item = Action;
    type IntoIter = FiniteActionContainerIntoIter<N>;

    fn into_iter(self) -> Self::IntoIter {
        FiniteActionContainerIntoIter {
            iter: self.container.into_iter(),
            item_count: 0,
        }
    }
}

impl<const N: usize> std::ops::Index<usize> for FiniteActionContainer<N> {
    type Output = Action;

    fn index(&self, index: usize) -> &Self::Output {
        self.container[index].as_ref().unwrap()
    }
}

impl<'a, const N: usize> FiniteActionContainer<N> {
    pub fn iter(&'a self) -> FiniteActionContainerIter<'a> {
        FiniteActionContainerIter {
            container: &self.container,
            cursor: 0,
        }
    }
}

/// Hacking trait for [`ActionContainer`].
///
/// The [`ActionContainer`] that implements trait [`MutableActionContainer`]
/// is no longer read-only; it has methods to construct and modify itself.
pub trait MutableActionContainer: ActionContainer {
    fn new() -> Self;

    fn push(&mut self, action: Action);
}

impl<const N: usize> MutableActionContainer for FiniteActionContainer<N> {
    fn new() -> Self {
        FiniteActionContainer {
            container: [None; N],
            cursor: 0,
        }
    }

    fn push(&mut self, action: Action) {
        if self.cursor >= N {
            panic!("index out of range");
        }
        self.container[self.cursor] = Some(action);
        self.cursor += 1;
    }
}

impl<const N: usize> ActionContainer for FiniteActionContainer<N> {
    fn len(&self) -> usize {
        self.cursor
    }

    fn is_empty(&self) -> bool {
        self.cursor == 0
    }

    fn contains(&self, action: Action) -> bool {
        for (i, a) in self.container.into_iter().enumerate() {
            if i >= self.cursor {
                return false;
            }
            if Some(action) == a {
                return true;
            }
        }
        false
    }
}

/// An [`Iterator`] returned by [`FiniteActionContainer::iter`]
pub struct FiniteActionContainerIter<'a> {
    container: &'a [Option<Action>],
    cursor: usize,
}

impl<'a> Iterator for FiniteActionContainerIter<'a> {
    type Item = &'a Action;

    fn next(&mut self) -> Option<Self::Item> {
        if self.cursor >= self.container.len() {
            return None;
        }

        let item = self.container[self.cursor].as_ref();
        if item.is_some() {
            self.cursor += 1;
        }
        item
    }
}

/// An [`Iterator`] returned by [`FiniteActionContainer::into_iter`]
pub struct FiniteActionContainerIntoIter<const N: usize> {
    iter: std::array::IntoIter<Option<Action>, N>,
    item_count: usize,
}

impl<const N: usize> Iterator for FiniteActionContainerIntoIter<N> {
    type Item = Action;

    fn next(&mut self) -> Option<Self::Item> {
        if self.item_count >= N {
            return None;
        }

        let item = self.iter.next()??;
        self.item_count += 1;
        Some(item)
    }
}

// *******************************************************************
//  Dove Container
// *******************************************************************
/// Read-only [`Sized`] container of [`Dove`]s without duplication.
#[derive(Debug, Clone, Copy)]
pub struct DoveSet {
    pub(super) hash: u8,
}

impl DoveSet {
    /// Returns `true` if it is empty.
    pub fn is_empty(&self) -> bool {
        self.hash == 0
    }

    /// Returns the number of elements.
    pub fn len(&self) -> usize {
        self.hash.count_ones() as usize
    }

    /// Returns `true` if it contains the specified [`Dove`].
    pub fn contains(&self, dove: Dove) -> bool {
        let bit = 1 << dove_to_index(dove);
        self.hash & bit != 0
    }
}

impl IntoIterator for DoveSet {
    type Item = Dove;
    type IntoIter = DoveSetIntoIter;
    fn into_iter(self) -> Self::IntoIter {
        DoveSetIntoIter::new(self)
    }
}

/// An [`Iterator`] returned by [`DoveSet::into_iter`]
pub struct DoveSetIntoIter {
    dove_set: DoveSet,
    cursor: u8,
}

impl DoveSetIntoIter {
    fn new(dove_set: DoveSet) -> Self {
        DoveSetIntoIter {
            dove_set,
            cursor: 1,
        }
    }
}

impl Iterator for DoveSetIntoIter {
    type Item = Dove;
    fn next(&mut self) -> Option<Self::Item> {
        if self.cursor.trailing_zeros() >= 6 {
            return None;
        }
        match (self.dove_set.hash & self.cursor).trailing_zeros() {
            idx @ 0..=5 => {
                let ret = try_index_to_dove(idx as usize);
                self.cursor <<= 1;
                if ret.is_none() {
                    unreachable!();
                }
                ret
            }
            8 => {
                self.cursor <<= 1;
                return self.next();
            }
            _ => unreachable!(),
        }
    }
}
