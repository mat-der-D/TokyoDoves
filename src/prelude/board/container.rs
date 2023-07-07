//! Container structs of some objects

use crate::prelude::{
    actions::Action,
    pieces::{dove_to_index, try_index_to_dove, Dove},
};

// *******************************************************************
//  Action Container
// *******************************************************************
/// Read-only [`Sized`] container of [`Action`]s.
///
/// This trait is sealed, i.e. it forces implementers to implement `Sealed` trait,
/// to prevent crate users from implementing this trait.
/// See also `https://sinkuu.github.io/api-guidelines/future-proofing.html#c-sealed`.
pub trait ActionContainer:
    Clone + IntoIterator<Item = Action> + std::ops::Index<usize, Output = Action> + private::Sealed
{
    /// Returns the number of elements.
    fn len(&self) -> usize;

    /// Returns `true` if it is empty.
    fn is_empty(&self) -> bool;

    /// Returns `true` if it contains the specified [`Action`].
    fn contains(&self, action: Action) -> bool;
}

pub mod private {
    pub trait Sealed {}
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

impl<const N: usize> private::Sealed for FiniteActionContainer<N> {}

impl<const N: usize> IntoIterator for FiniteActionContainer<N> {
    type Item = Action;
    type IntoIter = FiniteActionContainerIntoIter<N>;

    fn into_iter(self) -> Self::IntoIter {
        FiniteActionContainerIntoIter {
            iter: self.container.into_iter(),
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
            iter: self.container.iter(),
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
    iter: std::slice::Iter<'a, Option<Action>>,
}

impl<'a> Iterator for FiniteActionContainerIter<'a> {
    type Item = &'a Action;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()?.as_ref()
    }
}

/// An [`Iterator`] returned by [`FiniteActionContainer::into_iter`]
pub struct FiniteActionContainerIntoIter<const N: usize> {
    iter: std::array::IntoIter<Option<Action>, N>,
}

impl<const N: usize> Iterator for FiniteActionContainerIntoIter<N> {
    type Item = Action;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()?
    }
}

// *******************************************************************
//  Dove Container
// *******************************************************************
/// Read-only [`Sized`] container of [`Dove`]s without duplication.
#[derive(Debug, Clone, Copy)]
pub struct DoveSet {
    pub(crate) hash: u8,
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
                self.next()
            }
            _ => unreachable!(),
        }
    }
}
