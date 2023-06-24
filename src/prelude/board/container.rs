//! Container structs of some objects

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
            container: self.container,
            cursor: 0,
        }
    }
}

impl<const N: usize> std::ops::Index<usize> for FiniteActionContainer<N> {
    type Output = Action;

    fn index(&self, index: usize) -> &Self::Output {
        self.container[index].as_ref().unwrap()
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

/// An [`Iterator`] returned by [`FiniteActionContainer::into_iter`]
pub struct FiniteActionContainerIntoIter<const N: usize> {
    container: [Option<Action>; N],
    cursor: usize,
}

impl<const N: usize> Iterator for FiniteActionContainerIntoIter<N> {
    type Item = Action;

    fn next(&mut self) -> Option<Self::Item> {
        if self.cursor >= N {
            return None;
        }

        let item = self.container[self.cursor];
        if item.is_some() {
            self.cursor += 1;
        }
        item
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
        use Dove::*;
        let bit = match dove {
            B => 0b1,
            A => 0b10,
            Y => 0b100,
            M => 0b1000,
            T => 0b10000,
            H => 0b100000,
        };
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
        if self.cursor > (1 << 5) {
            return None;
        }
        use Dove::*;
        let dove = match self.dove_set.hash & self.cursor {
            0b0 => {
                self.cursor <<= 1;
                return self.next();
            }
            0b1 => B,
            0b10 => A,
            0b100 => Y,
            0b1000 => M,
            0b10000 => T,
            0b100000 => H,
            _ => unreachable!(),
        };
        self.cursor <<= 1;
        Some(dove)
    }
}
