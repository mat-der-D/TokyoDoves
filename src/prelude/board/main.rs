use strum::IntoEnumIterator;

use crate::error;

use crate::prelude::{
    actions::Action,
    pieces::{color_to_index, dove_to_index, Color, Dove},
    shift::Shift,
};

use crate::prelude::board::{
    bitutil::*, canonicalizer::*, container::*, mask::*, position::*, route::*,
};

pub use crate::prelude::board::{
    container::{ActionContainer, DoveSet, DoveSetIntoIter},
    display::{BoardDisplay, BoardDisplayFormat},
    mask::{Rectangle, RectangleSize},
};

// *******************************************************************
//  Utility Struct
// *******************************************************************
/// Inherited implementation for capsuling
macro_rules! impl_mutable_action_container {
    ( $($target:ident { $internal:ty, $iter:ident, $iter_name:expr, $into_iter:ident, $into_iter_name:expr })* ) => {
        $(
            impl std::fmt::Debug for $target {
                fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                    write!(f, "{:?}", self.0)
                }
            }

            impl<'a> std::fmt::Debug for $iter<'a> {
                fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                    let vec: Vec<&Action> = self.0.clone().collect();
                    f.debug_tuple($iter_name).field(&vec).finish()
                }
            }

            impl std::fmt::Debug for $into_iter {
                fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                    let vec: Vec<Action> = self.0.clone().collect();
                    f.debug_tuple($into_iter_name).field(&vec).finish()
                }
            }

            impl<'a> Iterator for $iter<'a> {
                type Item = &'a Action;
                fn next(&mut self) -> Option<Self::Item> {
                    self.0.next()
                }
            }

            impl Iterator for $into_iter {
                type Item = Action;
                fn next(&mut self) -> Option<Self::Item> {
                    self.0.next()
                }
            }

            impl IntoIterator for $target {
                type Item = Action;
                type IntoIter = $into_iter;
                fn into_iter(self) -> Self::IntoIter {
                    $into_iter(self.0.into_iter())
                }
            }

            impl std::ops::Index<usize> for $target {
                type Output = Action;
                fn index(&self, index: usize) -> &Self::Output {
                    self.0.index(index)
                }
            }

            impl private::Sealed for $target {}

            impl ActionContainer for $target {
                fn len(&self) -> usize {
                    self.0.len()
                }

                fn is_empty(&self) -> bool {
                    self.0.is_empty()
                }

                fn contains(&self, action: Action) -> bool {
                    self.0.contains(action)
                }
            }

            impl<'a> $target {
                pub fn iter(&'a self) -> $iter<'a> {
                    $iter(self.0.iter())
                }

                pub fn display_as_ssn(&self, board: &Board) -> Result<String, error::Error> {
                    self.0.display_as_ssn(board)
                }
            }

            impl<'a> IntoIterator for &'a $target {
                type Item = <<Self as IntoIterator>::IntoIter as Iterator>::Item;
                type IntoIter = $iter<'a>;
                fn into_iter(self) -> Self::IntoIter {
                    self.iter()
                }
            }

            impl MutableActionContainer for $target {
                fn new() -> Self {
                    Self(<$internal as MutableActionContainer>::new())
                }

                fn push(&mut self, cmd: Action) {
                    self.0.push(cmd)
                }
            }

        )*
    };
}

/// A read-only [`ActionContainer`] returned by
/// the [`legal_actions`](`Board::legal_actions`) method
/// on [`Board`].
///
/// Its contents are in the stack memory.
#[derive(Clone)]
pub struct ActionsFwd(FiniteActionContainer<64>);

/// An [`Iterator`] returned by
/// the [`iter`](`ActionsFwd::iter`) method
/// on [`ActionsFwd`].
#[derive(Clone)]
pub struct ActionsFwdIter<'a>(FiniteActionContainerIter<'a>);

/// An [`Iterator`] returned by
/// the [`into_iter`](`ActionsFwd::into_iter`) method
/// on [`ActionsFwd`].
#[derive(Clone)]
pub struct ActionsFwdIntoIter(FiniteActionContainerIntoIter<64>);

/// A read-only [`ActionContainer`] returned by
/// the [`legal_actions_bwd`](`Board::legal_actions_bwd`) method
/// on [`Board`].
///
/// Its contents are in the stack memory.
#[derive(Clone)]
pub struct ActionsBwd(FiniteActionContainer<100>);

/// An [`Iterator`] returned by
/// [`iter`](`ActionsBwd::iter`) method
/// on [`ActionsBwd`].
#[derive(Clone)]
pub struct ActionsBwdIter<'a>(FiniteActionContainerIter<'a>);

/// An [`Iterator`] returned by
/// the [`into_iter`](`ActionsBwd::into_iter`) method
/// on [`ActionsBwd`].
#[derive(Clone)]
pub struct ActionsBwdIntoIter(FiniteActionContainerIntoIter<100>);

impl_mutable_action_container! {
    ActionsFwd {
        FiniteActionContainer<64>,
        ActionsFwdIter, "ActionsFwdIter",
        ActionsFwdIntoIter, "ActionsFwdIntoIter"
    }
    ActionsBwd {
        FiniteActionContainer<100>,
        ActionsBwdIter, "ActionsBwdIter",
        ActionsBwdIntoIter, "ActionsBwdIntoIter"
    }
}

/// Represents whether two bosses are surrounded or not.
///
/// This enum is created by
/// the [`surrounded_status`](`Board::surrounded_status`) method
/// on [`Board`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SurroundedStatus {
    /// Both bosses are surrounded.
    ///
    /// # Examples
    /// ```text
    /// +---+---+---+---+
    /// | b | B | h |   |
    /// +---+---+---+---+
    /// | A | a |   | m |
    /// +---+---+---+---+
    /// |   |   | M |   |
    /// +---+---+---+---+
    /// |   | H |   | Y |
    /// +---+---+---+---+
    /// ```
    /// In this example,
    /// - red boss "B" is surrounded by "b", "h", "a" and a wall.
    /// - green boss "b" is surrounded by "B", "A" and two walls.
    Both,
    /// Only one boss is surrounded.
    ///
    /// # Examples
    /// ```text
    /// +---+---+---+---+
    /// | b |   | h |   |
    /// +---+---+---+---+
    /// | A | a | B | m |
    /// +---+---+---+---+
    /// |   |   | M |   |
    /// +---+---+---+---+
    /// |   | H |   | Y |
    /// +---+---+---+---+
    /// => OneSide(Color::Red)
    /// ```
    /// In this example,
    /// - red boss "B" is surrounded by "h", "a", "m" and "M".
    /// - the right side of green boss "b" is not occupied.
    OneSide(Color),
    /// None of bosses are surrounded.
    ///
    /// # Examples
    /// ```text
    /// +---+---+---+---+
    /// | b |   | h |   |
    /// +---+---+---+---+
    /// | A | a |   | m |
    /// +---+---+---+---+
    /// |   | B | M |   |
    /// +---+---+---+---+
    /// |   | H |   | Y |
    /// +---+---+---+---+
    /// ```
    /// In this example,
    /// - the left side of red boss "B" is not occupied.
    /// - the right side of green boss "b" is not occupied.
    None,
}

// *******************************************************************
//  Implement Traits
// *******************************************************************
/// A board of Tokyo Doves based on bitboard techniques.
///
/// See [the documentation at the top of this crate](`crate`)
/// for quick start examples.
#[derive(Clone, Copy)]
pub struct Board {
    pub(crate) viewer: MaskViewer,
    pub(crate) positions: ColorDovePositions,
}

impl std::fmt::Debug for Board {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Board({:?})", self.to_simple_string(' ', ";"))
    }
}

impl Board {
    pub(crate) fn from_components(viewer: MaskViewer, positions: ColorDovePositions) -> Self {
        Self { viewer, positions }
    }
}

impl std::fmt::Display for Board {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.to_framed_string())
    }
}

impl PartialEq for Board {
    fn eq(&self, other: &Self) -> bool {
        self.to_u64() == other.to_u64()
    }
}

impl Eq for Board {}

impl Default for Board {
    fn default() -> Self {
        Self::new()
    }
}

impl std::hash::Hash for Board {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        state.write_u64(self.to_u64());
    }
}

impl Board {
    /// Creates [`Board`] at the beginning of the game.
    ///
    /// # Examples
    /// The following two ways are equivalent:
    /// ```rust
    /// use tokyodoves::{Board, BoardBuilder};
    ///
    /// let board1 = Board::new();
    /// let board2 = BoardBuilder::new().build_unchecked();
    /// assert_eq!(board1, board2);
    /// ```
    /// [`BoardBuilder`](`crate::prelude::BoardBuilder`) provides
    /// a variety of ways to create [`Board`].
    pub fn new() -> Self {
        crate::prelude::builder::BoardBuilder::new().build_unchecked()
    }

    // *******************************************************************
    //  Methods For Peforming Actions
    // *******************************************************************
    /// Performs the specified `action` to `self`.
    ///
    /// # Errors
    /// Returns `Err` if performing the specified `action` is illegal.
    /// `self` will not be changed when this method returns `Err`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use tokyodoves::{Board, Action, Color, Dove, Shift};
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut board = Board::new();
    /// let action = Action::Put(Color::Red, Dove::A, Shift::new(0, 1));
    /// let result = board.perform(action);
    /// assert!(result.is_ok());
    /// # Ok(())
    /// # }
    /// ```
    pub fn perform(&mut self, action: Action) -> Result<(), error::Error> {
        self.check_action(action)?;
        self.perform_unchecked_raw(action)?;
        Ok(())
    }

    /// Returns the result of the [`perform`](`Board::perform`) method
    /// without changing `self`.
    ///
    /// # Errors
    /// Returns `Err` if performing the specified `action` is illegal.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use tokyodoves::{Board, Action, Color, Dove, Shift};
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let board = Board::new();
    /// let action = Action::Put(Color::Red, Dove::A, Shift::new(0, 1));
    /// let next_board = board.perform_copied(action)?;
    /// # Ok(())
    /// # }
    /// ```
    /// The code above is almost equivalent to the following.
    /// ```rust
    /// use tokyodoves::{Board, Action, Color, Dove, Shift};
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let board = Board::new();
    /// let action = Action::Put(Color::Red, Dove::A, Shift::new(0, 1));
    /// let mut next_board = board; // copied
    /// next_board.perform(action)?;
    /// # Ok(())
    /// # }
    /// ```
    pub fn perform_copied(&self, action: Action) -> Result<Self, error::Error> {
        let mut board = *self;
        board.perform(action)?;
        Ok(board)
    }

    /// Performs the specified action to `self`. The action is checked in backward direction.
    ///
    /// The action (A) is legal in backward direction
    /// if there is such a legal action (B) that
    /// performing B to the board after A results in the board before A.
    ///
    /// # Errors
    /// Returns `Err` if performing the specified `action` is illegal in backward direction.
    /// `self` will not be changed when this method returns `Err`.
    ///
    /// # Examples
    /// ```rust
    /// use tokyodoves::{Board, Action, Color, Dove, Shift};
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut board = Board::new();
    /// let action = Action::Put(Color::Red, Dove::A, Shift::new(-1, 1));
    /// let result = board.perform_bwd(action);
    /// assert!(result.is_ok());
    /// # Ok(())
    /// # }
    /// ```
    pub fn perform_bwd(&mut self, action: Action) -> Result<(), error::Error> {
        self.check_action_bwd(action)?;
        self.perform_unchecked_raw(action)?;
        Ok(())
    }

    /// Returns the result of the [`perform_bwd`](`Board::perform_bwd`) method
    /// without changing `self`.
    ///
    /// # Errors
    /// Returns `Err` if performing the specified `action` is illegal in backward direction.
    ///
    /// # Examples
    /// ```rust
    /// use tokyodoves::{Board, Action, Color, Dove, Shift};
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let board = Board::new();
    /// let action = Action::Put(Color::Red, Dove::A, Shift::new(0, 1));
    /// let next_board = board.perform_bwd_copied(action)?;
    /// # Ok(())
    /// # }
    /// ```
    /// The code above is almost equivalent to the following.
    /// ```rust
    /// use tokyodoves::{Board, Action, Color, Dove, Shift};
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let board = Board::new();
    /// let action = Action::Put(Color::Red, Dove::A, Shift::new(0, 1));
    /// let mut next_board = board; // copied
    /// next_board.perform_bwd(action)?;
    /// # Ok(())
    /// # }
    /// ```
    pub fn perform_bwd_copied(&self, action: Action) -> Result<Self, error::Error> {
        let mut board = *self;
        board.perform_bwd(action)?;
        Ok(board)
    }

    /// Performs `action` to `self` without legality check.
    ///
    /// It may return `Ok(())` even if the specified `action` is illegal in both forward and backward directions.
    /// In such a case, the resulting board may (or may not) violate the rule (e.g. some dove would be isolated from others).
    /// If you are not sure that the action is legal, consider to select one of the following choices:
    /// - Call the [`check_action`](`Self::check_action`) method
    ///     or the [`check_action_bwd`](`Self::check_action_bwd`) method
    ///     to check legality in advance.
    /// - Call the [`perform`](`Self::perform`) method
    ///     or the [`perform_bwd`](`Self::perform_bwd`) method insted,
    ///     which calls the [`check_action`](`Self::check_action`) method
    ///     or the [`check_action_bwd`](`Self::check_action_bwd`) method internally.
    ///
    /// Note that this method is faster than
    /// the methods [`perform`](`Self::perform`) and [`perform_bwd`](`Self::perform_bwd`)
    /// thanks to absence of legality check.
    ///
    /// # Panics
    /// Panics if the action is [`Move`](`Action::Move`) or [`Put`](`Action::Put`),
    /// and the target position is more than two squares
    /// far from the current 4x4 field (, which are clearly illegal).
    /// `self` will not be changed when this method returns `Err`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use tokyodoves::{Board, Action, Color, Dove, Shift};
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut board = Board::new();
    /// let action = Action::Put(Color::Red, Dove::A, Shift::new(0, 1));
    /// board.perform_unchecked(action);
    /// # Ok(())
    /// # }
    /// ```
    pub fn perform_unchecked(&mut self, action: Action) {
        self.perform_unchecked_raw(action).unwrap();
    }

    fn perform_unchecked_raw(&mut self, action: Action) -> Result<(), error::Error> {
        use Action::*;
        match action {
            Put(c, d, s) => {
                let boss_pos = self.positions.position_of(c, Dove::B);
                let pos = apply_shift(*boss_pos, s);
                self.viewer
                    .shift_toward(pos)
                    .map_err(|_| error::BoardError::MaskShiftError)?;
                self.positions.set_position(c, d, pos);
            }
            Move(c, d, s) => {
                let pos_now = self.positions.position_of(c, d);
                let pos_next = apply_shift(*pos_now, s);
                self.viewer
                    .shift_toward(pos_next)
                    .map_err(|_| error::BoardError::MaskShiftError)?;
                self.positions.set_position(c, d, pos_next);
            }
            Remove(c, d) => self.positions.set_position(c, d, 0),
        }
        Ok(())
    }

    /// Returns the result of the [`perform_unchecked`](`Board::perform_unchecked`) method
    /// without changing `self`.
    ///
    /// # Panics
    /// Panics if the action is [`Move`](`Action::Move`) or [`Put`](`Action::Put`),
    /// and the target position is more than two squares
    /// far from the current 4x4 field (, which are clearly illegal).
    ///
    /// # Examples
    ///
    /// ```rust
    /// use tokyodoves::{Board, Action, Color, Dove, Shift};
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let board = Board::new();
    /// let action = Action::Put(Color::Red, Dove::A, Shift::new(0, 1));
    /// let next_board = board.perform_unchecked_copied(action);
    /// # Ok(())
    /// # }
    /// ```
    /// The code above is almost equivalent to the following.
    /// ```rust
    /// use tokyodoves::{Board, Action, Color, Dove, Shift};
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let board = Board::new();
    /// let action = Action::Put(Color::Red, Dove::A, Shift::new(0, 1));
    /// let mut next_board = board; // copied
    /// next_board.perform_unchecked(action);
    /// # Ok(())
    /// # }
    /// ```
    pub fn perform_unchecked_copied(&self, action: Action) -> Self {
        let mut board = *self;
        board.perform_unchecked(action);
        board
    }

    // *******************************************************************
    //  Methods For Actions Check
    // *******************************************************************
    /// Returns `Ok(())` if the given `action` is legal.
    ///
    /// # Errors
    /// Returns `Err` if performing the specified `action` is illegal.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use tokyodoves::{Board, Action, Color, Dove, Shift};
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut board = Board::new();
    /// let action = Action::Put(Color::Red, Dove::A, Shift::new(0, 1));
    /// assert!(board.check_action(action).is_ok());
    /// # Ok(())
    /// # }
    /// ```
    pub fn check_action(&self, action: Action) -> Result<(), error::Error> {
        self.check_action_core(action, true)
    }

    /// Check if backward `action` is legal in backward direction.
    ///
    /// The action (A) is legal in backward direction
    /// if there is such a legal action (B) that
    /// performing B to the board after A results in the board before A.
    ///
    /// # Errors
    /// Returns `Err` if performing the specified `action` is illegal in backward direction.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use tokyodoves::{Board, Action, Color, Dove, Shift};
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut board = Board::new();
    /// let action = Action::Put(Color::Red, Dove::A, Shift::new(-1, 1));
    /// assert!(board.check_action_bwd(action).is_ok());
    /// # Ok(())
    /// # }
    /// ```
    pub fn check_action_bwd(&self, action: Action) -> Result<(), error::Error> {
        self.check_action_core(action, false)
    }

    fn check_action_core(&self, action: Action, fwd: bool) -> Result<(), error::Error> {
        use Action::*;
        match action {
            Put(c, d, s) => self.check_put(c, d, s, fwd),
            Move(c, d, s) => self.check_move(c, d, s),
            Remove(c, d) => self.check_remove(c, d, fwd),
        }
    }

    // Methods for check_action, check_action_bwd
    fn check_put(&self, c: Color, d: Dove, s: Shift, fwd: bool) -> Result<(), error::Error> {
        use error::ActionPerformErrorKind::*;
        fn _restore_cmd(c_: Color, d_: Dove, s_: Shift) -> Action {
            Action::Put(c_, d_, s_)
        }

        if *self.positions.position_of(c, d) != 0 {
            return Err((AlreadyOnBoard, _restore_cmd(c, d, s)).into());
        }
        if s.dh < -3 || s.dh > 3 || s.dv < -3 || s.dv > 3 {
            return Err((InvalidShift, _restore_cmd(c, d, s)).into());
        }
        let boss_pos = self.positions.position_of(c, Dove::B);
        let pos = apply_shift(*boss_pos, s);
        let Ok(next_mask) = self.viewer.view_mask_at(pos) else {
            return Err((OutOfField, _restore_cmd(c, d, s)).into());
        };

        let all = self.positions.union();
        if all & next_mask.core != all {
            return Err((OutOfField, _restore_cmd(c, d, s)).into());
        }

        if fwd {
            let another_boss_pos = self.positions.position_of(!c, Dove::B);
            let another_boss_sides = sides_of_bit(*another_boss_pos);
            let adj_ours = calc_adjacents(self.positions.union_in_color(c));
            if pos & !all & !another_boss_sides & adj_ours != pos {
                return Err((InvalidPosition, _restore_cmd(c, d, s)).into());
            }
        } else {
            let adj_all = calc_adjacents(all);
            if pos & !all & adj_all != pos {
                return Err((InvalidPosition, _restore_cmd(c, d, s)).into());
            }
        }

        Ok(())
    }

    fn check_move(&self, c: Color, d: Dove, s: Shift) -> Result<(), error::Error> {
        use error::ActionPerformErrorKind::*;

        fn _restore_cmd(c_: Color, d_: Dove, s_: Shift) -> Action {
            Action::Move(c_, d_, s_)
        }

        let pos = self.positions.position_of(c, d);
        if *pos == 0 {
            return Err((NotOnBoard, _restore_cmd(c, d, s)).into());
        }
        let mut new_pos = 0;
        let mut route = 0_u64;
        let mut found = false;
        for (p, r, (dh, dv)) in bit_route_shift(*pos, d) {
            if (s.dh, s.dv) == (*dh, *dv) {
                found = true;
                route = *r;
                new_pos = *p;
                break;
            }
        }
        if !found {
            return Err((InvalidShift, _restore_cmd(c, d, s)).into());
        }

        let others = self.positions.union_except(c, d);
        if route & others != 0 {
            return Err((ObstacleInRoute, _restore_cmd(c, d, s)).into());
        }

        let outfield = self.viewer.view_mask().outfield;
        if route & outfield != 0 {
            return Err((ThroughOuterField, _restore_cmd(c, d, s)).into());
        }

        let Ok(new_mask) = self.viewer.view_mask_at(new_pos) else {
            return Err((OutOfField, _restore_cmd(c, d, s)).into());
        };
        if others & !new_mask.core != 0 {
            return Err((OutOfField, _restore_cmd(c, d, s)).into());
        }

        let adj_others = calc_adjacents(others);
        let adj_new_pos = adjacents_of_bit(new_pos);
        if (others | new_pos) & !adj_others & !adj_new_pos != 0 {
            return Err((ToBeIsolated, _restore_cmd(c, d, s)).into());
        }

        Ok(())
    }

    fn check_remove(&self, c: Color, d: Dove, fwd: bool) -> Result<(), error::Error> {
        use error::ActionPerformErrorKind::*;

        fn _restore_cmd(c_: Color, d_: Dove) -> Action {
            Action::Remove(c_, d_)
        }

        if matches!(d, Dove::B) {
            return Err((TriedToRemoveBoss, _restore_cmd(c, d)).into());
        }
        let pos = self.positions.position_of(c, d);
        if *pos == 0 {
            return Err((NotOnBoard, _restore_cmd(c, d)).into());
        }

        if !fwd {
            let another_boss_pos = self.positions.position_of(!c, Dove::B);
            let another_boss_sides = sides_of_bit(*another_boss_pos);
            let adj_ours = calc_adjacents(self.positions.union_in_color(c));

            if pos & !another_boss_sides & adj_ours != *pos {
                return Err((InvalidPosition, _restore_cmd(c, d)).into());
            }
        }

        let others = self.positions.union_except(c, d);
        if others & !calc_adjacents(others) != 0 {
            return Err((ToBeIsolated, _restore_cmd(c, d)).into());
        }
        Ok(())
    }

    // *******************************************************************
    //  Methods For Legal Action Search
    // *******************************************************************
    /// Collects and returns all legal [`Action`]s
    /// performed by the specified player.
    ///
    /// Three boolean arguments ---
    /// `contains_put`, `contains_move` and `contains_remove` ---
    /// specify what kinds of [`Action`]s should be contained.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use tokyodoves::{Board, Color};
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let board = Board::new();
    /// let actions = board.legal_actions(Color::Red, true, true, true);
    /// for action in actions {
    ///     println!("{}", board.perform_copied(action)?);
    /// }
    /// # Ok(())
    /// # }
    /// ```
    pub fn legal_actions(
        &self,
        player: Color,
        contains_put: bool,
        contains_move: bool,
        contains_remove: bool,
    ) -> ActionsFwd {
        self.legal_actions_base::<ActionsFwd>(
            player,
            contains_put,
            contains_move,
            contains_remove,
            true,
        )
    }

    /// Collects and returns all [`Action`]s legal in backward direction
    /// performed by the specified player.
    ///
    /// Three boolean arguments ---
    /// `contains_put`, `contains_move` and `contains_remove` ---
    /// specify what kinds of [`Action`]s should be contained.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use tokyodoves::{Board, Color};
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let board = Board::new();
    /// let actions = board.legal_actions_bwd(Color::Red, true, true, true);
    /// for action in actions {
    ///     println!("{}", board.perform_bwd_copied(action)?);
    /// }
    /// # Ok(())
    /// # }
    /// ```
    pub fn legal_actions_bwd(
        &self,
        player: Color,
        contains_put: bool,
        contains_move: bool,
        contains_remove: bool,
    ) -> ActionsBwd {
        self.legal_actions_base::<ActionsBwd>(
            player,
            contains_put,
            contains_move,
            contains_remove,
            false,
        )
    }

    fn legal_actions_base<T: MutableActionContainer>(
        &self,
        player: Color,
        contains_put: bool,
        contains_move: bool,
        contains_remove: bool,
        fwd: bool,
    ) -> T {
        let mut actions = T::new();
        if contains_put {
            self.pack_puts(&mut actions, player, fwd);
        }
        if contains_move {
            self.pack_moves(&mut actions, player);
        }
        if contains_remove {
            self.pack_removes(&mut actions, player, fwd);
        }
        actions
    }

    fn pack_puts(&self, actions: &mut impl MutableActionContainer, player: Color, fwd: bool) {
        let doves_in_hand = self.positions.doves_in_hand(player);
        // skip if no dove is in hand
        if !doves_in_hand.is_empty() {
            let mut mask_sum = self.viewer.view_mask().core;
            let all = self.positions.union();
            for direction in Direction::iter() {
                let mask = self.viewer.view_next_mask(direction);
                if all & mask.core == all {
                    mask_sum |= mask.core;
                }
            }

            let possibles = if fwd {
                let another_boss_pos = self.positions.position_of(!player, Dove::B);
                let another_boss_sides = sides_of_bit(*another_boss_pos);
                let adj_ours = calc_adjacents(self.positions.union_in_color(player));
                mask_sum & !all & !another_boss_sides & adj_ours
            } else {
                let adj_all = calc_adjacents(all);
                mask_sum & !all & adj_all
            };

            let boss_pos = self.positions.position_of(player, Dove::B);
            for dst in HotBitIter::from(possibles) {
                let shift = create_shift_from_bits(*boss_pos, dst);
                for d in doves_in_hand {
                    actions.push(Action::Put(player, d, shift));
                }
            }
        }
    }

    fn pack_moves(&self, actions: &mut impl MutableActionContainer, player: Color) {
        let doves_on_field = self.positions.doves_on_field(player);
        let outfield = self.viewer.view_mask().outfield;
        for d in doves_on_field {
            let pos_now = self.positions.position_of(player, d);
            let others = self.positions.union_except(player, d);
            let adj_others = calc_adjacents(others);
            for (pos_next, route, (dh, dv)) in bit_route_shift(*pos_now, d) {
                if route & (others | outfield) != 0 {
                    continue; // obstacle in route
                }

                let Ok(next_mask) = self.viewer.view_mask_at(*pos_next) else {
                    continue // out of field
                };

                if others & !next_mask.core != 0 {
                    continue; // out of field
                }

                let adj_pos_next = adjacents_of_bit(*pos_next);
                if (others | pos_next) & !adj_others & !adj_pos_next != 0 {
                    continue; // isolated
                }

                // passed all checks
                let shift = Shift { dh: *dh, dv: *dv };
                actions.push(Action::Move(player, d, shift));
            }
        }
    }

    fn pack_removes(&self, actions: &mut impl MutableActionContainer, player: Color, fwd: bool) {
        let doves_on_field = self.positions.doves_on_field(player);
        // skip if only the boss is on the field
        if doves_on_field.len() > 1 {
            let adj_ours: u64;
            let another_boss_sides: u64;
            if fwd {
                adj_ours = 0;
                another_boss_sides = 0;
            } else {
                adj_ours = calc_adjacents(self.positions.union_in_color(player));
                let another_boss_pos = self.positions.position_of(!player, Dove::B);
                another_boss_sides = sides_of_bit(*another_boss_pos);
            }

            for d in doves_on_field {
                if matches!(d, Dove::B) {
                    continue;
                }

                if !fwd {
                    let pos = self.positions.position_of(player, d);
                    if pos & !another_boss_sides & adj_ours != *pos {
                        continue;
                    }
                }

                let others = self.positions.union_except(player, d);
                if others & calc_adjacents(others) != others {
                    continue;
                }
                actions.push(Action::Remove(player, d));
            }
        }
    }

    /// Swaps the colors red and green.
    ///
    /// # Examples
    /// ```rust
    /// use std::str::FromStr;
    /// use tokyodoves::BoardBuilder;
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    ///
    /// let mut board1 = BoardBuilder::from_str("BbA")?.build()?;
    /// let board2 = BoardBuilder::from_str("bBa")?.build()?;
    /// board1.swap_color();
    /// assert_eq!(board1, board2);
    /// # Ok(())
    /// # }
    /// ```
    pub fn swap_color(&mut self) {
        self.positions.swap_color();
    }

    // *******************************************************************
    //  Information
    // *******************************************************************
    /// Returns the position of specified player and dove in
    /// Red-Boss-Centered Coordinate (RBCC).
    ///
    /// `dv` and `dh` in RBCC is shown in below (B is red boss):
    ///
    /// ```text
    ///     dh  -3   -2   -1    0    +1   +2   +3
    ///   dv  +----+----+----+-----+----+----+----+
    ///   -3  |    |    |    |     |    |    |    |
    ///       +----+----+----+-----+----+----+----+
    ///   -2  |    |    |    |     |    |    |    |
    ///       +----+----+----+-----+----+----+----+
    ///   -1  |    |    |    |     |    |    |    |
    ///       +----+----+----+-----+----+----+----+
    ///    0  |    |    |    |  B  |    |    |    |
    ///       +----+----+----+-----+----+----+----+
    ///   +1  |    |    |    |     |    |    |    |
    ///       +----+----+----+-----+----+----+----+
    ///   +2  |    |    |    |     |    |    |    |
    ///       +----+----+----+-----+----+----+----+
    ///   +3  |    |    |    |     |    |    |    |
    ///       +----+----+----+-----+----+----+----+
    /// ```
    ///
    /// It returns `None` if specified dove is not found on the field.
    pub fn position_in_rbcc(&self, player: Color, dove: Dove) -> Option<Shift> {
        let pos = self.positions.position_of(player, dove);
        if *pos == 0 {
            return None;
        }
        let red_boss_pos = self.positions.position_of(Color::Red, Dove::B);
        let shift = create_shift_from_bits(*red_boss_pos, *pos);
        Some(shift)
    }

    /// Counts the number of all doves on the field.
    ///
    /// # Examples
    /// ```rust
    /// use tokyodoves::Board;
    ///
    /// let board = Board::new();
    /// assert_eq!(board.count_doves_on_field(), 2);
    /// ```
    pub fn count_doves_on_field(&self) -> usize {
        self.positions.union().count_ones() as usize
    }

    /// Counts the number of doves of the `player` on the field.
    ///
    /// # Examples
    /// ```rust
    /// use tokyodoves::{Board, Color};
    ///
    /// let board = Board::new();
    /// assert_eq!(board.count_doves_on_field_of(Color::Red), 1);
    /// ```
    pub fn count_doves_on_field_of(&self, player: Color) -> usize {
        self.positions.union_in_color(player).count_ones() as usize
    }

    /// Collects and returns the set of doves in the `player`'s hand.
    ///
    /// # Examples
    /// ```rust
    /// use tokyodoves::{Board, Color};
    ///
    /// let board = Board::new();
    /// for dove in board.doves_in_hand_of(Color::Red) {
    ///     println!("{:?}", dove); // A, Y, M, T, H
    /// }
    /// ```
    pub fn doves_in_hand_of(&self, player: Color) -> DoveSet {
        self.positions.doves_in_hand(player)
    }

    /// Collects and returns the set of doves of the `player` on the field.
    ///
    /// # Examples
    /// ```rust
    /// use tokyodoves::{Board, Color};
    ///
    /// let board = Board::new();
    /// for dove in board.doves_on_field_of(Color::Red) {
    ///     println!("{:?}", dove); // B
    /// }
    /// ```
    pub fn doves_on_field_of(&self, player: Color) -> DoveSet {
        self.positions.doves_on_field(player)
    }

    /// Returns `true` if the `player`'s `dove` is on the field.
    ///
    /// # Examples
    /// ```rust
    /// use tokyodoves::{Board, Color, Dove};
    ///
    /// let board = Board::new();
    /// assert!(board.is_on_field(Color::Red, Dove::B));
    /// assert!(!board.is_on_field(Color::Green, Dove::A));
    /// ```
    pub fn is_on_field(&self, player: Color, dove: Dove) -> bool {
        *self.positions.position_of(player, dove) != 0
    }

    /// Returns `true` if the `player`'s `dove` is in their hand.
    ///
    /// # Examples
    /// ```rust
    /// use tokyodoves::{Board, Color, Dove};
    ///
    /// let board = Board::new();
    /// assert!(board.is_in_hand(Color::Green, Dove::A));
    /// assert!(!board.is_in_hand(Color::Red, Dove::B));
    /// ```
    pub fn is_in_hand(&self, player: Color, dove: Dove) -> bool {
        *self.positions.position_of(player, dove) == 0
    }

    /// Returns "liberty" of `player`'s `dove`,
    /// where liberty is the number of free squares
    /// next to the specified dove.
    ///
    /// Note that `None` and `Some(0)` have different meanings;
    /// `None` means that the specified dove is not on the board
    /// while `Some(0)` means that the specified dove is on the field
    /// and completely surrounded.
    ///
    /// # Examples
    /// ```text
    /// +---+---+---+---+
    /// | b | T |   |   |
    /// +---+---+---+---+
    /// |   | B |   |   |
    /// +---+---+---+---+
    /// |   | a | H | M |
    /// +---+---+---+---+
    /// |   |   | m |   |
    /// +---+---+---+---+
    /// ```
    /// In this case, the liberty of "B" is two.
    /// The liberty of "T" is one,
    /// because three of four squares next to "T" is occupied
    /// by "B", "b" and a wall.
    /// ```rust
    /// use std::str::FromStr;
    /// use tokyodoves::{BoardBuilder, Color, Dove};
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let board = BoardBuilder::from_str("bT; B; aHM;  m")?.build()?;
    /// assert_eq!(Some(2), board.liberty(Color::Red, Dove::B));
    /// assert_eq!(Some(1), board.liberty(Color::Red, Dove::T));
    /// assert_eq!(None, board.liberty(Color::Green, Dove::H)); // not on field
    /// # Ok(())
    /// # }
    /// ```
    pub fn liberty(&self, player: Color, dove: Dove) -> Option<usize> {
        let all = self.positions.union();
        let walls = self.viewer.view_mask().calc_wall_bits(all);
        let pos = self.positions.position_of(player, dove);
        if *pos == 0 {
            return None;
        }
        let sides = sides_of_bit(*pos);
        Some((sides & !all & !walls).count_ones() as usize)
    }

    /// Returns "liberty" of `player`'s boss-hato.
    ///
    /// The meaning of liberty is written in the description
    /// of the [`liberty`](`Self::liberty`) method.
    /// A player loses when the liberty of their boss-hato becomes 0.
    ///
    /// # Panics
    /// Panics if `player`'s boss is not on the field,
    /// which does not happen in normal play.
    ///
    /// # Examples
    /// ```text
    /// +---+---+---+---+
    /// | b | T |   |   |
    /// +---+---+---+---+
    /// |   | B |   |   |
    /// +---+---+---+---+
    /// |   | a | H | M |
    /// +---+---+---+---+
    /// |   |   | m |   |
    /// +---+---+---+---+
    /// ```
    /// ```rust
    /// use std::str::FromStr;
    /// use tokyodoves::{BoardBuilder, Color, Dove};
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let board = BoardBuilder::from_str("bT; B; aHM;  m")?.build()?;
    /// assert_eq!(2, board.liberty_of_boss(Color::Red));
    /// assert_eq!(1, board.liberty_of_boss(Color::Green));
    /// # Ok(())
    /// # }
    /// ```
    pub fn liberty_of_boss(&self, player: Color) -> usize {
        self.liberty(player, Dove::B).unwrap()
    }

    /// Returns information about whether bosses are surrounded or not.
    ///
    /// See the description of [`SurroundedStatus`] for detail.
    ///
    /// # Examples
    /// ```rust
    /// use std::str::FromStr;
    /// use tokyodoves::{BoardBuilder, Color, Dove, SurroundedStatus};
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let board1 = BoardBuilder::from_str("bBh;Aa m;  M; H Y")?.build()?;
    /// let board2 = BoardBuilder::from_str("b h;AaBm;  M; H Y")?.build()?;
    /// let board3 = BoardBuilder::from_str("b h;Aa m; BM ; H Y")?.build()?;
    ///
    /// assert_eq!(SurroundedStatus::Both, board1.surrounded_status());
    /// assert_eq!(
    ///     SurroundedStatus::OneSide(Color::Red),
    ///     board2.surrounded_status()
    /// );
    /// assert_eq!(SurroundedStatus::None, board3.surrounded_status());
    /// # Ok(())
    /// # }
    pub fn surrounded_status(&self) -> SurroundedStatus {
        let lib_red = self.liberty_of_boss(Color::Red);
        let lib_green = self.liberty_of_boss(Color::Green);
        use SurroundedStatus::*;
        match (lib_red, lib_green) {
            (0, 0) => Both,
            (0, _) => OneSide(Color::Red),
            (_, 0) => OneSide(Color::Green),
            (_, _) => None,
        }
    }

    /// Returns the minimum rectangle
    /// that contains all doves on the field.
    ///
    /// It has fields `hmin`, `hmax`, `vmin` and `vmax`,
    /// standing for coordinates of edges of the rectangle.
    ///
    /// # Examples
    ///
    /// ```text
    /// [Case 1]
    ///     0   1   2   3
    ///   +---+---+---+---+
    /// 0 | b |   | T |   |
    ///   +---+---+---+---+
    /// 1 |   | B | a |   |
    ///   +---+---+---+---+
    /// 2 |   |   |   |   |
    ///   +---+---+---+---+
    /// 3 |   |   |   |   |
    ///   +---+---+---+---+
    /// -> hmin=0, hmax=2, vmin=0, vmax=1
    ///
    /// [Case 2]
    ///     0   1   2   3
    ///   +---+---+---+---+
    /// 0 |   |   |   |   |
    ///   +---+---+---+---+
    /// 1 |   | b |   |   |
    ///   +---+---+---+---+
    /// 2 | a |   | H | B |
    ///   +---+---+---+---+
    /// 3 |   |   |   |   |
    ///   +---+---+---+---+
    /// -> hmin=0, hmax=3, vmin=1, vmax=2
    ///
    /// [Case 3]
    ///     0   1   2   3
    ///   +---+---+---+---+
    /// 0 |   |   |   |   |
    ///   +---+---+---+---+
    /// 1 |   |   |   |   |
    ///   +---+---+---+---+
    /// 2 |   |   |   |   |
    ///   +---+---+---+---+
    /// 3 | h | B | b | Y |
    ///   +---+---+---+---+
    /// -> hmin=0, hmax=3, vmin=3, vmax=3
    /// ```
    pub fn minimum_rectangle(&self) -> Rectangle {
        let all = self.positions.union();
        let mask = self.viewer.view_mask();
        mask.minimum_rectangle(all)
    }

    // *******************************************************************
    //  Methods For Conversion
    // *******************************************************************
    /// Returns a light expression of a `Board` in `u64`.
    ///
    /// 64 bits consist of the following three parts:
    /// - Top 4 bits: empty (filled by 0)
    /// - Next 12 bits: each bit means that each kind of dove is on the field (1) or not (0)
    /// - Next 48 bits: positions of doves are expressed by 0~15, which consumes 4 bits per one dove
    ///     (4 bits x 12 doves = 48 bits)
    ///
    /// The order of 12 doves is "B > b > A > a > Y > y > M > m > T > t > H > h",
    /// where capital/lower cases mean red/green dove, respectively.
    ///
    /// # Examples
    /// Initial board:
    /// ```text
    /// +---+---+---+---+     +---+---+---+---+
    /// | b |   |   |   |     | 0 | 1 | 2 | 3 |
    /// +---+---+---+---+     +---+---+---+---+
    /// | B |   |   |   |     | 4 | 5 | 6 | 7 |
    /// +---+---+---+---+ <=> +---+---+---+---+
    /// |   |   |   |   |     | 8 | 9 |10 |11 |
    /// +---+---+---+---+     +---+---+---+---+
    /// |   |   |   |   |     |12 |13 |14 |15 |
    /// +---+---+---+---+     +---+---+---+---+
    /// ```
    /// As a code:
    /// ```rust
    /// use tokyodoves::Board;
    ///
    /// let board = Board::new();
    /// let top_4 = 0b0000;
    /// let next_12 = 0b110000_000000; // B + b
    /// let next_48 = 4 << 44 | 0 << 40; // B at 4 + b at 0
    /// let hash = top_4 << 60 | next_12 << 48 | next_48;
    /// assert_eq!(board.to_u64(), hash);
    /// ```
    pub fn to_u64(&self) -> u64 {
        let mut hash = 0;
        for d in Dove::iter() {
            let id = dove_to_index(d);
            for c in Color::iter() {
                let ic = color_to_index(c);
                let pos = self.positions.position_of(c, d);
                if *pos == 0 {
                    continue;
                }
                let ishift = 11 - (2 * id + ic);
                let Some(ipos) = self.viewer.view_mask().field_idx(*pos) else {
                    continue;
                };
                hash |= (ipos as u64) << (4 * ishift);
                hash |= 1_u64 << (48 + ishift);
            }
        }
        hash
    }

    /// Returns a light expression of `u64` invariant under reflection, rotation and translation
    /// transformations.
    ///
    /// The composition of the returned value is the same as that of [`to_u64`](`Self::to_u64`).
    /// This method returns the same value for boards that
    /// - coinside with each other under reflection, rotation, translation, and any compositions of them.
    /// - coinside with each other after alternating next player and swapping colors of doves simultaneously.
    ///
    /// # Examples
    /// Boards
    /// ```text
    /// +---+---+---+---+
    /// | b | B |   |   |
    /// +---+---+---+---+
    /// |   | H |   |   |
    /// +---+---+---+---+
    /// |   | y |   |   |
    /// +---+---+---+---+
    /// |   |   |   |   |
    /// +---+---+---+---+
    /// ```
    /// and
    /// ```text
    /// +---+---+---+---+
    /// |   |   |   |   |
    /// +---+---+---+---+
    /// |   | b |   |   |
    /// +---+---+---+---+
    /// |   | B | H | y |
    /// +---+---+---+---+
    /// |   |   |   |   |
    /// +---+---+---+---+
    /// ```
    /// viewed from red and
    /// ```text
    /// +---+---+---+---+
    /// |   |   |   |   |
    /// +---+---+---+---+
    /// |   | B |   |   |
    /// +---+---+---+---+
    /// |   | b | h | Y |
    /// +---+---+---+---+
    /// |   |   |   |   |
    /// +---+---+---+---+
    /// ```
    /// viewed from green
    /// return the same values.
    /// ```rust
    /// use std::str::FromStr;
    /// use tokyodoves::{BoardBuilder, Color};
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let board1 = BoardBuilder::from_str("bB; H; y")?.build()?;
    /// let hash1 = board1.to_invariant_u64(Color::Red);
    /// let board2 = BoardBuilder::from_str("; b; BHy")?.build()?;
    /// let hash2 = board2.to_invariant_u64(Color::Red);
    /// let board3 = BoardBuilder::from_str("; B; bhY")?.build()?;
    /// let hash3 = board3.to_invariant_u64(Color::Green);
    /// assert_eq!(hash1, hash2);
    /// assert_eq!(hash2, hash3);
    /// # Ok(())
    /// # }
    /// ```
    pub fn to_invariant_u64(&self, next_player: Color) -> u64 {
        use Color::*;
        let mut board = *self;
        if matches!(next_player, Green) {
            board.positions.swap_color();
        }

        let mut hashes = [0_u64; 8];
        let Rectangle {
            hmin,
            hmax,
            vmin,
            vmax,
        } = board.minimum_rectangle();
        let (hsize, vsize) = (hmax - hmin + 1, vmax - vmin + 1);

        let mapper = PositionMapper::try_create(vsize, hsize).unwrap();
        let idx_shift = hmin + 4 * vmin;
        for d in Dove::iter() {
            let id = dove_to_index(d);
            for c in Color::iter() {
                let ic = color_to_index(c);
                let pos = board.positions.position_of(c, d);
                if *pos == 0 {
                    continue;
                }
                let ishift = 11 - (2 * id + ic);
                let Some(ipos_raw) = board.viewer.view_mask().field_idx(*pos) else { continue; };
                let ipos = ipos_raw - idx_shift;
                for (i, hash) in hashes.iter_mut().enumerate() {
                    let new_pos = mapper.map(i, ipos) as u64;
                    *hash |= new_pos << (4 * ishift);
                    *hash |= 1_u64 << (48 + ishift);
                }
            }
        }
        hashes.into_iter().min().unwrap()
    }

    /// Returns 4x4 matrix (array of array) representing the board.
    ///
    /// # Examples
    /// ```rust
    /// use tokyodoves::{Board, Color, Dove};
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let board = Board::new();
    /// let matrix = [
    ///     [Some((Color::Green, Dove::B)), None, None, None],
    ///     [Some((Color::Red, Dove::B)), None, None, None],
    ///     [None, None, None, None],
    ///     [None, None, None, None],
    /// ];
    /// assert_eq!(board.to_4x4_matrix(), matrix);
    /// # Ok(())
    /// # }
    /// ```
    pub fn to_4x4_matrix(&self) -> [[Option<(Color, Dove)>; 4]; 4] {
        let mut matrix: [[Option<(Color, Dove)>; 4]; 4] = Default::default();

        for c in Color::iter() {
            for d in Dove::iter() {
                let pos = self.positions.position_of(c, d);
                if *pos != 0 {
                    let Some(idx) = self
                    .viewer
                    .view_mask()
                    .field_idx(*pos) else {
                        continue;
                    };

                    // safety is guaranteed because ih and iv ranges from 0 to 3
                    // iv < 16 holds because field_idx above returns Some(0 ~ 15)
                    let ih = idx % 4;
                    let iv = idx / 4;
                    unsafe {
                        *matrix.get_unchecked_mut(iv).get_unchecked_mut(ih) = Some((c, d));
                    }
                }
            }
        }
        matrix
    }

    /// Returns [`BoardDisplay`] to display the board.
    ///
    /// [`BoardDisplay`] provides a way to configure display styles.
    /// See its documentation for more.
    pub fn display(&self) -> BoardDisplay {
        BoardDisplay::new(self)
    }

    /// Returns a `String` expression with a frame.
    ///
    /// # Examples
    /// ```rust
    /// use tokyodoves::Board;
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let board = Board::new();
    /// let string: String = [
    ///     "+---+---+---+---+",
    ///     "| b |   |   |   |",
    ///     "+---+---+---+---+",
    ///     "| B |   |   |   |",
    ///     "+---+---+---+---+",
    ///     "|   |   |   |   |",
    ///     "+---+---+---+---+",
    ///     "|   |   |   |   |",
    ///     "+---+---+---+---+",
    /// ].join("\n");
    /// assert_eq!(board.to_framed_string(), string);
    /// # Ok(())
    /// # }
    /// ```
    pub fn to_framed_string(&self) -> String {
        self.display()
            .with_format(BoardDisplayFormat::Framed)
            .to_string()
    }

    /// Returns a simple `String` expression.
    ///
    /// `empty` specifies what character fills empty squares.
    /// `delimiter` specifies what `&str` divides each row.
    ///
    /// # Examples
    /// ```rust
    /// use tokyodoves::Board;
    ///
    /// let board = Board::new();
    /// let string = String::from("b---;B---;----;----");
    /// assert_eq!(string, board.to_simple_string('-', ";"));
    /// ```
    pub fn to_simple_string(&self, empty: char, delimiter: &str) -> String {
        self.display()
            .with_format(BoardDisplayFormat::Simple {
                empty,
                delimiter: delimiter.to_owned(),
            })
            .to_string()
    }
}

#[cfg(test)]
mod tests {
    use crate::*;
    use strum::IntoEnumIterator;

    struct RandomPlayIter {
        board: Board,
        num: usize,
        player: Color,
    }

    impl RandomPlayIter {
        fn new() -> Self {
            let board = Board::new();
            let num = 0;
            let player = Color::Red;
            RandomPlayIter { board, num, player }
        }

        fn next_action(&self) -> Action {
            let actions = self.board.legal_actions(self.player, true, true, true);
            actions[self.num % actions.len()]
        }

        fn random_num(n: usize) -> usize {
            (33 * n + 31) % 65536
        }
    }

    impl Iterator for RandomPlayIter {
        type Item = (Board, Action, Color);
        fn next(&mut self) -> Option<Self::Item> {
            let action = self.next_action();
            self.board.perform_unchecked_raw(action).unwrap();

            match self.board.surrounded_status() {
                SurroundedStatus::None => self.player = !self.player,
                _ => {
                    self.board = Board::new();
                    self.player = Color::Red;
                }
            }

            self.num = Self::random_num(self.num);
            let next_action = self.next_action();
            Some((self.board, next_action, self.player))
        }
    }

    fn normal_actions(player: Color) -> Vec<Action> {
        let mut actions = Vec::new();
        for dove in Dove::iter() {
            // Put
            for dv in -3..=3 {
                for dh in -3..=3 {
                    let shift = Shift { dv, dh };
                    actions.push(Action::Put(player, dove, shift));
                }
            }

            // Move
            for dv in -4..=4 {
                for dh in -4..=4 {
                    let shift = Shift { dv, dh };
                    actions.push(Action::Move(player, dove, shift));
                }
            }

            // Remove
            actions.push(Action::Remove(player, dove));
        }

        actions
    }

    fn strange_actions(player: Color) -> Vec<Action> {
        let mut actions = Vec::new();
        let range = 10;
        for dove in Dove::iter() {
            // Put
            for dv in -range..=range {
                for dh in -range..=range {
                    if -3 <= dv && dv <= 3 && -3 <= dh && dh <= 3 {
                        continue;
                    }
                    let shift = Shift { dv, dh };
                    actions.push(Action::Put(player, dove, shift));
                }
            }

            // Move
            for dv in -range..=range {
                for dh in -range..=range {
                    if -4 <= dv && dv <= 4 && -4 <= dh && dh <= 4 {
                        continue;
                    }
                    let shift = Shift { dv, dh };
                    actions.push(Action::Move(player, dove, shift));
                }
            }
        }
        actions
    }

    #[test]
    fn test_actions_iter_consistency() {
        let num_turns = 10_000;
        for (board, _, player) in RandomPlayIter::new().take(num_turns) {
            let actions = board.legal_actions(player, true, true, true);
            let actions_cloned = actions.clone();
            for (a_into_iter, &a_iter) in actions.into_iter().zip(actions_cloned.iter()) {
                let b_into_iter = board.perform_copied(a_into_iter).unwrap();
                let b_iter = board.perform_copied(a_iter).unwrap();
                assert_eq!(b_into_iter, b_iter);
            }
        }
    }

    #[test]
    fn test_equality_consistency() {
        let num_turns = 10_000;
        let mut board_set = std::collections::HashSet::new();
        for (board, _, _) in RandomPlayIter::new().take(num_turns) {
            // --- u64 base recreation ---
            let board2 = BoardBuilder::from_u64(board.to_u64()).build_unchecked();

            assert_eq!(board, board2);
            assert_eq!(board.to_u64(), board2.to_u64());
            assert_eq!(board.to_4x4_matrix(), board2.to_4x4_matrix());
            board_set.clear();
            board_set.insert(board);
            board_set.insert(board2);
            assert_eq!(board_set.len(), 1);

            // --- matrix base recreation ---
            let board3 = BoardBuilder::try_from_4x4_matrix(board.to_4x4_matrix())
                .unwrap()
                .build_unchecked();

            assert_eq!(board, board3);
            assert_eq!(board.to_u64(), board3.to_u64());
            assert_eq!(board.to_4x4_matrix(), board3.to_4x4_matrix());
            board_set.clear();
            board_set.insert(board);
            board_set.insert(board3);
            assert_eq!(board_set.len(), 1);
        }
    }

    #[test]
    fn test_search_consistency() {
        let num_turns = 10_000;
        use std::collections::HashMap;
        let mut all_action_map = HashMap::new();
        for p in Color::iter() {
            all_action_map.insert(p, normal_actions(p));
        }

        for (board, _, player) in RandomPlayIter::new().take(num_turns) {
            let legal_actions = board.legal_actions(player, true, true, true);
            for a in all_action_map.get(&player).unwrap().iter() {
                assert_eq!(legal_actions.contains(*a), board.check_action(*a).is_ok());
            }
        }
    }

    #[test]
    fn test_search_consistency_bwd() {
        let num_turns = 10_000;
        use std::collections::HashMap;
        let mut all_action_map = HashMap::new();
        for p in Color::iter() {
            all_action_map.insert(p, normal_actions(p));
        }

        for (board, _, player) in RandomPlayIter::new().take(num_turns) {
            let legal_actions = board.legal_actions_bwd(player, true, true, true);
            for a in all_action_map.get(&player).unwrap().iter() {
                assert_eq!(
                    legal_actions.contains(*a),
                    board.check_action_bwd(*a).is_ok()
                );
            }
        }
    }

    #[test]
    fn test_strange_actions() {
        let num_turns = 10_000;
        use std::collections::HashMap;
        let mut strange_action_map = HashMap::new();
        for p in Color::iter() {
            strange_action_map.insert(p, strange_actions(p));
        }

        for (board, _, player) in RandomPlayIter::new().take(num_turns) {
            for a in strange_action_map.get(&player).unwrap().iter() {
                assert!(board.check_action(*a).is_err());
                assert!(board.check_action_bwd(*a).is_err());
            }
        }
    }

    #[test]
    fn test_err_unchanged() {
        let num_turns = 1_000;
        use std::collections::HashMap;
        let mut all_action_map = HashMap::new();
        for p in Color::iter() {
            all_action_map.insert(p, normal_actions(p));
        }

        for (board, _, player) in RandomPlayIter::new().take(num_turns) {
            for a in all_action_map.get(&player).unwrap().iter() {
                let mut b_tmp = board;
                if b_tmp.perform(*a).is_err() {
                    assert_eq!(b_tmp.to_u64(), board.to_u64());
                }
                let mut b_tmp_bwd = board;
                if b_tmp_bwd.perform_bwd(*a).is_err() {
                    assert_eq!(b_tmp_bwd.to_u64(), board.to_u64());
                }
            }
        }
    }

    #[test]
    fn test_err_unchanged_strange() {
        let num_turns = 1_000;
        use std::collections::HashMap;
        let mut strange_action_map = HashMap::new();
        for p in Color::iter() {
            strange_action_map.insert(p, strange_actions(p));
        }

        for (board, _, player) in RandomPlayIter::new().take(num_turns) {
            for a in strange_action_map.get(&player).unwrap().iter() {
                let mut b_tmp = board;
                if b_tmp.perform(*a).is_err() {
                    assert_eq!(b_tmp.to_u64(), board.to_u64());
                }
                let mut b_tmp_bwd = board;
                if b_tmp_bwd.perform_bwd(*a).is_err() {
                    assert_eq!(b_tmp_bwd.to_u64(), board.to_u64());
                }
            }
        }
    }

    #[test]
    fn test_dove_count() {
        let num_turns = 10_000;
        for (board, _, _) in RandomPlayIter::new().take(num_turns) {
            let on_field_red = board.doves_on_field_of(Color::Red);
            let on_field_green = board.doves_on_field_of(Color::Green);
            assert_eq!(
                on_field_red.len(),
                board.count_doves_on_field_of(Color::Red)
            );
            assert_eq!(
                on_field_green.len(),
                board.count_doves_on_field_of(Color::Green)
            );
            assert_eq!(
                on_field_red.len() + on_field_green.len(),
                board.count_doves_on_field()
            );
        }
    }

    #[test]
    fn test_dove_bool() {
        let num_turns = 10_000;
        for (board, _, _) in RandomPlayIter::new().take(num_turns) {
            let on_field_red = board.doves_on_field_of(Color::Red);
            let on_field_green = board.doves_on_field_of(Color::Green);
            for d in Dove::iter() {
                assert_eq!(on_field_red.contains(d), board.is_on_field(Color::Red, d));
                assert_eq!(
                    on_field_green.contains(d),
                    board.is_on_field(Color::Green, d)
                );
                for player in Color::iter() {
                    assert_ne!(board.is_in_hand(player, d), board.is_on_field(player, d));
                }
            }
        }
    }

    #[test]
    fn test_swap_color() {
        let num_turns = 10_000;
        for (board, _, _) in RandomPlayIter::new().take(num_turns) {
            let mut board_tmp = board;
            board_tmp.swap_color();
            board_tmp.swap_color();
            assert_eq!(board.to_string(), board_tmp.to_string());
        }
    }

    #[test]
    fn test_swap_color_invariant_u64() {
        let num_turns = 10_000;
        for (board, _, _) in RandomPlayIter::new().take(num_turns) {
            let mut board_swap = board;
            board_swap.swap_color();
            for player in Color::iter() {
                assert_eq!(
                    board.to_invariant_u64(player),
                    board_swap.to_invariant_u64(!player),
                );
            }
        }
    }
}
