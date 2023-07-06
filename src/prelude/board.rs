use strum::IntoEnumIterator;

pub(super) mod bitutil;
pub(super) mod canonicalizer;
pub(super) mod container;
pub(super) mod mask;
pub(super) mod position;
pub(super) mod route;

use crate::prelude::pieces::{color_dove_to_char, color_to_index, dove_to_index, Color, Dove};
use crate::prelude::{error, Action, Shift};

use bitutil::*;
use canonicalizer::*;
use container::*;
pub use container::{ActionContainer, DoveSet, DoveSetIntoIter};
pub use mask::Rectangle;
use mask::*;
use position::*;
use route::*;

// *******************************************************************
//  Utility Struct
// *******************************************************************
/// Inherited implementation for capsuling
macro_rules! impl_mutable_action_container {
    ( $($target: ident { $internal: ty, $iter: ident, $into_iter: ident })* ) => {
        $(
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

/// An [`ActionContainer`] returned by [`Board::legal_actions`]
#[derive(Debug, Clone)]
pub struct ActionsFwd(FiniteActionContainer<64>);

/// An [`Iterator`] returned by [`ActionsFwd::iter`]
pub struct ActionsFwdIter<'a>(FiniteActionContainerIter<'a>);

/// An [`Iterator`] returned by [`ActionsFwd::into_iter`]
pub struct ActionsFwdIntoIter(FiniteActionContainerIntoIter<64>);

/// An [`ActionContainer`] returned by [`Board::legal_actions_bwd`]
#[derive(Debug, Clone)]
pub struct ActionsBwd(FiniteActionContainer<100>);

/// An [`Iterator`] returned by [`ActionsBwd::iter`]
pub struct ActionsBwdIter<'a>(FiniteActionContainerIter<'a>);

/// An [`Iterator`] returned by [`ActionsBwd::into_iter`]
pub struct ActionsBwdIntoIter(FiniteActionContainerIntoIter<100>);

impl_mutable_action_container! {
    ActionsFwd { FiniteActionContainer<64>, ActionsFwdIter, ActionsFwdIntoIter }
    ActionsBwd { FiniteActionContainer<100>, ActionsBwdIter, ActionsBwdIntoIter }
}

/// An enum returned by [`Board::surrounded_status`]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SurroundedStatus {
    Both,
    OneSide(Color),
    None,
}

// *******************************************************************
//  Implement Traits
// *******************************************************************
/// An implementation of Tokyo Doves board based on bitboard techniques
#[derive(Debug, Clone, Copy, Default)]
pub struct Board {
    pub(super) viewer: MaskViewer,
    pub(super) positions: ColorDovePositions,
}

impl Board {
    pub(crate) fn new(viewer: MaskViewer, positions: ColorDovePositions) -> Self {
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

impl std::hash::Hash for Board {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        state.write_u64(self.to_u64());
    }
}

impl Board {
    // *******************************************************************
    //  Methods For Peforming Actions
    // *******************************************************************
    /// Performs the specified `action` to `self`.
    ///
    /// # Errors
    ///
    /// # Examples
    ///
    /// ```ignore
    /// use tokyodoves::{BoardBuilder, Action, Color, Dove, Shift};
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut board = BoardBuilder::new().build()?;
    /// let action = Action::Put(Color::Red, Dove::A, Shift { dh: 1, dv: 0 });
    /// let result = board.perform(action);
    /// assert!(result.is_ok());
    /// # Ok(())
    /// # }
    /// ```
    pub fn perform(&mut self, action: Action) -> Result<(), error::BoardError> {
        self.check_action(action)?;
        self.perform_unchecked_raw(action)?;
        Ok(())
    }

    /// Returns the result of performing the specified action to `self`.
    /// It differs from [`perform`](`Self::perform`) in that it does not change `self`.
    ///
    /// # Errors
    ///
    /// # Examples
    ///
    /// ```ignore
    /// use tokyodoves::{BoardBuilder, Action, Color, Dove, Shift};
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let board = BoardBuilder::new().build()?;
    /// let action = Action::Put(Color::Red, Dove::A, Shift { dh: 1, dv: 0 });
    /// let next_board = board.perform_copied(action)?;
    /// # Ok(())
    /// # }
    /// ```
    pub fn perform_copied(&self, action: Action) -> Result<Self, error::BoardError> {
        let mut board = *self;
        board.perform(action)?;
        Ok(board)
    }

    /// Performs the specified backward action to `self`.
    ///
    /// # Errors
    ///
    /// # Examples
    ///
    /// ```ignore
    /// use tokyodoves::{BoardBuilder, Action, Color, Dove, Shift};
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut board = BoardBuilder::new().build()?;
    /// let action = Action::Put(Color::Red, Dove::A, Shift { dh: 1, dv: -1 });
    /// let result = board.perform_bwd(action);
    /// assert!(result.is_ok());
    /// # Ok(())
    /// # }
    /// ```
    pub fn perform_bwd(&mut self, action: Action) -> Result<(), error::BoardError> {
        self.check_action_bwd(action)?;
        self.perform_unchecked_raw(action)?;
        Ok(())
    }

    /// Returns the result of performing the specified backward action to `self`.
    /// It differs from [`perform_bwd`](`Self::perform_bwd`) in that it does not change `self`.
    ///
    /// # Errors
    ///
    /// # Examples
    ///
    /// ```ignore
    /// use tokyodoves::{BoardBuilder, Action, Color, Dove, Shift};
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let board = BoardBuilder::new().build()?;
    /// let action = Action::Put(Color::Red, Dove::A, Shift { dh: 1, dv: 0 });
    /// let next_board = board.perform_bwd_copied(action)?;
    /// # Ok(())
    /// # }
    /// ```
    pub fn perform_bwd_copied(&self, action: Action) -> Result<Self, error::BoardError> {
        let mut board = *self;
        board.perform_bwd(action)?;
        Ok(board)
    }

    /// Performs `action` to `self` (without distinction between forward and backward).
    ///
    /// It may return `Ok(())` even if the specified `action` is illegal.
    /// In such a case, the resulting board may violate the rule (e.g. some dove would be isolated from others).
    /// If you are not sure that the action is legal, consider to select one of the following choices:
    /// - Call [`check_action`](`Self::check_action`) or [`check_action_bwd`](`Self::check_action_bwd`)
    ///     to check legality in advance.
    /// - Call [`perform`](`Self::perform`) or [`perform_bwd`](`Self::perform_bwd`) insted of this method,
    ///     which calls [`check_action`](`Self::check_action`) or [`check_action_bwd`](`Self::check_action_bwd`) internally.
    /// This method is faster than [`perform`](`Self::perform`) and [`perform_bwd`](`Self::perform_bwd`)
    /// thanks to absence of legality check.
    ///
    /// # Panics
    ///
    /// Panics if the target position of [`Action::Move`] or [`Action::Put`] is more than two squares
    /// far from the current 4x4 field (, which are clearly illegal).
    /// When it returns an error, `self` is not changed.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// use tokyodoves::{BoardBuilder, Action, Color, Dove, Shift};
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut board = BoardBuilder::new().build()?;
    /// let action = Action::Put(Color::Red, Dove::A, Shift { dh: 1, dv: 0 });
    /// board.perform_unchecked(action);
    /// # Ok(())
    /// # }
    /// ```
    pub fn perform_unchecked(&mut self, action: Action) {
        self.perform_unchecked_raw(action).unwrap();
    }

    fn perform_unchecked_raw(&mut self, action: Action) -> Result<(), error::BoardError> {
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

    /// Returns the result of performing the specified action to `self`.
    /// It differs from [`perform_unchecked`](`Self::perform_unchecked`) in that it does not change `self`.
    ///
    /// # Panics
    ///
    /// Panics if the target position of [`Action::Move`] or [`Action::Put`] is more than two squares
    /// far from the current 4x4 field (, which are clearly illegal).
    ///
    /// # Examples
    ///
    /// ```ignore
    /// use tokyodoves::{BoardBuilder, Action, Color, Dove, Shift};
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let board = BoardBuilder::new().build()?;
    /// let action = Action::Put(Color::Red, Dove::A, Shift { dh: 1, dv: 0 });
    /// let next_board = board.perform_unchecked_copied(action);
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
    /// Check if `action` is legal.
    ///
    /// # Errors
    ///
    /// # Examples
    ///
    /// ```ignore
    /// use tokyodoves::{BoardBuilder, Action, Color, Dove, Shift};
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut board = BoardBuilder::new().build()?;
    /// let action = Action::Put(Color::Red, Dove::A, Shift { dh: 1, dv: 0 });
    /// assert!(board.check_action(action).is_ok());
    /// # Ok(())
    /// # }
    /// ```
    pub fn check_action(&self, action: Action) -> Result<(), error::BoardError> {
        self.check_action_core(action, true)
    }

    /// Check if backward `action` is legal.
    ///
    /// # Errors
    ///
    /// # Examples
    ///
    /// ```ignore
    /// use tokyodoves::{BoardBuilder, Action, Color, Dove, Shift};
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut board = BoardBuilder::new().build()?;
    /// let action = Action::Put(Color::Red, Dove::A, Shift { dh: 1, dv: -1 });
    /// assert!(board.check_action_bwd(action).is_ok());
    /// # Ok(())
    /// # }
    /// ```
    pub fn check_action_bwd(&self, action: Action) -> Result<(), error::BoardError> {
        self.check_action_core(action, false)
    }

    fn check_action_core(&self, action: Action, fwd: bool) -> Result<(), error::BoardError> {
        use Action::*;
        match action {
            Put(c, d, s) => self.check_put(c, d, s, fwd),
            Move(c, d, s) => self.check_move(c, d, s),
            Remove(c, d) => self.check_remove(c, d, fwd),
        }
    }

    // Methods for check_action, check_action_bwd
    fn check_put(&self, c: Color, d: Dove, s: Shift, fwd: bool) -> Result<(), error::BoardError> {
        use error::ActionPerformErrorType::*;
        use error::BoardError::*;

        fn _restore_cmd(c_: Color, d_: Dove, s_: Shift) -> Action {
            Action::Put(c_, d_, s_)
        }

        if *self.positions.position_of(c, d) != 0 {
            return Err(ActionPerformError {
                error_type: AlreadyOnBoard,
                action: _restore_cmd(c, d, s),
            });
        }
        if s.dh < -3 || s.dh > 3 || s.dv < -3 || s.dv > 3 {
            return Err(ActionPerformError {
                error_type: InvalidShift,
                action: _restore_cmd(c, d, s),
            });
        }
        let boss_pos = self.positions.position_of(c, Dove::B);
        let pos = apply_shift(*boss_pos, s);
        let Ok(next_mask) = self.viewer.view_mask_at(pos) else {
            return Err(ActionPerformError { error_type: OutOfField, action: _restore_cmd(c, d, s) });
        };

        let all = self.positions.union();
        if all & next_mask.core != all {
            return Err(ActionPerformError {
                error_type: OutOfField,
                action: _restore_cmd(c, d, s),
            });
        }

        if fwd {
            let another_boss_pos = self.positions.position_of(!c, Dove::B);
            let another_boss_sides = sides_of_bit(*another_boss_pos);
            let adj_ours = calc_adjacents(self.positions.union_in_color(c));
            if pos & !all & !another_boss_sides & adj_ours != pos {
                return Err(ActionPerformError {
                    error_type: InvalidPosition,
                    action: _restore_cmd(c, d, s),
                });
            }
        } else {
            let adj_all = calc_adjacents(all);
            if pos & !all & adj_all != pos {
                return Err(ActionPerformError {
                    error_type: InvalidPosition,
                    action: _restore_cmd(c, d, s),
                });
            }
        }

        Ok(())
    }

    fn check_move(&self, c: Color, d: Dove, s: Shift) -> Result<(), error::BoardError> {
        use error::ActionPerformErrorType::*;
        use error::BoardError::*;

        fn _restore_cmd(c_: Color, d_: Dove, s_: Shift) -> Action {
            Action::Move(c_, d_, s_)
        }

        let pos = self.positions.position_of(c, d);
        if *pos == 0 {
            return Err(ActionPerformError {
                error_type: NotOnBoard,
                action: _restore_cmd(c, d, s),
            });
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
            return Err(ActionPerformError {
                error_type: InvalidShift,
                action: _restore_cmd(c, d, s),
            });
        }

        let others = self.positions.union_except(c, d);
        if route & others != 0 {
            return Err(ActionPerformError {
                error_type: ObstacleInRoute,
                action: _restore_cmd(c, d, s),
            });
        }

        let outfield = self.viewer.view_mask().outfield;
        if route & outfield != 0 {
            return Err(ActionPerformError {
                error_type: ThroughOuterField,
                action: _restore_cmd(c, d, s),
            });
        }

        let Ok(new_mask) = self.viewer.view_mask_at(new_pos) else {
            return Err(ActionPerformError { error_type: OutOfField, action: _restore_cmd(c, d, s) })
        };
        if others & !new_mask.core != 0 {
            return Err(ActionPerformError {
                error_type: OutOfField,
                action: _restore_cmd(c, d, s),
            });
        }

        let adj_others = calc_adjacents(others);
        let adj_new_pos = adjacents_of_bit(new_pos);
        if (others | new_pos) & !adj_others & !adj_new_pos != 0 {
            return Err(ActionPerformError {
                error_type: ToBeIsolated,
                action: _restore_cmd(c, d, s),
            });
        }

        Ok(())
    }

    fn check_remove(&self, c: Color, d: Dove, fwd: bool) -> Result<(), error::BoardError> {
        use error::ActionPerformErrorType::*;
        use error::BoardError::*;

        fn _restore_cmd(c_: Color, d_: Dove) -> Action {
            Action::Remove(c_, d_)
        }

        if matches!(d, Dove::B) {
            return Err(ActionPerformError {
                error_type: TriedToRemoveBoss,
                action: _restore_cmd(c, d),
            });
        }
        let pos = self.positions.position_of(c, d);
        if *pos == 0 {
            return Err(ActionPerformError {
                error_type: NotOnBoard,
                action: _restore_cmd(c, d),
            });
        }

        if !fwd {
            let another_boss_pos = self.positions.position_of(!c, Dove::B);
            let another_boss_sides = sides_of_bit(*another_boss_pos);
            let adj_ours = calc_adjacents(self.positions.union_in_color(c));

            if pos & !another_boss_sides & adj_ours != *pos {
                return Err(ActionPerformError {
                    error_type: InvalidPosition,
                    action: _restore_cmd(c, d),
                });
            }
        }

        let others = self.positions.union_except(c, d);
        if others & !calc_adjacents(others) != 0 {
            return Err(ActionPerformError {
                error_type: ToBeIsolated,
                action: _restore_cmd(c, d),
            });
        }
        Ok(())
    }

    // *******************************************************************
    //  Methods For Legal Action Search
    // *******************************************************************
    /// Collects and returns the set of all legal [`Action`]s
    /// for the specified player. Three boolean arguments ---
    /// `contains_put`, `contains_move` and `contains_remove` ---
    /// controls what kinds of `Actions` should be contained.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// use tokyodoves::{BoardBuilder, Color};
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let board = BoardBuilder::new().build()?;
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

    /// Collects and returns the set of all legal backward-[`Action`]s
    /// for the specified player.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// use tokyodoves::{BoardBuilder, Color};
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let board = BoardBuilder::new().build()?;
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
    pub fn count_doves_on_field(&self) -> usize {
        self.positions.union().count_ones() as usize
    }

    /// Counts the number of doves of the `player` on the field.
    pub fn count_doves_on_field_of(&self, player: Color) -> usize {
        self.positions.union_in_color(player).count_ones() as usize
    }

    /// Collects and returns the set of doves in the `player`'s hand.
    pub fn doves_in_hand_of(&self, player: Color) -> DoveSet {
        self.positions.doves_in_hand(player)
    }

    /// Collects and returns the set of doves of the `player` on the field.
    pub fn doves_on_field_of(&self, player: Color) -> DoveSet {
        self.positions.doves_on_field(player)
    }

    /// Returns `true` if the `player`'s `dove` is on the field.
    pub fn is_on_field(&self, player: Color, dove: Dove) -> bool {
        *self.positions.position_of(player, dove) != 0
    }

    /// Returns `true` if the `player`'s `dove` is in their hand.
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
    ///
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
    /// The liberty of "M" is three,
    /// because two of four squares next to "M" is occupied
    /// by "H" and a wall.
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
    /// The meaning of liberty is written in [`liberty`](`Self::liberty`) section.
    /// A player loses when the liberty of their boss-hato becomes 0.
    ///
    /// # Panics
    ///
    /// Panics if `player`'s boss is not on the field,
    /// which does not happen in normal play.
    pub fn liberty_of_boss(&self, player: Color) -> usize {
        self.liberty(player, Dove::B).unwrap()
    }

    /// Get info whether bosses are surrounded or not
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
    /// Returns a light expression of 64 bits.
    ///
    /// 64 bits consist of the following three parts:
    /// - Top 4 bits: empty (filled by 0)
    /// - Next 12 bits: each bit means that each kind of dove is on the field (1) or not (0)
    /// - Next 48 bits: positions of doves are expressed by 0~15, which consumes 4 bits per one dove
    ///     (4 bits x 12 doves = 48 bits)
    ///
    /// The order of 12 doves is "B > b > A > a > Y > y > M > m > T > t > H > h",
    /// where capital/lower cases mean red/green dove, respectively.
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

    /// Returns a light expression of `u64` with a universality.
    ///
    /// The composition of the returned value is the same as that of [`to_u64`](`Self::to_u64`).
    /// "Universality" means that this method returns the same value for boards that
    /// - coinside with each other under reflection, rotation, translation, and any compositions of them.
    /// - coinside with each other after alternating next player and swapping colors of doves simultaneously.
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

        let cons = CONGRUENT_MAPS[(hsize - 1) + 4 * (vsize - 1)];
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
                    let new_pos = cons[i][ipos] as u64;
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
    /// ```ignore
    /// use tokyodoves::{BoardBuilder, Color, Dove};
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let board = BoardBuilder::new().build()?;
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

                    let ih = idx % 4;
                    let iv = idx / 4;
                    matrix[iv][ih] = Some((c, d));
                }
            }
        }
        matrix
    }

    /// Returns a `String` expression with a frame.
    ///
    /// # Examples
    /// ```ignore
    /// use tokyodoves::BoardBuilder;
    ///
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// let board = BoardBuilder::new().build()?;
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
        let hframe = "+---+---+---+---+".to_string();
        let mut lines = Vec::new();
        for line in self.to_4x4_matrix().into_iter() {
            lines.push(hframe.clone());
            let line_str: String = line
                .into_iter()
                .map(|x| match x {
                    Some((c, d)) => format!("| {} ", color_dove_to_char(c, d)),
                    None => "|   ".to_string(),
                })
                .collect();
            lines.push(line_str + "|");
        }
        lines.push(hframe);
        lines.join("\n")
    }

    pub fn to_simple_string(&self, empty: char, delimiter: &str) -> String {
        let mut lines = Vec::new();
        for line in self.to_4x4_matrix().into_iter() {
            let line_str: String = line
                .into_iter()
                .map(|x| match x {
                    Some((c, d)) => color_dove_to_char(c, d),
                    None => empty,
                })
                .collect();
            lines.push(line_str);
        }
        lines.join(delimiter)
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
            let board = BoardBuilder::new().build_unchecked();
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
                    self.board = BoardBuilder::new().build_unchecked();
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
