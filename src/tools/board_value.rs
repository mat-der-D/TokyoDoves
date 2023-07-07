use std::collections::hash_map;
use std::collections::HashMap;

use crate::game::{GameRule, Judge};
use crate::prelude::{Action, Board, Color, SurroundedStatus};

// ************************************************************
//  Errors
// ************************************************************
/// Error variants for validating [`BoardValue`]
#[derive(Debug, Clone, Copy, thiserror::Error)]
pub enum BoardValueError {
    #[error("[WinArgMustOdd] {}", .0)]
    WinArgMustOdd(usize),

    #[error("[LoseArgMustPositiveEven] {}", .0)]
    LoseArgMustPositiveEven(usize),

    #[error("[UnknownNotSupported]")]
    UnknownNotSupported,
}

/// Error variants for [`evaluate_board`]
#[derive(Debug, Clone, Copy, thiserror::Error)]
pub enum EvaluateBoardError {
    #[error("[BoardAlreadyFinished]")]
    BoardAlreadyFinished,

    #[error("[DrawNotSupportedError]")]
    DrawNotSupportedError,
}

/// Error variants for [`compare_board_value`]
#[derive(Debug, Clone, Copy, thiserror::Error)]
pub enum CompareBoardValueError {
    #[error("[BoardAlreadyFinished]")]
    BoardAlreadyFinished,

    #[error("[BoardValueError]")]
    BoardValueError { detail: BoardValueError },

    #[error("[DrawNotSupportedError]")]
    DrawNotSupportedError,
}

/// Error variants for [`create_checkmate_tree`]
#[derive(Debug, Clone, Copy, thiserror::Error)]
pub enum CreateCheckmateTreeError {
    #[error("[BoardAlreadyFinished]")]
    BoardAlreadyFinished,

    #[error("[BoardValueError]")]
    BoardValueError { detail: BoardValueError },

    #[error("[DrawNotSupportedError]")]
    DrawNotSupportedError,

    #[error("[EmptyTreeError]")]
    EmptyTreeError,
}

// ************************************************************
//  Building Blocks
// ************************************************************
/// Value of board
///
/// The order of the values is as follows:
/// ```text
/// Lose(2) < Lose(4) < Lose(6) < ... < Unknown < ... < Win(5) < Win(3) < Win(1)
/// ```
///
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BoardValue {
    /// `Win(n)` means the player will win in `n` turns at least.
    Win(usize),
    /// `Lose(n)` means the player will lose in `n` turns at most.
    Lose(usize),
    /// Cannot detect win or lose.
    /// This variant does not mean the value of the board cannot be determined ultimately,
    /// but the value cannot be determined within the reach of search performed.
    Unknown,
}

impl PartialOrd for BoardValue {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for BoardValue {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        fn _val_to_i8(val: &BoardValue) -> i8 {
            use BoardValue::*;
            match val {
                Win(_) => 1,
                Unknown => 0,
                Lose(_) => -1,
            }
        }

        use std::cmp::Ordering::*;
        use BoardValue::*;
        match (self, other) {
            (Unknown, Unknown) => Equal,
            (Win(left), Win(right)) => right.cmp(left),
            (Lose(left), Lose(right)) => left.cmp(right),
            (left, right) => _val_to_i8(left).cmp(&_val_to_i8(right)),
        }
    }
}

impl TryFrom<BoardValue> for usize {
    type Error = BoardValueError;
    fn try_from(value: BoardValue) -> Result<Self, Self::Error> {
        use BoardValue::*;
        use BoardValueError::*;
        let n = match value {
            Win(n) => {
                if n % 2 == 1 {
                    n
                } else {
                    return Err(WinArgMustOdd(n));
                }
            }
            Lose(n) => {
                if (n != 0) && (n % 2 == 0) {
                    n
                } else {
                    return Err(LoseArgMustPositiveEven(n));
                }
            }
            Unknown => {
                return Err(UnknownNotSupported);
            }
        };
        Ok(n)
    }
}

// ************************************************************
//  Evaluate Board
// ************************************************************
/// Evaluates `Board`
///
/// It searches the value of `board` under `max_search_depth`.
/// If it does not the value, it returns `Ok(Unknown)`
///
/// # Errors
/// Returns `Err` only when the argument is invalid. Specifically,
/// the following cases are invalid:
/// - `board` is already finished (at least one boss is surrounded)
/// - `rule.suicide_atk_judge` is `Judge::Draw`
pub fn evaluate_board(
    board: &Board,
    max_search_depth: usize,
    player: Color,
    rule: GameRule,
) -> Result<BoardValue, EvaluateBoardError> {
    use BoardValue::*;
    if max_search_depth == 0 {
        return Ok(Unknown);
    }

    use EvaluateBoardError::*;
    if !matches!(board.surrounded_status(), SurroundedStatus::None) {
        return Err(BoardAlreadyFinished);
    }

    use Judge::*;
    let wins_if_both = match rule.suicide_atk_judge() {
        LastWins => true,
        NextWins => false,
        Draw => return Err(DrawNotSupportedError),
    };
    let is_remove_accepted = *rule.is_remove_accepted();

    for depth in 1..=max_search_depth {
        let cmp = compare_board_value_core(board, depth, player, is_remove_accepted, wins_if_both);
        if cmp == 0 {
            return match depth {
                0 => unreachable!(),
                n => match n % 2 {
                    0 => Ok(Lose(n)),
                    1 => Ok(Win(n)),
                    _ => unreachable!(),
                },
            };
        }
    }
    Ok(Unknown)
}

// ************************************************************
//  Compare Value
// ************************************************************
/// Compares the value of specified [`Board`] to a given [`BoardValue`].
///
/// It returns:
/// - `Ok(Greater)` if the value of `board` is greater than `value`
/// - `Ok(Equal)` if the value of `board` equals to `value`
/// - `Ok(Less)` if the value of `board` is less than `value
///
/// # Errors
/// Returns `Err` only when the argument is invalid. Specifically,
/// the following cases are invalid:
/// - `board` is already finished (at least one boss is surrounded)
/// - `value` is `Unknown`, `Win(even number)` or `Lose(odd or zero)`
/// - `rule.suicide_atk_judge` is `Judge::Draw`
pub fn compare_board_value(
    board: &Board,
    value: BoardValue,
    player: Color,
    rule: GameRule,
) -> Result<std::cmp::Ordering, CompareBoardValueError> {
    use CompareBoardValueError::*;
    if !matches!(board.surrounded_status(), SurroundedStatus::None) {
        return Err(BoardAlreadyFinished);
    }

    let n = value
        .try_into()
        .map_err(|e| CompareBoardValueError::BoardValueError { detail: e })?;

    use Judge::*;
    let wins_if_both = match rule.suicide_atk_judge() {
        LastWins => true,
        NextWins => false,
        Draw => return Err(DrawNotSupportedError),
    };
    let is_remove_accepted = *rule.is_remove_accepted();
    use std::cmp::Ordering::*;
    let cmp = match compare_board_value_core(board, n, player, is_remove_accepted, wins_if_both) {
        -1 => Less,
        0 => Equal,
        1 => Greater,
        _ => unreachable!(),
    };
    Ok(cmp)
}

fn compare_board_value_core(
    board: &Board,
    step_to_finish: usize,
    player: Color,
    is_remove_accepted: bool,
    wins_if_both: bool,
) -> i8 {
    let mut cmp = if step_to_finish == 2 { 0 } else { -1 };
    for action in board.legal_actions(player, true, true, is_remove_accepted) {
        let next_board = board.perform_unchecked_copied(action);

        use SurroundedStatus::*;
        let status = next_board.surrounded_status();
        let is_both = matches!(status, Both);
        if (wins_if_both && is_both) || matches!(status, OneSide(p) if p != player) {
            return if step_to_finish == 1 { 0 } else { 1 };
        } else if (step_to_finish == 1)
            || (!wins_if_both && is_both)
            || matches!(status, OneSide(p) if p == player)
        {
            continue;
        } else {
            let next_cmp = compare_board_value_core(
                &next_board,
                step_to_finish - 1,
                !player,
                is_remove_accepted,
                wins_if_both,
            );
            if next_cmp == -1 {
                return 1;
            }
            cmp = cmp.max(-next_cmp);
        }
    }
    cmp
}

// ************************************************************
//  Action Tree
// ************************************************************
/// A tree structure that contains [`Action`]s on its edges.
///
/// It is returned by [`create_checkmate_tree`] to describe
/// routes, i.e. possible serieses of `Action`s, to ends of the game.
#[derive(Debug, Clone)]
pub struct ActionTree(HashMap<Action, ActionTree>);

impl ActionTree {
    fn new() -> Self {
        Self(HashMap::new())
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    fn insert(&mut self, action: Action, tree: ActionTree) {
        self.0.insert(action, tree);
    }

    pub fn child(&self, action: &Action) -> Option<&ActionTree> {
        self.0.get(&action)
    }

    pub fn children(&self) -> hash_map::Values<'_, Action, ActionTree> {
        self.0.values()
    }

    pub fn actions(&self) -> hash_map::Keys<'_, Action, ActionTree> {
        self.0.keys()
    }

    pub fn actions_children(&self) -> hash_map::Iter<'_, Action, ActionTree> {
        self.0.iter()
    }

    pub fn depth(&self) -> usize {
        if self.0.is_empty() {
            0
        } else {
            self.0.values().map(|t| t.depth()).max().unwrap() + 1
        }
    }

    pub fn to_serieses(&self) -> Vec<Vec<&Action>> {
        let mut serieses = Vec::new();
        for (a, t) in self.actions_children() {
            if t.depth() == 2 {
                serieses.push(vec![a]);
            }
            for next_vec in t.to_serieses() {
                let series: Vec<&Action> = [a].into_iter().chain(next_vec.into_iter()).collect();
                serieses.push(series);
            }
        }
        serieses
    }

    pub fn is_good_for_puzzle(&self, step: usize) -> bool {
        if step == 0 {
            true
        } else {
            self.actions_children().len() == 1
                && self
                    .actions_children()
                    .nth(0)
                    .unwrap()
                    .1
                    .is_good_for_puzzle(step - 1)
        }
    }
}

/// Creates an [`ActionTree`] that describes routes to ends of the game.
///
/// It supposes the value of `board` equals to `value`.
/// [`compare_board_value`] may be a good tool to examine this in advance.
///
/// # Errors
/// Returns `Err` when the argument is invalid. Specifically,
/// the following cases are invalid:
/// - `board` is already finished (at least one boss is surrounded)
/// - `value` is `Unknown`, `Win(even number)` or `Lose(odd or zero)`
/// - `rule.suicide_atk_judge` is `Judge::Draw`
/// Furthermore, it returns `Err(EmptyTreeError)` if the value of `board`
/// does not equal to `value`.
pub fn create_checkmate_tree(
    board: &Board,
    value: BoardValue,
    player: Color,
    rule: GameRule,
) -> Result<ActionTree, CreateCheckmateTreeError> {
    use CreateCheckmateTreeError::*;
    if !matches!(board.surrounded_status(), SurroundedStatus::None) {
        return Err(BoardAlreadyFinished);
    }

    let n = value
        .try_into()
        .map_err(|e| CreateCheckmateTreeError::BoardValueError { detail: e })?;

    use Judge::*;
    let wins_if_both = match rule.suicide_atk_judge() {
        LastWins => true,
        NextWins => false,
        Draw => return Err(DrawNotSupportedError),
    };
    let is_remove_accepted = *rule.is_remove_accepted();

    let (_, tree) = create_checkmate_tree_core(board, n, player, is_remove_accepted, wins_if_both);
    if tree.is_empty() {
        return Err(EmptyTreeError);
    }
    Ok(tree)
}

fn create_checkmate_tree_core(
    board: &Board,
    step_to_finish: usize,
    player: Color,
    is_remove_accepted: bool,
    wins_if_both: bool,
) -> (i8, ActionTree) {
    let mut tree = ActionTree::new();
    let mut cmp = if step_to_finish == 2 { 0 } else { -1 };
    for action in board.legal_actions(player, true, true, is_remove_accepted) {
        let next_board = board.perform_unchecked_copied(action);

        use SurroundedStatus::*;
        let status = next_board.surrounded_status();
        let is_both = matches!(status, Both);
        if (wins_if_both && is_both) || matches!(status, OneSide(p) if p != player) {
            if step_to_finish == 1 {
                tree.insert(action, ActionTree::new());
                cmp = 0;
                continue;
            } else {
                return (1, ActionTree::new());
            };
        } else if (step_to_finish == 1)
            || (!wins_if_both && is_both)
            || matches!(status, OneSide(p) if p == player)
        {
            continue;
        } else {
            let (next_cmp, next_tree) = create_checkmate_tree_core(
                &next_board,
                step_to_finish - 1,
                !player,
                is_remove_accepted,
                wins_if_both,
            );
            if next_cmp == -1 {
                return (1, ActionTree::new());
            }
            if next_cmp == 0 {
                tree.insert(action, next_tree);
            }
            cmp = cmp.max(-next_cmp);
        }
    }
    (cmp, tree)
}

// ************************************************************
//  Tests
// ************************************************************
#[cfg(test)]
mod tests {
    use crate::{tools::create_checkmate_tree, *};

    #[test]
    fn test_evaluate_board() {
        use std::str::FromStr;
        use tools::BoardValue::*;
        let rule = game::GameRule::new(true).with_suicide_atk_judge(game::Judge::NextWins);
        let board_value = [
            (" B; a;TH y;b mM", Win(5)),
            (" By;H  a;A m;  Yb", Win(3)),
            ("bB; H;Y h;  T", Win(3)),
            ("T; B b;  yY; t", Win(3)),
            ("hB A;maYT; Htb;M y", Win(5)),
            ("Ba;  H;  hA;MY b", Win(5)),
            (" B;a  b; MtY;T  H", Win(7)),
            ("Y; B;y hA; M b", Win(5)),
            ("bB;T YA", Win(5)),
        ];
        let max_depth = 10; // it must be greater than all n of Win(n)
        for (s, val) in board_value {
            let board = BoardBuilder::from_str(s).unwrap().build().unwrap();
            let evaluated = tools::evaluate_board(&board, max_depth, Color::Red, rule).unwrap();
            assert_eq!(evaluated, val);
        }
    }

    #[test]
    fn test_compare_value() {
        use std::str::FromStr;
        use tools::BoardValue::*;
        let rule = game::GameRule::new(true).with_suicide_atk_judge(game::Judge::NextWins);
        let board_value = [
            (" B; a;TH y;b mM", Win(5)),
            (" By;H  a;A m;  Yb", Win(3)),
            ("bB; H;Y h;  T", Win(3)),
            ("T; B b;  yY; t", Win(3)),
            ("hB A;maYT; Htb;M y", Win(5)),
            ("Ba;  H;  hA;MY b", Win(5)),
            (" B;a  b; MtY;T  H", Win(7)),
            ("Y; B;y hA; M b", Win(5)),
            ("bB;T YA", Win(5)),
        ];
        for (s, val) in board_value {
            let board = BoardBuilder::from_str(s).unwrap().build().unwrap();
            let cmp = tools::compare_board_value(&board, val, Color::Red, rule);
            assert!(matches!(cmp, Ok(std::cmp::Ordering::Equal)));
        }
    }

    #[test]
    fn test_checkmate_tree() {
        use std::str::FromStr;
        use tools::BoardValue::*;
        let rule = game::GameRule::new(true).with_suicide_atk_judge(game::Judge::NextWins);
        let board_value = [
            (" B; a;TH y;b mM", Win(5)),
            (" By;H  a;A m;  Yb", Win(3)),
            ("bB; H;Y h;  T", Win(3)),
            ("T; B b;  yY; t", Win(3)),
            ("hB A;maYT; Htb;M y", Win(5)),
            ("Ba;  H;  hA;MY b", Win(5)),
            (" B;a  b; MtY;T  H", Win(7)),
            ("Y; B;y hA; M b", Win(5)),
            ("bB;T YA", Win(5)),
        ];
        for (s, val) in board_value {
            let board = BoardBuilder::from_str(s).unwrap().build().unwrap();
            let tree = create_checkmate_tree(&board, val, Color::Red, rule).unwrap();
            let step_to_finish: usize = val.try_into().unwrap();
            assert!(tree.is_good_for_puzzle(step_to_finish - 2));
        }
    }
}
