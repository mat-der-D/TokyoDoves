use std::cmp::{Ord, Ordering, PartialOrd};
use std::collections::{hash_map, HashMap};
use std::io::{BufWriter, Write};

use crate::{
    error,
    game::{GameRule, Judge},
    Action, ActionsFwdIntoIter, Board, BoardBuilder, Color, SurroundedStatus,
};

// ****************************************************************************
//  BoardValue
// ****************************************************************************
/// Kinds of [`BoardValue`]
///
/// This type is returned by [`BoardValue::kind`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BoardValueKind {
    Win,
    Lose,
    Unknown,
    Finished,
}

impl Default for BoardValueKind {
    fn default() -> Self {
        Self::Unknown
    }
}

impl std::fmt::Display for BoardValueKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}

impl PartialOrd for BoardValueKind {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        fn _kind_to_u8(kind: &BoardValueKind) -> u8 {
            use BoardValueKind::*;
            match kind {
                Win => 2,
                Unknown => 1,
                Lose => 0,
                Finished => unreachable!(),
            }
        }

        use BoardValueKind::*;
        if matches!(self, Finished) || matches!(other, Finished) {
            if self.eq(other) {
                return Some(Ordering::Equal);
            } else {
                return None;
            }
        }

        _kind_to_u8(self).partial_cmp(&_kind_to_u8(other))
    }
}

/// Value of [`Board`].
///
/// The order of the values is as follows:
/// ```text
/// BoardValue::MIN = Lose(2) < Lose(4) < Lose(6) < ...
///     < Unknown
///     < ... < Win(5) < Win(3) < Win(1) = BoardValue::MAX
/// ```
/// - n of `Lose(n)` means that the player will lose in n turns at most.
/// - n of `Win(n)` means that the player will win in n turns at least.
/// - `Unknown` means that the value of the board was failed to be determined.
///     It can change to `Lose(n)` or `Win(n)` if you search more deeply.
///
/// It takes another value `Finished`, which is attributed to boards of finished games.
/// This value is, however, not compared to other values,
/// which is the reason why `BoardValue` is `PartialOrd` but not `Ord`.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash)]
pub struct BoardValue {
    value: Option<usize>,
}

impl std::fmt::Display for BoardValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use BoardValueKind::*;
        let kind = self.kind();
        let s = match kind {
            Unknown | Finished => kind.to_string(),
            _ => {
                let num = self.value.unwrap();
                format!("{kind}({num})")
            }
        };
        write!(f, "{s}")
    }
}

impl BoardValue {
    /// Win(1)
    ///
    /// # Examples
    /// ```rust
    /// use tokyodoves::analysis::BoardValue;
    /// assert_eq!(BoardValue::MAX, BoardValue::win(1).unwrap());
    /// ```
    pub const MAX: BoardValue = BoardValue { value: Some(1) };
    /// Lose(2)
    ///
    /// # Examples
    /// ```rust
    /// use tokyodoves::analysis::BoardValue;
    /// assert_eq!(BoardValue::MIN, BoardValue::lose(2).unwrap());
    /// ```
    pub const MIN: BoardValue = BoardValue { value: Some(2) };

    /// Returns the kind of the value.
    ///
    /// # Examples
    /// ```rust
    /// use tokyodoves::analysis::{BoardValue, BoardValueKind};
    ///
    /// let value = BoardValue::default();
    /// assert_eq!(value.kind(), BoardValueKind::Unknown);
    /// ```
    pub fn kind(&self) -> BoardValueKind {
        use BoardValueKind::*;
        match self.value {
            None => Unknown,
            Some(0) => Finished,
            Some(n) => match n % 2 {
                0 => Lose,
                1 => Win,
                _ => unreachable!(),
            },
        }
    }

    /// Creates win value.
    ///
    /// The argument `num` must be odd, otherwise it returns `None`.
    ///
    /// # Examples
    /// ```rust
    /// use tokyodoves::analysis::{BoardValue, BoardValueKind};
    ///
    /// let value = BoardValue::win(3).unwrap();
    /// assert_eq!(value.kind(), BoardValueKind::Win);
    /// ```
    pub fn win(num: usize) -> Option<Self> {
        if num % 2 == 1 {
            Some(BoardValue { value: Some(num) })
        } else {
            None
        }
    }

    /// Creates lose value.
    ///
    /// The argument `num` must be positive and even,
    /// otherwise it returns `None`.
    ///
    /// # Examples
    /// ```rust
    /// use tokyodoves::analysis::{BoardValue, BoardValueKind};
    ///
    /// let value = BoardValue::lose(4).unwrap();
    /// assert_eq!(value.kind(), BoardValueKind::Lose);
    /// ```
    pub fn lose(num: usize) -> Option<Self> {
        if num != 0 && num % 2 == 0 {
            Some(BoardValue { value: Some(num) })
        } else {
            None
        }
    }

    /// Creates unknown value.
    ///
    /// # Examples
    /// ```rust
    /// use tokyodoves::analysis::{BoardValue, BoardValueKind};
    ///
    /// let value = BoardValue::unknown();
    /// assert_eq!(value.kind(), BoardValueKind::Unknown);
    /// ```
    pub fn unknown() -> Self {
        BoardValue { value: None }
    }

    /// Creates finished value.
    ///
    /// # Examples
    /// ```rust
    /// use tokyodoves::analysis::{BoardValue, BoardValueKind};
    ///
    /// let value = BoardValue::finished();
    /// assert_eq!(value.kind(), BoardValueKind::Finished);
    /// ```
    pub fn finished() -> Self {
        BoardValue { value: Some(0) }
    }

    /// Tries to get the number in win or lose.
    ///
    /// If `self` is not win or lose, it returns `None`.
    ///
    /// # Examples
    /// ```
    /// use tokyodoves::analysis::BoardValue;
    ///
    /// let win = BoardValue::win(3).unwrap();
    /// assert_eq!(Some(3), win.try_unwrap());
    /// let unknown = BoardValue::unknown();
    /// assert_eq!(None, unknown.try_unwrap());
    /// ```
    pub fn try_unwrap(&self) -> Option<usize> {
        match self.value {
            Some(num) if num >= 1 => self.value,
            _ => None,
        }
    }

    /// Get the number in win or lose.
    ///
    /// # Panics
    /// Panics if `self` is not win or lose.
    ///
    /// # Examples
    /// ```
    /// use tokyodoves::analysis::BoardValue;
    ///
    /// let win = BoardValue::win(3).unwrap();
    /// assert_eq!(3, win.unwrap());
    /// ```
    pub fn unwrap(&self) -> usize {
        self.try_unwrap().unwrap()
    }

    /// Returns `true` if `self` is win.
    ///
    /// # Examples
    /// ```rust
    /// use tokyodoves::analysis::BoardValue;
    ///
    /// let win = BoardValue::win(3).unwrap();
    /// assert!(win.is_win());
    /// let unknown = BoardValue::unknown();
    /// assert!(!unknown.is_win());
    /// ```
    pub fn is_win(&self) -> bool {
        matches!(self.kind(), BoardValueKind::Win)
    }

    /// Returns `true` if `self` is lose.
    ///
    /// # Examples
    /// ```rust
    /// use tokyodoves::analysis::BoardValue;
    ///
    /// let lose = BoardValue::lose(4).unwrap();
    /// assert!(lose.is_lose());
    /// let unknown = BoardValue::unknown();
    /// assert!(!unknown.is_lose());
    /// ```
    pub fn is_lose(&self) -> bool {
        matches!(self.kind(), BoardValueKind::Lose)
    }

    /// Returns `true` if `self` is unknown.
    ///
    /// # Examples
    /// ```rust
    /// use tokyodoves::analysis::BoardValue;
    ///
    /// let unknown = BoardValue::unknown();
    /// assert!(unknown.is_unknown());
    /// let win = BoardValue::win(3).unwrap();
    /// assert!(!win.is_unknown());
    /// ```
    pub fn is_unknown(&self) -> bool {
        matches!(self.kind(), BoardValueKind::Unknown)
    }

    /// Returns `true` if `self` is finished.
    ///
    /// # Examples
    /// ```rust
    /// use tokyodoves::analysis::BoardValue;
    ///
    /// let finished = BoardValue::finished();
    /// assert!(finished.is_finished());
    /// let unknown = BoardValue::unknown();
    /// assert!(!unknown.is_finished());
    /// ```
    pub fn is_finished(&self) -> bool {
        matches!(self.kind(), BoardValueKind::Finished)
    }

    /// Returns the next value of a series below:
    /// ```text
    /// Unknown -> Unknown
    /// Finished -> Win(1) -> Lose(2) -> Win(3) -> Lose(4) -> ...
    /// ```
    ///
    /// # Examples
    /// ```rust
    /// use tokyodoves::analysis::BoardValue;
    ///
    /// let value = BoardValue::win(3).unwrap();
    /// let next = BoardValue::lose(4).unwrap();
    /// assert_eq!(next, value.increment());
    /// let unknown = BoardValue::unknown();
    /// assert_eq!(unknown, unknown.increment());
    /// ```
    pub fn increment(&self) -> Self {
        Self {
            value: self.value.map(|num| num + 1),
        }
    }

    /// Returns "next" values of a series below:
    /// ```text
    /// Unknown -> Unknown
    /// ... -> Lose(4) -> Win(3) -> Lose(2) -> Win(1) -> Finished
    /// ```
    /// It returns `None` if self is `Finished`, otherwise `Some(next_value)`.
    /// # Examples
    /// ```rust
    /// use tokyodoves::analysis::BoardValue;
    ///
    /// let value = BoardValue::win(3).unwrap();
    /// let next = BoardValue::lose(2).unwrap();
    /// assert_eq!(Some(next), value.try_decrement());
    /// let unknown = BoardValue::unknown();
    /// assert_eq!(Some(unknown), unknown.try_decrement());
    /// ```
    pub fn try_decrement(&self) -> Option<Self> {
        let value = match self.value {
            Some(0) => return None,
            x => x.map(|num| num - 1),
        };
        Some(Self { value })
    }
}

impl From<Option<usize>> for BoardValue {
    fn from(value: Option<usize>) -> Self {
        Self { value }
    }
}

impl From<BoardValue> for Option<usize> {
    fn from(board_value: BoardValue) -> Self {
        board_value.value
    }
}

impl PartialOrd for BoardValue {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        let left_kind = self.kind();
        let right_kind = other.kind();

        use BoardValueKind::*;
        if (left_kind != right_kind) || matches!(left_kind, Unknown | Finished) {
            return left_kind.partial_cmp(&right_kind);
        }

        // In the following, left_kind == right_kind not in {Unknown, Finished}

        let left_num = self.value.as_ref().unwrap();
        let right_num = other.value.as_ref().unwrap();
        match left_kind {
            Lose => left_num.partial_cmp(right_num),
            Win => right_num.partial_cmp(left_num),
            _ => unreachable!(),
        }
    }
}

#[cfg(test)]
mod tests_board_value {
    use crate::analysis::{BoardValue, BoardValueKind};

    #[test]
    fn test_create_win() {
        for n in 0..100 {
            let Some(val) = BoardValue::win(n) else {
                continue;
            };
            assert_eq!(val, BoardValue::from(Some(n)));
            assert!(val.is_win());
            assert_eq!(val.kind(), BoardValueKind::Win);
            let num = val.unwrap();
            assert_eq!(n, num);
            assert_eq!(val, BoardValue::win(num).unwrap());
        }
    }

    #[test]
    fn test_create_lose() {
        for n in 0..100 {
            let Some(val) = BoardValue::lose(n) else {
                continue;
            };
            assert_eq!(val, BoardValue::from(Some(n)));
            assert!(val.is_lose());
            assert_eq!(val.kind(), BoardValueKind::Lose);
            let num = val.unwrap();
            assert_eq!(n, num);
            assert_eq!(val, BoardValue::lose(num).unwrap());
        }
    }

    #[test]
    fn test_create_unknown() {
        let val = BoardValue::unknown();
        assert_eq!(val, BoardValue::from(None));
        assert!(val.is_unknown());
        assert_eq!(val.kind(), BoardValueKind::Unknown);
        assert!(val.try_unwrap().is_none());
    }

    #[test]
    fn test_create_finished() {
        let val = BoardValue::finished();
        assert_eq!(val, BoardValue::from(Some(0)));
        assert!(val.is_finished());
        assert_eq!(val.kind(), BoardValueKind::Finished);
        assert!(val.try_unwrap().is_none());
    }

    #[test]
    fn test_increment() {
        assert_eq!(BoardValue::unknown(), BoardValue::unknown().increment());

        let mut val = BoardValue::finished();
        for num in 1..100 {
            val = val.increment();
            assert_eq!(val, BoardValue::from(Some(num)));
            assert_eq!(val.unwrap(), num);
        }
    }

    #[test]
    fn test_try_decrement() {
        assert_eq!(
            BoardValue::unknown(),
            BoardValue::unknown().try_decrement().unwrap()
        );
        let mut val = BoardValue::lose(100).unwrap();
        for num in (0..100).rev() {
            val = val.try_decrement().unwrap();
            assert_eq!(val, BoardValue::from(Some(num)));
            if num == 0 {
                assert!(val.try_unwrap().is_none());
            } else {
                assert_eq!(val.unwrap(), num);
            }
        }
        assert!(val.try_decrement().is_none());
    }

    #[test]
    fn test_compare() {
        let unknown = BoardValue::unknown();
        let finished = BoardValue::finished();
        assert!(!(finished < finished));
        assert!(!(finished > finished));
        assert_eq!(finished, finished);
        assert!(!(finished < unknown));
        assert!(!(unknown < finished));
        assert!(!(finished > unknown));
        assert!(!(unknown > finished));

        let mut is_first_loop = true;
        for num_win in (1..100).step_by(2) {
            let win = BoardValue::win(num_win).unwrap();
            assert!(win <= BoardValue::MAX);
            if win != BoardValue::MAX {
                assert!(win < BoardValue::MAX);
            }
            assert!(unknown < win);
            assert!(!(finished < win));
            assert!(!(finished > win));
            assert!(!(win < finished));
            assert!(!(win > finished));

            for num_lose in (2..100).step_by(2) {
                let lose = BoardValue::lose(num_lose).unwrap();
                assert!(lose >= BoardValue::MIN);
                if lose != BoardValue::MIN {
                    assert!(lose > BoardValue::MIN);
                }
                assert!(lose < win);
                assert!(lose < unknown);

                if is_first_loop {
                    assert!(!(finished < lose));
                    assert!(!(finished > lose));
                    assert!(!(lose < finished));
                    assert!(!(lose > finished));
                }
            }
            is_first_loop = false;
        }
    }
}

// ****************************************************************************
//  NextBoardIter
// ****************************************************************************
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum NextBoardStatus {
    Win,
    Lose,
    Unknown,
}

struct NextBoardIter {
    current_board: Board,
    current_player: Color,
    wins_if_both: bool,
    actions_iter: ActionsFwdIntoIter,
}

impl NextBoardIter {
    fn new(current_board: Board, current_player: Color, rule: GameRule) -> Self {
        use Judge::*;
        let wins_if_both = match rule.suicide_atk_judge() {
            LastWins => true,
            NextWins => false,
            Draw => panic!("validation error"),
        };
        let actions_iter = current_board
            .legal_actions(current_player, true, true, *rule.is_remove_accepted())
            .into_iter();
        Self {
            current_board,
            current_player,
            wins_if_both,
            actions_iter,
        }
    }
}

impl Iterator for NextBoardIter {
    type Item = (Action, Board, NextBoardStatus);
    fn next(&mut self) -> Option<Self::Item> {
        let action = self.actions_iter.next()?;
        let next_board = self.current_board.perform_unchecked_copied(action);

        use SurroundedStatus::*;
        let sur_status = next_board.surrounded_status();
        let is_both = matches!(sur_status, Both);

        use NextBoardStatus::*;
        let next_board_status = if (self.wins_if_both && is_both)
            || matches!(sur_status, OneSide(p) if p != self.current_player)
        {
            Win
        } else if (!self.wins_if_both && is_both)
            || matches!(sur_status, OneSide(p) if p == self.current_player)
        {
            Lose
        } else {
            Unknown
        };
        Some((action, next_board, next_board_status))
    }
}

// ****************************************************************************
//  BoardValueTree
// ****************************************************************************
/// A tree structure that contains [`Board`] and [`BoardValue`] on its nodes,
/// and [`Action`]s on its edges.
///
/// It is returned by [`create_checkmate_tree`].
#[derive(Debug, Clone)]
pub struct BoardValueTree {
    board_raw: u64,
    player: Color,
    value: BoardValue,
    actions2children: HashMap<Action, BoardValueTree>,
}

impl BoardValueTree {
    fn new(board: Board, player: Color) -> Self {
        Self {
            board_raw: board.to_u64(),
            player,
            value: Default::default(),
            actions2children: Default::default(),
        }
    }

    /// Returns [`Board`] at the root node.
    pub fn board(&self) -> Board {
        BoardBuilder::from_u64(self.board_raw).build_unchecked()
    }

    /// Returns a reference to the player [`Color`] at the root node.
    pub fn player(&self) -> &Color {
        &self.player
    }

    /// Returns a reference to the [`BoardValue`] at the root node.
    pub fn value(&self) -> &BoardValue {
        &self.value
    }

    /// Returns [`TreeDisplay`] to display `self`.
    pub fn display(&self) -> TreeDisplay {
        TreeDisplay::new(self)
    }

    /// Returns a reference to a child tree associated to the specified [`Action`].
    ///
    /// It returns `Some(&child)` if a child exists, otherwise `None`.
    pub fn child(&self, action: &Action) -> Option<&BoardValueTree> {
        self.actions2children.get(action)
    }

    /// Returns an [`Iterator`] that iterates over all [`Action`]s connecting to children.
    pub fn actions(&self) -> hash_map::Keys<'_, Action, BoardValueTree> {
        self.actions2children.keys()
    }

    /// Returns an [`Iterator`] that iterates over all children.
    pub fn children(&self) -> hash_map::Values<'_, Action, BoardValueTree> {
        self.actions2children.values()
    }

    /// Counts the number of children.
    pub fn num_children(&self) -> usize {
        self.actions2children.len()
    }

    /// Returns `true` if it is a leaf node, i.e., it has no children.
    pub fn is_leaf(&self) -> bool {
        self.actions2children.is_empty()
    }

    /// Returns an [`Iterator`] that iterates all pairs of [`Action`] and [`BoardValueTree`].
    pub fn actions_children(&self) -> hash_map::Iter<'_, Action, BoardValueTree> {
        self.actions2children.iter()
    }

    /// Returns the depth of the tree, i.e.,
    /// the longest steps from the root node to leaf node.
    pub fn depth(&self) -> usize {
        1 + self
            .actions2children
            .values()
            .map(|t| t.depth())
            .max()
            .unwrap_or_default()
    }

    /// Returns `true` if the tree is a single road
    /// during the first `step` steps.
    pub fn is_good_for_puzzle(&self, step: usize) -> bool {
        if step == 0 {
            true
        } else {
            self.actions2children.len() == 1
                && self
                    .actions2children
                    .values()
                    .all(|c| c.is_good_for_puzzle(step - 1))
        }
    }

    fn color_to_code(color: Color) -> &'static str {
        use Color::*;
        match color {
            Red => "#ffcccc",
            Green => "#ccffcc",
        }
    }

    fn value_to_style(value: &BoardValue) -> &'static str {
        if value.is_win() {
            "bold,solid,filled"
        } else {
            "bold,dotted,filled"
        }
    }

    /// Saves the tree as a file in DOT language.
    ///
    /// DOT language is a graph description language,
    /// used in a graph visualization software [Graphviz](https://graphviz.org/).
    ///
    /// # Examples
    /// The saved file can be converted to colorful graph by the following command:
    /// ```text
    /// graphviz.exe -Tsvg tree.dot -o output.svg
    /// ```
    /// See the documentation of Graphviz for more.
    pub fn save_as_dot<W>(&self, writer: W) -> std::io::Result<()>
    where
        W: Write,
    {
        let mut fs = BufWriter::new(writer);
        write!(fs, "{}", self.to_dot_string())
    }

    fn to_dot_string(&self) -> String {
        let dot = vec![
            "digraph {".to_string(),
            format!(
                "node[style={:?} fontname=\"Courier New\" shape=\"box\"]",
                Self::value_to_style(self.value())
            ),
            format!("node[fillcolor={:?}]", Self::color_to_code(self.player)),
            self.to_dot_string_body("", ""),
            "}".to_string(),
        ]
        .join("\n");
        dot
    }

    fn to_dot_string_body(&self, parent: &str, action: &str) -> String {
        let mut dot: String;
        let board = self.board().to_simple_string('-', "\\n");
        let style = Self::value_to_style(self.value());
        let name: String;
        if parent.is_empty() {
            name = String::from("Root");
            dot = format!("{name}[label=\"{board}\", style=\"{style}\"]");
        } else {
            name = format!("{parent}_{}", action.replace('+', "p").replace('-', "m"));
            dot = format!(
                "{name}[label={board:?}, style={style:?}]\n{parent} -> {name}[label={action:?}]"
            );
        }

        if !self.is_leaf() {
            let sub_body = self
                .actions_children()
                .map(|(a, c)| {
                    let ssn = a.try_into_ssn(&self.board()).unwrap();
                    c.to_dot_string_body(&name, &ssn)
                })
                .collect::<Vec<String>>()
                .join("\n");
            let sub_graph = format!(
                "subgraph {{\nnode[fillcolor={:?}]\n{sub_body}\n}}",
                Self::color_to_code(!self.player),
            );
            dot = format!("{dot}\n{sub_graph}");
        }
        dot
    }
}

/// Formats of display used by [`TreeDisplay`].
#[derive(Debug, Clone)]
pub enum TreeDisplayFormat {
    Standard,
}

impl Default for TreeDisplayFormat {
    fn default() -> Self {
        Self::Standard
    }
}

impl TreeDisplayFormat {
    fn typeset(&self, tree: &BoardValueTree) -> String {
        use TreeDisplayFormat::*;
        match self {
            Standard => Self::typeset_standard(tree),
        }
    }

    fn typeset_standard(tree: &BoardValueTree) -> String {
        Self::typeset_standard_core(tree, "", "")
    }

    fn typeset_standard_core(tree: &BoardValueTree, indent: &str, action_ssn: &str) -> String {
        let edge = if action_ssn.is_empty() {
            String::new()
        } else {
            format!("{action_ssn} => ")
        };
        let node = format!(
            "({0:?}, {1}, {2})",
            tree.board().to_simple_string(' ', ";"),
            tree.player(),
            tree.value()
        );
        let next_indent = format!("    {indent}");
        let children = tree
            .actions_children()
            .map(|(a, t)| {
                let ssn = a.try_into_ssn(&tree.board()).unwrap();
                Self::typeset_standard_core(t, &next_indent, &ssn)
            })
            .collect::<Vec<String>>()
            .join("\n");
        if children.is_empty() {
            format!("{indent}{edge}{node}")
        } else {
            format!("{indent}{edge}{node}\n{children}")
        }
    }
}

/// A struct to configure display styles of [`BoardValueTree`].
#[derive(Debug, Clone)]
pub struct TreeDisplay<'a> {
    tree: &'a BoardValueTree,
    format: TreeDisplayFormat,
}

impl<'a> std::fmt::Display for TreeDisplay<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.format.typeset(self.tree))
    }
}

impl<'a> TreeDisplay<'a> {
    fn new(tree: &'a BoardValueTree) -> Self {
        Self {
            tree,
            format: Default::default(),
        }
    }

    pub fn with_format(self, format: TreeDisplayFormat) -> Self {
        Self { format, ..self }
    }
}

// ****************************************************************************
//  Helper Items
// ****************************************************************************
fn validate_args(board: Board, value: BoardValue, rule: GameRule) -> Result<(), error::Error> {
    use error::ArgsValidationErrorKind::*;
    if board.surrounded_status() != SurroundedStatus::None {
        return Err(FinishedGameBoard(board).into());
    }
    if value.is_finished() || value.is_unknown() {
        return Err(UnsupportedValue(value).into());
    }
    if !matches!(rule.suicide_atk_judge(), Judge::NextWins | Judge::LastWins) {
        return Err(DrawJudge.into());
    }
    Ok(())
}

/// A struct representing closed interval between two [`BoardValue`]s.
///
/// An interval is returned by [`evaluate_board`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Interval {
    left: BoardValue,
    right: BoardValue,
}

impl std::fmt::Display for Interval {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[{0}, {1}]", self.left, self.right)
    }
}

impl Interval {
    /// Creates new object.
    pub fn new(left: BoardValue, right: BoardValue) -> Self {
        Self { left, right }
    }

    /// Returns a reference to the left end value.
    pub fn left(&self) -> &BoardValue {
        &self.left
    }

    /// Returns a reference to the right end value.
    pub fn right(&self) -> &BoardValue {
        &self.right
    }

    /// Returns if a given value is between left and right.
    pub fn contains(&self, item: &BoardValue) -> bool {
        self.left <= *item && *item <= self.right
    }

    /// Returns one value in the interval if left and right values are the same.
    ///
    /// # Examples
    /// ```rust
    /// use tokyodoves::analysis::{Interval, BoardValue};
    ///
    /// let win = BoardValue::win(3).unwrap();
    /// let interval1 = Interval::new(win, win);
    /// assert_eq!(Some(win), interval1.single());
    /// let lose = BoardValue::lose(4).unwrap();
    /// let interval2 = Interval::new(lose, win);
    /// assert_eq!(None, interval2.single());
    /// ```
    pub fn single(&self) -> Option<BoardValue> {
        if self.left == self.right {
            Some(self.left)
        } else {
            None
        }
    }
}

// ****************************************************************************
//  Functions for Analysis
// ****************************************************************************
/// Creates an [`BoardValueTree`] that describes routes to ends of the game.
///
/// Once the value of a board in a search process is determined,
/// succeeding edges whose values are not the "next" value are pruned.
/// The following diagram describes what "next" value means:
/// ```text
/// ... -> Win(5) -> Lose(4) -> Win(3) -> Lose(2) -> Win(1)
/// ```
/// Especially, the node with the value `Win(1)` becomes a leaf node,
/// that is, all the succeeding edges are pruned.
///
/// If you know the value of `board` in advance,
/// [`create_checkmate_tree_with_value`], a much faster version,
/// would be more appropriate.
///
/// # Errors
/// Returns `Err` when the argument is invalid. Specifically,
/// the following cases are invalid:
/// - `board` is already finished (at least one boss is surrounded)
/// - `value` is `Unknown`, `Win(even number)` or `Lose(odd or zero)`
/// - `rule.suicide_atk_judge` is `Judge::Draw`
pub fn create_checkmate_tree(
    board: Board,
    player: Color,
    max_depth: usize,
    rule: GameRule,
) -> Result<BoardValueTree, error::Error> {
    validate_args(board, BoardValue::MAX, rule)?;
    Ok(create_checkmate_tree_unchecked(
        board, player, max_depth, rule,
    ))
}

fn create_checkmate_tree_unchecked(
    board: Board,
    player: Color,
    max_depth: usize,
    rule: GameRule,
) -> BoardValueTree {
    if max_depth == 0 {
        return BoardValueTree::new(board, player);
    }

    let mut tree = BoardValueTree::new(board, player);
    tree.value = BoardValue::MIN;

    for (action, next_board, status) in NextBoardIter::new(board, player, rule) {
        use NextBoardStatus::*;
        match status {
            Win => {
                tree.value = BoardValue::win(1).unwrap();
                tree.actions2children.clear();
                NextBoardIter::new(board, player, rule)
                    .filter(|(_, _, s)| matches!(s, Win))
                    .for_each(|(action_, next_board_, _)| {
                        let mut child = BoardValueTree::new(next_board_, player);
                        child.value = BoardValue::finished();
                        tree.actions2children.insert(action_, child);
                    });
                return tree;
            }
            Lose => continue,
            Unknown => {
                let child =
                    create_checkmate_tree_unchecked(next_board, !player, max_depth - 1, rule);
                let child_value_increment = child.value.increment();
                if child_value_increment < tree.value {
                    continue;
                }
                if child_value_increment > tree.value {
                    tree.value = child_value_increment;
                    tree.actions2children.clear();
                }
                tree.actions2children.insert(action, child);
            }
        }
    }
    tree
}

/// Creates an [`BoardValueTree`] that describes routes to ends of the game.
///
/// This function behaves almost similar to [`create_checkmate_tree`],
/// except that it receives `value` ([`BoardValue`]) instead of search depth,
/// and requires `value` coinsides with the value of `board`.
/// This function runs much faster than [`create_checkmate_tree_with_value`]
/// in exchange for restriction of possible arguments.
///
/// # Errors
/// Returns `Err` when the argument is invalid. Specifically,
/// the following cases are invalid:
/// - `board` is already finished (at least one boss is surrounded)
/// - `value` is `Unknown`, `Win(even number)` or `Lose(odd or zero)`
/// - `rule.suicide_atk_judge` is `Judge::Draw`
/// Furthermore, it returns `Err` when the value of `board` differs from `value`.
/// In such a case, returned value contains a variant of [`std::cmp::Ordering`],
/// which means that the value of board is greater (`Greater`) or less (`Less`)
/// than the specified `value`.
pub fn create_checkmate_tree_with_value(
    board: Board,
    value: BoardValue,
    player: Color,
    rule: GameRule,
) -> Result<BoardValueTree, error::Error> {
    validate_args(board, value, rule)?;
    let (tree, cmp) = create_checkmate_tree_with_value_unchecked(board, value, player, rule);
    if cmp == Ordering::Equal {
        Ok(tree)
    } else {
        Err(error::AnalysisError::BoardValueMismatch(cmp).into())
    }
}

fn create_checkmate_tree_with_value_unchecked(
    board: Board,
    value: BoardValue,
    player: Color,
    rule: GameRule,
) -> (BoardValueTree, Ordering) {
    use Ordering::*;
    let mut tree = BoardValueTree::new(board, player);
    tree.value = value;
    let mut cmp = Less;
    for (action, next_board, status) in NextBoardIter::new(board, player, rule) {
        use NextBoardStatus::*;
        match status {
            Win => {
                if value == BoardValue::MAX {
                    cmp = Equal;
                    let mut child = BoardValueTree::new(next_board, !player);
                    child.value = BoardValue::finished();
                    tree.actions2children.insert(action, child);
                    continue;
                } else {
                    tree.actions2children.clear();
                    cmp = Greater;
                    tree.value = BoardValue::unknown();
                    return (tree, cmp);
                }
            }
            Lose => continue,
            Unknown => {
                if value == BoardValue::MAX {
                    continue;
                }
                let next_value = value.try_decrement().unwrap();
                let (child, next_cmp) = create_checkmate_tree_with_value_unchecked(
                    next_board, next_value, !player, rule,
                );
                if next_cmp == Less {
                    tree.value = BoardValue::unknown();
                    tree.actions2children.clear();
                    return (tree, Greater);
                }
                if next_cmp == Equal {
                    tree.actions2children.insert(action, child);
                }
                cmp = cmp.max(next_cmp.reverse());
            }
        }
    }
    if cmp != Equal {
        tree.value = BoardValue::unknown();
        tree.actions2children.clear();
    }
    (tree, cmp)
}

/// Compares the value of specified [`Board`] to a given [`BoardValue`].
///
/// It returns:
/// - `Ok(Greater)` if the value of `board` is greater than `value`,
/// - `Ok(Equal)` if the value of `board` equals to `value`,
/// - `Ok(Less)` if the value of `board` is less than `value`.
///
/// # Errors
/// Returns `Err` only when the argument is invalid. Specifically,
/// the following cases are invalid:
/// - `board` is already finished (at least one boss is surrounded)
/// - `value` is `Unknown`, `Win(even number)` or `Lose(odd or zero)`
/// - `rule.suicide_atk_judge` is `Judge::Draw`
pub fn compare_board_value(
    board: Board,
    value: BoardValue,
    player: Color,
    rule: GameRule,
) -> Result<Ordering, error::Error> {
    validate_args(board, value, rule)?;
    Ok(compare_board_value_unchecked(board, value, player, rule))
}

fn compare_board_value_unchecked(
    board: Board,
    value: BoardValue,
    player: Color,
    rule: GameRule,
) -> Ordering {
    use Ordering::*;
    let mut cmp = Less;
    for (_, next_board, status) in NextBoardIter::new(board, player, rule) {
        use NextBoardStatus::*;
        match status {
            Win => {
                if value == BoardValue::MAX {
                    return Equal;
                } else {
                    return Greater;
                }
            }
            Lose => continue,
            Unknown => {
                if value == BoardValue::MAX {
                    continue;
                }
                let next_val = value.try_decrement().unwrap();
                let next_cmp = compare_board_value_unchecked(next_board, next_val, !player, rule);
                if next_cmp == Less {
                    return Greater;
                }
                cmp = cmp.max(next_cmp.reverse());
            }
        }
    }
    cmp
}

/// Calculates a possible range of [`BoardValue`] of specified [`Board`].
///
/// It searches the value of `board` by pursuing `search_depth` turns forward.
/// The result is returned in [`Interval`], which is a closed interval
/// between two [`BoardValue`]s. It means that the value of the board is in the interval.
///
/// # Errors
/// Returns `Err` only when the argument is invalid. Specifically,
/// the following cases are invalid:
/// - `board` is already finished (at least one boss is surrounded)
/// - `rule.suicide_atk_judge` is `Judge::Draw`
pub fn evaluate_board(
    board: Board,
    player: Color,
    search_depth: usize,
    rule: GameRule,
) -> Result<Interval, error::Error> {
    validate_args(board, BoardValue::MAX, rule)?;
    Ok(evaluate_board_unchecked(board, player, search_depth, rule))
}

fn evaluate_board_unchecked(
    board: Board,
    player: Color,
    search_depth: usize,
    rule: GameRule,
) -> Interval {
    for depth in 1..=search_depth {
        let value = BoardValue::from(Some(depth));
        if matches!(
            compare_board_value_unchecked(board, value, player, rule),
            Ordering::Equal
        ) {
            return Interval::new(value, value);
        }
    }
    let (left_num, right_num) = if search_depth % 2 == 0 {
        (search_depth + 2, search_depth + 1)
    } else {
        (search_depth + 1, search_depth + 2)
    };
    let left = BoardValue::from(Some(left_num));
    let right = BoardValue::from(Some(right_num));
    Interval::new(left, right)
}

/// Collects the best [`Action`]s by [`BoardValue`].
///
/// # Errors
/// Returns `Err` only when the argument is invalid. Specifically,
/// the following cases are invalid:
/// - `board` is already finished (at least one boss is surrounded)
/// - `rule.suicide_atk_judge` is `Judge::Draw`
pub fn find_best_actions(
    board: Board,
    player: Color,
    search_depth: usize,
    rule: GameRule,
) -> Result<Vec<Action>, error::Error> {
    validate_args(board, BoardValue::MAX, rule)?;
    Ok(find_best_actions_unchecked(
        board,
        player,
        search_depth,
        rule,
    ))
}

fn find_best_actions_unchecked(
    board: Board,
    player: Color,
    search_depth: usize,
    rule: GameRule,
) -> Vec<Action> {
    if search_depth == 0 {
        return board
            .legal_actions(player, true, true, *rule.is_remove_accepted())
            .into_iter()
            .collect();
    }

    let value_interval = evaluate_board_unchecked(board, player, search_depth, rule);
    let value = value_interval.single().unwrap_or(BoardValue::unknown());

    let mut actions = Vec::new();
    for (action, next_board, status) in NextBoardIter::new(board, player, rule) {
        use NextBoardStatus::*;
        match status {
            Win => {
                if value != BoardValue::MAX {
                    unreachable!()
                }
                actions.push(action);
                continue;
            }
            Lose => continue,
            Unknown => (),
        }

        if value == BoardValue::MAX {
            continue;
        }

        let next_value = value.try_decrement().unwrap();
        if next_value.is_unknown() {
            if !matches!(
                compare_board_value_unchecked(
                    next_board,
                    value_interval.left().try_decrement().unwrap(),
                    !player,
                    rule
                ),
                Ordering::Greater
            ) {
                actions.push(action);
            }
        } else {
            // next_value is Win or Lose
            if matches!(
                compare_board_value_unchecked(next_board, next_value, !player, rule),
                Ordering::Equal
            ) {
                actions.push(action);
            }
        }
    }
    actions
}

// ************************************************************
//  Tests
// ************************************************************
#[cfg(test)]
mod tests {
    use crate::{analysis::BoardValue, *};

    #[test]
    fn test_evaluate_board() {
        use analysis::BoardValue;
        use std::str::FromStr;
        let rule = game::GameRule::new(true).with_suicide_atk_judge(game::Judge::NextWins);
        let board_value = [
            (" B; a;TH y;b mM", 5),
            (" By;H  a;A m;  Yb", 3),
            ("bB; H;Y h;  T", 3),
            ("T; B b;  yY; t", 3),
            ("hB A;maYT; Htb;M y", 5),
            ("Ba;  H;  hA;MY b", 5),
            (" B;a  b; MtY;T  H", 7),
            ("Y; B;y hA; M b", 5),
            ("bB;T YA", 5),
        ];
        let max_depth = 10; // it must be greater than all n of Win(n)
        for (s, num) in board_value {
            let val = BoardValue::win(num).unwrap();
            let board = BoardBuilder::from_str(s).unwrap().build().unwrap();
            let evaluated = analysis::evaluate_board(board, Color::Red, max_depth, rule).unwrap();
            assert_eq!(evaluated.single().unwrap(), val);
        }
    }

    #[test]
    fn test_compare_value() {
        use analysis::BoardValue;
        use std::str::FromStr;
        let rule = game::GameRule::new(true).with_suicide_atk_judge(game::Judge::NextWins);
        let board_value = [
            (" B; a;TH y;b mM", 5),
            (" By;H  a;A m;  Yb", 3),
            ("bB; H;Y h;  T", 3),
            ("T; B b;  yY; t", 3),
            ("hB A;maYT; Htb;M y", 5),
            ("Ba;  H;  hA;MY b", 5),
            (" B;a  b; MtY;T  H", 7),
            ("Y; B;y hA; M b", 5),
            ("bB;T YA", 5),
        ];
        for (s, num) in board_value {
            let val = BoardValue::win(num).unwrap();
            let board = BoardBuilder::from_str(s).unwrap().build().unwrap();
            let cmp = analysis::compare_board_value(board, val, Color::Red, rule);
            assert!(matches!(cmp, Ok(std::cmp::Ordering::Equal)));
        }
    }

    #[test]
    fn test_checkmate_tree() {
        use std::str::FromStr;
        let rule = game::GameRule::new(true).with_suicide_atk_judge(game::Judge::NextWins);
        let board_value = [
            (" B; a;TH y;b mM", 5),
            (" By;H  a;A m;  Yb", 3),
            ("bB; H;Y h;  T", 3),
            ("T; B b;  yY; t", 3),
            ("hB A;maYT; Htb;M y", 5),
            ("bB;T YA", 5),
        ];
        for (s, num) in board_value {
            let board = BoardBuilder::from_str(s).unwrap().build().unwrap();
            let tree = analysis::create_checkmate_tree(board, Color::Red, num, rule).unwrap();
            assert_eq!(tree.depth(), num + 1);
            assert!(tree.is_good_for_puzzle(num - 2));
        }
    }

    #[test]
    fn test_checkmate_tree_with_value() {
        use std::str::FromStr;
        let rule = game::GameRule::new(true).with_suicide_atk_judge(game::Judge::NextWins);
        let board_value = [
            (" B; a;TH y;b mM", 5),
            (" By;H  a;A m;  Yb", 3),
            ("bB; H;Y h;  T", 3),
            ("T; B b;  yY; t", 3),
            ("hB A;maYT; Htb;M y", 5),
            ("Ba;  H;  hA;MY b", 5),
            (" B;a  b; MtY;T  H", 7),
            ("Y; B;y hA; M b", 5),
            ("bB;T YA", 5),
        ];
        for (s, num) in board_value {
            let val = BoardValue::win(num).unwrap();
            let board = BoardBuilder::from_str(s).unwrap().build().unwrap();
            let tree =
                analysis::create_checkmate_tree_with_value(board, val, Color::Red, rule).unwrap();
            assert_eq!(tree.depth(), num + 1);
            assert!(tree.is_good_for_puzzle(num - 2));
        }
    }
}
