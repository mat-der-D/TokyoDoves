use crate::prelude::board::main::Board;
use crate::prelude::pieces::color_dove_to_char;

#[derive(Debug, Clone)]
pub enum BoardDisplayFormat {
    /// The first board will be displayed as below:
    /// ```text
    /// +---+---+---+---+
    /// | b |   |   |   |
    /// +---+---+---+---+
    /// | B |   |   |   |
    /// +---+---+---+---+
    /// |   |   |   |   |
    /// +---+---+---+---+
    /// |   |   |   |   |
    /// +---+---+---+---+
    /// ```
    Framed,
    /// The first board will be displayed as below (for `empty='-'`, `delimiter=String::from(";")`):
    /// ```text
    /// b---;B---;----;----
    /// ```
    Simple { empty: char, delimiter: String },
}

impl Default for BoardDisplayFormat {
    fn default() -> Self {
        Self::Framed
    }
}

impl BoardDisplayFormat {
    fn typeset(&self, board: &Board) -> String {
        use BoardDisplayFormat::*;
        match self {
            Framed => Self::typeset_standard(board),
            Simple { empty, delimiter } => Self::typeset_simple(board, *empty, delimiter),
        }
    }

    fn typeset_standard(board: &Board) -> String {
        let hframe = "+---+---+---+---+".to_string();
        let mut lines = Vec::new();
        for line in board.to_4x4_matrix() {
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

    fn typeset_simple(board: &Board, empty: char, delimiter: &str) -> String {
        let mut lines = Vec::new();
        for line in board.to_4x4_matrix() {
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

#[derive(Debug, Clone)]
pub struct BoardDisplay<'a> {
    board: &'a Board,
    format: BoardDisplayFormat,
}

impl<'a> BoardDisplay<'a> {
    pub(crate) fn new(board: &'a Board) -> Self {
        Self {
            board,
            format: Default::default(),
        }
    }

    pub fn with_format(self, format: BoardDisplayFormat) -> Self {
        Self { format, ..self }
    }
}

impl<'a> std::fmt::Display for BoardDisplay<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.format.typeset(self.board))
    }
}
