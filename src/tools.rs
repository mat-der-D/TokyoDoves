//! Convenient tools to analyze the game
use crate::prelude::{Board, Color, SurroundedStatus, WinnerJudgement};

#[derive(Debug, Clone, Copy, thiserror::Error)]
pub enum WinnerJudgementConvertError {
    #[error("[DrawProhibited]")]
    DrawProhibited,
}

#[derive(Debug, Clone, Copy)]
pub enum WinnerJudgementNoDraw {
    LastPlayer,
    NextPlayer,
}

impl TryFrom<WinnerJudgement> for WinnerJudgementNoDraw {
    type Error = WinnerJudgementConvertError;
    fn try_from(judgement: WinnerJudgement) -> Result<Self, Self::Error> {
        use WinnerJudgement::*;
        match judgement {
            NextPlayer => Ok(WinnerJudgementNoDraw::NextPlayer),
            LastPlayer => Ok(WinnerJudgementNoDraw::LastPlayer),
            Draw => Err(WinnerJudgementConvertError::DrawProhibited),
        }
    }
}

/// Value of board
#[derive(Debug, Clone, Copy)]
pub enum BoardValue {
    /// `Win(n)` means the player will win in `n` turns at least
    Win(usize),
    /// `Lose(n)` means the player will lose in `n` turns at most
    Lose(usize),
    /// Cannot detect win or lose
    Unknown,
}

/// Compare `value` and the value of `board`.
///
/// It returns `Ok(-1)`, `Ok(0)` or `Ok(1)` when the argument is valid.
pub fn compare_board_value(
    value: &BoardValue,
    board: &Board,
    player: Color,
    allow_remove: bool,
    surrounding_judgement: WinnerJudgementNoDraw,
) -> Result<i8, &'static str> {
    use BoardValue::*;
    use SurroundedStatus::*;
    if !matches!(board.surrounded_status(), None) {
        return Err("invalid board: already finished");
    }
    let n = match value {
        Win(n) => {
            if n % 2 == 1 {
                *n
            } else {
                return Err("n of BoardValue::Win(n) must be odd");
            }
        }
        Lose(n) => {
            if (*n != 0) && (n % 2 == 0) {
                *n
            } else {
                return Err("n of BoardValue::Lose(n) must be positive and even");
            }
        }
        Unknown => return Err("BoardValue::Unknown is not supported"),
    };
    let wins_if_both = matches!(surrounding_judgement, WinnerJudgementNoDraw::LastPlayer);
    Ok(compare_board_value_core(
        n,
        board,
        player,
        allow_remove,
        wins_if_both,
    ))
}

fn compare_board_value_core(
    n: usize,
    board: &Board,
    player: Color,
    allow_remove: bool,
    wins_if_both: bool,
) -> i8 {
    let mut cmp = if n == 2 { 0 } else { -1 };
    for action in board.legal_actions(player, true, true, allow_remove) {
        // println!("n: {}, action: {:?}", n, action);
        let next_board = board
            .perform_unchecked_copied(action)
            .expect("illegal action from Board::legal_actions");

        use SurroundedStatus::*;
        let status = next_board.surrounded_status();
        let is_both = matches!(status, Both);
        if (wins_if_both && is_both) || matches!(status, OneSide(p) if p != player) {
            return if n == 1 { 0 } else { 1 };
        } else if (n == 1)
            || (!wins_if_both && is_both)
            || matches!(status, OneSide(p) if p == player)
        {
            continue;
        } else {
            let next_cmp =
                compare_board_value_core(n - 1, &next_board, !player, allow_remove, wins_if_both);
            if next_cmp == -1 {
                return 1;
            }
            cmp = cmp.max(-next_cmp);
        }
    }
    cmp
}

#[cfg(test)]
mod tests {
    use crate::*;

    #[test]
    fn test_compare_value() {
        use std::str::FromStr;
        use tools::BoardValue::*;
        let allow_remove = true;
        let judge = tools::WinnerJudgementNoDraw::NextPlayer;
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
            let cmp = tools::compare_board_value(&val, &board, Color::Red, allow_remove, judge);
            assert_eq!(cmp, Ok(0));
        }
    }
}
