//! Position holders

use super::bitutil::calc_adjacents;
use super::container::DoveSet;
use crate::prelude::pieces::{color_to_index, dove_to_index, Color, Dove};

/// [`Dove`] -> position
#[derive(Debug, Clone, Copy, Default)]
pub struct DovePositions {
    positions: [u64; 6], // B, A, Y, M, T, H
}

impl DovePositions {
    pub fn new(positions: [u64; 6]) -> Self {
        DovePositions { positions }
    }

    fn set_position(&mut self, dove: Dove, bit: u64) {
        // safety is guaranteed because dove_to_index returns 0~5
        let i = dove_to_index(dove);
        unsafe {
            *self.positions.get_unchecked_mut(i) = bit;
        }
    }

    fn position_of(&self, dove: Dove) -> &u64 {
        // safety is guaranteed because dove_to_index returns 0~5
        let i = dove_to_index(dove);
        unsafe { self.positions.get_unchecked(i) }
    }

    fn union(&self) -> u64 {
        self.positions.into_iter().fold(0, |union, x| union | x)
    }

    fn union_except(&self, dove: Dove) -> u64 {
        let index = dove_to_index(dove);
        self.positions
            .iter()
            .enumerate()
            .filter(|(i, _)| *i != index)
            .fold(0, |union, (_, pos)| union | *pos)
    }

    fn doves_in_hand(&self) -> DoveSet {
        let hash = self
            .positions
            .into_iter()
            .enumerate()
            .fold(0, |cum, (i, x)| cum | (((x == 0) as u8) << i));
        DoveSet { hash }
    }

    fn doves_on_field(&self) -> DoveSet {
        let hash = self
            .positions
            .into_iter()
            .enumerate()
            .fold(0, |cum, (i, x)| cum | (((x != 0) as u8) << i));
        DoveSet { hash }
    }
}

/// [`Color`] -> [`DovePositions`],
/// inducing ([`Color`], [`Dove`]) -> position
#[derive(Debug, Clone, Copy, Default)]
pub struct ColorDovePositions {
    positions: [DovePositions; 2],
}

impl ColorDovePositions {
    pub fn new(positions: [DovePositions; 2]) -> Self {
        Self { positions }
    }

    pub fn dove_positions(&self, color: Color) -> &DovePositions {
        // safety is guaranteed because color_to_index return 0 or 1
        let i = color_to_index(color);
        unsafe { self.positions.get_unchecked(i) }
    }

    pub fn dove_positions_mut(&mut self, color: Color) -> &mut DovePositions {
        // safety is guaranteed because color_to_index return 0 or 1
        let i = color_to_index(color);
        unsafe { self.positions.get_unchecked_mut(i) }
    }

    pub fn set_position(&mut self, color: Color, dove: Dove, bit: u64) {
        self.dove_positions_mut(color).set_position(dove, bit);
    }

    pub fn position_of(&self, color: Color, dove: Dove) -> &u64 {
        self.dove_positions(color).position_of(dove)
    }

    pub fn union(&self) -> u64 {
        self.positions.into_iter().fold(0, |cum, p| cum | p.union())
    }

    pub fn union_in_color(&self, color: Color) -> u64 {
        self.dove_positions(color).union()
    }

    pub fn union_except(&self, color: Color, dove: Dove) -> u64 {
        self.dove_positions(color).union_except(dove) | self.union_in_color(!color)
    }

    pub fn doves_in_hand(&self, color: Color) -> DoveSet {
        self.dove_positions(color).doves_in_hand()
    }

    pub fn doves_on_field(&self, color: Color) -> DoveSet {
        self.dove_positions(color).doves_on_field()
    }

    pub fn swap_color(&mut self) {
        self.positions.swap(0, 1);
    }

    pub fn isolated(&self) -> bool {
        let all = self.union();
        all != all & calc_adjacents(all)
    }
}
