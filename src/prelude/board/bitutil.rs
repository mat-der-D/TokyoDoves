//! Utility functions for bit manupulations.
use array_macro::array;

use crate::prelude::shift::Shift;

const BIT_SIDES: [u64; 64] = {
    let sides0 = calc_sides(1);
    array![n => sides0.rotate_left(n as u32); 64]
};

const BIT_ADJS: [u64; 64] = {
    let adj0 = calc_adjacents(1);
    array![n => adj0.rotate_left(n as u32); 64]
};

pub struct HotBitIter {
    bits: u64,
}

impl From<u64> for HotBitIter {
    fn from(value: u64) -> Self {
        HotBitIter { bits: value }
    }
}

impl Iterator for HotBitIter {
    type Item = u64;
    fn next(&mut self) -> Option<Self::Item> {
        if self.bits != 0 {
            let unit = 1 << self.bits.trailing_zeros();
            self.bits &= !unit;
            Some(unit)
        } else {
            None
        }
    }
}

pub const fn calc_sides(bits: u64) -> u64 {
    let mut sides = 0;
    sides |= bits.rotate_right(8);
    sides |= bits.rotate_right(1);
    sides |= bits.rotate_left(1);
    sides |= bits.rotate_left(8);
    sides
}

pub const fn calc_adjacents(bits: u64) -> u64 {
    let mut adj = 0;
    adj |= bits.rotate_left(1);
    adj |= bits.rotate_right(1);
    adj |= adj.rotate_left(8);
    adj |= adj.rotate_right(8);
    adj |= bits.rotate_left(8);
    adj |= bits.rotate_right(8);
    adj
}

pub fn sides_of_bit(bit: u64) -> u64 {
    BIT_SIDES[bit.trailing_zeros() as usize]
}

pub fn adjacents_of_bit(bit: u64) -> u64 {
    BIT_ADJS[bit.trailing_zeros() as usize]
}

pub const fn apply_shift(bit: u64, shift: Shift) -> u64 {
    let n = ((shift.dh + shift.dv * 8) % 64 + 64) as u32;
    bit.rotate_left(n)
}

pub fn create_shift_from_bits(bit_from: u64, bit_to: u64) -> Shift {
    let n_from = bit_from.trailing_zeros();
    let n_to = bit_to.trailing_zeros();
    let n_shift = (64 + n_to - n_from) % 64;
    let dh = ((n_shift + 3) & 0b111) as i8 - 3;
    let dv = (((n_shift + 27) >> 3) & 0b111) as i8 - 3;
    Shift { dh, dv }
}
