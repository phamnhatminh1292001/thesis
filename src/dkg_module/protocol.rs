use core::cmp::Ordering;
use core::fmt::{Error, Formatter};

use std::cmp::Ordering::{Equal, Greater, Less};
use std::fmt::{Debug, Display};

#[derive(Clone, Copy, Hash, Eq, PartialEq)]
pub struct PartyIndex(pub [u8; 32]);

impl PartyIndex {
    pub fn from_slice(slice: &[u8]) -> Self {
        let mut result = [0u8; 32];
        result.clone_from_slice(slice);
        PartyIndex(result)
    }

    fn write_as_hex_str(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        self.0.iter().rev().try_for_each(|x| write!(f, "{:02X}", x))
    }
}

impl Default for PartyIndex {
    fn default() -> Self {
        PartyIndex([0u8; 32])
    }
}

impl Display for PartyIndex {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        self.write_as_hex_str(f)
    }
}

impl Debug for PartyIndex {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        self.write_as_hex_str(f)
    }
}

impl From<usize> for PartyIndex {
    fn from(x: usize) -> Self {
        let mut result = [0u8; 32];
        let bytes = x.to_le_bytes();
        result[..bytes.len()].clone_from_slice(&bytes);
        PartyIndex(result)
    }
}

impl Ord for PartyIndex {
    fn cmp(&self, other: &Self) -> Ordering {
        if self.eq(other) {
            return Equal;
        }
        if self.0.iter().lt(other.0.iter()) {
            Less
        } else {
            Greater
        }
    }
}

impl PartialOrd for PartyIndex {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
