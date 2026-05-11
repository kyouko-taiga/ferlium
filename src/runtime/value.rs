use std::fmt;

use crate::{ssa::value::FunctionReference};

/// A runtime value
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Value {
  /// A memory adress
  MemoryAdress(u64),

  /// A constant boolean
  Boolean(bool),

  /// A dictionnary
  Dictionnary(Vec<Self>),

  /// A runtime function
  Function(FunctionReference),

  /// A constant integer
  Integer(Box<Integer>),

  /// A unit value
  Unit
}

impl fmt::Display for Value {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Value::MemoryAdress(i) => write!(f, "#{}", i),
      Value::Unit => write!(f, "()"),
      Value::Boolean(i) => write!(f, "{}", i),
      Value::Integer(i) => i.fmt(f),
      Value::Dictionnary(d) => write!(f, "{:?}", d),
      Value::Function(d) => write!(f, "{}", d.representation),
    }
  }
}


/// A constant integer, represented as a two's complement value.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Integer {
  /// The bit pattern of the value. Only the `bit_width` least significant bits are relevant.
  pub bits: u64,

  /// The number of bits in the representation of `self`.
  pub bit_width: u8,

  /// `true` iff the representation of `self` is signed.
  pub signed: bool,
}

impl Integer {
  pub fn from_isize(value: isize) -> Self {
    Self {
      bits: isize::cast_unsigned(value) as u64,
      bit_width: 32,
      signed: true,
    }
  }

  pub fn from_u32(value: u32) -> Self {
    Self {
      bits: value.into(),
      bit_width: 32,
      signed: false,
    }
  }

  pub fn from_u64(value: u64) -> Self {
    Self {
      bits: value,
      bit_width: 64,
      signed: false
    }
  }

  pub fn from_i32(value: i32) -> Self {
    Self {
      bits: i32::cast_unsigned(value).into(),
      bit_width: 32,
      signed: true,
    }
  }
}

impl fmt::Display for Integer {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    if self.signed {
      write!(f, "{}", u64::cast_signed(self.bits))
    } else {
      write!(f, "u{}", self.bits)
    }
  }
}
