use std::fmt;

use itertools::Itertools;
use ustr::Ustr;

use crate::{module::{LocalFunctionId, ModuleId, TraitDictionaryId}, ssa};

/// A value in the SSA form of Ferlium.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Value {

  /// A constant boolean
  Boolean(bool),

  /// A dictionary value
  Dictionary(TraitDictionary),

  /// A reference to a lowered function.
  Function(FunctionReference),

  /// A constant integer.
  Integer(Box<Integer>),

  /// The `i`-th parameter of a function.
  Parameter(usize),

  /// The register assigned by an instruction.
  Register(ssa::InstructionIdentity),

  /// A unit value.
  Unit,

}

impl fmt::Display for Value {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Value::Boolean(i) => write!(f, "i1 {}", *i as u8),
      Value::Dictionary(t) => {
        write!(f, "({})", t.values.iter().map(|v| format!("{}", v)).join(", "))
      },
      Value::Function(i) => write!(f, "{}", i.representation),
      Value::Integer(i) => i.fmt(f),
      Value::Parameter(i) => write!(f, "%p{}", i),
      Value::Register(i) => write!(f, "%r{}", i.raw()),
      Value::Unit => write!(f, "()")
    }
  }
}



/// A SSA TraitDictionnary, represented by its identity and its values
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct TraitDictionary {
  /// The identity of this trait dictionnary
  pub identity: TraitDictionaryId,

  /// The value fo this trait dictionnary
  pub values: Vec<ssa::Value>
}

/// A function reference, represented as its reference, and its representation
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct FunctionReference {
  /// The string representation of `self`.
  pub representation: Ustr,

  /// The module id in which the function is defined.
  pub module: ModuleId,

  /// The LocalFunctionId in the module in which the function is declared.
  pub identity: LocalFunctionId,
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
      bits: (value as i64) as u64,
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

  pub fn from_i32(value: i32) -> Self {
    Self {
      bits: (value as i64) as u64,
      bit_width: 32,
      signed: true,
    }
  }

  pub fn from_u64(value: u64) -> Self {
    Self {
      bits: value,
      bit_width: 64,
      signed: false
    }
  }

  pub fn to_isize(self) -> isize {
    self.bits as isize
  }
}

impl fmt::Display for Integer {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    if self.signed {
      write!(f, "i{} {}", self.bit_width, u64::cast_signed(self.bits))
    } else {
      write!(f, "u{} {}", self.bit_width, self.bits)
    }
  }
}
