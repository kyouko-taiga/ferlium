use std::any::Any;
use std::fmt;

use crate::{
  Location,
  list,
  ssa, r#type::Type,
};

/// The identity of an instruction in the context of its containing funtion.
pub type InstructionIdentity = list::Address;

/// An instruction in the SSA form of Ferlium.
pub struct Instruction {

  /// The region of the code corresponding to this instruction.
  pub span: Location,

  /// The operands of the instruction.
  pub operands: Vec<ssa::Value>,

  /// The kind-specific part of `self`.
  pub kind: Box<dyn InstructionKind>,

}

impl Instruction {

  /// The type of the instruction's result.
  pub fn result(&self) -> InstructionResult {
    self.kind.result()
  }

  /// Returns `true` iff `self` is a terminator.
  pub fn is_terminator(&self) -> bool {
    self.kind.is_terminator()
  }

  /// Creates a 'call' instruction with the given properties.
  pub fn call<T: IntoIterator<Item = ssa::Value>>(
    span: Location, callee: ssa::Value, arguments: T, ty: Type
  ) -> Self {
    let mut operands = vec![callee];
    operands.extend(arguments);
    Instruction { span, operands, kind: Box::new(Call { ty }) }
  }

  /// Creates a 'ret' instruction with the given properties.
  pub fn ret(span: Location, value: ssa::Value) -> Self {
    Instruction { span, operands: vec![value], kind: Box::new(Ret {}) }
  }

}

impl fmt::Display for Instruction {

  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    self.kind.fmt_within(f, self)
  }

}

/// A type encoding the kind-specific contents of an instruction.
pub trait InstructionKind: Any {

  /// The type of the instruction's result.
  fn result(&self) -> InstructionResult { InstructionResult::Nothing }

  /// Returns `true` iff `self` is a terminator.
  fn is_terminator(&self) -> bool { false }

  /// Computes a textual representation of `self`, which is the kind-specific part of `whole`.
  fn fmt_within(&self, f: &mut fmt::Formatter<'_>, whole: &Instruction) -> std::fmt::Result;

}

/// The type of an instruction's result.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum InstructionResult {

  /// A type expressible in Ferlium.
  Lowered(Type),

  /// The type of a SSA value.
  Same(ssa::Value),

  /// The type of an isntruction that doesn't produce any value.
  Nothing,

}

struct Call {

  /// The type of the value returned by the callee.
  pub ty: Type,

}

impl InstructionKind for Call {

  fn result(&self) -> InstructionResult {
    InstructionResult::Lowered(self.ty)
  }

  fn fmt_within(&self, f: &mut fmt::Formatter<'_>, whole: &Instruction) -> fmt::Result {
    write!(f, "call {}(", whole.operands[0])?;
    for i in 1..whole.operands.len() {
      if i > 1 { write!(f, ", ")?; }
      write!(f, "{}", whole.operands[i])?;
    }
    write!(f, ")")
  }

}

struct Ret {}

impl InstructionKind for Ret {

  fn fmt_within(&self, f: &mut fmt::Formatter<'_>, whole: &Instruction) -> fmt::Result {
    write!(f, "ret {}", whole.operands[0])
  }

}
