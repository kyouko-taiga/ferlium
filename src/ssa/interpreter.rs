use ustr::Ustr;

use crate::ssa;

struct Frame<'a> {

  /// The function corresponding to this frame.
  function: &'a ssa::Function,

  /// The position of the program counter, relative to `function`.
  pc: Option<ssa::InstructionIdentity>,

}

/// The state of an SSA IR interpreter.
pub struct EvaluationContext<'a> {

  /// The program being interpreter.
  program: &'a ssa::Program,

  /// The call frames of the interpreter, from oldest to most recent.
  frames: Vec<Frame<'a>>,

}

/// How to update a program counter after the evaluation of a single instruction.
pub enum Step {

  /// Moves to the next instruction.
  Advance,

  /// Moves to the start of the given basic block.
  Goto(ssa::BlockIdentity),

  /// Returns from the current function with the given value.
  Return(ssa::Value),

}

impl <'a> EvaluationContext<'a> {

  /// Creates a new instance for interpreting the contents of `program`.
  pub fn new(program: &'a ssa::Program) -> Self {
    Self { program, frames: vec![] }
  }

  /// Returns a reference to the function having the given `name`, if any.
  pub fn function(&self, name: Ustr) -> Option<&'a ssa::Function> {
    self.program.function(name)
  }

  /// Evaluates the instruction referred to by the program counter.
  pub fn step(&mut self) -> Step {
    let frame = self.top();
    let i = frame.pc.unwrap();
    frame.function.at(i).evaluate(self)
  }

  /// Advances the program counter to the instruction immediately after the current one.
  pub fn advance(&mut self) {
    let mut frame = self.top();
    let i = frame.pc.unwrap();
    frame.pc = frame.function.instruction_after(i);
  }

  pub fn goto(&mut self, i: ssa::BlockIdentity) {
    let frame = self.top();
    self.top().pc = frame.function.block(i).instructions().next();
  }

  /// Pushes a new call frame with the given properties.
  pub fn push_frame(
    &mut self, function: &'a ssa::Function, pc: Option<ssa::InstructionIdentity>
  ) {
    self.frames.push(Frame { function, pc })
  }

  /// Pops the most recent call frame, assuming there is one.
  pub fn pop_frame(&mut self) {
    self.frames.pop();
  }

  /// Returns a reference to the most recent call frame.
  fn top(&mut self) -> &mut Frame<'a> {
    self.frames.last_mut().unwrap()
  }

}
