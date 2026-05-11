use rustc_hash::FxHashMap;
use ustr::Ustr;

use crate::{runtime, ssa::{self, InstructionIdentity}};

struct Frame<'a> {

  /// The function corresponding to this frame.
  function: &'a ssa::Function,

  /// The position of the program counter, relative to `function`.
  pc: Option<ssa::InstructionIdentity>,

  locals: FxHashMap<ssa::Value, runtime::Value>,
}

/// The state of an SSA IR interpreter.
pub struct EvaluationContext<'a> {

  /// The program being interpreter.
  pub program: &'a ssa::Program<'a>,

  /// The call frames of the interpreter, from oldest to most recent.
  frames: Vec<Frame<'a>>,

  memory: FxHashMap<u64, runtime::Value>,

  current_memory_index: u64
}

/// How to update a program counter after the evaluation of a single instruction.
pub enum Step {

  /// Moves to the next instruction.
  Advance,

  /// Moves to the start of the given basic block.
  Goto(ssa::BlockIdentity),

  /// Returns from the current function with the given value.
  Return(runtime::Value),

}

impl <'a> EvaluationContext<'a> {

  /// Creates a new instance for interpreting the contents of `program`.
  pub fn new(program: &'a ssa::Program) -> Self {
    Self { program, frames: vec![] , memory: FxHashMap::default(), current_memory_index: 0}
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
    let frame = self.top();
    let i = frame.pc.unwrap();
    frame.pc = frame.function.instruction_after(i);
  }

  /// Set the `pc` to the next instruction after `i`
  pub fn goto(&mut self, i: ssa::BlockIdentity) {
    let frame = self.top();
    self.top().pc = frame.function.block(i).instructions().next();
  }

  /// Pushes a new call frame with the given properties.
  pub fn push_frame(
    &mut self, function: &'a ssa::Function, pc: Option<ssa::InstructionIdentity>
  ) {
    self.frames.push(Frame { function, pc , locals: FxHashMap::default()})
  }

  /// Pops the most recent call frame, assuming there is one.
  pub fn pop_frame(&mut self) {
    self.frames.pop();
  }

  /// Returns a reference to the most recent call frame.
  fn top(&mut self) -> &mut Frame<'a> {
    self.frames.last_mut().unwrap()
  }

  /// Returns a clone of the value stored in the top frame locals at `v`
  /// Panics if not defined
  pub fn get_local(&mut self, v: &ssa::Value) -> runtime::Value {
    self.top().locals.get(v).unwrap().clone()
  }

  /// Returns a clone of the value stored in memory at `a`
  /// Panic if index not defined
  pub fn get_memory(&mut self, a: &u64) -> runtime::Value {
    self.memory.get(a).unwrap().clone()
  }

  /// Set the value of the memory at the adress contained in `locals[a]`
  pub fn set_memory(&mut self, a: runtime::Value, v: runtime::Value) {
    let runtime::Value::MemoryAdress(ma) = a else {
      panic!("unreachable: the index to set memory should be a 'MemoryAdress'");
    };
    self.memory.insert(ma, v);
  }

  /// Sets the local at index `a` to `v` in the current `frame`
  pub fn set_local(&mut self, a: ssa::Value, v: runtime::Value) -> Option<runtime::Value> {
    self.top().locals.insert(a, v)
  }

  /// Set a local value with the current program counter as key
  pub fn set_local_at_current_position(&mut self, v: runtime::Value) -> Option<runtime::Value>{
    let k = ssa::Value::Register(self.get_pc().unwrap());
    self.top().locals.insert(k, v)
  }

  /// Returns the current program counter
  pub fn get_pc(&mut self) -> Option<InstructionIdentity> {
    self.top().pc
  }

  /// Reserve a new memory slot, and returns its index
  pub fn allocate(&mut self) -> u64 {
    self.current_memory_index += 1;
    self.current_memory_index
  }

  /// Convert a `ssa::Value` to a `runtime::Value`, using `self` as context
  pub fn to_runtime_value(&mut self, v: &ssa::Value) -> runtime::Value {
    match v {
      ssa::Value::Register(_) => {
        self.get_local(v)
      },
      ssa::Value::Boolean(b) => {
        runtime::Value::Boolean(*b)
      },
      ssa::Value::Integer(i) => {
        runtime::Value::Integer(Box::new(runtime::value::Integer::from_u64(i.bits)))
      },
      ssa::Value::Parameter(_) => {
        let runtime::Value::MemoryAdress(m) = self.get_local(v) else {
          panic!("unreachable: parameter does not point to a memory adress")
        };
        self.get_memory(&m)
      },
      ssa::Value::Dictionary(d) => {
        let mut t: Vec<runtime::Value> = vec![];
        for v in d {
          t.push(self.to_runtime_value(v));
        };
        runtime::Value::Dictionnary(t)
      },
      ssa::Value::Function(r) => {
        runtime::Value::Function(r.clone())
      },
      _ => {
        todo!("not implemented for v : {:?}", v)
      }
    }
  }
}
