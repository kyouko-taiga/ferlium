use std::fmt;

use rustc_hash::FxHashMap;


use crate::{CompilerSession, eval::EvalCtx, hir::{self, value::{FunctionValue, NativeDisplay}}, module::{LocalFunctionId, ModuleId}, ssa::{self, interpreter}};

/// A key uniquely identifying a function across modules.
#[derive(Hash, Eq, PartialEq, Clone)]
pub struct FunctionKey {
  pub module: ModuleId,

  pub identity: LocalFunctionId
}

impl FunctionKey {
  /// Returns a `FunctionKey` created from `fv`
  pub fn from_function_value(fv: &FunctionValue) -> Self {
    Self {
      module: fv.module_id,
      identity: fv.function_id
    }
  }
}

/// Returns a copy of a `hir` value iff it is a primitive type. Returns `None` otherwise.
fn copy_primitive(v: &hir::value::Value) -> Option<hir::value::Value> {
  if let Some(l) = v.to_literal_value() {
    Some(l.into_value())
  } else {
    // This case handles the copy of the memory address
    let addr = v.as_primitive_ty::<MemoryAddress>()?;
    Some(hir::value::Value::native(MemoryAddress(addr.0)))
  }
}

/// An address in the memory of the `EvaluationContext`
#[derive(Debug, Clone)]
pub struct MemoryAddress(pub u64);


impl MemoryAddress {

  /// Returns a new instance of `self` created from `a`
  pub fn new(a:u64) -> hir::value::Value {
    hir::value::Value::native(MemoryAddress(a))
  }
}

impl NativeDisplay for MemoryAddress {
    fn fmt_repr(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "#{}", self.0)
    }
}


/// Compare two HIR values and returns `true` iff the two values have the same type AND the same value
pub fn ssa_eq(a: & hir::value::Value, b: & hir::value::Value) -> bool {
  match (a, b) {
    (hir::value::Value::Native(a), hir::value::Value::Native(b)) => {
      if let (Some(a), Some(b)) = (a.as_any().downcast_ref::<isize>(), b.as_any().downcast_ref::<isize>()) { a == b }
      else if let (Some(a), Some(b)) = (a.as_any().downcast_ref::<bool>(), b.as_any().downcast_ref::<bool>()) { a == b }
      else if let (Some(a), Some(b)) = (a.as_any().downcast_ref::<u64>(), b.as_any().downcast_ref::<u64>()) { a == b }
      else if let (Some(_), Some(_)) = (a.as_any().downcast_ref::<()>(), b.as_any().downcast_ref::<()>()) { true }
      else if let (Some(MemoryAddress(a)), Some(MemoryAddress(b))) = (a.as_any().downcast_ref::<MemoryAddress>(), b.as_any().downcast_ref::<MemoryAddress>()) { a == b }
      else { false }
    },
    _ => false
  }
}

impl std::fmt::Display for hir::value::Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.format_as_string_repr(f)
    }
}

/// A function frame in the `EvaluationContext`
struct Frame {

  /// The index of the function corresponding to this frame
  key: FunctionKey,

  /// The position of the program counter, relative to `function_name`.
  pc: Option<ssa::InstructionIdentity>,

  locals: FxHashMap<ssa::Value, hir::value::Value>,
}

/// The state of an SSA IR interpreter.
pub struct EvaluationContext<'a> {

  /// The call frames of the interpreter, from oldest to most recent.
  frames: Vec<Frame>,

  /// The memory hashmap of the SSA interpreter
  memory: FxHashMap<u64, hir::value::Value>,

  /// The current stack pointer for the memory indexes.
  current_memory_index: u64,

  /// The HIR context, used to call the STD functions
  pub(crate) hir_context: EvalCtx<'a>,

  /// A temporary cache to hold a created `hir::value::Value`, of which a reference is returned
  value_cache: hir::value::Value
}

/// How to update a program counter after the evaluation of a single instruction.
pub enum Step {

  /// Moves to the next instruction.
  Advance,

  /// Moves to the start of the given basic block.
  Goto(ssa::BlockIdentity),

  /// Returns from the current function with the given value.
  Return(hir::value::Value),

}

impl <'a> EvaluationContext<'a> {

  /// Creates a new instance for interpreting the contents of `program`.
  pub fn new(module_id: ModuleId, session: &'a CompilerSession) -> Self {
    Self { frames: vec![] , memory: FxHashMap::default(), current_memory_index: 0, hir_context: EvalCtx::new(module_id, session), value_cache: hir::value::Value::uninit()}
  }

  /// Evaluates the instruction referred to by the program counter.
  pub fn step(&mut self, program: &ssa::Program) -> Step {
    let (key, i) = {
      let frame = self.top();
      (&frame.key, frame.pc.unwrap())
    };
    let instr = program.function(key).expect("function with `key` not found.").at(i);
    instr.evaluate(self, program)
  }

  /// Advances the program counter to the instruction immediately after the current one.
  pub fn advance(&mut self, program: &ssa::Program) {
    let (key, i) = {
      let frame = self.top();
      (&frame.key, frame.pc.unwrap())
    };
    self.top().pc = program.function(key).expect("function with `key` not found").instruction_after(i);
  }

  /// Set the `pc` to the next instruction after `i`
  pub fn goto(&mut self, block: ssa::BlockIdentity, program: &ssa::Program) {
    let key = {
      let frame = self.top();
      &frame.key
    };
    self.top().pc = program.function(key).expect("function with `key` not found.").block(block).instructions().next();
  }

  /// Pushes a new call frame with the given properties.
  pub fn push_frame(
    &mut self, key: interpreter::FunctionKey, pc: Option<ssa::InstructionIdentity>
  ) {
    self.frames.push(Frame { key: key, pc , locals: FxHashMap::default()})
  }

  /// Pops the most recent call frame, assuming there is one.
  pub fn pop_frame(&mut self) {
    self.frames.pop();
  }

  /// Returns a reference to the most recent call frame.
  fn top(&mut self) -> &mut Frame {
    self.frames.last_mut().unwrap()
  }

  /// Returns a reference to a local value.
  pub fn read_local(&mut self, v: &ssa::Value) -> &hir::value::Value {
    self.top().locals.get(v).expect("local not found.")
  }

  /// Returns a reference to a value holded in memory.
  pub fn read_memory(&mut self, v: &u64) -> &hir::value::Value {
    self.memory.get(v).expect("memory address not found")
  }

  /// Returns a value stored in the locals. Consumes the value
  pub fn get_local(&mut self, v: &ssa::Value) -> hir::value::Value {
    match self.top().locals.get_mut(v) {
      Some(value) => std::mem::replace(value, hir::value::Value::uninit()),
      None => panic!("local not found.")
    }
  }

  /// Returns a value holded in memory. Consumes the value
  pub fn get_memory(&mut self, a: &u64) -> hir::value::Value {
    match self.memory.get_mut(a) {
      Some(value) => std::mem::replace(value, hir::value::Value::uninit()),
      None => panic!("memory address not found")
    }
  }

  /// Set the value of the memory at the adress `a`
  pub fn set_memory(&mut self, a: hir::value::Value, v: hir::value::Value) {
    let ma = a.as_primitive_ty::<MemoryAddress>().expect("Need a memory address").0;
    self.memory.insert(ma, v);
  }

  /// Sets the local at index `a` to `v` in the current `frame`
  pub fn set_local(&mut self, a: ssa::Value, v: hir::value::Value) -> Option<hir::value::Value> {
    self.top().locals.insert(a, v)
  }

  /// Set a local value with the current program counter as key
  pub fn set_local_at_current_position(&mut self, v: hir::value::Value) -> Option<hir::value::Value> {
    let k = ssa::Value::Register(self.get_pc().unwrap());
    self.top().locals.insert(k, v)
  }

  /// Returns the current program counter
  pub fn get_pc(&mut self) -> Option<ssa::InstructionIdentity> {
    self.top().pc
  }

  /// Reserve a new memory slot, and returns its index
  pub fn allocate(&mut self) -> u64 {
    self.current_memory_index += 1;
    self.current_memory_index
  }

  /// Returns a reference to the `hir::value::Value` that `v` refers to.
  /// `v` is expected to be either a `ssa::Value::Parameter` or a `ssa::Value::Register`
  pub fn resolve_hir_value(&mut self, v: &ssa::Value) -> &hir::value::Value {
    match v {
      ssa::Value::Register(_) => {
        self.read_local(v)
      },
      ssa::Value::Parameter(_) => {
        let v = self.read_local(v);
        let a = v.as_primitive_ty::<MemoryAddress>().unwrap().0;
        self.read_memory(&a)
      },
      _ => {
        // The cache is needed so that the value is stored somewhere while we give out the the reference
        // This is okay as self is a mutable borrow. So we can't call this method twice while having a ref to its result
        self.value_cache = self.to_hir_value(v);
        &self.value_cache
      }
    }
  }

  /// Convert a `ssa::Value` to a `hir::value::Value`, using `self` as context.
  pub fn to_hir_value(&mut self, v: &ssa::Value) -> hir::value::Value {
    match v {
      ssa::Value::Register(_) => {
        let p = self.read_local(v);
        match copy_primitive(p) {
          Some(d) => d,
          // Here, if we cannot copy the value -> non-trivial type
          // This means we need to move the value
          None => self.get_local(v)
        }
      },
      ssa::Value::Boolean(b) => {
        hir::value::Value::native(*b)
      },
      ssa::Value::Integer(i) => {
        hir::value::Value::native(i.to_isize())
      },
      ssa::Value::Parameter(_) => {
        let p = copy_primitive(self.read_local(v)).unwrap();
        let a = p.as_primitive_ty::<MemoryAddress>().unwrap().0;
        let rv = self.read_memory(&a);
        match copy_primitive(rv) {
          Some(r) => r,
          None => self.get_memory(&a)
        }
      },
      ssa::Value::Dictionary(d) => {
        let mut t: Vec<hir::value::Value> = vec![];
        for v in &d.values {
          t.push(self.to_hir_value(v));
        };
        hir::value::Value::tuple(t)
      },
      ssa::Value::Function(r) => {
        hir::value::Value::function(r.identity, r.module)
      },
      _ => {
        todo!("not implemented for v : {:?}", v)
      }
    }
  }

  /// Load all the arguments in memory and store the adresses in the `Frame` locals.
  pub fn load_arguments_in_memory(&mut self, arguments: Vec<hir::value::Value>) {
    for (i, a) in arguments.into_iter().enumerate() {
      let ad = self.allocate();
      let p = ssa::Value::Parameter(i);
      self.set_local(p, MemoryAddress::new(ad));
      self.set_memory(MemoryAddress::new(ad), a);
    }
  }


}
