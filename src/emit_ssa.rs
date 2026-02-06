use crate::{
  Location,
  containers,
  format::FormatWith,
  ir,
  module::{
    FunctionId, LocalFunctionId, ModuleEnv, ModuleRc, Modules
  },
  ssa,
  value
};

/// Emit the low-level (aka SSA) ferlium IR of `module`.
pub fn emit_ssa(
  module: &ModuleRc,
  others: &Modules
) {
  for n in module.owned_functions() {
    for i in &module.function_name_to_id[n] {
      Emitter::emit_ssa_fn(*i, module, others);
    }
  }

    //  Ref::map(f.function.code.as_ref().borrow(), |code| 1);

    // let x = match f.function.code.as_ref().borrow().downcast_ref::<ScriptFunction>() {
    //     Some(s) => s,
    //     None => None,
    // };
    // // let x: u32 = f;
}

/// A constructor of SSA IR.
struct Emitter<'a> {

  /// The module being lowered.
  module: &'a ModuleRc,

  /// The other modules.
  others: &'a Modules,

  /// The context in which the emitter inserts new IR.
  context: InsertionContext,

}

impl<'a> Emitter<'a> {

  /// Generates the IR of `source`, which has the given `identity`.
  fn emit_ssa_fn(identity: LocalFunctionId, module: &'a ModuleRc, others: &'a Modules) {
    let f = module.get_own_function_by_id(identity).unwrap();
    match f.code.as_ref().borrow().as_script() {
      Some(source) => {
        // Create the function.
        // TODO: Use better identities.
        let e = ModuleEnv::new(module, others, false);
        let s = format!("{}", FunctionId::Local(identity).format_with(&e));
        let mut lowered = ssa::Function::new(s.into());

        // Create the function's entry.
        let entry = lowered.add_block().id();

        // Instantiate an emitter to generate the function's contents.
        let mut emitter = Self {
          module,
          others,
          context: InsertionContext {
            function: lowered,
            point: InsertionPoint::End(entry),
            span: source.code.span,
          }
        };

        // The body of the function evaluates to the return value.
        let v = emitter.lower_as_rvalue(&source.code);
        emitter.context.function.block_mut(entry).append(
          ssa::Instruction::ret(emitter.context.span, v));

        println!("{}", emitter.context.function);
      },

      None => panic!(),
    }
  }

  /// Returns a reference to the function identified by `f`.
  fn demand_function(&mut self, f: FunctionId) -> ssa::Value {
    let e = ModuleEnv::new(self.module, self.others, false);
    let s = format!("{}", f.format_with(&e));
    ssa::Value::Function(s.into())
  }

  /// Generates the IR for `node`, which occurs as a statement.
  fn lower_as_statement(&mut self, node: &ir::Node) {
    // use ir::NodeKind as K;
    match &node.kind {
      _ => {
        // QUESTION: Should we explicitly drop values?
        self.lower_as_rvalue(node);
      },
    }
  }

  /// Generates the IR for `node`, which occurs as rvalue.
  fn lower_as_rvalue(&mut self, node: &ir::Node) -> ssa::Value {
    use ir::NodeKind as K;
    match &node.kind {
      K::Block(n) => {
        let (last, prefix) = n.split_last().unwrap();
        prefix.iter().for_each(|s| self.lower_as_statement(s));
        self.lower_as_rvalue(last)
      },

      K::Immediate(n) => {
        if let Some(result) = self.lower_as_primitive(&n.value) {
          result
        } else {
          let s = self.show(node.ty);
          println!("lowering is unimplemented for node of kind '{:?}' of type {:?}", n.value, s);
          panic!()
        }
      },

      K::StaticApply(n) => {
        let f = self.demand_function(n.function);
        let mut a: Vec<ssa::Value> = vec![];
        for x in &n.arguments {
          a.push(self.lower_as_rvalue(x));
        }

        assert!(node.ty == n.ty.ret);
        self.insert(ssa::Instruction::call(node.span, f, a, n.ty.ret)).unwrap()
      },

      _ => {
        println!("lowering is unimplemented for node of kind '{:?}'", node.kind);
        todo!()
      },
    }
  }

  /// Returns the lowered representation of the given native value.
  fn lower_as_primitive(&mut self, native: &value::Value) -> Option<ssa::Value> {
    use ssa::value::Integer as Int;

    if native.as_primitive_ty::<()>() != None {
      Some(ssa::Value::Unit)
    } else if let Some(n) = native.as_primitive_ty::<isize>() {
      Some(ssa::Value::Integer(containers::b(Int::from_isize(*n))))
    } else if let Some(n) = native.as_primitive_ty::<u32>() {
      Some(ssa::Value::Integer(containers::b(Int::from_u32(*n))))
    } else if let Some(n) = native.as_primitive_ty::<i32>() {
      Some(ssa::Value::Integer(containers::b(Int::from_i32(*n))))
    } else {
      None
    }
  }

  // /// Returns the result of `action` on `self` with the insertion context attached to `span`.
  // fn at<T>(&mut self, mut span: Location, action: impl FnOnce(&mut Self) -> T) -> T {
  //   mem::swap(&mut self.context.span, &mut span);
  //   let result = action(self);
  //   mem::swap(&mut self.context.span, &mut span);
  //   result
  // }

  /// Inserts `s` at the current insertion point and returns the result the register assigned by
  /// that instruction, if any.
  fn insert(&mut self, s: ssa::Instruction) -> Option<ssa::Value> {
    let i = match &self.context.point {
      InsertionPoint::End(b) => self.context.function.block_mut(*b).append(s),
    };
    self.context.function.definition(i)
  }

  /// Returns a textual representation of `x`.
  fn show<T: FormatWith::<ModuleEnv<'a>>>(&self, x: T) -> String {
    let e = ModuleEnv::new(self.module, self.others, false);
    format!("{}", x.format_with(&e))
  }

}

/// The context in which instructions are inserted.
struct InsertionContext {

  /// The function in which new instructions are inserted.
  function: ssa::Function,

  /// Where new instructions are inserted in `function`.
  point: InsertionPoint,

  /// The region in the source code to which inserted instructions are associated.
  span: Location,

}

/// Where an instruction should be inserted in a basic block.
enum InsertionPoint {

  /// The end of a basic block.
  End(ssa::BlockIdentity)

}
