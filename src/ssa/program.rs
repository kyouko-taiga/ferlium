use std::collections::HashMap;
use ustr::Ustr;

use crate::{
    eval::{self, Place, ValOrMut}, hir::{self, value::FunctionHiddenArgValue}, ssa::{self, interpreter::{self, FunctionKey}}, std::STD_MODULE_ID
};



/// A Ferlium program expressed in SSA form.
pub struct Program {

  /// The functions in the program.
  functions: HashMap<interpreter::FunctionKey, ssa::Function>,

}

impl Program {

  /// Creates an empty program.
  pub fn new() -> Self {
    Program { functions: HashMap::new()}
  }

  /// Returns a reference to the function having the given `index`, if any.
  pub fn function(&self, index: &interpreter::FunctionKey) -> Option<&ssa::Function> {
    self.functions.get(index)
  }

  /// Adds the declaration of a function having the given `key` iff such a function has not been
  /// declared in `self` yet.
  pub fn declare(&mut self, key: interpreter::FunctionKey, repr: Ustr) -> &mut ssa::Function {
    self.functions.entry(key).or_insert(ssa::Function::new(repr))
  }

  /// Adds the definition of `f` this this program.
  ///
  /// `f` is declared if it was not already. Otherwise, the definition of the existing function is
  /// set to that of `f`.
  pub fn set_definition(&mut self, key: interpreter::FunctionKey, f: ssa::Function) -> &ssa::Function {
    let g = self.declare(key, f.name);
    *g = f;
    g
  }

  /// Evaluate a lowered function given the `arguments`, `extra_arguments` and `context`, and returns the evaluation result.
  fn evaluate_lowered_function(&self, callee: FunctionKey, arguments: Vec<hir::value::Value>, extra_arguments: Vec<FunctionHiddenArgValue>, context: &mut ssa::EvaluationContext) -> hir::value::Value {
    let entry = self.functions[&callee].entry().unwrap();
    context.push_frame(callee, entry.instructions().next());
    context.load_arguments_in_memory(arguments);
    loop {
        match context.step(self) {
            ssa::Step::Advance => context.advance(self),
            ssa::Step::Goto(b) => context.goto(b, self),
            ssa::Step::Return(v) => {
                context.pop_frame();
                return v;
            }
        }
    }
  }

  /// Evaluates a Standard Library function with the given `arguments`, `extra_arguments` and `context`, and returns the evaluation result.
  fn evaluate_std_function(&self, callee: FunctionKey, arguments: Vec<hir::value::Value>, extra_arguments: Vec<FunctionHiddenArgValue>, context: &mut ssa::EvaluationContext) -> hir::value::Value {
    let module = context.hir_context.compiler_session().expect_fresh_module(callee.module);
    let function_data = module.get_function_by_id(callee.identity).unwrap();
    let arg_tys = &function_data.definition.ty_scheme.ty.args;

    let mut vs: Vec<ValOrMut> = Vec::with_capacity(arguments.len());
    let mut indexes = Vec::new();
    for (i, a) in arguments.into_iter().enumerate() {
      if i < arg_tys.len() && arg_tys[i].mut_ty.is_mutable() {
        let val = ValOrMut::Val(a);
        let idx = context.hir_context.environment.len();
        context.hir_context.environment.push(val);
        vs.push(ValOrMut::Mut(Place { target: idx, path: vec![] }));
        indexes.push(idx);
      } else {
        vs.push(ValOrMut::Val(a));
      }
    }

    let res = context.hir_context.call_function(callee.identity, callee.module, extra_arguments, vs);
    let v = match res {
        Ok(eval::ControlFlow::Return(v)) | Ok(eval::ControlFlow::Continue(v)) => v,
        _ => panic!("function call returned no result")
    };
    context.hir_context.environment.truncate(context.hir_context.environment.len() - indexes.len());
    v
  }

  /// Evaluates the function identified by `callee` with the given `arguments`, `extra_arguments` and `context`, and returns the evaluation result.
  pub fn evaluate(&self, callee: FunctionKey, arguments: Vec<hir::value::Value>, extra_arguments:Vec<FunctionHiddenArgValue>, context: &mut ssa::EvaluationContext) -> hir::value::Value {
    if callee.module == context.hir_context.module_id {
      self.evaluate_lowered_function(callee, arguments, extra_arguments, context)
    } else if callee.module == STD_MODULE_ID {
      self.evaluate_std_function(callee, arguments, extra_arguments, context)
    } else {
      let prev_module_id = context.hir_context.module_id;
      context.hir_context.module_id = callee.module;
      let r = self.evaluate_lowered_function(callee, arguments, extra_arguments, context);
      context.hir_context.module_id = prev_module_id;
      return r;
    }
  }

}
