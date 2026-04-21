use std::collections::HashMap;
use ustr::Ustr;

use crate::{ssa};

/// A Ferlium program expressed in SSA form.
pub struct Program {

  /// The functions in the program.
  functions: HashMap<Ustr, ssa::Function>,

}

impl Program {

  /// Creates an empty program.
  pub fn new() -> Self {
    Program { functions: HashMap::new() }
  }

  /// Returns a reference to the function having the given `name`, if any.
  pub fn function(&self, name: Ustr) -> Option<&ssa::Function> {
    self.functions.get(&name)
  }

  /// Adds the declaration of a function having the given `name` iff such a function has not been
  /// declared in `self` yet.
  pub fn declare(&mut self, name: Ustr) -> &mut ssa::Function {
    self.functions.entry(name).or_insert(ssa::Function::new(name))
  }

  /// Adds the definition of `f` this this program.
  ///
  /// `f` is declared if it was not already. Otherwise, the definition of the existing function is
  /// set to that of `f`.
  pub fn set_definition(&mut self, f: ssa::Function) -> &ssa::Function {
    let g = self.declare(f.name);
    *g = f;
    g
  }

  /// Returns the result of applying `callee` to `arguments`.
  pub fn evaluate(&self, callee: Ustr, arguments: Vec<ssa::Value>) -> ssa::Value {
    self.evaluate_in_context(callee, arguments, &mut ssa::EvaluationContext::new(self))
  }

  /// Returns the result of applying `callee` to `arguments` in the given `context`.
  fn evaluate_in_context<'a>(
    &'a self, callee: Ustr, arguments: Vec<ssa::Value>, context: &mut ssa::EvaluationContext<'a>
  ) -> ssa::Value {
    // Push a new call frame.
    let f = &self.functions[&callee];
    let e = f.entry().unwrap();
    context.push_frame(f, e.instructions().next());

    // Evaluate the contents of the function.
    loop {
      match context.step() {
        ssa::Step::Advance => context.advance(),
        ssa::Step::Goto(i) => context.goto(i),
        ssa::Step::Return(v) => {
          context.pop_frame();
          return v
        }
      }
    }
  }

}
