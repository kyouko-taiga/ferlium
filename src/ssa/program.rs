use std::collections::HashMap;
use ustr::Ustr;

use crate::{module::{self, Module}, runtime, ssa::{self, value::FunctionReference}, std::STD_MODULE_ID};

/// A Ferlium program expressed in SSA form.
pub struct Program<'a> {

  /// The functions in the program.
  functions: HashMap<Ustr, ssa::Function>,

  /// The module corresponding to this program
  module: &'a Module
}

impl<'a> Program<'a> {

  /// Creates an empty program.
  pub fn new(module: &'a Module) -> Self {
    Program { functions: HashMap::new(), module: module }
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
  pub fn evaluate(&self, callee: FunctionReference, arguments: Vec<runtime::Value>) -> runtime::Value {
    self.evaluate_in_context(callee, arguments, &mut ssa::EvaluationContext::new(self))
  }

  /// Load all the argument in memory and store the adresses in the `Frame` locals
  fn load_arguments_in_memory(&self, arguments: Vec<runtime::Value>, context: &mut ssa::EvaluationContext){
    for (i, a) in arguments.iter().enumerate() {
      let ad = context.allocate();
      let p = ssa::Value::Parameter(i);
      context.set_local(p, runtime::Value::MemoryAdress(ad));
      context.set_memory(runtime::Value::MemoryAdress(ad), a.clone());
    }
  }

  /// Returns the result of applying `callee` to `arguments` in the given `context`.
  fn evaluate_in_context<'b>(
    &'a self, callee: FunctionReference, arguments: Vec<runtime::Value>, context: &mut ssa::EvaluationContext<'a>
  ) -> runtime::Value {

    match callee.reference {
      module::FunctionId::Local(_) => {
        let f = &self.functions[&callee.representation];
        let e = f.entry().unwrap();

        // Push a new call frame
        context.push_frame(f, e.instructions().next());

        // Load the arguments in memory, and put their respective memory adress in the parameter registers
        self.load_arguments_in_memory(arguments, context);

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
      },
      module::FunctionId::Import(i) => {
        let slot = self.module.get_import_fn_slot(i).unwrap();
        if slot.module == STD_MODULE_ID {
          // We are calling a function from STD
          match &slot.target {
            module::ImportFunctionTarget::NamedFunction(n) => {
              ssa::std::call_named_function(n, arguments)
            },
            module::ImportFunctionTarget::TraitImplMethod { key, index } => {
              // For now, this seems very hacky. I think we should try to find a nicer way to do this.
              let n = match key {
                module::TraitKey::Concrete(c) =>  {
                  &c.trait_ref
                },
                module::TraitKey::Blanket(b) => {
                  &b.trait_ref
                }
              }.functions[*index as usize].0;
              ssa::std::call_named_function(n.into(), arguments)
            }
          }
        } else {
          todo!("No implemented")
        }
      }
    }
  }

}
