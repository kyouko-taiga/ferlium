pub mod function;
pub mod instruction;
pub mod interpreter;
pub mod program;
pub mod value;

pub use function::{BlockIdentity, Function};
pub use instruction::{Instruction, InstructionIdentity, InstructionResult};
pub use interpreter::{EvaluationContext, Step};
pub use program::Program;
pub use value::Value;
