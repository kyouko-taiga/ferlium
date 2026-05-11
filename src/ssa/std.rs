use crate::{runtime};


pub fn call_named_function(name: &str, arguments: Vec<runtime::Value>) -> runtime::Value {
  match name {
    "not" =>  {
      assert!(arguments.iter().count() == 1);
      let runtime::Value::Boolean(b) = arguments[0] else {
        panic!("Argument passed to `not` must be a boolean")
      };
      runtime::Value::Boolean(!b)
    },
    "add" => {
      assert!(arguments.iter().count() == 2);
      let runtime::Value::Integer(v1) = arguments[0].clone() else {
        panic!("First argument of `add` must be an integer")
      };
      let runtime::Value::Integer(v2) = arguments[1].clone() else {
        panic!("Second argument of `add` must be an integer")
      };
      runtime::Value::Integer(Box::new(runtime::value::Integer::from_u64(v1.bits + v2.bits)))
    },
   "mul" => {
     assert!(arguments.iter().count() == 2);
     let runtime::Value::Integer(v1) = arguments[0].clone() else {
       panic!("First argument of `add` must be an integer")
     };
     let runtime::Value::Integer(v2) = arguments[1].clone() else {
       panic!("Second argument of `add` must be an integer")
     };
     runtime::Value::Integer(Box::new(runtime::value::Integer::from_u64(v1.bits * v2.bits)))
    },
    "from_int" =>  {
      assert!(arguments.iter().count() == 1);
      let runtime::Value::Integer(v1) = arguments[0].clone() else {
        panic!("First argument of `add` must be an integer")
      };
      runtime::Value::Integer(Box::new(runtime::value::Integer::from_u64(v1.bits)))
    },
    "sub" => {
      assert!(arguments.iter().count() == 2);
      let runtime::Value::Integer(v1) = arguments[0].clone() else {
        panic!("First argument of `add` must be an integer")
      };
      let runtime::Value::Integer(v2) = arguments[1].clone() else {
        panic!("Second argument of `add` must be an integer")
      };
      runtime::Value::Integer(Box::new(runtime::value::Integer::from_u64(v1.bits - v2.bits)))
    },
    "le" => {
      assert!(arguments.iter().count() == 3);
      let runtime::Value::Integer(v1) = arguments[1].clone() else {
        panic!("First argument of `add` must be an integer")
      };
      let runtime::Value::Integer(v2) = arguments[2].clone() else {
        panic!("Second argument of `add` must be an integer")
      };
      runtime::Value::Boolean(v1.bits <= v2.bits)
    },
    _ => {
      todo!("No implemented : {}", name);
    }
  }
}
