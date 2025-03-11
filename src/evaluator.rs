use std::collections::HashMap;

use crate::{Node, Operation};

/// Returns the value computed in `node` given assignments to all required variables.
pub fn evaluate(node: &Node, assignments: &HashMap<String, bool>) -> bool {
    Evaluator {
        cache: HashMap::new(),
        assignments,
    }
    .evaluate(node)
}

struct Evaluator<'a> {
    cache: HashMap<usize, bool>,
    assignments: &'a HashMap<String, bool>,
}

impl<'a> Evaluator<'a> {
    fn evaluate(&mut self, node: &Node) -> bool {
        if let Some(&result) = self.cache.get(&node.id()) {
            return result;
        }
        let result = match node.operation() {
            Operation::Variable(name) => {
                *self.assignments.get(name.as_str()).unwrap_or_else(|| {
                    panic!("No assignment for variable '{name}'");
                })
            }
            Operation::Constant(value) => *value,
            Operation::Negation(inner) => !self.evaluate(inner),
            Operation::Conjunction(left, right) => self.evaluate(left) && self.evaluate(right),
            Operation::Disjunction(left, right) => self.evaluate(left) || self.evaluate(right),
            Operation::Xor(left, right) => self.evaluate(left) ^ self.evaluate(right),
        };
        self.cache.insert(node.id(), result);
        result
    }
}
