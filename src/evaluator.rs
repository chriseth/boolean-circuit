use std::collections::HashMap;

use crate::{Circuit, Gate, Operation};

/// Returns the value computed in `gate` given assignments to all required variables.
pub fn evaluate_gate(gate: &Gate, assignments: &HashMap<String, bool>) -> bool {
    Evaluator {
        cache: HashMap::new(),
        assignments,
    }
    .evaluate(gate)
}

/// Returns the values computed in the circuit's output gates given assignments to all required variables.
pub fn evaluate(circuit: &Circuit, assignments: &HashMap<String, bool>) -> Vec<bool> {
    let mut evaluator = Evaluator {
        cache: HashMap::new(),
        assignments,
    };
    circuit
        .outputs()
        .iter()
        .map(|gate| evaluator.evaluate(gate))
        .collect()
}

struct Evaluator<'a> {
    cache: HashMap<usize, bool>,
    assignments: &'a HashMap<String, bool>,
}

impl Evaluator<'_> {
    fn evaluate(&mut self, gate: &Gate) -> bool {
        if let Some(&result) = self.cache.get(&gate.id()) {
            return result;
        }
        let result = match gate.operation() {
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
        self.cache.insert(gate.id(), result);
        result
    }
}
