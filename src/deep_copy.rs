use std::{collections::HashMap, rc::Rc};

/// Creates a deep copy of the given circuit, assigning new names to all input
/// and output gates except those in `gate_names_to_keep`.
/// Note that if input gates are not renamed, they will refer to the same
/// inputs as the original gate in a combined circuit.
///
/// Returns the new circuit and the variable substitution map.
pub fn deep_copy<'a>(
    circuit: &'a Circuit,
    gate_names_to_keep: &'a [String],
    // TODO If we want to create multiple copies, we probably also need a way to
    // block existing names.
) -> (Circuit, HashMap<&'a str, Rc<String>>) {
    let mut deep_copy = DeepCopy::new(circuit, gate_names_to_keep);
    let output_gates = circuit
        .outputs()
        .iter()
        .map(|o| deep_copy.copy(o))
        .collect();
    let substitution_map = deep_copy.input_name_substitutions();
    (
        Circuit::from_unnamed_outputs(output_gates),
        substitution_map,
    )
}

struct DeepCopy<'a> {
    input_name_substitutions: HashMap<&'a str, Gate>,
    input_name_dispenser: NameDispenser,
    gate_substitutions: HashMap<usize, Gate>,
}

impl<'a> DeepCopy<'a> {
    fn new(node: &'a Gate, input_gate_names_to_keep: &'a [String]) -> Self {
        Self {
            input_name_substitutions: input_gate_names_to_keep
                .iter()
                .map(|name| (name.as_str(), Gate::from(name.clone())))
                .collect(),
            input_name_dispenser: NameDispenser::new(node),
            gate_substitutions: HashMap::new(),
        }
    }

    fn copy(&mut self, gate: &'a Gate) -> Gate {
        for n in gate.post_visit_iter() {
            let substitution = match n.operation() {
                Operation::Variable(name) => {
                    if let Some(new_node) = self.input_name_substitutions.get(name.as_str()) {
                        new_node.clone()
                    } else {
                        let new_node = Gate::from(self.input_name_dispenser.next());
                        self.input_name_substitutions
                            .insert(name.as_str(), new_node.clone());
                        new_node
                    }
                }
                Operation::Constant(value) => Gate::from(*value),
                Operation::Negation(inner) => !self.sub(inner),
                Operation::Conjunction(left, right) => self.sub(left) & self.sub(right),
                Operation::Disjunction(left, right) => self.sub(left) | self.sub(right),
                Operation::Xor(left, right) => self.sub(left) ^ self.sub(right),
            };
            self.gate_substitutions.insert(n.id(), substitution);
        }
        self.sub(gate)
    }

    fn input_name_substitutions(self) -> HashMap<&'a str, Rc<String>> {
        self.input_name_substitutions
            .into_iter()
            .map(|(k, v)| {
                let Operation::Variable(name) = v.operation() else {
                    unreachable!()
                };
                (k, Rc::clone(name))
            })
            .collect()
    }

    fn sub(&self, node: &'a Gate) -> Gate {
        self.gate_substitutions.get(&node.id()).unwrap().clone()
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn simple() {
        let circuit = Gate::from("v1");
        let copied_circuit = deep_copy(&circuit, &[]).0;
        assert_eq!(copied_circuit.to_string_as_tree(), "v2");
    }

    #[test]
    fn intermediate1() {
        let circuit = (Gate::from("v1") & Gate::from("v2")) | !Gate::from("v1");
        let (copied_circuit, var_substitution) = deep_copy(&circuit, &[]);
        assert_eq!(var_substitution.len(), 2);
        assert_eq!(var_substitution["v1"].as_str(), "v3");
        assert_eq!(var_substitution["v2"].as_str(), "v4");
        assert_eq!(copied_circuit.to_string_as_tree(), "((v3 & v4) | !v3)");
    }

    #[test]
    fn intermediate2() {
        let circuit = (Gate::from("v3") ^ Gate::from("v3")) & Gate::from(true) | Gate::from(false);
        let copied_circuit = deep_copy(&circuit, &[]).0;
        assert_eq!(
            copied_circuit.to_string_as_tree(),
            "(((v4 ^ v4) & true) | false)"
        );
    }

    #[test]
    fn with_exceptions() {
        let circuit = Gate::from("v1") & Gate::from("v2");
        let variable_exceptions = vec!["v1".to_string()];
        let (copied_circuit, var_substitution) = deep_copy(&circuit, &variable_exceptions);
        assert_eq!(var_substitution.len(), 2);
        assert_eq!(var_substitution["v1"].as_str(), "v1");
        assert_eq!(var_substitution["v2"].as_str(), "v3");
        assert_eq!(copied_circuit.to_string_as_tree(), "(v1 & v3)");
    }
}
use std::collections::HashSet;

use boolean_circuit::{Gate, Operation};

use crate::{Circuit, Gate};

/// Returns a hash set of all variables in the circuit.
pub fn variables_in_circuit(node: &Gate) -> HashSet<&str> {
    node.iter()
        .filter_map(|n| match n.operation() {
            Operation::Variable(name) => Some(name.as_str()),
            _ => None,
        })
        .collect()
}

/// Returns a number `u` such that for any `i` >= `u`, there is no
/// variable called `v{i}` in the circuit.
pub fn next_free_variable(node: &Gate) -> u64 {
    variables_in_circuit(node)
        .iter()
        .filter_map(|v| v.strip_prefix('v'))
        .filter_map(|v| v.parse::<u64>().ok())
        .max()
        .unwrap_or(0)
        + 1
}

pub struct NameDispenser {
    next_variable: u64,
}

impl NameDispenser {
    /// Creates a variable dispenser such that each call to `next` returns a
    /// variable name that does not occur in `existing_circuit`.
    pub fn new<'a>(existing_circuit: impl Iterator<Item = &'a Gate>) -> Self {
        Self {
            next_variable: next_free_variable(existing_circuit),
        }
    }

    /// Returns a new unique variable name.
    pub fn next(&mut self) -> String {
        let var = format!("v{}", self.next_variable);
        self.next_variable += 1;
        var
    }
}
