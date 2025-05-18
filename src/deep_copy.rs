use std::collections::HashMap;

use itertools::Itertools;

use crate::{Circuit, Gate, Operation};

/// A trait used to return names for input and output gates
/// when creating copies of circuits.
pub trait NameMapper {
    /// Given an input name in the original circuit, returns
    /// the name in the copy.
    fn map_input_name(&mut self, input_name: &str) -> String;
    /// Given an output name in the original circuit, returns
    /// the name in the copy.
    ///
    /// For both the argument and the return value, the empty string
    /// counts as "unnamed output".
    fn map_output_name(&mut self, output_name: &str) -> String;
}

/// Creates a deep / independent copy of the given circuit.
/// The `name_mapper` is responsible for returning new names for the inputs and outputs.
/// If the `name_mapper` returns existing names for inputs, these gates will still be shared,
/// since input nodes are identified by their names.
///
/// The name mapper will only be called once for each input or output name.
///
/// Returns the new circuit.
pub fn deep_copy(circuit: &Circuit, mut name_mapper: impl NameMapper) -> Result<Circuit, String> {
    let output_names = circuit
        .output_names()
        .iter()
        .map(|n| name_mapper.map_output_name(n))
        .collect_vec();
    let mut deep_copy = DeepCopy::new(name_mapper);
    let output_gates = circuit
        .outputs()
        .iter()
        .map(|o| deep_copy.copy(o))
        .collect_vec();
    let input_names = circuit
        .input_names()
        .map(|n| deep_copy.copy_of_input(n).to_string_as_tree())
        .unique()
        .collect_vec();

    Circuit::from_named_outputs(output_gates.into_iter().zip(output_names))
        .with_input_order(input_names)
}

pub fn deep_copy_of_gate(gate: &Gate, name_mapper: impl NameMapper) -> Gate {
    DeepCopy::new(name_mapper).copy(gate)
}

struct DeepCopy<'a, N> {
    name_mapper: N,
    input_name_substitutions: HashMap<&'a str, Gate>,
    gate_substitutions: HashMap<usize, Gate>,
}

impl<'a, N: NameMapper> DeepCopy<'a, N> {
    fn new(name_mapper: N) -> Self {
        Self {
            name_mapper,
            input_name_substitutions: Default::default(),
            gate_substitutions: HashMap::new(),
        }
    }

    fn copy(&mut self, gate: &'a Gate) -> Gate {
        for n in gate.post_visit_iter() {
            let substitution = match n.operation() {
                Operation::Variable(name) => self.copy_of_input(name.as_str()),
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

    fn copy_of_input(&mut self, name: &'a str) -> Gate {
        self.input_name_substitutions
            .entry(name)
            .or_insert_with(|| Gate::from(self.name_mapper.map_input_name(name)))
            .clone()
    }

    fn sub(&self, node: &'a Gate) -> Gate {
        self.gate_substitutions.get(&node.id()).unwrap().clone()
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[derive(Default)]
    struct CountedNames {
        counter: usize,
    }

    impl NameMapper for CountedNames {
        fn map_input_name(&mut self, _: &str) -> String {
            self.counter += 1;
            format!("copy_{}", self.counter)
        }

        fn map_output_name(&mut self, _: &str) -> String {
            self.counter += 1;
            format!("copy_{}", self.counter)
        }
    }

    #[test]
    fn simple() {
        let copied_circuit = deep_copy_of_gate(&Gate::from("v1"), CountedNames::default());
        assert_eq!(copied_circuit.to_string_as_tree(), "copy_1");
    }

    #[test]
    fn intermediate1() {
        let gate = (Gate::from("v1") & Gate::from("v2")) | !Gate::from("v1");
        let copied_circuit = deep_copy_of_gate(&gate, CountedNames::default());
        assert_eq!(
            copied_circuit.to_string_as_tree(),
            "((copy_1 & copy_2) | !copy_1)"
        );
    }

    #[test]
    fn intermediate2() {
        let gate = (Gate::from("v3") ^ Gate::from("v3")) & Gate::from(true) | Gate::from(false);
        let copied_circuit = deep_copy_of_gate(&gate, CountedNames::default());
        assert_eq!(
            copied_circuit.to_string_as_tree(),
            "(((copy_1 ^ copy_1) & true) | false)"
        );
    }

    impl NameMapper for HashMap<&str, String> {
        fn map_input_name(&mut self, n: &str) -> String {
            self[n].clone()
        }
        fn map_output_name(&mut self, n: &str) -> String {
            self[n].clone()
        }
    }

    #[test]
    fn with_input_repetitions() {
        let substitutions = HashMap::from([("v1", "x".to_string()), ("v2", "x".to_string())]);
        let circuit = Gate::from("v1") & Gate::from("v2");
        let copied_circuit = deep_copy_of_gate(&circuit, substitutions);
        assert_eq!(copied_circuit.to_string_as_tree(), "(x & x)");
    }

    #[test]
    fn circuit_copy() {
        let out_b = Gate::from("v1") | Gate::from("v2");
        let out_a = Gate::from("v1") ^ Gate::from("v3");
        let circuit = Circuit::from_named_outputs([(out_a, "a"), (out_b, "b")])
            .with_input_order(["v2", "v3", "v1"])
            .unwrap();
        let substitutions = HashMap::from([
            ("v1", "r1".to_string()),
            ("v2", "r2".to_string()),
            ("v3", "r3".to_string()),
            ("a", "x".to_string()),
            ("b", "y".to_string()),
        ]);
        let copy = deep_copy(&circuit, substitutions).unwrap();
        assert_eq!(copy.input_names().collect_vec(), vec!["r2", "r3", "r1"]);
        assert_eq!(copy.output_names(), vec!["x".to_string(), "y".to_string()]);
    }

    #[test]
    fn input_order_with_repetitions() {
        let out_b = Gate::from("v1") | Gate::from("v2");
        let out_a = Gate::from("v1") ^ Gate::from("v3");
        let circuit = Circuit::from_named_outputs([(out_a, "a"), (out_b, "b")])
            .with_input_order(["v2", "v3", "v1"])
            .unwrap();
        let substitutions = HashMap::from([
            ("v1", "r2".to_string()),
            ("v2", "r2".to_string()),
            ("v3", "r1".to_string()),
            ("a", "x".to_string()),
            ("b", "y".to_string()),
        ]);
        let copy = deep_copy(&circuit, substitutions).unwrap();
        assert_eq!(copy.input_names().collect_vec(), vec!["r2", "r1"]);
        assert_eq!(copy.output_names(), vec!["x".to_string(), "y".to_string()]);
    }
}
