use std::collections::HashSet;

use itertools::Itertools;

use crate::{
    gate::{GraphIterator, PostVisitIterator},
    Gate, Operation,
};

/// A boolean circuit with named inputs and outputs.
/// Input variables are identified by their name.
/// The gates in the circuit are [`Gate`]s.
#[derive(Default)]
pub struct Circuit {
    /// The output gates of the circuit. They contain their predecessors.
    outputs: Vec<Gate>,
    /// The names of the (non-constant) input gates, specifying their order.
    /// If `None`, the input gates are in no particular order and identified
    /// by their name only. If `Some(_)`, the list of names need to match
    /// the names of the input gates.
    input_names: Option<Vec<String>>,
    /// The names of the output gates. Unnamed outputs use the empty string.
    output_names: Vec<String>,
}

impl From<Gate> for Circuit {
    fn from(gate: Gate) -> Self {
        Circuit {
            outputs: vec![gate],
            input_names: None,
            output_names: vec![String::new()],
        }
    }
}

impl Circuit {
    /// Creates a circuit from unnamed outputs. Note that the [`Gate`]s can
    /// share predecessors. Any two input gates in the circuit with the same
    /// name are considered identical.
    pub fn from_unnamed_outputs(outputs: impl IntoIterator<Item = Gate>) -> Self {
        Self::from_named_outputs(outputs.into_iter().map(|n| (n, String::new())))
    }

    /// Adds the order of input gates to the circuit, or changes it.
    pub fn with_input_order(self, input_names: Vec<String>) -> Result<Self, String> {
        let inputs_in_circuit = self.input_names_from_traversal().collect::<HashSet<_>>();
        let input_names_set = input_names
            .iter()
            .map(|n| n.as_str())
            .collect::<HashSet<_>>();
        if input_names_set.len() != input_names.len() {
            return Err("Duplicate input names in list.".to_string());
        }
        if inputs_in_circuit != input_names_set {
            return Err(format!(
                "Input names do not match circuit inputs:\n{}\n  !=\n{}",
                input_names.iter().sorted().format(", "),
                inputs_in_circuit.iter().sorted().format(", ")
            ));
        }

        Ok(Circuit {
            input_names: Some(input_names),
            ..self
        })
    }

    /// Creates a circuit from (uniquely) named outputs.  Note that the [`Gate`]s can
    /// share predecessors. Any two input gates in the circuit with the same
    /// name are considered identical.
    ///
    /// The empty string can be used to not name outputs.
    ///
    /// Panics if the output names are not unique.
    pub fn from_named_outputs(items: impl IntoIterator<Item = (Gate, String)>) -> Self {
        let mut seen_names: HashSet<_> = Default::default();
        let mut circuit = Self::default();
        for (gate, name) in items {
            if !name.is_empty() && !seen_names.insert(name.clone()) {
                panic!("Duplicate output name {name}");
            }
            circuit.outputs.push(gate);
            circuit.output_names.push(name);
        }
        circuit
    }

    /// Returns the names of the input gates either in the order given by [`with_input_order`] or
    /// otherwise from a circuit traversal.
    pub fn input_names(&self) -> impl Iterator<Item = &str> + '_ {
        if let Some(names) = &self.input_names {
            Box::new(names.iter().map(|n| n.as_str())) as Box<dyn Iterator<Item = &str>>
        } else {
            Box::new(self.input_names_from_traversal())
        }
    }

    /// Returns the output gates.
    pub fn outputs(&self) -> &[Gate] {
        &self.outputs
    }

    /// Returns the names of the output gates, where unnamed output gates use the empty String.
    pub fn output_names(&self) -> &[String] {
        &self.output_names
    }

    /// Creates an iterator over the graph (the output gates and all their predecessors)
    /// that returns each gate exactly once.
    pub fn iter(&self) -> impl Iterator<Item = &Gate> {
        GraphIterator::new(&self.outputs)
    }

    /// Creates an iterator over the graph (the output gates and all their predecessors)
    /// with post-visit order, visiting each gate exactly once.
    /// This means that the predecessors of each gate are always visited before the gate itself.
    pub fn post_visit_iter(&self) -> impl Iterator<Item = &Gate> {
        PostVisitIterator::new(self.outputs.iter())
    }

    /// Returns the names of the input gates from a traversal of the circuit,
    /// not as potentially given by [`with_input_order`].
    fn input_names_from_traversal(&self) -> impl Iterator<Item = &str> {
        self.iter()
            .filter_map(|gate| match gate.operation() {
                Operation::Variable(name) => Some(name.as_str()),
                _ => None,
            })
            .unique()
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn input_order() {
        let c = Circuit::from(Gate::from("a") & Gate::from("b"));
        assert_eq!(c.input_names().collect::<Vec<_>>(), vec!["a", "b"]);
        let c = c
            .with_input_order(vec!["b".to_string(), "a".to_string()])
            .unwrap();
        assert_eq!(
            c.input_names().collect::<Vec<_>>(),
            vec!["b".to_string(), "a".to_string()]
        );
    }
}
