use std::collections::HashSet;

use crate::{
    gate::{GraphIterator, PostVisitIterator},
    Gate,
};

/// A boolean circuit with named inputs and outputs.
/// Input variables are identified by their name.
/// The gates in the circuit are [`Gate`]s.
#[derive(Default)]
pub struct Circuit {
    /// The output gates of the circuit. They contain their predecessors.
    outputs: Vec<Gate>,
    /// The names of the output gates. Unnamed outputs use the empty string.
    output_names: Vec<String>,
}

impl From<Gate> for Circuit {
    fn from(gate: Gate) -> Self {
        Circuit {
            outputs: vec![gate],
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
}
