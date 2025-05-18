use std::collections::HashSet;

use itertools::Itertools;

use crate::{
    deep_copy::{deep_copy, NameMapper},
    Circuit,
};

/// Takes a sequence of circuits that might share gates and turns them
/// into a single circuit but with the original circuits being fully independent
/// sub-circuits. This also includes renaming of all shared input and output names.
pub fn disjoint_union<'a>(circuits: impl Iterator<Item = &'a Circuit>) -> Circuit {
    let mut dispenser = NameDispenser::default();

    let circuits = circuits
        .map(|circuit| deep_copy(circuit, &mut dispenser).unwrap())
        .collect_vec();

    Circuit::from_named_outputs(
        circuits
            .iter()
            .flat_map(|circuit| circuit.named_outputs())
            .map(|(g, n)| (g.clone(), n)),
    )
    .with_input_order(circuits.iter().flat_map(|circuit| circuit.input_names()))
    .unwrap()
}

/// A name mapper that makes sure that all names it returns are
/// unique but tries to keep names as long as they do not clash.
#[derive(Default)]
struct NameDispenser {
    counter: u64,
    seen_names: HashSet<String>,
}

impl NameMapper for &mut NameDispenser {
    fn map_input_name(&mut self, input_name: &str) -> String {
        self.map_name(input_name)
    }

    fn map_output_name(&mut self, output_name: &str) -> String {
        if output_name.is_empty() {
            String::default()
        } else {
            self.map_name(output_name)
        }
    }
}

impl NameDispenser {
    /// Map a given name.
    /// The correct behavior of the function relies on the fact
    /// that it is only called once per name and circuit.
    fn map_name(&mut self, name: &str) -> String {
        let mut name = name.to_string();
        loop {
            if self.seen_names.insert(name.clone()) {
                return name;
            }
            self.counter += 1;
            name = format!("v_{}", self.counter);
        }
    }
}

#[cfg(test)]
mod test {
    use itertools::Itertools;

    use crate::Gate;

    use super::*;

    #[test]
    fn name_dispenser() {
        let names = ["a", "b", "v_3", "b", "b", "v_1", "c", "v_5", "a"];
        let mut dispenser = &mut NameDispenser::default();

        assert_eq!(
            &names.map(|n| dispenser.map_input_name(n)).join(" "),
            "a b v_3 v_1 v_2 v_4 c v_5 v_6"
        );
    }

    #[test]
    fn disjoint_union_test() {
        let or = Gate::from("v_1") | Gate::from("v_2");
        let xor = Gate::from("v_1") ^ Gate::from("v_3");
        let circuit = Circuit::from_named_outputs([(xor, "xor"), (or, "or")])
            .with_input_order(["v_2", "v_3", "v_1"])
            .unwrap();
        let circuit = disjoint_union([&circuit, &circuit].into_iter());
        assert_eq!(
            circuit.output_names().iter().join(", "),
            "xor, or, v_4, v_5"
        );
        assert_eq!(
            circuit.input_names().join(", "),
            "v_2, v_3, v_1, v_8, v_7, v_6"
        );
        assert_eq!(
            circuit
                .outputs()
                .iter()
                .map(|g| g.to_string_as_tree())
                .join("\n"),
            "(v_1 ^ v_3)\n(v_1 | v_2)\n(v_6 ^ v_7)\n(v_6 | v_8)"
        );
    }
}
