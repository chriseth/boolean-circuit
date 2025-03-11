use std::{collections::HashMap, iter, rc::Rc};

use crate::{Literal, Node, Operation};

/// Turns the circuit represented by the ouput node `node` into a conjunctive normal form (CNF) formula.
///
/// The function uses the Tseitin transformation, so it needs a way to generate new unique variables,
/// which is done by the function `new_var`.
///
/// Parameters
/// * `node`: The output gate of the circuit.
/// * `new_var`: A function that can be used to generate new unique variable names. Each call has to return
///              a new variable name not returned before and not used in the circuit.
///
/// Returns an iterator over the clauses of the CNF formula. Each clause is a vector of literals.
pub fn generate_cnf<'a>(
    node: &'a Node,
    new_var: &mut impl FnMut() -> String,
) -> impl Iterator<Item = Vec<Literal>> + 'a {
    // We start by generating a variable / literal for each node.
    let lit_for_node_id: HashMap<_, _> = node
        .iter()
        .map(|n| {
            let var = match n.operation() {
                Operation::Variable(name) => Literal::Pos(name.clone()),
                _ => Literal::Pos(Rc::new(new_var())),
            };
            (n.id(), var)
        })
        .collect();
    let lit_for_node = move |node: &Node| lit_for_node_id[&node.id()].clone();
    let output_var = lit_for_node(node);
    // Now we iterate over the nodes and generate the required clauses for each node.
    node.into_iter()
        .flat_map(move |n| {
            let var = lit_for_node(n);
            match n.operation() {
                Operation::Variable(_) => vec![],
                Operation::Constant(true) => vec![vec![var]],
                Operation::Constant(false) => vec![vec![!&var]],
                Operation::Conjunction(left, right) => {
                    let left_var = lit_for_node(left);
                    let right_var = lit_for_node(right);
                    vec![
                        vec![!&left_var, !&right_var, var.clone()],
                        vec![left_var.clone(), !&var],
                        vec![right_var.clone(), !&var],
                    ]
                }
                Operation::Disjunction(left, right) => {
                    let left_var = lit_for_node(left);
                    let right_var = lit_for_node(right);
                    vec![
                        vec![left_var.clone(), right_var.clone(), !&var],
                        vec![!&left_var, var.clone()],
                        vec![!&right_var, var.clone()],
                    ]
                }
                Operation::Xor(left, right) => {
                    let left_var = lit_for_node(left);
                    let right_var = lit_for_node(right);
                    vec![
                        vec![left_var.clone(), right_var.clone(), !&var],
                        vec![left_var.clone(), !&right_var, var.clone()],
                        vec![!&left_var, right_var.clone(), var.clone()],
                        vec![!&left_var, !&right_var, !&var],
                    ]
                }
                Operation::Negation(inner) => {
                    let inner_var = lit_for_node(inner);
                    vec![
                        vec![inner_var.clone(), var.clone()],
                        vec![!&inner_var, !&var],
                    ]
                }
            }
        })
        // Finally, we add the output variable as its own clause.
        .chain(iter::once(vec![output_var]))
}

#[cfg(test)]
mod test {
    use itertools::Itertools;

    use super::*;

    #[derive(Default)]
    struct VarGen {
        counter: u32,
    }

    impl VarGen {
        fn next(&mut self) -> String {
            let name = format!("x{}", self.counter);
            self.counter += 1;
            name
        }
    }

    fn to_cnf_string(node: &Node, new_var: &mut impl FnMut() -> String) -> String {
        generate_cnf(node, new_var)
            .map(|clause| format!("({})", clause.iter().format(" \\/ ")))
            .format(" /\\ ")
            .to_string()
    }

    #[test]
    fn test_to_cnf() {
        let mut var_gen = VarGen::default();
        let mut new_var = || var_gen.next();
        let node = Node::from("a");
        assert_eq!(to_cnf_string(&node, &mut new_var), "(a)".to_string());
    }

    #[test]
    fn test_to_cnf_conjunction() {
        let mut var_gen = VarGen::default();
        let mut new_var = || var_gen.next();
        let node = Node::from("a") & Node::from("b");
        assert_eq!(
            to_cnf_string(&node, &mut new_var),
            "(-a \\/ -b \\/ x0) /\\ (a \\/ -x0) /\\ (b \\/ -x0) /\\ (x0)".to_string()
        );
    }

    #[test]
    fn test_to_cnf_disjunction() {
        let mut var_gen = VarGen::default();
        let mut new_var = || var_gen.next();
        let node = Node::from("a") | Node::from("b");
        assert_eq!(
            to_cnf_string(&node, &mut new_var),
            "(a \\/ b \\/ -x0) /\\ (-a \\/ x0) /\\ (-b \\/ x0) /\\ (x0)".to_string()
        );
    }

    #[test]
    fn test_clause_reuse() {
        let mut var_gen = VarGen::default();
        let mut new_var = || var_gen.next();
        let v = Node::from("a");
        let x = v.clone() | v;
        let y = x.clone() & (!x);
        assert_eq!(
            to_cnf_string(&y, &mut new_var),
            "(-x1 \\/ -x2 \\/ x0) /\\ (x1 \\/ -x0) /\\ (x2 \\/ -x0) /\\ (a \\/ a \\/ -x1) /\\ (-a \\/ x1) /\\ (-a \\/ x1) /\\ (x1 \\/ x2) /\\ (-x1 \\/ -x2) /\\ (x0)".to_string()
        );
    }
}
