use std::{collections::HashSet, rc::Rc};

use super::literal::Literal;

/// A gate in a boolean circuit.
///
/// The inputs of the circuit are variables identified by their name.
/// Other types of gates are constant gates or operations that have
/// predecessors.
///
/// The clone operation only performs a shallow clone and thus
/// allows sharing of gates.
#[derive(Clone, Debug)]
pub struct Gate(Rc<Operation>);

/// The inner operation of a {Gate} and the predecessors.
#[derive(Clone, Debug)]
pub enum Operation {
    /// An input variable.
    Variable(Rc<String>),
    /// A constant value.
    Constant(bool),
    /// The boolean negation of another gate.
    Negation(Gate),
    /// The boolean conjunction of two gates.
    Conjunction(Gate, Gate),
    /// The boolean disjunction of two gates.
    Disjunction(Gate, Gate),
    /// The boolean exclusive or of two gates.
    Xor(Gate, Gate),
}

impl From<&str> for Gate {
    /// Constructs a new gate representing an input variable.
    ///
    /// Two variables with the same name are considered equal, even
    /// if they are different {Gate} instances.
    fn from(name: &str) -> Gate {
        name.to_string().into()
    }
}

impl From<String> for Gate {
    /// Constructs a new gate representing an input variable.
    ///
    /// Two variables with the same name are considered equal, even
    /// if they are different gate instances.
    fn from(name: String) -> Gate {
        Gate(Rc::new(Operation::Variable(Rc::new(name))))
    }
}

impl From<bool> for Gate {
    /// Creates a constant gate.
    fn from(value: bool) -> Gate {
        Gate(Rc::new(Operation::Constant(value)))
    }
}

impl From<&Literal> for Gate {
    /// Converts a literal to either a variable or a gate that is the negation
    /// of a variable.
    fn from(literal: &Literal) -> Gate {
        let v = literal.var().into();
        if literal.is_negated() {
            !&v
        } else {
            v
        }
    }
}

impl Gate {
    /// Returns an identifier for the gate which is unique in the circuit
    /// but not stable across program reloads.
    pub fn id(&self) -> usize {
        Rc::as_ptr(&self.0) as usize
    }

    /// Returns the operation of the gate.
    pub fn operation(&self) -> &Operation {
        &self.0
    }

    /// Creates an iterator over the graph (the gate itself and all its predecessors)
    /// that returns each gate exactly once.
    pub fn iter(&self) -> impl Iterator<Item = &Gate> {
        self.into_iter()
    }

    /// Creates an iterator over the graph (the gate itself and all its predecessors)
    /// with post-visit order, visiting each gate exactly once.
    /// This means that the predecessors of each gate are always visited before the gate itself.
    pub fn post_visit_iter(&self) -> impl Iterator<Item = &Gate> {
        PostVisitIterator::new(std::iter::once(self))
    }

    /// Turns the gate and its predecessors into a string representation, repeating shared gates.
    pub fn to_string_as_tree(&self) -> String {
        match self.operation() {
            Operation::Variable(name) => format!("{name}"),
            Operation::Constant(value) => format!("{value}"),
            Operation::Conjunction(left, right) => {
                format!(
                    "({} & {})",
                    left.to_string_as_tree(),
                    right.to_string_as_tree()
                )
            }
            Operation::Disjunction(left, right) => {
                format!(
                    "({} | {})",
                    left.to_string_as_tree(),
                    right.to_string_as_tree()
                )
            }
            Operation::Xor(left, right) => format!(
                "({} ^ {})",
                left.to_string_as_tree(),
                right.to_string_as_tree()
            ),
            Operation::Negation(gate) => format!("!{}", gate.to_string_as_tree()),
        }
    }

    /// Returns the value of the gate if it is a constant input gate.
    pub fn try_to_constant(&self) -> Option<bool> {
        match self.operation() {
            Operation::Constant(value) => Some(*value),
            _ => None,
        }
    }

    /// Returns the number of variables and inner gates (gates not counting
    /// variables or constants) in the circuit.
    ///
    /// This depends on how the circuit was constructed, i.e. it does not deduplicate
    /// sub-circuits, but it does deduplicate variables with the same name.
    pub fn gate_count(&self) -> (usize, usize) {
        let mut vars: HashSet<_> = Default::default();
        let mut gate_count = 0;
        for n in self {
            match n.operation() {
                Operation::Variable(v) => {
                    vars.insert(v.as_str());
                }
                Operation::Constant(_) => {}
                Operation::Negation(..)
                | Operation::Conjunction(..)
                | Operation::Disjunction(..)
                | Operation::Xor(..) => {
                    gate_count += 1;
                }
            }
        }
        (vars.len(), gate_count)
    }
}

impl std::ops::BitAnd for Gate {
    type Output = Gate;

    fn bitand(self, other: Gate) -> Gate {
        Gate(Rc::new(Operation::Conjunction(self, other)))
    }
}

impl std::ops::BitAnd for &Gate {
    type Output = Gate;

    fn bitand(self, other: &Gate) -> Gate {
        Gate::bitand(self.clone(), other.clone())
    }
}

impl std::ops::BitOr for Gate {
    type Output = Gate;

    fn bitor(self, other: Gate) -> Gate {
        Gate(Rc::new(Operation::Disjunction(self, other)))
    }
}

impl std::ops::BitOr for &Gate {
    type Output = Gate;

    fn bitor(self, other: &Gate) -> Gate {
        Gate::bitor(self.clone(), other.clone())
    }
}

impl std::ops::BitXor for Gate {
    type Output = Gate;

    fn bitxor(self, other: Gate) -> Gate {
        Gate(Rc::new(Operation::Xor(self, other)))
    }
}

impl std::ops::BitXor for &Gate {
    type Output = Gate;

    fn bitxor(self, other: &Gate) -> Gate {
        Gate::bitxor(self.clone(), other.clone())
    }
}

impl std::ops::Not for Gate {
    type Output = Gate;

    fn not(self) -> Gate {
        Gate(Rc::new(Operation::Negation(self)))
    }
}

impl std::ops::Not for &Gate {
    type Output = Gate;

    fn not(self) -> Gate {
        Gate::not(self.clone())
    }
}

impl<'a> IntoIterator for &'a Gate {
    type Item = &'a Gate;
    type IntoIter = GraphIterator<'a>;

    /// Creates an iterator over the graph that returns each gate exactly once.
    fn into_iter(self) -> Self::IntoIter {
        GraphIterator::new(std::iter::once(self))
    }
}

pub struct GraphIterator<'a> {
    visited: HashSet<usize>,
    stack: Vec<&'a Gate>,
}

impl<'a> GraphIterator<'a> {
    pub(crate) fn new(gates: impl IntoIterator<Item = &'a Gate>) -> Self {
        Self {
            visited: HashSet::new(),
            stack: gates.into_iter().collect(),
        }
    }

    fn add_predecessors(&mut self, gate: &'a Gate) {
        match gate.operation() {
            Operation::Variable(_) | Operation::Constant(_) => {}
            Operation::Conjunction(left, right)
            | Operation::Disjunction(left, right)
            | Operation::Xor(left, right) => {
                self.stack.push(right);
                self.stack.push(left);
            }
            Operation::Negation(inner) => {
                self.stack.push(inner);
            }
        }
    }
}

impl<'a> Iterator for GraphIterator<'a> {
    type Item = &'a Gate;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(gate) = self.stack.pop() {
            if self.visited.insert(gate.id()) {
                self.add_predecessors(gate);
                return Some(gate);
            }
        }
        None
    }
}

pub(crate) struct PostVisitIterator<'a> {
    visited: HashSet<usize>,
    /// Stack of gates to visit. If the flag is true, we will have
    /// visited all its predecessors once we reach the gate.
    stack: Vec<(&'a Gate, bool)>,
}

impl<'a> PostVisitIterator<'a> {
    pub(crate) fn new(gates: impl IntoIterator<Item = &'a Gate>) -> Self {
        Self {
            visited: HashSet::new(),
            stack: gates.into_iter().map(|n| (n, false)).collect(),
        }
    }
}

impl<'a> Iterator for PostVisitIterator<'a> {
    type Item = &'a Gate;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some((gate, visited_predecessors)) = self.stack.pop() {
            if visited_predecessors {
                return Some(gate);
            } else if self.visited.insert(gate.id()) {
                self.stack.push((gate, true));
                match gate.operation() {
                    Operation::Variable(_) | Operation::Constant(_) => {}
                    Operation::Conjunction(left, right)
                    | Operation::Disjunction(left, right)
                    | Operation::Xor(left, right) => {
                        self.stack.push((right, false));
                        self.stack.push((left, false));
                    }
                    Operation::Negation(inner) => {
                        self.stack.push((inner, false));
                    }
                }
            }
        }
        None
    }
}
