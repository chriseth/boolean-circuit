use std::{collections::HashSet, rc::Rc};

use super::literal::Literal;

/// A node or gate in a boolean circuit.
///
/// The inputs of the circuit are variables identified by their name.
/// Other types of nodes are constant nodes or operations that have
/// predecessors.
///
/// The clone operation only performs a shallow clone and thus
/// allows sharing of nodes.
#[derive(Clone, Debug)]
pub struct Node(Rc<Operation>);

/// The inner operation of a {Node} and the predecessors.
#[derive(Clone, Debug)]
pub enum Operation {
    /// An input variable.
    Variable(Rc<String>),
    /// A constant value.
    Constant(bool),
    /// The boolean negation of another node.
    Negation(Node),
    /// The boolean conjunction of two nodes.
    Conjunction(Node, Node),
    /// The boolean disjunction of two nodes.
    Disjunction(Node, Node),
    /// The boolean exclusive or of two nodes.
    Xor(Node, Node),
}

impl From<&str> for Node {
    /// Constructs a new node representing an input variable.
    ///
    /// Two variables with the same name are considered equal, even
    /// if they are different node instances.
    fn from(name: &str) -> Node {
        name.to_string().into()
    }
}

impl From<String> for Node {
    /// Constructs a new node representing an input variable.
    ///
    /// Two variables with the same name are considered equal, even
    /// if they are different node instances.
    fn from(name: String) -> Node {
        Node(Rc::new(Operation::Variable(Rc::new(name))))
    }
}

impl From<bool> for Node {
    /// Creates a constant node.
    fn from(value: bool) -> Node {
        Node(Rc::new(Operation::Constant(value)))
    }
}

impl From<&Literal> for Node {
    /// Converts a literal to either a variable or a node that is the negation
    /// of a variable.
    fn from(literal: &Literal) -> Node {
        let v = literal.var().into();
        if literal.is_negated() {
            !&v
        } else {
            v
        }
    }
}

impl Node {
    /// Returns an identifier for the node which is unique in the circuit
    /// but not stable across program reloads.
    pub fn id(&self) -> usize {
        Rc::as_ptr(&self.0) as usize
    }

    /// Returns the operation of the node.
    pub fn operation(&self) -> &Operation {
        &self.0
    }

    /// Creates an iterator over the graph (the node itself and all its predecessors)
    /// that returns each node exactly once.
    pub fn iter(&self) -> impl Iterator<Item = &Node> {
        self.into_iter()
    }

    /// Creates an iterator over the graph (the node itself and all its predecessors)
    /// with post-visit order, visiting each node exactly once.
    /// This means that the predecessors of each node are always visited before the node itself.
    pub fn post_visit_iter(&self) -> impl Iterator<Item = &Node> {
        PostVisitIterator::new(self)
    }

    /// Turns the node and its predecessors into a string representation, repeating shared nodes.
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
            Operation::Negation(node) => format!("!{}", node.to_string_as_tree()),
        }
    }

    /// Returns the value of the node if it is a constant input node.
    pub fn try_to_constant(&self) -> Option<bool> {
        match self.operation() {
            Operation::Constant(value) => Some(*value),
            _ => None,
        }
    }

    /// Returns the number of variables and gates (nodes not counting
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

impl std::ops::BitAnd for Node {
    type Output = Node;

    fn bitand(self, other: Node) -> Node {
        Node(Rc::new(Operation::Conjunction(self, other)))
    }
}

impl std::ops::BitAnd for &Node {
    type Output = Node;

    fn bitand(self, other: &Node) -> Node {
        Node::bitand(self.clone(), other.clone())
    }
}

impl std::ops::BitOr for Node {
    type Output = Node;

    fn bitor(self, other: Node) -> Node {
        Node(Rc::new(Operation::Disjunction(self, other)))
    }
}

impl std::ops::BitOr for &Node {
    type Output = Node;

    fn bitor(self, other: &Node) -> Node {
        Node::bitor(self.clone(), other.clone())
    }
}

impl std::ops::BitXor for Node {
    type Output = Node;

    fn bitxor(self, other: Node) -> Node {
        Node(Rc::new(Operation::Xor(self, other)))
    }
}

impl std::ops::BitXor for &Node {
    type Output = Node;

    fn bitxor(self, other: &Node) -> Node {
        Node::bitxor(self.clone(), other.clone())
    }
}

impl std::ops::Not for Node {
    type Output = Node;

    fn not(self) -> Node {
        Node(Rc::new(Operation::Negation(self)))
    }
}

impl std::ops::Not for &Node {
    type Output = Node;

    fn not(self) -> Node {
        Node::not(self.clone())
    }
}

impl<'a> IntoIterator for &'a Node {
    type Item = &'a Node;
    type IntoIter = GraphIterator<'a>;

    /// Creates an iterator over the graph that returns each node exactly once.
    fn into_iter(self) -> Self::IntoIter {
        GraphIterator::new(self)
    }
}

pub struct GraphIterator<'a> {
    visited: HashSet<usize>,
    stack: Vec<&'a Node>,
}

impl<'a> GraphIterator<'a> {
    fn new(node: &'a Node) -> Self {
        Self {
            visited: HashSet::new(),
            stack: vec![node],
        }
    }

    fn add_predecessors(&mut self, node: &'a Node) {
        match node.operation() {
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
    type Item = &'a Node;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(node) = self.stack.pop() {
            if self.visited.insert(node.id()) {
                self.add_predecessors(node);
                return Some(node);
            }
        }
        None
    }
}

struct PostVisitIterator<'a> {
    visited: HashSet<usize>,
    /// Stack of nodes to visit. If the flag is true, we will have
    /// visited all its predecessors once we reach the node.
    stack: Vec<(&'a Node, bool)>,
}

impl<'a> PostVisitIterator<'a> {
    fn new(node: &'a Node) -> Self {
        Self {
            visited: HashSet::new(),
            stack: vec![(node, false)],
        }
    }
}

impl<'a> Iterator for PostVisitIterator<'a> {
    type Item = &'a Node;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some((node, visited_predecessors)) = self.stack.pop() {
            if visited_predecessors {
                return Some(node);
            } else if self.visited.insert(node.id()) {
                self.stack.push((node, true));
                match node.operation() {
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
