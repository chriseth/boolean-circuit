use std::rc::Rc;

use itertools::Itertools;

/// A positive or negated variable identified by its name.
///
/// Cloning is efficient because the name is shared.
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum Literal {
    Pos(Rc<String>),
    Neg(Rc<String>),
}

impl Literal {
    /// Returns the name of the variable.
    pub fn var(&self) -> &str {
        match self {
            Literal::Pos(name) | Literal::Neg(name) => name.as_str(),
        }
    }

    /// Returns true if the literal is negated, false otherwise.
    pub fn is_negated(&self) -> bool {
        match self {
            Literal::Pos(_) => false,
            Literal::Neg(_) => true,
        }
    }
}

/// Formats a clause in human-readable form.
pub fn clause_to_string(clause: &[Literal]) -> String {
    clause.iter().format(" v ").to_string()
}

impl From<&str> for Literal {
    fn from(name: &str) -> Literal {
        Literal::Pos(Rc::new(name.to_string()))
    }
}

impl std::ops::Not for &Literal {
    type Output = Literal;

    fn not(self) -> Literal {
        match self {
            Literal::Pos(name) => Literal::Neg(Rc::clone(name)),
            Literal::Neg(name) => Literal::Pos(Rc::clone(name)),
        }
    }
}

impl std::fmt::Display for Literal {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Literal::Pos(name) => write!(f, "{name}"),
            Literal::Neg(name) => write!(f, "-{name}"),
        }
    }
}
