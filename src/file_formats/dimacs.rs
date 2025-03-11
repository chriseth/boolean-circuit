use std::{
    collections::HashMap,
    io::{BufRead, Read, Write},
    rc::Rc,
};

use itertools::Itertools;

use crate::Literal;

/// Writes the given CNF into a writer in DIMACS format and returns
/// a mapping from variable IDs to their names.
pub fn to_dimacs(mut w: impl Write, cnf: &[Vec<Literal>]) -> HashMap<u32, String> {
    let var_map = var_mapping(cnf);
    writeln!(w, "p cnf {} {}", var_map.len(), cnf.len()).unwrap();

    for clause in cnf {
        for literal in clause {
            if literal.is_negated() {
                write!(w, "-").unwrap();
            }
            write!(w, "{} ", var_map[literal.var()]).unwrap();
        }
        writeln!(w, "0").unwrap();
    }
    // Invert the mapping
    var_map
        .into_iter()
        .map(|(name, id)| (id, name.to_string()))
        .collect()
}

fn var_mapping(cnf: &[Vec<Literal>]) -> HashMap<String, u32> {
    cnf.iter()
        .flatten()
        .map(|literal| literal.var())
        .unique()
        .enumerate()
        .map(|(i, var)| (var.to_string(), (i + 1) as u32))
        .collect()
}

/// Parses a pseudo dimacs file and returns it as a CNF.
pub fn from_pseudo_dimacs(i: impl Read) -> Vec<Vec<Literal>> {
    std::io::BufReader::new(i)
        .lines()
        .map(|line| {
            let line = line.unwrap();
            line.split_whitespace()
                .map(|name| {
                    if let Some(name) = name.strip_prefix('-') {
                        Literal::Neg(Rc::new(name.to_string()))
                    } else {
                        Literal::Pos(Rc::new(name.to_string()))
                    }
                })
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>()
}
