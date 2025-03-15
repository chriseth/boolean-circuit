use std::{
    collections::HashMap,
    io::{BufRead, Read, Write},
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

/// Parses a DIMACS file and returns it in CNF.
/// Variable names are kept as decimal numbers.
pub fn from_dimacs(i: impl Read) -> Result<Vec<Vec<Literal>>, String> {
    let mut reader = std::io::BufReader::new(i);
    let mut header = Default::default();
    reader.read_line(&mut header).map_err(|e| e.to_string())?;
    if !header.starts_with("p cnf") {
        return Err("Invalid DIMACS header, expected to start with 'p cnf'.".to_string());
    }
    // We ignore the number of clauses and variables, since it is not relevant.
    reader
        .lines()
        .map(|line| {
            let line = line.map_err(|e| e.to_string())?;
            let mut items = line.split_whitespace();
            if items.next_back() != Some("0") {
                return Err("Invalid DIMACS clause, expected to end with '0'.".to_string());
            }
            items
                .map(|item| {
                    if item == "0" {
                        Err(format!(
                            "Invalid DIMACS clause, inner literal {item} not allowed."
                        ))
                    } else if let Some(name) = item.strip_prefix('-') {
                        Ok(!Literal::from(name))
                    } else {
                        Ok(Literal::from(item))
                    }
                })
                .collect::<Result<Vec<_>, String>>()
        })
        .collect::<Result<Vec<_>, String>>()
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_var_mapping() {
        let cnf = vec![vec!["a".into(), "b".into(), !Literal::from("a")]];
        let var_map = var_mapping(&cnf);
        assert_eq!(var_map.len(), 2);
        assert_eq!(var_map["a"], 1);
        assert_eq!(var_map["b"], 2);
    }

    #[test]
    fn test_to_dimacs() {
        let x: Literal = "x".into();
        let y: Literal = "y".into();
        let z: Literal = "z".into();

        let cnf = vec![
            vec![x.clone(), y.clone()],
            vec![!x.clone(), z.clone()],
            vec![y.clone(), z.clone()],
            vec![],
        ];
        let mut buf = Vec::new();
        let var_map = to_dimacs(&mut buf, &cnf);
        let expected = "p cnf 3 4\n1 2 0\n-1 3 0\n2 3 0\n0\n";
        assert_eq!(String::from_utf8(buf).unwrap(), expected);
        assert_eq!(var_map.len(), 3);
        assert_eq!(var_map[&1], "x");
        assert_eq!(var_map[&2], "y");
        assert_eq!(var_map[&3], "z");
    }

    #[test]
    fn test_from_dimacs() {
        let input = "p cnf 2 4\n1 2 0\n-2 0\n1 0\n0\n";
        let cnf = from_dimacs(input.as_bytes()).unwrap();
        assert_eq!(
            cnf,
            vec![
                vec![Literal::from("1"), Literal::from("2")],
                vec![!Literal::from("2")],
                vec![Literal::from("1")],
                vec![],
            ]
        );
        let mut buf = Vec::new();
        to_dimacs(&mut buf, &cnf);
        assert_eq!(String::from_utf8(buf).unwrap(), input);
    }
}
