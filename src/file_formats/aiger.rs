use std::{
    cmp::{max, min},
    collections::{HashMap, HashSet},
    io::{BufRead, BufReader, Read, Write},
};

use itertools::Itertools;

use crate::{Node, Operation};

/// Translates the output node (and the circuit it references) to (text) AIGER
/// format and writes it to the given writer.
pub fn to_aiger(f: impl Write, output: &Node) -> Result<(), String> {
    AigerWriter::new(output, false).process(f)
}

/// Translates the output node (and the circuit it references) to binary AIGER
/// format and writes it to the given writer.
pub fn to_aiger_binary(f: impl Write, output: &Node) -> Result<(), String> {
    AigerWriter::new(output, true).process(f)
}

/// Reads an AIGER file (in binary or text format) and returns the output node.
///
/// Does not support latches.
pub fn from_aiger(f: impl Read) -> Result<Node, String> {
    let mut input = BufReader::new(f);
    let AigerHeader {
        is_binary,
        input_count,
        and_count,
    } = parse_header(&mut input)?;
    let input_literals = parse_input_literals(input_count, is_binary, &mut input)?;
    let output_literal = parse_output_literal(&mut input)?;
    let and_gates = parse_and_gates(input_count, and_count, is_binary, &mut input)?;
    let gates = build_named_inputs(input_literals, &mut input)?;

    CircuitBuilder { gates, and_gates }.build_node(output_literal)
}

/// Returns true if the output of the AIG translation of the node is inverted.
fn has_inverted_output(n: &Node) -> bool {
    match n.operation() {
        Operation::Variable(_) => false,
        Operation::Constant(v) => *v,
        Operation::Conjunction(_, _) => false,
        Operation::Disjunction(_, _) => true,
        Operation::Xor(_, _) => true,
        Operation::Negation(_) => true,
    }
}

/// Returns the number of AND gates required to translate this gate.
fn and_gates_needed(n: &Node) -> usize {
    match n.operation() {
        Operation::Variable(_) | Operation::Constant(_) | Operation::Negation(_) => 0,
        Operation::Conjunction(..) | Operation::Disjunction(..) => 1,
        Operation::Xor(..) => 3,
    }
}

fn invert(literal: u32) -> u32 {
    literal ^ 1
}

fn aiger_encode_number(f: &mut impl Write, mut n: u32) -> Result<(), std::io::Error> {
    while n >= 0x80 {
        f.write_all(&[(n & 0x7f | 0x80) as u8])?;
        n >>= 7;
    }
    f.write_all(&[n as u8])
}

struct AigerWriter<'a> {
    binary_format: bool,
    output: &'a Node,
    node_id_to_literal: HashMap<usize, u32>,
    input_name_to_literal: HashMap<&'a str, u32>,
    var_count: usize,
}

impl<'a> AigerWriter<'a> {
    pub fn new(output: &'a Node, binary_format: bool) -> Self {
        // Create a node-to-literal mapping that already incorporates if the
        // output is inverted or not.
        // Start with inputs since this is a requirement for binary encoding.
        let var_name_to_literal: HashMap<_, _> = output
            .iter()
            .filter_map(|n| {
                if let Operation::Variable(name) = n.operation() {
                    Some(name.as_str())
                } else {
                    None
                }
            })
            .unique()
            .enumerate()
            .map(|(i, name)| {
                let literal = 2 * (i + 1) as u32;
                (name, literal)
            })
            .collect();
        // We skip constants and not-gates, since they do not need variables.
        // Post-order traversal is important since the predecessor nodes have to
        // have smaller IDs.
        let (node_id_to_literal, var_count) = output
            .post_visit_iter()
            .filter(|n| {
                !matches!(
                    n.operation(),
                    Operation::Constant(_) | Operation::Negation(_) | Operation::Variable(_)
                )
            })
            .fold(
                (HashMap::new(), var_name_to_literal.len()),
                |(mut map, var_count), node| {
                    let gates_needed = and_gates_needed(node);
                    assert!(gates_needed > 0);
                    let var_id = var_count + gates_needed;
                    let literal = 2 * var_id as u32 + if has_inverted_output(node) { 1 } else { 0 };
                    map.insert(node.id(), literal);
                    (map, var_id)
                },
            );
        Self {
            binary_format,
            output,
            node_id_to_literal,
            input_name_to_literal: var_name_to_literal,
            var_count,
        }
    }

    pub fn process(mut self, mut f: impl Write) -> Result<(), String> {
        let and_gates = self.compute_and_gates();
        self.write_out(&mut f, and_gates).map_err(|e| e.to_string())
    }

    fn compute_and_gates(&mut self) -> Vec<(u32, u32, u32)> {
        let mut and_gates = vec![];
        for n in self.output.post_visit_iter() {
            let gate_var = self.literal(n);
            match n.operation() {
                Operation::Variable(_) | Operation::Constant(_) | Operation::Negation(_) => {}
                Operation::Conjunction(left, right) => {
                    let left = self.literal_ref(left);
                    let right = self.literal_ref(right);
                    and_gates.push((gate_var, left, right));
                }
                Operation::Disjunction(left, right) => {
                    let left = self.literal_ref(left);
                    let right = self.literal_ref(right);
                    and_gates.push((gate_var, invert(left), invert(right)));
                }
                Operation::Xor(left, right) => {
                    let left = self.literal_ref(left);
                    let right = self.literal_ref(right);
                    let a = gate_var - 4;
                    and_gates.push((a, left, invert(right)));
                    let b = gate_var - 2;
                    and_gates.push((b, invert(left), right));
                    and_gates.push((gate_var, invert(a), invert(b)));
                }
            }
        }
        and_gates
    }

    fn write_out(
        self,
        f: &mut impl Write,
        and_gates: Vec<(u32, u32, u32)>,
    ) -> Result<(), std::io::Error> {
        // Header
        writeln!(
            f,
            "a{}g {} {} 0 1 {}",
            if self.binary_format { "i" } else { "a" },
            self.var_count,
            self.input_name_to_literal.len(),
            and_gates.len()
        )?;
        if !self.binary_format {
            // Inputs
            for var in self.input_name_to_literal.values().sorted() {
                writeln!(f, "{var}")?;
            }
        }
        // Output
        writeln!(f, "{}", self.literal_ref(self.output))?;
        // And gates
        for (out, left, right) in and_gates {
            self.write_gate(f, (out, left, right))?;
        }
        // Symbol table
        for (i, (name, _)) in self
            .input_name_to_literal
            .iter()
            .sorted_by_key(|(_, v)| *v)
            .enumerate()
        {
            writeln!(f, "i{i} {name}")?;
        }

        Ok(())
    }

    fn write_gate(&self, f: &mut impl Write, gate: (u32, u32, u32)) -> Result<(), std::io::Error> {
        let (gate_var, left, right) = gate;
        let (left, right) = (max(left, right), min(left, right));
        if self.binary_format {
            aiger_encode_number(f, gate_var - left)?;
            aiger_encode_number(f, left - right)
        } else {
            writeln!(f, "{gate_var} {left} {right}")
        }
    }

    /// Returns the literal when referencing the node, i.e. including the inversion.
    fn literal_ref(&self, node: &Node) -> u32 {
        match node.operation() {
            Operation::Constant(v) => *v as u32,
            Operation::Variable(name) => self.input_name_to_literal[name.as_str()],
            Operation::Negation(inner) => invert(self.literal_ref(inner)),
            _ => self.node_id_to_literal[&node.id()],
        }
    }

    /// Returns the literal when identifying the node in the definition,
    /// i.e. excluding the inversion.
    fn literal(&self, node: &Node) -> u32 {
        self.literal_ref(node) & !1
    }
}

struct AigerHeader {
    is_binary: bool,
    input_count: usize,
    and_count: usize,
}

fn parse_header(input: &mut impl BufRead) -> Result<AigerHeader, String> {
    let header = read_line(input)?;
    let (is_binary, header) = if let Some(header) = header.strip_prefix("aag ") {
        (false, header)
    } else if let Some(header) = header.strip_prefix("aig ") {
        (true, header)
    } else {
        return Err("Invalid header".to_string());
    };
    let header_numbers = header
        .split(' ')
        .map(|n| {
            n.parse::<usize>()
                .map_err(|e| format!("Error reading number in header: {e}"))
        })
        .collect::<Result<Vec<_>, _>>()?;
    let [_variable_count, input_count, latch_count, output_count, and_count] = header_numbers
        .try_into()
        .map_err(|_| "Invalid number of items in the header".to_string())?;

    if latch_count != 0 {
        return Err("Latches are not supported".to_string());
    }
    if output_count != 1 {
        return Err("Only one output is supported".to_string());
    }
    Ok(AigerHeader {
        is_binary,
        input_count,
        and_count,
    })
}

fn parse_input_literals(
    input_count: usize,
    is_binary: bool,
    f: &mut impl BufRead,
) -> Result<Vec<u64>, String> {
    Ok(if is_binary {
        (0..input_count).map(|i| 2 * (i as u64 + 1)).collect()
    } else {
        let literals = (0..input_count)
            .map(|_| {
                let line = read_line(f)?;
                line.parse::<u64>().map_err(|e| e.to_string())
            })
            .collect::<Result<Vec<_>, _>>()?;
        assert_eq!(literals.len(), input_count);
        literals
    })
}

fn parse_output_literal(f: &mut impl BufRead) -> Result<u64, String> {
    read_line(f)?.parse::<u64>().map_err(|e| e.to_string())
}

/// Parses the gates into a hash map of output -> (left, right).
fn parse_and_gates(
    input_count: usize,
    and_count: usize,
    is_binary: bool,
    f: &mut impl BufRead,
) -> Result<HashMap<u64, (u64, u64)>, String> {
    if is_binary {
        (0..and_count)
            .map(|i| {
                let output_literal = 2 * (input_count + 1 + i) as u64;
                let delta0 = aiger_decode_number(f)? as u64;
                let delta1 = aiger_decode_number(f)? as u64;
                let left = output_literal - delta0;
                let right = left - delta1;
                Ok((output_literal, (left, right)))
            })
            .collect()
    } else {
        // Lines of the form: (out, left, right)
        (0..and_count)
            .map(|_| {
                let line = read_line(f)?;
                let items = line
                    .split(' ')
                    .map(|n| {
                        n.parse::<u64>()
                            .map_err(|e| format!("Error parsing gate number: {e}"))
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                match items.as_slice() {
                    [output, left, right] => {
                        if output % 2 != 0 {
                            Err(format!("Expected even literal for output: {output}"))
                        } else {
                            Ok((*output, (*left, *right)))
                        }
                    }
                    _ => Err(format!(
                        "Invalid number of gate items, expected 3 got {}",
                        items.len()
                    )),
                }
            })
            .try_fold(HashMap::new(), |mut acc, res| {
                let (output, (left, right)) = res?;
                if acc.insert(output, (left, right)).is_none() {
                    Ok(acc)
                } else {
                    Err(format!("Duplicate output gate ID: {output}"))
                }
            })
    }
}

fn aiger_decode_number(f: &mut impl Read) -> Result<u32, String> {
    let mut result: u32 = 0;
    let mut buf = [0; 1];
    for shift_amount in (0..).step_by(7) {
        f.read_exact(&mut buf).map_err(|e| e.to_string())?;
        let b = buf[0];
        result |= ((b & 0x7f) as u32) << shift_amount;
        if b & 0x80 == 0 {
            break;
        }
    }
    Ok(result)
}

fn build_named_inputs(
    input_literals: Vec<u64>,
    f: &mut impl BufRead,
) -> Result<HashMap<u64, Node>, String> {
    let mut used_input_names: HashSet<String> = Default::default();
    let mut named_inputs = HashMap::default();
    loop {
        let Ok(line) = read_line(f) else {
            break;
        };
        let Some(suffix) = line.strip_prefix("i") else {
            break;
        };
        let parts = suffix.split(' ').collect_vec();
        if parts.len() != 2 {
            return Err(format!(
                "Expected exactly two parts for input name, but got {suffix}"
            ));
        }
        let index = parts[0]
            .parse::<usize>()
            .map_err(|e| format!("Expected input literal: {e}"))?;
        if index >= input_literals.len() {
            return Err(format!("Out of range for input literal name: {index}"));
        }
        let name = parts[1];
        if !used_input_names.insert(name.to_string()) {
            return Err(format!("Duplicate input name: {name}"));
        }
        named_inputs.insert(input_literals[index], Node::from(parts[1]));
    }
    let mut last_input_id = 0;
    let anonymous_inputs = input_literals
        .iter()
        .filter(|lit| !named_inputs.contains_key(lit))
        .map(|&lit| {
            while used_input_names.contains(&format!("v_{last_input_id}")) {
                last_input_id += 1;
            }
            (lit, Node::from(format!("v_{last_input_id}")))
        })
        .collect_vec();
    named_inputs.extend(anonymous_inputs);
    assert_eq!(named_inputs.len(), input_literals.len());
    Ok(named_inputs)
}

struct CircuitBuilder {
    gates: HashMap<u64, Node>,
    and_gates: HashMap<u64, (u64, u64)>,
}

impl CircuitBuilder {
    fn build_node(&mut self, literal: u64) -> Result<Node, String> {
        if literal & 1 == 1 {
            return Ok(!(self.build_node(literal & !1)?));
        }
        Ok(if let Some(n) = self.gates.get(&literal) {
            n.clone()
        } else {
            let (left, right) = self
                .and_gates
                .get(&literal)
                .cloned()
                .ok_or_else(|| format!("Gate not found: {literal}"))?;
            self.build_node(left)? & self.build_node(right)?
        })
    }
}

fn read_line(input: &mut impl BufRead) -> Result<String, String> {
    let mut line = String::new();
    match input.read_line(&mut line) {
        Ok(0) => Err("Unexpected end of input".to_string()),
        Ok(_n) => {
            if line.ends_with('\n') {
                line.pop();
                if line.ends_with('\r') {
                    line.pop();
                }
            }
            Ok(line)
        }
        Err(e) => Err(e.to_string()),
    }
}

#[cfg(test)]
mod test {
    use super::*;

    fn test_aiger_out(node: Node, expected: &str) {
        let mut buf = vec![];
        to_aiger(&mut buf, &node).unwrap();
        assert_eq!(String::from_utf8(buf).unwrap(), expected);
    }

    mod output {
        use super::*;
        use pretty_assertions::assert_eq;

        #[test]
        fn constant_true() {
            let output = Node::from(true);
            test_aiger_out(output, "aag 0 0 0 1 0\n1\n");
        }

        #[test]
        fn constant_false() {
            let output = Node::from(false);
            test_aiger_out(output, "aag 0 0 0 1 0\n0\n");
        }

        #[test]
        fn inverter() {
            let output = !Node::from("x");
            test_aiger_out(output, "aag 1 1 0 1 0\n2\n3\ni0 x\n");
        }

        #[test]
        fn and_gate() {
            let output = Node::from("x") & Node::from("y");
            test_aiger_out(output, "aag 3 2 0 1 1\n2\n4\n6\n6 4 2\ni0 x\ni1 y\n");
        }

        #[test]
        fn or_gate() {
            let output = Node::from("x") | Node::from("y");
            test_aiger_out(output, "aag 3 2 0 1 1\n2\n4\n7\n6 5 3\ni0 x\ni1 y\n");
        }

        #[test]
        fn xor_gate() {
            let output = Node::from("x") ^ Node::from("y");
            test_aiger_out(
                output,
                "aag 5 2 0 1 3\n2\n4\n11\n6 5 2\n8 4 3\n10 9 7\ni0 x\ni1 y\n",
            );
        }

        #[test]
        fn var_repetition() {
            // Tests repetition of the same variable name but in different nodes.
            let output = Node::from("x") & Node::from("x");
            test_aiger_out(output, "aag 2 1 0 1 1\n2\n4\n4 2 2\ni0 x\n");
        }

        #[test]
        fn multi_stage() {
            let a = Node::from("x") & Node::from("y");
            let output = &a | &!&a;
            test_aiger_out(output, "aag 4 2 0 1 2\n2\n4\n9\n6 4 2\n8 7 6\ni0 x\ni1 y\n");
        }

        #[test]
        fn encode_number() {
            let mut buf = vec![];
            aiger_encode_number(&mut buf, 0x7f).unwrap();
            assert_eq!(buf, vec![0x7f]);
            buf.clear();
            aiger_encode_number(&mut buf, 0x80).unwrap();
            assert_eq!(buf, vec![0x80, 0x01]);
            buf.clear();
            aiger_encode_number(&mut buf, 0x81).unwrap();
            assert_eq!(buf, vec![0x81, 0x01]);
            buf.clear();
            aiger_encode_number(&mut buf, 16387).unwrap();
            assert_eq!(buf, vec![0x83, 0x80, 0x01]);
            buf.clear();
        }

        #[test]
        fn multi_stage_binary() {
            let a = Node::from("x") & Node::from("y");
            let output = &a | &!&a;
            let mut buf = vec![];
            to_aiger_binary(&mut buf, &output).unwrap();
            let expected = b"aig 4 2 0 1 2\n9\n\x02\x02\x01\x01i0 x\ni1 y\n";
            assert_eq!(buf, expected);
        }
    }

    mod input {

        use crate::evaluate;

        use super::*;

        fn test_function_x_y(data: &[u8], fun: &impl Fn(bool, bool) -> bool) {
            let out = from_aiger(data).unwrap();
            for x_val in [false, true] {
                for y_val in [false, true] {
                    let assignments = [("x", x_val), ("y", y_val)]
                        .into_iter()
                        .map(|(n, v)| (n.to_string(), v))
                        .collect();
                    let result = evaluate(&out, &assignments);
                    assert_eq!(result, fun(x_val, y_val));
                }
            }
        }

        #[test]
        fn xor_ascii() {
            let data = b"aag 5 2 0 1 3\n2\n4\n11\n6 5 2\n8 4 3\n10 9 7\ni0 x\ni1 y\n";
            test_function_x_y(data, &|x, y| x ^ y);
        }

        #[test]
        fn multi_stage_binary() {
            let data = b"aig 4 2 0 1 2\n9\n\x02\x02\x01\x01i0 x\ni1 y\n";
            test_function_x_y(data, &|_, _| true);
        }

        #[test]
        fn decode_number() {
            let buf = vec![0x7f];
            assert_eq!(aiger_decode_number(&mut &*buf).unwrap(), 0x7f);
            let buf = vec![0x80, 0x01];
            assert_eq!(aiger_decode_number(&mut &*buf).unwrap(), 0x80);
            let buf = vec![0x81, 0x01];
            assert_eq!(aiger_decode_number(&mut &*buf).unwrap(), 0x81);
            let buf = vec![0x83, 0x80, 0x01];
            assert_eq!(aiger_decode_number(&mut &*buf).unwrap(), 16387);
        }
    }
}
