# boolean-circuit

A library to import, modify and export boolean circuits.

## Circuits

A circuit in this library is a directed acyclic graph (DAG) where the nodes are gates of one of the following types:

- Variable / Input gate
- Constant true / false
- Negation
- Conjunction / And
- Disjunciton / Or
- Exclusive Or

Predecessors are stored via `Rc`-pointers, all clones are shallow.

Input gates are identified by their name, i.e. independently created input gates with the same name are considered
the same gate.

While circuits can be imported from files, it is also rather straightforward to create them programmatically.
Rust's boolean operators are supported on gates.


## Supported File Formats

### AIGER

[AIGER](https://fmv.jku.at/aiger/) is a file format for and-inverter graphs. This library supports reading and
writing AIGER files both in binary and text format.

Latches or multiple output nodes are not supported.

Both the conversion to and the conversion from AIGER results in more gates since and-inverter gates are not native
to this library.

### DIMACS

A conversion from and to the DIMACS CNF format is supported. A Tseitin transformation is used to convert the circuit
to CNF which creates now variables and thus a callback to generate new unique variable names is required.


# License

This project is dual-licensed under MIT and Apache 2.0.