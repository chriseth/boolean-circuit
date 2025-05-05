## Version 2.2.0

- Ability to create deep copies of circuits, i.e. a circuit with the same behavior, but which does not share gates with the original.
- Ability to create disjoint unions of circuits, i.e. combine circuits that might share gates into a single circuit while creating deep copies.

## Version 2.1.0

- Ability to set a certain order of input nodes (useful for AIGER import/export).

## Vesion 2.0.0

- Added `Circuit` as a concept that can have multiple outputs.
- Renamed `Node` to `Gate`.

## Version 1.0.0

- First public release.
