use crate::Node;

/// Constructs a node that evaluates to `true` if and only if `x` and `y`
/// evaluate to the same value.
pub fn eq(x: &Node, y: &Node) -> Node {
    !(x ^ y)
}

/// Constructs a node that evaluates to `true` if and only if all of the
/// nodes returned by `i` evaulate to `true`.
///
/// The construction has logarithmic depth in the length if `i`.
pub fn reduce_conjunction(i: impl IntoIterator<Item = Node>) -> Node {
    reduce_associative(i.into_iter().collect::<Vec<_>>().as_slice(), |x, y| x & y)
        .unwrap_or_else(|| true.into())
}

/// Constructs a node that evaluates to `true` if and only if at least one of the
/// nodes returned by `i` evaulates to `true`.
///
/// The construction has logarithmic depth in the length if `i`.
pub fn reduce_disjunction(i: impl IntoIterator<Item = Node>) -> Node {
    reduce_associative(i.into_iter().collect::<Vec<_>>().as_slice(), |x, y| x | y)
        .unwrap_or_else(|| false.into())
}

/// Constructs a node that evaluates to `true` if and only if an odd number of the
/// nodes returned by `i` evaulate to `true`.
///
/// The construction has logarithmic depth in the length if `i`.
pub fn reduce_xor(i: impl IntoIterator<Item = Node>) -> Node {
    reduce_associative(i.into_iter().collect::<Vec<_>>().as_slice(), |x, y| x ^ y).unwrap()
}

fn reduce_associative<T: Clone>(i: &[T], op: fn(&T, &T) -> T) -> Option<T> {
    match i.len() {
        0 => None,
        1 => Some(i[0].clone()),
        _ => {
            let mid = i.len() / 2;
            Some(op(
                &reduce_associative(&i[..mid], op).unwrap(),
                &reduce_associative(&i[mid..], op).unwrap(),
            ))
        }
    }
}
