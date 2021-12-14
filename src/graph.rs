use std::collections::HashMap;
use std::fmt::Display;
use std::hash::Hash;
use std::io::Write;

pub trait Node: Display + Eq + Hash {}

pub fn render_graph<W, N, Wh>(output: &mut W, edges: Vec<(N, N, Wh)>) -> std::io::Result<()>
where
    W: Write,
    N: Node,
    Wh: Display,
{
    writeln!(output, "digraph {{")?;

    let mut index = 0;
    let mut nodes = HashMap::<&N, usize>::new();
    let node_iter = edges.iter().flat_map(|(a, b, _)| [a, b]);
    for node in node_iter {
        if !nodes.contains_key(node) {
            writeln!(output, "\tnode [label=\"{}\"] {};", node, index)?;
            nodes.insert(node, index);
            index += 1;
        }
    }

    writeln!(output)?;

    for (a, b, w) in edges.iter() {
        let a_idx = nodes.get(a).unwrap();
        let b_idx = nodes.get(b).unwrap();
        writeln!(output, "\t{} -> {} [label=\"{}\"];", a_idx, b_idx, w)?;
    }

    writeln!(output, "}}")?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;

    impl Node for i32 {}

    #[test]
    fn test_dump() -> std::io::Result<()> {
        let edges = vec![(1, 2, "a"), (1, 3, "b"), (2, 3, "c")];
        let mut output = fs::File::create("test-output.dot")?;
        render_graph(&mut output, edges)?;
        Ok(())
    }
}
