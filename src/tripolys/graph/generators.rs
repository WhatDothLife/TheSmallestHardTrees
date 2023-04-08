//! Provides functions to construct common types of directed graphs.

use super::traits::Build;

/// Returns a directed path with `n` vertices.
pub fn directed_path<G>(n: usize) -> G
where
    G: Build<Vertex = usize>,
{
    let mut g = G::with_capacities(n, n - 1);
    for v in 0..n {
        g.add_vertex(v);
    }
    for (u, v) in (0..n).zip((0..n).skip(1)) {
        g.add_edge(u, v);
    }
    g
}

/// Returns a directed cycle with length `n`.
pub fn directed_cycle<G>(n: usize) -> G
where
    G: Build<Vertex = usize>,
{
    let mut g = G::with_capacities(n, n);
    for v in 0..n {
        g.add_vertex(v);
    }
    for (u, v) in (0..n).zip((0..n).cycle().skip(1)) {
        g.add_edge(u, v);
    }
    g
}

/// Returns a transitive tournament graph on `n` vertices.
pub fn transitive_tournament<G>(n: usize) -> G
where
    G: Build<Vertex = usize>,
{
    let mut g = G::with_capacities(n, n);
    for v in 0..n {
        g.add_vertex(v);
    }
    for (u, v) in (0..n).flat_map(|u| (u..n).map(move |v| (u, v))) {
        g.add_edge(u, v);
    }
    g
}

/// Returns the complete digraph on `n` vertices.
pub fn complete_digraph<G>(n: usize) -> G
where
    G: Build<Vertex = usize>,
{
    let mut g = G::with_capacities(n, n);
    for v in 0..n {
        g.add_vertex(v);
    }
    for (u, v) in (0..n)
        .flat_map(|u| (0..n).map(move |v| (u, v)))
        .filter(|(a, b)| a != b)
    {
        g.add_edge(u, v);
    }
    g
}

/// Returns the complete digraph on `n` vertices.
pub fn triad<G>(s: &str) -> Result<G, String>
where
    G: Build<Vertex = usize>,
{
    if s.matches(',').count() != 2 {
        return Err("A triad must have exactly 3 arms!".into());
    }

    let nvertices = s.len() - 1;
    let mut g = G::with_capacities(nvertices, nvertices - 1);
    for v in 0..nvertices {
        g.add_vertex(v);
    }

    let mut j = 1;
    for arm in s.split(',') {
        for (i, c) in arm.chars().enumerate() {
            match c {
                '1' => {
                    if i == 0 {
                        g.add_edge(j, 0);
                    } else {
                        g.add_edge(j, j - 1);
                    }
                }
                '0' => {
                    if i == 0 {
                        g.add_edge(0, j);
                    } else {
                        g.add_edge(j - 1, j);
                    }
                }
                c => {
                    return Err(format!(
                        "Could not parse {c} as edge (must be either '0' or '1')"
                    ));
                }
            }
            j += 1;
        }
    }

    Ok(g)
}
