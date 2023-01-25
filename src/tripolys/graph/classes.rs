/// Returns a directed path with `m` edges.
pub fn directed_path<G>(m: usize) -> G
where
    G: FromIterator<(usize, usize)>,
{
    G::from_iter((0..=m).zip((0..=m).skip(1)))
}

/// Returns a directed cycle with length `n`.
pub fn directed_cycle<G>(n: usize) -> G
where
    G: FromIterator<(usize, usize)>,
{
    G::from_iter((0..n).zip((0..n).cycle().skip(1)))
}

/// Returns a transitive tournament graph with `n` nodes.
pub fn transitive_tournament<G>(n: usize) -> G
where
    G: FromIterator<(usize, usize)>,
{
    G::from_iter((0..n).flat_map(|u| (u..n).map(move |v| (u, v))))
}

/// Returns the complete digraph on `n` nodes.
pub fn complete_digraph<G>(n: usize) -> G
where
    G: FromIterator<(usize, usize)>,
{
    G::from_iter(
        (0..n)
            .flat_map(|u| (0..n).map(move |v| (u, v)))
            .filter(|(a, b)| a != b),
    )
}
