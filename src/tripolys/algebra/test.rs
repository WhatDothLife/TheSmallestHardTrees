use crate::algebra::Polymorphisms;
use crate::graph::generators::triad;
use crate::graph::AdjList;

#[test]
fn test_np_hard() {
    let triad: AdjList<_> = triad("01001111,1010000,011000").unwrap();
    let graph = AdjList::from_edges([
        (1, 0),
        (1, 2),
        (2, 3),
        (4, 3),
        (5, 4),
        (6, 5),
        (7, 0),
        (8, 7),
        (8, 9),
        (9, 10),
        (10, 11),
        (11, 12),
        (13, 0),
        (13, 14),
        (15, 14),
        (15, 18),
        (18, 19),
        (16, 15),
        (17, 16),
    ]);
    let wnu2 = Polymorphisms::wnu(2);
    let wnu2_exists = wnu2.exist(&graph) || wnu2.exist(&triad);
    assert!(!wnu2_exists);

    let kmm = Polymorphisms::kmm();
    let kmm_exists = kmm.exist(&graph) || kmm.exist(&triad);
    assert!(!kmm_exists);
}

#[test]
fn test_not_solved_by_ac() {
    let graph = AdjList::from_edges([
        (0, 1),
        (1, 2),
        (2, 3),
        (4, 5),
        (5, 6),
        (6, 7),
        (8, 9),
        (9, 10),
        (11, 12),
        (12, 13),
        (13, 14),
        (15, 16),
        (16, 17),
        (17, 18),
        (8, 6),
        (9, 3),
        (15, 9),
        (12, 10),
    ]);
    let wnu2_exists = Polymorphisms::wnu(2).exist(&graph);
    assert!(!wnu2_exists);

    let majority_exists = Polymorphisms::majority().exist(&graph);
    assert!(majority_exists);
}

#[test]
fn test_not_known_to_be_in_nl() {
    let graph = AdjList::from_edges([
        (0, 1),
        (1, 2),
        (2, 3),
        (3, 4),
        (0, 5),
        (5, 6),
        (7, 8),
        (8, 5),
        (8, 9),
        (9, 10),
        (10, 11),
        (12, 13),
        (13, 14),
        (14, 15),
        (13, 6),
    ]);
    let majority = Polymorphisms::majority().exist(&graph);
    assert!(!majority);

    let homck2 = Polymorphisms::hobby_mckenzie(2).exist(&graph);
    assert!(homck2);

    let kk5 = Polymorphisms::kearnes_kiss(5).exist(&graph);
    assert!(kk5);
}

#[test]
fn test_nl_hard() {
    let graph = AdjList::from_edges([
        (0, 1),
        (1, 2),
        (3, 2),
        (3, 4),
        (4, 5),
        (6, 0),
        (6, 7),
        (8, 7),
        (9, 8),
        (8, 10),
        (10, 11),
    ]);
    let hami = Polymorphisms::hagemann_mitschke(8).exist(&graph);
    assert!(hami);
}
