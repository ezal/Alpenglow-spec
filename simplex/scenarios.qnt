module simplex_4_nodes {
  import statemachine(
    correct = Set("p1", "p2", "p3", "p4"),
    byzantine = Set(),
    power = Set("p1", "p2", "p3", "p4").mapBy(_ => 1),
    p = 0,
    proposalValues = Set(1, 2),
  ).* from "./statemachine"
}

module simplex_5_nodes_1_byz {
  import statemachine(
    correct = Set("p1", "p2", "p3", "p4"),
    byzantine = Set("b1"),
    power = Set("p1", "p2", "p3", "p4", "b1").mapBy(_ => 1),
    p = 1,
    proposalValues = Set(1, 2),
  ).* from "./statemachine"
}