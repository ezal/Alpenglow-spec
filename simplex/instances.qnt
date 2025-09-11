module simplex_4_parties {
  import statemachine(
    correct = Set("p1", "p2", "p3", "p4"),
    byzantine = Set(),
    power = Set("p1", "p2", "p3", "p4").mapBy(_ => 1),
    f = 0,
    p = 0,
    proposalValues = Set(1, 2),
  ).* from "./statemachine"
}

module simplex_5_parties_1_byz {
  import statemachine(
    correct = Set("p1", "p2", "p3", "p4"),
    byzantine = Set("b1"),
    power = Set("p1", "p2", "p3", "p4", "b1").mapBy(_ => 1),
    f = 1,
    p = 1,
    proposalValues = Set(1, 2),
  ).* from "./statemachine"
}