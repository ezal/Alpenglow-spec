module simplex_2_parties {
  import statemachine(
    CORRECT = Set("p1", "p2"),
    BYZANTINE = Set("b1"),
    F = 1,
    P = 1,
    power = Map("p1" -> 1, "p2" -> 4, "b1" -> 1),
    proposalValues = Set(1, 2),
    maxCounter = 20,
    maxView = 2,
  ).* from "./statemachine"


  run fast_agree_in_view_0 =
    init
    .then(proposeValueAtViewZero("p1", 1))
    .then(voteOnProposal("p1"))
    .then(voteOnProposal("p2"))
    .then(takeDecisionOn("p1", 1))
    .then(takeDecisionOn("p2", 1))
    .expect(allCorrectDecided)

  // If "p1" does not participate in voting, a (slow) decision can still be made
  run slow_agree_in_view_0 =
    init
    .then(proposeAtViewZero("p1"))
    .then(voteOnProposal("p2"))
    .then(sendFinal("p2"))
    .then(takeDecision("p1"))
    .then(takeDecision("p2"))
    .expect(allCorrectDecided)

  // TODO: decide in view 1 due to timeouts in view 0
  // run view_change_due_to_timeout =
  //   .then(voteTimeout("p1")))
  //   .then(...)
}

module simplex_5_parties_1_byz {
  import statemachine(
    CORRECT = Set("p1", "p2", "p3", "p4"),
    BYZANTINE = Set("b1"),
    F = 1,
    P = 1,
    power = Set("p1", "p2", "p3", "p4", "b1").mapBy(_ => 1),
    proposalValues = Set(1, 2),
  ).* from "./statemachine"
}
