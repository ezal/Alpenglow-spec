module simplex_2_parties {
  import statemachine(
    CORRECT = Set("p1", "p2"),
    BYZANTINE = Set("b1"),
    F = 1,
    P = 1,
    POWER = Map("p1" -> 1, "p2" -> 4, "b1" -> 1),
    VALUES = Set(1, 2),
    MAX_COUNTER = 20,
    MAX_VIEW = 2,
    byzNetworkMsgs = Set(),  // Byzantine is silent
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

  // decide in view 1 due to no proposal in view 0
  run view_change_due_to_timeout =
    init
    .then(voteTimeout("p2"))
    .then(finalTimeout("p2"))
    .then(moveToNextViewAndMaybePropose("p2"))
    .then(voteTimeout("p1"))
    .then(finalTimeout("p1"))
    .then(moveToNextViewAndMaybePropose("p1"))
    .then(voteOnProposal("p1"))
    .then(voteOnProposal("p2"))
    // Note: we don't know what value was proposed in view 1, so we can't use takeDecisionOn
    .then(takeDecision("p1"))
    .then(takeDecision("p2"))
    .expect(allCorrectDecided)

}

// This is similar to the above, but the power distribution has changed:
// "p2" cannot build a slow certificate alone (only a fast one)
module simplex_2_parties_bis {
  import statemachine(
    CORRECT = Set("p1", "p2", "p3"),
    BYZANTINE = Set(),
    F = 1,
    P = 1,
    POWER = Map("p1" -> 2, "p2" -> 3, "p3" -> 1),
    VALUES = Set(1, 2),
    MAX_COUNTER = 20,
    MAX_VIEW = 2,
    byzNetworkMsgs = Set(),  // Byzantine is silent
  ).* from "./statemachine"


  run fast_agree_in_view_0 =
    init
    .then(proposeValueAtViewZero("p1", 1))
    .then(voteOnProposal("p1"))
    .then(voteOnProposal("p2"))
    .then(takeDecisionOn("p1", 1))
    .then(takeDecisionOn("p2", 1))
    .then(takeDecisionOn("p3", 1))
    .expect(allCorrectDecided)

  // Take a (slow) decision with "p2" and "p3"
  run slow_agree_in_view_0 =
    init
    .then(proposeAtViewZero("p1"))
    .then(voteOnProposal("p2"))
    .then(voteOnProposal("p3"))
    .then(sendFinal("p2"))
    .then(sendFinal("p3"))
    .then(takeDecision("p1"))
    .then(takeDecision("p2"))
    .then(takeDecision("p3"))
    .expect(allCorrectDecided)

  // decide in view 1 due to no proposal in view 0
  run view_change_due_to_timeout =
    init
    .then(voteTimeout("p2"))
    .then(finalTimeout("p2"))
    .then(finalTimeout("p1"))
    .then(moveToNextViewAndMaybePropose("p2"))
    .then(voteTimeout("p1"))
    .then(moveToNextViewAndMaybePropose("p1"))
    .then(voteOnProposal("p1"))
    .then(voteOnProposal("p2"))
    .then(takeDecision("p1"))
    .then(takeDecision("p2"))
    .then(voteTimeout("p3"))
    .then(finalTimeout("p3"))
    .then(moveToNextViewAndMaybePropose("p3"))
    .then(takeDecision("p3"))
    .expect(allCorrectDecided)

  // scenarios with Fast-Cert re-proposal
  run view_change_and_repropose =
    init
    .then(proposeValueAtViewZero("p1", 1))
    .then(voteTimeout("p1"))
    .then(finalTimeout("p1"))
    .then(voteOnProposal("p2"))
    .then(finalTimeout("p2"))
    .then(moveToNextViewAndMaybePropose("p2"))
    .then(moveToNextViewAndMaybePropose("p1"))
    .then(voteOnProposal("p1"))
    .then(voteOnProposal("p2"))
    .then(takeDecision("p1"))
    .then(takeDecision("p2"))
    .then(voteTimeout("p3"))
    .then(finalTimeout("p3"))
    .then(moveToNextViewAndMaybePropose("p3"))
    .then(takeDecision("p3"))
    .expect(allCorrectDecided)

  // scenarios with Slow-Cert re-proposal
  run view_change_and_slow_cert_repropose =
    init
    .then(proposeValueAtViewZero("p1", 1))
    .then(voteOnProposal("p1"))
    .then(finalTimeout("p1"))
    .then(voteOnProposal("p2"))
    .then(finalTimeout("p2"))
    .then(moveToNextViewAndMaybePropose("p2"))
    .then(moveToNextViewAndMaybePropose("p1"))
    .then(voteOnProposal("p1"))
    .then(voteOnProposal("p2"))
    .then(takeDecision("p1"))
    .then(takeDecision("p2"))
    .then(voteTimeout("p3"))
    .then(finalTimeout("p3"))
    .then(moveToNextViewAndMaybePropose("p3"))
    .then(takeDecision("p3"))
    .expect(allCorrectDecided)
}

module byz_messages {
  import statemachine.* from "./statemachine"
  pure val maxView = 2
  pure val proposalValues = Set(1, 2)
  pure val byzProcesses = Set("b1")
  pure val byzMsgs = allByzNetworkMsgs(Set("b1"), maxView, proposalValues)
}

module simplex_2_byz {
  import byz_messages.*
  import statemachine(
    CORRECT = Set("p1", "p2"),
    BYZANTINE = byzProcesses,
    F = 1,
    P = 1,
    POWER = Map("p1" -> 2, "p2" -> 2, "b1" -> 2),
    VALUES = proposalValues,
    MAX_COUNTER = 20,
    MAX_VIEW = maxView,
    byzNetworkMsgs = byzMsgs,
  ).* from "./statemachine"
}
