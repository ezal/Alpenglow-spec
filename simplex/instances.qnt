// byzNetworkMsgs =
//     BYZANTINE.fold(Set(), (acc, sender) =>
//       byzMessages.fold(acc, (acc2, msg) =>
//         acc2.union(Set({ sender: sender, msg: msg }))
//       )
//     )

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
    power = Map("p1" -> 2, "p2" -> 3, "p3" -> 1),
    proposalValues = Set(1, 2),
    maxCounter = 20,
    maxView = 2,
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
