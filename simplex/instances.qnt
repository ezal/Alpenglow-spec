module simplex_2_parties {
  import statemachine(
    CORRECT = Set("p1", "p2"),
    BYZANTINE = Set("b1"),
    F = 1,
    P = 1,
    POWER = Map("p1" -> 1, "p2" -> 4, "b1" -> 1),
    MAX_VIEW = 2,
    LEADER = Map(0 -> "p1", 1 -> "p2", 2 -> "b1"),
    VALUES = Set(1, 2),
    MAX_COUNTER = 20,
    byzNetworkMsgs = Set(),  // Byzantine is silent
  ).* from "./statemachine"


  run fast_agree_in_view_0 =
    init
    .then(propose("p1"))
    .then(voteOnSomeProposal("p1"))
    .then(voteOnSomeProposal("p2"))
    .then(takeDecision("p1"))
    .then(takeDecision("p2"))
    .expect(allCorrectDecided)

  // If "p1" does not participate in voting, a (slow) decision can still be made
  run slow_agree_in_view_0 =
    init
    .then(propose("p1"))
    .then(voteOnSomeProposal("p2"))
    .then(sendFinal("p2"))
    .then(takeDecision("p1"))
    .then(takeDecision("p2"))
    .expect(allCorrectDecided)

  // decide in view 1 due to no proposal in view 0
  run view_change_due_to_timeout =
    init
    .then(voteTimeout("p2"))
    .then(finalTimeout("p2"))
    .then(moveToNextView("p2"))
    .then(propose("p2"))
    .then(voteTimeout("p1"))
    .then(finalTimeout("p1"))
    .then(moveToNextView("p1"))
    .then(voteOnSomeProposal("p1"))
    .then(voteOnSomeProposal("p2"))
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
    MAX_VIEW = 2,
    LEADER = Map(0 -> "p1", 1 -> "p2", 2 -> "b1"),
    VALUES = Set(1, 2),
    MAX_COUNTER = 20,
    byzNetworkMsgs = Set(),  // Byzantine is silent
  ).* from "./statemachine"


  run fast_agree_in_view_0 =
    init
    .then(propose("p1"))
    .then(voteOnSomeProposal("p1"))
    .then(voteOnSomeProposal("p2"))
    .then(takeDecision("p1"))
    .then(takeDecision("p2"))
    .then(takeDecision("p3"))
    .expect(allCorrectDecided)

  // Take a (slow) decision with "p2" and "p3"
  run slow_agree_in_view_0 =
    init
    .then(propose("p1"))
    .then(voteOnSomeProposal("p2"))
    .then(voteOnSomeProposal("p3"))
    .then(sendFinal("p2"))
    .then(sendFinal("p3"))
    .then(takeDecision("p1"))
    .then(takeDecision("p2"))
    .then(takeDecision("p3"))
    .expect(allCorrectDecided)

  // decide in view 1 due to no proposal in view 0
  run view_change_due_to_timeout =
    init
    .then(voteTimeout("p2"))  // that's already a Fast-Cert(0,bot)
    .then(finalTimeout("p2"))
    .then(finalTimeout("p1")) // and now also a Slow-Cert(0,bot)
    .then(moveToNextView("p2")).then(propose("p2"))
    .then(voteTimeout("p1"))
    .then(moveToNextView("p1"))
    .then(voteOnSomeProposal("p1"))
    .then(voteOnSomeProposal("p2"))
    .then(takeDecision("p1"))
    .then(takeDecision("p2"))
    .then(voteTimeout("p3"))
    .then(finalTimeout("p3"))
    .then(moveToNextView("p3"))
    .then(takeDecision("p3"))
    .expect(allCorrectDecided)

  // scenarios with Fast-Cert re-proposal
  run view_change_and_repropose =
    val v = 1
    init
    .then(proposeValueNoCert("p1", v))
    .then(voteTimeout("p1"))
    .then(finalTimeout("p1"))
    .then(voteOnSomeProposal("p2")) // already a Fast-Cert(0,v)
    .then(finalTimeout("p2")) // and now also a Slow-Cert(0,bot)
    .then(moveToNextView("p2"))
    .then(proposeWithXCert("p2",FastCert({view:0, value:v})))
    .then(moveToNextView("p1"))
    .then(voteOnSomeProposal("p1"))
    .then(voteOnSomeProposal("p2"))
    .then(takeDecision("p1"))
    .then(takeDecision("p2"))
    .then(voteTimeout("p3"))
    .then(finalTimeout("p3"))
    .then(moveToNextView("p3"))
    .then(takeDecision("p3"))
    .expect(allCorrectDecided)

  // scenarios with Slow-Cert re-proposal
  run view_change_and_slow_cert_repropose =
    init
    .then(propose("p1"))
    .then(voteOnSomeProposal("p1"))
    .then(finalTimeout("p1"))
    .then(voteOnSomeProposal("p2"))
    .then(finalTimeout("p2"))
    .then(moveToNextView("p2")).then(propose("p2"))
    .then(moveToNextView("p1"))
    .then(voteOnSomeProposal("p1"))
    .then(voteOnSomeProposal("p2"))
    .then(takeDecision("p1"))
    .then(takeDecision("p2"))
    .then(voteTimeout("p3"))
    .then(finalTimeout("p3"))
    .then(moveToNextView("p3"))
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
    CORRECT = Set("p1", "p2", "p3"),
    BYZANTINE = byzProcesses,
    F = 1,
    P = 1,
    POWER = Map("b1" -> 2, "p1" -> 1, "p2" -> 1, "p3" -> 2),
    MAX_VIEW = maxView,
    LEADER = Map(0 -> "b1", 1 -> "p2", 2 -> "p1", 3 -> "p3"),
    VALUES = proposalValues,
    MAX_COUNTER = 20, 
    byzNetworkMsgs = byzMsgs,
  ).* from "./statemachine"

  pure val proposalView0Value1 = {msg: ProposeMsg({ view: 0, value: 1, cert: NoCert}), sender: "b1"}
  pure val proposalView0Value2 = {msg: ProposeMsg({ view: 0, value: 2, cert: NoCert}), sender: "b1"}
  pure val proposalView1Value2 = {msg: ProposeMsg({ view: 1, value: 2, cert: FastCert({view:0, value:2}) }), sender: "p2"}

  run agreement_failure =
    init
    .then(voteOnProposal("p1", proposalView0Value1))
    .then(voteOnProposal("p3", proposalView0Value1))
    .then(takeDecisionOn("p1", 1))
    .then(voteOnProposal("p2", proposalView0Value2))
    // so for now there is Fast-Cert(0,2)
    .then(finalTimeout("p2"))
    .then(finalTimeout("p3"))
    // there is now also a Slow-Cert(0,bot)
    .then(moveToNextView("p2"))
    .then(proposeWithXCert("p2", FastCert({view:0, value:2})))
    .expect(proposalView1Value2.in(s.msgBuffer))
    .then(moveToNextView("p3"))
    .then(voteOnSomeProposal("p2"))
    .then(voteOnSomeProposal("p3"))
    // we now have a Slow-Cert(2,1) 
    .then(sendFinal("p2"))
    .then(sendFinal("p3"))
    .then(takeDecision("p2")) // different decision due to byz msg
    .expect(not(agreement))
}
