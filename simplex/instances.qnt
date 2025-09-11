module simplex_2_parties {
  import statemachine(
    correct = Set("p1", "p2"),
    byzantine = Set("b1"),
    power = Map("p1" -> 1, "p2" -> 3, "b1" -> 1),
    f = 1,
    p = 1,
    proposalValues = Set(1, 2)
  ).* from "./statemachine"

  // run agree_in_view_2 =
  //   init
  //   .then(voteTimeout("p1"))
  //   .then(receiveMessage("p1", { msg: CertMsg(VoteMsg({ value: -1, view: 0 })), sender: "p1" }))
  //   .then(...)

  run agree_in_view_1 =
    init
    .then(sendProposal("p1"))
    .then(receiveMessage("p1", { msg: ProposeMsg({ cert: Set(), value: 2, view: 0 }), sender: "p1" }))
    .then(receiveMessage("p2", { msg: ProposeMsg({ cert: Set(), value: 2, view: 0 }), sender: "p1" }))
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
