/**
 * State machine for Simplex consensus (2-round and 3-round BFT)
 * Based on https://decentralizedthoughts.github.io/2025-07-29-2-round-3-round-simplex/
 */

module statemachine {
  import basicSpells.* from "./basicSpells"
  import simplex.* from "./simplex"
  export simplex.*

  const MAX_COUNTER: int  // Bound for model checking

  const MAX_VIEW: int

  /// This is all the information of the global state
  type System = {
    // The local state of each process
    localStates: ProcessID -> LocalState,

    // Messages sent so far, a.k.a. the message soup
    msgBuffer: Set[NetworkMsg],

    // Decided values
    // TODO: this could also be directly obtained from the localStates...
    // Moreover, not sure this is needed at all
    decisions: ProcessID -> Option[Value],
  }

  /// Interface consensus algorithm / state machine: how consensus algorithm effects the environment
  pure def applyResult(sys: System, pid: ProcessID, res: Result): System =
    // update the state of the process
    val new = { ... sys, localStates: sys.localStates.set(pid, res.post) }
    // update the message buffer and decisions
    res.output.fold(new, (acc_sys, output) =>
      match output {
        | Broadcast(msg) =>
          val newMsg = { sender: pid, msg: msg }
          { ...acc_sys, msgBuffer: acc_sys.msgBuffer.union(Set(newMsg)) }
        | Decide(value) =>
          { ...acc_sys, decisions: acc_sys.decisions.set(pid, Some(value)) }
      })

  action applyInput(id: ProcessID, input: ConsensusInput): bool = all {
    val res = processInput(s.localStates.get(id), input)
    s' = applyResult(s, id, res),
    counter' = counter + 1,
  }


  //// State Machine

  var s: System

  var counter: int // Required for bounded model checking

  pure def proposeMsgs(view: View, value: Value) : Set[Message] =
      0.to(view-1).fold(Set(ProposeMsg({ view: view, value: value, cert: NoCert })), (acc, v) =>
        acc.union(Set(
          ProposeMsg({ view: view, value: value, cert: FastCert({ view: v, value: value }) }),
          ProposeMsg({ view: view, value: value, cert: SlowCert({ view: v, value: value }) })))
      )

  /// All possible messages that Byzantine processes can send
  pure def byzMessages(sender: ProcessID, maxView: View, values: Set[Value]) : Set[Message] =
    values.fold(Set(), (acc, value) =>
      // Consider views 0 to mAX_VIEW
      0.to(maxView).fold(acc, (acc2, view) =>
        val proposals =
          if (sender.isLeader(view))
            proposeMsgs(view, value)
          else 
            Set()
        acc2.union(Set(
          VoteMsg({ view: view, value: value }),
          FinalMsg({ view: view, value: value })
        ).union(proposals))
      )
    )

  /// All the messages that can be sent by the Byzantine processes
  pure def allByzNetworkMsgs(byzantines: Set[ProcessID], maxView: View, values: Set[Value]) : Set[NetworkMsg] =
    byzantines.fold(Set(), (acc, sender) =>
      byzMessages(sender, maxView, values).fold(acc, (acc2, msg) =>
        acc2.union(Set({ sender: sender, msg: msg }))
      )
    )

  /// All messages actually made available to the Byzantine processes
  const byzNetworkMsgs : Set[NetworkMsg]

  /// All the messages that could be received, i.e., the ones sent by correct processes
  /// and the ones that byzantine processes may send
  val allNetworkMsgs = s.msgBuffer.union(byzNetworkMsgs)

  /// All possible values that can be proposed
  const VALUES: Set[Value]

  action init = all {
    s' = {
      localStates: CORRECT.mapBy(_ => {
        view: 0,
        proposed: false,
        voted: false,
        sentFinal: false,
        decided: None,
        highestCert: NoCert,
      }),
      msgBuffer: Set(),
      decisions: CORRECT.mapBy(_ => None),
    },
    counter' = 0,
  }

  // TODO: I think it would be cleaner to not have the `applyInput` inside specific actions,
  // but rather have the action functions just return the input, and then have a single `apply

  /// Process Vote time-out
  action voteTimeout(u: ProcessID): bool = all {
    u.in(CORRECT),
    val input = VoteTimeoutInput(s.localStates.get(u).view)
    applyInput(u, input)
  }

  /// Process Final time-out
  action finalTimeout(u: ProcessID): bool = all {
    u.in(CORRECT),
    val input = FinalTimeoutInput(s.localStates.get(u).view)
    applyInput(u, input)
  }

  /// 'u' moves to next view and proposes a value if it is the leader (Rules 8 and 1)
  action moveToNextViewAndMaybePropose(u: ProcessID): bool = all {
    u.in(CORRECT),
    s.decisions.get(u) == None,
    val ls = s.localStates.get(u)
    val msgs = allNetworkMsgs

    all {
      ls.view < MAX_VIEW,
      canIncreaseView(ls, msgs),
      // TODO: we could rather choose any not-yet-proposed value
      nondet value = VALUES.oneOf()
      val input = NextViewInput((u, value, msgs, VALUES))
      applyInput(u, input)
    }
  }

  /// 'u' moves to next view and proposes a value if it is the leader (Rules 8 and 1)
  action proposeValueAtViewZero(u: ProcessID, value: Value): bool = all {
    u.in(CORRECT),
    s.decisions.get(u) == None,  // Haven't decided yet
    val ls = s.localStates.get(u)
    all {
      ls.view == 0,
      not(ls.proposed),
      isLeader(u, ls.view),
      val res = propose(ls, value)
      s' = applyResult(s, u, res),
      counter' = counter + 1,
    }
  }

  action proposeAtViewZero(u: ProcessID): bool = all {
    // TODO: we could rather choose any not-yet-proposed value
    nondet value = VALUES.oneOf()
    proposeValueAtViewZero(u, value)
  }

  action takeDecisionOn(u: ProcessID, value: Value): bool = all {
    u.in(CORRECT),
    s.decisions.get(u) == None,
    val ls = s.localStates.get(u)
    val msgs = allNetworkMsgs
    all {
      canDecide(ls.view, value, msgs),
      s' = applyResult(s, u, decide(ls, value)),
      counter' = counter + 1,
    }
  }

  action takeDecision(u: ProcessID): bool = all {
    nondet value = VALUES.oneOf()
    takeDecisionOn(u, value)
  }

  /// Vote on a valid proposal (Rule 2)
  action voteOnProposal(u: ProcessID, proposeMsg: NetworkMsg): bool = all {
    u.in(CORRECT),
    s.decisions.get(u) == None,
    val ls = s.localStates.get(u)
    all {
      not(ls.voted),
      // TODO: do we indeed only accept the proposal in the current view? I think
      // this makes sense indeed, but it's not in the spec!
      // TODO: check invariant: all proposals come from the expected leaders
      isValidProposal(ls, proposeMsg, allNetworkMsgs),
      // TODO: update highestCert?? We should do that even if u has already voted, right?
      val res = {
        output: Set(Broadcast(VoteMsg({view: ls.view, value: getMsgValue(proposeMsg.msg)}))),
        post: { ...ls, voted: true }}
      s' = applyResult(s, u, res),
      counter' = counter + 1,
    }
  }

  action voteOnSomeProposal(u: ProcessID): bool = {
    val proposals = allNetworkMsgs.getProposals(s.localStates.get(u).view)
    all {
      proposals.size() > 0,
      nondet proposeMsg = proposals.oneOf()
      voteOnProposal(u, proposeMsg)
    }
  }

  // Send Final message if we have enough votes to (Rule 3)
  action sendFinal(u: ProcessID): bool = all {
    u.in(CORRECT),
    s.decisions.get(u) == None,
    val ls = s.localStates.get(u)
    all {
      not(ls.sentFinal),
      val values = slowCertValues(allNetworkMsgs, ls.view)
      all {
        values.size() > 0,
        assert(values.size() == 1),
        nondet value = values.oneOf()
        all {
          val res = sendFinalMsg(ls, value)
          s' = applyResult(s, u, res),
          counter' = counter + 1
        }
      }
    }
  }

  /// Main step action
  action step = all {
    counter < MAX_COUNTER,
    any {
      nondet u = CORRECT.oneOf()
      any {
        voteTimeout(u),
        finalTimeout(u),
        proposeAtViewZero(u),
        moveToNextViewAndMaybePropose(u),
        voteOnSomeProposal(u),
        sendFinal(u),
        takeDecision(u),
      }
    }
  }

  //// Invariants and Properties

  val allCorrectDecided = CORRECT.forall(p => s.decisions.get(p) != None)

  /// Agreement: no two correct processes decide different values
  val agreement =
    CORRECT.forall(p1 =>
      CORRECT.forall(p2 =>
        (s.decisions.get(p1) != None and s.decisions.get(p2) != None) implies
        (s.decisions.get(p1) == s.decisions.get(p2))
      )
    )
}
