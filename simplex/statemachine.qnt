/**
 * State machine for Simplex consensus (2-round and 3-round BFT)
 * Based on https://decentralizedthoughts.github.io/2025-07-29-2-round-3-round-simplex/
 */

module statemachine {
  import basicSpells.* from "./basicSpells"
  import simplex.* from "./simplex"
  export simplex.*

  /// This is all the information of the global state
  type System = {
    // The local state of each process
    localStates: ProcessID -> LocalState,

    // Messages sent so far, a.k.a. the message soup
    msgBuffer: Set[NetworkMsg],

    // Decided values
    // TODO: this could also be directly obtained from the localStates...
    decisions: ProcessID -> Option[Value],
  }

  /// Interface consensus algorithm / state machine: how consensus algorithm effects the environment
  pure def applyEffect(sys: System, pid: ProcessID, res: Result): System =
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
    s' = applyEffect(s, id, processInput(s.localStates.get(id), input)),
    counter' = counter + 1,
  }


  //
  //
  // State Machine
  //
  //

  var s: System

  var counter: int // Required for bounded model checking

  /// All possible messages that Byzantine processes can send
  pure val byzMessages =
    proposalValues.union(Set(BOTTOM)).fold(Set(), (acc, value) =>
      // Consider views 0 to 3
      0.to(3).fold(acc, (acc2, view) =>
        acc2.union(Set(
          CertMsg(VoteMsg({ view: view, value: value })),
          CertMsg(FinalMsg({ view: view, value: value }))
        ))
      )
    )

  /// All votes that can be sent by the Byzantine processes
  pure val byzNetworkMsgs =
    byzantine.fold(Set(), (acc, sender) =>
      byzMessages.fold(acc, (acc2, msg) =>
        acc2.union(Set({ sender: sender, msg: msg }))
      )
    )

  /// all the messages that could be received, i.e., the ones sent by correct processes
  /// and the ones that byzantine processes may send
  val allNetworkMsgs = s.msgBuffer.union(byzNetworkMsgs)

  /// All possible values that can be proposed
  const proposalValues: Set[Value]

  action init = all {
    s' = {
      localStates: correct.mapBy(_ => {
        view: 0,
        proposed: false,
        voted: false,
        sentFinal: false,
        decided: None,
        highestCert: NoCert,
        seenMsgs: Set()
      }),
      msgBuffer: Set(),
      decisions: correct.mapBy(_ => None),
    },
    counter' = 0,
  }

  /// Correct process receives a message
  action receiveMessage(u: ProcessID, msg: NetworkMsg): bool = all {
    u.in(correct),
    val input = MessageInput(msg)
    applyInput(u, input)
  }

  /// Leader 'u' proposes a value (Rule 1)
  action sendProposal(u: ProcessID): bool = all {
    u.in(correct),
    not(s.localStates.get(u).proposed),
    isLeader(u, s.localStates.get(u).view),
    // TODO: we could just choose any not-yet-proposed value
    nondet value = proposalValues.oneOf()
    val input = ProposeInput(value)
    applyInput(u, input)
  }

  /// Process Vote time-out
  action voteTimeout(u: ProcessID): bool = all {
    u.in(correct),
    val input = VoteTimeoutInput(s.localStates.get(u).view)
    applyInput(u, input)
  }

  /// Process Final time-out
  action finalTimeout(u: ProcessID): bool = all {
    u.in(correct),
    val input = FinalTimeoutInput(s.localStates.get(u).view)
    applyInput(u, input)
  }

  // TODO: remove after checking that this code is not useful
  /// Move to next view with appropriate certificate
  // action moveToNextView(u: ProcessID): bool = all {
  //   u.in(correct),
  //   s.decisions.get(u) == None,  // Haven't decided yet
  //   val ls = s.localStates.get(u)
  //   val currentView = ls.view
  //   val msgs = allNetworkMsgs

  //   // Find the highest certificate from current or previous views
  //   val values = proposalValues.union(Set(BOTTOM))
  //   val certs = values.fold(Set(), (acc, value) =>
  //     0.to(currentView).fold(acc, (acc2, view) =>
  //       val votes = countVotes(msgs, view, value).size()
  //       val res =
  //         if (votes >= n - f - p and value != BOTTOM) {
  //           acc2.union(Set(SlowCert({ view: view, value: value })))
  //         } else if (votes >= n - 2*f - p) {
  //           acc2.union(Set(FastCert({ view: view, value: value })))
  //         } else {
  //           acc2
  //         }
  //       val finals = countFinals(msgs, view, value).size()
  //       if (finals >= n - f - p and value == BOTTOM) {
  //         res.union(Set(SlowCert({ view: view, value: value })))
  //       } else {
  //         res
  //       }
  //     )
  //   )

  //   // TODO: not checked further
  //   val highestCert = certs.fold(NoCert, (best, cert) =>
  //     if (higherPriority(cert, best)) cert else best
  //   )

  //   all {
  //     s' = { ...s,
  //       localStates: s.localStates.set(u, {
  //         view: currentView + 1,
  //         voted: false,
  //         sentFinal: false,
  //         decided: None,
  //         highestCert: highestCert,
  //         seenMsgs: ls.seenMsgs,
  //       })
  //     },
  //     counter' = counter + 1,
  //   }
  // }


  /// Main step action
  action step = all {
    counter < 20,  // Bound for model checking
    any {
      nondet u = correct.oneOf()
      any {
        sendProposal(u),
        nondet msg = allNetworkMsgs.oneOf()
        receiveMessage(u, msg),
        voteTimeout(u),
        finalTimeout(u)
      }
    }
  }

  //
  //
  // Invariants and Properties
  //
  //

  /// Agreement: no two correct processes decide different values
  val agreement =
    correct.forall(p1 =>
      correct.forall(p2 =>
        (s.decisions.get(p1) != None and s.decisions.get(p2) != None) implies
        (s.decisions.get(p1) == s.decisions.get(p2))
      )
    )
}
