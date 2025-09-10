/**
 * State machine for Simplex consensus (2-round and 3-round BFT)
 * Based on https://decentralizedthoughts.github.io/2025-07-29-2-round-3-round-simplex/
 */

module statemachine {
  import basicSpells.* from "./basicSpells"
  import simplex.* from "./simplex"
  export simplex.*

  /// This is all the information of the global state
  type Environment = {
    // The local state of each process
    localStates: ProcessID -> LocalState,

    // Messages sent so far, a.k.a. the message soup
    msgBuffer: Set[NetworkMsg],

    // Decided values
    // This could be obtained from the localStates...
    decisions: ProcessID -> Option[Value],
  }

  /// Interface consensus algorithm / state machine: how consensus algorithm effects the environment
  pure def applyEffect(env: Environment, v: ProcessID, res: Result): Environment =
    // update the state of the process
    val new = { ... env, localStates: env.localStates.set(v, res.post) }
    // update the message buffer and decisions
    res.output.fold(new, (s, o) =>
      match o {
        | Broadcast(msg) =>
          val nm = { sender: v, msg: msg }
          { ...s, msgBuffer: s.msgBuffer.union(Set(nm)) }
        | Decide(value) =>
          { ...s, decisions: s.decisions.set(v, Some(value)) }
      })

  //
  //
  // State Machine
  //
  //

  var s: Environment

  var counter: int // Required for bounded model checking

  /// All possible messages that Byzantine processes can send
  pure val byzMessages =
    proposalValues.union(Set(BOTTOM)).fold(Set(), (acc, value) =>
      // Consider views 0 to 3
      0.to(3).fold(acc, (acc2, view) =>
        acc2.union(Set(
          VoteMsg({ view: view, value: value }),
          FinalMsg({ view: view, value: value })
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
  val allMessages = s.msgBuffer.union(byzNetworkMsgs)

  /// All possible values that can be proposed
  const proposalValues: Set[Value]

  action init = all {
    s' = {
      localStates: correct.mapBy(_ => {
        view: 0,
        voted: false,
        sentFinal: false,
        decided: None,
        highestCert: NoCert,
        timer: 0,
      }),
      msgBuffer: Set(),
      decisions: correct.mapBy(_ => None),
    },
    counter' = 0,
  }

  /// Process receives a proposal
  action receiveProposal(v: ProcessID, view: View, value: Value, cert: Certificate): bool = all {
    v.in(correct),
    view == s.localStates.get(v).view,
    // leader(view) != v,  // Only non-leaders process proposals // EZ: why!?
    val input = ProposeInput({ view: view, value: value, cert: cert })
    processInput(v, input)
  }

  /// Leader 'u' proposes a value (Rule 1)
  /// EZ: I don't get it; also, what is the difference with receiveProposal?
  action leaderProposes(u: ProcessID): bool = all {
    u.in(correct),
    leader(s.localStates.get(u).view) == u,
    not(s.localStates.get(u).voted),
    // Choose value based on highest certificate
    // EZ: TODO
    val highestCertValue = certValue(s.localStates.get(u).highestCert)
    val values = if (highestCertValue != BOTTOM) { Set(highestCertValue) } else { proposalValues }
    nondet value = values.oneOf()
    val input = ProposeInput({
      view: s.localStates.get(u).view,
      value: value,
      cert: s.localStates.get(u).highestCert
    })
    processInput(u, input)
  }

  /// Process Vote time-out
  action voteTimeout(u: ProcessID): bool = all {
    u.in(correct),
    val input = VoteTimeoutInput({ view: s.localStates.get(u).view })
    processInput(u, input)
  }

  /// Process Final time-out
  action finalTimeout(u: ProcessID): bool = all {
    u.in(correct),
    val input = FinalTimeoutInput({ view: s.localStates.get(u).view })
    processInput(u, input)
  }

  /// Process receives a vote and checks for decisions
  // EZ: I don't get it, this does not make sense
  action receiveVote(u: ProcessID): bool = all {
    u.in(correct),
    // Just trigger the final processing logic
    val input = VoteInput({ view: s.localStates.get(u).view, value: 0 })
    processInput(u, input)
  }

  /// Process receives a final message and checks for decisions
  // EZ: I don't get it, this does not make sense
  action receiveFinal(u: ProcessID): bool = all {
    u.in(correct),
    // Just trigger the final processing logic
    val input = FinalInput({ view: s.localStates.get(u).view, value: 0 })
    processInput(u, input)
  }

  /// Move to next view with appropriate certificate
  action moveToNextView(u: ProcessID): bool = all {
    u.in(correct),
    s.decisions.get(u) == None,  // Haven't decided yet
    val currentView = s.localStates.get(u).view
    val msgs = allMessages

    // Find the highest certificate from current or previous views
    val values = proposalValues.union(Set(BOTTOM))
    val certs = values.fold(Set(), (acc, value) =>
      0.to(currentView).fold(acc, (acc2, view) =>
        val votes = countVotes(msgs, view, value).size()
        val res =
          if (votes >= n - f - p and value != BOTTOM) {
            acc2.union(Set(SlowCert({ view: view, value: value })))
          } else if (votes >= n - 2*f - p) {
            acc2.union(Set(FastCert({ view: view, value: value })))
          } else {
            acc2
          }
        val finals = countFinals(msgs, view, value).size()
        if (finals >= n - f - p and value == BOTTOM) {
          res.union(Set(SlowCert({ view: view, value: value })))
        } else {
          res
        }
      )
    )

    // EZ: not checked further
    val highestCert = certs.fold(NoCert, (best, cert) =>
      if (higherPriority(cert, best)) cert else best
    )

    all {
      s' = { ...s,
        localStates: s.localStates.set(u, {
          view: currentView + 1,
          voted: false,
          sentFinal: false,
          decided: None,
          highestCert: highestCert,
          timer: 0,
        })
      },
      counter' = counter + 1,
    }
  }

  //
  // auxiliary functions for actions
  //

  action processInput(id: ProcessID, input: ConsensusInput): bool = all {
    s' = applyEffect(s, id, consensus(s.localStates.get(id), input, allMessages)),
    counter' = counter + 1,
  }

  /// Main step action
  action step = all {
    counter < 20,  // Bound for model checking
    any {
      nondet u = correct.oneOf()
      any {
        leaderProposes(u),
        nondet value = proposalValues.oneOf()
        receiveProposal(u, s.localStates.get(u).view, value, NoCert),
        voteTimeout(u),
        finalTimeout(u),
        receiveVote(u),
        receiveFinal(u),
        moveToNextView(u),
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

  /// Validity: if all correct processes propose the same value v, then v is decided
  val validity =
    proposalValues.forall(v =>
      // If all initial proposals are v
      (correct.forall(p =>
        s.localStates.get(p).view == 0 implies
        (leader(0) == p implies s.localStates.get(p).highestCert == NoCert)
      )) implies
      // Then any decision is v
      (correct.forall(p =>
        s.decisions.get(p) != None implies s.decisions.get(p) == Some(v)
      ))
    )

  /// Fast termination: processes decide in 2 rounds when at most p failures
  val fastTerminationWitness =
    correct.exists(p =>
      s.decisions.get(p) != None and s.localStates.get(p).view <= 1
    )

  /// Slow termination: processes decide in 3 rounds when at most f failures
  val slowTerminationWitness =
    correct.exists(p =>
      s.decisions.get(p) != None and s.localStates.get(p).view <= 2
    )

  /// No decision witness
  val noDecisionWitness =
    correct.forall(p => s.decisions.get(p) == None)
}

module simplex_4_nodes {
  import statemachine(
    correct = Set("p1", "p2", "p3", "p4"),
    byzantine = Set(),
    power = Set("p1", "p2", "p3", "p4").mapBy(_ => 1),
    p = 0,
    proposalValues = Set(1, 2),
  ).*
}

module simplex_5_nodes_1_byz {
  import statemachine(
    correct = Set("p1", "p2", "p3", "p4"),
    byzantine = Set("b1"),
    power = Set("p1", "p2", "p3", "p4", "b1").mapBy(_ => 1),
    p = 1,
    proposalValues = Set(1, 2),
  ).*
}