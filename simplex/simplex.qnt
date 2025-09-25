/**
 * Specification of 2-round and 3-round BFT (Simplex)
 * Based on https://decentralizedthoughts.github.io/2025-07-29-2-round-3-round-simplex/
 *
 * This is a one-shot consensus protocol with integrated fast and slow paths.
 * - Fast path: 2 rounds with n-p votes when at most p failures
 * - Slow path: 3 rounds with n-f-p votes when at most f failures
 */

/****************************************************
Meaning of TODO:
- something needs to be double-checked
- something seems to be missing (but can be added later; it should be discovered when checking some properties)
- something can improved, mostly for clarity/completeness

Meaning of FIXME:
- something does not make sense and needs to be fixed

Main observed issues:
#4 Rule 7 is missing

For some of the items, we could first detect some issues and then fix them
*****************************************************/


module simplex {
  import basicSpells.* from "./basicSpells"

  type ProcessID = str

  type View = int

  type Value = int

  /// Special bottom value representing no decision/timeout
  pure val BOTTOM = -1

  const CORRECT: Set[ProcessID]
  const BYZANTINE: Set[ProcessID]
  pure val PROCESSES = CORRECT.union(BYZANTINE)

  const POWER: ProcessID -> int

  /// Number of processes (total voting power)
  pure def sumPower(s: Set[ProcessID]): int =
    s.fold(0, (acc, x) => acc + POWER.get(x))

  pure val N = sumPower(PROCESSES)

  /// Slow-path parameter; also maximum power of Byzantines
  const F: int

  /// Fast-path parameter
  const P: int

  /// Constraints on parameters
  assume parameterConstraints = and {
    N >= 3 * F + 2 * P + 1,
    F >= 0,
    P >= 0,
    P <= F,
    // sumPower(byzantine) <= F,
  }

  const LEADER: View -> ProcessID

  /// Check if process is the leader of a view
  pure def isLeader(proc: ProcessID, view: View): bool = {
    // echo(proc + " is leader of view " + view + ": " + (leader(view) == proc))
    // assert(view.in(LEADER.keys()))
    LEADER.get(view) == proc
  }

  /// Certificate types
  type Certificate =
    | FastCert({ view: View, value: Value })
    | SlowCert({ view: View, value: Value })
    | NoCert

  /// Message types
  type Message =
    | ProposeMsg({ view: View, value: Value, cert: Certificate })
    | VoteMsg({ view: View, value: Value })
    | FinalMsg({ view: View, value: Value })

  /// Messages on the network carry the sender
  type NetworkMsg = {
    sender: ProcessID,
    msg: Message,
  }




  pure def getMsgValue(msg: Message): Value = {
    match msg {
      | ProposeMsg(m) => m.value
      | VoteMsg(m) => m.value
      | FinalMsg(m) => m.value
    }
  }

  pure def getProposals(msgs: Set[NetworkMsg], view: View): Set[NetworkMsg] = {
    msgs
      .filter(m => match m.msg {
        | ProposeMsg(propose) => propose.view == view
        | _ => false
      })
  }

  /// Return the Vote messages for a given view and value from a set of messages
  pure def getVotes(msgs: Set[NetworkMsg], view: View, value: Value): Set[NetworkMsg] = {
    msgs
      .filter(m => match m.msg {
        | VoteMsg(vote) => vote.view == view and vote.value == value
        | _ => false
      })
  }

  pure def getVotesPower(msgs: Set[NetworkMsg], view: View, value: Value): int =
    getVotes(msgs, view, value).map(m => m.sender).sumPower()

  /// Return the senders of Vote messages for a given view and value from a set of messages
  pure def getVoteSenders(msgs: Set[NetworkMsg], view: View, value: Value): Set[ProcessID] =
    getVotes(msgs,view,value).map(m => m.sender)

  /// Return the Final messages for a given view and value from a set of messages
  pure def getFinals(msgs: Set[NetworkMsg], view: View, value: Value): Set[NetworkMsg] = {
    msgs
      .filter(m => match m.msg {
        | FinalMsg(final) => final.view == view and final.value == value
        | _ => false
      })
  }

  /// Return the senders of Final messages for a given view and value from a set of messages
  pure def getFinalSenders(msgs: Set[NetworkMsg], view: View, value: Value): Set[ProcessID] =
    getFinals(msgs,view,value).map(m => m.sender)

  pure def getFinalsPower(msgs: Set[NetworkMsg], view: View, value: Value): int =
    getFinals(msgs, view, value).map(m => m.sender).sumPower()

  /// Check if a certificate is valid
  pure def isValidCert(cert: Certificate, msgs: Set[NetworkMsg]): bool = {
    match cert {
      | FastCert(c) => getVotesPower(msgs, c.view, c.value) >= N - 2*F - P
      | SlowCert(c) =>
        if (c.value != BOTTOM) {
          getVotesPower(msgs, c.view, c.value) >= N - F - P
        } else {
          getFinalsPower(msgs, c.view, c.value) >= N - F - P
        }
      | NoCert => true
    }
  }

  /// Compare certificates by priority (higher view wins, Fast < Slow for same view)
  pure def higherPriority(cert1: Certificate, cert2: Certificate): bool = {
    match cert1 {
      | NoCert => match cert2 {
          | NoCert => true
          | FastCert(c2) => false
          | SlowCert(c2) => false
        }
      | FastCert(c1) => match cert2 {
          | NoCert => true
          | FastCert(c2) => c1.view >= c2.view
          | SlowCert(c2) => c1.view > c2.view
        }
      | SlowCert(c1) => match cert2 {
          | NoCert => true
          | FastCert(c2) => c1.view >= c2.view
          | SlowCert(c2) => c1.view >= c2.view
        }
    }
  }

  pure def findHighestCert(highestView: View, msgs: Set[NetworkMsg], values: Set[Value]) : Certificate = {
    val certs = values.fold(Set(), (acc, value) =>
      0.to(highestView).fold(acc, (acc2, view) =>
        val votesPower = getVotesPower(msgs, view, value)
        val res =
          if (votesPower >= N - F - P and value != BOTTOM) {
            acc2.union(Set(SlowCert({ view: view, value: value })))
          } else if (votesPower >= N - 2*F - P) {
            acc2.union(Set(FastCert({ view: view, value: value })))
          } else {
            acc2
          }
        val finalsPower = getFinalsPower(msgs, view, value)
        if (finalsPower >= N - F - P and value == BOTTOM) {
          res.union(Set(SlowCert({ view: view, value: value })))
        } else {
          res
        }
      )
    )

    certs.fold(NoCert, (best, cert) =>
      if (higherPriority(cert, best)) cert else best
    )
  }

  /// Get the value from a certificate
  pure def certValue(cert: Certificate): Value = {
    match cert {
      | FastCert(c) => c.value
      | SlowCert(c) => c.value
      | NoCert => BOTTOM
    }
  }

  /// Local state of a process
  type LocalState = {
    view: View,
    proposed: bool,
    voted: bool,
    sentFinal: bool,
    decided: Option[Value],
    highestCert: Certificate,
  }

  type ConsensusInput =
    | VoteTimeoutInput(View)
    | FinalTimeoutInput(View)
    | NextViewInput((ProcessID, Value, Set[NetworkMsg], Set[Value]))

  type ConsensusOutput =
    | Broadcast(Message)
    | Decide(Value)

  type Result = {
    output: Set[ConsensusOutput],
    post: LocalState,
  }

  /// Process a propose message (Rule 2)
  pure def processPropose(ls: LocalState, k: View, x: Value, cert: Certificate): Result = {
    if (k != ls.view or ls.voted) {
      // TODO: we indeed only accept the proposal in the current view? I think
      // this makes sense indeed, but it's not in the spec!
      // Wrong view or already voted
      { output: Set(), post: ls }
    }
    else {
      // Valid proposal, vote for it
      val highestCert = if (higherPriority(cert, ls.highestCert)) cert else ls.highestCert
      val newState = { ...ls,
        voted: true,
        highestCert: highestCert
      }
      {
        output: Set(Broadcast(VoteMsg({ view: k, value: x }))),
        post: newState
      }
    }
  }

  /// check Proposal is valid (Rule 2's precondition)
  pure def isValidProposal(ls: LocalState, proposal: NetworkMsg, msgs: Set[NetworkMsg]): bool = {
    match proposal.msg {
      | ProposeMsg(m) =>
        if ((m.view == ls.view) and (isValidCert(m.cert, msgs))) {
          // Check that all certs between the cert view and the current view exist
          // [res] gives the first view to check and whether both certs are to be checked or only the slow-cert one
          val res = match m.cert {
            | NoCert => (0, true)
            | FastCert(c) => (c.view, false)
            | SlowCert(c) => (c.view + 1, true)
          }
          val firstViewToCheck = res._1
          val checkBothCerts = res._2
          val restValid =
            (firstViewToCheck + 1).to(ls.view - 1).forall(v =>
              isValidCert(FastCert({view: v, value: BOTTOM}), msgs) and
              isValidCert(SlowCert({view: v, value: BOTTOM}), msgs))
          if (restValid) {
            if (firstViewToCheck < ls.view) {
              if (checkBothCerts) {
                // Check both certs
                (isValidCert(FastCert({view: firstViewToCheck, value: BOTTOM}), msgs)) and
                (isValidCert(SlowCert({view: firstViewToCheck, value: BOTTOM}), msgs))
              } else {
                // Check only slow-cert
                isValidCert(SlowCert({view: firstViewToCheck, value: BOTTOM}), msgs)
              }
            } else true
          } else false
        } else false
      | _ => false
    }
  }

  /// Process a Vote timeout (Rule 5)
  pure def processVoteTimeout(ls: LocalState, k: View): Result = {
    if (k != ls.view or ls.voted) {
      // Wrong view or already sent Vote
      { output: Set(), post: ls }
    } else {
      // Timeout, vote for bottom
      val newState = { ...ls, voted: true }
      {
        output: Set(Broadcast(VoteMsg({ view: k, value: BOTTOM }))),
        post: newState
      }
    }
  }

  /// Process a Final timeout (Rule 6)
  // TODO: normally this cannot be triggered before the Vote timeout; however,
  // we don't check this
  pure def processFinalTimeout(ls: LocalState, k: View): Result = {
    if (k != ls.view or ls.sentFinal) {
      // Wrong view or already sent Final
      { output: Set(), post: ls }
    } else {
      // Timeout, vote for bottom
      val newState = { ...ls, sentFinal: true }
      {
        output: Set(Broadcast(FinalMsg({ view: k, value: BOTTOM }))),
        post: newState
      }
    }
  }

  /// Get all the values in Vote and Final messages in [msgs], including BOTTOM
  pure def getValues(msgs: Set[NetworkMsg], view: View): Set[Value] = {
    msgs
      .filterMap(m => match m.msg {
        | VoteMsg(vote) => if (vote.view == view) { Some(vote.value) } else None
        | FinalMsg(vote) => if (vote.view == view) { Some(vote.value) } else None
        | _ => None
      })
  }

  pure def sendFinalMsg(ls: LocalState, value: Value): Result = {
    output: Set(Broadcast(FinalMsg({ view: ls.view, value: value }))),
    post: { ...ls, sentFinal: true }
  }

  pure def slowCertValues(msgs: Set[NetworkMsg], view: View): Set[Value] = {
    // Check all values for slow certificate (n-f-p votes)
    val values = msgs.getValues(view).exclude(Set(BOTTOM))
    values.fold(Set(), (acc, x) =>
      if (getVotesPower(msgs, view, x) >= N - F - P) {
        acc.union(Set(x))
      } else acc
    )
  }

  pure def canIncreaseView(ls: LocalState, msgs: Set[NetworkMsg]): bool = {
    ls.voted and ls.sentFinal and (
      val values = msgs.getValues(ls.view)
      val certs = values.fold((Set(), Set()), (accCerts, value) =>
        val votesPower = getVotesPower(msgs, ls.view, value)
        val fastCerts = accCerts._1
        val slowCerts = accCerts._2
        val newCerts =
          if (votesPower >= N - F - P) {
            val slowCert = SlowCert({ view: ls.view, value: value })
            if (value != BOTTOM) {
              // a slow cert on non-bot is also a fast-cert
              (fastCerts.union(Set(slowCert)), slowCerts.union(Set(slowCert))) }
            else { (fastCerts.union(Set(slowCert)), slowCerts) }
          } else if (votesPower >= N - 2*F - P) {
            val fastCert = FastCert({ view: ls.view, value: value })
            (fastCerts.union(Set(fastCert)), slowCerts)
          } else {
            (fastCerts, slowCerts)
          }
        val finalsPower = getFinalsPower(msgs, ls.view, value)
        if (finalsPower >= N - F - P and value == BOTTOM) {
          val slowCert = SlowCert({ view: ls.view, value: value })
          (newCerts._1, newCerts._2.union(Set(slowCert)))
        } else {
          newCerts
        }
      )
    certs._1.size() >= 1 and certs._2.size() >= 1
    )
  }

  pure def decide(ls: LocalState, value: Value): Result = {
    output: Set(Decide(value)),
    post: { ...ls, decided: Some(value) }
  }

  pure def canDecide(view: View, value: Value, msgs: Set[NetworkMsg]): bool = {
    (getVotesPower(msgs, view, value) >= N - P) or
    (getFinalsPower(msgs, view, value) >= N - F - P)
  }

  /// Propose an existing value if there is an certificate for it, otherwise propose [value] (Rule 1)
  pure def propose(ls: LocalState, newValue: Value): Result = {
    val proposedValue = match ls.highestCert {
      | FastCert(c) => c.value
      | SlowCert(c) => c.value
      | NoCert => newValue
    }
    val msg = ProposeMsg({ view: ls.view, value: proposedValue, cert: ls.highestCert })
    val newLS = {...ls, proposed: true}
    {output: Set(Broadcast(msg)), post: newLS}
  }

  pure def maybePropose(u: ProcessID, ls: LocalState, newValue: Value): Result = {
    if (isLeader(u, ls.view) and not(ls.proposed)) {
      propose(ls, newValue)
    } else {
      { output: Set(), post: ls }
    }
  }

  // Increase view
  pure def processNextView(u: ProcessID, ls: LocalState, newValue: Value, msgs: Set[NetworkMsg], values: Set[Value]): Result = {
    // TODO: is it correct to update the highest cert in this way?
    val highestCert = findHighestCert(ls.view, msgs, values)
    val newLS = { ...ls,
          view: ls.view + 1,
          voted: false,
          sentFinal: false,
          proposed: false,
          decided: None,
          highestCert: highestCert,
        }
    maybePropose(u, newLS, newValue)
  }

  /// Main consensus function
  pure def processInput(ls: LocalState, input: ConsensusInput): Result = {
    match input {
      | VoteTimeoutInput(view) => processVoteTimeout(ls, view)
      | FinalTimeoutInput(view) => processFinalTimeout(ls, view)
      | NextViewInput(t) => processNextView(t._1, ls, t._2, t._3, t._4)
    }
  }


  /// Initial local state
  pure def initLocalState(): LocalState = {
    view: 0,
    proposed: false,
    voted: false,
    sentFinal: false,
    decided: None,
    highestCert: NoCert,
  }
}