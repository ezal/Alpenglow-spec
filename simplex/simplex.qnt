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
#1 FIXED it is unclear "how the system works", in particular how messages are received
#2 FIXED Rules 8&1 are actually one rule, and should have a single action
   - I couldn't put it into a single action, because I don't know how to pick
     a value in a 'pure def'. (Normally, a party advances in view only when it
     receives a new message, so sending a proposal is normally part of
     [processMessage])
#3 We don't have the right checks in Rule 2
#4 Rule 7 is missing
#5 FIXED Pre-requisite for #3 are: #1 and have a better state in which we store (a summary) of received messages
#6 FIXED If the proposal is valid, add the messages in its certificate to the received messages
#7 Properly update the local state, including highestCert (code in [moveToNextView] may be useful)

For some of the items, we could first detect some issues and then fix them
*****************************************************/


module simplex {
  import basicSpells.* from "./basicSpells"

  type ProcessID = str

  type View = int

  type Value = int

  /// Special bottom value representing no decision/timeout
  pure val BOTTOM = -1

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

  const correct: Set[ProcessID]
  const byzantine: Set[ProcessID]
  pure val processes = correct.union(byzantine)

  const power: ProcessID -> int

  /// Number of processes (total voting power)
  pure def voting_power(s: Set[ProcessID]): int =
    s.fold(0, (acc, x) => acc + power.get(x))

  pure val n = voting_power(processes)

  /// Slow-path parameter; also maximum power of Byzantines
  const f: int

  /// Fast-path parameter
  const p: int

  /// Constraints on parameters
  assume parameterConstraints = and {
    n >= 3 * f + 2 * p + 1,
    f >= 0,
    p >= 0,
    p <= f,
    // voting_power(byzantine) <= f,
  }

  /// Leader selection function: simple round-robin leader selection
  pure def leader(view: View): ProcessID = {
    val allProcs = processes.fold(List(), (acc, p) => acc.append(p))
    val index = view % allProcs.length()
    allProcs[index]
  }

  /// Check if process is the leader of a view
  pure def isLeader(proc: ProcessID, view: View): bool = {
    leader(view) == proc
  }

  pure def getMsgValue(msg: Message): Value = {
    match msg {
      | ProposeMsg(m) => m.value
      | VoteMsg(m) => m.value
      | FinalMsg(m) => m.value
    }
  }

  /// Return the Vote messages for a given view and value from a set of messages
  pure def getVotes(msgs: Set[NetworkMsg], view: View, value: Value): Set[NetworkMsg] = {
    msgs
      .filter(m => match m.msg {
        | VoteMsg(vote) => vote.view == view and vote.value == value
        | _ => false
      })
  }

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

  pure def getProposals(msgs: Set[NetworkMsg], view: View): Set[NetworkMsg] = {
    msgs
      .filter(m => match m.msg {
        | ProposeMsg(propose) => propose.view == view
        | _ => false
      })
  } 

  /// Check if a certificate is valid
  pure def isValidCert(cert: Certificate, msgs: Set[NetworkMsg]): bool = {
    match cert {
      | FastCert(c) => getVoteSenders(msgs, c.view, c.value).size() >= n - 2*f - p
      | SlowCert(c) => getVoteSenders(msgs, c.view, c.value).size() >= n - f - p
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
        val votes = getVotes(msgs, view, value).size()
        val res =
          if (votes >= n - f - p and value != BOTTOM) {
            acc2.union(Set(SlowCert({ view: view, value: value })))
          } else if (votes >= n - 2*f - p) {
            acc2.union(Set(FastCert({ view: view, value: value })))
          } else {
            acc2
          }
        val finals = getFinals(msgs, view, value).size()
        if (finals >= n - f - p and value == BOTTOM) {
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

  // FIXME#3: not the right checks, UPDATE! But not here, here we assume the proposal is valid
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
          restValid and
          (if (checkBothCerts) {
              // Check both certs
              (isValidCert(FastCert({view: firstViewToCheck, value: BOTTOM}), msgs)) and
              (isValidCert(SlowCert({view: firstViewToCheck, value: BOTTOM}), msgs))
          } else {
              // Check only slow-cert
            isValidCert(SlowCert({view: firstViewToCheck, value: BOTTOM}), msgs)
          })
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

  /// Send Final message if we have enough votes to (Rule 3)
  pure def maybeSendFinal(ls: LocalState, msgs: Set[NetworkMsg]): Result = {
    if (ls.sentFinal) {
      // Already sent final
      { output: Set(), post: ls }
    } else {
      // Check all values for slow certificate (n-f-p votes)
      val values = msgs.getValues(ls.view).exclude(Set(BOTTOM))
      val canSendFinal = values.fold(None, (acc, x) =>
        if (acc != None) acc
        else if (getVoteSenders(msgs, ls.view, x).size() >= n - f - p) Some(x)
        else None
      )

      match canSendFinal {
        | Some(x) => {
            output: Set(Broadcast(FinalMsg({ view: ls.view, value: x }))),
            post: { ...ls, sentFinal: true }
          }
        | None => { output: Set(), post: ls }
      }
    }
  }

  pure def canIncreaseView(ls: LocalState, msgs: Set[NetworkMsg]): bool = {
    ls.voted and ls.sentFinal and (
      val values = msgs.getValues(ls.view)
      val certs = values.fold((Set(), Set()), (accCerts, value) =>
        val votes = getVoteSenders(msgs, ls.view, value).size()
        val fastCerts = accCerts._1
        val slowCerts = accCerts._2
        val newCerts =
          if (votes >= n - f - p) {
            val slowCert = SlowCert({ view: ls.view, value: value })
            if (value != BOTTOM) {
              // a slow cert on non-bot is also a fast-cert
              (fastCerts.union(Set(slowCert)), slowCerts.union(Set(slowCert))) }
            else { (fastCerts.union(Set(slowCert)), slowCerts) }
          } else if (votes >= n - 2*f - p) {
            val fastCert = FastCert({ view: ls.view, value: value })
            (fastCerts.union(Set(fastCert)), slowCerts)
          } else {
            (fastCerts, slowCerts)
          }
        val finals = getFinalSenders(msgs, ls.view, value).size()
        if (finals >= n - f - p and value == BOTTOM) {
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
    (getVoteSenders(msgs, view, value).size() >= n - p) or 
    (getFinalSenders(msgs, view, value).size() >= n - f - p)
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

  /* 
  pure def composeResult(res1: Result, res2: Result): Result =
    { output: res1.output.union(res2.output), post: res2.post }

  pure def processMessage(ls: LocalState, networkMsg: NetworkMsg): Result = {
    match networkMsg.msg {
      | ProposeMsg(m) =>
          processPropose(ls, m.view, m.value, m.cert)
      | VoteMsg(m) => {
          // FIXME#7 properly update the local state, including highestCert
          val ls2 = { ...ls, seenMsgs: ls.seenMsgs.union(Set(networkMsg)) }
          // Process vote by checking if we can decide or send final
          // FIXME#4: missing Rule 7
          // TODO: that's hard to read, improve!
          val res = checkFastDecision(ls2)
          if (res.output.size() > 0) res
          else {
            val res2 = maybeSendFinal(res.post)
            val res3 = composeResult(res, res2)
            val ls3 = maybeIncreaseView(res3.post)
            {...res3, post: ls3}
          }
        }
      | FinalMsg(m) => {
          // FIXME#7 properly update the local state, including highestCert
          val ls2 = { ...ls, seenMsgs: ls.seenMsgs.union(Set(networkMsg)) }
          val res = checkSlowDecision(ls2)
          if (res.output.size() > 0) res
          else {
            val ls3 = maybeIncreaseView(res.post)
            {...res, post: ls3}
          }
        }
    }
  }
  */

  pure def processNextView(u: ProcessID, ls: LocalState, newValue: Value, msgs: Set[NetworkMsg], values: Set[Value]): Result = {
    // Increase view
    val highestCert = findHighestCert(ls.view, msgs, values) 
    val newLS = { ...ls,
          view: ls.view + 1,
          voted: false,
          sentFinal: false,
          proposed: false,
          decided: None,
          highestCert: highestCert,
        }
    if (isLeader(u, newLS.view)) {
      propose(newLS, newValue)
    } else {
      { output: Set(), post: newLS }
    }
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