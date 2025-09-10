/**
 * Specification of 2-round and 3-round BFT (Simplex)
 * Based on https://decentralizedthoughts.github.io/2025-07-29-2-round-3-round-simplex/
 *
 * This is a one-shot consensus protocol with integrated fast and slow paths.
 * - Fast path: 2 rounds with n-p votes when at most p failures
 * - Slow path: 3 rounds with n-f-p votes when at most f failures
 */

// meaning of TODO:
// - something needs to be double-checked
// - something seems to be missing (but can be added later; it should be discovered when checking some properties)
// - something can improved, mostly for clarity/completeness
// meaning of FIXME:
// - something does not make sense and needs to be fixed

// Main observed issues:
// #1 FIXED it is unclear "how the system works", in particular how messages are received
// #2 Rules 8&1 are actually one rule, and should have a single action
// #3 we don't have the right checks in Rule 2
// #4 Rule 7 is missing
// #5 Pre-requisite for #3 are: #1 and have a better state in which we store (a summary) of received messages
// For the last three items, we should first detect some issues

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
    voted: bool,
    sentFinal: bool,
    decided: Option[Value],
    highestCert: Certificate,
    timer: int,
  }

  // TODO: why not MessageInput({msg: Message}) ?
  type ConsensusInput =
    | MessageInput(NetworkMsg)
    | VoteTimeoutInput({ view: View })
    | FinalTimeoutInput({ view: View })

  type ConsensusOutput =
    | Broadcast(Message)
    | Decide(Value)

  type Result = {
    output: Set[ConsensusOutput], // TODO: Set needed?
    post: LocalState,
  }

  /// Set of correct processes (non Byzantine)
  const correct: Set[ProcessID]

  /// Set of Byzantine processes
  const byzantine: Set[ProcessID]

  /// Voting power of the processes
  const power: ProcessID -> int

  /// All processes
  pure val processes = correct.union(byzantine)

  /// Number of processes (total voting power)
  pure def voting_power(s: Set[ProcessID]): int =
    s.fold(0, (acc, x) => acc + power.get(x))

  pure val n = voting_power(processes)

  /// Maximum Byzantine failures
  pure val f = voting_power(byzantine)

  /// Fast path parameter
  const p: int

  /// Constraints on parameters
  assume parameterConstraints = and {
    n >= 3 * f + 2 * p + 1,
    f >= 0,
    p >= 0,
    p <= f,
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

  // TODO: naming is a bit misleading: the function does not return an integer...
  /// Count votes from a set of messages
  pure def countVotes(msgs: Set[NetworkMsg], view: View, value: Value): Set[ProcessID] = {
    msgs
      .filter(m => match m.msg {
        | VoteMsg(vote) => vote.view == view and vote.value == value
        | _ => false
      })
      .map(m => m.sender)
  }

  /// Count final messages from a set of messages
  pure def countFinals(msgs: Set[NetworkMsg], view: View, value: Value): Set[ProcessID] = {
    msgs
      .filter(m => match m.msg {
        | FinalMsg(final) => final.view == view and final.value == value
        | _ => false
      })
      .map(m => m.sender)
  }

  /// Check if a certificate is valid
  pure def isValidCert(cert: Certificate, msgs: Set[NetworkMsg]): bool = {
    match cert {
      | FastCert(c) => countVotes(msgs, c.view, c.value).size() >= n - 2*f - p
      | SlowCert(c) => countVotes(msgs, c.view, c.value).size() >= n - f - p
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

  /// Get the value from a certificate
  pure def certValue(cert: Certificate): Value = {
    match cert {
      | FastCert(c) => c.value
      | SlowCert(c) => c.value
      | NoCert => BOTTOM
    }
  }

  // FIXME#3: not the right checks, UPDATE!
  /// Process a propose message (Rule 2)
  pure def processPropose(ls: LocalState, k: View, x: Value, cert: Certificate): Result = {
    if (k != ls.view or ls.voted) {
      // Wrong view or already voted
      { output: Set(), post: ls }
    } else if (not(higherPriority(cert, ls.highestCert))) {
      // Certificate not high priority enough
      { output: Set(), post: ls }
    } else {
      // Valid proposal, vote for it
      val newState = { ...ls,
        voted: true,
        highestCert: cert
      }
      {
        output: Set(Broadcast(VoteMsg({ view: k, value: x }))),
        post: newState
      }
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

  /// get all the values in Vote and Final messages in [msgs], including BOTTOM
  pure def getValues(msgs: Set[NetworkMsg], view: View): Set[Value] = {
    msgs
      .filterMap(m => match m.msg {
        | VoteMsg(vote) => if (vote.view == view) { Some(vote.value) } else None
        | FinalMsg(vote) => if (vote.view == view) { Some(vote.value) } else None
        | _ => None
      })
  }

  /// Check if we can form a fast certificate and decide (Rule 4, part 1)
  pure def checkFastDecision(ls: LocalState, msgs: Set[NetworkMsg]): Result = {
    if (ls.decided != None) {
      // Already decided
      { output: Set(), post: ls }
    } else {
      // Check all values for fast certificate (n-p votes)
      val values = msgs.getValues(ls.view)
      val fastDecision = values.fold(None, (acc, x) =>
        if (acc != None) acc
        else if (countVotes(msgs, ls.view, x).size() >= n - p) Some(x)
        else None
      )

      match fastDecision {
        | Some(x) => {
            // TODO: forward commit certificate?
            output: Set(Decide(x)),
            post: { ...ls, decided: Some(x) }
          }
        | None => { output: Set(), post: ls }
      }
    }
  }

  /// Check if we have enough votes to send final message (Rule 3)
  pure def checkSendFinal(ls: LocalState, msgs: Set[NetworkMsg]): Result = {
    if (ls.sentFinal) {
      // Already sent final
      { output: Set(), post: ls }
    } else {
      // Check all values for slow certificate (n-f-p votes)
      val values = msgs.getValues(ls.view).exclude(Set(BOTTOM))
      val canSendFinal = values.fold(None, (acc, x) =>
        if (acc != None) acc
        else if (countVotes(msgs, ls.view, x).size() >= n - f - p) Some(x)
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

  /// Check if we can decide based on final messages (Rule 4, part 2)
  pure def checkSlowDecision(ls: LocalState, msgs: Set[NetworkMsg]): Result = {
    if (ls.decided != None) {
      // Already decided
      { output: Set(), post: ls }
    } else {
      // Check for n-f-p final messages
      val values = msgs.getValues(ls.view).exclude(Set(BOTTOM))
      val slowDecision = values.fold(None, (acc, x) =>
        if (acc != None) acc
        else {
          val finalCount = countFinals(msgs, ls.view, x).size()
          if (finalCount >= n - f - p) Some(x)
          else None
        }
      )

      match slowDecision {
        | Some(x) => {
            // TODO: forward certificate?
            output: Set(Decide(x)),
            post: { ...ls, decided: Some(x) }
          }
        | None => { output: Set(), post: ls }
      }
    }
  }

  // FIXME#5: I'm not sure we should use [msgs] here (or what its meaning is)
  pure def processMessage(ls: LocalState, networkMsg: NetworkMsg, msgs: Set[NetworkMsg]): Result = {
    match networkMsg.msg {
      | ProposeMsg(m) => processPropose(ls, m.view, m.value, m.cert)
      | VoteMsg(_) => {
          // Process vote by checking if we can decide or send final
          // FIXME#4: missing Rule 7
          val r1 = checkFastDecision(ls, msgs)
          if (r1.output.size() > 0) r1
          else checkSendFinal(r1.post, msgs)
        }
      | FinalMsg(_) => checkSlowDecision(ls, msgs)
    }
  }


  /// Main consensus function
  pure def processInput(ls: LocalState, input: ConsensusInput, msgs: Set[NetworkMsg]): Result = {
    match input {
      | MessageInput(msg) => processMessage(ls, msg, msgs)
      | VoteTimeoutInput(t) => processVoteTimeout(ls, t.view)
      | FinalTimeoutInput(t) => processFinalTimeout(ls, t.view)
    }
  }

  /// Initial local state
  pure def initLocalState(): LocalState = {
    view: 0,
    voted: false,
    sentFinal: false,
    decided: None,
    highestCert: NoCert,
    timer: 0,
  }
}