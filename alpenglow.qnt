// -*- mode: Bluespec; -*-
/**
 * Simplified Specification of Alpenglow Consensus
 * - Removed slot windows (no more parallel consensus instances)
 * - Each slot can have a different leader
 * - Kept concurrent fast/slow paths
 *
 * Based on the original specification by Josef Widder and Gabriela Moreira
 * Simplified by removing slot windows
 */

module alpenglow {
  import basicSpells.* from "./basicSpells"

  type ProcessID = str

  type Slot = int

  type Block = {
    slot: Slot,
    hash: Blockhash,
    parent: Blockhash,
  }

  type BlockReference = { slot: Slot, hash: Blockhash }

  type Blockhash = int

  /// Fields are lists indexed by slot
  type LocalState = {
    pendingBlocks: List[Option[Block]],
    state: List[Set[SlotObject]],
  }

  /// Definition 18 (Votor State) - simplified
  type SlotObject =
    | ParentReady(Blockhash)
    | Voted
    | VotedNotar(Blockhash)
    | BlockNotarized(Blockhash)
    | ItsOver
    | BadSlot  // renamed from BadWindow

  type ConsensusInput =
    | BlockInput(Block)
    | TimeOutInput(Slot)
    | BlockNotarizedInput(BlockReference)
    | ParentReadyInput(BlockReference)
    | SafeToNotarInput(BlockReference)
    | SafeToSkipInput(Slot)

  /// Table 4 (Alpenglow's voting messages)
  type Message =
    | NotarVoteMsg(BlockReference)
    | NotarFallBackVoteMsg(BlockReference)
    | SkipVoteMsg(Slot)
    | SkipFallbackVoteMsg(Slot)
    | FinalVoteMsg(Slot)

  type Certificate =
    | FastFinalizationCertificate(BlockReference)
    | NotarizationCertificate(BlockReference)
    | NotarFallbackCertificate(BlockReference)
    | SkipCertificate(Slot)
    | FinalizationCertificate(Slot)

  type TimeoutEventData = Slot

  type ConsensusOutput =
    | ScheduleEventTimeout(TimeoutEventData)
    | Broadcast(Message)

  type Bookkeeping

  type Result = {
    output: Set[ConsensusOutput],
    post: LocalState,
  }

  /// Messages on the network carry the sender
  type NetworkMsg = {
    sender: ProcessID,
    msg: Message,
  }

  /// Set of correct processes (non Byzantine)
  const correct: Set[ProcessID]

  /// Set of processes that follow the algorithm but might fail in a benign way
  const good: Set[ProcessID]

  /// Set of Byzantine processes
  const byzantine: Set[ProcessID]

  /// Voting power of the processes
  const power: ProcessID -> int

  /// Set of blocks
  const correctBlocks: Set[Block]
  /// Set of Byzantine blocks
  const byzantineBlocks: Set[Block]

  /// Set of all blocks
  pure val allBlocks = correctBlocks.union(byzantineBlocks)

  /// Set of correct processes and processes that follow the algorithm but might fail in a benign way
  pure val benevolent = correct.union(good)

  pure val maxSlot = allBlocks.fold(-1, (s, x) => max(x.slot, s))

  /// Slots for which this model considers votes
  const aliveSlots: Set[Slot]
  /// Hashes for which this model considers votes
  const aliveHashes: Set[Blockhash]

  //
  // Constraints on the number of processes
  //

  assume uniqueRole = and {
    correct.intersect(byzantine) == Set(),
    correct.intersect(good) == Set(),
    good.intersect(byzantine) == Set(),
  }

  pure def voting_power(s: Set[ProcessID]): int =
    s.fold(0, (s, x) => s + power.get(x))

  pure val totalVotingPower = correct.union(good).union(byzantine).voting_power()

  // Assumption 1 and Assumption 2
  assume resilienceCondition = all {
    totalVotingPower > byzantine.voting_power() * 5, // N > 5F
    totalVotingPower > good.voting_power() * 5, // Less than a fifth is not Byzantine but may be silent
  }

  /// Checks for thresholds, using the known total voting power
  pure def surpassesThreshold(votes, threshold) =
    votes.voting_power() * 100 >= totalVotingPower * threshold

  /// All votes that can be sent by the Byzantine processes (without senders)
  pure val byzMessages = tuples(aliveSlots, aliveHashes).map(((slot, hash)) =>
    Set(
      NotarVoteMsg({ slot: slot, hash: hash }),
      NotarFallBackVoteMsg({ slot: slot, hash: hash }),
      SkipVoteMsg(slot),
      SkipFallbackVoteMsg(slot),
      FinalVoteMsg(slot)
    )
  ).flatten()

  /// All votes that can be sent by the Byzantine processes
  pure val byzNetworkMsgs = tuples(byzantine, byzMessages).map(((sender, msg)) =>
    { sender: sender, msg: msg }
  )

  // Auxiliary functions

  pure def slotOf(msg: Message): Slot =
    match msg {
      | NotarVoteMsg(m) => m.slot
      | NotarFallBackVoteMsg(m) => m.slot
      | SkipVoteMsg(slot) => slot
      | SkipFallbackVoteMsg(slot) => slot
      | FinalVoteMsg(slot) => slot
    }

  pure def reference(b: Block): BlockReference = { slot: b.slot, hash: b.hash }

  pure def addObjects(ls: LocalState, slot: Slot, obj: Set[SlotObject]): LocalState =
    { ...ls, state: ls.state.replaceAt(slot, ls.state[slot].union(obj)) }

  pure def setPendingBlock(ls: LocalState, slot: Slot, b: Option[Block]): LocalState =
    { ...ls, pendingBlocks: ls.pendingBlocks.replaceAt(slot, b) }

  pure def notarizedBlocks(msgs: Set[NetworkMsg]): Set[BlockReference] =
    msgs
      .fold(Set(), (s, x) => match x.msg {
        | NotarVoteMsg(m) => s.union(Set(m))
        | _ => s
      })
      .filter(b => isCertified(NotarizationCertificate(b), msgs))

  pure def notarFallbackBlocks(msgs: Set[NetworkMsg]): Set[BlockReference] =
    msgs
      .fold(Set(), (s, x) => match x.msg {
        | NotarVoteMsg(m) => s.union(Set(m))
        | NotarFallBackVoteMsg(m) => s.union(Set(m))
        | _ => s
      })
      .filter(b => isCertified(NotarFallbackCertificate(b), msgs))

  pure def slotsSkipCertified(msgs: Set[NetworkMsg]): Set[Slot] =
    msgs
      .fold(Set(), (s, x) => match x.msg {
        | SkipVoteMsg(m) => s.union(Set(m))
        | _ => s
      })
      .filter(s => isCertified(SkipCertificate(s), msgs))

  // Definition 5 (ancestor and descendant)
  pure def isDescendant(a: Block, b: Block): bool = {
    pure val bAncestors = (b.slot.to(a.slot)).fold(Set(b.hash), (path, s) =>
      pure val potentialAncestors = allBlocks.filter(block => block.slot == s)
      pure val ancestors = potentialAncestors.filter(ancestor =>
        path.exists(h => ancestor.parent == h)
      )
      path.union(ancestors.map(block => block.hash))
    )

    bAncestors.contains(a.hash)
  }

  // Definition 13 (certificates)
  /// Table 5: Alpenglow's certificate messages.
  pure def isCertified(cert: Certificate, msgs: Set[NetworkMsg]): bool = {
    pure val aggregatedVotes = msgs.filter(m => {
      match cert {
        | FastFinalizationCertificate(b) =>
          m.msg == NotarVoteMsg(b)
        | NotarizationCertificate(b) =>
          m.msg == NotarVoteMsg(b)
        | NotarFallbackCertificate(b) =>
          m.msg == NotarVoteMsg(b) or m.msg == NotarFallBackVoteMsg(b)
        | SkipCertificate(s) =>
          m.msg == SkipVoteMsg(s) or m.msg == SkipFallbackVoteMsg(s)
        | FinalizationCertificate(s) =>
          m.msg == FinalVoteMsg(s)
      }
    })

    pure val threshold = match cert {
      | FastFinalizationCertificate => 80
      | NotarizationCertificate => 60
      | NotarFallbackCertificate => 60
      | SkipCertificate => 60
      | FinalizationCertificate => 60
    }

    aggregatedVotes.map(x => x.sender).surpassesThreshold(threshold)
  }

  // Definition 14 (finalization)
  /// If a finalization certificate on slot s is in Pool, the unique notarized block
  /// in slot s is finalized (we call this slow-finalized).
  pure def finalized(slot: Slot, msgs: Set[NetworkMsg]): Set[Blockhash] =
    allBlocks.map(b => b.reference())
      .filter(b => b.slot == slot)
      .filter(b => {
        isCertified(FinalizationCertificate(b.slot), msgs)
          and isCertified(NotarizationCertificate(b), msgs)
      })
      .map(b => b.hash)

  /// If a fast-finalization certificate on block b is in Pool, the block b is
  /// finalized (fast-finalized).
  pure def fastFinalized(slot: Slot, msgs: Set[NetworkMsg]): Set[Blockhash] =
    allBlocks.map(b => b.reference())
      .filter(b => b.slot == slot)
      .filter(b => isCertified(FastFinalizationCertificate(b), msgs))
      .map(b => b.hash)

  // Algorithm 2 - Simplified without windows

  /// Set timeout only for the current slot
  pure def setTimeouts(ls: LocalState, slot: Slot): Result =
    { post: ls,
      output: Set(ScheduleEventTimeout(slot)) }

  /// Check if a notarization vote can be cast - simplified
  pure def tryNotar(ls: LocalState, b: Block): { result: Result, success: bool } =
    if (ls.state[b.slot].contains(Voted))
      { result: { post: ls, output: Set() }, success: false }
    else
      // Check if parent is ready (notarized) for any slot
      if (b.slot == 0 or ParentReady(b.parent).in(ls.state[b.slot]))
        // Notarization vote
        val out = Set(Broadcast(NotarVoteMsg({ slot:b.slot, hash: b.hash })))
        val s2 = ls
          .addObjects(b.slot, Set(Voted, VotedNotar(b.hash)))
          // Won't vote notar a second time
          .setPendingBlock(b.slot, None)

        // Maybe vote finalize as well
        val tf = tryFinal(s2, b.slot, b.hash)

        { result: { post: tf.post, output: out.union(tf.output) }, success: true }
      else
        { result: { post: ls, output: Set() }, success: false }

  pure def tryFinal(ls: LocalState, slot: Slot, hash: Blockhash): Result =
    if (BlockNotarized(hash).in(ls.state[slot]) and VotedNotar(hash).in(ls.state[slot])
        and not(BadSlot.in(ls.state[slot])))
      // Finalization vote
      { output: Set(Broadcast(FinalVoteMsg(slot))), post: ls.addObjects(slot, Set(ItsOver)) }
    else
      { output: Set(), post: ls }

  /// Simplified: skip only the current slot
  pure def trySkip(ls: LocalState, slot: Slot): Result =
    if (not(Voted.in(ls.state[slot])))
      // Skip vote
      val update = Set(Broadcast(SkipVoteMsg(slot)))
      val s2 = ls
        .addObjects(slot, Set(Voted, BadSlot))
        // Won't vote notar after skip
        .setPendingBlock(slot, None)

      { output: update, post: s2 }
    else
      { output: Set(), post: ls }

  pure def checkPendingBlocks(ls: LocalState): Result =
    // Iterate with increasing slot
    ls.pendingBlocks.foldl({ output: Set(), post: ls }, (res, pendingBlock) =>
      match pendingBlock {
        | Some(b) =>
          val tn = tryNotar(res.post, b)
          { output: res.output.union(tn.result.output), post: tn.result.post }
        | None =>
          res
      }
    )

  /// Algorithm 1: each upon corresponds to one consensus input - simplified
  pure def consensus(ls: LocalState, input: ConsensusInput): Result =
    match input {
      | BlockInput(b) =>
        val tn = tryNotar(ls, b)
        if (tn.success)
          val cpb = checkPendingBlocks(tn.result.post)
          { post: cpb.post, output: cpb.output.union(tn.result.output) }
        else if (not(Voted.in(tn.result.post.state[b.slot])))
          { output: tn.result.output, post: tn.result.post.setPendingBlock(b.slot, Some(b)) }
        else
          { output: tn.result.output, post: tn.result.post }

      | TimeOutInput(slot) =>
        if (not(Voted.in(ls.state[slot])))
          trySkip(ls, slot)
        else
          { output: Set(), post: ls }

      | BlockNotarizedInput(sh) =>
        val s1 = ls.addObjects(sh.slot, Set(BlockNotarized(sh.hash)))
        tryFinal(s1, sh.slot, sh.hash)

      | ParentReadyInput(sh) =>
        val s1 = ls.addObjects(sh.slot, Set(ParentReady(sh.hash)))
        val s2 = checkPendingBlocks(s1)
        // Start timer only for this slot
        val s3 = setTimeouts(s2.post, sh.slot)
        { output: s2.output.union(s3.output), post: s3.post }

      | SafeToNotarInput(sh) =>
        val s1 = trySkip(ls, sh.slot)
        if (not(ItsOver.in(s1.post.state[sh.slot])))
          // Notar-fallback vote
          val output = s1.output.union(Set(Broadcast(NotarFallBackVoteMsg(sh))))
          { output: output, post: s1.post.addObjects(sh.slot, Set(BadSlot)) }
        else
          s1

      | SafeToSkipInput(slot) =>
        val s1 = trySkip(ls, slot)
        if (not(ItsOver.in(s1.post.state[slot])))
          // Skip-fallback vote
          val output = s1.output.union(Set(Broadcast(SkipFallbackVoteMsg(slot))))
          { output: output, post: addObjects(s1.post, slot, Set(BadSlot)) }
        else
          s1
    }
}