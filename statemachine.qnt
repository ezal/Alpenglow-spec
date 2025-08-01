// -*- mode: Bluespec; -*-

module consensus {
  import basicSpells.* from "./basicSpells"
  import alpenglow.* from "./alpenglow"
  export alpenglow.*

  /// This is all the information of the global state
  type Environment = {
    // The local state of each process
    system: ProcessID -> LocalState,

    // Messages sent so far, a.k.a. the message soup
    msgBuffer: Set[NetworkMsg],

    // Started timeouts per process
    activeTimeouts: ProcessID -> Set[TimeoutEventData],
  }

  /// Interface consensus algorithm / state machine: how consensus algorithm effects the environment
  pure def applyEffect(env: Environment, v: ProcessID, res: Result): Environment =
    // update the state of the process
    val new = { ... env, system: env.system.set(v, res.post) } 
    // update the message buffer and active timeouts
    res.output.fold(new, (s, o) =>
      match o {
        | Broadcast(msg) =>
          val nm = { sender: v, msg: msg }
          { ...s, msgBuffer: s.msgBuffer.union(Set(nm)) }
        | ScheduleEventTimeout(slot) =>
          { ...s, activeTimeouts: s.activeTimeouts.set(v, s.activeTimeouts.get(v).union(Set(slot))) }
      })

  //
  //
  // State Machine
  //
  //

  var s: Environment

  val finalizedBlocks: Slot -> Set[Blockhash] = aliveSlots.mapBy(s => finalized(s, allMessages))

  var ch: Slot -> Set[Blockhash] // blockchain as seen by message soup

  var counter: int // Required for TLC

  /// all the messages that could be received, i.e., the ones sent by benevolent processes
  /// and the ones that byzantine processes may send
  val allMessages = s.msgBuffer.union(byzNetworkMsgs)

  action init = all {
    s' = {
      system: benevolent.mapBy(_ => {
        // preload state for 5 slots
        state: [
          Set(ParentReady(-1)),
          Set(),
          Set(),
          Set(),
          Set(),
        ],
        pendingBlocks: [None, None, None, None, None]
      }),
      msgBuffer: Set(),
      activeTimeouts: benevolent.mapBy(v => Set(0)),
    },
    ch' = aliveSlots.mapBy(s => Set()),
    counter' = 0,
  }

  action receiveSpecificBlock(v: ProcessID, b: Block): bool = all {
    allBlocks.contains(b),
    v.processInput(BlockInput(b)),
  }

  action receiveBlock(v: ProcessID, now: Slot): bool = all{
    nondet block = allBlocks.filter(b => b.slot == now).oneOf()
    receiveSpecificBlock(v, block)
  }

  /// Fire timeout for slot
  action fireTimeoutEvent(v: ProcessID, now: Slot): bool = all {
    s.activeTimeouts.get(v).contains(now),
    val s2 = { ...s, activeTimeouts: s.activeTimeouts.set(v, s.activeTimeouts.get(v).exclude(Set(now))) }
    s' = applyEffect(s2, v, consensus(s2.system.get(v), TimeOutInput(now))),
    ch' = finalizedBlocks,
    counter' = counter + 1,
  }

  //
  // auxiliary functions for actions below
  //

  action processInput(id: ProcessID, input: ConsensusInput): bool = all {
    s' = applyEffect(s, id, consensus(s.system.get(id), input)),
    ch' = finalizedBlocks,
    counter' = counter + 1,
  }

  // Definition 15 (Pool events)

  // • BlockNotarized(slot(b), hash(b)): Pool holds a notarization certificate for block b.
  def notarizedBlocksCondition(v: ProcessID, b: BlockReference): bool =
    isCertified(NotarizationCertificate(b), allMessages)

  /// Emit BlockNotarized and process it
  action blockNotarizedAction(v: ProcessID, now: Slot): bool =
    val bs = allBlocks.filter(b =>
      notarizedBlocksCondition(v, { slot: now, hash: b.hash })
    )
    all {
      bs.size() > 0,
      nondet b = bs.oneOf()
      v.processInput(BlockNotarizedInput({ slot: b.slot, hash: b.hash })),
    }

  // • ParentReady(s, hash(b)): Simplified - just check if parent is notarized
  pure def parentReadyCondition(slot: Slot, hash: Blockhash, msgs: Set[NetworkMsg]): bool = all {
    // For slot 0, always ready
    or {
      slot == 0,
      // For other slots, parent must be notarized or have notar-fallback certificate
      0.to(slot - 1).exists(s =>
        val b = { slot: s, hash: hash }
        or {
          isCertified(NotarizationCertificate(b), msgs),
          isCertified(NotarFallbackCertificate(b), msgs)
        }
      )
    }
  }

  /// Emit ParentReady and process it
  action parentReadyAction(v: ProcessID, now: Slot): bool =
    val bs = allBlocks.filter(b => parentReadyCondition(now, b.hash, allMessages))
    all {
      bs.size() > 0,
      nondet b = bs.oneOf()
      v.processInput(ParentReadyInput({slot: now, hash: b.hash})),
    }

  /// Definition 16 (fallback events)

  pure def votedToSkip(s: Slot, msgs: Set[NetworkMsg]): Set[ProcessID] =
    msgs.filter(m =>  m.msg == SkipVoteMsg(s)).map(m => m.sender)

  pure def votedToNotar(b: BlockReference, msgs: Set[NetworkMsg]): Set[ProcessID] =
    msgs.filter(m => m.msg == NotarVoteMsg(b)).map(m => m.sender)

  // • SafeToNotar(s, hash(b)): The event is only issued if the node voted in
  // slot s already, but not to notarize b.
  def safeToNotarCondition(v: ProcessID, now: Slot, b: Block): bool = all {
    // Consider block b in slot s = slot(b).
    b.slot == now,

    val voted = allMessages.filter(m => m.sender == v and now == slotOf(m.msg))
    val notarVoted =
      voted.filter(m => match m.msg {
        | NotarVoteMsg(m) => true
        | _ => false
      })

    and {
      voted.size() > 0,
      notarVoted.size() == 0,
    },
    val notar = votedToNotar(b.reference(), allMessages)
    val skip = votedToSkip(now, allMessages)
    // notar(b) ≥ 40% or (skip(s) + notar(b) ≥ 60% and notar(b) ≥ 20%).
    or {
      surpassesThreshold(notar, 40),
      and {
        surpassesThreshold(skip.union(notar), 60),
        surpassesThreshold(notar, 20)
      }
    }
  }

  // Emit SafeToNotar and process it
  action safeToNotarAction(v: ProcessID, now: Slot): bool =
    val bs = allBlocks.filter(b => safeToNotarCondition(v, now, b))
    all {
      bs.size() > 0,
      nondet b = bs.oneOf()
      v.processInput(SafeToNotarInput({ slot: b.slot, hash: b.hash })),
    }

  // • SafeToSkip(s): The event is only issued if the node voted in slot s already,
  // but not to skip s.
  def safeToSkipCondition(v: ProcessID, now: Slot): bool = all {
    // node voted in slot s already, but not to skip s.
    allMessages.exists(m =>
      m.sender == v
      and slotOf(m.msg) == now
      and m.msg != SkipVoteMsg(now)
    ),

    // Moreover:
    // skip(s) + Σ_b notar(b) − max_b notar(b) ≥ 40%.
    val blocksWithNotarVotes =
      allMessages
        .filter(m => slotOf(m.msg) == now)
        .fold(Set(), (s, m) => match m.msg {
          | NotarVoteMsg(n) => s.setAdd(n)
          | _ => s
        })

    // Σ_b notar(b)
    val allNotarVotes = blocksWithNotarVotes.map(b =>
      votedToNotar(b, allMessages)
    ).flatten()

    // max_b
    val blockWithMostVotes = blocksWithNotarVotes.fold({ slot: -1, hash: -1 }, (res, x) => {
      if (votedToNotar(x, allMessages).size() > votedToNotar(res, allMessages).size())
        x
      else
        res
    })

    // skip(s) + Σ_b notar(b) − max_b notar(b) ≥ 40%.
    votedToSkip(now, allMessages)
      .union(allNotarVotes)
      .exclude(votedToNotar(blockWithMostVotes, allMessages))
      .surpassesThreshold(40)
  }

  // Emit SafeToSkip and process it
  action safeToSkipAction(v: ProcessID, now: Slot): bool = all {
    safeToSkipCondition(v, now),
    v.processInput(SafeToSkipInput(now)),
  }

  /// Any upon that is triggered by messages
  action messageResponse (v, slot) =
    any {
      receiveBlock(v, slot),
      blockNotarizedAction(v, slot),
      parentReadyAction(v, slot),
      safeToNotarAction(v, slot),
      safeToSkipAction(v, slot),
    }

  /// Main step action. Includes all behavior
  action step = all {
    counter < 10,
    nondet v = oneOf(benevolent)
    nondet slot = oneOf(aliveSlots)
    any {
      messageResponse(v, slot),
      fireTimeoutEvent(v, slot),
    }
  }

  /// Alternative step action. With this, no timeout ever expires
  action noTimeout = any {
    nondet v = oneOf(benevolent)
    nondet slot = oneOf(aliveSlots)    
    messageResponse(v, slot),
  }

  //
  //
  // Invariants and Witnesses
  //
  //

  val agreement =
    aliveSlots.forall(slot => finalized(slot, allMessages).size() <= 1)

  val fastAgreement =
    aliveSlots.forall(slot => fastFinalized(slot, allMessages).union(finalized(slot, allMessages)).size() <= 1)

  // Witness - updated to use BadSlot instead of BadWindow
  val noBad =
    benevolent.forall(v => not(s.system.get(v).state[1].contains(BadSlot)))

  /// Witness to find a run where a block is fast finalized
  val fastFinalizedWitness =
    allBlocks.forall(b => not(isCertified(FastFinalizationCertificate(b.reference()), allMessages)))

  /// Witness to find a run where a timeout is started
  val timeoutWitness = 
     s.activeTimeouts.values().forall(v => v == Set())

  /// Theorem 1 (safety)
  val safety = tuples(aliveSlots, allBlocks).forall(((slot, block)) => {
    val finalizedAtSlot = finalized(slot, allMessages)
    block.hash.in(finalizedAtSlot) implies tuples(
      aliveSlots.filter(s2 => s2 >= slot), allBlocks).forall(((slot2, block2)) => {
      block2.hash.in(finalized(slot2, allMessages)) implies block2.isDescendant(block)
    })
  })

  /// This generates example traces where a block is finalized after some empty slots
  val emptySlotsWitness = 
    aliveSlots.forall(s1 => 
      aliveSlots.forall(s2 => 
        s1 < s2 implies
      ch.get(s1).size() >= ch.get(s2).size()))
                              
  /// This generates example traces where every slot is finalized
  val noEmptySlotsWitness = 
    aliveSlots.exists(s1 => 
      ch.get(s1).size() == 0)
}

module some_byz {
  // For a trace where a value is fast finalized call
  // quint run statemachine.qnt --main some_byz --invariant fastFinalizedWitness
  import consensus(
    correct = Set("v1", "v2", "v3", "v4", "v5"),
    good = Set(),
    byzantine = Set("b1"),
    power = Set("v1", "v2", "v3", "v4", "v5", "b1").mapBy(_ => 1), 
    correctBlocks = Set(
      { slot: 0, hash: 42, parent: -1 },
      { slot: 1, hash: 43, parent: 42 },
      { slot: 2, hash: 44, parent: 43 },
    ),
    byzantineBlocks = Set(
      { slot: 1, hash: 46, parent: 42 },
      { slot: 1, hash: 47, parent: 45 },
      { slot: 2, hash: 48, parent: 43 },
      { slot: 2, hash: 49, parent: 45 },
    ),
    aliveSlots = 0.to(2),
    aliveHashes = 42.to(49),
  ).*

  run ffTest =
    init
    .then(receiveSpecificBlock("v1", { hash: 42, parent: -1, slot: 0 }))
    .then(receiveSpecificBlock("v2", { hash: 42, parent: -1, slot: 0 }))
    .then(receiveSpecificBlock("v3", { hash: 42, parent: -1, slot: 0 }))
    .then(receiveSpecificBlock("v4", { hash: 42, parent: -1, slot: 0 }))
    .expect(fastFinalized(0, allMessages) == Set(42))
}

module some_byz_vp {
  // For a trace where a value is fast finalized with variable voting power
  import consensus(
    correct = Set("v1", "v2"),
    good = Set(),
    byzantine = Set("b1"),
    power = Map("v1" -> 3, "v2" -> 2, "b1"-> 1), 
    correctBlocks = Set(
      { slot: 0, hash: 42, parent: -1 },
      { slot: 1, hash: 43, parent: 42 },
      { slot: 2, hash: 44, parent: 43 },
    ),
    byzantineBlocks = Set(
      { slot: 1, hash: 46, parent: 42 },
      { slot: 1, hash: 47, parent: 45 },
      { slot: 2, hash: 48, parent: 43 },
      { slot: 2, hash: 49, parent: 45 },
    ),
    aliveSlots = 0.to(2),
    aliveHashes = 42.to(49),
  ).*
}

module too_many_byz_1 {
  // to violate agreement, run
  // quint run statemachine.qnt --main too_many_byz_1 --step oneSlotNoTimeout  --invariant agreement

  import consensus(
    correct = Set("v1", "v2", "v3", "v4"),
    good = Set(),
    byzantine = Set("b1"),
    power = Set("v1", "v2", "v3", "v4", "b1").mapBy(_ => 1), 
    correctBlocks = Set(
      { slot: 0, hash: 42, parent: -1 },
      { slot: 1, hash: 43, parent: 42 },
      { slot: 2, hash: 44, parent: 43 },
    ),
    byzantineBlocks = Set(
      { slot: 0, hash: 45, parent: -1 },
      { slot: 1, hash: 46, parent: 42 },
      { slot: 1, hash: 47, parent: 45 },
      { slot: 2, hash: 48, parent: 43 },
      { slot: 2, hash: 49, parent: 45 },
    ),
    aliveSlots = 0.to(2),
    aliveHashes = 42.to(49),
  ).*
}

module too_many_byz {
  // to violate agreement, run
  // quint run statemachine.qnt --main too_many_byz --step oneSlotNoTimeout --invariant agreement

  import consensus(
    correct = Set("v1", "v2", "v3", "v4"),
    good = Set(),
    byzantine = Set("b1", "b2"),
    power = Set("v1", "v2", "v3", "v4", "b1", "b2").mapBy(_ => 1), 
    correctBlocks = Set({ slot: 0, hash: 42, parent: -1 }),
    byzantineBlocks = Set({ slot: 0, hash: 41, parent: -1 }),
    aliveSlots = Set(0),
    aliveHashes = 41.to(42),
  ).*

  run disagreement_example_Test =
    init
    .then(receiveSpecificBlock("v3", { hash: 41, parent: -1, slot: 0 }))
    .then(receiveSpecificBlock("v4", { hash: 41, parent: -1, slot: 0 }))
    .expect(s.msgBuffer == 
      Set(  { msg: NotarVoteMsg({ hash: 41, slot: 0 }), sender: "v3" },
            { msg: NotarVoteMsg({ hash: 41, slot: 0 }), sender: "v4" }))
    .then(receiveSpecificBlock("v2", { hash: 42, parent: -1, slot: 0 }))
    .then(blockNotarizedAction("v3", 0))
    .then(blockNotarizedAction("v4", 0)) 
    .expect(
        Set(  { msg: FinalVoteMsg(0), sender: "v3" },
              { msg: FinalVoteMsg(0), sender: "v4" })
        .subseteq(s.msgBuffer))
    .then(receiveSpecificBlock("v1", { hash: 42, parent: -1, slot: 0 }))    
    .expect(not(agreement))
    .expect(
      Set(  { msg: NotarVoteMsg({ hash: 41, slot: 0 }), sender: "v3" },
            { msg: NotarVoteMsg({ hash: 41, slot: 0 }), sender: "v4" },
            { msg: NotarVoteMsg({ hash: 41, slot: 0 }), sender: "b1" },
            { msg: NotarVoteMsg({ hash: 41, slot: 0 }), sender: "b2" }, 
            { msg: NotarVoteMsg({ hash: 42, slot: 0 }), sender: "v1" },
            { msg: NotarVoteMsg({ hash: 42, slot: 0 }), sender: "v2" },
            { msg: NotarVoteMsg({ hash: 42, slot: 0 }), sender: "b1" },
            { msg: NotarVoteMsg({ hash: 42, slot: 0 }), sender: "b2" },
            { msg: FinalVoteMsg(0), sender: "v3" },
            { msg: FinalVoteMsg(0), sender: "v4" },
            { msg: FinalVoteMsg(0), sender: "b1" },
            { msg: FinalVoteMsg(0), sender: "b2" })
      .subseteq(allMessages))
}