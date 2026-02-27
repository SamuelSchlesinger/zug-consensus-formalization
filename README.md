# Zug

A Lean 4 formalization of the safety and liveness proofs for the Zug
Atomic Broadcast protocol, from the paper [*From Weakly-terminating
Binary Agreement and Reliable Broadcast to Atomic
Broadcast*](https://arxiv.org/abs/2205.06314) (Fackler, Schlesinger,
Doty, 2022).

**Status:** Both Theorem 1 (Safety) and Theorem 2 (Liveness /
Censorship Resilience) are fully mechanized with zero `sorry`, zero
warnings, and zero errors. ~1,450 lines of Lean 4 across 12 files.

## What is Zug?

Zug is an Atomic Broadcast (AB) protocol that reduces AB to two
subprotocols:

- **Reliable Broadcast (RB)**: ensures all correct nodes receive the
  same proposed value.
- **Weakly-terminating Binary Agreement (WBA)**: a relaxation of Binary
  Agreement that does not guarantee termination in all cases, admitting
  simpler implementations.

The protocol proceeds in rounds. Each round has a designated leader who
proposes a value via RB, and validators vote on whether to commit the
round via WBA. Safety (agreement on the output sequence) holds without
any synchrony assumptions. Liveness (censorship resilience) requires
partial synchrony.

## What is formalized

### Safety (Theorem 1)

The safety proof shows that all correct nodes produce the same output
sequence. It requires only the Agreement and Persistence properties of
RB and WBA — no synchrony, no state machine.

- **Lemma 1** (`Safety/Monotonicity.lean`): Committed, skippable,
  accepted, and finalized are persistent in time and propagate to all
  correct nodes.
- **Lemma 2** (`Safety/Ordering.lean`): Finalized rounds at any correct
  node form a chain — any two are ancestors of each other.
- **Theorem 1** (`Safety/Theorem.lean`): All correct nodes eventually
  finalize the same rounds (Agreement + Total Order).

### Liveness (Theorem 2)

The liveness proof shows censorship resilience: every correct proposer
eventually has a round committed. It requires partial synchrony
(bounded message delay Δ after GST) and timed properties of the
subprotocols.

- **Lemma 1.3** (`Liveness/TimedPropagation.lean`): After GST, all
  predicates (skippable, accepted, reached round) propagate from any
  correct node to all correct nodes within Δ.
- **Lemma 3** (`Liveness/RoundProgress.lean`): At time GST + 3rΔ, every
  correct node has reached round r.
- **Lemma 4** (`Liveness/CorrectLeader.lean`): If a round has a correct
  leader, it is committed at all correct nodes within 3Δ of all
  correct nodes reaching that round.
- **Theorem 2** (`Liveness/Theorem.lean`): For every correct node and
  every round, there exists a later round where that node is leader and
  the round is finalized at all correct nodes.

## Module structure

```
Zug/
  Network.lean                 -- Network config, quorum threshold, partial synchrony
  Subprotocols.lean            -- RB/WBA specs: Agreement, Persistence, Timed Delay,
                               --   Weak Termination
  Protocol/
    Defs.lean                  -- Core definitions: AcceptedAt, Ancestor, Finalized
    Execution.lean             -- Execution model: ReachedRound, LeaderSequence,
                               --   ExecutionContext, ProtocolBehavior
  Safety/
    Monotonicity.lean          -- Lemma 1: persistence + propagation
    Ordering.lean              -- Lemma 2: finalized rounds form a chain
    Theorem.lean               -- Theorem 1: safety (agreement + total order)
  Liveness/
    TimedPropagation.lean      -- Lemma 1.3: timed propagation within Δ
    RoundProgress.lean         -- Lemma 3: round progress (GST + 3rΔ)
    CorrectLeader.lean         -- Lemma 4: correct leaders get committed
    Theorem.lean               -- Theorem 2: censorship resilience
```

Dependency graph:

```
Network ← Subprotocols ← Protocol/Defs ← Safety/Monotonicity ← Safety/Ordering ← Safety/Theorem
                                              ↓
                                      Protocol/Execution ← Liveness/TimedPropagation
                                                               ↓
                                                    Liveness/RoundProgress
                                                               ↓
                                                    Liveness/CorrectLeader
                                                               ↓
                                          Safety/Theorem → Liveness/Theorem
```

## Design

### Axiomatized subprotocols

RB and WBA are axiomatized as black boxes. We never model their
internals. Instead, we assume:

**For safety** (`SubprotocolAgreement`):
- *Persistence:* once a correct node sees an output, it sees it forever.
- *Agreement:* if one correct node outputs v, all correct nodes
  eventually output v.

**For liveness** (additional timed properties in `ProtocolBehavior`):
- *RB Timed Delay:* after GST, RB outputs propagate within Δ.
- *WBA Timed Delay:* after GST, WBA outputs propagate within Δ.
- *WBA Weak Termination:* if all correct nodes input the same bit by
  time t ≥ GST, all output that bit by t + Δ.

### Axiomatized protocol behavior

Rather than building a reactive state machine, the liveness proof
axiomatizes the *observable consequences* of protocol execution via
the `ProtocolBehavior` structure. This mirrors the approach used for
safety and keeps the formalization tractable.

The 7 axioms in `ProtocolBehavior` capture:

| # | Axiom | Justification |
|---|-------|---------------|
| 1 | RB timed delay | Subprotocol property |
| 2 | WBA timed delay | Subprotocol property |
| 3 | WBA timed weak termination | Subprotocol property |
| 4 | Correct nodes start before GST | Protocol assumption |
| 5 | Timer: 2Δ without acceptance → input 0 to WBA | Protocol pseudocode (§5.3) |
| 6 | Vote: accepted value → input 1 to WBA | Protocol pseudocode (§5.3) |
| 7 | Leader proposal: correct leader → all accepted within Δ | Combines leader construction, RB delivery, timed propagation |

### Key proof techniques

- **Strong induction on round number** (Lemma 3): each round settles
  within 3Δ of all correct nodes reaching it.
- **Case analysis** (round settling): either some correct node accepts
  (propagates to all) or none does (timer fires, WBA skips).
- **`finite_persistent_choice`** (Safety/Theorem.lean): if finitely many
  persistent predicates each hold at some time, they all hold
  simultaneously at some time.
- **Nat arithmetic without omega**: Lean 4's `omega` tactic cannot see
  through nested struct field projections (`ctx.sync.delta`). We use
  explicit `Nat.add_assoc`, `Nat.succ_mul`, `Nat.mul_le_mul_right`,
  and helper lemmas instead.

## Building

Requires [Lean 4](https://leanprover.github.io/lean4/doc/setup.html)
(see `lean-toolchain` for the exact version).

```
lake build
```

## Future work

- Concrete RB/WBA implementations (Bracha's algorithm, gossip-based WBA)
- Practical extensions (unknown Δ, orphaned rounds, validation, spam
  resistance)

## References

- A. Fackler, S. Schlesinger, M. Doty. *From Weakly-terminating Binary
  Agreement and Reliable Broadcast to Atomic Broadcast.*
  [arXiv:2205.06314](https://arxiv.org/abs/2205.06314), 2022.
