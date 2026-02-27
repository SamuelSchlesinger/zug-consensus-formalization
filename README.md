# Zug

A Lean 4 formalization of the safety proof for the Zug Atomic Broadcast
protocol, from the paper [*From Weakly-terminating Binary Agreement and
Reliable Broadcast to Atomic
Broadcast*](https://arxiv.org/abs/2205.06314) (Fackler, Schlesinger,
Doty, 2022).

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

The **safety proof** is fully mechanized with zero `sorry`, zero
warnings, and zero errors.

### Theorems

- **Lemma 1** (`Monotonicity.lean`): Committed, skippable, accepted,
  and finalized are persistent in time and propagate to all correct
  nodes.
- **Lemma 2** (`Ordering.lean`): Finalized rounds at any correct node
  form a chain — any two are ancestors of each other.
- **Theorem 1** (`Theorem.lean`): Safety — all correct nodes produce the
  same output sequence (Agreement + Total Order).

### Module structure

```
Zug/
  Network.lean              -- Network config, quorum threshold, time
  Subprotocols.lean         -- RB/WBA specs (Agreement, Persistence)
  Protocol/
    Defs.lean               -- AcceptedAt, Ancestor, Finalized
  Safety/
    Monotonicity.lean       -- Lemma 1
    Ordering.lean           -- Lemma 2
    Theorem.lean            -- Theorem 1
```

### Design

- **RB and WBA are black boxes.** We axiomatize their Agreement and
  Persistence properties. The proof is parameterized over any
  implementations satisfying these specs.
- **Safety uses only Agreement**, not Validity or Weak Termination.
  No synchrony assumptions are needed.
- **No state machine.** Safety is proven purely from properties of
  subprotocol outputs, without modeling the reactive execution.

## Building

Requires [Lean 4](https://leanprover.github.io/lean4/doc/setup.html)
(see `lean-toolchain` for the exact version).

```
lake build
```

## Future work

- Liveness proof (Theorem 2: Censorship Resilience)
- Concrete RB/WBA implementations (Bracha's algorithm, gossip-based)
- Practical extensions (unknown δ, orphaned rounds)

## References

- A. Fackler, S. Schlesinger, M. Doty. *From Weakly-terminating Binary
  Agreement and Reliable Broadcast to Atomic Broadcast.* arXiv:2205.06314,
  2022.
