# Zug

A Lean 4 formalization of the safety and liveness proofs for the Zug
Atomic Broadcast protocol, from the paper [*From Weakly-terminating
Binary Agreement and Reliable Broadcast to Atomic
Broadcast*](https://arxiv.org/abs/2205.06314) (Fackler, Schlesinger,
Doty, 2022).

**Status:** The full Atomic Broadcast correctness theorem is mechanized
with zero `sorry`, zero warnings, and zero errors. ~2,800 lines of
Lean 4 across 21 files, zero external dependencies.

## What is Zug?

Zug is an Atomic Broadcast (AB) protocol that reduces AB to two
subprotocols:

- **Reliable Broadcast (RB):** ensures all correct nodes receive the
  same proposed value.
- **Weakly-terminating Binary Agreement (WBA):** a relaxation of Binary
  Agreement that does not guarantee termination in all cases, admitting
  simpler implementations.

The protocol proceeds in rounds. Each round has a designated leader who
proposes a value via RB, and validators vote on whether to commit the
round via WBA. Safety (agreement on the output sequence) holds without
any synchrony assumptions. Liveness (censorship resilience) requires
partial synchrony.

## Main result

The formalization proves that Zug is a correct Atomic Broadcast
protocol: all correct nodes produce the same totally-ordered output
sequence, and every correct proposer's values eventually appear in it.

This is captured by `atomic_broadcast_correctness`: for every correct
proposer L and every starting round, there exists a later round r where
L is leader and **every correct node finalizes r with the same
RB-delivered value**.

The proof combines two complementary theorems:

- **Safety (Theorem 1):** All correct nodes finalize the same rounds in
  the same order and agree on each round's value. Requires only
  agreement and persistence of RB/WBA — no synchrony assumptions.
- **Liveness (Theorem 2):** Every correct proposer eventually has a
  round committed and finalized at all correct nodes. Requires partial
  synchrony (bounded message delay Δ after GST).

The abstract proof is parameterized over any RB and WBA satisfying a
small set of axioms. The `Concrete/` layer then verifies Bracha's RB and
a WBA protocol against this interface, deriving the required properties
from a standard Byzantine fault model (n > 3f).

## Module structure

```
Zug/
├── Network.lean               — Time type and partial synchrony parameters
├── Subprotocols.lean          — RB/WBA abstract specs (agreement, persistence, timed delay)
├── Protocol/
│   ├── Defs.lean              — Core definitions: AcceptedAt, Ancestor, Finalized, RBOutput
│   └── Execution.lean         — Execution model: ReachedRound, LeaderSequence, ProtocolBehavior
├── Safety/
│   ├── Monotonicity.lean      — Persistence and cross-node propagation
│   ├── Ordering.lean          — Finalized rounds form a chain
│   └── Theorem.lean           — Theorem 1: agreement, total order, validity
├── Liveness/
│   ├── TimedPropagation.lean  — Timed propagation within Δ after GST
│   ├── RoundProgress.lean     — All correct nodes reach round r by GST + 3rΔ
│   ├── CorrectLeader.lean     — Correct leaders get committed within 3Δ
│   └── Theorem.lean           — Theorem 2 + capstone: atomic_broadcast_correctness
└── Concrete/
    ├── Network.lean           — Point-to-point network axioms
    ├── Quorum.lean            — Quorum predicates and axioms
    ├── FaultModel.lean        — n > 3f derives quorum properties
    ├── RB/                    — Bracha Reliable Broadcast
    ├── WBA/                   — WBA protocol
    └── Instantiation.lean     — Wires concrete subprotocols into ProtocolBehavior
```

## Building

Requires [Lean 4](https://leanprover.github.io/lean4/doc/setup.html)
(see `lean-toolchain` for the exact version).

```
lake build
```

## Design

See [DESIGN.md](DESIGN.md) for the axiomatization approach, the full
axiom table, concrete subprotocol details, and proof techniques.

## Future work

- Practical extensions (unknown Δ, orphaned rounds, validation, spam
  resistance)
- Verified executable implementation (extracting to a runnable node)

## References

- A. Fackler, S. Schlesinger, M. Doty. *From Weakly-terminating Binary
  Agreement and Reliable Broadcast to Atomic Broadcast.*
  [arXiv:2205.06314](https://arxiv.org/abs/2205.06314), 2022.
