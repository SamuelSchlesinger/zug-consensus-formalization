# Formalization Design

Design decisions and proof techniques for the Zug formalization.
For the high-level overview, see [README.md](README.md).

## Two-layer architecture

The formalization has two layers:

1. **Abstract layer** (`Safety/`, `Liveness/`): proves safety and
   liveness assuming RB and WBA satisfy a small axiom set. This mirrors
   the paper's proof structure, where the theorems hold for *any*
   conforming subprotocol implementations.
2. **Concrete layer** (`Concrete/`): verifies specific implementations
   of Bracha's RB and a WBA protocol, discharging the abstract axioms
   from a Byzantine fault model (n > 3f).

This separation means the core safety/liveness proofs are reusable —
swapping in a different RB or WBA implementation requires only proving
the axioms, not re-verifying the protocol.

## Dependency graph

```
Network ← Subprotocols ← Protocol/Defs
                               ↓
                     Safety/Monotonicity
                          ↓         ↓
               Safety/Ordering   Protocol/Execution
                    ↓                  ↓
               Safety/Theorem   Liveness/TimedPropagation
                    ↓                  ↓
                    ↓            Liveness/RoundProgress
                    ↓                  ↓
                    ↓            Liveness/CorrectLeader
                    ↓                  ↓
                    └──→ Liveness/Theorem ←──┘
                                         ↑
                              Concrete/Instantiation
                               ↑         ↑        ↑
                          Concrete/   Concrete/  Concrete/
                            RB/*       WBA/*    FaultModel
                               ↑         ↑        ↑
                          Concrete/   Concrete/  Concrete/
                          Network     Network    Quorum
```

## Axiomatized subprotocols

Rather than fixing a specific RB or WBA algorithm for the main proofs,
we axiomatize the properties that the safety and liveness arguments
actually use. This keeps the proof close to the paper and makes the
guarantees independent of any particular implementation.

**For safety** (`SubprotocolAgreement`):
- *Persistence:* once a correct node sees an output, it sees it forever.
- *Agreement:* if one correct node outputs v, all correct nodes
  eventually output v.

**For liveness** (additional timed properties in `ProtocolBehavior`):
- *RB Timed Delay:* after GST, RB outputs propagate within Δ.
- *WBA Timed Delay:* after GST, WBA outputs propagate within Δ.
- *WBA Weak Termination:* if all correct nodes input the same bit by
  time t ≥ GST, all output that bit by t + Δ.

## Axiomatized protocol behavior

Rather than building a reactive state machine, the liveness proof
axiomatizes the *observable consequences* of protocol execution via
the `ProtocolBehavior` structure. This keeps the formalization
tractable: we reason about what correct nodes eventually observe, not
about message-level state transitions.

The 7 axioms in `ProtocolBehavior`:

| # | Axiom | Justification |
|---|-------|---------------|
| 1 | RB timed delay | Subprotocol property |
| 2 | WBA timed delay | Subprotocol property |
| 3 | WBA timed weak termination | Subprotocol property |
| 4 | Correct nodes start before GST | Protocol assumption |
| 5 | Timer: 2Δ without acceptance → input 0 to WBA | Protocol pseudocode (§5.3) |
| 6 | Vote: accepted value → input 1 to WBA | Protocol pseudocode (§5.3) |
| 7 | Leader proposal: correct leader → all accepted within Δ | Combines leader construction, RB delivery, timed propagation |

Axioms 1–3 are discharged by the concrete subprotocol implementations.
Axioms 4–7 remain as protocol-level assumptions.

## Concrete subprotocols

The `Concrete/` layer provides verified implementations that discharge
axioms 1–3.

- **Network model** (`Network.lean`): point-to-point authenticated
  channels with four axioms — bounded delay, eventual delivery, no
  forgery, and receipt persistence.
- **Fault model** (`FaultModel.lean`): given n nodes with at most f
  Byzantine and n > 3f, derives quorum intersection and related
  properties via classical counting.
- **Bracha RB** (`RB/`): the standard echo-ready protocol. Proves
  agreement, persistence, and timed delay with δ = 3Δ\_net.
- **WBA** (`WBA/`): a vote-ready protocol. Proves agreement,
  persistence, timed delay, and weak termination with δ = 3Δ\_net.
- **Instantiation** (`Instantiation.lean`): assembles the concrete
  proofs into a `SubprotocolAgreement` and the timed-delay/termination
  fields of `ProtocolBehavior`.

## Proof techniques

### Conceptual

- **Strong induction on round number** (Lemma 3): each round settles
  within 3Δ of all correct nodes reaching it, giving the GST + 3rΔ
  bound.
- **Case analysis on round settling**: either some correct node accepts
  (which propagates to all) or none does (timer fires, WBA outputs
  skip). Both cases resolve the round.
- **Finite persistent choice** (`Safety/Theorem.lean`): if finitely many
  persistent predicates each hold at some time, there exists a single
  time at which all hold simultaneously. Used to synchronize witnesses
  across rounds and nodes.
- **Classical counting** (`FaultModel.lean`): quorum intersection follows
  from inclusion-exclusion on complement counts. The `countSat`
  function counts elements of `{0, …, n-1}` satisfying a decidable
  predicate.

### Lean-specific

- **Nat arithmetic without omega**: Lean 4's `omega` tactic cannot see
  through nested struct field projections (e.g., `ctx.sync.delta`). We
  use explicit lemmas (`Nat.add_assoc`, `Nat.succ_mul`,
  `Nat.mul_le_mul_right`, etc.) throughout the liveness proofs.
