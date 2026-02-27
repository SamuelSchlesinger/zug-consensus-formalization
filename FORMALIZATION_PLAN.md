# Formalization of the Zug Protocol in Lean 4

This project formalizes the safety proof of the paper *"From Weakly-terminating
Binary Agreement and Reliable Broadcast to Atomic Broadcast"* (Fackler,
Schlesinger, Doty, 2022) in Lean 4.

The paper presents a modular Atomic Broadcast (AB) protocol built from two
subprotocols — Reliable Broadcast (RB) and Weakly-terminating Binary Agreement
(WBA). Safety is proven without synchrony assumptions; liveness requires partial
synchrony.

---

## Completed: Safety Proof (Theorem 1)

The safety proof is fully formalized with **zero `sorry`**, zero warnings,
and zero errors. It consists of ~980 lines of Lean 4 across 6 files.

### Module structure

```
Zug/
  Network.lean              -- Network config, quorum threshold, time model
  Subprotocols.lean         -- RB and WBA specs (Agreement, Persistence)
  Protocol/
    Defs.lean               -- AcceptedAt, Ancestor, Finalized definitions
  Safety/
    Monotonicity.lean       -- Lemma 1: persistence + cross-node propagation
    Ordering.lean           -- Lemma 2: finalized rounds form a chain
    Theorem.lean            -- Theorem 1: Safety (Agreement + Total Order)
```

### Proven theorems

| Theorem | File | Description |
|---------|------|-------------|
| `finalized_are_ancestors` | `Ordering.lean` | **Lemma 2**: Finalized rounds at a single node are ancestors of each other |
| `safety_total_order` | `Theorem.lean` | **Theorem 1a**: Finalized rounds form a total order |
| `safety_agreement` | `Theorem.lean` | **Theorem 1b**: All correct nodes finalize the same rounds |
| `finalized_value_agreement` | `Theorem.lean` | The value in each finalized round agrees across nodes |

### Key auxiliary lemmas

| Lemma | File | Description |
|-------|------|-------------|
| `committed_persistent` | `Monotonicity.lean` | Committed/skippable/accepted/finalized are persistent in time |
| `committed_propagates` | `Monotonicity.lean` | These properties propagate to all correct nodes |
| `not_committed_and_skippable` | `Ordering.lean` | A round cannot be both committed and skippable |
| `rb_output_unique` | `Ordering.lean` | RB outputs are unique per correct node |
| `committed_is_ancestor_of_accepted` | `Ordering.lean` | A committed round below an accepted round is in its ancestor chain |
| `ancestors_of_accepted_comparable` | `Ordering.lean` | Two ancestors of the same accepted round are comparable |
| `accepted_at_propagates` | `Theorem.lean` | AcceptedAt propagates across correct nodes |
| `finite_persistent_choice` | `Theorem.lean` | Finitely many persistent existentials can be combined at one time |

### Design decisions

1. **RB and WBA as black boxes**: We axiomatize their Agreement and Persistence
   properties via structures (`RBAgreement`, `WBAAgreement`). The protocol is
   parameterized over any `SubprotocolViews` satisfying `SubprotocolAgreement`.

2. **Combined `AcceptedAt` inductive**: The paper defines `fertile` and
   `accepted` as mutually recursive functions. Lean 4's kernel rejects mutual
   inductives with existentials in constructors, so we combined them into a
   single inductive `AcceptedAt` with two constructors (`mk_bot` and
   `mk_parent`). The `Fertile` definition is then derived as a `def`.

3. **No state machine for safety**: Safety is proven purely from the properties
   of subprotocol outputs, without modeling the reactive execution. This
   matches the paper's structure and dramatically simplifies the formalization.

4. **Safety uses only Agreement, not Validity**: Confirmed during formalization
   that the safety proof requires only WBA/RB Agreement and Persistence — not
   WBA Validity or Weak Termination. These are needed only for liveness.

### Observations about the paper

- **No bugs found.** The paper's proofs are correct.
- **Lemma 2's proof is compressed** but sound. The paper's one-paragraph
  minimality argument expands into three key lemmas in the formalization
  (`committed_is_ancestor_of_accepted`, `ancestor_of_accepted_goes_to_parent`,
  `ancestors_of_accepted_comparable`). Induction on AcceptedAt structure was
  more natural than the paper's explicit minimality argument.
- **The `finalize` function's termination** depends on the protocol invariant
  that it is only called on accepted rounds (guaranteeing parent < round).
  This is implicit in the pseudocode.

---

## Future Work: Liveness Proof (Theorem 2)

The liveness proof (Censorship Resilience) is not yet formalized. It requires:

### Additional infrastructure needed

1. **State machine model** (`Protocol/Algorithm.lean`): Model each node's
   execution as a labeled transition system with timer behavior.

2. **Partial synchrony reasoning**: After GST, messages arrive within δ.
   Need to model the causal chain: timer fires → WBA input → WBA output →
   round advance → next timer.

3. **Leader sequence**: Axiomatize that every proposer leads infinitely many
   rounds.

### Theorems to prove

| Theorem | Description | Difficulty |
|---------|-------------|------------|
| **Lemma 3** | After GST, rounds progress at rate ≤ 3Δ per round | High |
| **Lemma 4** | Correct leaders after GST get their rounds committed | High |
| **Theorem 2** | Every input to a correct proposer is eventually output | Medium |

### Estimated effort

Liveness proofs in distributed systems are significantly harder to mechanize
than safety proofs. The interaction between time, events, and multiple nodes
introduces substantial proof obligations. This is a natural second milestone.

---

## Out of Scope

- **Concrete implementations** (Section 6): Bracha's RB, gossip-based WBA
- **Practical extensions** (Section 7): unknown δ, orphaned rounds, validation,
  spam resistance, minimum delays
