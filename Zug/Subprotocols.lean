/-
  Zug.Subprotocols: Specifications for Reliable Broadcast (RB) and
  Weakly-terminating Binary Agreement (WBA).

  These are axiomatized as structures with their required properties.
  The AB protocol is parameterized over any implementations satisfying
  these specs.

  For safety, only Agreement + Persistence are needed (Part 1).
  For liveness, we additionally assume timed delay and weak termination
  bounds that hold after GST (Part 2).
-/

import Zug.Network

namespace Zug

/-- Node identifier. -/
abbrev NodeId := Nat

/-- A predicate identifying which nodes are correct (not faulty). -/
abbrev Correctness := NodeId → Prop

/-! ## Reliable Broadcast (RB)

  RB has a designated proposer. If the proposer is correct and provides
  input v, all correct nodes eventually output v. If any correct node
  outputs v, all correct nodes eventually output v.

  For safety, we only need the Agreement property.
  For liveness, we additionally need delay bounds.
-/

/-- The output that a node observes from an RB instance at a given time.
    `none` means no output yet. -/
structure RBView (V : Type) where
  /-- What node N has observed as RB output at time t. -/
  output_at : NodeId → Time → Option V

/-- RB Agreement: if one correct node outputs v, all correct nodes
    eventually output the same v. Outputs are persistent. -/
structure RBAgreement {V : Type} (correct : Correctness)
    (view : RBView V) : Prop where
  /-- Outputs are persistent: once seen, always seen. -/
  persistent : ∀ N t v, correct N → view.output_at N t = some v →
    ∀ t', t ≤ t' → view.output_at N t' = some v
  /-- Agreement: if N outputs v, N' eventually outputs v. -/
  agreement : ∀ N N' t v, correct N → correct N' →
    view.output_at N t = some v →
    ∃ t', view.output_at N' t' = some v

/-! ## Weakly-terminating Binary Agreement (WBA)

  WBA takes single-bit inputs (0 or 1) from validators and produces
  at most one output bit. Agreement says all correct nodes that output
  agree on the bit.
-/

/-- The view of a WBA instance: what each node sees at each time. -/
structure WBAView where
  /-- What node N has observed as WBA output at time t.
      `none` means no output yet. `some true` = 1, `some false` = 0. -/
  output_at : NodeId → Time → Option Bool

/-- WBA Agreement: all correct nodes that output agree on the bit,
    and outputs are persistent. -/
structure WBAAgreement (correct : Correctness) (view : WBAView) : Prop where
  /-- Outputs are persistent. -/
  persistent : ∀ N t b, correct N → view.output_at N t = some b →
    ∀ t', t ≤ t' → view.output_at N t' = some b
  /-- Agreement: if N outputs b, N' eventually outputs b (same bit). -/
  agreement : ∀ N N' t b, correct N → correct N' →
    view.output_at N t = some b →
    ∃ t', view.output_at N' t' = some b

/-! ## Protocol-level view of subprotocol outputs

  The AB protocol indexes RB and WBA instances by round number.
  We bundle the per-round views and their agreement properties.
-/

/-- The value type for RB in the Zug protocol: pairs (v, s) where
    v is the proposed value and s is the parent round (none = ⊥). -/
structure Proposal (V : Type) where
  value : V
  parent : Option Nat

/-- All subprotocol views for the entire protocol execution. -/
structure SubprotocolViews (V : Type) where
  /-- RB view for each round. -/
  rb : Nat → RBView (Proposal V)
  /-- WBA view for each round. -/
  wba : Nat → WBAView

/-- The agreement properties we assume for all subprotocol instances.
    These are sufficient for the safety proof (Theorem 1). -/
structure SubprotocolAgreement (V : Type) (correct : Correctness)
    (views : SubprotocolViews V) : Prop where
  /-- Every RB instance satisfies agreement. -/
  rb_agreement : ∀ r : Nat, RBAgreement correct (views.rb r)
  /-- Every WBA instance satisfies agreement. -/
  wba_agreement : ∀ r : Nat, WBAAgreement correct (views.wba r)

/-! ## Timed subprotocol properties (for liveness)

  These extend the safety-only Agreement properties with timing guarantees
  that hold after GST. They are separate structures so the safety proof
  remains untouched.
-/

/-- RB Timed Delay: if any correct node outputs v at time t ≥ GST,
    all correct nodes output v by t + Δ.

    This is a standard property of RB in the partial synchrony model:
    after GST, message delivery is bounded by Δ. -/
structure RBTimedDelay {V : Type} (correct : Correctness)
    (view : RBView V) (gst delta : Time) : Prop where
  timed_delay : ∀ N N' t v, correct N → correct N' →
    gst ≤ t → view.output_at N t = some v →
    view.output_at N' (t + delta) = some v

/-- WBA Timed Delay: if any correct node outputs b at time t ≥ GST,
    all correct nodes output b by t + Δ.

    Analogous to RBTimedDelay for binary agreement outputs. -/
structure WBATimedDelay (correct : Correctness)
    (view : WBAView) (gst delta : Time) : Prop where
  timed_delay : ∀ N N' t b, correct N → correct N' →
    gst ≤ t → view.output_at N t = some b →
    view.output_at N' (t + delta) = some b

/-- WBA Timed Weak Termination: if all correct nodes provide the same
    input bit b by time t ≥ GST, all correct nodes output b by t + Δ.

    The `input_at` function records when each node provided its input
    to this WBA instance: `input_at N = some (time, bit)`. -/
structure WBATimedWeakTermination (correct : Correctness)
    (view : WBAView) (gst delta : Time)
    (input_at : NodeId → Option (Time × Bool)) : Prop where
  weak_termination : ∀ t b,
    gst ≤ t →
    (∀ N, correct N → ∃ ti, ti ≤ t ∧ input_at N = some (ti, b)) →
    ∀ N', correct N' → view.output_at N' (t + delta) = some b

end Zug
