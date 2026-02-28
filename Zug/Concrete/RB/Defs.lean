/-
  Zug.Concrete.RB.Defs: Bracha Reliable Broadcast — messages,
  behavior axioms, and output definition.

  Messages: initial v | echo v | ready v
  Thresholds (standard Bracha):
    - Echo: triggered by (initial, v) from proposer
    - Ready: triggered by > q echoes for v, OR > f readies for v
    - Output: triggered by > 2f readies for v
-/

import Zug.Concrete.Quorum

namespace Zug.Concrete.RB

open Zug

/-- Messages in the Bracha RB protocol. -/
inductive Msg (V : Type) where
  | initial (v : V)
  | echo (v : V)
  | ready (v : V)

/-- An RB instance bundles configuration, network, and proposer. -/
structure RBInstance (V : Type) where
  cfg : NetworkConfig
  correct : Correctness
  net : PtPNetwork (Msg V)
  proposer : NodeId
  gst : Time
  delta_net : Time

/-- Behavior axioms for correct nodes in a Bracha RB instance.
    These capture what correct nodes do without modeling internal state. -/
structure RBBehavior {V : Type} (inst : RBInstance V) (qa : QuorumAxioms inst.cfg inst.correct)
    (np : NetworkProperties (Msg V) inst.correct inst.net inst.gst inst.delta_net) : Prop where
  /-- Correct nodes echo at most one value. -/
  echo_unique : ∀ N t₁ t₂ v₁ v₂, inst.correct N →
    inst.net.sent N (Msg.echo v₁) t₁ →
    inst.net.sent N (Msg.echo v₂) t₂ →
    v₁ = v₂
  /-- Correct nodes send ready for at most one value. -/
  ready_unique : ∀ N t₁ t₂ v₁ v₂, inst.correct N →
    inst.net.sent N (Msg.ready v₁) t₁ →
    inst.net.sent N (Msg.ready v₂) t₂ →
    v₁ = v₂
  /-- On receiving initial from proposer, a correct node echoes it. -/
  echo_triggered : ∀ N t v, inst.correct N →
    inst.net.received N inst.proposer (Msg.initial v) t →
    ∃ t', t' ≤ t ∧ inst.net.sent N (Msg.echo v) t'
  /-- On receiving > q echoes for v, a correct node sends ready. -/
  ready_from_echo_quorum : ∀ N t v, inst.correct N →
    MoreThan inst.cfg.q inst.cfg.n
      (fun S => inst.net.received N S (Msg.echo v) t) →
    ∃ t', t' ≤ t ∧ inst.net.sent N (Msg.ready v) t'
  /-- On receiving > f readies for v, a correct node sends ready
      (amplification step). -/
  ready_from_ready_amplify : ∀ N t v, inst.correct N →
    MoreThan inst.cfg.f inst.cfg.n
      (fun S => inst.net.received N S (Msg.ready v) t) →
    ∃ t', t' ≤ t ∧ inst.net.sent N (Msg.ready v) t'
  /-- A correct proposer sends initial. -/
  proposer_sends : ∀ v, inst.correct inst.proposer →
    (∃ t, inst.net.sent inst.proposer (Msg.initial v) t) →
    ∀ t', (∃ t, t ≤ t' ∧ inst.net.sent inst.proposer (Msg.initial v) t) →
    True  -- placeholder; actual content is in proposer_initial below
  /-- A correct proposer sends initial for exactly one value. -/
  proposer_initial : inst.correct inst.proposer →
    ∃ v t, inst.net.sent inst.proposer (Msg.initial v) t

/-- Node N has RB output v at time t: it has received > 2f readies for v. -/
def HasRBOutput {V : Type} (inst : RBInstance V) (N : NodeId) (t : Time) (v : V) : Prop :=
  MoreThan (2 * inst.cfg.f) inst.cfg.n
    (fun S => inst.net.received N S (Msg.ready v) t)

/-- HasRBOutput is persistent (follows from receipt_persistent). -/
theorem hasRBOutput_persistent {V : Type} {inst : RBInstance V}
    (np : NetworkProperties (Msg V) inst.correct inst.net inst.gst inst.delta_net)
    {N : NodeId} {t t' : Time} {v : V}
    (h : HasRBOutput inst N t v) (hle : t ≤ t') :
    HasRBOutput inst N t' v :=
  h.mono (fun S hrec => np.receipt_persistent N S _ t t' hrec hle)

/-- If a correct node has HasRBOutput for two values, they are equal.
    Proof: > 2f readied v₁ and > 2f readied v₂. By super_majority_intersection,
    some correct C is in both. By no_forgery, C sent ready v₁ and ready v₂.
    By ready_unique, v₁ = v₂. -/
theorem hasRBOutput_unique {V : Type} {inst : RBInstance V}
    {qa : QuorumAxioms inst.cfg inst.correct}
    {np : NetworkProperties (Msg V) inst.correct inst.net inst.gst inst.delta_net}
    (beh : RBBehavior inst qa np)
    {N : NodeId} {t₁ t₂ : Time} {v₁ v₂ : V}
    (hN : inst.correct N)
    (h₁ : HasRBOutput inst N t₁ v₁)
    (h₂ : HasRBOutput inst N t₂ v₂) :
    v₁ = v₂ := by
  -- Persist both to max t₁ t₂
  have h₁' := hasRBOutput_persistent np h₁ (Nat.le_max_left t₁ t₂)
  have h₂' := hasRBOutput_persistent np h₂ (Nat.le_max_right t₁ t₂)
  -- Both have > 2f senders; find a correct node in the intersection
  obtain ⟨C, hC_correct, hC_v₁, hC_v₂⟩ := qa.super_majority_intersection h₁' h₂'
  -- By no_forgery, C actually sent ready v₁ and ready v₂
  obtain ⟨ts₁, _, hsent₁⟩ := np.no_forgery C N (Msg.ready v₁) _ hC_correct hN hC_v₁
  obtain ⟨ts₂, _, hsent₂⟩ := np.no_forgery C N (Msg.ready v₂) _ hC_correct hN hC_v₂
  exact beh.ready_unique C ts₁ ts₂ v₁ v₂ hC_correct hsent₁ hsent₂

/-- Construct an RBView from a concrete RB instance.
    Uses Classical.choose to pick the unique output value. -/
noncomputable def mkRBView {V : Type} (inst : RBInstance V) : RBView V where
  output_at N t :=
    open Classical in
    if h : ∃ v, HasRBOutput inst N t v then
      some (Classical.choose h)
    else
      none

end Zug.Concrete.RB
