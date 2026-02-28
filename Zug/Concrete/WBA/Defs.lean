/-
  Zug.Concrete.WBA.Defs: Weakly-terminating Binary Agreement —
  messages, behavior axioms, and output definition.

  Messages: vote b | ready b
  Thresholds (generalized for n > 3f):
    - Vote: triggered by input b, OR > f votes for b, OR > f readies for b
    - Ready: triggered by > q votes for b, OR > f readies for b
    - Output: triggered by > q readies for b
-/

import Zug.Concrete.Quorum

namespace Zug.Concrete.WBA

open Zug

/-- Messages in the WBA protocol. -/
inductive Msg where
  | vote (b : Bool)
  | ready (b : Bool)

/-- A WBA instance bundles configuration, network, and input tracking. -/
structure WBAInstance where
  cfg : NetworkConfig
  correct : Correctness
  net : PtPNetwork Msg
  gst : Time
  delta_net : Time
  /-- Input tracking: when each node provided its input bit. -/
  input_at : NodeId → Option (Time × Bool)

/-- Behavior axioms for correct nodes in a WBA instance. -/
structure WBABehavior (inst : WBAInstance) (qa : QuorumAxioms inst.cfg inst.correct)
    (np : NetworkProperties Msg inst.correct inst.net inst.gst inst.delta_net) : Prop where
  /-- Correct nodes vote for at most one value. -/
  vote_unique : ∀ N t₁ t₂ b₁ b₂, inst.correct N →
    inst.net.sent N (Msg.vote b₁) t₁ →
    inst.net.sent N (Msg.vote b₂) t₂ →
    b₁ = b₂
  /-- Correct nodes send ready for at most one value. -/
  ready_unique : ∀ N t₁ t₂ b₁ b₂, inst.correct N →
    inst.net.sent N (Msg.ready b₁) t₁ →
    inst.net.sent N (Msg.ready b₂) t₂ →
    b₁ = b₂
  /-- On receiving input b, a correct node votes b. -/
  vote_from_input : ∀ N t b, inst.correct N →
    inst.input_at N = some (t, b) →
    ∃ t', t' ≤ t ∧ inst.net.sent N (Msg.vote b) t'
  /-- On receiving > f votes for b, a correct node votes b. -/
  vote_from_vote_amplify : ∀ N t b, inst.correct N →
    MoreThan inst.cfg.f inst.cfg.n
      (fun S => inst.net.received N S (Msg.vote b) t) →
    ∃ t', t' ≤ t ∧ inst.net.sent N (Msg.vote b) t'
  /-- On receiving > q votes for b, a correct node sends ready. -/
  ready_from_vote_quorum : ∀ N t b, inst.correct N →
    MoreThan inst.cfg.q inst.cfg.n
      (fun S => inst.net.received N S (Msg.vote b) t) →
    ∃ t', t' ≤ t ∧ inst.net.sent N (Msg.ready b) t'
  /-- On receiving > f readies for b, a correct node sends ready
      (amplification step). -/
  ready_from_ready_amplify : ∀ N t b, inst.correct N →
    MoreThan inst.cfg.f inst.cfg.n
      (fun S => inst.net.received N S (Msg.ready b) t) →
    ∃ t', t' ≤ t ∧ inst.net.sent N (Msg.ready b) t'

/-- Node N has WBA output b at time t: received > q readies for b,
    where q = (n + f) / 2. For n = 3f + 1 this equals 2f. -/
def HasWBAOutput (inst : WBAInstance) (N : NodeId) (t : Time) (b : Bool) : Prop :=
  MoreThan inst.cfg.q inst.cfg.n
    (fun S => inst.net.received N S (Msg.ready b) t)

/-- HasWBAOutput is persistent. -/
theorem hasWBAOutput_persistent {inst : WBAInstance}
    (np : NetworkProperties Msg inst.correct inst.net inst.gst inst.delta_net)
    {N : NodeId} {t t' : Time} {b : Bool}
    (h : HasWBAOutput inst N t b) (hle : t ≤ t') :
    HasWBAOutput inst N t' b :=
  h.mono (fun S hrec => np.receipt_persistent N S _ t t' hrec hle)

/-- Output uniqueness: if correct N outputs b₁ and b₂, then b₁ = b₂. -/
theorem hasWBAOutput_unique {inst : WBAInstance}
    {qa : QuorumAxioms inst.cfg inst.correct}
    {np : NetworkProperties Msg inst.correct inst.net inst.gst inst.delta_net}
    (beh : WBABehavior inst qa np)
    {N : NodeId} {t₁ t₂ : Time} {b₁ b₂ : Bool}
    (hN : inst.correct N)
    (h₁ : HasWBAOutput inst N t₁ b₁)
    (h₂ : HasWBAOutput inst N t₂ b₂) :
    b₁ = b₂ := by
  have h₁' := hasWBAOutput_persistent np h₁ (Nat.le_max_left t₁ t₂)
  have h₂' := hasWBAOutput_persistent np h₂ (Nat.le_max_right t₁ t₂)
  obtain ⟨C, hC_correct, hC_b₁, hC_b₂⟩ := qa.quorum_intersection h₁' h₂'
  obtain ⟨ts₁, _, hsent₁⟩ := np.no_forgery C N (Msg.ready b₁) _ hC_correct hN hC_b₁
  obtain ⟨ts₂, _, hsent₂⟩ := np.no_forgery C N (Msg.ready b₂) _ hC_correct hN hC_b₂
  exact beh.ready_unique C ts₁ ts₂ b₁ b₂ hC_correct hsent₁ hsent₂

/-- Construct a WBAView from a concrete WBA instance. -/
noncomputable def mkWBAView (inst : WBAInstance) : WBAView where
  output_at N t :=
    open Classical in
    if h : ∃ b, HasWBAOutput inst N t b then
      some (Classical.choose h)
    else
      none

end Zug.Concrete.WBA
