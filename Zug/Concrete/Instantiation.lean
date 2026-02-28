/-
  Zug.Concrete.Instantiation: Wire concrete Bracha RB and WBA
  into the abstract SubprotocolAgreement and timed property interfaces.

  This eliminates axioms 1-3 of ProtocolBehavior by constructing concrete
  inhabitants from Bracha's subprotocols.

  The remaining axioms 4-7 (correct_start, timer_axiom, vote_axiom,
  leader_proposal) concern the outer AB protocol logic, not the
  subprotocols. The end-to-end statement becomes:
  "Bracha's subprotocols + correct Zug AB implementation → safety + liveness."
-/

import Zug.Concrete.RB.TimedDelay
import Zug.Concrete.WBA.TimedDelay
import Zug.Protocol.Execution

namespace Zug.Concrete

open Zug

/-- Bundle of RB instances, one per round. Each broadcasts Proposal V
    (matching SubprotocolViews which uses RBView (Proposal V)). -/
structure RBInstances (V : Type) where
  inst : Nat → RB.RBInstance (Proposal V)
  qa : ∀ r, QuorumAxioms (inst r).cfg (inst r).correct
  np : ∀ r, NetworkProperties (RB.Msg (Proposal V)) (inst r).correct (inst r).net
    (inst r).gst (inst r).delta_net
  beh : ∀ r, RB.RBBehavior (inst r) (qa r) (np r)

/-- Bundle of WBA instances, one per round. -/
structure WBAInstances where
  inst : Nat → WBA.WBAInstance
  qa : ∀ r, QuorumAxioms (inst r).cfg (inst r).correct
  np : ∀ r, NetworkProperties WBA.Msg (inst r).correct (inst r).net
    (inst r).gst (inst r).delta_net
  beh : ∀ r, WBA.WBABehavior (inst r) (qa r) (np r)

/-- Construct SubprotocolViews from concrete instances. -/
noncomputable def mkViews {V : Type}
    (rb_insts : RBInstances V)
    (wba_insts : WBAInstances) : SubprotocolViews V where
  rb r := RB.mkRBView (rb_insts.inst r)
  wba r := WBA.mkWBAView (wba_insts.inst r)

/-- Concrete SubprotocolAgreement: every RB and WBA instance satisfies
    agreement properties. -/
theorem concrete_agreement {V : Type}
    {correct : Correctness}
    (rb_insts : RBInstances V)
    (wba_insts : WBAInstances)
    (h_rb_correct : ∀ r, (rb_insts.inst r).correct = correct)
    (h_wba_correct : ∀ r, (wba_insts.inst r).correct = correct) :
    SubprotocolAgreement V correct (mkViews rb_insts wba_insts) where
  rb_agreement r := by
    have h := RB.rb_agreement (rb_insts.beh r)
    rw [h_rb_correct] at h; exact h
  wba_agreement r := by
    have h := WBA.wba_agreement (wba_insts.beh r)
    rw [h_wba_correct] at h; exact h

/-- Concrete RBTimedDelay for each round. -/
theorem concrete_rb_timed_delay {V : Type}
    {correct : Correctness} {gst delta_net : Time}
    (rb_insts : RBInstances V)
    (h_correct : ∀ r, (rb_insts.inst r).correct = correct)
    (h_gst : ∀ r, (rb_insts.inst r).gst = gst)
    (h_delta : ∀ r, (rb_insts.inst r).delta_net = delta_net) :
    ∀ r, RBTimedDelay correct (RB.mkRBView (rb_insts.inst r))
      gst (3 * delta_net) := by
  intro r
  have h := RB.rb_timed_delay (rb_insts.beh r)
  rw [h_correct, h_gst, h_delta] at h; exact h

/-- Concrete WBATimedDelay for each round. -/
theorem concrete_wba_timed_delay
    {correct : Correctness} {gst delta_net : Time}
    (wba_insts : WBAInstances)
    (h_correct : ∀ r, (wba_insts.inst r).correct = correct)
    (h_gst : ∀ r, (wba_insts.inst r).gst = gst)
    (h_delta : ∀ r, (wba_insts.inst r).delta_net = delta_net) :
    ∀ r, WBATimedDelay correct (WBA.mkWBAView (wba_insts.inst r))
      gst (3 * delta_net) := by
  intro r
  have h := WBA.wba_timed_delay (wba_insts.beh r)
  rw [h_correct, h_gst, h_delta] at h; exact h

/-- Concrete WBATimedWeakTermination for each round. -/
theorem concrete_wba_weak_termination
    {correct : Correctness} {gst delta_net : Time}
    (wba_insts : WBAInstances)
    (h_correct : ∀ r, (wba_insts.inst r).correct = correct)
    (h_gst : ∀ r, (wba_insts.inst r).gst = gst)
    (h_delta : ∀ r, (wba_insts.inst r).delta_net = delta_net) :
    ∀ r, WBATimedWeakTermination correct (WBA.mkWBAView (wba_insts.inst r))
      gst (3 * delta_net) (wba_insts.inst r).input_at := by
  intro r
  have h := WBA.wba_weak_termination (wba_insts.beh r)
  rw [h_correct, h_gst, h_delta] at h; exact h

/-- Main instantiation theorem: given Bracha RB and WBA instances
    with consistent parameters, we can construct the subprotocol
    portion of ProtocolBehavior (axioms 1-3). -/
theorem concrete_protocol_behavior {V : Type}
    {correct : Correctness} {gst delta_net : Time}
    (rb_insts : RBInstances V)
    (wba_insts : WBAInstances)
    (h_rb_correct : ∀ r, (rb_insts.inst r).correct = correct)
    (h_wba_correct : ∀ r, (wba_insts.inst r).correct = correct)
    (h_rb_gst : ∀ r, (rb_insts.inst r).gst = gst)
    (h_wba_gst : ∀ r, (wba_insts.inst r).gst = gst)
    (h_rb_delta : ∀ r, (rb_insts.inst r).delta_net = delta_net)
    (h_wba_delta : ∀ r, (wba_insts.inst r).delta_net = delta_net)
    (leaders : LeaderSequence correct)
    (wba_input : Nat → NodeId → Option (Time × Bool))
    (h_wba_input : ∀ r, (wba_insts.inst r).input_at = wba_input r)
    (h_delta_pos : 3 * delta_net > 0)
    -- Remaining axioms (4-7) about the AB protocol itself
    (correct_start : ∀ N, correct N →
      ReachedRound (mkViews rb_insts wba_insts) N gst 0)
    (timer_axiom : ∀ N r t, correct N → gst ≤ t →
      ReachedRound (mkViews rb_insts wba_insts) N t r →
      (¬HasAccepted (mkViews rb_insts wba_insts) N (t + 2 * (3 * delta_net)) r) →
      ∃ ti, ti ≤ t + 2 * (3 * delta_net) ∧
        wba_input r N = some (ti, false))
    (vote_axiom : ∀ N r t, correct N →
      HasAccepted (mkViews rb_insts wba_insts) N t r →
      ∃ ti, ti ≤ t ∧ wba_input r N = some (ti, true))
    (leader_proposal : ∀ r t N, correct (leaders.leader r) → correct N →
      gst ≤ t →
      ReachedRound (mkViews rb_insts wba_insts) (leaders.leader r) t r →
      HasAccepted (mkViews rb_insts wba_insts) N (t + 3 * delta_net) r) :
    ProtocolBehavior V
      { correct := correct
        views := mkViews rb_insts wba_insts
        sync := ⟨gst, 3 * delta_net, h_delta_pos⟩
        leaders := leaders
        wba_input := wba_input } where
  agreement := concrete_agreement rb_insts wba_insts h_rb_correct h_wba_correct
  rb_timed_delay r :=
    concrete_rb_timed_delay rb_insts h_rb_correct h_rb_gst h_rb_delta r
  wba_timed_delay r :=
    concrete_wba_timed_delay wba_insts h_wba_correct h_wba_gst h_wba_delta r
  wba_weak_termination r := by
    have h := concrete_wba_weak_termination wba_insts h_wba_correct h_wba_gst h_wba_delta r
    rw [h_wba_input] at h; exact h
  correct_start := correct_start
  timer_axiom := timer_axiom
  vote_axiom := vote_axiom
  leader_proposal := leader_proposal

end Zug.Concrete
