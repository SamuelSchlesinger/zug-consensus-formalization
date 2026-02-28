/-
  Zug.Concrete.RB.TimedDelay: Proof that Bracha RB satisfies
  RBTimedDelay with delta = 3 * delta_net.

  If correct N outputs v at time t ≥ GST:
  1. > f correct sent ready(v) at times ≤ t.
  2. By bounded_delay, all correct receive > f readies by t + δ.
  3. All correct amplify → send ready(v) by t + δ.
  4. All correct receive > q readies by t + 2δ.
  5. Persist from t + 2δ to t + 3δ.
-/

import Zug.Concrete.RB.Agreement

namespace Zug.Concrete.RB

open Zug

variable {V : Type}

/-- Bounded delivery helper: if correct S sent m at time ts ≤ t,
    gst ≤ t, then correct R receives m by t + d. -/
private theorem deliver_by
    {inst : RBInstance V}
    (np : NetworkProperties (Msg V) inst.correct inst.net inst.gst inst.delta_net)
    {S R : NodeId} {m : Msg V} {ts t : Time}
    (hS : inst.correct S) (hR : inst.correct R)
    (hgst : inst.gst ≤ t) (hts : ts ≤ t)
    (hsent : inst.net.sent S m ts) :
    inst.net.received R S m (t + inst.delta_net) :=
  np.receipt_persistent R S m _ (t + inst.delta_net)
    (np.bounded_delay S R m ts hS hR hsent)
    (max_add_le_add hgst hts)

/-- RBTimedDelay with delta = 3 * delta_net. -/
theorem rb_timed_delay
    {inst : RBInstance V}
    {qa : QuorumAxioms inst.cfg inst.correct}
    {np : NetworkProperties (Msg V) inst.correct inst.net inst.gst inst.delta_net}
    (beh : RBBehavior inst qa np) :
    RBTimedDelay inst.correct (mkRBView inst) inst.gst (3 * inst.delta_net) where
  timed_delay := by
    intro N N' t v hN hN' hgst hout
    have h_rb := mkRBView_output_implies_hasRBOutput hout
    -- Step 1: > f correct sent ready(v) at times ≤ t
    have h_cf : MoreThan inst.cfg.f inst.cfg.n
        (fun S => inst.correct S ∧ ∃ ts, ts ≤ t ∧
          inst.net.sent S (Msg.ready v) ts) := by
      exact (qa.quorum_correct_subset h_rb).mono fun S ⟨hcorr, hrec⟩ =>
        let ⟨ts, hle, hsent⟩ := np.no_forgery S N _ t hcorr hN hrec
        ⟨hcorr, ts, hle, hsent⟩
    obtain ⟨enum_f, hinj_f, hsat_f⟩ := h_cf
    -- Step 2: All correct receive > f readies by t + δ
    have h_recv_at : ∀ M, inst.correct M → ∀ i : Fin (inst.cfg.f + 1),
        inst.net.received M (↑(enum_f i)) (Msg.ready v) (t + inst.delta_net) := by
      intro M hM i
      obtain ⟨hcorr, ts, hts, hsent⟩ := hsat_f i
      exact deliver_by np hcorr hM hgst hts hsent
    -- Step 3: All correct amplify → send ready(v) by t + δ
    have h_all_send : ∀ M, inst.correct M →
        ∃ ts, ts ≤ t + inst.delta_net ∧
          inst.net.sent M (Msg.ready v) ts := by
      intro M hM
      exact beh.ready_from_ready_amplify M (t + inst.delta_net) v hM
        ⟨enum_f, hinj_f, h_recv_at M hM⟩
    -- Step 4: > q correct sent ready(v), each at time ≤ t + δ
    have h_super : MoreThan inst.cfg.q inst.cfg.n
        (fun S => inst.correct S ∧ ∃ ts, ts ≤ t + inst.delta_net ∧
          inst.net.sent S (Msg.ready v) ts) :=
      qa.all_correct_quorum fun M hM _ => ⟨hM, h_all_send M hM⟩
    obtain ⟨enum_s, hinj_s, hsat_s⟩ := h_super
    -- N' receives > q readies by (t + δ) + δ = t + 2δ
    have hgst' : inst.gst ≤ t + inst.delta_net :=
      Nat.le_trans hgst (Nat.le_add_right t _)
    have h_recv_s : ∀ i : Fin (inst.cfg.q + 1),
        inst.net.received N' (↑(enum_s i)) (Msg.ready v)
          (t + inst.delta_net + inst.delta_net) := by
      intro i
      obtain ⟨hcorr, ts, hts, hsent⟩ := hsat_s i
      exact deliver_by np hcorr hN' hgst' hts hsent
    -- Rewrite t + δ + δ = t + 2δ
    have h_arith : t + inst.delta_net + inst.delta_net = t + 2 * inst.delta_net :=
      add_d_d t inst.delta_net
    -- HasRBOutput at t + 2δ
    have h_out : HasRBOutput inst N' (t + 2 * inst.delta_net) v := by
      rw [← h_arith]
      exact ⟨enum_s, hinj_s, h_recv_s⟩
    -- Persist to t + 3δ
    have h_le : t + 2 * inst.delta_net ≤ t + 3 * inst.delta_net :=
      Nat.add_le_add_left (two_le_three_mul inst.delta_net) t
    exact hasRBOutput_implies_mkRBView beh hN'
      (hasRBOutput_persistent np h_out h_le)

end Zug.Concrete.RB
