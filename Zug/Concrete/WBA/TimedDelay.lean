/-
  Zug.Concrete.WBA.TimedDelay: Proofs of WBATimedDelay and
  WBATimedWeakTermination with delta = 3 * delta_net.
-/

import Zug.Concrete.WBA.Agreement

namespace Zug.Concrete.WBA

open Zug

/-- Bounded delivery helper: if correct S sent m at time ts ≤ t,
    gst ≤ t, then correct R receives m by t + d. -/
private theorem deliver_by
    {inst : WBAInstance}
    (np : NetworkProperties Msg inst.correct inst.net inst.gst inst.delta_net)
    {S R : NodeId} {m : Msg} {ts t : Time}
    (hS : inst.correct S) (hR : inst.correct R)
    (hgst : inst.gst ≤ t) (hts : ts ≤ t)
    (hsent : inst.net.sent S m ts) :
    inst.net.received R S m (t + inst.delta_net) :=
  np.receipt_persistent R S m _ (t + inst.delta_net)
    (np.bounded_delay S R m ts hS hR hsent)
    (max_add_le_add hgst hts)

/-- WBATimedDelay with delta = 3 * delta_net. -/
theorem wba_timed_delay
    {inst : WBAInstance}
    {qa : QuorumAxioms inst.cfg inst.correct}
    {np : NetworkProperties Msg inst.correct inst.net inst.gst inst.delta_net}
    (beh : WBABehavior inst qa np) :
    WBATimedDelay inst.correct (mkWBAView inst) inst.gst (3 * inst.delta_net) where
  timed_delay := by
    intro N N' t b hN hN' hgst hout
    have h_wba := mkWBAView_output_implies_hasWBAOutput hout
    -- Step 1: > f correct sent ready(b) at times ≤ t
    have h_cf : MoreThan inst.cfg.f inst.cfg.n
        (fun S => inst.correct S ∧ ∃ ts, ts ≤ t ∧
          inst.net.sent S (Msg.ready b) ts) := by
      exact (qa.quorum_correct_subset h_wba).mono fun S ⟨hcorr, hrec⟩ =>
        let ⟨ts, hle, hsent⟩ := np.no_forgery S N _ t hcorr hN hrec
        ⟨hcorr, ts, hle, hsent⟩
    obtain ⟨enum_f, hinj_f, hsat_f⟩ := h_cf
    -- Step 2: All correct amplify → send ready by t + δ
    have h_all_send : ∀ M, inst.correct M →
        ∃ ts, ts ≤ t + inst.delta_net ∧
          inst.net.sent M (Msg.ready b) ts := by
      intro M hM
      have h_recv : ∀ i : Fin (inst.cfg.f + 1),
          inst.net.received M (↑(enum_f i)) (Msg.ready b) (t + inst.delta_net) := by
        intro i
        obtain ⟨hcorr, ts, hts, hsent⟩ := hsat_f i
        exact deliver_by np hcorr hM hgst hts hsent
      exact beh.ready_from_ready_amplify M (t + inst.delta_net) b hM
        ⟨enum_f, hinj_f, h_recv⟩
    -- Step 3: > q correct sent ready at times ≤ t + δ
    have h_super : MoreThan inst.cfg.q inst.cfg.n
        (fun S => inst.correct S ∧ ∃ ts, ts ≤ t + inst.delta_net ∧
          inst.net.sent S (Msg.ready b) ts) :=
      qa.all_correct_quorum fun M hM _ => ⟨hM, h_all_send M hM⟩
    obtain ⟨enum_s, hinj_s, hsat_s⟩ := h_super
    -- Step 4: N' receives > q by (t + δ) + δ = t + 2δ
    have hgst' : inst.gst ≤ t + inst.delta_net :=
      Nat.le_trans hgst (Nat.le_add_right t _)
    have h_recv_s : ∀ i : Fin (inst.cfg.q + 1),
        inst.net.received N' (↑(enum_s i)) (Msg.ready b)
          (t + inst.delta_net + inst.delta_net) := by
      intro i
      obtain ⟨hcorr, ts, hts, hsent⟩ := hsat_s i
      exact deliver_by np hcorr hN' hgst' hts hsent
    have h_out : HasWBAOutput inst N' (t + 2 * inst.delta_net) b := by
      rw [← add_d_d t inst.delta_net]
      exact ⟨enum_s, hinj_s, h_recv_s⟩
    exact hasWBAOutput_implies_mkWBAView beh hN'
      (hasWBAOutput_persistent np h_out
        (Nat.add_le_add_left (two_le_three_mul inst.delta_net) t))

/-- WBATimedWeakTermination with delta = 3 * delta_net. -/
theorem wba_weak_termination
    {inst : WBAInstance}
    {qa : QuorumAxioms inst.cfg inst.correct}
    {np : NetworkProperties Msg inst.correct inst.net inst.gst inst.delta_net}
    (beh : WBABehavior inst qa np) :
    WBATimedWeakTermination inst.correct (mkWBAView inst) inst.gst
      (3 * inst.delta_net) inst.input_at where
  weak_termination := by
    intro t b hgst h_all_input N' hN'
    -- Step 1: All correct voted b at times ≤ t
    have h_all_vote : ∀ M, inst.correct M →
        ∃ ts, ts ≤ t ∧ inst.net.sent M (Msg.vote b) ts := by
      intro M hM
      obtain ⟨ti, hti, hinp⟩ := h_all_input M hM
      obtain ⟨ts, hts_ti, hsent⟩ := beh.vote_from_input M ti b hM hinp
      exact ⟨ts, Nat.le_trans hts_ti hti, hsent⟩
    -- Step 2: > q correct voted b (since n-f > q from n > 3f)
    have h_vote_q : MoreThan inst.cfg.q inst.cfg.n
        (fun S => inst.correct S ∧ ∃ ts, ts ≤ t ∧
          inst.net.sent S (Msg.vote b) ts) :=
      qa.all_correct_quorum fun M hM _ => ⟨hM, h_all_vote M hM⟩
    obtain ⟨enum_v, hinj_v, hsat_v⟩ := h_vote_q
    -- Step 3: All correct receive > q votes by t + δ → send ready
    have h_all_ready : ∀ M, inst.correct M →
        ∃ ts, ts ≤ t + inst.delta_net ∧
          inst.net.sent M (Msg.ready b) ts := by
      intro M hM
      have h_recv_v : ∀ i : Fin (inst.cfg.q + 1),
          inst.net.received M (↑(enum_v i)) (Msg.vote b) (t + inst.delta_net) := by
        intro i
        obtain ⟨hcorr, ts, hts, hsent⟩ := hsat_v i
        exact deliver_by np hcorr hM hgst hts hsent
      exact beh.ready_from_vote_quorum M (t + inst.delta_net) b hM
        ⟨enum_v, hinj_v, h_recv_v⟩
    -- Step 4: > q correct sent ready at times ≤ t + δ
    have h_super : MoreThan inst.cfg.q inst.cfg.n
        (fun S => inst.correct S ∧ ∃ ts, ts ≤ t + inst.delta_net ∧
          inst.net.sent S (Msg.ready b) ts) :=
      qa.all_correct_quorum fun M hM _ => ⟨hM, h_all_ready M hM⟩
    obtain ⟨enum_r, hinj_r, hsat_r⟩ := h_super
    -- Step 5: N' receives > q readies by (t + δ) + δ = t + 2δ
    have hgst' : inst.gst ≤ t + inst.delta_net :=
      Nat.le_trans hgst (Nat.le_add_right t _)
    have h_recv_r : ∀ i : Fin (inst.cfg.q + 1),
        inst.net.received N' (↑(enum_r i)) (Msg.ready b)
          (t + inst.delta_net + inst.delta_net) := by
      intro i
      obtain ⟨hcorr, ts, hts, hsent⟩ := hsat_r i
      exact deliver_by np hcorr hN' hgst' hts hsent
    -- HasWBAOutput at t + 2δ
    have h_out : HasWBAOutput inst N' (t + 2 * inst.delta_net) b := by
      rw [← add_d_d t inst.delta_net]
      exact ⟨enum_r, hinj_r, h_recv_r⟩
    -- Persist to t + 3δ
    exact hasWBAOutput_implies_mkWBAView beh hN'
      (hasWBAOutput_persistent np h_out
        (Nat.add_le_add_left (two_le_three_mul inst.delta_net) t))

end Zug.Concrete.WBA
