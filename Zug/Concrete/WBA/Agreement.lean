/-
  Zug.Concrete.WBA.Agreement: Proof that WBA satisfies WBAAgreement.

  Same structure as RB/Agreement:
  - Persistence from receipt_persistent + output uniqueness.
  - Agreement: output at N → > f correct sent ready → amplification →
    all correct send ready → > q → output at N'.
-/

import Zug.Concrete.WBA.Defs

namespace Zug.Concrete.WBA

open Zug

/-- If mkWBAView outputs some b at (N, t), then HasWBAOutput inst N t b. -/
theorem mkWBAView_output_implies_hasWBAOutput
    {inst : WBAInstance}
    {N : NodeId} {t : Time} {b : Bool}
    (hout : (mkWBAView inst).output_at N t = some b) :
    HasWBAOutput inst N t b := by
  unfold mkWBAView at hout
  simp only at hout
  open Classical in
  split at hout
  case isTrue h =>
    have heq := Option.some.inj hout
    rw [← heq]; exact Classical.choose_spec h
  case isFalse => simp at hout

/-- If HasWBAOutput inst N t b, then mkWBAView outputs b. -/
theorem hasWBAOutput_implies_mkWBAView
    {inst : WBAInstance}
    {qa : QuorumAxioms inst.cfg inst.correct}
    {np : NetworkProperties Msg inst.correct inst.net inst.gst inst.delta_net}
    (beh : WBABehavior inst qa np)
    {N : NodeId} {t : Time} {b : Bool}
    (hN : inst.correct N)
    (h : HasWBAOutput inst N t b) :
    (mkWBAView inst).output_at N t = some b := by
  unfold mkWBAView; simp only
  open Classical in
  rw [dif_pos ⟨b, h⟩]
  congr 1
  exact hasWBAOutput_unique beh hN (Classical.choose_spec ⟨b, h⟩) h

/-- WBAAgreement for mkWBAView. -/
theorem wba_agreement
    {inst : WBAInstance}
    {qa : QuorumAxioms inst.cfg inst.correct}
    {np : NetworkProperties Msg inst.correct inst.net inst.gst inst.delta_net}
    (beh : WBABehavior inst qa np) :
    WBAAgreement inst.correct (mkWBAView inst) where
  persistent := by
    intro N t b hN hout t' hle
    have h_wba := mkWBAView_output_implies_hasWBAOutput hout
    exact hasWBAOutput_implies_mkWBAView beh hN (hasWBAOutput_persistent np h_wba hle)
  agreement := by
    intro N N' t b hN hN' hout
    have h_wba := mkWBAView_output_implies_hasWBAOutput hout
    -- Step 1: > f correct sent ready(b)
    have h_cf : MoreThan inst.cfg.f inst.cfg.n
        (fun S => inst.correct S ∧ ∃ ts, inst.net.sent S (Msg.ready b) ts) := by
      exact (qa.quorum_correct_subset h_wba).mono fun S ⟨hcorr, hrec⟩ =>
        let ⟨ts, _, hsent⟩ := np.no_forgery S N _ t hcorr hN hrec
        ⟨hcorr, ts, hsent⟩
    -- Step 2: Every correct node receives > f ready(b) → sends ready(b)
    have h_all_send : ∀ M, inst.correct M →
        ∃ ts, inst.net.sent M (Msg.ready b) ts := by
      intro M hM
      obtain ⟨enum, hinj, hsat⟩ := h_cf
      have h_del : ∀ i, ∃ t_recv,
          inst.net.received M (↑(enum i)) (Msg.ready b) t_recv := by
        intro i
        obtain ⟨hcorr, ts, hsent⟩ := hsat i
        exact let ⟨t_recv, _, hrec⟩ := np.eventual_delivery _ M _ ts hcorr hM hsent
          ⟨t_recv, hrec⟩
      obtain ⟨t_all, h_all⟩ := collect_at_one_time enum hinj
        (fun S t t' h hle => np.receipt_persistent M S _ t t' h hle) h_del
      have h_mt : MoreThan inst.cfg.f inst.cfg.n
          (fun S => inst.net.received M S (Msg.ready b) t_all) :=
        ⟨enum, hinj, h_all⟩
      obtain ⟨ts, _, hs⟩ := beh.ready_from_ready_amplify M t_all b hM h_mt
      exact ⟨ts, hs⟩
    -- Step 3: > q correct sent ready(b)
    have h_super : MoreThan inst.cfg.q inst.cfg.n
        (fun S => inst.correct S ∧ ∃ ts, inst.net.sent S (Msg.ready b) ts) :=
      qa.all_correct_quorum fun M hM _ => ⟨hM, h_all_send M hM⟩
    -- Step 4: N' receives > q ready(b) → HasWBAOutput
    obtain ⟨enum', hinj', hsat'⟩ := h_super
    have h_del' : ∀ i, ∃ t_recv,
        inst.net.received N' (↑(enum' i)) (Msg.ready b) t_recv := by
      intro i
      obtain ⟨hcorr, ts, hsent⟩ := hsat' i
      exact let ⟨t_recv, _, hrec⟩ := np.eventual_delivery _ N' _ ts hcorr hN' hsent
        ⟨t_recv, hrec⟩
    obtain ⟨t', h_all'⟩ := collect_at_one_time enum' hinj'
      (fun S t t' h hle => np.receipt_persistent N' S _ t t' h hle) h_del'
    exact ⟨t', hasWBAOutput_implies_mkWBAView beh hN' ⟨enum', hinj', h_all'⟩⟩

end Zug.Concrete.WBA
