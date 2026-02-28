/-
  Zug.Concrete.RB.Agreement: Proof that Bracha RB satisfies RBAgreement.

  Persistence follows from receipt_persistent + output uniqueness.
  Agreement: if correct N outputs v, all correct N' eventually output v.
-/

import Zug.Concrete.RB.Defs

namespace Zug.Concrete.RB

open Zug

variable {V : Type}

/-- Combine finitely many existential witnesses into one time using
    persistence. Induction on k. -/
private theorem collect_at_one_time
    {k n : Nat}
    (enum : Fin (k + 1) → Fin n)
    (hinj : Function.Injective enum)
    {P : NodeId → Time → Prop}
    (hpers : ∀ S t t', P S t → t ≤ t' → P S t')
    (h : ∀ i : Fin (k + 1), ∃ t, P (enum i) t) :
    ∃ t, ∀ i : Fin (k + 1), P (enum i) t := by
  induction k with
  | zero =>
    obtain ⟨t, ht⟩ := h ⟨0, by omega⟩
    exact ⟨t, fun i => by
      have : i = ⟨0, by omega⟩ := Fin.ext (by omega)
      rw [this]; exact ht⟩
  | succ k' ih =>
    have hinj' : Function.Injective (fun i : Fin (k' + 1) => enum ⟨i.val, by omega⟩) := by
      intro a b hab
      exact Fin.ext (Fin.mk.inj (hinj hab))
    obtain ⟨t₁, ht₁⟩ := ih (fun i => enum ⟨i.val, by omega⟩) hinj'
      (fun i => h ⟨i.val, by omega⟩)
    obtain ⟨t₂, ht₂⟩ := h ⟨k' + 1, by omega⟩
    refine ⟨max t₁ t₂, fun i => ?_⟩
    by_cases h_last : i.val = k' + 1
    · rw [show i = ⟨k' + 1, by omega⟩ from Fin.ext h_last]
      exact hpers _ t₂ _ ht₂ (Nat.le_max_right t₁ t₂)
    · have := ht₁ ⟨i.val, by omega⟩
      simp only at this
      exact hpers _ t₁ _ this (Nat.le_max_left t₁ t₂)

/-- If mkRBView outputs some v at (N, t), then HasRBOutput inst N t v. -/
theorem mkRBView_output_implies_hasRBOutput
    {inst : RBInstance V}
    {N : NodeId} {t : Time} {v : V}
    (hout : (mkRBView inst).output_at N t = some v) :
    HasRBOutput inst N t v := by
  unfold mkRBView at hout
  simp only at hout
  open Classical in
  split at hout
  case isTrue h =>
    have heq := Option.some.inj hout
    rw [← heq]
    exact Classical.choose_spec h
  case isFalse => simp at hout

/-- If HasRBOutput inst N t v, then mkRBView outputs v. -/
theorem hasRBOutput_implies_mkRBView
    {inst : RBInstance V}
    {qa : QuorumAxioms inst.cfg inst.correct}
    {np : NetworkProperties (Msg V) inst.correct inst.net inst.gst inst.delta_net}
    (beh : RBBehavior inst qa np)
    {N : NodeId} {t : Time} {v : V}
    (hN : inst.correct N)
    (h : HasRBOutput inst N t v) :
    (mkRBView inst).output_at N t = some v := by
  unfold mkRBView
  simp only
  open Classical in
  have hex : ∃ v, HasRBOutput inst N t v := ⟨v, h⟩
  rw [dif_pos hex]
  congr 1
  exact hasRBOutput_unique beh hN (Classical.choose_spec hex) h

/-- Main agreement theorem: mkRBView satisfies RBAgreement. -/
theorem rb_agreement
    {inst : RBInstance V}
    {qa : QuorumAxioms inst.cfg inst.correct}
    {np : NetworkProperties (Msg V) inst.correct inst.net inst.gst inst.delta_net}
    (beh : RBBehavior inst qa np) :
    RBAgreement inst.correct (mkRBView inst) where
  persistent := by
    intro N t v hN hout t' hle
    have h_rb := mkRBView_output_implies_hasRBOutput hout
    exact hasRBOutput_implies_mkRBView beh hN (hasRBOutput_persistent np h_rb hle)
  agreement := by
    intro N N' t v hN hN' hout
    have h_rb := mkRBView_output_implies_hasRBOutput hout
    -- Step 1: > f correct sent ready(v)
    have h_correct_f : MoreThan inst.cfg.f inst.cfg.n
        (fun S => inst.correct S ∧ ∃ ts, inst.net.sent S (Msg.ready v) ts) := by
      exact (qa.super_majority_correct_quorum h_rb).mono fun S ⟨hcorr, hrec⟩ =>
        let ⟨ts, _, hsent⟩ := np.no_forgery S N _ t hcorr hN hrec
        ⟨hcorr, ts, hsent⟩
    -- Step 2: Every correct node receives > f ready(v) → sends ready(v)
    have h_all_send : ∀ M, inst.correct M →
        ∃ ts, inst.net.sent M (Msg.ready v) ts := by
      intro M hM
      obtain ⟨enum, hinj, hsat⟩ := h_correct_f
      have h_del : ∀ i, ∃ t_recv,
          inst.net.received M (↑(enum i)) (Msg.ready v) t_recv := by
        intro i
        obtain ⟨hcorr, ts, hsent⟩ := hsat i
        exact let ⟨t_recv, _, hrec⟩ := np.eventual_delivery _ M _ ts hcorr hM hsent
          ⟨t_recv, hrec⟩
      obtain ⟨t_all, h_all⟩ := collect_at_one_time enum hinj
        (fun S t t' h hle => np.receipt_persistent M S _ t t' h hle) h_del
      have h_mt : MoreThan inst.cfg.f inst.cfg.n
          (fun S => inst.net.received M S (Msg.ready v) t_all) :=
        ⟨enum, hinj, h_all⟩
      obtain ⟨ts, _, hs⟩ := beh.ready_from_ready_amplify M t_all v hM h_mt
      exact ⟨ts, hs⟩
    -- Step 3: > 2f correct nodes sent ready(v)
    have h_super : MoreThan (2 * inst.cfg.f) inst.cfg.n
        (fun S => inst.correct S ∧
          ∃ ts, inst.net.sent S (Msg.ready v) ts) :=
      qa.all_correct_super_majority fun M hM _ => ⟨hM, h_all_send M hM⟩
    -- Step 4: N' receives > 2f ready(v) → HasRBOutput
    obtain ⟨enum', hinj', hsat'⟩ := h_super
    have h_del' : ∀ i, ∃ t_recv,
        inst.net.received N' (↑(enum' i)) (Msg.ready v) t_recv := by
      intro i
      obtain ⟨hcorr, ts, hsent⟩ := hsat' i
      exact let ⟨t_recv, _, hrec⟩ := np.eventual_delivery _ N' _ ts hcorr hN' hsent
        ⟨t_recv, hrec⟩
    obtain ⟨t', h_all'⟩ := collect_at_one_time enum' hinj'
      (fun S t t' h hle => np.receipt_persistent N' S _ t t' h hle) h_del'
    exact ⟨t', hasRBOutput_implies_mkRBView beh hN' ⟨enum', hinj', h_all'⟩⟩

end Zug.Concrete.RB
