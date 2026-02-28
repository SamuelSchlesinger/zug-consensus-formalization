/-
  Zug.Safety.Theorem: Theorem 1 (Safety) from the paper.

  Agreement, Total Order, and Validity: all correct nodes finalize
  the same rounds in the same order, and agree on the RB-delivered
  value for each finalized round.
-/

import Zug.Safety.Ordering

namespace Zug

variable {V : Type}
variable {correct : Correctness}
variable {views : SubprotocolViews V}

/-! ## Finite persistent choice

  If finitely many persistent predicates each hold at some time,
  there exists a single time at which all hold simultaneously.
-/

theorem finite_persistent_choice {P : Nat → Time → Prop}
    (hpers : ∀ u t t', P u t → t ≤ t' → P u t')
    (r : Nat)
    (h : ∀ u, u < r → ∃ t, P u t) :
    ∃ t, ∀ u, u < r → P u t := by
  induction r with
  | zero => exact ⟨0, fun _ hu => absurd hu (Nat.not_lt_zero _)⟩
  | succ k ih =>
    have ⟨t₁, ht₁⟩ := ih (fun u hu => h u (Nat.lt_of_lt_of_le hu (Nat.le_succ k)))
    have ⟨t₂, ht₂⟩ := h k (by omega)
    exact ⟨max t₁ t₂, fun u hu => by
      by_cases heq : u = k
      · rw [heq]; exact hpers k t₂ _ ht₂ (Nat.le_max_right t₁ t₂)
      · have hlt : u < k := by omega
        exact hpers u t₁ _ (ht₁ u hlt) (Nat.le_max_left t₁ t₂)⟩

/-! ## Cross-node propagation of AcceptedAt -/

/-- AcceptedAt propagates from correct node N to correct node N'. -/
theorem accepted_at_propagates
    (agreement : SubprotocolAgreement V correct views)
    {N N' : NodeId} {t : Time} {r : Nat} {s : Option Nat}
    (hN : correct N) (hN' : correct N')
    (h : AcceptedAt views N t r s) :
    ∃ t', AcceptedAt views N' t' r s := by
  induction h with
  | mk_bot r v hall hrb =>
    have hskips : ∀ u, u < r → ∃ t', Skippable views N' t' u :=
      fun u hu => skippable_propagates agreement hN hN' (hall u hu)
    obtain ⟨trb, hrb'⟩ := rb_output_propagates agreement hN hN' hrb
    obtain ⟨tskip, hskip'⟩ := @finite_persistent_choice
      (fun u t => Skippable views N' t u)
      (fun u t t' h hle => skippable_persistent agreement hN' h hle)
      r hskips
    exact ⟨max tskip trb, AcceptedAt.mk_bot r v
      (fun u hu => skippable_persistent agreement hN' (hskip' u hu)
        (Nat.le_max_left tskip trb))
      (rb_output_persistent agreement hN' hrb' (Nat.le_max_right tskip trb))⟩
  | mk_parent r s v p hs hskip _hacc_s hrb ih =>
    -- Gap skippable rounds propagate
    have hskips : ∀ u, s < u → u < r → ∃ t', Skippable views N' t' u :=
      fun u hsu hur => skippable_propagates agreement hN hN' (hskip u hsu hur)
    -- RB output propagates
    obtain ⟨trb, hrb'⟩ := rb_output_propagates agreement hN hN' hrb
    -- IH: parent's AcceptedAt propagates
    obtain ⟨tacc, hacc'⟩ := ih
    -- Combine gap skippable conditions: we need them for u in (s, r).
    -- We use finite_persistent_choice with all u < r, but only care about s < u.
    have hskips_padded : ∀ u, u < r → ∃ t', (s < u → Skippable views N' t' u) := by
      intro u hu
      by_cases hsu : s < u
      · obtain ⟨t', h'⟩ := hskips u hsu hu
        exact ⟨t', fun _ => h'⟩
      · exact ⟨0, fun h => absurd h hsu⟩
    obtain ⟨tskip, hskip_all⟩ := @finite_persistent_choice
      (fun u t => s < u → Skippable views N' t u)
      (fun u t t' (h : s < u → Skippable views N' t u) hle =>
        fun hsu => skippable_persistent agreement hN' (h hsu) hle)
      r hskips_padded
    let tmax := max (max tskip trb) tacc
    exact ⟨tmax, AcceptedAt.mk_parent r s v p hs
      (fun u hsu hur => skippable_persistent agreement hN' (hskip_all u hur hsu)
        (Nat.le_trans (Nat.le_max_left tskip trb) (Nat.le_max_left _ tacc)))
      (accepted_at_persistent agreement hN' hacc' (Nat.le_max_right _ tacc))
      (rb_output_persistent agreement hN' hrb'
        (Nat.le_trans (Nat.le_max_right tskip trb) (Nat.le_max_left _ tacc)))⟩

/-- HasAccepted propagates from correct node N to correct node N'. -/
theorem has_accepted_propagates
    (agreement : SubprotocolAgreement V correct views)
    {N N' : NodeId} {t : Time} {r : Nat}
    (hN : correct N) (hN' : correct N')
    (h : HasAccepted views N t r) :
    ∃ t', HasAccepted views N' t' r := by
  obtain ⟨s, hacc⟩ := h
  obtain ⟨t', hacc'⟩ := accepted_at_propagates agreement hN hN' hacc
  exact ⟨t', s, hacc'⟩

/-- Ancestor propagates from correct node N to correct node N'. -/
theorem ancestor_propagates
    (agreement : SubprotocolAgreement V correct views)
    {N N' : NodeId} {t : Time} {s r : Nat}
    (hN : correct N) (hN' : correct N')
    (h : Ancestor views N t s r) :
    ∃ t', Ancestor views N' t' s r := by
  induction h with
  | direct s r v hrb =>
    obtain ⟨t', hrb'⟩ := rb_output_propagates agreement hN hN' hrb
    exact ⟨t', Ancestor.direct s r v hrb'⟩
  | trans s p r _ _ ih1 ih2 =>
    obtain ⟨t₁, h₁⟩ := ih1
    obtain ⟨t₂, h₂⟩ := ih2
    exact ⟨max t₁ t₂,
      Ancestor.trans s p r
        (ancestor_persistent agreement hN' h₁ (Nat.le_max_left t₁ t₂))
        (ancestor_persistent agreement hN' h₂ (Nat.le_max_right t₁ t₂))⟩

/-- AncestorOrEq propagates from correct node N to correct node N'. -/
theorem ancestor_or_eq_propagates
    (agreement : SubprotocolAgreement V correct views)
    {N N' : NodeId} {t : Time} {s r : Nat}
    (hN : correct N) (hN' : correct N')
    (h : AncestorOrEq views N t s r) :
    ∃ t', AncestorOrEq views N' t' s r := by
  cases h with
  | inl heq => exact ⟨0, Or.inl heq⟩
  | inr hanc =>
    obtain ⟨t', h'⟩ := ancestor_propagates agreement hN hN' hanc
    exact ⟨t', Or.inr h'⟩

/-! ## Cross-node agreement on values -/

/-- RB outputs agree across correct nodes: if two correct nodes both
    have an RB output for round r, the proposals are identical. -/
theorem rb_output_agreement
    (agreement : SubprotocolAgreement V correct views)
    {N N' : NodeId} {t t' : Time}
    {r : Nat} {p p' : Proposal V}
    (hN : correct N) (hN' : correct N')
    (hrb : RBOutput views N t r = some p)
    (hrb' : RBOutput views N' t' r = some p') :
    p = p' := by
  obtain ⟨t'', hrb''⟩ := rb_output_propagates agreement hN hN' hrb
  exact rb_output_unique agreement hN' hrb'' hrb'

/-! ## Theorem 1: Safety -/

/-- Safety: Total Order. The finalized rounds form the same totally
    ordered chain at every correct node. -/
theorem safety_total_order
    (agreement : SubprotocolAgreement V correct views)
    {N : NodeId} {t : Time} {r₁ r₂ : Nat}
    (hN : correct N)
    (h₁ : Finalized views N t r₁)
    (h₂ : Finalized views N t r₂) :
    AncestorOrEq views N t r₁ r₂ ∨ AncestorOrEq views N t r₂ r₁ :=
  finalized_are_ancestors agreement hN h₁ h₂

/-- Safety: Agreement. If correct node N eventually finalizes round r,
    then every correct node N' eventually finalizes round r. -/
theorem safety_agreement
    (agreement : SubprotocolAgreement V correct views)
    {N N' : NodeId} {t : Time} {r : Nat}
    (hN : correct N) (hN' : correct N')
    (h : Finalized views N t r) :
    ∃ t', Finalized views N' t' r := by
  obtain ⟨r', hanc, hacc, hcom⟩ := h
  obtain ⟨t₁, hanc'⟩ := ancestor_or_eq_propagates agreement hN hN' hanc
  obtain ⟨t₂, hacc'⟩ := has_accepted_propagates agreement hN hN' hacc
  obtain ⟨t₃, hcom'⟩ := committed_propagates agreement hN hN' hcom
  let tmax := max (max t₁ t₂) t₃
  exact ⟨tmax, r',
    ancestor_or_eq_persistent agreement hN' hanc'
      (Nat.le_trans (Nat.le_max_left t₁ t₂) (Nat.le_max_left _ t₃)),
    has_accepted_persistent agreement hN' hacc'
      (Nat.le_trans (Nat.le_max_right t₁ t₂) (Nat.le_max_left _ t₃)),
    committed_persistent agreement hN' hcom' (Nat.le_max_right _ t₃)⟩

/-! ## Validity: finalized rounds carry agreed-upon values -/

/-- If r is an ancestor-or-equal of an accepted round r', then r itself
    has an accepted value. Ancestors travel through the parent chain, and
    each parent has AcceptedAt by the inductive structure. -/
theorem ancestor_of_accepted_has_accepted
    (agreement : SubprotocolAgreement V correct views)
    {N : NodeId} {t : Time} {r : Nat}
    (hN : correct N)
    (r' : Nat) {s' : Option Nat}
    (hacc : AcceptedAt views N t r' s')
    (hanc : AncestorOrEq views N t r r') :
    HasAccepted views N t r := by
  cases hanc with
  | inl heq => subst heq; exact ⟨s', hacc⟩
  | inr hanc_strict =>
    cases hacc with
    | mk_bot _ v _ hrb =>
      exact absurd hanc_strict
        (fun h => no_ancestor_of_none_parent agreement hN hrb h)
    | mk_parent _ s v p hs hskip hacc_s hrb =>
      exact ancestor_of_accepted_has_accepted agreement hN s hacc_s
        (ancestor_of_accepted_goes_to_parent agreement hN hanc_strict
          (AcceptedAt.mk_parent r' s v p hs hskip hacc_s hrb))
  termination_by r'
  decreasing_by omega

/-- A finalized round has an accepted value: Finalized gives an
    ancestor-or-equal committed round r', and
    `ancestor_of_accepted_has_accepted` brings acceptance down to r. -/
theorem finalized_has_accepted
    (agreement : SubprotocolAgreement V correct views)
    {N : NodeId} {t : Time} {r : Nat}
    (hN : correct N)
    (h : Finalized views N t r) :
    HasAccepted views N t r := by
  obtain ⟨r', hanc, ⟨s', hacc⟩, _⟩ := h
  exact ancestor_of_accepted_has_accepted agreement hN r' hacc hanc

/-- A finalized round has an RB-delivered proposal. -/
theorem finalized_has_rb_output
    (agreement : SubprotocolAgreement V correct views)
    {N : NodeId} {t : Time} {r : Nat}
    (hN : correct N)
    (h : Finalized views N t r) :
    ∃ p, RBOutput views N t r = some p := by
  obtain ⟨s, hacc⟩ := finalized_has_accepted agreement hN h
  obtain ⟨v, hrb⟩ := accepted_has_rb_output hacc
  exact ⟨⟨v, s⟩, hrb⟩

/-- Safety: Validity. If round r is finalized at two correct nodes,
    they agree on the RB-delivered proposal for that round (both the
    value and the parent pointer). Combined with Agreement and Total
    Order, this completes the safety story: all correct nodes produce
    the same totally-ordered sequence of (round, value) pairs. -/
theorem safety_validity
    (agreement : SubprotocolAgreement V correct views)
    {N N' : NodeId} {t t' : Time} {r : Nat}
    (hN : correct N) (hN' : correct N')
    (hfin : Finalized views N t r)
    (hfin' : Finalized views N' t' r) :
    ∃ p, RBOutput views N t r = some p ∧ RBOutput views N' t' r = some p := by
  obtain ⟨p, hrb⟩ := finalized_has_rb_output agreement hN hfin
  obtain ⟨p', hrb'⟩ := finalized_has_rb_output agreement hN' hfin'
  obtain rfl := rb_output_agreement agreement hN hN' hrb hrb'
  exact ⟨p, hrb, hrb'⟩

end Zug
