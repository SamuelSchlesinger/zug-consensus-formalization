/-
  Zug.Safety.Ordering: Lemma 2 from the paper.

  The key safety lemma: finalized rounds at a single node are
  always ancestors of each other (they form a chain).
-/

import Zug.Safety.Monotonicity

namespace Zug

variable {V : Type}
variable {correct : Correctness}
variable {views : SubprotocolViews V}

/-- A round cannot be both committed and skippable at the same node. -/
theorem not_committed_and_skippable
    (agreement : SubprotocolAgreement V correct views)
    {N : NodeId} {t₁ t₂ : Time} {r : Nat}
    (hN : correct N)
    (hc : Committed views N t₁ r) (hs : Skippable views N t₂ r) : False := by
  unfold Committed Skippable at *
  have hc' := (agreement.wba_agreement r).persistent N t₁ true hN hc
    (max t₁ t₂) (Nat.le_max_left t₁ t₂)
  have hs' := (agreement.wba_agreement r).persistent N t₂ false hN hs
    (max t₁ t₂) (Nat.le_max_right t₁ t₂)
  simp [hc'] at hs'

/-- RB outputs are unique per correct node. -/
theorem rb_output_unique
    (agreement : SubprotocolAgreement V correct views)
    {N : NodeId} {t₁ t₂ : Time} {r : Nat}
    {p₁ p₂ : Proposal V}
    (hN : correct N)
    (h₁ : RBOutput views N t₁ r = some p₁)
    (h₂ : RBOutput views N t₂ r = some p₂) :
    p₁ = p₂ := by
  have h₁' := rb_output_persistent agreement hN h₁ (Nat.le_max_left t₁ t₂)
  have h₂' := rb_output_persistent agreement hN h₂ (Nat.le_max_right t₁ t₂)
  rw [h₁'] at h₂'
  exact Option.some.inj h₂'

/-- AcceptedAt carries witness of the RB output. -/
theorem accepted_has_rb_output {N : NodeId} {t : Time} {r : Nat}
    {s : Option Nat}
    (h : AcceptedAt views N t r s) :
    ∃ v, RBOutput views N t r = some ⟨v, s⟩ := by
  cases h with
  | mk_bot _ v _ hrb => exact ⟨v, hrb⟩
  | mk_parent _ _ v _ _ _ _ hrb => exact ⟨v, hrb⟩

/-- Accepted parent is strictly less than the round. -/
theorem accepted_parent_lt {N : NodeId} {t : Time} {r s : Nat}
    (h : AcceptedAt views N t r (some s)) : s < r := by
  cases h with
  | mk_parent _ _ _ _ hs _ _ _ => exact hs

/-- If AcceptedAt with parent (some s), then s has an accepted value. -/
theorem accepted_parent_has_accepted {N : NodeId} {t : Time} {r s : Nat}
    (h : AcceptedAt views N t r (some s)) :
    HasAccepted views N t s := by
  cases h with
  | mk_parent _ _ _ p _ _ hacc _ => exact ⟨p, hacc⟩

/-- Accepted parent is unique per correct node. -/
theorem accepted_parent_unique
    (agreement : SubprotocolAgreement V correct views)
    {N : NodeId} {t₁ t₂ : Time} {r : Nat}
    {s₁ s₂ : Option Nat}
    (hN : correct N)
    (h₁ : AcceptedAt views N t₁ r s₁)
    (h₂ : AcceptedAt views N t₂ r s₂) :
    s₁ = s₂ := by
  obtain ⟨v₁, hrb₁⟩ := accepted_has_rb_output h₁
  obtain ⟨v₂, hrb₂⟩ := accepted_has_rb_output h₂
  have := rb_output_unique agreement hN hrb₁ hrb₂
  simp [Proposal.mk.injEq] at this
  exact this.2

/-- If RB[r] has parent none, r has no strict ancestor. -/
theorem no_ancestor_of_none_parent
    (agreement : SubprotocolAgreement V correct views)
    {N : NodeId} {t : Time} {r : Nat} {v : V}
    (hN : correct N)
    (hrb : RBOutput views N t r = some ⟨v, none⟩)
    {a : Nat}
    (hanc : Ancestor views N t a r) : False := by
  induction hanc with
  | direct s' r' v' hrb' =>
    have := rb_output_unique agreement hN hrb' hrb
    simp [Proposal.mk.injEq] at this
  | trans s' p' r' _ _ _ ih_pr =>
    exact ih_pr hrb

/-- If round c is committed and r has AcceptedAt with parent (some s)
    with s < c < r, that contradicts c being committed (gap is skippable). -/
theorem committed_not_in_accepted_gap
    (agreement : SubprotocolAgreement V correct views)
    {N : NodeId} {t : Time} {r s c : Nat}
    (hN : correct N)
    (hc_comm : Committed views N t c)
    (hacc : AcceptedAt views N t r (some s))
    (hsc : s < c) (hcr : c < r) : False := by
  cases hacc with
  | mk_parent _ _ _ _ _ hskip _ _ =>
    exact not_committed_and_skippable agreement hN hc_comm (hskip c hsc hcr)

/-- Key lemma: if c₁ is committed and c < some round r which has AcceptedAt,
    then c₁ is an ancestor of r.

    This is proved by induction on AcceptedAt for r. -/
theorem committed_is_ancestor_of_accepted
    (agreement : SubprotocolAgreement V correct views)
    {N : NodeId} {t : Time} {c₁ r : Nat} {s : Option Nat}
    (hN : correct N)
    (hlt : c₁ < r)
    (hc₁ : Committed views N t c₁)
    (hacc : AcceptedAt views N t r s) :
    Ancestor views N t c₁ r := by
  induction hacc with
  | mk_bot r' v' hall hrb =>
    -- All rounds < r' are skippable, but c₁ < r' is committed → contradiction
    exact absurd (hall c₁ hlt)
      (fun h => not_committed_and_skippable agreement hN hc₁ h)
  | mk_parent r' s' v' _ hs' hskip _ hrb ih =>
    -- r' has parent s'. c₁ < r'.
    -- Either c₁ ≤ s' or s' < c₁.
    rcases Nat.lt_or_ge c₁ (s' + 1) with hle | hgt
    · -- c₁ ≤ s' (i.e., c₁ < s' + 1)
      rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hle) with heq | hlt'
      · -- c₁ = s': direct parent
        subst heq
        exact Ancestor.direct c₁ r' v' hrb
      · -- c₁ < s': by IH, c₁ is ancestor of s'
        exact Ancestor.trans c₁ s' r' (ih hlt') (Ancestor.direct s' r' v' hrb)
    · -- s' < c₁ (i.e., c₁ ≥ s' + 1)
      -- Then s' < c₁ < r', so c₁ is in the skippable gap → contradiction
      have : s' < c₁ := Nat.lt_of_succ_le hgt
      exact absurd (hskip c₁ this hlt)
        (fun h => not_committed_and_skippable agreement hN hc₁ h)

/-- If a is an Ancestor of r, and r has AcceptedAt with parent (some s),
    then a is an AncestorOrEq of s. -/
theorem ancestor_of_accepted_goes_to_parent
    (agreement : SubprotocolAgreement V correct views)
    {N : NodeId} {t : Time} {a r s : Nat}
    (hN : correct N)
    (hanc : Ancestor views N t a r)
    (hacc : AcceptedAt views N t r (some s)) :
    AncestorOrEq views N t a s := by
  induction hanc with
  | direct a' r' v' hrb' =>
    obtain ⟨v_acc, hrb_acc⟩ := accepted_has_rb_output hacc
    have heq := rb_output_unique agreement hN hrb' hrb_acc
    simp [Proposal.mk.injEq] at heq
    exact Or.inl heq.2
  | trans a' p' r' _ _ ih_ap ih_pr =>
    have h_p_s := ih_pr hacc
    cases h_p_s with
    | inl heq => subst heq; exact Or.inr (by assumption)
    | inr hp_anc_s => exact Or.inr (Ancestor.trans a' p' s (by assumption) hp_anc_s)

/-- AncestorOrEq is transitive. -/
theorem ancestor_or_eq_trans {N : NodeId} {t : Time} {a b c : Nat}
    (h₁ : AncestorOrEq views N t a b) (h₂ : AncestorOrEq views N t b c) :
    AncestorOrEq views N t a c := by
  cases h₂ with
  | inl heq => subst heq; exact h₁
  | inr hanc =>
    cases h₁ with
    | inl heq => subst heq; exact Or.inr hanc
    | inr hanc₁ => exact Or.inr (Ancestor.trans a b c hanc₁ hanc)

/-- Two AncestorOrEq of the same accepted round are comparable.
    Proved by strong induction on the round number. -/
theorem ancestors_of_accepted_comparable
    (agreement : SubprotocolAgreement V correct views)
    {N : NodeId} {t : Time} {a b : Nat} (r : Nat) {s : Option Nat}
    (hN : correct N)
    (ha : AncestorOrEq views N t a r)
    (hb : AncestorOrEq views N t b r)
    (hacc : AcceptedAt views N t r s) :
    AncestorOrEq views N t a b ∨ AncestorOrEq views N t b a := by
  -- If a = r or b = r, trivial
  cases ha with
  | inl heq_a => subst heq_a; right; exact hb
  | inr hanc_a =>
    cases hb with
    | inl heq_b => subst heq_b; left; exact Or.inr hanc_a
    | inr hanc_b =>
      -- Both a and b are strict ancestors of r
      cases hacc with
      | mk_bot _ v' _ hrb =>
        exact absurd hanc_a (fun h => no_ancestor_of_none_parent agreement hN hrb h)
      | mk_parent _ s' v' p' hs' hskip hacc_s' hrb =>
        have ha_s' := ancestor_of_accepted_goes_to_parent agreement hN
          hanc_a (AcceptedAt.mk_parent r s' v' p' hs' hskip hacc_s' hrb)
        have hb_s' := ancestor_of_accepted_goes_to_parent agreement hN
          hanc_b (AcceptedAt.mk_parent r s' v' p' hs' hskip hacc_s' hrb)
        exact ancestors_of_accepted_comparable agreement s' hN ha_s' hb_s' hacc_s'
  termination_by r
  decreasing_by omega

/-- Lemma 2: If both r₁ and r₂ are (N, t)-finalized, they are
    equal or ancestors of each other. -/
theorem finalized_are_ancestors
    (agreement : SubprotocolAgreement V correct views)
    {N : NodeId} {t : Time} {r₁ r₂ : Nat}
    (hN : correct N)
    (h₁ : Finalized views N t r₁)
    (h₂ : Finalized views N t r₂) :
    AncestorOrEq views N t r₁ r₂ ∨ AncestorOrEq views N t r₂ r₁ := by
  obtain ⟨c₁, hanc₁, ⟨s₁, hacc₁⟩, hcom₁⟩ := h₁
  obtain ⟨c₂, hanc₂, ⟨s₂, hacc₂⟩, hcom₂⟩ := h₂
  rcases Nat.lt_or_ge c₁ c₂ with hlt | hge
  · -- c₁ < c₂: c₁ is ancestor of c₂
    have hanc_c₁_c₂ : Ancestor views N t c₁ c₂ :=
      committed_is_ancestor_of_accepted agreement hN hlt hcom₁ hacc₂
    have hr₁_c₂ : AncestorOrEq views N t r₁ c₂ :=
      ancestor_or_eq_trans hanc₁ (Or.inr hanc_c₁_c₂)
    exact ancestors_of_accepted_comparable agreement c₂ hN hr₁_c₂ hanc₂ hacc₂
  · rcases Nat.eq_or_lt_of_le hge with heq | hlt
    · -- c₁ = c₂
      subst heq
      exact ancestors_of_accepted_comparable agreement c₂ hN hanc₁ hanc₂ hacc₁
    · -- c₂ < c₁: symmetric
      have hanc_c₂_c₁ : Ancestor views N t c₂ c₁ :=
        committed_is_ancestor_of_accepted agreement hN hlt hcom₂ hacc₁
      have hr₂_c₁ : AncestorOrEq views N t r₂ c₁ :=
        ancestor_or_eq_trans hanc₂ (Or.inr hanc_c₂_c₁)
      have result := ancestors_of_accepted_comparable agreement c₁ hN hr₂_c₁ hanc₁ hacc₁
      cases result with
      | inl h => right; exact h
      | inr h => left; exact h

end Zug
