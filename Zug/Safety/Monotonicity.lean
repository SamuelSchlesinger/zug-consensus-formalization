/-
  Zug.Safety.Monotonicity: Lemma 1 from the paper.

  Proves that committed, skippable, accepted, and finalized are:
  1. Persistent in time (once true, always true for that node)
  2. Eventually true for all correct nodes (propagation)
-/

import Zug.Protocol.Defs

namespace Zug

variable {V : Type}
variable {correct : Correctness}
variable {views : SubprotocolViews V}

/-! ## Part 1: Persistence in time -/

/-- Committed is persistent: if (N, t)-committed then (N, t')-committed
    for all t' ≥ t. -/
theorem committed_persistent
    (agreement : SubprotocolAgreement V correct views)
    {N : NodeId} {t t' : Time} {r : Nat}
    (hN : correct N)
    (h : Committed views N t r) (hle : t ≤ t') :
    Committed views N t' r := by
  unfold Committed at *
  exact (agreement.wba_agreement r).persistent N t true hN h t' hle

/-- Skippable is persistent. -/
theorem skippable_persistent
    (agreement : SubprotocolAgreement V correct views)
    {N : NodeId} {t t' : Time} {r : Nat}
    (hN : correct N)
    (h : Skippable views N t r) (hle : t ≤ t') :
    Skippable views N t' r := by
  unfold Skippable at *
  exact (agreement.wba_agreement r).persistent N t false hN h t' hle

/-- RBOutput is persistent. -/
theorem rb_output_persistent
    (agreement : SubprotocolAgreement V correct views)
    {N : NodeId} {t t' : Time} {r : Nat}
    {p : Proposal V}
    (hN : correct N)
    (h : RBOutput views N t r = some p) (hle : t ≤ t') :
    RBOutput views N t' r = some p := by
  unfold RBOutput at *
  exact (agreement.rb_agreement r).persistent N t p hN h t' hle

/-- AcceptedAt is persistent: if AcceptedAt at (N, t), then at (N, t')
    for t' ≥ t. -/
theorem accepted_at_persistent
    (agreement : SubprotocolAgreement V correct views)
    {N : NodeId} {t t' : Time} {r : Nat} {s : Option Nat}
    (hN : correct N)
    (h : AcceptedAt views N t r s) (hle : t ≤ t') :
    AcceptedAt views N t' r s := by
  induction h with
  | mk_bot r v hall hrb =>
    exact AcceptedAt.mk_bot r v
      (fun u hu => skippable_persistent agreement hN (hall u hu) hle)
      (rb_output_persistent agreement hN hrb hle)
  | mk_parent r s v p hs hskip _hacc hrb ih =>
    exact AcceptedAt.mk_parent r s v p hs
      (fun u hsu hur => skippable_persistent agreement hN (hskip u hsu hur) hle)
      ih
      (rb_output_persistent agreement hN hrb hle)

/-- HasAccepted is persistent. -/
theorem has_accepted_persistent
    (agreement : SubprotocolAgreement V correct views)
    {N : NodeId} {t t' : Time} {r : Nat}
    (hN : correct N)
    (h : HasAccepted views N t r) (hle : t ≤ t') :
    HasAccepted views N t' r := by
  obtain ⟨s, hacc⟩ := h
  exact ⟨s, accepted_at_persistent agreement hN hacc hle⟩

/-- Ancestor is persistent. -/
theorem ancestor_persistent
    (agreement : SubprotocolAgreement V correct views)
    {N : NodeId} {t t' : Time} {s r : Nat}
    (hN : correct N)
    (h : Ancestor views N t s r) (hle : t ≤ t') :
    Ancestor views N t' s r := by
  induction h with
  | direct s r v hrb =>
    exact Ancestor.direct s r v (rb_output_persistent agreement hN hrb hle)
  | trans s p r _ _ ih1 ih2 =>
    exact Ancestor.trans s p r ih1 ih2

/-- AncestorOrEq is persistent. -/
theorem ancestor_or_eq_persistent
    (agreement : SubprotocolAgreement V correct views)
    {N : NodeId} {t t' : Time} {s r : Nat}
    (hN : correct N)
    (h : AncestorOrEq views N t s r) (hle : t ≤ t') :
    AncestorOrEq views N t' s r := by
  cases h with
  | inl heq => exact Or.inl heq
  | inr hanc => exact Or.inr (ancestor_persistent agreement hN hanc hle)

/-- Finalized is persistent. -/
theorem finalized_persistent
    (agreement : SubprotocolAgreement V correct views)
    {N : NodeId} {t t' : Time} {r : Nat}
    (hN : correct N)
    (h : Finalized views N t r) (hle : t ≤ t') :
    Finalized views N t' r := by
  obtain ⟨r', hanc, hacc, hcom⟩ := h
  exact ⟨r',
    ancestor_or_eq_persistent agreement hN hanc hle,
    has_accepted_persistent agreement hN hacc hle,
    committed_persistent agreement hN hcom hle⟩

/-! ## Part 2: Propagation to all correct nodes -/

/-- If round r is (N, t)-committed and N is correct, then for every
    correct N' there exists t' such that r is (N', t')-committed. -/
theorem committed_propagates
    (agreement : SubprotocolAgreement V correct views)
    {N N' : NodeId} {t : Time} {r : Nat}
    (hN : correct N) (hN' : correct N')
    (h : Committed views N t r) :
    ∃ t', Committed views N' t' r := by
  unfold Committed at *
  exact (agreement.wba_agreement r).agreement N N' t true hN hN' h

/-- If round r is (N, t)-skippable and N is correct, then for every
    correct N' there exists t' such that r is (N', t')-skippable. -/
theorem skippable_propagates
    (agreement : SubprotocolAgreement V correct views)
    {N N' : NodeId} {t : Time} {r : Nat}
    (hN : correct N) (hN' : correct N')
    (h : Skippable views N t r) :
    ∃ t', Skippable views N' t' r := by
  unfold Skippable at *
  exact (agreement.wba_agreement r).agreement N N' t false hN hN' h

/-- RB output propagates to all correct nodes. -/
theorem rb_output_propagates
    (agreement : SubprotocolAgreement V correct views)
    {N N' : NodeId} {t : Time} {r : Nat}
    {p : Proposal V}
    (hN : correct N) (hN' : correct N')
    (h : RBOutput views N t r = some p) :
    ∃ t', RBOutput views N' t' r = some p := by
  unfold RBOutput at *
  exact (agreement.rb_agreement r).agreement N N' t p hN hN' h

end Zug
