/-
  Zug.Concrete.FaultModel: BFT fault model and derivation of QuorumAxioms.

  Defines the `FaultModel` structure (at most f of n validators are
  Byzantine) and derives all `QuorumAxioms` fields as theorems via
  classical counting on Fin n.

  The key tool is `countSat n P`, counting elements of [0,n) satisfying P.
  We prove the equivalence between `MoreThan k n P` and `countSat n P ≥ k+1`,
  then use standard counting arguments (inclusion-exclusion) to derive
  quorum intersection properties.
-/

import Zug.Concrete.Quorum

namespace Zug.Concrete

open Zug Classical

/-! ## Fault model -/

/-- The BFT fault model: at most f of the n validators are Byzantine.

    `node_bound` says correct nodes have IDs in [0, n).
    `correct_majority` witnesses ≥ n - f correct nodes in [0, n).
    Since n > 3f, this gives ≥ 2f + 1 correct nodes. -/
structure FaultModel (cfg : NetworkConfig) (correct : Correctness) : Prop where
  /-- Correct nodes have IDs in [0, n). -/
  node_bound : ∀ N, correct N → N < cfg.n
  /-- At least n - f nodes in [0, n) are correct. -/
  correct_majority : MoreThan (cfg.n - cfg.f - 1) cfg.n correct

/-! ## Classical counting on [0, n) -/

/-- Count elements in [0, n) satisfying P, using classical decidability. -/
noncomputable def countSat : (n : Nat) → (Nat → Prop) → Nat
  | 0, _ => 0
  | n + 1, P => countSat n P + if P n then 1 else 0

@[simp] theorem countSat_zero (P : Nat → Prop) : countSat 0 P = 0 := rfl

theorem countSat_succ (n : Nat) (P : Nat → Prop) :
    countSat (n + 1) P = countSat n P + if P n then 1 else 0 := rfl

/-- countSat is bounded by n. -/
theorem countSat_le (n : Nat) (P : Nat → Prop) : countSat n P ≤ n := by
  induction n with
  | zero => simp
  | succ k ih => simp [countSat_succ]; split <;> omega

/-- P and ¬P partition [0, n). -/
theorem countSat_compl (n : Nat) (P : Nat → Prop) :
    countSat n P + countSat n (fun x => ¬P x) = n := by
  induction n with
  | zero => simp
  | succ k ih =>
    simp [countSat_succ]
    by_cases hk : P k <;> simp [hk] <;> omega

/-- Monotonicity: if P → Q on [0,n), then countSat n P ≤ countSat n Q. -/
theorem countSat_mono {n : Nat} {P Q : Nat → Prop}
    (h : ∀ x, x < n → P x → Q x) : countSat n P ≤ countSat n Q := by
  induction n with
  | zero => simp
  | succ k ih =>
    simp [countSat_succ]
    have := ih (fun x hx => h x (by omega))
    by_cases hk : P k
    · simp [hk, h k (by omega) hk]; omega
    · simp [hk]; split <;> omega

/-- Union bound: countSat n (P ∨ Q) ≤ countSat n P + countSat n Q. -/
theorem countSat_union (n : Nat) (P Q : Nat → Prop) :
    countSat n (fun x => P x ∨ Q x) ≤ countSat n P + countSat n Q := by
  induction n with
  | zero => simp
  | succ k ih =>
    simp [countSat_succ]
    have := ih
    by_cases hp : P k <;> by_cases hq : Q k <;> simp [hp, hq] <;> omega

/-- Three-way union bound. -/
theorem countSat_union₃ (n : Nat) (P Q R : Nat → Prop) :
    countSat n (fun x => P x ∨ Q x ∨ R x)
    ≤ countSat n P + countSat n Q + countSat n R := by
  have h1 := countSat_union n (fun x => P x ∨ Q x) R
  have h2 := countSat_union n P Q
  have h3 : countSat n (fun x => (P x ∨ Q x) ∨ R x)
      = countSat n (fun x => P x ∨ Q x ∨ R x) := by
    congr 1; ext x; exact or_assoc
  omega

/-! ## Equivalence: MoreThan ↔ countSat -/

/-- If MoreThan k n P, then countSat n P ≥ k + 1. -/
theorem countSat_of_moreThan {k n : Nat} {P : Nat → Prop}
    (h : MoreThan k n P) : countSat n P ≥ k + 1 := by
  obtain ⟨e, he, hp⟩ := h
  induction n generalizing k with
  | zero => exact absurd (e ⟨0, Nat.zero_lt_succ k⟩).isLt (by omega)
  | succ n ih =>
    simp [countSat_succ]
    by_cases hex : ∃ i, (e i).val = n
    · obtain ⟨i₀, hi₀⟩ := hex
      have hPn : P n := hi₀ ▸ hp i₀
      simp [hPn]
      cases k with
      | zero => omega
      | succ k' =>
        -- Build e' : Fin(k'+1) → Fin n avoiding i₀
        -- Use Fin.succAbove-like construction manually
        let skip : Fin (k' + 1) → Fin (k' + 2) := fun j =>
          if j.val < i₀.val then ⟨j.val, by omega⟩ else ⟨j.val + 1, by omega⟩
        have skip_val : ∀ j : Fin (k' + 1),
            (skip j).val = if j.val < i₀.val then j.val else j.val + 1 := by
          intro j; simp only [skip]; split <;> rfl
        have skip_ne : ∀ j, skip j ≠ i₀ := by
          intro j h
          have hv := congrArg Fin.val h
          rw [skip_val] at hv
          split at hv <;> omega
        have skip_inj : Function.Injective skip := by
          intro a b hab
          have hv := congrArg Fin.val hab
          rw [skip_val, skip_val] at hv
          ext
          split at hv <;> split at hv <;> omega
        let e' : Fin (k' + 1) → Fin n := fun j =>
          have hne : e (skip j) ≠ e i₀ := fun h => absurd (he h) (skip_ne j)
          have : (e (skip j)).val ≠ n := fun h =>
            hne (Fin.ext (by omega))
          ⟨(e (skip j)).val, by omega⟩
        have he' : Function.Injective e' := by
          intro a b hab
          have hv := congrArg Fin.val hab
          simp [e'] at hv
          exact skip_inj (he (Fin.ext hv))
        have hp' : ∀ i, P (e' i).val := fun j => hp (skip j)
        have := ih e' he' hp'
        omega
    · -- No element maps to n
      simp at hex
      let e' : Fin (k + 1) → Fin n := fun i =>
        ⟨(e i).val, by have := (e i).isLt; have := hex i; omega⟩
      have he' : Function.Injective e' := by
        intro a b hab
        have := congrArg Fin.val hab
        simp [e'] at this
        exact he (Fin.ext this)
      have hp' : ∀ i, P (e' i).val := fun i => hp i
      have := ih e' he' hp'
      split <;> omega

/-- If countSat n P ≥ k + 1, then MoreThan k n P. -/
theorem moreThan_of_countSat {k n : Nat} {P : Nat → Prop}
    (h : countSat n P ≥ k + 1) : MoreThan k n P := by
  induction n generalizing k with
  | zero => simp at h
  | succ n ih =>
    simp [countSat_succ] at h
    by_cases hPn : P n
    · simp [hPn] at h
      cases k with
      | zero =>
        exact ⟨fun _ => ⟨n, by omega⟩,
          fun a b _ => Fin.ext (by have := a.isLt; have := b.isLt; omega),
          fun _ => hPn⟩
      | succ k' =>
        have ⟨e, he, hp⟩ := ih (k := k') (by omega : countSat n P ≥ k' + 1)
        -- Extend e with n at position k'+1
        let f : Fin (k' + 2) → Fin (n + 1) := fun i =>
          if hi : i.val < k' + 1
          then ⟨(e ⟨i.val, hi⟩).val, by have := (e ⟨i.val, hi⟩).isLt; omega⟩
          else ⟨n, by omega⟩
        refine ⟨f, ?_, ?_⟩
        · intro a b hab
          have hv := congrArg Fin.val hab
          simp only [f] at hv
          by_cases ha : a.val < k' + 1 <;> by_cases hb : b.val < k' + 1
          · simp only [dif_pos ha, dif_pos hb] at hv
            have := he (Fin.ext hv)
            exact Fin.ext (congrArg (fun (x : Fin (k' + 1)) => x.val) this)
          · simp only [dif_pos ha, dif_neg hb] at hv
            exact absurd hv (by have := (e ⟨a.val, ha⟩).isLt; omega)
          · simp only [dif_neg ha, dif_pos hb] at hv
            exact absurd hv.symm (by have := (e ⟨b.val, hb⟩).isLt; omega)
          · exact Fin.ext (by omega)
        · intro i; simp only [f]; split
          · exact hp ⟨i.val, by assumption⟩
          · exact hPn
    · simp [hPn] at h
      have ⟨e, he, hp⟩ := ih h
      refine ⟨fun i => ⟨(e i).val, by have := (e i).isLt; omega⟩, ?_, fun i => hp i⟩
      intro a b hab
      have hv := congrArg Fin.val hab
      simp only at hv
      exact he (Fin.ext hv)

/-- If a + b = n and a < n, then b ≥ 1. -/
private theorem pos_of_compl_lt {a b n : Nat} (h1 : a + b = n) (h2 : a < n) : b ≥ 1 := by
  omega

/-! ## QuorumAxioms from FaultModel -/

/-- q ≥ 2f when n > 3f. -/
private theorem q_ge_2f (cfg : NetworkConfig) : cfg.q ≥ 2 * cfg.f := by
  have : cfg.q = (cfg.n + cfg.f) / 2 := rfl
  have := cfg.fault_tolerance
  omega

/-- n - f - 1 ≥ q when n > 3f. -/
private theorem n_sub_f_sub_one_ge_q (cfg : NetworkConfig) :
    cfg.n - cfg.f - 1 ≥ cfg.q := by
  have : cfg.q = (cfg.n + cfg.f) / 2 := rfl
  have := cfg.fault_tolerance
  omega

/-- Faulty count: at most f nodes are not correct. -/
private theorem faulty_count_le (cfg : NetworkConfig) (correct : Correctness)
    (fm : FaultModel cfg correct) :
    countSat cfg.n (fun x => ¬correct x) ≤ cfg.f := by
  have h1 := countSat_compl cfg.n correct
  have h2 := countSat_of_moreThan fm.correct_majority
  have h3 := n_sub_f_sub_one_ge_q cfg
  omega

/-- Derive all QuorumAxioms from a FaultModel. -/
noncomputable def QuorumAxioms.ofFaultModel
    (cfg : NetworkConfig) (correct : Correctness)
    (fm : FaultModel cfg correct) : QuorumAxioms cfg correct where
  node_bound := fm.node_bound

  quorum_intersection := by
    intro A B hA hB
    -- Complement equations and lower bounds
    have h_compA := countSat_compl cfg.n A
    have h_compB := countSat_compl cfg.n B
    have hcA := countSat_of_moreThan hA
    have hcB := countSat_of_moreThan hB
    have hcF := faulty_count_le cfg correct fm
    have h_qi := cfg.quorum_intersection
    -- Key step: sum of negation counts < n
    have h_neg_sum_lt : countSat cfg.n (fun x => ¬A x)
        + countSat cfg.n (fun x => ¬B x)
        + countSat cfg.n (fun x => ¬correct x) < cfg.n := by omega
    -- Union₃ gives bound on the compound negation
    have h_union := countSat_union₃ cfg.n
      (fun x => ¬A x) (fun x => ¬B x) (fun x => ¬correct x)
    -- Complement of (A ∧ B ∧ correct)
    have h_compl := countSat_compl cfg.n (fun x => ¬A x ∨ ¬B x ∨ ¬correct x)
    have h_eq : (fun x => ¬(¬A x ∨ ¬B x ∨ ¬correct x))
        = (fun x => A x ∧ B x ∧ correct x) := by
      ext x; simp [not_or]
    rw [h_eq] at h_compl
    -- Bound on the compound negation
    have h_neg_lt : countSat cfg.n (fun x => ¬A x ∨ ¬B x ∨ ¬correct x) < cfg.n :=
      Nat.lt_of_le_of_lt h_union h_neg_sum_lt
    -- Positive count ≥ 1
    have h_pos : countSat cfg.n (fun x => A x ∧ B x ∧ correct x) ≥ 1 :=
      pos_of_compl_lt h_compl h_neg_lt
    obtain ⟨e, _, hp⟩ := moreThan_of_countSat h_pos
    exact ⟨(e ⟨0, by omega⟩).val, (hp ⟨0, by omega⟩).2.2,
      (hp ⟨0, by omega⟩).1, (hp ⟨0, by omega⟩).2.1⟩

  quorum_correct_subset := by
    intro P hP
    have h_compP := countSat_compl cfg.n P
    have hcP := countSat_of_moreThan hP
    have hcF := faulty_count_le cfg correct fm
    -- ¬(correct ∧ P) → ¬correct ∨ ¬P (classical De Morgan)
    have h_neg_mono : countSat cfg.n (fun x => ¬(correct x ∧ P x))
        ≤ countSat cfg.n (fun x => ¬correct x ∨ ¬P x) :=
      countSat_mono (fun x _ h => by
        by_cases hc : correct x
        · exact Or.inr (fun hp => h ⟨hc, hp⟩)
        · exact Or.inl hc)
    have h_neg_union := countSat_union cfg.n (fun x => ¬correct x) (fun x => ¬P x)
    have h_compl := countSat_compl cfg.n (fun x => correct x ∧ P x)
    have h_q := q_ge_2f cfg
    have h_bound : countSat cfg.n (fun x => correct x ∧ P x) ≥ cfg.f + 1 := by omega
    exact moreThan_of_countSat h_bound

  all_correct_quorum := by
    intro P hP
    have hC := fm.correct_majority
    have hP' : MoreThan (cfg.n - cfg.f - 1) cfg.n P :=
      hC.mono fun N hcorr => hP N hcorr (fm.node_bound N hcorr)
    exact hP'.weaken (n_sub_f_sub_one_ge_q cfg)

end Zug.Concrete
