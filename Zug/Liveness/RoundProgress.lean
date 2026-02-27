/-
  Zug.Liveness.RoundProgress: Lemma 3 from the paper.

  After GST, rounds progress at a bounded rate: at time GST + 3rΔ,
  every correct node has reached round r.

  The proof proceeds by induction on r:
  - Base case: ReachedRound 0 is vacuously true.
  - Inductive step: By IH all correct nodes reach round k by GST + 3kΔ.
    We show round k is "settled" (skippable or accepted) by GST + 3kΔ + 3Δ
    via a case split:
    (A) Some correct node accepts → timed propagation → all accept by + 3Δ.
    (B) No one accepts within 2Δ → timer fires → all input 0 → WBA weak
        termination → round skippable by + 3Δ.
-/

import Zug.Liveness.TimedPropagation

namespace Zug

variable {V : Type}
variable {ctx : ExecutionContext V}

/-! ## Nat arithmetic helpers

  The `omega` tactic cannot see through nested struct field projections
  like `ctx.sync.delta`. We provide explicit lemmas for the arithmetic
  identities needed in timing proofs.
-/

/-- 2Δ + Δ = 3Δ. -/
private theorem time_2d_plus_d (T : Time) :
    T + 2 * ctx.sync.delta + ctx.sync.delta = T + 3 * ctx.sync.delta := by
  rw [Nat.add_assoc]; congr 1; rw [← Nat.succ_mul]

/-- 3(k+1)Δ = 3kΔ + 3Δ. -/
private theorem three_succ_mul (k d : Nat) :
    3 * (k + 1) * d = 3 * k * d + 3 * d := by
  simp [Nat.add_mul, Nat.mul_assoc, Nat.mul_add]

/-! ## Round settling -/

/-- If all correct nodes reach round r by time T ≥ GST, then for every
    correct node, round r is settled (skippable or accepted) by T + 3Δ.

    Case A: Some correct node accepts for r by T + 2Δ. By timed
    propagation (Δ more), all correct nodes accept by T + 3Δ.

    Case B: No correct node accepts for r by T + 2Δ. By the timer axiom,
    every correct node inputs 0 to WBA[r] by T + 2Δ. By WBA weak
    termination, all output 0 (skippable) by T + 3Δ. -/
theorem round_settles
    (pb : ProtocolBehavior V ctx)
    {T : Time} {r : Nat}
    (hgst : ctx.sync.gst ≤ T)
    (hall_reach : ∀ N, ctx.correct N → ReachedRound ctx.views N T r) :
    ∀ N, ctx.correct N →
      Skippable ctx.views N (T + 3 * ctx.sync.delta) r ∨
      HasAccepted ctx.views N (T + 3 * ctx.sync.delta) r := by
  have h_arith := time_2d_plus_d (ctx := ctx) T
  have hgst' : ctx.sync.gst ≤ T + 2 * ctx.sync.delta :=
    Nat.le_trans hgst (Nat.le_add_right T _)
  by_cases h_case : ∃ N, ctx.correct N ∧ HasAccepted ctx.views N (T + 2 * ctx.sync.delta) r
  · -- Case A: some correct node accepted by T + 2Δ
    obtain ⟨N, hN, hacc⟩ := h_case
    intro N' hN'
    right
    have h_prop := has_accepted_timed_propagation pb hN hN' hgst' hacc
    rw [h_arith] at h_prop; exact h_prop
  · -- Case B: no correct node accepted by T + 2Δ → all input 0 → skippable
    have h_no_acc : ∀ N, ctx.correct N →
        ¬HasAccepted ctx.views N (T + 2 * ctx.sync.delta) r :=
      fun N hN hacc => h_case ⟨N, hN, hacc⟩
    have h_all_input_0 : ∀ N, ctx.correct N →
        ∃ ti, ti ≤ T + 2 * ctx.sync.delta ∧ ctx.wba_input r N = some (ti, false) :=
      fun N hN => pb.timer_axiom N r T hN hgst (hall_reach N hN) (h_no_acc N hN)
    intro N' hN'
    left
    have h_wt := (pb.wba_weak_termination r).weak_termination
      (T + 2 * ctx.sync.delta) false hgst' h_all_input_0 N' hN'
    unfold Skippable
    rw [h_arith] at h_wt; exact h_wt

/-! ## Lemma 3: Round Progress -/

/-- Induction-friendly form with explicit time parameter T. -/
private theorem round_progress_aux
    (pb : ProtocolBehavior V ctx)
    (r : Nat) (T : Time)
    (hT : T = 3 * r * ctx.sync.delta) :
    ∀ N, ctx.correct N →
      ReachedRound ctx.views N (ctx.sync.gst + T) r := by
  induction r generalizing T with
  | zero =>
    intro N _
    subst hT; simp [Nat.mul_zero, Nat.add_zero]
    exact reached_round_zero ctx.views N ctx.sync.gst
  | succ k ih =>
    intro N hN
    -- T = 3(k+1)Δ = 3kΔ + 3Δ
    have h_Tk_eq : 3 * k * ctx.sync.delta + 3 * ctx.sync.delta = T := by
      rw [hT, three_succ_mul]
    -- By IH: all correct reach round k by GST + 3kΔ
    have ih_all : ∀ N', ctx.correct N' →
        ReachedRound ctx.views N' (ctx.sync.gst + 3 * k * ctx.sync.delta) k :=
      fun N' hN' => ih (3 * k * ctx.sync.delta) rfl N' hN'
    -- By round_settles: round k settled by GST + 3kΔ + 3Δ = GST + T
    have h_settles := round_settles pb (Nat.le_add_right _ _) ih_all
    -- Time arithmetic: GST + 3kΔ + 3Δ = GST + T
    have h_time_eq : ctx.sync.gst + 3 * k * ctx.sync.delta + 3 * ctx.sync.delta =
        ctx.sync.gst + T := by rw [Nat.add_assoc, h_Tk_eq]
    -- GST + 3kΔ ≤ GST + T
    have hle_Tk_T : ctx.sync.gst + 3 * k * ctx.sync.delta ≤ ctx.sync.gst + T := by
      rw [← h_Tk_eq]; exact Nat.add_le_add_left (Nat.le_add_right _ _) _
    -- Show ∀ s < k+1, round s is settled at GST + T
    intro s hs
    rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hs) with heq | hlt
    · -- s = k: use round_settles result
      subst heq
      rcases h_settles N hN with hskip | hacc
      · left; rw [← h_time_eq]; exact hskip
      · right; rw [← h_time_eq]; exact hacc
    · -- s < k: settled since GST + 3kΔ, persistent to GST + T
      rcases ih_all N hN s hlt with hskip | hacc
      · left; exact skippable_persistent pb.agreement hN hskip hle_Tk_T
      · right; exact has_accepted_persistent pb.agreement hN hacc hle_Tk_T

/-- Lemma 3 (Round Progress): At time GST + 3rΔ, every correct node
    has reached round r. -/
theorem round_progress
    (pb : ProtocolBehavior V ctx) :
    ∀ r N, ctx.correct N →
      ReachedRound ctx.views N (ctx.sync.gst + 3 * r * ctx.sync.delta) r :=
  fun r => round_progress_aux pb r (3 * r * ctx.sync.delta) rfl

end Zug
