/-
  Zug.Liveness.CorrectLeader: Lemma 4 from the paper.

  If a round r has a correct leader and all correct nodes have reached
  round r by some time T ≥ GST, then round r is committed for all
  correct nodes by T + 3Δ.

  The proof:
  1. Leader proposes, all correct nodes have HasAccepted by T + Δ.
  2. All correct nodes input 1 (commit) to WBA[r] by T + Δ.
  3. WBA weak termination: all output 1 by T + 2Δ.
  4. Persistence: committed at T + 2Δ ≤ T + 3Δ.
-/

import Zug.Liveness.RoundProgress

namespace Zug

variable {V : Type}
variable {ctx : ExecutionContext V}

/-- Lemma 4: If all correct nodes reach round r by T ≥ GST and the
    leader of round r is correct, then round r is committed for all
    correct nodes by T + 3Δ. -/
theorem correct_leader_committed
    (pb : ProtocolBehavior V ctx)
    {T : Time} {r : Nat}
    (hgst : ctx.sync.gst ≤ T)
    (hall_reach : ∀ N, ctx.correct N → ReachedRound ctx.views N T r)
    (hleader_correct : ctx.correct (ctx.leaders.leader r)) :
    ∀ N, ctx.correct N →
      Committed ctx.views N (T + 3 * ctx.sync.delta) r := by
  intro N' hN'
  -- Step 1: All correct have HasAccepted by T + Δ (leader_proposal)
  have h_all_accepted : ∀ N'', ctx.correct N'' →
      HasAccepted ctx.views N'' (T + ctx.sync.delta) r :=
    fun N'' hN'' => pb.leader_proposal r T N''
      hleader_correct hN'' hgst (hall_reach _ hleader_correct)
  -- Step 2: All correct input 1 to WBA[r] by T + Δ (vote_axiom)
  have h_all_vote : ∀ N'', ctx.correct N'' →
      ∃ ti, ti ≤ T + ctx.sync.delta ∧
        ctx.wba_input r N'' = some (ti, true) :=
    fun N'' hN'' => pb.vote_axiom N'' r (T + ctx.sync.delta)
      hN'' (h_all_accepted N'' hN'')
  -- Step 3: WBA weak termination → all output 1 by T + 2Δ
  have hgst_delta : ctx.sync.gst ≤ T + ctx.sync.delta :=
    Nat.le_trans hgst (Nat.le_add_right T _)
  have h_wba_out := (pb.wba_weak_termination r).weak_termination
    (T + ctx.sync.delta) true hgst_delta h_all_vote N' hN'
  -- Step 4: Persistence from T + 2Δ to T + 3Δ
  unfold Committed
  have h_le : T + ctx.sync.delta + ctx.sync.delta ≤ T + 3 * ctx.sync.delta := by
    rw [Nat.add_assoc]; apply Nat.add_le_add_left
    rw [← Nat.two_mul]
    exact Nat.mul_le_mul_right _ (by omega)
  exact (pb.agreement.wba_agreement r).persistent N' _ true hN' h_wba_out _ h_le

/-- Corollary: If round r has a correct leader, then round r is committed
    for all correct nodes by GST + 3rΔ + 3Δ.

    Combines round_progress (Lemma 3) with correct_leader_committed. -/
theorem correct_leader_committed_at
    (pb : ProtocolBehavior V ctx)
    {r : Nat}
    (hleader_correct : ctx.correct (ctx.leaders.leader r)) :
    ∀ N, ctx.correct N →
      Committed ctx.views N
        (ctx.sync.gst + 3 * r * ctx.sync.delta + 3 * ctx.sync.delta) r :=
  correct_leader_committed pb (Nat.le_add_right _ _)
    (fun N hN => round_progress pb r N hN) hleader_correct

end Zug
