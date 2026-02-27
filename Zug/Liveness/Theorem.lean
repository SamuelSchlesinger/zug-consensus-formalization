/-
  Zug.Liveness.Theorem: Theorem 2 (Censorship Resilience / Liveness).

  Every correct proposer eventually has one of its rounds committed.
  Combined with the safety proof (Theorem 1), this ensures that every
  correct proposer's values are eventually output by all correct nodes.

  The proof combines:
  - Lemma 3 (round_progress): all correct nodes reach any round r
    by GST + 3rΔ.
  - Lemma 4 (correct_leader_committed): if round r has a correct leader,
    it is committed by GST + 3rΔ + 3Δ.
  - Infinite leadership: every correct node leads infinitely many rounds.
  - Safety agreement (Theorem 1): all correct nodes finalize committed rounds.
-/

import Zug.Liveness.CorrectLeader
import Zug.Safety.Theorem

namespace Zug

variable {V : Type}
variable {ctx : ExecutionContext V}

/-- A committed round with HasAccepted is finalized: take r' = r in the
    Finalized definition (AncestorOrEq is reflexive). -/
theorem committed_and_accepted_finalized
    {N : NodeId} {t : Time} {r : Nat}
    (hcom : Committed ctx.views N t r)
    (hacc : HasAccepted ctx.views N t r) :
    Finalized ctx.views N t r :=
  ⟨r, Or.inl rfl, hacc, hcom⟩

/-- Theorem 2 (Censorship Resilience): For every correct node L and
    every round r₀, there exists a round r ≥ r₀ where L is leader
    and round r is finalized at all correct nodes.

    This means every correct proposer eventually gets one of its rounds
    committed and finalized. Combined with the total ordering of
    finalized rounds (Theorem 1), this ensures that every value proposed
    by a correct leader in such a round is eventually output by all
    correct nodes. -/
theorem censorship_resilience
    (pb : ProtocolBehavior V ctx)
    (L : NodeId) (hL : ctx.correct L)
    (r₀ : Nat) :
    ∃ r, r ≥ r₀ ∧ ctx.leaders.leader r = L ∧
      ∀ N, ctx.correct N → ∃ t, Finalized ctx.views N t r := by
  -- Step 1: By infinite leadership, L leads some round r ≥ r₀
  obtain ⟨r, hr_ge, hr_leader⟩ := ctx.leaders.infinite_leadership L hL r₀
  refine ⟨r, hr_ge, hr_leader, ?_⟩
  -- Step 2: The leader is correct
  have hleader_correct : ctx.correct (ctx.leaders.leader r) := hr_leader ▸ hL
  -- Step 3: All correct nodes reach round r by GST + 3rΔ (Lemma 3)
  have hall_reach : ∀ N, ctx.correct N →
      ReachedRound ctx.views N (ctx.sync.gst + 3 * r * ctx.sync.delta) r :=
    fun N hN => round_progress pb r N hN
  -- Step 4: Round r is committed at all correct by GST + 3rΔ + 3Δ (Lemma 4)
  have h_committed : ∀ N, ctx.correct N →
      Committed ctx.views N
        (ctx.sync.gst + 3 * r * ctx.sync.delta + 3 * ctx.sync.delta) r :=
    correct_leader_committed pb (Nat.le_add_right _ _) hall_reach hleader_correct
  -- Step 5: All correct have HasAccepted by the same time
  have h_accepted : ∀ N, ctx.correct N →
      HasAccepted ctx.views N
        (ctx.sync.gst + 3 * r * ctx.sync.delta + 3 * ctx.sync.delta) r := by
    intro N hN
    have hacc := pb.leader_proposal r (ctx.sync.gst + 3 * r * ctx.sync.delta) N
      hleader_correct hN (Nat.le_add_right _ _) (hall_reach _ hleader_correct)
    -- HasAccepted at GST + 3rΔ + Δ, persist to GST + 3rΔ + 3Δ
    exact has_accepted_persistent pb.agreement hN hacc
      (Nat.add_le_add_left (Nat.le_mul_of_pos_left ctx.sync.delta (by omega)) _)
  -- Step 6: Committed + HasAccepted → Finalized
  intro N hN
  exact ⟨ctx.sync.gst + 3 * r * ctx.sync.delta + 3 * ctx.sync.delta,
    committed_and_accepted_finalized (h_committed N hN) (h_accepted N hN)⟩

end Zug
