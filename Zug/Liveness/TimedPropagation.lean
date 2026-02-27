/-
  Zug.Liveness.TimedPropagation: Timed propagation lemmas (Lemma 1, part 3).

  If a property holds at a correct node N at time t ≥ GST, it holds at
  every correct node N' by time t + Δ. This follows from the timed delay
  axioms on RB and WBA.
-/

import Zug.Protocol.Execution

namespace Zug

variable {V : Type}
variable {ctx : ExecutionContext V}

/-! ## Timed propagation of individual predicates -/

/-- Skippable timed propagation: if Skippable at (N, t) with t ≥ GST,
    then Skippable at (N', t + Δ) for all correct N'. -/
theorem skippable_timed_propagation
    (pb : ProtocolBehavior V ctx)
    {N N' : NodeId} {t : Time} {r : Nat}
    (hN : ctx.correct N) (hN' : ctx.correct N')
    (hgst : ctx.sync.gst ≤ t)
    (h : Skippable ctx.views N t r) :
    Skippable ctx.views N' (t + ctx.sync.delta) r := by
  unfold Skippable at *
  exact (pb.wba_timed_delay r).timed_delay N N' t false hN hN' hgst h

/-- Committed timed propagation: if Committed at (N, t) with t ≥ GST,
    then Committed at (N', t + Δ) for all correct N'. -/
theorem committed_timed_propagation
    (pb : ProtocolBehavior V ctx)
    {N N' : NodeId} {t : Time} {r : Nat}
    (hN : ctx.correct N) (hN' : ctx.correct N')
    (hgst : ctx.sync.gst ≤ t)
    (h : Committed ctx.views N t r) :
    Committed ctx.views N' (t + ctx.sync.delta) r := by
  unfold Committed at *
  exact (pb.wba_timed_delay r).timed_delay N N' t true hN hN' hgst h

/-- RB output timed propagation: if RBOutput at (N, t) with t ≥ GST,
    then RBOutput at (N', t + Δ) for all correct N'. -/
theorem rb_output_timed_propagation
    (pb : ProtocolBehavior V ctx)
    {N N' : NodeId} {t : Time} {r : Nat} {p : Proposal V}
    (hN : ctx.correct N) (hN' : ctx.correct N')
    (hgst : ctx.sync.gst ≤ t)
    (h : RBOutput ctx.views N t r = some p) :
    RBOutput ctx.views N' (t + ctx.sync.delta) r = some p := by
  unfold RBOutput at *
  exact (pb.rb_timed_delay r).timed_delay N N' t p hN hN' hgst h

/-! ## Timed propagation of AcceptedAt -/

/-- AcceptedAt timed propagation: if AcceptedAt at (N, t) with t ≥ GST,
    then AcceptedAt at (N', t + Δ) for all correct N'.

    Proved by induction on AcceptedAt: each component (skippable gaps,
    RB outputs, parent acceptance) propagates within Δ at the same time t,
    so they all hold at (N', t + Δ). -/
theorem accepted_at_timed_propagation
    (pb : ProtocolBehavior V ctx)
    {N N' : NodeId} {t : Time} {r : Nat} {s : Option Nat}
    (hN : ctx.correct N) (hN' : ctx.correct N')
    (hgst : ctx.sync.gst ≤ t)
    (h : AcceptedAt ctx.views N t r s) :
    AcceptedAt ctx.views N' (t + ctx.sync.delta) r s := by
  induction h with
  | mk_bot r v hall hrb =>
    exact AcceptedAt.mk_bot r v
      (fun u hu => skippable_timed_propagation pb hN hN' hgst (hall u hu))
      (rb_output_timed_propagation pb hN hN' hgst hrb)
  | mk_parent r s v p hs hskip _hacc hrb ih =>
    exact AcceptedAt.mk_parent r s v p hs
      (fun u hsu hur => skippable_timed_propagation pb hN hN' hgst (hskip u hsu hur))
      ih
      (rb_output_timed_propagation pb hN hN' hgst hrb)

/-- HasAccepted timed propagation. -/
theorem has_accepted_timed_propagation
    (pb : ProtocolBehavior V ctx)
    {N N' : NodeId} {t : Time} {r : Nat}
    (hN : ctx.correct N) (hN' : ctx.correct N')
    (hgst : ctx.sync.gst ≤ t)
    (h : HasAccepted ctx.views N t r) :
    HasAccepted ctx.views N' (t + ctx.sync.delta) r := by
  obtain ⟨s, hacc⟩ := h
  exact ⟨s, accepted_at_timed_propagation pb hN hN' hgst hacc⟩

/-! ## Timed propagation of ReachedRound -/

/-- ReachedRound timed propagation: if correct N has reached round r
    at time t ≥ GST, then every correct N' has reached round r by t + Δ.

    Follows because each lower round is either skippable or has accepted,
    and both propagate within Δ. -/
theorem reached_round_timed_propagation
    (pb : ProtocolBehavior V ctx)
    {N N' : NodeId} {t : Time} {r : Nat}
    (hN : ctx.correct N) (hN' : ctx.correct N')
    (hgst : ctx.sync.gst ≤ t)
    (h : ReachedRound ctx.views N t r) :
    ReachedRound ctx.views N' (t + ctx.sync.delta) r := by
  intro s hs
  rcases h s hs with hskip | hacc
  · exact Or.inl (skippable_timed_propagation pb hN hN' hgst hskip)
  · exact Or.inr (has_accepted_timed_propagation pb hN hN' hgst hacc)

end Zug
