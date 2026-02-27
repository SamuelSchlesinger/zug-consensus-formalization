/-
  Zug.Protocol.Execution: Execution model for liveness proofs.

  Defines ReachedRound, LeaderSequence, and the ProtocolBehavior axiom
  bundle that captures observable consequences of protocol execution
  without modeling a full state machine.

  This mirrors the approach used for safety: rather than building a
  reactive state machine (heavy, error-prone), we axiomatize the
  *observable consequences* of the protocol's behavior.

  The paper's liveness proofs only need timing relationships between
  events ("all correct nodes reach round r by time t" → "WBA[r] outputs
  by t + 3Δ"), not internal node state.
-/

import Zug.Safety.Monotonicity

namespace Zug

variable {V : Type}

/-! ## Round progress predicates -/

/-- A node has reached round r when all lower rounds are settled
    (either skippable or has an accepted value).

    This captures the paper's notion of "node N is at round r" without
    modeling internal state: N has enough information to participate
    in round r because all prior rounds are resolved. -/
def ReachedRound (views : SubprotocolViews V) (N : NodeId) (t : Time)
    (r : Nat) : Prop :=
  ∀ s, s < r → Skippable views N t s ∨ HasAccepted views N t s

/-! ## Leader sequence -/

/-- Leader assignment: maps round numbers to proposer node IDs.
    Every correct node is the designated leader of infinitely many rounds.

    The infinite leadership property ensures liveness: no correct node
    can be permanently excluded from proposing. -/
structure LeaderSequence (correct : Correctness) where
  /-- The designated proposer for round r. -/
  leader : Nat → NodeId
  /-- Every correct node leads infinitely many rounds. -/
  infinite_leadership : ∀ N, correct N → ∀ r, ∃ r', r' ≥ r ∧ leader r' = N

/-! ## Execution context and protocol behavior -/

/-- An execution context bundles all the parameters needed for the
    liveness proof: correctness predicate, subprotocol views, synchrony
    parameters, leader sequence, and WBA input tracking. -/
structure ExecutionContext (V : Type) where
  /-- Which nodes are correct (not Byzantine). -/
  correct : Correctness
  /-- Observable subprotocol outputs for each round. -/
  views : SubprotocolViews V
  /-- Partial synchrony parameters (GST and Δ). -/
  sync : PartialSynchrony
  /-- Leader assignment for each round. -/
  leaders : LeaderSequence correct
  /-- WBA input tracking: for each round r and node N, records when
      (if ever) node N provided input to WBA[r], and what bit it input. -/
  wba_input : Nat → NodeId → Option (Time × Bool)

/-- ProtocolBehavior: axiomatized observable consequences of protocol
    execution. These are the assumptions beyond SubprotocolAgreement
    needed for the liveness proof (Theorem 2).

    The axioms are organized as:
    - Axioms 1–3: Timed subprotocol properties (delay bounds + weak termination)
    - Axiom 4: Protocol initialization
    - Axioms 5–6: Node behavior (timer and voting rules from §5.3)
    - Axiom 7: Leader behavior (proposal construction + RB delivery) -/
structure ProtocolBehavior (V : Type) (ctx : ExecutionContext V) : Prop where
  /-- The underlying safety properties (Agreement + Persistence for all
      RB and WBA instances). Required by the liveness proof when it
      invokes persistence lemmas. -/
  agreement : SubprotocolAgreement V ctx.correct ctx.views

  /-- Axiom 1: RB timed delay — after GST, if any correct node sees
      an RB output at time t, all correct nodes see it by t + Δ. -/
  rb_timed_delay : ∀ r, RBTimedDelay ctx.correct (ctx.views.rb r)
    ctx.sync.gst ctx.sync.delta

  /-- Axiom 2: WBA timed delay — after GST, if any correct node sees
      a WBA output at time t, all correct nodes see it by t + Δ. -/
  wba_timed_delay : ∀ r, WBATimedDelay ctx.correct (ctx.views.wba r)
    ctx.sync.gst ctx.sync.delta

  /-- Axiom 3: WBA timed weak termination — after GST, if all correct
      nodes input the same bit b to WBA[r] by time t, all correct nodes
      output b by t + Δ. -/
  wba_weak_termination : ∀ r, WBATimedWeakTermination ctx.correct
    (ctx.views.wba r) ctx.sync.gst ctx.sync.delta (ctx.wba_input r)

  /-- Axiom 4: All correct nodes start (reach round 0) before GST.
      This models the protocol assumption that all correct nodes are
      initialized and running before synchrony is established. -/
  correct_start : ∀ N, ctx.correct N →
    ReachedRound ctx.views N ctx.sync.gst 0

  /-- Axiom 5: Timer — if a correct node reaches round r at time t ≥ GST
      and has not accepted a value for r by time t + 2Δ, it inputs 0
      (skip) to WBA[r].

      This models the timeout mechanism from §5.3: nodes wait 2Δ for a
      valid proposal before voting to skip the round. -/
  timer_axiom : ∀ N r t, ctx.correct N →
    ctx.sync.gst ≤ t →
    ReachedRound ctx.views N t r →
    (¬HasAccepted ctx.views N (t + 2 * ctx.sync.delta) r) →
    ∃ ti, ti ≤ t + 2 * ctx.sync.delta ∧
      ctx.wba_input r N = some (ti, false)

  /-- Axiom 6: Vote — if a correct node has accepted a value for round r,
      it inputs 1 (commit) to WBA[r].

      This models the voting rule from §5.3: nodes that see a valid
      accepted proposal vote to commit the round. -/
  vote_axiom : ∀ N r t, ctx.correct N →
    HasAccepted ctx.views N t r →
    ∃ ti, ti ≤ t ∧ ctx.wba_input r N = some (ti, true)

  /-- Axiom 7: Leader proposal — if the leader of round r is correct and
      reaches round r at time t ≥ GST, then all correct nodes have
      HasAccepted for round r by t + Δ.

      This axiom combines three protocol steps:
      (a) The correct leader constructs a valid proposal from its own
          settled rounds (its ReachedRound gives a valid parent chain).
      (b) RB delivers the proposal to all correct nodes within Δ.
      (c) Each receiver's settled rounds (which by timed propagation
          match the leader's within Δ) validate the parent chain,
          yielding AcceptedAt. -/
  leader_proposal : ∀ r t N, ctx.correct (ctx.leaders.leader r) →
    ctx.correct N →
    ctx.sync.gst ≤ t →
    ReachedRound ctx.views (ctx.leaders.leader r) t r →
    HasAccepted ctx.views N (t + ctx.sync.delta) r

/-! ## Helper lemmas about ReachedRound -/

/-- ReachedRound is persistent: if reached at time t, still reached at
    t' ≥ t. Follows because Skippable and HasAccepted are each persistent. -/
theorem reached_round_persistent
    (agreement : SubprotocolAgreement V correct views)
    {N : NodeId} {t t' : Time} {r : Nat}
    (hN : correct N)
    (h : ReachedRound views N t r) (hle : t ≤ t') :
    ReachedRound views N t' r := by
  intro s hs
  rcases h s hs with hskip | hacc
  · exact Or.inl (skippable_persistent agreement hN hskip hle)
  · exact Or.inr (has_accepted_persistent agreement hN hacc hle)

/-- ReachedRound is monotone in round number. -/
theorem reached_round_mono
    {views : SubprotocolViews V} {N : NodeId} {t : Time} {r s : Nat}
    (h : ReachedRound views N t r) (hle : s ≤ r) :
    ReachedRound views N t s := by
  intro u hu
  exact h u (Nat.lt_of_lt_of_le hu hle)

/-- ReachedRound 0 is vacuously true (no lower rounds to settle). -/
theorem reached_round_zero (views : SubprotocolViews V) (N : NodeId) (t : Time) :
    ReachedRound views N t 0 := by
  intro s hs
  exact absurd hs (Nat.not_lt_zero s)

end Zug
