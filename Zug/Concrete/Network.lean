/-
  Zug.Concrete.Network: Point-to-point network model and shared timing
  helpers for concrete RB and WBA implementations.

  Declarative Prop-valued predicates matching the existing codebase style.
  `sent S m t` means node S broadcast message m at time t.
  `received R S m t` means node R has received message m (allegedly from S)
  by time t.
-/

import Zug.Subprotocols

namespace Zug

/-- A network configuration with n validators, f of which may be faulty. -/
structure NetworkConfig where
  /-- Number of validators. -/
  n : Nat
  /-- Maximum number of faulty validators. -/
  f : Nat
  /-- Byzantine fault tolerance: n > 3f. -/
  fault_tolerance : n > 3 * f

namespace NetworkConfig

/-- The quorum threshold. A quorum has strictly more than q members.
    q = (n + f) / 2, using natural number division (floor). -/
def q (cfg : NetworkConfig) : Nat := (cfg.n + cfg.f) / 2

/-- Two quorums (each with > q members) overlap in > f validators.
    Since at most f are faulty, they share ≥ 1 correct validator.

    Proof: Each quorum has > (n+f)/2 members, so two have
    > 2 * (n+f)/2 ≥ n+f total "slots". Since there are only n validators,
    the overlap is > n+f - n = f. -/
theorem quorum_intersection (cfg : NetworkConfig) :
    cfg.n + cfg.f < 2 * (cfg.q + 1) := by
  unfold q
  omega

end NetworkConfig

end Zug

namespace Zug.Concrete

/-- A point-to-point network carrying messages of type `Msg`. -/
structure PtPNetwork (Msg : Type) where
  /-- Node S broadcast message m at time t. -/
  sent : NodeId → Msg → Time → Prop
  /-- Node R has received message m from S by time t. -/
  received : NodeId → NodeId → Msg → Time → Prop

/-- Properties of a partially synchronous point-to-point network.
    These hold for all correct nodes after GST. -/
structure NetworkProperties (Msg : Type)
    (correct : Correctness) (net : PtPNetwork Msg)
    (gst delta_net : Time) : Prop where
  /-- Eventual delivery: if correct S sends m, every correct R
      eventually receives it. -/
  eventual_delivery : ∀ S R m t_send, correct S → correct R →
    net.sent S m t_send →
    ∃ t_recv, t_send ≤ t_recv ∧ net.received R S m t_recv
  /-- Bounded delay (standard partial synchrony): any message sent by
      a correct node is received by every correct node by
      max(GST, t_send) + δ_net. Messages sent before GST arrive by
      GST + δ_net; messages sent after GST arrive by t_send + δ_net. -/
  bounded_delay : ∀ S R m t_send, correct S → correct R →
    net.sent S m t_send →
    net.received R S m (max gst t_send + delta_net)
  /-- No forgery: if correct R receives m allegedly from correct S,
      then S actually sent m. -/
  no_forgery : ∀ S R m t, correct S → correct R →
    net.received R S m t → ∃ t_send, t_send ≤ t ∧ net.sent S m t_send
  /-- Receipt persistence: once received, always received. -/
  receipt_persistent : ∀ R S m t t',
    net.received R S m t → t ≤ t' → net.received R S m t'

/-! ## Shared timing helpers -/

/-- Combine finitely many existential witnesses into one time using
    persistence. Induction on k. -/
theorem collect_at_one_time
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

/-- Arithmetic helper: max(gst, ts) + d ≤ t + d when gst ≤ t and ts ≤ t. -/
theorem max_add_le_add {gst ts t d : Nat}
    (h1 : gst ≤ t) (h2 : ts ≤ t) :
    max gst ts + d ≤ t + d :=
  Nat.add_le_add_right (Nat.max_le.mpr ⟨h1, h2⟩) d

/-- Arithmetic: a + d + d = a + 2 * d. -/
theorem add_d_d (a d : Nat) : a + d + d = a + 2 * d := by
  rw [Nat.add_assoc, ← Nat.two_mul]

/-- Arithmetic: 2 * d ≤ 3 * d. -/
theorem two_le_three_mul (d : Nat) : 2 * d ≤ 3 * d :=
  Nat.mul_le_mul_right d (by omega)

end Zug.Concrete
