/-
  Zug.Network: Network model for the Zug Atomic Broadcast protocol.

  Models nodes, correct/faulty distinction, quorum arithmetic,
  and partial synchrony assumptions.
-/

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

/-- Abstract time type. We use Nat for discrete time steps. -/
abbrev Time := Nat

/-- Partial synchrony parameters. -/
structure PartialSynchrony where
  /-- Global Stabilization Time. -/
  gst : Time
  /-- Known upper bound on message delay after GST. -/
  delta : Time
  /-- Delta is positive. -/
  delta_pos : delta > 0

end Zug
