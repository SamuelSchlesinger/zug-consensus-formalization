/-
  Zug.Network: Network model for the Zug Atomic Broadcast protocol.

  Models nodes, correct/faulty distinction, quorum arithmetic,
  and partial synchrony assumptions.
-/

namespace Zug

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
