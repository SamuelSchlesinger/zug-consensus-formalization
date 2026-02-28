/-
  Zug.Concrete.Network: Point-to-point network model shared by
  concrete RB and WBA implementations.

  Declarative Prop-valued predicates matching the existing codebase style.
  `sent S m t` means node S broadcast message m at time t.
  `received R S m t` means node R has received message m (allegedly from S)
  by time t.
-/

import Zug.Subprotocols

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

end Zug.Concrete
