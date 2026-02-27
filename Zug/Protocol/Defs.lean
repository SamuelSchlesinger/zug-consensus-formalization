/-
  Zug.Protocol.Defs: Core definitions for the Zug AB protocol.

  Defines committed, skippable, fertile, accepted, finalized, and
  the ancestor relation — all indexed by (Node, Time) to capture
  the subjective view of each node at each point in time.
-/

import Zug.Subprotocols

namespace Zug

variable {V : Type}

/-! ## Round status predicates

  These are indexed by a node N and time t, capturing the subjective
  view: what node N has observed from the subprotocols by time t.
-/

/-- Round r is (N, t)-committed if WBA[r] has output `true` (= 1)
    as observed by node N at time t. -/
def Committed (views : SubprotocolViews V) (N : NodeId) (t : Time)
    (r : Nat) : Prop :=
  (views.wba r).output_at N t = some true

/-- Round r is (N, t)-skippable if WBA[r] has output `false` (= 0)
    as observed by node N at time t. -/
def Skippable (views : SubprotocolViews V) (N : NodeId) (t : Time)
    (r : Nat) : Prop :=
  (views.wba r).output_at N t = some false

/-- The RB output observed by node N at time t for round r. -/
def RBOutput (views : SubprotocolViews V) (N : NodeId) (t : Time)
    (r : Nat) : Option (Proposal V) :=
  (views.rb r).output_at N t

/-! ## Accepted

  We combine the paper's `fertile` and `accepted` into a single
  inductive `AcceptedAt`, avoiding mutual inductives (which have
  kernel limitations in Lean 4 with existentials).

  `AcceptedAt views N t r s` means round r has an accepted value
  with parent s, as observed by node N at time t.

  - If s = none (⊥): all rounds < r are skippable, and RB[r]
    output has parent none.
  - If s = some s': s' < r, all rounds strictly between s' and r
    are skippable, s' itself has an accepted value (witnessed by
    AcceptedAt at s'), and RB[r] output has parent s'.
-/
inductive AcceptedAt (views : SubprotocolViews V) (N : NodeId) (t : Time) :
    Nat → Option Nat → Prop where
  | mk_bot (r : Nat) (v : V) :
      (∀ u, u < r → Skippable views N t u) →
      RBOutput views N t r = some ⟨v, none⟩ →
      AcceptedAt views N t r none
  | mk_parent (r s : Nat) (v : V) (p : Option Nat) :
      s < r →
      (∀ u, s < u → u < r → Skippable views N t u) →
      AcceptedAt views N t s p →
      RBOutput views N t r = some ⟨v, some s⟩ →
      AcceptedAt views N t r (some s)

/-- Round r has an accepted value (with some parent) at (N, t). -/
def HasAccepted (views : SubprotocolViews V) (N : NodeId) (t : Time)
    (r : Nat) : Prop :=
  ∃ s, AcceptedAt views N t r s

/-- `Fertile views N t r s` means parent s is fertile in round r.
    This is derived from AcceptedAt for convenience. -/
def Fertile (views : SubprotocolViews V) (N : NodeId) (t : Time)
    (r : Nat) (s : Option Nat) : Prop :=
  match s with
  | none => ∀ u, u < r → Skippable views N t u
  | some s => s < r ∧ (∀ u, s < u → u < r → Skippable views N t u) ∧
              HasAccepted views N t s

/-! ## Ancestor relation -/

/-- The ancestor relation on rounds, derived from the proposal tree.

    Round s is an ancestor of round r if there is a chain of parent
    pointers from r back to s, where each link is witnessed by an
    RB output (at node N, time t). -/
inductive Ancestor (views : SubprotocolViews V) (N : NodeId) (t : Time) :
    Nat → Nat → Prop where
  /-- s is a direct parent of r if RB[r] output has parent s. -/
  | direct (s r : Nat) (v : V) :
      RBOutput views N t r = some ⟨v, some s⟩ →
      Ancestor views N t s r
  /-- Transitivity through the parent chain. -/
  | trans (s p r : Nat) :
      Ancestor views N t s p →
      Ancestor views N t p r →
      Ancestor views N t s r

/-- s is an ancestor of r, or s = r. -/
def AncestorOrEq (views : SubprotocolViews V) (N : NodeId) (t : Time)
    (s r : Nat) : Prop :=
  s = r ∨ Ancestor views N t s r

/-- Round r is (N, t)-finalized if it is equal to or an ancestor of
    some committed round that has an accepted value. -/
def Finalized (views : SubprotocolViews V) (N : NodeId) (t : Time)
    (r : Nat) : Prop :=
  ∃ r', AncestorOrEq views N t r r' ∧
        HasAccepted views N t r' ∧
        Committed views N t r'

end Zug
