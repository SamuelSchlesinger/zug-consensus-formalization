/-
  Zug.Concrete.Quorum: Quorum reasoning for concrete subprotocol proofs.

  Defines `MoreThan k n P` ("more than k nodes in [0,n) satisfy P")
  and the `QuorumAxioms` structure capturing quorum intersection and
  counting properties that follow from the BFT fault model.
-/

import Zug.Concrete.Network

namespace Zug.Concrete

/-- More than k nodes in [0, n) satisfy predicate P.
    Witnessed by an injective function from Fin (k+1) into Fin n
    whose image satisfies P. -/
def MoreThan (k n : Nat) (P : NodeId → Prop) : Prop :=
  ∃ (enum : Fin (k + 1) → Fin n), Function.Injective enum ∧
    ∀ i, P (enum i)

/-- MoreThan is monotone in the predicate. -/
theorem MoreThan.mono {k n : Nat} {P Q : NodeId → Prop}
    (h : MoreThan k n P) (hpq : ∀ N, P N → Q N) :
    MoreThan k n Q := by
  obtain ⟨enum, hinj, hsat⟩ := h
  exact ⟨enum, hinj, fun i => hpq _ (hsat i)⟩

/-- MoreThan can be weakened: if more than k satisfy P,
    then more than k' ≤ k satisfy P. -/
theorem MoreThan.weaken {k k' n : Nat} {P : NodeId → Prop}
    (h : MoreThan k n P) (hle : k' ≤ k) :
    MoreThan k' n P := by
  obtain ⟨enum, hinj, hsat⟩ := h
  refine ⟨fun i => enum ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.succ_le_succ hle)⟩, ?_, ?_⟩
  · intro a b hab
    have := hinj hab
    exact Fin.ext (Fin.mk.inj this)
  · intro i; exact hsat _

/-- Extract a single witness from MoreThan. -/
theorem MoreThan.witness {k n : Nat} {P : NodeId → Prop}
    (h : MoreThan k n P) :
    ∃ N, N < n ∧ P N := by
  obtain ⟨enum, _, hsat⟩ := h
  exact ⟨(enum ⟨0, Nat.zero_lt_succ k⟩).val, (enum ⟨0, Nat.zero_lt_succ k⟩).isLt, hsat _⟩

/-- Quorum properties for concrete subprotocol proofs.

    These capture the counting arguments that underlie BFT quorum
    intersection. All thresholds use `q = (n + f) / 2`, the quorum
    threshold from `NetworkConfig`. Two sets of size > q overlap in
    > f elements (by pigeonhole), guaranteeing a correct member.

    These properties are derived from `FaultModel` in this file. -/
structure QuorumAxioms (cfg : NetworkConfig) (correct : Correctness) : Prop where
  /-- All correct nodes have IDs in [0, n). -/
  node_bound : ∀ N, correct N → N < cfg.n
  /-- Two sets with > q members each share a correct node.
      Proof sketch: |A| + |B| > 2q ≥ n + f > n, so |A ∩ B| > f,
      and at most f are faulty, leaving ≥ 1 correct. -/
  quorum_intersection :
    MoreThan cfg.q cfg.n A →
    MoreThan cfg.q cfg.n B →
    ∃ N, correct N ∧ A N ∧ B N
  /-- A set with > q members contains > f correct nodes.
      Proof sketch: |P| ≥ q + 1 > f + 1 faulty nodes,
      so > f are correct. -/
  quorum_correct_subset :
    MoreThan cfg.q cfg.n P →
    MoreThan cfg.f cfg.n (fun N => correct N ∧ P N)
  /-- If all correct nodes (with ID < n) satisfy P, then P has
      > q members (since n - f > q when n > 3f). -/
  all_correct_quorum :
    (∀ N, correct N → N < cfg.n → P N) →
    MoreThan cfg.q cfg.n P

end Zug.Concrete
