module

public import Linglib.Logic.Truthmaker.Formula
public import Linglib.Semantics.Mereology.Exemplification

/-!
# Deigan (2020): A plea for inexact truthmaking

A state exactly verifies a sentence when it is wholly relevant to the sentence's truth, and
inexactly when it guarantees the truth and may contain more. The states carry the topology whose
open sets are the sets closed under parts. Fine defines the inexact verifiers from the exact
ones, as the states that contain an exact verifier: they are the closure of the exact verifiers.
Deigan defines the exact verifiers from the inexact ones. For a sentence letter they are the
exemplifiers of its inexact verifiers, their interior points and isolated points in the sense of
`Mereology.Exemplifies`, and its exact falsifiers are the exemplifiers of its inexact falsifiers;
negation, conjunction and disjunction are then Fine's. We define `inexact X`, the closures of the
verifiers and of the falsifiers of a bilateral proposition, and `exemplifiers X`, their
exemplifiers.

In a well-founded space of states the two definitions compose to the identity on inexact
propositions: the inexact verifiers of a proposition are the closure of their exemplifiers. In
the other order they compose to the identity on a proposition whose verifiers and falsifiers are
antichains of states that have proper parts, and every formula over such letters then denotes
under Deigan's definition what it denotes under the exact valuation. A proposition has no
exemplifier exactly when its verifiers have empty interior and no isolated point, as the
proposition that there are infinitely many stars has none, `Kratzer2002.not_exemplifies_infinite`.

Two simpler definitions fail. The minimal inexact verifiers are no definition where the
verifiers are open and every state has a proper part, since nothing is then minimal, though
every verifier exemplifies. And the exemplifiers of the inexact verifiers of an arbitrary formula
are not its exact verifiers: `A ∨ (A ∧ B)` has the inexact verifiers of `A`, so a fusion that
exactly verifies it and not `A` does not exemplify them. With a null state, the letter verified
by the null state alone and the letter verified by every state have the same exemplifiers.

## TODO

The quantified sentences, whose exact verifiers are defined from those of their instances, and
the sentences whose inexact verifiers are argued to contain no exact verifier.

## References

* [deigan-2020]
* [fine-2017]
* [kratzer-2012]
-/

@[expose] public section

namespace Deigan2020

open Mereology Truthmaker Topology
open scoped Bilattice
open Bilattice.Product (mk)

variable {A S : Type*} [TopologicalSpace S]

/-- The inexact verifiers and falsifiers of a proposition, as Fine defines them: the closure of
its exact verifiers and the closure of its exact falsifiers, which in the topology of parts are
the states that contain one. -/
def inexact (X : Set S ⊙ Set S) : Set S ⊙ Set S :=
  X.map closure closure

/-- The exemplifiers of the verifiers and of the falsifiers of a proposition, the exact verifiers
and falsifiers that Deigan defines for a sentence letter from its inexact ones. -/
def exemplifiers (X : Set S ⊙ Set S) : Set S ⊙ Set S :=
  X.map (fun p ↦ {s | Exemplifies p s}) fun p ↦ {s | Exemplifies p s}

@[simp] theorem pro_inexact (X : Set S ⊙ Set S) : (inexact X).pro = closure X.pro := rfl

@[simp] theorem con_inexact (X : Set S ⊙ Set S) : (inexact X).con = closure X.con := rfl

@[simp] theorem pro_exemplifiers (X : Set S ⊙ Set S) :
    (exemplifiers X).pro = {s | Exemplifies X.pro s} := rfl

@[simp] theorem con_exemplifiers (X : Set S ⊙ Set S) :
    (exemplifiers X).con = {s | Exemplifies X.con s} := rfl

section PartialOrder

variable [PartialOrder S] [Topology.IsLowerSet S] {X : Set S ⊙ Set S} {p : Set S}

open Topology.IsLowerSet

/-- Where the verifiers are open and every state has a proper part, as with *Achilles was
moving*, every verifier exemplifies and none is minimal. -/
theorem exemplifies_and_not_minimal [NoMinOrder S] (hp : IsOpen p) {x : S} (hx : x ∈ p) :
    Exemplifies p x ∧ ¬ Minimal (· ∈ p) x :=
  ⟨hp.exemplifies_iff.2 hx, fun h ↦
    let ⟨_, hy⟩ := exists_lt x; h.not_prop_of_lt hy (isOpen_iff_isLowerSet.1 hp hy.le hx)⟩

/-- In a well-founded space of states, the inexact verifiers and falsifiers of a proposition are
those of the exact ones that Deigan defines from them. -/
theorem inexact_exemplifiers_inexact [WellFoundedLT S] (X : Set S ⊙ Set S) :
    inexact (exemplifiers (inexact X)) = inexact X :=
  Bilattice.Product.ext (closure_setOf_exemplifies isClosed_closure)
    (closure_setOf_exemplifies isClosed_closure)

theorem exemplifiers_inexact (hpro : IsAntichain (· ≤ ·) X.pro)
    (hcon : IsAntichain (· ≤ ·) X.con) (hmin : ∀ s ∈ X.pro ∪ X.con, ¬ IsMin s) :
    exemplifiers (inexact X) = X :=
  Bilattice.Product.ext
    (Set.ext fun _ ↦ by
      rw [pro_exemplifiers, pro_inexact, closure_eq_upperClosure]
      exact hpro.exemplifies_upperClosure_iff fun s hs ↦ hmin s (.inl hs))
    (Set.ext fun _ ↦ by
      rw [con_exemplifiers, con_inexact, closure_eq_upperClosure]
      exact hcon.exemplifies_upperClosure_iff fun s hs ↦ hmin s (.inr hs))

-- fn. 22
theorem pro_exemplifiers_inexact_bot [OrderBot S] (F : Set S) :
    (exemplifiers (inexact (mk {⊥} F))).pro = (exemplifiers (inexact (mk Set.univ F))).pro := by
  simp [closure_eq_upperClosure, upperClosure_singleton]

end PartialOrder

section SemilatticeSup

variable [SemilatticeSup S] [Topology.IsLowerSet S] {V : A → Set S ⊙ Set S}
  {P Q : Set S ⊙ Set S} {a b : S}

open Topology.IsLowerSet

/-- Deigan's definition of exact verification from inexact gives every formula the proposition
that the exact valuation gives it, where the verifiers and the falsifiers of each letter are
antichains of states that have proper parts. -/
theorem denote_exemplifiers_inexact (hpro : ∀ a, IsAntichain (· ≤ ·) (V a).pro)
    (hcon : ∀ a, IsAntichain (· ≤ ·) (V a).con)
    (hmin : ∀ a, ∀ s ∈ (V a).pro ∪ (V a).con, ¬ IsMin s) (φ : Formula A) :
    φ.denote (fun a ↦ exemplifiers (inexact (V a))) = φ.denote V :=
  congrArg φ.denote (funext fun a ↦ exemplifiers_inexact (hpro a) (hcon a) (hmin a))

-- Table 2
theorem closure_pro_disj_conj (P Q : Set S ⊙ Set S) :
    closure (disj P (conj P Q)).pro = closure P.pro := by
  rw [closure_eq_upperClosure, closure_eq_upperClosure, pro_disj, pro_conj, upperClosure_union,
    upperClosure_sups, inf_sup_self]

/-- A fusion `a ⊔ b` of the verifier of `A` with a verifier of `B` exactly verifies
`A ∨ (A ∧ B)` and not `A`, and does not exemplify the inexact verifiers of `A ∨ (A ∧ B)`, where
neither state is part of the other. -/
theorem sup_mem_pro_disj_conj_and_not_exemplifies (ha : P.pro = {a}) (hb : b ∈ Q.pro)
    (hab : ¬ a ≤ b) (hba : ¬ b ≤ a) :
    a ⊔ b ∈ (disj P (conj P Q)).pro ∧ a ⊔ b ∉ P.pro ∧
      ¬ Exemplifies (closure (disj P (conj P Q)).pro) (a ⊔ b) := by
  refine ⟨.inr ⟨a, ha ▸ rfl, b, hb, rfl⟩, fun h ↦ hba ?_, ?_⟩
  · rw [ha, Set.mem_singleton_iff] at h
    exact sup_eq_left.1 h
  · rw [closure_pro_disj_conj, ha, IsLowerSet.closure_singleton]
    exact not_exemplifies_sup Set.self_mem_Ici hab hba

end SemilatticeSup

end Deigan2020
