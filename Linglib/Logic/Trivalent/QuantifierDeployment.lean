/-
Copyright (c) 2026 Patrick Elliott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Elliott
-/
module

public import Linglib.Logic.Trivalent.Deployment
public import Linglib.Logic.Trivalent.Supervaluation

/-!
# Peters-Kleene deployment for quantifiers

A generalised quantifier is a function from predicate extensions to truth values, so Peters-Kleene
deployment applies to it once a trivalent predicate has repairs ([george-2014] §4.1). The repairs of
a predicate `A : U → SignType` are the classical predicates that agree with `A` wherever `A` is
classical and are free wherever `A` is undefined (Definition 19). A quantifier deployed on a
trivalent predicate is then the supervaluation over its repairs, which George relates to the
supervaluation quantifiers of [van-eijck-1996]. Deploying the universal and existential
quantifiers gives the Strong Kleene quantifiers `forallStrong` and `existsStrong`, so
*everybody has stopped smoking* presupposes only that somebody smokes or everybody has smoked
(`forallStrong_ne_zero_iff`, George's (11)), not that everybody has smoked.

A determiner takes its restrictor first. Either two repairs of the restrictor make different
quantifiers of the determiner, and the deployment is undefined, or they all make the same
quantifier, and the deployment is that quantifier deployed on the nuclear scope. In the nuclear
scope, then, a deployed determiner is a supervaluation over repairs.

## Main definitions

* `Trivalent.repairs`: the repairs `REP(A)` of a trivalent predicate (Definition 19).
* `Trivalent.lowerRepair`, `Trivalent.upperRepair`: the least and greatest repairs.
* `Trivalent.deployQuantifier`: the deployment `Q[A]` of a generalised quantifier.
* `Trivalent.deployDeterminer`: the deployment `D[A, B]` of a determiner.

## Main results

* `Trivalent.deployWith_unary`: deploying a unary function is the supervaluation over the repairs
  of its argument.
* `Trivalent.deployQuantifier_eq_supervaluationOn`, `Trivalent.deployQuantifier_ofProp`: a
  deployed quantifier is the supervaluation over the repairs of its argument, and the quantifier
  itself on a classical predicate.
* `Trivalent.deployQuantifier_of_monotone`, `Trivalent.deployQuantifier_of_antitone`: a monotone
  or antitone quantifier is settled by the lower and upper repairs.
* `Trivalent.deployQuantifier_eq_forallStrong`, `Trivalent.deployQuantifier_eq_existsStrong`:
  deploying `∀` and `∃` (Definitions 16 and 17) gives the Strong Kleene quantifiers.
* `Trivalent.deployDeterminer_of_forall`, `Trivalent.deployDeterminer_eq_zero_of_ne`,
  `Trivalent.deployDeterminer_ofProp_left`: a deployed determiner is undefined or a deployed
  quantifier on its nuclear scope, according to its restrictor.

## References

* [george-2014]
* [van-eijck-1996]
-/

@[expose] public section

namespace Trivalent

open SignType

/-! ### Unary deployment as supervaluation -/

section Unary

variable {α β : Type*} {rep : β → Set α}

/-- Deploying a unary function by a nonempty repair set is the supervaluation over the repairs. -/
theorem deployWith_unary {f : α → Bool} {x : β} (hx : (rep x).Nonempty) :
    deployWith rep (fun y ↦ f (y 0)) ![x] = supervaluationOn (rep x) (f · = true) := by
  by_cases h : ∃ a ∈ rep x, ∃ b ∈ rep x, f a ≠ f b
  · obtain ⟨a, ha, b, hb, hab⟩ := h
    rw [deployWith_succ_of_ne (f := fun y : Fin 1 → α ↦ f (y 0)) (x := ![x]) ha hb
      fun e ↦ hab (congrFun e ![]), eq_comm, supervaluationOn_eq_zero_iff]
    cases hfa : f a <;> cases hfb : f b <;> simp only [hfa, hfb, ne_eq, not_true_eq_false] at hab
    · exact ⟨⟨b, hb, hfb⟩, a, ha, by simp [hfa]⟩
    · exact ⟨⟨a, ha, hfa⟩, b, hb, by simp [hfb]⟩
  · push Not at h
    obtain ⟨a, ha⟩ := hx
    rw [deployWith_succ_of_forall (f := fun y : Fin 1 → α ↦ f (y 0)) (x := ![x])
      (g := fun _ ↦ f a) ⟨a, ha⟩ fun c hc ↦ funext fun _ ↦ h c hc a ha, deployWith_zero]
    cases hfa : f a
    · simp only [Bool.false_eq_true, ofProp_false]
      rw [eq_comm, supervaluationOn_eq_neg_one_iff]
      exact ⟨⟨a, ha⟩, fun c hc ↦ by simp [h c hc a ha, hfa]⟩
    · simp only [ofProp_true]
      rw [eq_comm, supervaluationOn_eq_one_iff]
      exact fun c hc ↦ (h c hc a ha).trans hfa

end Unary

variable {U : Type*}

/-! ### Repairs of a predicate -/

/-- The repairs of a trivalent predicate are the classical predicates that agree with it wherever
it is classical (Definition 19). -/
def repairs (A : U → SignType) : Set (U → Bool) :=
  Set.univ.pi fun u ↦ ↑(toFinset (A u))

@[simp] theorem mem_repairs {A : U → SignType} {g : U → Bool} :
    g ∈ repairs A ↔ ∀ u, g u ∈ toFinset (A u) := by
  simp [repairs]

/-- The lower repair of a predicate sends every gap to `false`, its K3 reading. -/
def lowerRepair (A : U → SignType) : U → Bool := fun u ↦ decide (A u = 1)

/-- The upper repair of a predicate sends every gap to `true`, its LP reading. -/
def upperRepair (A : U → SignType) : U → Bool := fun u ↦ decide (A u ≠ -1)

theorem lowerRepair_mem_repairs (A : U → SignType) : lowerRepair A ∈ repairs A := by
  simp only [mem_repairs, lowerRepair]; intro u; cases A u <;> decide

theorem upperRepair_mem_repairs (A : U → SignType) : upperRepair A ∈ repairs A := by
  simp only [mem_repairs, upperRepair]; intro u; cases A u <;> decide

theorem repairs_nonempty (A : U → SignType) : (repairs A).Nonempty :=
  ⟨_, lowerRepair_mem_repairs A⟩

theorem lowerRepair_le_of_mem_repairs {A : U → SignType} {g : U → Bool} (hg : g ∈ repairs A) :
    lowerRepair A ≤ g := fun u ↦ by
  have := mem_repairs.1 hg u
  simp only [lowerRepair]
  generalize A u = a, g u = b at this ⊢
  cases a <;> cases b <;> simp_all

theorem le_upperRepair_of_mem_repairs {A : U → SignType} {g : U → Bool} (hg : g ∈ repairs A) :
    g ≤ upperRepair A := fun u ↦ by
  have := mem_repairs.1 hg u
  simp only [upperRepair]
  generalize A u = a, g u = b at this ⊢
  cases a <;> cases b <;> simp_all

/-- A classical predicate is its own only repair. -/
@[simp] theorem repairs_ofProp (g : U → Bool) : repairs (fun u ↦ ofProp (g u)) = {g} := by
  ext h
  simp only [mem_repairs, Set.mem_singleton_iff, funext_iff]
  exact forall_congr' fun u ↦ by cases g u <;> simp [ofProp]

/-! ### Deployed quantifiers -/

/-- The Peters-Kleene deployment `Q[A]` of a generalised quantifier on a trivalent predicate. -/
noncomputable def deployQuantifier (Q : (U → Bool) → Bool) (A : U → SignType) : SignType :=
  deployWith repairs (fun v ↦ Q (v 0)) ![A]

/-- A deployed quantifier is the supervaluation over the repairs of its argument. -/
theorem deployQuantifier_eq_supervaluationOn (Q : (U → Bool) → Bool) (A : U → SignType) :
    deployQuantifier Q A = supervaluationOn (repairs A) (Q · = true) :=
  deployWith_unary (repairs_nonempty A)

/-- On a classical predicate, a deployed quantifier is the quantifier. -/
@[simp] theorem deployQuantifier_ofProp (Q : (U → Bool) → Bool) (g : U → Bool) :
    deployQuantifier Q (fun u ↦ ofProp (g u)) = ofProp (Q g) := by
  rw [deployQuantifier_eq_supervaluationOn, repairs_ofProp]
  refine eq_of_eq_one_iff_of_eq_neg_one_iff ?_ ?_ <;>
    simp [supervaluationOn_eq_one_iff, supervaluationOn_eq_neg_one_iff]

/-- A monotone quantifier deployed on a predicate is settled by its lower and upper repairs. -/
theorem deployQuantifier_of_monotone {Q : (U → Bool) → Bool} (hQ : Monotone Q)
    (A : U → SignType) :
    deployQuantifier Q A = supervaluationOn {lowerRepair A, upperRepair A} (Q · = true) := by
  rw [deployQuantifier_eq_supervaluationOn]
  refine supervaluationOn_eq_of_between (lowerRepair_mem_repairs A) (upperRepair_mem_repairs A)
    fun g hg ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact le_antisymm (Bool.le_true _) (h ▸ hQ (lowerRepair_le_of_mem_repairs hg))
  · exact le_antisymm (Bool.le_true _) (h ▸ hQ (le_upperRepair_of_mem_repairs hg))

/-- An antitone quantifier deployed on a predicate is settled by its upper and lower repairs. -/
theorem deployQuantifier_of_antitone {Q : (U → Bool) → Bool} (hQ : Antitone Q)
    (A : U → SignType) :
    deployQuantifier Q A = supervaluationOn {upperRepair A, lowerRepair A} (Q · = true) := by
  rw [deployQuantifier_eq_supervaluationOn]
  refine supervaluationOn_eq_of_between (upperRepair_mem_repairs A) (lowerRepair_mem_repairs A)
    fun g hg ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact le_antisymm (Bool.le_true _) (h ▸ hQ (le_upperRepair_of_mem_repairs hg))
  · exact le_antisymm (Bool.le_true _) (h ▸ hQ (lowerRepair_le_of_mem_repairs hg))

private theorem neg_one_ne_one : (-1 : SignType) ≠ 1 := by decide

/-- Deploying the universal quantifier (Definition 16) gives the Strong Kleene universal. -/
theorem deployQuantifier_eq_forallStrong {Q : (U → Bool) → Bool}
    (hQ : ∀ g, Q g = true ↔ ∀ u, g u = true) : deployQuantifier Q = forallStrong := by
  funext A
  rw [deployQuantifier_of_monotone fun g h hgh ↦ Bool.le_iff_imp.2 fun H ↦
    (hQ h).2 fun u ↦ Bool.le_iff_imp.1 (hgh u) ((hQ g).1 H u)]
  refine eq_of_eq_one_iff_of_eq_neg_one_iff ?_ ?_
  · simp [supervaluationOn_eq_one_iff, hQ, lowerRepair, upperRepair]; grind [neg_one_ne_one]
  · simp [supervaluationOn_eq_neg_one_iff, hQ, lowerRepair, upperRepair]; grind [neg_one_ne_one]

/-- Deploying the existential quantifier (Definition 17) gives the Strong Kleene existential. -/
theorem deployQuantifier_eq_existsStrong {Q : (U → Bool) → Bool}
    (hQ : ∀ g, Q g = true ↔ ∃ u, g u = true) : deployQuantifier Q = existsStrong := by
  funext A
  rw [deployQuantifier_of_monotone fun g h hgh ↦ Bool.le_iff_imp.2 fun H ↦
    (hQ h).2 <| let ⟨u, hu⟩ := (hQ g).1 H; ⟨u, Bool.le_iff_imp.1 (hgh u) hu⟩]
  refine eq_of_eq_one_iff_of_eq_neg_one_iff ?_ ?_
  · simp [supervaluationOn_eq_one_iff, hQ, lowerRepair, upperRepair]; grind [neg_one_ne_one]
  · simp [supervaluationOn_eq_neg_one_iff, hQ, lowerRepair, upperRepair]; grind [neg_one_ne_one]

/-! ### Deployed determiners -/

/-- The Peters-Kleene deployment `D[A, B]` of a determiner on a trivalent restrictor `A` and
nuclear scope `B`, the restrictor first. -/
noncomputable def deployDeterminer (D : (U → Bool) → (U → Bool) → Bool)
    (A B : U → SignType) : SignType :=
  deployWith repairs (fun v ↦ D (v 0) (v 1)) ![A, B]

/-- If every repair of the restrictor makes the same quantifier of the determiner, the deployed
determiner is that quantifier deployed on the nuclear scope. -/
theorem deployDeterminer_of_forall {D : (U → Bool) → (U → Bool) → Bool} {A B : U → SignType}
    {Q : (U → Bool) → Bool} (h : ∀ g ∈ repairs A, D g = Q) :
    deployDeterminer D A B = deployQuantifier Q B :=
  deployWith_succ_of_forall (repairs_nonempty A) fun g hg ↦ funext fun v ↦ by
    simp [h g hg]

/-- Two repairs of the restrictor that the determiner tells apart make it undefined. -/
theorem deployDeterminer_eq_zero_of_ne {D : (U → Bool) → (U → Bool) → Bool}
    {A B : U → SignType} {g h : U → Bool} (hg : g ∈ repairs A) (hh : h ∈ repairs A)
    (hgh : D g ≠ D h) : deployDeterminer D A B = 0 :=
  deployWith_succ_of_ne hg hh fun e ↦ hgh (funext fun b ↦ congrFun e ![b])

/-- With a classical restrictor, a deployed determiner is the deployed quantifier it makes of the
restrictor. -/
theorem deployDeterminer_ofProp_left (D : (U → Bool) → (U → Bool) → Bool) (g : U → Bool)
    (B : U → SignType) :
    deployDeterminer D (fun u ↦ ofProp (g u)) B = deployQuantifier (D g) B :=
  deployDeterminer_of_forall fun h hh ↦ by rw [repairs_ofProp] at hh; rw [hh]

end Trivalent
