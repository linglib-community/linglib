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
a predicate `A : U → Trivalent` are the classical predicates that agree with `A` wherever `A` is
classical and are free wherever `A` is undefined (Definition 19). A quantifier deployed on a
trivalent predicate is then the supervaluation over its repairs, which George relates to the
supervaluation quantifiers of [van-eijck-1996]. Deploying the universal and existential
quantifiers gives the Strong Kleene quantifiers `forallStrong` and `existsStrong`, so
*everybody has stopped smoking* presupposes only that somebody smokes or everybody has smoked
(`forallStrong_ne_undefined_iff`, George's (11)), not that everybody has smoked.

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
* `Trivalent.forall_repairs_imp_iff`: a property of the repairs forces definedness on a domain
  exactly when it never holds of both a set and the set with one more element of the domain.
* `Trivalent.deployQuantifier_eq_supervaluationOn`, `Trivalent.deployQuantifier_ofProp`: a
  deployed quantifier is the supervaluation over the repairs of its argument, and the quantifier
  itself on a classical predicate.
* `Trivalent.deployQuantifier_of_monotone`, `Trivalent.deployQuantifier_of_antitone`: a monotone
  or antitone quantifier is settled by the lower and upper repairs.
* `Trivalent.deployQuantifier_eq_forallStrong`, `Trivalent.deployQuantifier_eq_existsStrong`:
  deploying `∀` and `∃` (Definitions 16 and 17) gives the Strong Kleene quantifiers.
* `Trivalent.deployDeterminer_of_forall`, `Trivalent.deployDeterminer_eq_undefined_of_ne`,
  `Trivalent.deployDeterminer_ofProp_left`: a deployed determiner is undefined or a deployed
  quantifier on its nuclear scope, according to its restrictor.

## References

* [george-2014]
* [van-eijck-1996]
-/

@[expose] public section

namespace Trivalent

open Trivalent

/-! ### Unary deployment as supervaluation -/

section Unary

variable {α β : Type*} {rep : β → Set α}

/-- Deploying a unary function by a nonempty repair set is the supervaluation over the repairs. -/
theorem deployWith_unary {f : α → Bool} {x : β} (hx : (rep x).Nonempty) :
    deployWith rep (fun y ↦ f (y 0)) ![x] = supervaluationOn (rep x) (f · = Bool.true) := by
  by_cases h : ∃ a ∈ rep x, ∃ b ∈ rep x, f a ≠ f b
  · obtain ⟨a, ha, b, hb, hab⟩ := h
    rw [deployWith_succ_of_ne (f := fun y : Fin 1 → α ↦ f (y 0)) (x := ![x]) ha hb
      fun e ↦ hab (congrFun e ![]), eq_comm, supervaluationOn_eq_undefined_iff]
    cases hfa : f a <;> cases hfb : f b <;> simp only [hfa, hfb, ne_eq, not_true_eq_false] at hab
    · exact ⟨⟨b, hb, hfb⟩, a, ha, by simp [hfa]⟩
    · exact ⟨⟨a, ha, hfa⟩, b, hb, by simp [hfb]⟩
  · push Not at h
    obtain ⟨a, ha⟩ := hx
    rw [deployWith_succ_of_forall (f := fun y : Fin 1 → α ↦ f (y 0)) (x := ![x])
      (g := fun _ ↦ f a) ⟨a, ha⟩ fun c hc ↦ funext fun _ ↦ h c hc a ha, deployWith_zero]
    cases hfa : f a
    · simp only [Bool.false_eq_true, ofProp_false]
      rw [eq_comm, supervaluationOn_eq_false_iff]
      exact ⟨⟨a, ha⟩, fun c hc ↦ by simp [h c hc a ha, hfa]⟩
    · simp only [ofProp_true]
      rw [eq_comm, supervaluationOn_eq_true_iff]
      exact fun c hc ↦ (h c hc a ha).trans hfa

end Unary

variable {U : Type*}

/-! ### Repairs of a predicate -/

/-- The repairs of a trivalent predicate are the classical predicates that agree with it wherever
it is classical (Definition 19). -/
def repairs (A : U → Trivalent) : Set (U → Bool) :=
  Set.univ.pi fun u ↦ ↑(toFinset (A u))

@[simp] theorem mem_repairs {A : U → Trivalent} {g : U → Bool} :
    g ∈ repairs A ↔ ∀ u, g u ∈ toFinset (A u) := by
  simp [repairs]

/-- The lower repair of a predicate sends every gap to `false`, its K3 reading. -/
def lowerRepair (A : U → Trivalent) : U → Bool := fun u ↦ decide (A u = .true)

/-- The upper repair of a predicate sends every gap to `true`, its LP reading. -/
def upperRepair (A : U → Trivalent) : U → Bool := fun u ↦ decide (A u ≠ .false)

theorem lowerRepair_mem_repairs (A : U → Trivalent) : lowerRepair A ∈ repairs A := by
  simp only [mem_repairs, lowerRepair]; intro u; cases A u <;> decide

theorem upperRepair_mem_repairs (A : U → Trivalent) : upperRepair A ∈ repairs A := by
  simp only [mem_repairs, upperRepair]; intro u; cases A u <;> decide

theorem repairs_nonempty (A : U → Trivalent) : (repairs A).Nonempty :=
  ⟨_, lowerRepair_mem_repairs A⟩

theorem lowerRepair_le_of_mem_repairs {A : U → Trivalent} {g : U → Bool} (hg : g ∈ repairs A) :
    lowerRepair A ≤ g := fun u ↦ by
  have := mem_repairs.1 hg u
  simp only [lowerRepair]
  generalize A u = a, g u = b at this ⊢
  cases a <;> cases b <;> simp_all

theorem le_upperRepair_of_mem_repairs {A : U → Trivalent} {g : U → Bool} (hg : g ∈ repairs A) :
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

/-! ### Single steps

A predicate undefined at a single point has two repairs, differing at that point, and any
predicate undefined at a point has repairs true on its positive extension and on that extension
with the point added. So whether a property of the repairs forces a predicate to be defined turns
on single steps. -/

section Step

open Classical in
/-- The predicate true on `B`, undefined at `a` and false elsewhere. -/
private noncomputable def gapAt (B : Set U) (a : U) : U → Trivalent :=
  fun x ↦ if x ∈ B then .true else if x = a then .undefined else .false

/-- When `a ∉ B`, the repairs of `gapAt B a` are true on `B` or on `insert a B`. -/
private theorem setOf_eq_of_mem_repairs_gapAt {B : Set U} {a : U} (ha : a ∉ B) {g : U → Bool}
    (hg : g ∈ repairs (gapAt B a)) : {x | g x} = B ∨ {x | g x} = insert a B := by
  classical
  rw [mem_repairs] at hg
  have hB : ∀ x, x ≠ a → (g x ↔ x ∈ B) := fun x hx ↦ by
    have := hg x
    by_cases hxB : x ∈ B <;> simp_all [gapAt]
  cases hga : g a
  · refine .inl (Set.ext fun x ↦ ?_)
    by_cases hx : x = a
    · subst hx; simp [hga, ha]
    · exact hB x hx
  · refine .inr (Set.ext fun x ↦ ?_)
    by_cases hx : x = a
    · subst hx; simp [hga]
    · simp [hx, hB x hx]

/-- Over a domain `R`, a property `P` of sets that holds of the repairs of a trivalent predicate
only when the predicate is defined throughout `R` is one that never holds of both a set and the
set with one more element of `R`. -/
theorem forall_repairs_imp_iff (P : Set U → Prop) (R : Set U) :
    (∀ A : U → Trivalent, (∀ g ∈ repairs A, P {a | g a}) → ∀ a ∈ R, A a ≠ .undefined) ↔
      ∀ B, ∀ a ∈ R, a ∉ B → ¬ (P B ∧ P (insert a B)) := by
  classical
  constructor
  · rintro h B a haR haB ⟨hB, hB'⟩
    refine h (gapAt B a) (fun g hg ↦ ?_) a haR (by simp [gapAt, haB])
    rcases setOf_eq_of_mem_repairs_gapAt haB hg with e | e <;> rw [e] <;> assumption
  · intro h A hA a haR hAa
    have hlow := lowerRepair_mem_repairs A
    have hstep : (fun x ↦ decide (A x = .true ∨ x = a)) ∈ repairs A := by
      rw [mem_repairs]
      intro x
      by_cases hx : x = a
      · subst hx; simp [hAa]
      · have := mem_repairs.1 hlow x
        simpa [lowerRepair, hx] using this
    refine h {x | A x = .true} a haR (by simp [hAa]) ⟨?_, ?_⟩
    · simpa [lowerRepair] using hA _ hlow
    · simpa [Set.insert_def, or_comm] using hA _ hstep

end Step

/-! ### Deployed quantifiers -/

/-- The Peters-Kleene deployment `Q[A]` of a generalised quantifier on a trivalent predicate. -/
noncomputable def deployQuantifier (Q : (U → Bool) → Bool) (A : U → Trivalent) : Trivalent :=
  deployWith repairs (fun v ↦ Q (v 0)) ![A]

/-- A deployed quantifier is the supervaluation over the repairs of its argument. -/
theorem deployQuantifier_eq_supervaluationOn (Q : (U → Bool) → Bool) (A : U → Trivalent) :
    deployQuantifier Q A = supervaluationOn (repairs A) (Q · = Bool.true) :=
  deployWith_unary (repairs_nonempty A)

/-- On a classical predicate, a deployed quantifier is the quantifier. -/
@[simp] theorem deployQuantifier_ofProp (Q : (U → Bool) → Bool) (g : U → Bool) :
    deployQuantifier Q (fun u ↦ ofProp (g u)) = ofProp (Q g) := by
  rw [deployQuantifier_eq_supervaluationOn, repairs_ofProp]
  refine eq_of_eq_true_iff_of_eq_false_iff ?_ ?_ <;>
    simp [supervaluationOn_eq_true_iff, supervaluationOn_eq_false_iff]

/-- A monotone quantifier deployed on a predicate is settled by its lower and upper repairs. -/
theorem deployQuantifier_of_monotone {Q : (U → Bool) → Bool} (hQ : Monotone Q)
    (A : U → Trivalent) :
    deployQuantifier Q A = supervaluationOn {lowerRepair A, upperRepair A} (Q · = Bool.true) := by
  rw [deployQuantifier_eq_supervaluationOn]
  refine supervaluationOn_eq_of_between (lowerRepair_mem_repairs A) (upperRepair_mem_repairs A)
    fun g hg ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact le_antisymm (Bool.le_true _) (h ▸ hQ (lowerRepair_le_of_mem_repairs hg))
  · exact le_antisymm (Bool.le_true _) (h ▸ hQ (le_upperRepair_of_mem_repairs hg))

/-- An antitone quantifier deployed on a predicate is settled by its upper and lower repairs. -/
theorem deployQuantifier_of_antitone {Q : (U → Bool) → Bool} (hQ : Antitone Q)
    (A : U → Trivalent) :
    deployQuantifier Q A = supervaluationOn {upperRepair A, lowerRepair A} (Q · = Bool.true) := by
  rw [deployQuantifier_eq_supervaluationOn]
  refine supervaluationOn_eq_of_between (upperRepair_mem_repairs A) (lowerRepair_mem_repairs A)
    fun g hg ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact le_antisymm (Bool.le_true _) (h ▸ hQ (le_upperRepair_of_mem_repairs hg))
  · exact le_antisymm (Bool.le_true _) (h ▸ hQ (lowerRepair_le_of_mem_repairs hg))

/-- Deploying the universal quantifier (Definition 16) gives the Strong Kleene universal. -/
theorem deployQuantifier_eq_forallStrong {Q : (U → Bool) → Bool}
    (hQ : ∀ g, Q g = Bool.true ↔ ∀ u, g u = Bool.true) : deployQuantifier Q = forallStrong := by
  funext A
  rw [deployQuantifier_of_monotone fun g h hgh ↦ Bool.le_iff_imp.2 fun H ↦
    (hQ h).2 fun u ↦ Bool.le_iff_imp.1 (hgh u) ((hQ g).1 H u)]
  refine eq_of_eq_true_iff_of_eq_false_iff ?_ ?_
  · simp [supervaluationOn_eq_true_iff, hQ, lowerRepair, upperRepair]; grind
  · simp [supervaluationOn_eq_false_iff, hQ, lowerRepair, upperRepair]; grind

/-- Deploying the existential quantifier (Definition 17) gives the Strong Kleene existential. -/
theorem deployQuantifier_eq_existsStrong {Q : (U → Bool) → Bool}
    (hQ : ∀ g, Q g = Bool.true ↔ ∃ u, g u = Bool.true) : deployQuantifier Q = existsStrong := by
  funext A
  rw [deployQuantifier_of_monotone fun g h hgh ↦ Bool.le_iff_imp.2 fun H ↦
    (hQ h).2 <| let ⟨u, hu⟩ := (hQ g).1 H; ⟨u, Bool.le_iff_imp.1 (hgh u) hu⟩]
  refine eq_of_eq_true_iff_of_eq_false_iff ?_ ?_
  · simp [supervaluationOn_eq_true_iff, hQ, lowerRepair, upperRepair]; grind
  · simp [supervaluationOn_eq_false_iff, hQ, lowerRepair, upperRepair]; grind

/-! ### Deployed determiners -/

/-- The Peters-Kleene deployment `D[A, B]` of a determiner on a trivalent restrictor `A` and
nuclear scope `B`, the restrictor first. -/
noncomputable def deployDeterminer (D : (U → Bool) → (U → Bool) → Bool)
    (A B : U → Trivalent) : Trivalent :=
  deployWith repairs (fun v ↦ D (v 0) (v 1)) ![A, B]

/-- If every repair of the restrictor makes the same quantifier of the determiner, the deployed
determiner is that quantifier deployed on the nuclear scope. -/
theorem deployDeterminer_of_forall {D : (U → Bool) → (U → Bool) → Bool} {A B : U → Trivalent}
    {Q : (U → Bool) → Bool} (h : ∀ g ∈ repairs A, D g = Q) :
    deployDeterminer D A B = deployQuantifier Q B :=
  deployWith_succ_of_forall (repairs_nonempty A) fun g hg ↦ funext fun v ↦ by
    simp [h g hg]

/-- Two repairs of the restrictor that the determiner tells apart make it undefined. -/
theorem deployDeterminer_eq_undefined_of_ne {D : (U → Bool) → (U → Bool) → Bool}
    {A B : U → Trivalent} {g h : U → Bool} (hg : g ∈ repairs A) (hh : h ∈ repairs A)
    (hgh : D g ≠ D h) : deployDeterminer D A B = .undefined :=
  deployWith_succ_of_ne hg hh fun e ↦ hgh (funext fun b ↦ congrFun e ![b])

/-- With a classical restrictor, a deployed determiner is the deployed quantifier it makes of the
restrictor. -/
theorem deployDeterminer_ofProp_left (D : (U → Bool) → (U → Bool) → Bool) (g : U → Bool)
    (B : U → Trivalent) :
    deployDeterminer D (fun u ↦ ofProp (g u)) B = deployQuantifier (D g) B :=
  deployDeterminer_of_forall fun h hh ↦ by rw [repairs_ofProp] at hh; rw [hh]

end Trivalent
