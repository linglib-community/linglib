/-
Copyright (c) 2026 Patrick Elliott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Elliott, Robert Hawkins
-/
module

public import Linglib.Logic.Trivalent.Part
public import Linglib.Logic.Trivalent.Powerset
public import Linglib.Logic.Trivalent.Supervaluation
public import Mathlib.Order.Interval.Basic
public import Linglib.Semantics.Quantification.Defs

/-!
# Peters-Kleene deployment

Peters-Kleene deployment applies a classical function to three-valued arguments one at a time, from
left to right ([george-2014] §3). An argument is replaced by each member of its repair set, and the
application goes through only if every repair leaves the same function of the remaining arguments.
Its one primitive is [reduction by a set](##Trivalent.pkReduce), a partial value, so that several
arguments are a `Part.bind`, and on a last argument reduction [is
supervaluation](##Trivalent.ofPart_pkReduce).
Deploying the classical connectives gives [the Middle Kleene tables of
Peters](##Trivalent.Connectives.middleKleene_eq_deploy), also called the Kleene-Peters tables. The
repairs of a trivalent predicate are [an interval of sets](##Trivalent.interval), got by
[reading each instance at a standard of its own](##Trivalent.coe_interval_eq_range), and
deploying `∀` gives [the Strong Kleene universal](##Trivalent.deployQuantifier_eq_forallStrong).
A deployed quantifier is [the greatest regular
extension](##Trivalent.IsRegular.kLE_deployQuantifier) of the classical one, and one that lives on
a set [takes its classical value](##Trivalent.deployQuantifier_of_livesOn) at a predicate defined
throughout the set.

## Implementation notes

The repair set of a value is the set of its readings at the two standards of
`Trivalent.Designation`, so a repair is a `Prop`, and a classical function is one on `Prop`:
`deploy₂ And` is the deployment of conjunction. `Set U → Prop` is `Quantifier U` by definition, so
quantifiers and determiners deploy as they are. A failed reduction is `Part.none`, where George has
a constant function to the failure value, and `Trivalent.ofPart` sends it to `undefined`.

Deployment is noncomputable, so its tables are proved by cases and not by `decide`, and it is stated
for one and two arguments. George's definitions are `n`-ary, but his results about truth functions
and determiners are unary and binary.

## References

* [george-2014]
* [peters-1979]
* [kleene-1952]
* [schlenker-2008a]
* [van-eijck-1996]
-/

@[expose] public section

namespace Trivalent

/-! ### Repair sets of truth values -/

/-- The repair set of a truth value is the set of its readings at the two standards: `{True}` for
`true`, `{False}` for `false`, and both for `undefined` (Definition 14 of [george-2014]). -/
def repairSet (a : Trivalent) : Set Prop :=
  Set.range fun d : Trivalent.Designation ↦ d.threshold ≤ a

theorem mem_repairSet_iff {a : Trivalent} {P : Prop} :
    P ∈ a.repairSet ↔ (a = .true → P) ∧ (P → a ≠ .false) := by
  constructor
  · rintro ⟨d, rfl⟩
    cases a <;> cases d <;> simp [Trivalent.Designation.threshold]
  · rintro ⟨h₁, h₂⟩
    by_cases hP : P
    · refine ⟨.lp, propext (iff_of_true ?_ hP)⟩
      have := h₂ hP
      cases a <;> first | decide | exact absurd rfl this
    · refine ⟨.k3, propext (iff_of_false ?_ hP)⟩
      have : a ≠ .true := fun e ↦ hP (h₁ e)
      cases a <;> first | decide | exact absurd rfl this

theorem repairSet_nonempty (a : Trivalent) : a.repairSet.Nonempty :=
  Set.range_nonempty _

@[simp] theorem repairSet_ofProp (P : Prop) [Decidable P] : (ofProp P).repairSet = {P} := by
  ext R
  rw [mem_repairSet_iff, Set.mem_singleton_iff]
  by_cases hP : P <;> simp [hP, ofProp]

@[simp] theorem repairSet_true : repairSet .true = {True} := repairSet_ofProp True

@[simp] theorem repairSet_false : repairSet .false = {False} := repairSet_ofProp False

@[simp] theorem repairSet_undefined : repairSet .undefined = Set.univ :=
  Set.eq_univ_of_forall fun _ ↦ mem_repairSet_iff.2 ⟨by simp, by simp⟩

/-- The repair set of a value is `Trivalent.toFinset` read in `Prop`. -/
theorem coe_mem_repairSet_iff {a : Trivalent} {b : Bool} :
    (b : Prop) ∈ a.repairSet ↔ b ∈ toFinset a := by
  rw [mem_repairSet_iff]
  cases a <;> cases b <;> simp


/-! ### Reduction by a set -/

section Reduce

variable {α γ : Type*} {f : α → γ} {X : Set α} {g : γ}

/-- The Peters-Kleene reduction `f///X` is the one value `f` takes throughout a nonempty `X`
(Definition 13 of [george-2014]). Since `f` may be curried, this is reduction of its first argument
position. -/
noncomputable def pkReduce (f : α → γ) (X : Set α) : Part γ where
  Dom := ∃ g, X.Nonempty ∧ ∀ a ∈ X, f a = g
  get h := h.choose

theorem mem_pkReduce : g ∈ pkReduce f X ↔ X.Nonempty ∧ ∀ a ∈ X, f a = g := by
  constructor
  · rintro ⟨h, rfl⟩
    exact h.choose_spec
  · intro h
    obtain ⟨a, ha⟩ := h.1
    have hex : ∃ g, X.Nonempty ∧ ∀ a ∈ X, f a = g := ⟨g, h⟩
    exact ⟨hex, (hex.choose_spec.2 a ha).symm.trans (h.2 a ha)⟩

theorem pkReduce_of_forall (hX : X.Nonempty) (h : ∀ a ∈ X, f a = g) :
    pkReduce f X = Part.some g :=
  Part.eq_some_iff.2 (mem_pkReduce.2 ⟨hX, h⟩)

@[simp] theorem pkReduce_singleton (a : α) : pkReduce f {a} = Part.some (f a) :=
  pkReduce_of_forall ⟨a, rfl⟩ (by simp)

theorem pkReduce_eq_none {a b : α} (ha : a ∈ X) (hb : b ∈ X) (h : f a ≠ f b) :
    pkReduce f X = Part.none :=
  Part.eq_none_iff.2 fun _ hg ↦
    h (((mem_pkReduce.1 hg).2 a ha).trans ((mem_pkReduce.1 hg).2 b hb).symm)

/-- On a last argument, reduction is supervaluation. -/
theorem ofPart_pkReduce (P : α → Prop) (hX : X.Nonempty) :
    ofPart (pkReduce P X) = supervaluationOn X P := by
  refine eq_of_eq_true_iff_of_eq_false_iff ?_ ?_
  · simp only [ofPart_eq_true_iff, mem_pkReduce, supervaluationOn_eq_true_iff]
    exact ⟨fun ⟨r, ⟨_, h⟩, hr⟩ a ha ↦ (h a ha).symm ▸ hr,
      fun h ↦ ⟨True, ⟨hX, fun a ha ↦ eq_true (h a ha)⟩, trivial⟩⟩
  · simp only [ofPart_eq_false_iff, mem_pkReduce, supervaluationOn_eq_false_iff]
    exact ⟨fun ⟨r, ⟨_, h⟩, hr⟩ ↦ ⟨hX, fun a ha hP ↦ hr ((h a ha) ▸ hP)⟩,
      fun ⟨_, h⟩ ↦ ⟨False, ⟨hX, fun a ha ↦ eq_false (h a ha)⟩, id⟩⟩

end Reduce

/-! ### Deploying truth functions -/

section Connectives

variable {f : Prop → Prop} {g : Prop → Prop → Prop} (x y : Trivalent)

/-- The deployment `f[x]` of a unary truth function (Definition 15 of [george-2014]). -/
noncomputable def deploy₁ (f : Prop → Prop) (x : Trivalent) : Trivalent :=
  ofPart (pkReduce f x.repairSet)

/-- The deployment `g[x, y]` of a binary truth function, which is `g[x][y]` (Definition 15 of
[george-2014], for two arguments). -/
noncomputable def deploy₂ (g : Prop → Prop → Prop) (x y : Trivalent) : Trivalent :=
  ofPart ((pkReduce g x.repairSet).bind (pkReduce · y.repairSet))

/-- Unary deployment is the supervaluation over the repair set of its argument. -/
theorem deploy₁_eq_supervaluationOn (f : Prop → Prop) (x : Trivalent) :
    deploy₁ f x = supervaluationOn x.repairSet f :=
  ofPart_pkReduce f x.repairSet_nonempty

-- Remark 8
theorem deploy₁_ofProp (f : Prop → Prop) (P : Prop) [Decidable P] [Decidable (f P)] :
    deploy₁ f (ofProp P) = ofProp (f P) := by
  simp [deploy₁]

/-- A classical first argument fills the first argument position. -/
theorem deploy₂_ofProp_left (g : Prop → Prop → Prop) (P : Prop) [Decidable P] :
    deploy₂ g (ofProp P) y = deploy₁ (g P) y := by
  simp [deploy₂, deploy₁, Part.bind_some]

-- Remark 8
theorem deploy₂_ofProp (g : Prop → Prop → Prop) (P Q : Prop) [Decidable P] [Decidable Q]
    [Decidable (g P Q)] : deploy₂ g (ofProp P) (ofProp Q) = ofProp (g P Q) := by
  rw [deploy₂_ofProp_left, deploy₁_ofProp]

theorem deploy₂_true (g : Prop → Prop → Prop) : deploy₂ g .true y = deploy₁ (g True) y :=
  deploy₂_ofProp_left y g True

theorem deploy₂_false (g : Prop → Prop → Prop) : deploy₂ g .false y = deploy₁ (g False) y :=
  deploy₂_ofProp_left y g False

/-- An undefined argument in a position whose value matters makes the deployment undefined,
generalising Remarks 9 and 10. -/
theorem deploy₁_undefined_of_ne (h : f True ≠ f False) : deploy₁ f .undefined = .undefined := by
  simp [deploy₁, pkReduce_eq_none (Set.mem_univ True) (Set.mem_univ False) h]

theorem deploy₂_undefined_of_ne (h : g True ≠ g False) : deploy₂ g .undefined y = .undefined := by
  simp [deploy₂, pkReduce_eq_none (Set.mem_univ True) (Set.mem_univ False) h, Part.bind_none]

/-- An undefined first argument is skipped if its position does not matter. -/
theorem deploy₂_undefined_of_eq (h : g True = g False) :
    deploy₂ g .undefined y = deploy₁ (g True) y := by
  have : pkReduce g Set.univ = Part.some (g True) := pkReduce_of_forall ⟨True, trivial⟩ fun P _ ↦ by
    rcases Classical.propComplete P with rfl | rfl
    · rfl
    · exact h.symm
  simp [deploy₂, deploy₁, this, Part.bind_some]

/-- A constant function ignores its argument, which is what rescues `0 ∧ #`. -/
theorem deploy₁_const (P : Prop) [Decidable P] : deploy₁ (fun _ ↦ P) y = ofProp P := by
  rw [deploy₁, pkReduce_of_forall y.repairSet_nonempty fun _ _ ↦ rfl, ofPart_some]

/-- Deploying the identity is the identity. -/
theorem deploy₁_id : deploy₁ id y = y := by
  cases y
  · simp [deploy₁]
  · exact deploy₁_undefined_of_ne (by simp)
  · simp [deploy₁]

-- Proposition 3
@[simp] theorem deploy₁_not : deploy₁ Not = compl := by
  funext y
  cases y
  · simp [deploy₁]
  · exact deploy₁_undefined_of_ne (by simp)
  · simp [deploy₁]

-- Proposition 3
@[simp] theorem deploy₂_and : deploy₂ And = meetMiddle := by
  funext x y
  cases x
  · rw [deploy₂_false, show And False = fun _ ↦ False by simp [funext_iff], deploy₁_const]
    cases y <;> rfl
  · rw [deploy₂_undefined_of_ne _ fun h ↦ by simpa using congrFun h True]
    cases y <;> rfl
  · rw [deploy₂_true, show And True = id by simp [funext_iff], deploy₁_id]
    cases y <;> rfl

-- Proposition 3
@[simp] theorem deploy₂_or : deploy₂ Or = joinMiddle := by
  funext x y
  cases x
  · rw [deploy₂_false, show Or False = id by simp [funext_iff], deploy₁_id]
    cases y <;> rfl
  · rw [deploy₂_undefined_of_ne _ fun h ↦ by simpa using congrFun h False]
    cases y <;> rfl
  · rw [deploy₂_true, show Or True = fun _ ↦ True by simp [funext_iff], deploy₁_const]
    cases y <;> rfl

-- Proposition 3
@[simp] theorem deploy₂_imp : deploy₂ (· → ·) = fun x y ↦ joinMiddle xᶜ y := by
  funext x y
  cases x
  · rw [deploy₂_false, show (False → ·) = fun _ ↦ True by simp, deploy₁_const]
    cases y <;> rfl
  · rw [deploy₂_undefined_of_ne _ fun h ↦ by simpa using congrFun h False]
    cases y <;> rfl
  · rw [deploy₂_true, show (True → ·) = id by simp [funext_iff], deploy₁_id]
    cases y <;> rfl

/-- The Middle Kleene connectives are the Peters-Kleene deployments of the classical ones
(Proposition 3 of [george-2014]). -/
theorem Connectives.middleKleene_eq_deploy :
    Connectives.middleKleene = ⟨deploy₂ And, deploy₂ Or, deploy₂ (· → ·)⟩ := by
  rw [deploy₂_and, deploy₂_or, deploy₂_imp]; rfl

end Connectives

/-! ### The interval of a predicate -/

variable {U : Type*}

theorem posExt_subset (A : U → Trivalent) : posExt A ⊆ (negExt A)ᶜ := fun u hu hn ↦ by
  simp only [mem_posExt, mem_negExt] at hu hn; rw [hu] at hn; exact absurd hn (by decide)

/-- The interval of sets that a trivalent predicate leaves open, from where it is true to where it
is not false. Its members are the repairs of the predicate (Definition 19 of [george-2014]). -/
protected def interval (A : U → Trivalent) : NonemptyInterval (Set U) :=
  ⟨(posExt A, (negExt A)ᶜ), posExt_subset A⟩

@[simp] theorem fst_interval (A : U → Trivalent) : (Trivalent.interval A).fst = posExt A := rfl

@[simp] theorem snd_interval (A : U → Trivalent) : (Trivalent.interval A).snd = (negExt A)ᶜ := rfl

@[simp] theorem mem_interval {A : U → Trivalent} {X : Set U} :
    X ∈ Trivalent.interval A ↔ posExt A ⊆ X ∧ X ⊆ (negExt A)ᶜ :=
  Iff.rfl

@[simp, norm_cast] theorem coe_interval (A : U → Trivalent) :
    (Trivalent.interval A : Set (Set U)) = Set.Icc (posExt A) (negExt A)ᶜ :=
  rfl

/-- A set is in the interval of a predicate iff it agrees with the predicate wherever it is
classical and is free wherever it is undefined. -/
theorem mem_interval_iff_forall_mem_repairSet {A : U → Trivalent} {X : Set U} :
    X ∈ Trivalent.interval A ↔ ∀ u, (u ∈ X) ∈ (A u).repairSet := by
  simp only [mem_interval, mem_repairSet_iff]
  exact ⟨fun h u ↦ ⟨fun e ↦ h.1 e, fun hu ↦ h.2 hu⟩,
    fun h ↦ ⟨fun u hu ↦ (h u).1 hu, fun u hu ↦ (h u).2 hu⟩⟩

/-- The interval of a predicate is got by reading each instance at a standard of its own. -/
theorem coe_interval_eq_range (A : U → Trivalent) :
    (Trivalent.interval A : Set (Set U)) =
      Set.range fun c : U → Designation ↦ {u | (c u).threshold ≤ A u} := by
  ext X
  rw [SetLike.mem_coe, mem_interval_iff_forall_mem_repairSet]
  constructor
  · intro h
    choose c hc using h
    exact ⟨c, Set.ext fun u ↦ iff_of_eq (hc u)⟩
  · rintro ⟨c, rfl⟩ u
    exact ⟨c u, rfl⟩

/-- A classical predicate leaves only itself open. -/
@[simp] theorem interval_ofProp (R : Set U) [DecidablePred (· ∈ R)] :
    Trivalent.interval (fun u ↦ ofProp (u ∈ R)) = NonemptyInterval.pure R := by
  refine NonemptyInterval.toProd_injective (Prod.ext ?_ ?_) <;> ext u <;> simp [Trivalent.interval]

open Classical in
/-- The predicate true on `B`, undefined on the rest of `C` and false elsewhere. -/
noncomputable def ofIcc (B C : Set U) : U → Trivalent :=
  fun u ↦ if u ∈ B then .true else if u ∈ C then .undefined else .false

/-- Every interval of sets is the interval of a predicate. -/
theorem interval_ofIcc {B C : Set U} (h : B ⊆ C) : Trivalent.interval (ofIcc B C) = ⟨(B, C), h⟩ := by
  have e₁ : posExt (ofIcc B C) = B := by
    ext u
    by_cases hu : u ∈ B
    · simp [ofIcc, hu]
    · by_cases hc : u ∈ C <;> simp [ofIcc, hu, hc]
  have e₂ : (negExt (ofIcc B C))ᶜ = C := by
    ext u
    by_cases hu : u ∈ B
    · simp [ofIcc, hu, h hu]
    · by_cases hc : u ∈ C <;> simp [ofIcc, hu, hc]
  exact NonemptyInterval.toProd_injective (Prod.ext e₁ e₂)

/-! ### Deployed quantifiers -/

variable {Q : Set U → Prop}

/-- The Peters-Kleene deployment `Q[A]` of a generalised quantifier on a trivalent predicate. -/
noncomputable def deployQuantifier (Q : Set U → Prop) (A : U → Trivalent) : Trivalent :=
  ofPart (pkReduce Q (Trivalent.interval A))

/-- A deployed quantifier is the supervaluation over the interval of its argument. -/
theorem deployQuantifier_eq_supervaluationOn (Q : Set U → Prop) (A : U → Trivalent) :
    deployQuantifier Q A = supervaluationOn (Trivalent.interval A) Q :=
  ofPart_pkReduce Q (Trivalent.interval A).coe_nonempty

/-- A deployed quantifier is the supervaluation over the readings of its instances, each at a
standard of its own. -/
theorem deployQuantifier_eq_supervaluationOn_standards (Q : Set U → Prop) (A : U → Trivalent) :
    deployQuantifier Q A =
      supervaluationOn Set.univ fun c : U → Designation ↦ Q {u | (c u).threshold ≤ A u} := by
  rw [deployQuantifier_eq_supervaluationOn, coe_interval_eq_range, ← Set.image_univ,
    supervaluationOn_image]
  rfl

/-- A monotone quantifier deployed on a predicate is settled by its K3 and LP readings. -/
theorem deployQuantifier_of_monotone (hQ : Monotone Q) (A : U → Trivalent) :
    deployQuantifier Q A =
      supervaluationOn Set.univ fun d : Designation ↦ Q {u | d.threshold ≤ A u} :=
  (deployQuantifier_eq_supervaluationOn_standards Q A).trans
    (supervaluationOn_pi_eq_const_of_monotone (Q := fun p ↦ Q {u | p u}) A fun _ _ h ↦ hQ h)

/-- An antitone quantifier deployed on a predicate is settled by its K3 and LP readings. -/
theorem deployQuantifier_of_antitone (hQ : Antitone Q) (A : U → Trivalent) :
    deployQuantifier Q A =
      supervaluationOn Set.univ fun d : Designation ↦ Q {u | d.threshold ≤ A u} :=
  (deployQuantifier_eq_supervaluationOn_standards Q A).trans
    (supervaluationOn_pi_eq_const_of_antitone (Q := fun p ↦ Q {u | p u}) A fun _ _ h ↦ hQ h)

/-- On a classical predicate, a deployed quantifier is the quantifier. -/
@[simp] theorem deployQuantifier_ofProp (Q : Set U → Prop) (R : Set U) [DecidablePred (· ∈ R)]
    [Decidable (Q R)] : deployQuantifier Q (fun u ↦ ofProp (u ∈ R)) = ofProp (Q R) := by
  simp [deployQuantifier]

/-- Deploying `∀`, the quantifier true only of `Set.univ` (Definition 16 of [george-2014]), gives
the Strong Kleene universal, as George computes in §4.1. -/
theorem deployQuantifier_eq_forallStrong (A : U → Trivalent) :
    deployQuantifier (· = Set.univ) A = forallStrong A := by
  rw [deployQuantifier_eq_supervaluationOn, coe_interval]
  refine eq_of_eq_true_iff_of_eq_false_iff ?_ ?_
  · rw [supervaluationOn_eq_true_iff, forallStrong_eq_true_iff]
    refine ⟨fun h u ↦ ?_, fun h X hX ↦ Set.eq_univ_of_forall fun u ↦ hX.1 (mem_posExt.2 (h u))⟩
    exact mem_posExt.1 ((h _ ⟨le_rfl, posExt_subset A⟩).symm ▸ Set.mem_univ u)
  · rw [supervaluationOn_eq_false_iff, forallStrong_eq_false_iff]
    refine ⟨fun ⟨_, h⟩ ↦ ?_, fun ⟨u, hu⟩ ↦ ⟨⟨_, le_rfl, posExt_subset A⟩, fun X hX e ↦
      hX.2 (e ▸ Set.mem_univ u) (mem_negExt.2 hu)⟩⟩
    obtain ⟨u, hu⟩ := (Set.ne_univ_iff_exists_notMem _).1 (h _ ⟨posExt_subset A, le_rfl⟩)
    exact ⟨u, mem_negExt.1 (not_not.1 hu)⟩

/-- Deploying `∃`, the quantifier true of the nonempty sets (Definition 17 of [george-2014]),
gives the Strong Kleene existential, by the computation George calls analogous in §4.1. -/
theorem deployQuantifier_eq_existsStrong (A : U → Trivalent) :
    deployQuantifier Set.Nonempty A = existsStrong A := by
  rw [deployQuantifier_eq_supervaluationOn, coe_interval]
  refine eq_of_eq_true_iff_of_eq_false_iff ?_ ?_
  · rw [supervaluationOn_eq_true_iff, existsStrong_eq_true_iff]
    refine ⟨fun h ↦ ?_, fun ⟨u, hu⟩ X hX ↦ ⟨u, hX.1 (mem_posExt.2 hu)⟩⟩
    obtain ⟨u, hu⟩ := h _ ⟨le_rfl, posExt_subset A⟩
    exact ⟨u, mem_posExt.1 hu⟩
  · rw [supervaluationOn_eq_false_iff, existsStrong_eq_false_iff]
    refine ⟨fun ⟨_, h⟩ u ↦ ?_, fun h ↦ ⟨⟨_, le_rfl, posExt_subset A⟩, fun X hX ⟨u, hu⟩ ↦
      hX.2 hu (mem_negExt.2 (h u))⟩⟩
    by_contra hu
    exact h _ ⟨posExt_subset A, le_rfl⟩ ⟨u, hu⟩

/-! ### Regular extensions -/

section Regular

open Bilattice

variable {T : (U → Trivalent) → Trivalent}

/-- A predicate with more information leaves a smaller interval open. -/
theorem interval_le_interval {A A' : U → Trivalent} :
    Trivalent.interval A' ≤ Trivalent.interval A ↔ ∀ u, A u ≤ₖ A' u := by
  simp only [NonemptyInterval.le_def, fst_interval, snd_interval,
    kLE_iff_eq_true_imp_eq_false_imp]
  exact ⟨fun h u ↦ ⟨fun ht ↦ h.1 ht, fun hf ↦ by_contra fun hn ↦ h.2 hn hf⟩,
    fun h ↦ ⟨fun u hu ↦ (h u).1 hu, fun u hu hn ↦ hu ((h u).2 hn)⟩⟩

/-- Supervaluation over a smaller nonempty set has at least as much information. -/
theorem supervaluationOn_kLE_supervaluationOn {α : Type*} {s t : Set α} {P : α → Prop}
    (h : t ⊆ s) (ht : t.Nonempty) : supervaluationOn s P ≤ₖ supervaluationOn t P := by
  simp only [kLE_iff_eq_true_imp_eq_false_imp, supervaluationOn_eq_true_iff,
    supervaluationOn_eq_false_iff]
  exact ⟨fun hs a ha ↦ hs a (h ha), fun hs ↦ ⟨ht, fun a ha ↦ hs.2 a (h ha)⟩⟩

theorem isExtensionOf_deployQuantifier (Q : Set U → Prop) : IsExtensionOf Q (deployQuantifier Q) :=
  fun R ↦ by classical exact deployQuantifier_ofProp Q R

theorem isRegular_deployQuantifier (Q : Set U → Prop) : IsRegular (deployQuantifier Q) :=
  fun A A' h ↦ by
    rw [deployQuantifier_eq_supervaluationOn, deployQuantifier_eq_supervaluationOn]
    exact supervaluationOn_kLE_supervaluationOn
      (NonemptyInterval.coe_subset_coe.2 (interval_le_interval.2 h)) (Trivalent.interval A').coe_nonempty

/-- The deployment of a quantifier is its greatest regular extension: a regular extension has
the deployed value wherever it is defined. -/
theorem IsRegular.kLE_deployQuantifier (hT : IsRegular T) (hQ : IsExtensionOf Q T)
    (A : U → Trivalent) : T A ≤ₖ deployQuantifier Q A := by
  classical
  have key (X : Set U) (hX : X ∈ Trivalent.interval A) : T A ≤ₖ ofProp (Q X) := by
    have h := hT (A := A) (A' := fun u ↦ ofProp (u ∈ X))
      (interval_le_interval.1 (by rw [interval_ofProp]; exact hX))
    rwa [hQ X] at h
  simp only [kLE_iff_eq_true_imp_eq_false_imp] at key ⊢
  rw [deployQuantifier_eq_supervaluationOn, supervaluationOn_eq_true_iff,
    supervaluationOn_eq_false_iff]
  exact ⟨fun ht X hX ↦ ofProp_eq_true_iff.1 ((key X hX).1 ht), fun hf ↦
    ⟨(Trivalent.interval A).coe_nonempty, fun X hX ↦ ofProp_eq_false_iff.1 ((key X hX).2 hf)⟩⟩

theorem isRegular_forallWeak : IsRegular (forallWeak (ι := U)) := fun A A' h ↦ by
  rw [kLE_iff]
  by_cases hd : ∀ u, A u ≠ .undefined
  · exact .inr (congrArg _ (funext fun u ↦ (kLE_iff.1 (h u)).resolve_left (hd u)))
  · exact .inl (by simpa using hd)

theorem isExtensionOf_forallWeak : IsExtensionOf (· = Set.univ) (forallWeak (ι := U)) := fun R ↦ by
  refine eq_of_eq_true_iff_of_eq_false_iff ?_ ?_ <;> simp [Set.eq_univ_iff_forall]

/-- Haug's universal is not regular: a gap filled by `false` turns `true` into `false`. -/
theorem not_isRegular_forallHaug [Nontrivial U] : ¬ IsRegular (forallHaug (W := U)) := by
  classical
  obtain ⟨a, b, hab⟩ := exists_pair_ne U
  intro h
  have := h (A := fun u ↦ if u = a then .undefined else .true)
    (A' := fun u ↦ if u = a then .false else .true) fun u ↦ by
      split_ifs
      exacts [undefined_kLE _, kLE_iff.2 (.inr rfl)]
  have h₁ : forallHaug (fun u ↦ if u = a then Trivalent.undefined else .true) = .true := by
    rw [forallHaug_eq_true_iff]
    exact ⟨⟨b, by simp [hab.symm]⟩, fun w ↦ by split_ifs <;> decide⟩
  have h₂ : forallHaug (fun u ↦ if u = a then Trivalent.false else .true) = .false := by
    rw [forallHaug_eq_false_iff]
    exact ⟨a, by simp⟩
  rw [h₁, h₂] at this
  exact absurd this (by decide)

end Regular

/-! ### Quantifiers that live on a set -/

section LivesOn

open Quantifier

variable {R : Set U} {A A' : U → Trivalent}

/-- A deployed quantifier is defined iff it gives one value throughout the interval of its
argument. -/
theorem deployQuantifier_ne_undefined_iff :
    deployQuantifier Q A ≠ .undefined ↔ ∀ X ∈ Trivalent.interval A, ∀ Y ∈ Trivalent.interval A, (Q X ↔ Q Y) := by
  rw [deployQuantifier_eq_supervaluationOn, supervaluationOn_ne_undefined_iff]
  rfl

/-- Intersecting the sets in the interval of a predicate with `R` gives the interval between the
intersections of its ends. -/
theorem image_inter_interval (R : Set U) (A : U → Trivalent) :
    (R ∩ ·) '' (Trivalent.interval A : Set (Set U)) = Set.Icc (R ∩ posExt A) (R ∩ (negExt A)ᶜ) := by
  refine Set.Subset.antisymm ?_ fun X hX ↦ ⟨X ∪ posExt A, ⟨Set.subset_union_right,
    Set.union_subset (hX.2.trans Set.inter_subset_right) (posExt_subset A)⟩, ?_⟩
  · rintro _ ⟨Y, hY, rfl⟩
    exact ⟨Set.inter_subset_inter_right _ hY.1, Set.inter_subset_inter_right _ hY.2⟩
  · change R ∩ (X ∪ posExt A) = X
    rw [Set.inter_union_distrib_left, Set.inter_eq_right.2 (hX.2.trans Set.inter_subset_left),
      Set.union_eq_left.2 hX.1]

/-- A quantifier that lives on `R` is deployed on the part of its argument inside `R`. -/
theorem deployQuantifier_eq_supervaluationOn_inter {Q : Quantifier U} (hQ : Q.LivesOn R)
    (A : U → Trivalent) : deployQuantifier Q A =
      supervaluationOn (Set.Icc (R ∩ posExt A) (R ∩ (negExt A)ᶜ)) Q := by
  rw [deployQuantifier_eq_supervaluationOn, supervaluationOn_congr fun X _ ↦ hQ X,
    ← image_inter_interval, supervaluationOn_image]
  rfl

/-- A quantifier that lives on `R` is deployed on what its argument does on `R`. -/
theorem deployQuantifier_congr_of_livesOn {Q : Quantifier U} (hQ : Q.LivesOn R)
    (h : Set.EqOn A A' R) : deployQuantifier Q A = deployQuantifier Q A' := by
  rw [deployQuantifier_eq_supervaluationOn_inter hQ, deployQuantifier_eq_supervaluationOn_inter hQ]
  exact congrArg₂ (fun B C ↦ supervaluationOn (Set.Icc B C) Q)
    (h.inter_preimage_eq {Trivalent.true}) (h.inter_preimage_eq {Trivalent.false}ᶜ)

open Classical in
/-- A quantifier that lives on `R`, deployed on a predicate defined throughout `R`, has its
classical value: the gaps of the argument outside `R` are filtered. -/
theorem deployQuantifier_of_livesOn {Q : Quantifier U} (hQ : Q.LivesOn R)
    (h : ∀ u ∈ R, A u ≠ .undefined) : deployQuantifier Q A = ofProp (Q (posExt A)) := by
  have e : R ∩ (negExt A)ᶜ = R ∩ posExt A := Set.ext fun u ↦ and_congr_right fun hu ↦ by
    have := h u hu
    cases hA : A u <;> simp_all
  rw [deployQuantifier_eq_supervaluationOn_inter hQ, e, Set.Icc_self, supervaluationOn_singleton]
  exact ofProp_congr (hQ _).symm

end LivesOn

/-! ### Deployed determiners -/

/-- The Peters-Kleene deployment `D[B, A]` of a determiner on a trivalent restrictor `B` and nuclear
scope `A`, the restrictor first. -/
noncomputable def deployDeterminer (D : Set U → Set U → Prop) (B A : U → Trivalent) : Trivalent :=
  ofPart ((pkReduce D (Trivalent.interval B)).bind (pkReduce · (Trivalent.interval A)))

/-- If every repair of the restrictor makes the same quantifier of the determiner, the deployed
determiner is that quantifier deployed on the nuclear scope. -/
theorem deployDeterminer_of_forall {D : Set U → Set U → Prop} {B A : U → Trivalent}
    (h : ∀ R ∈ Trivalent.interval B, D R = Q) : deployDeterminer D B A = deployQuantifier Q A := by
  rw [deployDeterminer,
    pkReduce_of_forall (X := (Trivalent.interval B : Set (Set U))) (Trivalent.interval B).coe_nonempty h,
    Part.bind_some, deployQuantifier]

/-- Two repairs of the restrictor that the determiner tells apart make it undefined. -/
theorem deployDeterminer_eq_undefined_of_ne {D : Set U → Set U → Prop} {B A : U → Trivalent}
    {R S : Set U} (hR : R ∈ Trivalent.interval B) (hS : S ∈ Trivalent.interval B) (h : D R ≠ D S) :
    deployDeterminer D B A = .undefined := by
  rw [deployDeterminer, pkReduce_eq_none (X := (Trivalent.interval B : Set (Set U))) hR hS h,
    Part.bind_none, ofPart_none]

/-- With a classical restrictor, a deployed determiner is the deployed quantifier it makes of the
restrictor. -/
@[simp] theorem deployDeterminer_ofProp_left (D : Set U → Set U → Prop) (R : Set U)
    [DecidablePred (· ∈ R)] (A : U → Trivalent) :
    deployDeterminer D (fun u ↦ ofProp (u ∈ R)) A = deployQuantifier (D R) A :=
  deployDeterminer_of_forall fun S hS ↦ by
    rw [interval_ofProp, NonemptyInterval.mem_pure] at hS; rw [hS]

open Classical in
/-- A conservative determiner with a classical restrictor, deployed on a scope defined throughout
the restrictor, has its classical value: the restrictor filters the gaps of the scope. -/
theorem deployDeterminer_of_conservative {D : Quantifier.Det U} (hD : D.Conservative) {R : Set U}
    {A : U → Trivalent} (h : ∀ u ∈ R, A u ≠ .undefined) :
    deployDeterminer D (fun u ↦ ofProp (u ∈ R)) A = ofProp (D R (posExt A)) := by
  rw [deployDeterminer_ofProp_left]
  exact deployQuantifier_of_livesOn (fun B ↦ hD R B) h

end Trivalent
