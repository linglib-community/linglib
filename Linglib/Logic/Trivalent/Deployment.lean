/-
Copyright (c) 2026 Patrick Elliott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Elliott, Robert Hawkins
-/
module

public import Linglib.Logic.Trivalent.Part
public import Linglib.Logic.Trivalent.Powerset
public import Linglib.Logic.Trivalent.Supervaluation

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
repairs of a trivalent predicate are [an interval of sets](##Trivalent.repairs_eq_Icc), got by
[reading each instance at a standard of its own](##Trivalent.repairs_eq_range), and deploying `∀`
gives [the Strong Kleene universal](##Trivalent.deployQuantifier_eq_forallStrong).

## Implementation notes

The repair set of a value is the set of its readings at the two standards of
`Trivalent.Designation`, so a repair is a `Prop`, and a classical function is one on `Prop`:
`deploy₂ And` is the deployment of conjunction. `Set U → Prop` is `Quantifier U` by definition, so
quantifiers and determiners deploy as they are. A failed reduction is `Part.none`, where George has
a constant function to the failure value, and `SignType.ofPart` sends it to `0`, the encoding of
undefinedness used for partial propositions elsewhere.

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

namespace SignType

/-! ### Repair sets of truth values -/

/-- The repair set of a truth value is the set of its readings at the two standards: `{True}` for
`1`, `{False}` for `-1`, and both for `0` (Definition 14 of [george-2014]). -/
def repairSet (a : SignType) : Set Prop :=
  Set.range fun d : Trivalent.Designation ↦ d.threshold ≤ a

theorem mem_repairSet_iff {a : SignType} {P : Prop} :
    P ∈ a.repairSet ↔ (a = 1 → P) ∧ (P → a ≠ -1) := by
  constructor
  · rintro ⟨d, rfl⟩
    cases a <;> cases d <;> simp [Trivalent.Designation.threshold]
  · rintro ⟨h₁, h₂⟩
    by_cases hP : P
    · refine ⟨.lp, propext (iff_of_true ?_ hP)⟩
      have := h₂ hP
      cases a <;> first | decide | exact absurd rfl this
    · refine ⟨.k3, propext (iff_of_false ?_ hP)⟩
      have : a ≠ 1 := fun e ↦ hP (h₁ e)
      cases a <;> first | decide | exact absurd rfl this

theorem repairSet_nonempty (a : SignType) : a.repairSet.Nonempty :=
  Set.range_nonempty _

@[simp] theorem repairSet_ofProp (P : Prop) [Decidable P] : (ofProp P).repairSet = {P} := by
  ext R
  rw [mem_repairSet_iff, Set.mem_singleton_iff]
  by_cases hP : P <;> simp [hP, ofProp]

@[simp] theorem repairSet_one : repairSet 1 = {True} := repairSet_ofProp True

@[simp] theorem repairSet_neg_one : repairSet (-1) = {False} := repairSet_ofProp False

@[simp] theorem repairSet_zero : repairSet 0 = Set.univ :=
  Set.eq_univ_of_forall fun _ ↦ mem_repairSet_iff.2 ⟨by simp, by simp⟩

/-- The repair set of a value is `SignType.toFinset` read in `Prop`. -/
theorem coe_mem_repairSet_iff {a : SignType} {b : Bool} :
    (b : Prop) ∈ a.repairSet ↔ b ∈ toFinset a := by
  rw [mem_repairSet_iff]
  cases a <;> cases b <;> simp

end SignType

namespace Trivalent

open SignType

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
  refine eq_of_eq_one_iff_of_eq_neg_one_iff ?_ ?_
  · simp only [ofPart_eq_one_iff, mem_pkReduce, supervaluationOn_eq_one_iff]
    exact ⟨fun ⟨r, ⟨_, h⟩, hr⟩ a ha ↦ (h a ha).symm ▸ hr,
      fun h ↦ ⟨True, ⟨hX, fun a ha ↦ eq_true (h a ha)⟩, trivial⟩⟩
  · simp only [ofPart_eq_neg_one_iff, mem_pkReduce, supervaluationOn_eq_neg_one_iff]
    exact ⟨fun ⟨r, ⟨_, h⟩, hr⟩ ↦ ⟨hX, fun a ha hP ↦ hr ((h a ha) ▸ hP)⟩,
      fun ⟨_, h⟩ ↦ ⟨False, ⟨hX, fun a ha ↦ eq_false (h a ha)⟩, id⟩⟩

end Reduce

/-! ### Deploying truth functions -/

section Connectives

variable {f : Prop → Prop} {g : Prop → Prop → Prop} (x y : SignType)

/-- The deployment `f[x]` of a unary truth function (Definition 15 of [george-2014]). -/
noncomputable def deploy₁ (f : Prop → Prop) (x : SignType) : SignType :=
  ofPart (pkReduce f x.repairSet)

/-- The deployment `g[x, y]` of a binary truth function, which is `g[x][y]` (Definition 15 of
[george-2014], for two arguments). -/
noncomputable def deploy₂ (g : Prop → Prop → Prop) (x y : SignType) : SignType :=
  ofPart ((pkReduce g x.repairSet).bind (pkReduce · y.repairSet))

/-- Unary deployment is the supervaluation over the repair set of its argument. -/
theorem deploy₁_eq_supervaluationOn (f : Prop → Prop) (x : SignType) :
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

theorem deploy₂_one (g : Prop → Prop → Prop) : deploy₂ g 1 y = deploy₁ (g True) y :=
  deploy₂_ofProp_left y g True

theorem deploy₂_neg_one (g : Prop → Prop → Prop) : deploy₂ g (-1) y = deploy₁ (g False) y :=
  deploy₂_ofProp_left y g False

/-- An undefined argument in a position whose value matters makes the deployment undefined,
generalising Remarks 9 and 10. -/
theorem deploy₁_zero_of_ne (h : f True ≠ f False) : deploy₁ f 0 = 0 := by
  simp [deploy₁, pkReduce_eq_none (Set.mem_univ True) (Set.mem_univ False) h]

theorem deploy₂_zero_of_ne (h : g True ≠ g False) : deploy₂ g 0 y = 0 := by
  simp [deploy₂, pkReduce_eq_none (Set.mem_univ True) (Set.mem_univ False) h, Part.bind_none]

/-- An undefined first argument is skipped if its position does not matter. -/
theorem deploy₂_zero_of_eq (h : g True = g False) : deploy₂ g 0 y = deploy₁ (g True) y := by
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
  · exact deploy₁_zero_of_ne (by simp)
  · simp [deploy₁]
  · simp [deploy₁]

-- Proposition 3
@[simp] theorem deploy₁_not : deploy₁ Not = Neg.neg := by
  funext y
  cases y
  · exact deploy₁_zero_of_ne (by simp)
  · simp [deploy₁]
  · simp [deploy₁]

-- Proposition 3
@[simp] theorem deploy₂_and : deploy₂ And = meetMiddle := by
  funext x y
  cases x
  · rw [SignType.zero_eq_zero, deploy₂_zero_of_ne _ fun h ↦ by simpa using congrFun h True]
    cases y <;> rfl
  · rw [SignType.neg_eq_neg_one, deploy₂_neg_one,
      show And False = fun _ ↦ False by simp [funext_iff], deploy₁_const]
    cases y <;> rfl
  · rw [SignType.pos_eq_one, deploy₂_one, show And True = id by simp [funext_iff], deploy₁_id]
    cases y <;> rfl

-- Proposition 3
@[simp] theorem deploy₂_or : deploy₂ Or = joinMiddle := by
  funext x y
  cases x
  · rw [SignType.zero_eq_zero, deploy₂_zero_of_ne _ fun h ↦ by simpa using congrFun h False]
    cases y <;> rfl
  · rw [SignType.neg_eq_neg_one, deploy₂_neg_one, show Or False = id by simp [funext_iff],
      deploy₁_id]
    cases y <;> rfl
  · rw [SignType.pos_eq_one, deploy₂_one, show Or True = fun _ ↦ True by simp [funext_iff],
      deploy₁_const]
    cases y <;> rfl

-- Proposition 3
@[simp] theorem deploy₂_imp : deploy₂ (· → ·) = fun x y ↦ joinMiddle (-x) y := by
  funext x y
  cases x
  · rw [SignType.zero_eq_zero, deploy₂_zero_of_ne _ fun h ↦ by simpa using congrFun h False]
    cases y <;> rfl
  · rw [SignType.neg_eq_neg_one, deploy₂_neg_one, show (False → ·) = fun _ ↦ True by simp,
      deploy₁_const]
    cases y <;> rfl
  · rw [SignType.pos_eq_one, deploy₂_one, show (True → ·) = id by simp [funext_iff], deploy₁_id]
    cases y <;> rfl

/-- The Middle Kleene connectives are the Peters-Kleene deployments of the classical ones
(Proposition 3 of [george-2014]). -/
theorem Connectives.middleKleene_eq_deploy :
    Connectives.middleKleene = ⟨deploy₂ And, deploy₂ Or, deploy₂ (· → ·)⟩ := by
  rw [deploy₂_and, deploy₂_or, deploy₂_imp]; rfl

end Connectives

/-! ### Repairs of a predicate -/

variable {U : Type*}

/-- The repairs of a trivalent predicate are the sets that agree with it wherever it is classical
and are free wherever it is undefined (Definition 19 of [george-2014]). -/
def repairs (A : U → SignType) : Set (Set U) :=
  {X | ∀ u, (u ∈ X) ∈ (A u).repairSet}

theorem mem_repairs {A : U → SignType} {X : Set U} :
    X ∈ repairs A ↔ ∀ u, (u ∈ X) ∈ (A u).repairSet :=
  Iff.rfl

/-- The repairs of a predicate are the interval from where it is true to where it is not false. -/
theorem repairs_eq_Icc (A : U → SignType) : repairs A = Set.Icc (posSupport A) (negSupport A)ᶜ := by
  ext X
  simp only [mem_repairs, mem_repairSet_iff]
  exact ⟨fun h ↦ ⟨fun u hu ↦ (h u).1 hu, fun u hu ↦ (h u).2 hu⟩,
    fun h u ↦ ⟨fun e ↦ h.1 e, fun hu ↦ h.2 hu⟩⟩

/-- The repairs of a predicate are got by reading each instance at a standard of its own. -/
theorem repairs_eq_range (A : U → SignType) :
    repairs A = Set.range fun c : U → Designation ↦ {u | (c u).threshold ≤ A u} := by
  ext X
  constructor
  · intro h
    choose c hc using h
    exact ⟨c, Set.ext fun u ↦ iff_of_eq (hc u)⟩
  · rintro ⟨c, rfl⟩ u
    exact ⟨c u, rfl⟩

theorem posSupport_subset (A : U → SignType) : posSupport A ⊆ (negSupport A)ᶜ := fun u hu hn ↦ by
  simp only [mem_posSupport, mem_negSupport] at hu hn; rw [hu] at hn; exact absurd hn (by decide)

theorem repairs_nonempty (A : U → SignType) : (repairs A).Nonempty :=
  repairs_eq_Icc A ▸ ⟨_, le_rfl, posSupport_subset A⟩

/-- A classical predicate is its own only repair. -/
theorem repairs_ofProp (R : Set U) [DecidablePred (· ∈ R)] :
    repairs (fun u ↦ ofProp (u ∈ R)) = {R} := by
  ext X
  simp only [mem_repairs, repairSet_ofProp, Set.mem_singleton_iff]
  exact ⟨fun h ↦ Set.ext fun u ↦ iff_of_eq (h u), fun h _ ↦ h ▸ rfl⟩

open Classical in
/-- The predicate true on `B`, undefined on the rest of `C` and false elsewhere. -/
noncomputable def ofIcc (B C : Set U) : U → SignType :=
  fun u ↦ if u ∈ B then 1 else if u ∈ C then 0 else -1

/-- Every interval of sets is the repairs of a predicate. -/
theorem repairs_ofIcc {B C : Set U} (h : B ⊆ C) : repairs (ofIcc B C) = Set.Icc B C := by
  have e₁ : posSupport (ofIcc B C) = B := by
    ext u
    by_cases hu : u ∈ B
    · simp [ofIcc, hu]
    · by_cases hc : u ∈ C <;> simp [ofIcc, hu, hc]
  have e₂ : (negSupport (ofIcc B C))ᶜ = C := by
    ext u
    by_cases hu : u ∈ B
    · simp [ofIcc, hu, h hu]
    · by_cases hc : u ∈ C <;> simp [ofIcc, hu, hc]
  rw [repairs_eq_Icc, e₁, e₂]

/-! ### Deployed quantifiers -/

variable {Q : Set U → Prop}

/-- The Peters-Kleene deployment `Q[A]` of a generalised quantifier on a trivalent predicate. -/
noncomputable def deployQuantifier (Q : Set U → Prop) (A : U → SignType) : SignType :=
  ofPart (pkReduce Q (repairs A))

/-- A deployed quantifier is the supervaluation over the repairs of its argument. -/
theorem deployQuantifier_eq_supervaluationOn (Q : Set U → Prop) (A : U → SignType) :
    deployQuantifier Q A = supervaluationOn (repairs A) Q :=
  ofPart_pkReduce Q (repairs_nonempty A)

/-- A deployed quantifier is the supervaluation over the readings of its instances, each at a
standard of its own. -/
theorem deployQuantifier_eq_supervaluationOn_standards (Q : Set U → Prop) (A : U → SignType) :
    deployQuantifier Q A =
      supervaluationOn Set.univ fun c : U → Designation ↦ Q {u | (c u).threshold ≤ A u} := by
  rw [deployQuantifier_eq_supervaluationOn, repairs_eq_range, ← Set.image_univ,
    supervaluationOn_image]
  rfl

/-- A monotone quantifier deployed on a predicate is settled by its K3 and LP readings. -/
theorem deployQuantifier_of_monotone (hQ : Monotone Q) (A : U → SignType) :
    deployQuantifier Q A =
      supervaluationOn Set.univ fun d : Designation ↦ Q {u | d.threshold ≤ A u} :=
  (deployQuantifier_eq_supervaluationOn_standards Q A).trans
    (supervaluationOn_pi_eq_const_of_monotone (Q := Q) A fun _ _ h ↦ hQ h)

/-- An antitone quantifier deployed on a predicate is settled by its K3 and LP readings. -/
theorem deployQuantifier_of_antitone (hQ : Antitone Q) (A : U → SignType) :
    deployQuantifier Q A =
      supervaluationOn Set.univ fun d : Designation ↦ Q {u | d.threshold ≤ A u} :=
  (deployQuantifier_eq_supervaluationOn_standards Q A).trans
    (supervaluationOn_pi_eq_const_of_antitone (Q := Q) A fun _ _ h ↦ hQ h)

/-- On a classical predicate, a deployed quantifier is the quantifier. -/
@[simp] theorem deployQuantifier_ofProp (Q : Set U → Prop) (R : Set U) [DecidablePred (· ∈ R)]
    [Decidable (Q R)] : deployQuantifier Q (fun u ↦ ofProp (u ∈ R)) = ofProp (Q R) := by
  simp [deployQuantifier, repairs_ofProp]

/-- Deploying `∀`, the quantifier true only of `Set.univ` (Definition 16 of [george-2014]), gives
the Strong Kleene universal, as George computes in §4.1. -/
theorem deployQuantifier_eq_forallStrong (A : U → SignType) :
    deployQuantifier (· = Set.univ) A = forallStrong A := by
  rw [deployQuantifier_eq_supervaluationOn, repairs_eq_Icc]
  refine eq_of_eq_one_iff_of_eq_neg_one_iff ?_ ?_
  · rw [supervaluationOn_eq_one_iff, forallStrong_eq_one_iff]
    refine ⟨fun h u ↦ ?_, fun h X hX ↦ Set.eq_univ_of_forall fun u ↦ hX.1 (mem_posSupport.2 (h u))⟩
    exact mem_posSupport.1 ((h _ ⟨le_rfl, posSupport_subset A⟩).symm ▸ Set.mem_univ u)
  · rw [supervaluationOn_eq_neg_one_iff, forallStrong_eq_neg_one_iff]
    refine ⟨fun ⟨_, h⟩ ↦ ?_, fun ⟨u, hu⟩ ↦ ⟨⟨_, le_rfl, posSupport_subset A⟩, fun X hX e ↦
      hX.2 (e ▸ Set.mem_univ u) (mem_negSupport.2 hu)⟩⟩
    obtain ⟨u, hu⟩ := (Set.ne_univ_iff_exists_notMem _).1 (h _ ⟨posSupport_subset A, le_rfl⟩)
    exact ⟨u, mem_negSupport.1 (not_not.1 hu)⟩

/-- Deploying `∃`, the quantifier true of the nonempty sets (Definition 17 of [george-2014]),
gives the Strong Kleene existential, by the computation George calls analogous in §4.1. -/
theorem deployQuantifier_eq_existsStrong (A : U → SignType) :
    deployQuantifier Set.Nonempty A = existsStrong A := by
  rw [deployQuantifier_eq_supervaluationOn, repairs_eq_Icc]
  refine eq_of_eq_one_iff_of_eq_neg_one_iff ?_ ?_
  · rw [supervaluationOn_eq_one_iff, existsStrong_eq_one_iff]
    refine ⟨fun h ↦ ?_, fun ⟨u, hu⟩ X hX ↦ ⟨u, hX.1 (mem_posSupport.2 hu)⟩⟩
    obtain ⟨u, hu⟩ := h _ ⟨le_rfl, posSupport_subset A⟩
    exact ⟨u, mem_posSupport.1 hu⟩
  · rw [supervaluationOn_eq_neg_one_iff, existsStrong_eq_neg_one_iff]
    refine ⟨fun ⟨_, h⟩ u ↦ ?_, fun h ↦ ⟨⟨_, le_rfl, posSupport_subset A⟩, fun X hX ⟨u, hu⟩ ↦
      hX.2 hu (mem_negSupport.2 (h u))⟩⟩
    by_contra hu
    exact h _ ⟨posSupport_subset A, le_rfl⟩ ⟨u, hu⟩

/-! ### Deployed determiners -/

/-- The Peters-Kleene deployment `D[B, A]` of a determiner on a trivalent restrictor `B` and nuclear
scope `A`, the restrictor first. -/
noncomputable def deployDeterminer (D : Set U → Set U → Prop) (B A : U → SignType) : SignType :=
  ofPart ((pkReduce D (repairs B)).bind (pkReduce · (repairs A)))

/-- If every repair of the restrictor makes the same quantifier of the determiner, the deployed
determiner is that quantifier deployed on the nuclear scope. -/
theorem deployDeterminer_of_forall {D : Set U → Set U → Prop} {B A : U → SignType}
    (h : ∀ R ∈ repairs B, D R = Q) : deployDeterminer D B A = deployQuantifier Q A := by
  rw [deployDeterminer, pkReduce_of_forall (repairs_nonempty B) h, Part.bind_some, deployQuantifier]

/-- Two repairs of the restrictor that the determiner tells apart make it undefined. -/
theorem deployDeterminer_eq_zero_of_ne {D : Set U → Set U → Prop} {B A : U → SignType}
    {R S : Set U} (hR : R ∈ repairs B) (hS : S ∈ repairs B) (h : D R ≠ D S) :
    deployDeterminer D B A = 0 := by
  simp [deployDeterminer, pkReduce_eq_none hR hS h, Part.bind_none]

/-- With a classical restrictor, a deployed determiner is the deployed quantifier it makes of the
restrictor. -/
@[simp] theorem deployDeterminer_ofProp_left (D : Set U → Set U → Prop) (R : Set U)
    [DecidablePred (· ∈ R)] (A : U → SignType) :
    deployDeterminer D (fun u ↦ ofProp (u ∈ R)) A = deployQuantifier (D R) A :=
  deployDeterminer_of_forall fun S hS ↦ by rw [repairs_ofProp, Set.mem_singleton_iff] at hS; rw [hS]

end Trivalent
