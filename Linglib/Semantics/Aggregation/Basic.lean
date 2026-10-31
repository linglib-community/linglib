module

public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Function.Basic
public import Mathlib.Logic.Relation
public import Mathlib.Order.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Linglib.Core.Order.Antisymmetrization

/-!
# Aggregation rules

This file defines aggregation rules, which combine several rankings of the same objects into one.
A profile assigns each object a vector of values, one per individual, and an aggregation rule
assigns each profile a relation on the objects, read `x ⪰ y`. In social choice the individuals
are voters and the objects social states; for a multidimensional adjective the individuals are
its dimensions and the relation is its comparative.

The information a rule may use is fixed by invariance under a class of transformation vectors.
On a single scale the changes of scale are the strictly increasing maps of an ordinal scale, the
positive affine maps of an interval scale and the similarities of a ratio scale. A class of
vectors applies such maps separately to each individual (non-comparability), one map to every
individual (full comparability), or affine maps with a common unit (unit comparability). Arrow's
conditions, the strong Pareto condition, Pareto indifference and anonymity are predicates on rules.

A rule ranks vectors when each output is the preimage, under the profile, of one relation on
vectors of values. Every classical rule does, and on three or more objects a rule with preorder
outputs does exactly when it is independent and Pareto indifferent.

## Main definitions

* `Aggregation.Rule`: a relation on the objects for each profile of values.
* `Aggregation.Invariant`: invariance under a class of transformation vectors.
* `Aggregation.ParetoIndifferent`: objects with the same vector of values are indifferent.

## Main statements

* `Aggregation.paretoIndifferent_iff_forall_exists_eq_preimage`: Pareto indifference as ranking
  vectors.
* `Aggregation.independent_and_paretoIndifferent_iff_exists_preimage`: welfarism, one ranking of
  vectors for every profile.

## Implementation notes

* A rule is total on profiles, so Arrow's unrestricted-domain condition is built in; a domain
  restriction is a hypothesis of the statement that needs it.
* Outputs are bare relations, since majority rule is not transitive. `AsymmRel` is the strict
  part of an output and `AntisymmRel` its indifference part.

## TODO

* `Preorder.ofCriteria`, the ordering of worlds by an ordering source, is the Pareto rule with
  propositions as the individuals; the harmony of Harmonic Grammar is the utilitarian rule with
  constraints as the individuals. State both as aggregation rules.

## References

* [dambrosio-hedden-2024]
* [arrow-1950]
* [sen-1970]
* [blackorby-donaldson-weymark-1990]
-/

@[expose] public section

namespace Aggregation

open Function

variable {ι α K : Type*}

/-- A profile assigns each object its vector of values, one per individual. -/
abbrev Profile (ι α K : Type*) := α → ι → K

/-- An aggregation rule assigns to each profile a relation on the objects, read `x ⪰ y`. -/
abbrev Rule (ι α K : Type*) := Profile ι α K → α → α → Prop

/-- A vector of transformations, one per individual, applied to a profile. -/
def Profile.transform (f : ι → K → K) (v : Profile ι α K) : Profile ι α K :=
  fun x i ↦ f i (v x i)

/-! ### Informational invariance -/

/-- Invariance of a function of profiles, such as a rule or a statement about values, under a class
of transformation vectors. -/
def Invariant {β : Type*} (T : Set (ι → K → K)) (a : Profile ι α K → β) : Prop :=
  ∀ f ∈ T, ∀ v, a (v.transform f) = a v

theorem Invariant.mono {β : Type*} {S T : Set (ι → K → K)} (h : S ⊆ T) {a : Profile ι α K → β}
    (ha : Invariant T a) : Invariant S a :=
  fun f hf ↦ ha f (h hf)

/-- Vectors of strictly increasing transformations, one for each individual; invariance under
them is ordinal non-comparability. -/
def ordinal [Preorder K] : Set (ι → K → K) := Set.univ.pi fun _ ↦ {u | StrictMono u}

/-- One strictly increasing transformation applied to every individual; invariance under these
is ordinal level comparability. -/
def ordinalLevel [Preorder K] : Set (ι → K → K) := const ι '' {u | StrictMono u}

@[simp]
theorem mem_ordinal [Preorder K] {f : ι → K → K} : f ∈ ordinal ↔ ∀ i, StrictMono (f i) :=
  Set.mem_univ_pi

/-- Applying one transformation to every individual is a special case of applying one to each. -/
theorem const_image_subset_pi {S : Set (K → K)} : const ι '' S ⊆ Set.univ.pi fun _ ↦ S := by
  rintro _ ⟨u, hu, rfl⟩ i -
  exact hu

theorem ordinalLevel_subset_ordinal [Preorder K] : ordinalLevel ⊆ (ordinal : Set (ι → K → K)) :=
  const_image_subset_pi

section Cardinal

variable [Semiring K] [PartialOrder K]

/-- The positive affine transformations `t ↦ a * t + b` with `0 < a`, the changes of scale of
an interval scale. -/
def positiveAffine : Set (K → K) := {u | ∃ a : K, 0 < a ∧ ∃ b : K, ∀ t, u t = a * t + b}

/-- The similarity transformations `t ↦ a * t` with `0 < a`, the changes of scale of a ratio
scale. -/
def similarity : Set (K → K) := {u | ∃ a : K, 0 < a ∧ ∀ t, u t = a * t}

/-- Vectors of positive affine transformations, one for each individual; invariance under them
is cardinal non-comparability. -/
def cardinal : Set (ι → K → K) := Set.univ.pi fun _ ↦ positiveAffine

/-- Positive affine transformation vectors with a common unit; invariance under them is cardinal
unit comparability. -/
def cardinalUnit : Set (ι → K → K) :=
  {f | ∃ a : K, 0 < a ∧ ∃ b : ι → K, ∀ i t, f i t = a * t + b i}

/-- One positive affine transformation applied to every individual; invariance under these is
cardinal full comparability. -/
def cardinalFull : Set (ι → K → K) := const ι '' positiveAffine

/-- Vectors of similarity transformations, one for each individual; invariance under them is
ratio-scale non-comparability. -/
def ratio : Set (ι → K → K) := Set.univ.pi fun _ ↦ similarity

/-- One similarity transformation applied to every individual; invariance under these is
ratio-scale full comparability. -/
def ratioFull : Set (ι → K → K) := const ι '' similarity

@[simp]
theorem mem_ratio {f : ι → K → K} : f ∈ ratio ↔ ∀ i, f i ∈ similarity :=
  Set.mem_univ_pi

theorem similarity_subset_positiveAffine : similarity ⊆ (positiveAffine : Set (K → K)) :=
  fun _ ⟨a, ha, hu⟩ ↦ ⟨a, ha, 0, fun t ↦ by rw [hu, add_zero]⟩

theorem cardinalFull_subset_cardinalUnit : cardinalFull ⊆ (cardinalUnit : Set (ι → K → K)) := by
  rintro _ ⟨u, ⟨a, ha, b, hu⟩, rfl⟩
  exact ⟨a, ha, fun _ ↦ b, fun _ ↦ hu⟩

theorem cardinalUnit_subset_cardinal : cardinalUnit ⊆ (cardinal : Set (ι → K → K)) :=
  fun _ ⟨a, ha, b, hf⟩ i _ ↦ ⟨a, ha, b i, hf i⟩

theorem ratioFull_subset_cardinalFull : ratioFull ⊆ (cardinalFull : Set (ι → K → K)) :=
  Set.image_mono similarity_subset_positiveAffine

theorem ratio_subset_cardinal : ratio ⊆ (cardinal : Set (ι → K → K)) :=
  Set.pi_mono fun _ _ ↦ similarity_subset_positiveAffine

theorem ratioFull_subset_ratio : ratioFull ⊆ (ratio : Set (ι → K → K)) :=
  const_image_subset_pi

variable [IsStrictOrderedRing K]

theorem positiveAffine_subset_strictMono : positiveAffine ⊆ {u : K → K | StrictMono u} :=
  fun _ ⟨a, ha, b, hu⟩ s t hst ↦ by
    simp only [hu]
    exact add_lt_add_left (mul_lt_mul_of_pos_left hst ha) _

theorem cardinal_subset_ordinal : cardinal ⊆ (ordinal : Set (ι → K → K)) :=
  Set.pi_mono fun _ _ ↦ positiveAffine_subset_strictMono

theorem cardinalFull_subset_ordinalLevel : cardinalFull ⊆ (ordinalLevel : Set (ι → K → K)) :=
  Set.image_mono positiveAffine_subset_strictMono

theorem cardinalUnit_subset_ordinal : cardinalUnit ⊆ (ordinal : Set (ι → K → K)) :=
  cardinalUnit_subset_cardinal.trans cardinal_subset_ordinal

theorem ratio_subset_ordinal : ratio ⊆ (ordinal : Set (ι → K → K)) :=
  ratio_subset_cardinal.trans cardinal_subset_ordinal

end Cardinal

/-! ### Conditions on rules -/

section Conditions

variable (a : Rule ι α K)

/-- Pareto indifference says that objects with the same vector of values are indifferent. -/
def ParetoIndifferent : Prop := ∀ v x y, v x = v y → AntisymmRel (a v) x y

/-- Independence of irrelevant alternatives says that the verdict on a pair depends only on the
vectors of that pair. -/
def Independent : Prop := ∀ v w x y, v x = w x → v y = w y → (a v x y ↔ a w x y)

/-- Every output is transitive. -/
def Transitive : Prop := ∀ v, IsTrans α (a v)

/-- Every output is complete. -/
def Complete : Prop := ∀ v, Std.Total (a v)

/-- Every output is a weak ordering, a complete preorder. -/
def WeakOrderValued : Prop := Transitive a ∧ Complete a

/-- Every output is a quasi-ordering, a preorder. -/
def QuasiOrderValued : Prop := ∀ v, IsPreorder α (a v)

/-- Anonymity says that permuting the individuals leaves the output unchanged. -/
def Anonymous : Prop := ∀ (σ : Equiv.Perm ι) v, a (fun x ↦ v x ∘ σ) = a v

variable {a}

theorem WeakOrderValued.quasiOrderValued (h : WeakOrderValued a) : QuasiOrderValued a :=
  fun v ↦
    haveI := h.1 v
    haveI := h.2 v
    IsPreorder.mk

variable (a) [Preorder K]

/-- Weak Pareto says that an object every individual ranks strictly above another is strictly
preferred. -/
def WeakPareto : Prop := ∀ v x y, StrongLT (v y) (v x) → AsymmRel (a v) x y

/-- Strong Pareto says that an object every individual ranks weakly above another is weakly
preferred, and strictly preferred if some individual moreover ranks it strictly above. -/
def StrongPareto : Prop := ∀ v x y, (v y ≤ v x → a v x y) ∧ (v y < v x → AsymmRel (a v) x y)

/-- Individual `i` is a dictator when its strict rankings are the strict overall rankings. -/
def IsDictator (i : ι) : Prop := ∀ v x y, v y i < v x i → AsymmRel (a v) x y

/-- No individual is a dictator. -/
def NonDictatorial : Prop := ∀ i, ¬ IsDictator a i

end Conditions

/-! ### Rules that rank vectors -/

section Preimage

variable {R : (ι → K) → (ι → K) → Prop}

/-- A rule that ranks objects by a relation on their vectors of values is independent. -/
theorem independent_preimage (R : (ι → K) → (ι → K) → Prop) :
    Independent (fun v ↦ v ⁻¹'o R : Rule ι α K) :=
  fun _ _ _ _ hx hy ↦ by simp only [Order.Preimage, hx, hy]

theorem paretoIndifferent_preimage (hR : ∀ p, R p p) :
    ParetoIndifferent (fun v ↦ v ⁻¹'o R : Rule ι α K) :=
  fun v x y h ↦ ⟨show R (v x) (v y) from h ▸ hR _, show R (v y) (v x) from h ▸ hR _⟩

theorem quasiOrderValued_preimage [IsPreorder (ι → K) R] :
    QuasiOrderValued (fun v ↦ v ⁻¹'o R : Rule ι α K) :=
  fun _ ↦ inferInstance

theorem weakOrderValued_preimage [IsTrans (ι → K) R] [Std.Total R] :
    WeakOrderValued (fun v ↦ v ⁻¹'o R : Rule ι α K) :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ inferInstance⟩

/-- A rule that ranks vectors is anonymous when permuting the coordinates leaves the ranking of
vectors unchanged. -/
theorem anonymous_preimage (h : ∀ σ : Equiv.Perm ι, (· ∘ σ) ⁻¹'o R = R) :
    Anonymous (fun v ↦ v ⁻¹'o R : Rule ι α K) :=
  fun σ v ↦ congrArg (v ⁻¹'o ·) (h σ)

/-- A rule that ranks vectors is invariant under a class of transformation vectors when each
of them, applied coordinatewise, leaves the ranking of vectors unchanged. -/
theorem invariant_preimage {T : Set (ι → K → K)} (h : ∀ f ∈ T, Pi.map f ⁻¹'o R = R) :
    Invariant T (fun v ↦ v ⁻¹'o R : Rule ι α K) :=
  fun f hf v ↦ congrArg (v ⁻¹'o ·) (h f hf)

end Preimage

/-! ### Welfarism -/

section Welfarism

variable {a : Rule ι α K}

/-- When every output is a preorder, Pareto indifference holds exactly when each output ranks the
objects by a ranking of their vectors of values ([dambrosio-hedden-2024] fn. 16, after
[blackorby-donaldson-weymark-1990]). -/
theorem paretoIndifferent_iff_forall_exists_eq_preimage (h : QuasiOrderValued a) :
    ParetoIndifferent a ↔ ∀ v, ∃ R : (ι → K) → (ι → K) → Prop, a v = v ⁻¹'o R := by
  refine ⟨fun hP v ↦ ⟨Relation.Map (a v) v v, funext₂ fun x y ↦
    propext ⟨fun hxy ↦ ⟨x, y, hxy, rfl, rfl⟩, ?_⟩⟩, fun h' v x y hxy ↦ ?_⟩
  · have := h v
    rintro ⟨x', y', h', hx, hy⟩
    exact _root_.trans (_root_.trans (hP v x x' hx.symm).1 h') (hP v y' y hy).1
  · obtain ⟨R, hR⟩ := h' v
    have := h v
    have e : ∀ z w, v z = v w → a v z w := fun z w hzw ↦ by
      simpa only [hR, Order.Preimage, hzw] using refl_of (a v) z
    exact ⟨e x y hxy, e y x hxy.symm⟩

variable (hI : Independent a) (hP : ParetoIndifferent a) (hQ : QuasiOrderValued a)
include hI hP hQ

private theorem iff_of_ne_right {v w : Profile ι α K} {x y z : α} (hxz : x ≠ z)
    (hx : v x = w x) (hy : v y = w z) : a v x y ↔ a w x z := by
  classical
  set u := update v z (v y)
  have hux : u x = v x := update_of_ne hxz _ _
  have huy : u y = v y := by by_cases hyz : y = z <;> simp [u, hyz]
  have huz : u z = v y := update_self _ _ _
  have := hQ u
  have hyz := hP u y z (huy.trans huz.symm)
  calc a v x y ↔ a u x y := hI v u x y hux.symm huy.symm
    _ ↔ a u x z := ⟨fun h ↦ _root_.trans h hyz.1, fun h ↦ _root_.trans h hyz.2⟩
    _ ↔ a w x z := hI u w x z (hux.trans hx) (huz.trans hy)

private theorem iff_of_ne_left {v w : Profile ι α K} {x y z : α} (hzy : z ≠ y)
    (hx : v x = w z) (hy : v y = w y) : a v x y ↔ a w z y := by
  classical
  set u := update v z (v x)
  have huy : u y = v y := update_of_ne hzy.symm _ _
  have hux : u x = v x := by by_cases hxz : x = z <;> simp [u, hxz]
  have huz : u z = v x := update_self _ _ _
  have := hQ u
  have hxz := hP u x z (hux.trans huz.symm)
  calc a v x y ↔ a u x y := hI v u x y hux.symm huy.symm
    _ ↔ a u z y := ⟨fun h ↦ _root_.trans hxz.2 h, fun h ↦ _root_.trans hxz.1 h⟩
    _ ↔ a w z y := hI u w z y (huz.trans hx) (huy.trans hy)

/-- Neutrality: two pairs of distinct objects with the same vectors of values get the same
verdict, at any two profiles. -/
theorem iff_of_eq_of_ne (h₃ : 3 ≤ ENat.card α) {v w : Profile ι α K} {x y x' y' : α}
    (hxy : x ≠ y) (hxy' : x' ≠ y') (hx : v x = w x') (hy : v y = w y') :
    a v x y ↔ a w x' y' := by
  classical
  -- a profile through which to route the pair `x, y`
  have mid : ∀ p q : α, p ≠ q → ∃ u : Profile ι α K, u p = v x ∧ u q = v y :=
    fun p q hpq ↦ ⟨update (fun _ ↦ v y) p (v x), update_self _ _ _, update_of_ne hpq.symm _ _⟩
  by_cases hx'y : x' ≠ y
  · obtain ⟨u, hu₁, hu₂⟩ := mid x' y hx'y
    exact (iff_of_ne_left hI hP hQ hx'y hu₁.symm hu₂.symm).trans
      (iff_of_ne_right hI hP hQ hxy' (hu₁.trans hx) (hu₂.trans hy))
  rw [not_ne_iff] at hx'y
  subst hx'y
  by_cases hy'x : y' ≠ x
  · obtain ⟨u, hu₁, hu₂⟩ := mid x y' hy'x.symm
    exact (iff_of_ne_right hI hP hQ hy'x.symm hu₁.symm hu₂.symm).trans
      (iff_of_ne_left hI hP hQ hxy' (hu₁.trans hx) (hu₂.trans hy))
  rw [not_ne_iff] at hy'x
  subst hy'x
  -- swapping the pair goes through a third object
  obtain ⟨z, hzx, hzy⟩ := ENat.exists_ne_ne_of_three_le h₃ y' x'
  obtain ⟨u, hu₁, hu₂⟩ := mid y' z hzx.symm
  obtain ⟨u', hu₁', hu₂'⟩ := mid x' z hzy.symm
  exact (iff_of_ne_right hI hP hQ hzx.symm hu₁.symm hu₂.symm).trans <|
    (iff_of_ne_left hI hP hQ hzy.symm (hu₁.trans hu₁'.symm) (hu₂.trans hu₂'.symm)).trans
      (iff_of_ne_right hI hP hQ hxy' (hu₁'.trans hx) (hu₂'.trans hy))

omit hI hP in
/-- Welfarism: on three or more objects, a rule with preorder outputs is independent and Pareto
indifferent exactly when one relation on vectors of values ranks the objects at every profile. -/
theorem independent_and_paretoIndifferent_iff_exists_preimage (h₃ : 3 ≤ ENat.card α) :
    Independent a ∧ ParetoIndifferent a ↔
      ∃ R : (ι → K) → (ι → K) → Prop, ∀ v, a v = v ⁻¹'o R := by
  classical
  have : Nontrivial α := (ENat.one_lt_card_iff_nontrivial α).1 (lt_of_lt_of_le (by simp) h₃)
  obtain ⟨x₀, y₀, h₀⟩ := exists_pair_ne α
  refine ⟨fun ⟨hI, hP⟩ ↦ ?_, fun ⟨R, hR⟩ ↦ ?_⟩
  · let pr (p q : ι → K) : Profile ι α K := update (fun _ ↦ q) x₀ p
    have hpr₁ (p q) : pr p q x₀ = p := update_self _ _ _
    have hpr₂ (p q) : pr p q y₀ = q := update_of_ne h₀.symm _ _
    refine ⟨fun p q ↦ a (pr p q) x₀ y₀, fun v ↦ funext₂ fun x y ↦ propext ?_⟩
    rcases eq_or_ne x y with rfl | hxy
    · have := hQ v
      exact iff_of_true (refl_of (a v) x) (hP _ _ _ ((hpr₁ _ _).trans (hpr₂ _ _).symm)).1
    · exact iff_of_eq_of_ne hI hP hQ h₃ hxy h₀ (hpr₁ _ _).symm (hpr₂ _ _).symm
  · obtain rfl : a = fun v ↦ v ⁻¹'o R := funext hR
    refine ⟨independent_preimage R, paretoIndifferent_preimage fun p ↦ ?_⟩
    have := hQ fun _ ↦ p
    exact refl_of ((fun _ : α ↦ p) ⁻¹'o R) x₀

end Welfarism

end Aggregation
