module

public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Function.Basic
public import Mathlib.Logic.Relation
public import Mathlib.Order.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Linglib.Core.Order.Antisymmetrization
public import Linglib.Semantics.MeasurementTheory.Invariance

/-!
# Aggregation rules

This file defines aggregation rules, which combine several rankings of the same objects into one.
A profile assigns each object a vector of values, one per individual, and an aggregation rule
assigns each profile a relation on the objects, read `x ⪰ y`. In social choice the individuals
are voters and the objects social states; for a multidimensional adjective the individuals are
its dimensions and the relation is its comparative.

The information a rule may use is fixed by invariance under a class of vectors of changes of
scale, one for each individual. On a single scale the changes of scale are the strictly increasing
maps of an ordinal scale, the positive affine maps of an interval scale and the similarities of a
ratio scale. A class applies such maps separately to each individual (non-comparability), one map
to every individual (full comparability), or affine maps with a common unit (unit
comparability). Arrow's conditions, the strong Pareto condition, Pareto indifference and anonymity
are predicates on rules.

A rule ranks vectors, `ofRel R`, when each output is the preimage, under the profile, of one
relation `R` on vectors of values. Every classical rule does, and on three or more objects a rule
with preorder outputs does exactly when it is independent and Pareto indifferent. `ofRel` carries
infima and suprema of relations on vectors to those of rules.

## Main definitions

* `Aggregation.Rule`: a relation on the objects for each profile of values.
* `Aggregation.ParetoIndifferent`: objects with the same vector of values are indifferent.
* `Aggregation.ofRel`: the rule that ranks objects by a relation on their vectors of values.
* `Aggregation.Arrovian`: Arrow's conditions, relative to a class of changes of scale.

## Main statements

* `Aggregation.paretoIndifferent_iff_forall_exists_eq_preimage`: Pareto indifference as ranking
  vectors.
* `Aggregation.independent_and_paretoIndifferent_iff_exists_ofRel`: welfarism, one ranking of
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

open Function MeasurementTheory

variable {ι α K : Type*}

/-- A profile assigns each object its vector of values, one per individual. -/
abbrev Profile (ι α K : Type*) := α → ι → K

/-- An aggregation rule assigns to each profile a relation on the objects, read `x ⪰ y`. -/
abbrev Rule (ι α K : Type*) := Profile ι α K → α → α → Prop

/-! ### Informational invariance

The information a rule may use is fixed by its `Invariant` classes: sets of vectors of changes of
scale, one for each individual, acting on a profile coordinatewise. -/

/-- A statement about the measure of object–individual pairs that is invariant on a scale is
invariant under its changes of scale applied to every individual alike. -/
theorem _root_.MeasurementTheory.Invariant.uncurry {β G : Type*} [SMul G K] {S : Set G}
    {φ : (α × ι → K) → β} (h : Invariant S φ) :
    Invariant (const ι '' S) fun v : Profile ι α K ↦ φ (Function.uncurry v) := by
  rintro _ ⟨u, hu, rfl⟩ v
  exact h u hu (Function.uncurry v)

/-- Applying one change of scale to every individual is a special case of applying one to each. -/
theorem const_image_subset_pi {G : Type*} {S : Set G} :
    const ι '' S ⊆ Set.univ.pi fun _ ↦ S := by
  rintro _ ⟨u, hu, rfl⟩ i -
  exact hu

section Classes

variable (ι K)

/-- A strictly increasing change of scale for each individual; invariance under them is ordinal
non-comparability. -/
def ordinal [LE K] : Set (ι → K ↪o K) := Set.univ

/-- One strictly increasing change of scale applied to every individual; invariance under these
is ordinal level comparability. -/
def ordinalLevel [LE K] : Set (ι → K ↪o K) := Set.range (const ι)

variable {ι K} in
theorem mem_ordinal [LE K] (f : ι → K ↪o K) : f ∈ ordinal ι K :=
  Set.mem_univ f

variable {ι K} in
theorem subset_ordinal [LE K] (S : Set (ι → K ↪o K)) : S ⊆ ordinal ι K :=
  Set.subset_univ S

variable [Semiring K] [PartialOrder K]

/-- A positive affine change of scale for each individual; invariance under them is cardinal
non-comparability. -/
def cardinal : Set (ι → K ↪o K) := Set.univ.pi fun _ ↦ positiveAffine

/-- Positive affine changes of scale with a common unit; invariance under them is cardinal unit
comparability. -/
def cardinalUnit : Set (ι → K ↪o K) :=
  {f | ∃ a : K, 0 < a ∧ ∃ b : ι → K, ∀ i t, f i t = a * t + b i}

/-- One positive affine change of scale applied to every individual; invariance under these is
cardinal full comparability. -/
def cardinalFull : Set (ι → K ↪o K) := const ι '' positiveAffine

/-- A similarity for each individual; invariance under them is ratio-scale non-comparability. -/
def ratio : Set (ι → K ↪o K) := Set.univ.pi fun _ ↦ similarity

/-- One similarity applied to every individual; invariance under these is ratio-scale full
comparability. -/
def ratioFull : Set (ι → K ↪o K) := const ι '' similarity

variable {ι K}

@[simp]
theorem mem_ratio {f : ι → K ↪o K} : f ∈ ratio ι K ↔ ∀ i, f i ∈ similarity :=
  Set.mem_univ_pi

variable (ι K)

theorem cardinalFull_subset_cardinalUnit : cardinalFull ι K ⊆ cardinalUnit ι K := by
  rintro _ ⟨u, ⟨a, ha, b, hu⟩, rfl⟩
  exact ⟨a, ha, fun _ ↦ b, fun _ ↦ hu⟩

theorem cardinalUnit_subset_cardinal : cardinalUnit ι K ⊆ cardinal ι K :=
  fun _ ⟨a, ha, b, hf⟩ i _ ↦ ⟨a, ha, b i, hf i⟩

theorem ratioFull_subset_cardinalFull : ratioFull ι K ⊆ cardinalFull ι K :=
  Set.image_mono similarity_subset_positiveAffine

theorem ratio_subset_cardinal : ratio ι K ⊆ cardinal ι K :=
  Set.pi_mono fun _ _ ↦ similarity_subset_positiveAffine

theorem ratioFull_subset_ratio : ratioFull ι K ⊆ ratio ι K :=
  const_image_subset_pi

theorem cardinalFull_subset_ordinalLevel : cardinalFull ι K ⊆ ordinalLevel ι K :=
  Set.image_subset_range _ _

end Classes

/-- A function of profiles that depends only on each individual's ordering of the objects is
invariant under ordinal non-comparability. -/
theorem invariant_ordinal_of_factorsThrough {β : Type*} [LE K] {a : Profile ι α K → β}
    (h : FactorsThrough a fun v i ↦ (v · i) ⁻¹'o (· ≤ ·)) : Invariant (ordinal ι K) a :=
  fun f _ v ↦ h (funext fun i ↦ funext₂ fun x y ↦
    propext (show f i (v x i) ≤ f i (v y i) ↔ v x i ≤ v y i from (f i).map_rel_iff))

/-! ### Conditions on rules -/

section Conditions

variable (a : Rule ι α K)

/-- Pareto indifference says that objects with the same vector of values are indifferent. -/
def ParetoIndifferent : Prop := ∀ v x y, v x = v y → AntisymmRel (a v) x y

/-- Independence of irrelevant alternatives says that the verdict on a pair depends only on the
vectors of that pair. -/
def Independent : Prop := ∀ v w x y, v x = w x → v y = w y → (a v x y ↔ a w x y)

/-- Every output is transitive. -/
def TransitiveValued : Prop := ∀ v, IsTrans α (a v)

/-- Every output is complete. -/
def CompleteValued : Prop := ∀ v, Std.Total (a v)

/-- Every output is a weak ordering, a complete preorder. -/
@[mk_iff]
structure WeakOrderValued : Prop where
  /-- Every output is transitive. -/
  transitive : TransitiveValued a
  /-- Every output is complete. -/
  complete : CompleteValued a

/-- Every output is a quasi-ordering, a preorder. -/
def QuasiOrderValued : Prop := ∀ v, IsPreorder α (a v)

/-- Anonymity says that permuting the individuals leaves the output unchanged. -/
def Anonymous : Prop := ∀ (σ : Equiv.Perm ι) v, a (fun x ↦ v x ∘ σ) = a v

variable {a}

theorem WeakOrderValued.quasiOrderValued (h : WeakOrderValued a) : QuasiOrderValued a :=
  fun v ↦
    haveI := h.transitive v
    haveI := h.complete v
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

variable {a}

theorem StrongPareto.weakPareto [Nonempty ι] (h : StrongPareto a) : WeakPareto a :=
  fun v x y hlt ↦ (h v x y).2 hlt.lt

end Conditions

/-- A rule meets Arrow's conditions relative to a class `T` of changes of scale when it is
invariant under `T`, outputs weak orderings, satisfies weak Pareto and independence, and has no
dictator. Arrow's own conditions take `T` to be `ordinal`. -/
@[mk_iff]
structure Arrovian [Preorder K] (T : Set (ι → K ↪o K)) (a : Rule ι α K) : Prop where
  /-- The rule is invariant under `T`. -/
  invariant : Invariant T a
  /-- Every output is a weak ordering. -/
  weakOrderValued : WeakOrderValued a
  /-- The rule satisfies weak Pareto. -/
  weakPareto : WeakPareto a
  /-- The rule is independent of irrelevant alternatives. -/
  independent : Independent a
  /-- No individual is a dictator. -/
  nonDictatorial : NonDictatorial a

/-! ### Rules that rank vectors -/

/-- The rule that ranks objects by a relation `R` on their vectors of values. -/
def ofRel (R : (ι → K) → (ι → K) → Prop) : Rule ι α K := fun v ↦ v ⁻¹'o R

section OfRel

variable {R : (ι → K) → (ι → K) → Prop} {v : Profile ι α K} {x y : α}

@[simp]
theorem ofRel_apply : ofRel R v x y ↔ R (v x) (v y) :=
  Iff.rfl

instance [DecidableRel R] (v : Profile ι α K) : DecidableRel (ofRel R v) :=
  Order.Preimage.decidable v R

theorem ofRel_iInf {κ : Sort*} (R : κ → (ι → K) → (ι → K) → Prop) :
    (ofRel (⨅ j, R j) : Rule ι α K) = ⨅ j, ofRel (R j) :=
  funext fun _ ↦ funext₂ fun _ _ ↦ by simp [iInf_apply]

theorem ofRel_iSup {κ : Sort*} (R : κ → (ι → K) → (ι → K) → Prop) :
    (ofRel (⨆ j, R j) : Rule ι α K) = ⨆ j, ofRel (R j) :=
  funext fun _ ↦ funext₂ fun _ _ ↦ by simp [iSup_apply]

theorem independent_ofRel (R : (ι → K) → (ι → K) → Prop) : Independent (ofRel R : Rule ι α K) :=
  fun _ _ _ _ hx hy ↦ by simp only [ofRel_apply, hx, hy]

theorem paretoIndifferent_ofRel (hR : ∀ p, R p p) : ParetoIndifferent (ofRel R : Rule ι α K) :=
  fun v x y h ↦ ⟨show R (v x) (v y) from h ▸ hR _, show R (v y) (v x) from h ▸ hR _⟩

theorem quasiOrderValued_ofRel [IsPreorder (ι → K) R] : QuasiOrderValued (ofRel R : Rule ι α K) :=
  fun v ↦ inferInstanceAs (IsPreorder α (v ⁻¹'o R))

theorem weakOrderValued_ofRel [IsTrans (ι → K) R] [Std.Total R] :
    WeakOrderValued (ofRel R : Rule ι α K) :=
  ⟨fun v ↦ inferInstanceAs (IsTrans α (v ⁻¹'o R)), fun v ↦ inferInstanceAs (Std.Total (v ⁻¹'o R))⟩

/-- A rule that ranks vectors is anonymous when permuting the coordinates leaves the ranking of
vectors unchanged. -/
theorem anonymous_ofRel (h : ∀ σ : Equiv.Perm ι, (· ∘ σ) ⁻¹'o R = R) :
    Anonymous (ofRel R : Rule ι α K) :=
  fun σ v ↦ congrArg (v ⁻¹'o ·) (h σ)

/-- A rule that ranks vectors is invariant under a class of changes of scale when each
of them leaves the ranking of vectors unchanged. -/
theorem invariant_ofRel [LE K] {T : Set (ι → K ↪o K)}
    (h : ∀ f ∈ T, (fun p : ι → K ↦ f • p) ⁻¹'o R = R) : Invariant T (ofRel R : Rule ι α K) :=
  fun f hf v ↦ congrArg (v ⁻¹'o ·) (h f hf)

/-- On two or more objects, a rule that ranks vectors satisfies weak Pareto exactly when its
ranking of vectors puts a vector strictly above every vector it dominates in each coordinate. -/
theorem weakPareto_ofRel_iff [Preorder K] [Nontrivial α] :
    WeakPareto (ofRel R : Rule ι α K) ↔ ∀ p q, StrongLT q p → R p q ∧ ¬ R q p := by
  refine ⟨fun h p q hpq ↦ ?_, fun h v x y hxy ↦ h _ _ hxy⟩
  obtain ⟨x, y, hxy⟩ := exists_pair_ne α
  classical
  have := h (fun z ↦ if z = x then p else q) x y (by simpa [hxy.symm] using hpq)
  simpa [AsymmRel, hxy.symm] using this

end OfRel

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
indifferent exactly when it ranks objects by one relation on their vectors of values. -/
theorem independent_and_paretoIndifferent_iff_exists_ofRel (h₃ : 3 ≤ ENat.card α) :
    Independent a ∧ ParetoIndifferent a ↔ ∃ R : (ι → K) → (ι → K) → Prop, a = ofRel R := by
  classical
  have : Nontrivial α := (ENat.one_lt_card_iff_nontrivial α).1 (lt_of_lt_of_le (by simp) h₃)
  obtain ⟨x₀, y₀, h₀⟩ := exists_pair_ne α
  refine ⟨fun ⟨hI, hP⟩ ↦ ?_, fun ⟨R, hR⟩ ↦ ?_⟩
  · let pr (p q : ι → K) : Profile ι α K := update (fun _ ↦ q) x₀ p
    have hpr₁ (p q) : pr p q x₀ = p := update_self _ _ _
    have hpr₂ (p q) : pr p q y₀ = q := update_of_ne h₀.symm _ _
    refine ⟨fun p q ↦ a (pr p q) x₀ y₀, funext fun v ↦ funext₂ fun x y ↦ propext ?_⟩
    rcases eq_or_ne x y with rfl | hxy
    · have := hQ v
      exact iff_of_true (refl_of (a v) x) (hP _ _ _ ((hpr₁ _ _).trans (hpr₂ _ _).symm)).1
    · exact iff_of_eq_of_ne hI hP hQ h₃ hxy h₀ (hpr₁ _ _).symm (hpr₂ _ _).symm
  · subst hR
    refine ⟨independent_ofRel R, paretoIndifferent_ofRel fun p ↦ ?_⟩
    have := hQ fun _ ↦ p
    exact refl_of (ofRel R (fun _ : α ↦ p)) x₀

end Welfarism

end Aggregation
