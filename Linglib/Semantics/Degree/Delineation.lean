module

public import Linglib.Logic.Trivalent.Basic

/-!
# Delineation semantics

In delineation semantics a gradable adjective has no degree argument. A delineation sends each
comparison class, a set of entities the adjective is evaluated against, to the adjective's
extension relative to it, and *a is taller than b* holds when some comparison class puts `a` in
the extension and leaves `b` out. Klein develops this analysis from Kamp's account of the
comparative. A measure function induces a delineation whose ordering is degree comparison, so the
threshold analysis embeds in this one.

## Main definitions

* `Degree.Delineation`: a delineation, applied to a comparison class as a function.
* `Degree.Delineation.Comparative`: Klein's comparative.
* `Degree.Delineation.IsMonotoneOn`: no comparison class in a set reverses a ranking another
  class in it makes.
* `Degree.Delineation.Outranks`, `Degree.Delineation.Nondistinct`: comparison and
  indistinguishability within a comparison class.
* `Degree.Delineation.ofMeasure`: the delineation a measure function induces.
* `Degree.Delineation.very`, `Degree.Delineation.fairly`: the modifiers *very* and *fairly*.

## Main statements

* `Degree.Delineation.IsMonotone.outranks_asymm`, `Degree.Delineation.Outranks.cotrans`: under
  monotonicity the ordering is a strict weak order.
* `Degree.Delineation.outranks_ofMeasure_iff`: under a measure-induced delineation the ordering is
  degree comparison.
* `Degree.Delineation.IsMonotone.not_isNonlinear`: a monotone delineation is never nonlinear, so no
  measure function induces a nonlinear one.

## References

* [klein-1980]
* [kamp-1975]
* [fine-1975]
* [bochnak-2015]
* [burnett-2017]
* [cobreros-etal-2012]
* [kennedy-2011]
* [van-rooij-2011a]
-/

@[expose] public section

namespace Degree

/-- A delineation sends each comparison class to the extension of a gradable adjective relative
to it. -/
@[ext]
structure Delineation (E : Type*) where
  /-- The extension relative to a comparison class. -/
  toFun : Set E → Set E

namespace Delineation

variable {E : Type*}

instance : CoeFun (Delineation E) fun _ ↦ Set E → Set E := ⟨toFun⟩

@[simp] theorem coe_mk (f : Set E → Set E) : ⇑(⟨f⟩ : Delineation E) = f := rfl

variable (d : Delineation E)

/-! ### The comparative -/

/-- Klein's comparative holds of `a` and `b` when some comparison class puts `a` in the extension
and leaves `b` out. -/
def Comparative (a b : E) : Prop :=
  ∃ C, a ∈ d C ∧ b ∉ d C

/-- A delineation is monotone on a set of comparison classes when no class in the set puts `b` in
the extension and leaves `a` out once another class in it has put `a` in and left `b` out. -/
def IsMonotoneOn (S : Set (Set E)) : Prop :=
  ∀ C₁ ∈ S, ∀ C₂ ∈ S, ∀ a b, a ∈ d C₁ → b ∉ d C₁ → b ∈ d C₂ → a ∈ d C₂

/-- A delineation is monotone when it is monotone on all comparison classes. -/
def IsMonotone : Prop := d.IsMonotoneOn Set.univ

/-! ### The Fine duality

Comparison classes are specification points: Klein's comparative is the existential dual of
Fine's supervaluation. -/

section Supervaluation

variable [∀ C (x : E), Decidable (x ∈ d C)] {a b : E} (S : Finset (Set E))

variable {d} in
theorem IsMonotoneOn.supervaluation_eq_true_of_comparative (hmono : d.IsMonotoneOn ↑S)
    (hdisc : ∃ C ∈ S, a ∈ d C ∧ b ∉ d C)
    (hb : SignType.supervaluation S (b ∈ d ·) = 1) :
    SignType.supervaluation S (a ∈ d ·) = 1 := by
  rw [SignType.supervaluation_eq_one_iff] at hb ⊢
  obtain ⟨C₀, hC₀, haC₀, hnotbC₀⟩ := hdisc
  exact fun C hC ↦ hmono C₀ hC₀ C hC a b haC₀ hnotbC₀ (hb C hC)

theorem supervaluation_ne_true_of_comparative (hdisc : ∃ C ∈ S, a ∈ d C ∧ b ∉ d C) :
    SignType.supervaluation S (b ∈ d ·) ≠ 1 := fun h ↦
  let ⟨C₀, hC₀, _, hnotb⟩ := hdisc
  hnotb ((SignType.supervaluation_eq_one_iff ..).mp h C₀ hC₀)

end Supervaluation

/-! ### The ordering within a comparison class -/

/-- Within the comparison class `C`, `u` outranks `v` when some subclass of `C` puts `u` in the
extension and leaves `v` out. -/
def Outranks (C : Set E) (u v : E) : Prop :=
  ∃ X ⊆ C, u ∈ d X ∧ v ∉ d X

theorem comparative_iff_outranks_univ {a b : E} : d.Comparative a b ↔ d.Outranks Set.univ a b :=
  ⟨fun ⟨C, h1, h2⟩ ↦ ⟨C, Set.subset_univ C, h1, h2⟩, fun ⟨C, _, h1, h2⟩ ↦ ⟨C, h1, h2⟩⟩

variable {d} {C : Set E} {u v w : E}

theorem IsMonotone.outranks_asymm (hmono : d.IsMonotone) :
    d.Outranks C u v → ¬ d.Outranks C v u := fun ⟨X₁, _, hu₁, hnv₁⟩ ⟨X₂, _, hv₂, hnu₂⟩ ↦
  hnu₂ (hmono X₁ (Set.mem_univ _) X₂ (Set.mem_univ _) u v hu₁ hnv₁ hv₂)

theorem IsMonotone.outranks_trans (hmono : d.IsMonotone) :
    d.Outranks C u v → d.Outranks C v w → d.Outranks C u w :=
  fun ⟨X₁, _, hu₁, hnv₁⟩ ⟨X₂, hX₂, hv₂, hnw₂⟩ ↦
    ⟨X₂, hX₂, hmono X₁ (Set.mem_univ _) X₂ (Set.mem_univ _) u v hu₁ hnv₁ hv₂, hnw₂⟩

theorem Outranks.cotrans (h : d.Outranks C u w) (v : E) :
    d.Outranks C u v ∨ d.Outranks C v w := by
  obtain ⟨X, hX, hu, hnw⟩ := h
  by_cases hv : v ∈ d X
  · exact .inr ⟨X, hX, hv, hnw⟩
  · exact .inl ⟨X, hX, hu, hv⟩

variable (d) in
/-- Two entities are nondistinct in `C` when no subclass of `C` containing both puts one in the
extension and leaves the other out. The relation is reflexive and symmetric, and transitive
only for linear adjectives. -/
def Nondistinct (C : Set E) (u v : E) : Prop :=
  ∀ X ⊆ C, u ∈ X → v ∈ X → (u ∈ d X ↔ v ∈ d X)

theorem Nondistinct.refl (C : Set E) (u : E) : d.Nondistinct C u u :=
  fun _ _ _ _ ↦ Iff.rfl

theorem Nondistinct.symm (h : d.Nondistinct C u v) : d.Nondistinct C v u :=
  fun X hX hv hu ↦ (h X hX hu hv).symm

theorem nondistinct_of_not_outranks (h₁ : ¬ d.Outranks C u v) (h₂ : ¬ d.Outranks C v u) :
    d.Nondistinct C u v := fun X hX _ _ ↦
  ⟨fun hu ↦ by_contra fun hv ↦ h₁ ⟨X, hX, hu, hv⟩,
    fun hv ↦ by_contra fun hu ↦ h₂ ⟨X, hX, hv, hu⟩⟩

/-! ### Linear and nonlinear adjectives -/

variable (d) in
/-- A delineation is linear when any two members of a comparison class are ordered one way or the
other or nondistinct, as for single-criterion adjectives such as *tall* and *heavy*. -/
def IsLinear : Prop :=
  ∀ C, ∀ u ∈ C, ∀ v ∈ C, u ≠ v → d.Outranks C u v ∨ d.Outranks C v u ∨ d.Nondistinct C u v

variable (d) in
/-- A delineation is nonlinear when its ordering ranks two entities each above the other, as when
different subclasses apply different criteria for *clever* or *nice*. -/
def IsNonlinear : Prop :=
  ∃ C u v, d.Outranks C u v ∧ d.Outranks C v u

theorem IsMonotone.not_isNonlinear (hmono : d.IsMonotone) : ¬ d.IsNonlinear :=
  fun ⟨_, _, _, h, h'⟩ ↦ hmono.outranks_asymm h h'

/-! ### The delineation of a measure

`ofMeasure` maps threshold semantics into delineation semantics, and `outranks_ofMeasure_iff`
says the map is faithful. -/

section Measure

variable {D : Type*} [LinearOrder D] (μ : E → D)

/-- The delineation a measure induces puts `x` in the extension relative to `C` when `x` measures
strictly more than some member of `C`. -/
def ofMeasure : Delineation E := ⟨fun C ↦ {x | ∃ y ∈ C, μ y < μ x}⟩

@[simp] theorem mem_ofMeasure {C : Set E} {x : E} : x ∈ ofMeasure μ C ↔ ∃ y ∈ C, μ y < μ x :=
  Iff.rfl

theorem isMonotone_ofMeasure : (ofMeasure μ).IsMonotone := by
  rintro C₁ - C₂ - a b ⟨y₁, hy₁, hlt_a⟩ hnotb ⟨y₂, hy₂, hlt_b⟩
  have hle : μ b ≤ μ y₁ := not_lt.mp fun h ↦ hnotb ⟨y₁, hy₁, h⟩
  exact ⟨y₂, hy₂, hlt_b.trans (hle.trans_lt hlt_a)⟩

theorem monotone_ofMeasure : Monotone (ofMeasure μ) :=
  fun _ _ hle _ ⟨y, hy, hlt⟩ ↦ ⟨y, hle hy, hlt⟩

theorem outranks_ofMeasure_iff {C : Set E} {a b : E} (ha : a ∈ C) (hb : b ∈ C) :
    (ofMeasure μ).Outranks C a b ↔ μ b < μ a := by
  refine ⟨fun ⟨_, _, ⟨y, hy, hlt⟩, hneg⟩ ↦ ?_, fun hlt ↦ ?_⟩
  · exact (not_lt.mp fun h ↦ hneg ⟨y, hy, h⟩).trans_lt hlt
  · refine ⟨{a, b}, Set.insert_subset ha (Set.singleton_subset_iff.2 hb),
      ⟨b, Set.mem_insert_of_mem _ rfl, hlt⟩, ?_⟩
    rintro ⟨y, hy | hy, hlt_y⟩ <;> subst hy
    · exact hlt.not_gt hlt_y
    · exact lt_irrefl _ hlt_y

theorem isLinear_ofMeasure : (ofMeasure μ).IsLinear := by
  intro C u hu v hv _
  rcases lt_trichotomy (μ u) (μ v) with hlt | heq | hgt
  · exact .inr (.inl ((outranks_ofMeasure_iff μ hv hu).2 hlt))
  · exact .inr (.inr fun X _ _ _ ↦ by simp [heq])
  · exact .inl ((outranks_ofMeasure_iff μ hu hv).2 hgt)

end Measure

/-! ### Degree modifiers as narrowings of the comparison class -/

variable (d) in
/-- Klein's *very A* holds of `x` relative to `C` when *A* holds of `x` relative to the members of
`C` that *A* holds of. -/
def very : Delineation E := ⟨fun C ↦ d (d C)⟩

variable (d) in
/-- Klein's *fairly A* holds of `x` relative to `C` when *A* holds of `x` relative to the members of
`C` that *very A* does not hold of. -/
def fairly : Delineation E := ⟨fun C ↦ d (C \ d.very C)⟩

theorem very_subset (hcc : ∀ C, d C ⊆ C) (C : Set E) : d.very C ⊆ d C :=
  hcc _

theorem fairly_disjoint_very (hcc : ∀ C, d C ⊆ C) (C : Set E) : Disjoint (d.fairly C) (d.very C) :=
  Set.disjoint_left.2 fun _ hf ↦ (hcc _ hf).2

/-! ### The equative -/

variable (d) in
/-- In the equative preorder `u ≤ v` holds when every comparison class whose extension contains `v`
also contains `u`, so `u ≤ v` says that *u is as A as v*. -/
abbrev preorder : Preorder E :=
  Preorder.lift fun u ↦ OrderDual.toDual {C | u ∈ d C}

theorem preorder_le_iff : (d.preorder).le u v ↔ ∀ C, v ∈ d C → u ∈ d C := Iff.rfl

/-! ### Faithfulness to a scalar relation

A delineation is sound for a scalar relation `R` when separation by a comparison class entails
`R`, which is Bochnak's second consistency constraint; it is complete when every pair related by
`R` is separated by some class, closer to Burnett's axioms. Both are classical: under the
tolerant semantics of Cobreros and colleagues, similar pairs would defeat strict separation. -/

section Faithfulness

variable (d) in
/-- A delineation is sound for a scalar relation `R` when every class that puts `x` in the
extension and leaves `y` out witnesses `R x y`. -/
def IsSoundFor (R : E → E → Prop) : Prop :=
  ∀ C x y, x ∈ d C → y ∉ d C → R x y

variable (d) in
/-- A delineation is complete for a scalar relation `R` when every pair related by `R` is
separated by some comparison class. -/
def IsCompleteFor (R : E → E → Prop) : Prop :=
  ∀ x y, R x y → d.Comparative x y

theorem comparative_iff_of_isSoundFor_of_isCompleteFor {R : E → E → Prop} (hs : d.IsSoundFor R)
    (hc : d.IsCompleteFor R) {x y : E} : d.Comparative x y ↔ R x y :=
  ⟨fun ⟨C, hpos, hneg⟩ ↦ hs C x y hpos hneg, hc x y⟩

variable {D : Type*} [LinearOrder D] (μ : E → D)

theorem isSoundFor_ofMeasure : (ofMeasure μ).IsSoundFor fun a b ↦ μ b < μ a :=
  fun C x y hpos hneg ↦ (outranks_ofMeasure_iff μ (Set.mem_univ x) (Set.mem_univ y)).1
    ⟨C, Set.subset_univ _, hpos, hneg⟩

theorem isCompleteFor_ofMeasure : (ofMeasure μ).IsCompleteFor fun a b ↦ μ b < μ a :=
  fun x y hR ↦ (comparative_iff_outranks_univ _).2
    ((outranks_ofMeasure_iff μ (Set.mem_univ x) (Set.mem_univ y)).2 hR)

theorem comparative_ofMeasure_iff {x y : E} : (ofMeasure μ).Comparative x y ↔ μ y < μ x :=
  comparative_iff_of_isSoundFor_of_isCompleteFor (isSoundFor_ofMeasure μ)
    (isCompleteFor_ofMeasure μ)

end Faithfulness

end Delineation

end Degree
