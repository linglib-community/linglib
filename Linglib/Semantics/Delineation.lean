module

public import Linglib.Logic.Trivalent.Connectives
public import Mathlib.Order.Antisymmetrization
public import Mathlib.Order.UpperLower.Closure
public import Mathlib.Order.UpperLower.CompleteLattice

/-!
# Delineation semantics

In delineation semantics a gradable adjective has no degree argument. A delineation sends each
comparison class, a set of entities the adjective is evaluated against, to disjoint positive and
negative extensions relative to it; what lies in neither is the extension gap, the borderline
cases. *a is taller than b* holds when some comparison class puts `a` in the positive extension
and `b` in the negative one, Klein's development of Kamp's account of the comparative.

Klein constrains delineations in two ways. The consistency constraint forbids a class from
reversing a separation another class makes, and the second constraint requires a class with
distinguishable members to have members in both extensions. A measure `m` and a standard `σ`, an
upper set of degrees for each class, give the delineation whose positive extension relative to
`C` is `m ⁻¹' σ C`, and the delineation of a measure alone takes for standard the degrees above
some member of the class.

Conversely a delineation has degrees of its own. The degree of an entity on a set of classes is
the set of those classes that put it in the positive extension, ordered by inclusion, and on
those classes the delineation is the delineation of its degrees, which are the coarsest measure
that gives it. A delineation without gaps meets the consistency constraint exactly when its
degrees form a chain, so exactly when it arises from a measure into a linear order and a
standard, with a measure that represents the comparative.

## Main definitions

* `Delineation`: positive and negative extensions relative to each comparison class.
* `Delineation.Comparative`, `Delineation.Outranks`: Klein's comparative, and the ordering it
  induces within a comparison class.
* `Delineation.IsMonotoneOn`, `Delineation.IsNontrivialOn`: Klein's two constraints.
* `Delineation.Nondistinct`, `Delineation.Equivalent`, `Delineation.IsComplete`: sameness of
  value across the subclasses of a class, and across more determinate delineations.
* `Delineation.ofStandard`: the delineation of a measure and a class-relative standard.
* `Delineation.degree`: the classes of a set that put an entity in the positive extension.
* `Delineation.ofMeasure`: the delineation of a measure, positive above some member of the class.
* `Delineation.very`, `Delineation.fairly`: degree modifiers as narrowings of the class.

## Main results

* `Delineation.IsMonotoneOn.isStrictOrder_outranks`: under the consistency constraint the
  ordering within a class is a strict partial order.
* `Delineation.equivalent_or_outranks_or_outranks`: under the second constraint any two members
  of a complete class are equivalent or ranked.
* `Delineation.ofStandard_degree`, `Delineation.exists_forall_eq_ofStandard_iff`: on a set of
  classes a delineation is the delineation of its degrees, and a measure gives it at some standard
  exactly when the degrees are monotone in the measure.
* `Delineation.isMonotoneOn_ofExtension_iff_isChain`,
  `Delineation.IsGapless.isMonotoneOn_iff_isChain_degree`: a gapless delineation meets the
  consistency constraint on a set of classes exactly when their positive extensions form a chain,
  and exactly when the degrees on them do.
* `Delineation.IsGapless.outranks_iff_degree_ssubset`: under the consistency constraint the
  ordering within a class is the strict ordering of the degrees.
* `Delineation.IsGapless.isMonotoneOn_iff_exists_ofStandard`,
  `Delineation.IsGapless.isMonotone_iff_exists_ofStandard`: a gapless delineation meets the
  consistency constraint exactly when it is the delineation of a measure into a linear order and
  a standard, with a measure that represents the comparative.
* `Delineation.mem_ofStandard_of_forall_le`, `Delineation.ofStandard_subset_ofMeasure`: when a
  class has members on both sides of a standard, its greatest members meet the standard and
  whatever meets the standard measures above some member.
* `Delineation.outranks_ofMeasure_iff`: under the delineation of a measure, the ordering within a
  class is degree comparison.

## Implementation notes

The comparison class of Klein's context is the parameter `C` of `Outranks`, and his constraints
are imposed on the subclasses of `C`, `𝒫 C`. A delineation is not required to leave entities
outside a class undecided, Klein's restriction of a valuation to its class; the results that need
it assume it, and `ofStandard` and `ofMeasure` classify every entity, so that the consistency
constraint, which compares classes that need not both contain the two entities, holds of them.
Klein's equivalence quantifies over the contexts at least as determinate as the given one, which
are here the delineations of an admissible family `𝒟` extending the given one.

On a gapless delineation the consistency constraint is the condition that defines a biorder in
[doignon-ducamp-falmagne-1984], imposed on the relation between entities and classes, *u is in
the positive extension relative to X*. [ducamp-falmagne-1969] study such relations as
bi-quasi-series, which generalize Guttman scales, and they are also called Ferrers relations. The
degree of an entity is the set of classes related to it, the ordering of entities by inclusion of
degrees is the left trace of [bouyssou-marchant-2011], and that a relation is a biorder exactly
when this ordering, or the like ordering of the classes, is connected is a proposition of
[doignon-ducamp-falmagne-1984]. The condition is stated here with mathlib's `IsChain`, on the
degrees and on the positive extensions. For finite sets a biorder is represented by two real
scales, with `u` related to `X` when the scale value of `u` exceeds that of `X`; here the
threshold of a class is an upper set of degrees, which needs no finiteness.

A standard is an upper set of degrees, as in `Semantics/Degree/PositiveStandard.lean`, and the
class-relative standard `σ : Set E → UpperSet D` is Klein's shape. A standard an adjective fixes
whatever the class is a constant `σ`, and a standard fixed from the measure on the class, as
Kennedy's standard-fixing function is, is a `σ` that depends on `C` through the restriction of
the measure to it.

## References

* [klein-1980]
* [kamp-1975]
* [fine-1975]
* [ducamp-falmagne-1969]
* [doignon-ducamp-falmagne-1984]
* [bouyssou-marchant-2011]
* [bochnak-2015]
* [burnett-2017]
* [cobreros-etal-2012]
* [kennedy-2007]
* [kennedy-2011]
* [van-rooij-2011a]
-/

@[expose] public section

/-- A delineation sends each comparison class to a positive and a negative extension of a
gradable adjective relative to it, which are disjoint; what lies in neither is in the extension
gap. -/
@[ext]
structure Delineation (E : Type*) where
  /-- The positive extension relative to a comparison class. -/
  pos : Set E → Set E
  /-- The negative extension relative to a comparison class. -/
  neg : Set E → Set E
  /-- Nothing is in both extensions. -/
  disjoint_pos_neg (C : Set E) : Disjoint (pos C) (neg C)

namespace Delineation

variable {E : Type*}

instance : CoeFun (Delineation E) fun _ ↦ Set E → Set E := ⟨pos⟩

/-- `d ≤ d'` when `d'` is at least as determinate as `d` ([klein-1980] (31)): it keeps every
value `d` assigns, and may settle what `d` leaves in a gap. -/
instance : PartialOrder (Delineation E) :=
  PartialOrder.lift (fun d ↦ (d.pos, d.neg)) fun _ _ h ↦
    Delineation.ext (congrArg Prod.fst h) (congrArg Prod.snd h)

theorem le_def {d d' : Delineation E} : d ≤ d' ↔ ∀ C, d C ⊆ d' C ∧ d.neg C ⊆ d'.neg C :=
  show d.pos ≤ d'.pos ∧ d.neg ≤ d'.neg ↔ _ from
    ⟨fun h C ↦ ⟨h.1 C, h.2 C⟩, fun h ↦ ⟨fun C ↦ (h C).1, fun C ↦ (h C).2⟩⟩

variable (d : Delineation E) {C : Set E} {x : E}

theorem notMem_neg_of_mem (h : x ∈ d C) : x ∉ d.neg C :=
  Set.disjoint_left.1 (d.disjoint_pos_neg C) h

/-! ### Delineations without gaps -/

/-- A delineation is gapless when every entity is in the positive or the negative extension of
every class. -/
def IsGapless : Prop := ∀ C, d.neg C = (d C)ᶜ

/-- The gapless delineation with the positive extensions `f`. -/
def ofExtension (f : Set E → Set E) : Delineation E :=
  ⟨f, fun C ↦ (f C)ᶜ, fun _ ↦ disjoint_compl_right⟩

@[simp] theorem pos_ofExtension (f : Set E → Set E) : (ofExtension f).pos = f := rfl

@[simp] theorem neg_ofExtension (f : Set E → Set E) (C : Set E) :
    (ofExtension f).neg C = (f C)ᶜ := rfl

theorem isGapless_ofExtension (f : Set E → Set E) : (ofExtension f).IsGapless := fun _ ↦ rfl

variable {d}

theorem IsGapless.eq_ofExtension (hd : d.IsGapless) : d = ofExtension d.pos :=
  Delineation.ext rfl (funext hd)

theorem IsGapless.mem_neg_iff (hd : d.IsGapless) : x ∈ d.neg C ↔ x ∉ d C := by
  rw [hd C, Set.mem_compl_iff]

/-- A gapless delineation is maximally determinate: whatever is at least as determinate is it. -/
theorem IsGapless.eq_of_le {d' : Delineation E} (hd : d.IsGapless) (h : d ≤ d') : d' = d := by
  rw [le_def] at h
  refine Delineation.ext (funext fun C ↦ Set.Subset.antisymm (fun x hx ↦ ?_) (h C).1)
    (funext fun C ↦ Set.Subset.antisymm (fun x hx ↦ ?_) (h C).2)
  · by_contra hx'
    exact d'.notMem_neg_of_mem hx ((h C).2 (hd.mem_neg_iff.2 hx'))
  · by_contra hx'
    exact d'.notMem_neg_of_mem ((h C).1 (not_not.1 (mt hd.mem_neg_iff.2 hx'))) hx

variable (d)

/-! ### The comparative -/

/-- Klein's comparative ((29)) holds of `a` and `b` when some comparison class puts `a` in the
positive extension and `b` in the negative one. -/
def Comparative (a b : E) : Prop :=
  ∃ C, a ∈ d C ∧ b ∈ d.neg C

/-- Within the comparison class `C`, `u` outranks `v` when some subclass of `C` puts `u` in the
positive extension and `v` in the negative one. -/
def Outranks (C : Set E) (u v : E) : Prop :=
  ∃ X ⊆ C, u ∈ d X ∧ v ∈ d.neg X

theorem comparative_iff_outranks_univ {a b : E} : d.Comparative a b ↔ d.Outranks Set.univ a b :=
  ⟨fun ⟨C, h1, h2⟩ ↦ ⟨C, Set.subset_univ C, h1, h2⟩, fun ⟨C, _, h1, h2⟩ ↦ ⟨C, h1, h2⟩⟩

/-! ### Klein's constraints -/

/-- A delineation is monotone on a set of comparison classes, Klein's consistency constraint
((37)), when once a class in the set puts `a` in the positive and `b` in the negative extension,
no class in the set puts `b` in the positive extension without `a`, or `a` in the negative
extension without `b`. -/
def IsMonotoneOn (S : Set (Set E)) : Prop :=
  ∀ C₁ ∈ S, ∀ C₂ ∈ S, ∀ a b, a ∈ d C₁ → b ∈ d.neg C₁ →
    (b ∈ d C₂ → a ∈ d C₂) ∧ (a ∈ d.neg C₂ → b ∈ d.neg C₂)

/-- A delineation is monotone when it is monotone on all comparison classes. -/
def IsMonotone : Prop := d.IsMonotoneOn Set.univ

/-- Two entities are nondistinct in `C` ((30)) when every subclass of `C` containing both gives
them the same value: both positive, both negative, or both in the gap. -/
def Nondistinct (C : Set E) (u v : E) : Prop :=
  ∀ X ⊆ C, u ∈ X → v ∈ X → (u ∈ d X ↔ v ∈ d X) ∧ (u ∈ d.neg X ↔ v ∈ d.neg X)

/-- A delineation is nontrivial on `C`, Klein's condition (36), when every subclass of `C` with two
members that are not nondistinct in `C` has a member in its positive and a member in its negative
extension. -/
def IsNontrivialOn (C : Set E) : Prop :=
  ∀ X ⊆ C, (∃ u ∈ X, ∃ v ∈ X, ¬ d.Nondistinct C u v) →
    (∃ w ∈ X, w ∈ d X) ∧ ∃ w ∈ X, w ∈ d.neg X

variable {d}

theorem IsMonotoneOn.mono {S T : Set (Set E)} (h : d.IsMonotoneOn S) (hTS : T ⊆ S) :
    d.IsMonotoneOn T :=
  fun C₁ h₁ C₂ h₂ ↦ h C₁ (hTS h₁) C₂ (hTS h₂)

/-- On a gapless delineation the consistency constraint is its positive half. -/
theorem isMonotoneOn_ofExtension_iff {f : Set E → Set E} {S : Set (Set E)} :
    (ofExtension f).IsMonotoneOn S ↔
      ∀ C₁ ∈ S, ∀ C₂ ∈ S, ∀ a b, a ∈ f C₁ → b ∉ f C₁ → b ∈ f C₂ → a ∈ f C₂ := by
  simp only [IsMonotoneOn, pos_ofExtension, neg_ofExtension, Set.mem_compl_iff]
  exact ⟨fun h C₁ h₁ C₂ h₂ a b ha hb ↦ (h C₁ h₁ C₂ h₂ a b ha hb).1,
    fun h C₁ h₁ C₂ h₂ a b ha hb ↦ ⟨h C₁ h₁ C₂ h₂ a b ha hb, mt (h C₁ h₁ C₂ h₂ a b ha hb)⟩⟩

/-- A gapless delineation meets the consistency constraint on a set of classes exactly when their
positive extensions form a chain. -/
theorem isMonotoneOn_ofExtension_iff_isChain {f : Set E → Set E} {S : Set (Set E)} :
    (ofExtension f).IsMonotoneOn S ↔ IsChain (· ⊆ ·) (f '' S) := by
  rw [isMonotoneOn_ofExtension_iff]
  refine ⟨?_, fun hc C₁ h₁ C₂ h₂ a b ha hb hb' ↦ ?_⟩
  · rintro h _ ⟨C₁, h₁, rfl⟩ _ ⟨C₂, h₂, rfl⟩ -
    by_contra hn
    obtain ⟨hn₁, hn₂⟩ := not_or.1 hn
    obtain ⟨a, ha, ha'⟩ := Set.not_subset.1 hn₁
    obtain ⟨b, hb, hb'⟩ := Set.not_subset.1 hn₂
    exact ha' (h C₁ h₁ C₂ h₂ a b ha hb' hb)
  · rcases hc.total (Set.mem_image_of_mem f h₁) (Set.mem_image_of_mem f h₂) with h | h
    exacts [h ha, absurd (h hb') hb]

theorem Nondistinct.refl (C : Set E) (u : E) : d.Nondistinct C u u :=
  fun _ _ _ _ ↦ ⟨Iff.rfl, Iff.rfl⟩

theorem Nondistinct.symm {u v : E} (h : d.Nondistinct C u v) : d.Nondistinct C v u :=
  fun X hX hv hu ↦ ⟨(h X hX hu hv).1.symm, (h X hX hu hv).2.symm⟩

/-! ### The ordering within a comparison class -/

variable {u v w : E}

theorem Outranks.irrefl : ¬ d.Outranks C u u :=
  fun ⟨_, _, hp, hn⟩ ↦ d.notMem_neg_of_mem hp hn

theorem IsMonotoneOn.outranks_asymm (hm : d.IsMonotoneOn (𝒫 C)) :
    d.Outranks C u v → ¬ d.Outranks C v u := fun ⟨X₁, h₁, hu₁, hv₁⟩ ⟨X₂, h₂, hv₂, hu₂⟩ ↦
  d.notMem_neg_of_mem ((hm X₁ h₁ X₂ h₂ u v hu₁ hv₁).1 hv₂) hu₂

theorem IsMonotoneOn.outranks_trans (hm : d.IsMonotoneOn (𝒫 C)) :
    d.Outranks C u v → d.Outranks C v w → d.Outranks C u w :=
  fun ⟨X₁, h₁, hu₁, hv₁⟩ ⟨X₂, h₂, hv₂, hw₂⟩ ↦ ⟨X₂, h₂, (hm X₁ h₁ X₂ h₂ u v hu₁ hv₁).1 hv₂, hw₂⟩

/-- Under the consistency constraint the ordering within a class is a strict partial order. Klein
derives this from both of his constraints (p. 23); the consistency constraint suffices. -/
theorem IsMonotoneOn.isStrictOrder_outranks (hm : d.IsMonotoneOn (𝒫 C)) :
    IsStrictOrder E (d.Outranks C) where
  irrefl _ := Outranks.irrefl
  trans _ _ _ := hm.outranks_trans

/-- Under Klein's condition (36), two members of `C` are nondistinct or ranked one way or the
other. -/
theorem IsNontrivialOn.nondistinct_or_outranks_or_outranks (hs : d.IsNontrivialOn C) (hu : u ∈ C)
    (hv : v ∈ C) : d.Nondistinct C u v ∨ d.Outranks C u v ∨ d.Outranks C v u := by
  by_cases h : d.Nondistinct C u v
  · exact .inl h
  have hX : ({u, v} : Set E) ⊆ C := Set.insert_subset hu (Set.singleton_subset_iff.2 hv)
  obtain ⟨⟨a, ha, hap⟩, b, hb, hbn⟩ :=
    hs _ hX ⟨u, Set.mem_insert u _, v, Set.mem_insert_of_mem u rfl, h⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact absurd hbn (d.notMem_neg_of_mem hap)
  · exact .inr (.inl ⟨_, hX, hap, hbn⟩)
  · exact .inr (.inr ⟨_, hX, hap, hbn⟩)
  · exact absurd hbn (d.notMem_neg_of_mem hap)

/-! ### Equivalence and completeness -/

variable (d) in
/-- Two entities are equivalent in `C` relative to a family `𝒟` of admissible delineations
((33)), *exactly as A as* each other, when every delineation of `𝒟` at least as determinate as
`d` leaves them nondistinct. -/
def Equivalent (𝒟 : Set (Delineation E)) (C : Set E) (u v : E) : Prop :=
  ∀ d' ∈ 𝒟, d ≤ d' → d'.Nondistinct C u v

variable (d) in
/-- A delineation is complete at `C` ((39)) when the members of `C` it leaves nondistinct are
equivalent. -/
def IsComplete (𝒟 : Set (Delineation E)) (C : Set E) : Prop :=
  ∀ u ∈ C, ∀ v ∈ C, d.Nondistinct C u v → d.Equivalent 𝒟 C u v

/-- An adjective interpreted by the family `𝒟` of delineations is linear when each of them is
complete at every comparison class, as single-criterion adjectives such as *tall* are. -/
def IsLinear (𝒟 : Set (Delineation E)) : Prop := ∀ d ∈ 𝒟, ∀ C, d.IsComplete 𝒟 C

/-- At a class where the delineation is complete and meets Klein's condition (36), any two
members are equivalent or ranked one way or the other: the ordering is connected up to
equivalence, and with the consistency constraint it is linear ([klein-1980], p. 25). -/
theorem equivalent_or_outranks_or_outranks {𝒟 : Set (Delineation E)} (hc : d.IsComplete 𝒟 C)
    (hs : d.IsNontrivialOn C) (hu : u ∈ C) (hv : v ∈ C) :
    d.Equivalent 𝒟 C u v ∨ d.Outranks C u v ∨ d.Outranks C v u :=
  (hs.nondistinct_or_outranks_or_outranks hu hv).imp_left (hc u hu v hv)

/-- A gapless delineation is complete: nothing is more determinate than it. -/
theorem IsGapless.isComplete (hd : d.IsGapless) (𝒟 : Set (Delineation E)) (C : Set E) :
    d.IsComplete 𝒟 C := fun _ _ _ _ h d' _ hle ↦ by
  rw [hd.eq_of_le hle]
  exact h

theorem isLinear_of_forall_isGapless {𝒟 : Set (Delineation E)} (h : ∀ d ∈ 𝒟, d.IsGapless) :
    IsLinear 𝒟 :=
  fun d hd C ↦ (h d hd).isComplete 𝒟 C

/-- On a gapless delineation two entities that neither outranks are nondistinct. -/
theorem IsGapless.nondistinct_of_not_outranks (hd : d.IsGapless) (h₁ : ¬ d.Outranks C u v)
    (h₂ : ¬ d.Outranks C v u) : d.Nondistinct C u v := fun X hX _ _ ↦ by
  have hp : u ∈ d X ↔ v ∈ d X :=
    ⟨fun hu ↦ by_contra fun hv ↦ h₁ ⟨X, hX, hu, hd.mem_neg_iff.2 hv⟩,
      fun hv ↦ by_contra fun hu ↦ h₂ ⟨X, hX, hv, hd.mem_neg_iff.2 hu⟩⟩
  exact ⟨hp, by rw [hd.mem_neg_iff, hd.mem_neg_iff, hp]⟩

/-- On a gapless delineation the ordering is cotransitive. -/
theorem IsGapless.outranks_cotrans (hd : d.IsGapless) (h : d.Outranks C u w) (v : E) :
    d.Outranks C u v ∨ d.Outranks C v w := by
  obtain ⟨X, hX, hu, hw⟩ := h
  by_cases hv : v ∈ d X
  · exact .inr ⟨X, hX, hv, hw⟩
  · exact .inl ⟨X, hX, hu, hd.mem_neg_iff.2 hv⟩

/-- On a gapless delineation under the consistency constraint the ordering is a strict weak order,
the order a degree scale would give. -/
theorem IsGapless.isStrictWeakOrder_outranks (hd : d.IsGapless) (hm : d.IsMonotoneOn (𝒫 C)) :
    IsStrictWeakOrder E (d.Outranks C) where
  irrefl _ := Outranks.irrefl
  trans _ _ _ := hm.outranks_trans
  incomp_trans _ b _ := fun ⟨hab, hba⟩ ⟨hbc, hcb⟩ ↦
    ⟨fun hac ↦ (hd.outranks_cotrans hac b).elim hab hbc,
      fun hca ↦ (hd.outranks_cotrans hca b).elim hcb hba⟩

/-! ### The Fine duality

Comparison classes are specification points: Klein's comparative is the existential dual of
Fine's supervaluation. -/

section Supervaluation

variable [∀ C (x : E), Decidable (x ∈ d C)] {a b : E} (S : Finset (Set E))

theorem IsMonotoneOn.supervaluation_eq_true_of_comparative (hmono : d.IsMonotoneOn ↑S)
    (hdisc : ∃ C ∈ S, a ∈ d C ∧ b ∈ d.neg C)
    (hb : Trivalent.supervaluation S (b ∈ d ·) = .true) :
    Trivalent.supervaluation S (a ∈ d ·) = .true := by
  rw [Trivalent.supervaluation_eq_true_iff] at hb ⊢
  obtain ⟨C₀, hC₀, haC₀, hbC₀⟩ := hdisc
  exact fun C hC ↦ (hmono C₀ hC₀ C hC a b haC₀ hbC₀).1 (hb C hC)

variable (d) in
theorem supervaluation_ne_true_of_comparative (hdisc : ∃ C ∈ S, a ∈ d C ∧ b ∈ d.neg C) :
    Trivalent.supervaluation S (b ∈ d ·) ≠ .true := fun h ↦
  let ⟨C₀, hC₀, _, hb⟩ := hdisc
  d.notMem_neg_of_mem ((Trivalent.supervaluation_eq_true_iff ..).mp h C₀ hC₀) hb

end Supervaluation

/-! ### The delineation of a measure and a standard

A standard is an upper set of degrees, and a class-relative standard `σ` assigns one to each
comparison class. `ofStandard m σ` puts in the positive extension relative to `C` what the measure
`m` places in `σ C`. -/

section Standard

variable {D : Type*} [Preorder D] (m : E → D) (σ : Set E → UpperSet D)

/-- The delineation of a measure and a class-relative standard is gapless and puts `x` in the
positive extension relative to `C` when the degree of `x` is in the standard of `C`. -/
def ofStandard : Delineation E := ofExtension fun C ↦ m ⁻¹' σ C

@[simp] theorem mem_ofStandard : x ∈ ofStandard m σ C ↔ m x ∈ σ C := Iff.rfl

@[simp] theorem mem_neg_ofStandard : x ∈ (ofStandard m σ).neg C ↔ m x ∉ σ C := Iff.rfl

theorem isGapless_ofStandard : (ofStandard m σ).IsGapless := isGapless_ofExtension _

/-- A weaker standard has the larger positive extension. -/
theorem antitone_ofStandard : Antitone fun σ ↦ (ofStandard m σ).pos :=
  fun _ _ h C _ hx ↦ h C hx

variable {m σ}

/-- When some member of the class meets the standard, so does whatever measures at least as much
as every member. -/
theorem mem_ofStandard_of_forall_le (h : (C ∩ ofStandard m σ C).Nonempty)
    (hx : ∀ y ∈ C, m y ≤ m x) : x ∈ ofStandard m σ C :=
  let ⟨y, hy, hyσ⟩ := h
  (σ C).upper (hx y hy) hyσ

/-- When some member of the class falls short of the standard, so does whatever measures at most
as much as every member. -/
theorem mem_neg_ofStandard_of_forall_le (h : (C ∩ (ofStandard m σ).neg C).Nonempty)
    (hx : ∀ y ∈ C, m x ≤ m y) : x ∈ (ofStandard m σ).neg C :=
  let ⟨y, hy, hyσ⟩ := h
  fun hxσ ↦ hyσ ((σ C).upper (hx y hy) hxσ)

/-- The delineation of a measure into a linear order and a standard meets Klein's consistency
constraint. -/
theorem isMonotone_ofStandard {D : Type*} [LinearOrder D] (m : E → D) (σ : Set E → UpperSet D) :
    (ofStandard m σ).IsMonotone := by
  rw [IsMonotone, ofStandard, isMonotoneOn_ofExtension_iff]
  exact fun C₁ _ C₂ _ a b ha hb hb' ↦
    (σ C₂).upper (le_of_not_ge fun h ↦ hb ((σ C₁).upper h ha)) hb'

end Standard

/-! ### The degrees of a delineation

The degree of an entity on a set `S` of comparison classes is the set of classes of `S` that put
it in the positive extension, and degrees are ordered by inclusion. Each class of `S` then holds
of exactly the entities whose degree contains it, so every delineation is, on `S`, the delineation
of its own degrees. On a gapless delineation the consistency constraint says that the degrees form
a chain: of two entities, one is positive wherever the other is. -/

section Degree

variable (d) (S : Set (Set E)) {a b : E} {X : Set E}

/-- The degree of `u` on a set `S` of comparison classes is the set of classes of `S` that put
`u` in the positive extension. -/
def degree (u : E) : Set (Set E) := {X ∈ S | u ∈ d X}

variable {d S}

@[simp] theorem mem_degree : X ∈ d.degree S a ↔ X ∈ S ∧ a ∈ d X := Iff.rfl

theorem degree_subset_degree_iff :
    d.degree S a ⊆ d.degree S b ↔ ∀ X ∈ S, a ∈ d X → b ∈ d X :=
  ⟨fun h _ hX ha ↦ (h ⟨hX, ha⟩).2, fun h _ hX ↦ ⟨hX.1, h _ hX.1 hX.2⟩⟩

/-- Some class of `S` puts `a` and not `b` in the positive extension exactly when the degree of
`a` is not below the degree of `b`. -/
theorem not_degree_subset_degree_iff :
    ¬ d.degree S a ⊆ d.degree S b ↔ ∃ X ∈ S, a ∈ d X ∧ b ∉ d X := by
  simp [degree_subset_degree_iff]

variable (d) in
/-- On the classes of `S`, a delineation is the delineation of its degrees, the standard of a
class being the degrees that contain it. -/
theorem ofStandard_degree (hX : X ∈ S) :
    ofStandard (d.degree S) (fun X ↦ .Ici {X}) X = d X :=
  Set.ext fun _ ↦ by simp [hX]

/-- A gapless delineation is the delineation of its degrees. -/
theorem IsGapless.eq_ofStandard_degree (hd : d.IsGapless) :
    d = ofStandard (d.degree Set.univ) fun X ↦ .Ici {X} := by
  rw [hd.eq_ofExtension, ofStandard]
  exact congrArg ofExtension (funext fun X ↦ (d.ofStandard_degree (Set.mem_univ X)).symm)

variable (d S) in
/-- A measure gives the positive extensions of the classes of `S` at some standard exactly when
the degrees are monotone in it, so the degrees are the coarsest such measure. -/
theorem exists_forall_eq_ofStandard_iff {D : Type*} [Preorder D] (m : E → D) :
    (∃ σ : Set E → UpperSet D, ∀ X ∈ S, d X = ofStandard m σ X) ↔
      ∀ ⦃a b⦄, m a ≤ m b → d.degree S a ⊆ d.degree S b := by
  refine ⟨fun ⟨σ, h⟩ a b hab ↦ degree_subset_degree_iff.2 fun X hX ha ↦ ?_, fun h ↦
    ⟨fun X ↦ upperClosure (m '' d X), fun X hX ↦ Set.ext fun x ↦ ?_⟩⟩
  · rw [h X hX] at ha ⊢
    exact (σ X).upper hab ha
  · simp only [mem_ofStandard, mem_upperClosure, Set.exists_mem_image]
    exact ⟨fun hx ↦ ⟨x, hx, le_rfl⟩, fun ⟨a, ha, hax⟩ ↦ (h hax ⟨hX, ha⟩).2⟩

/-- A gapless delineation meets the consistency constraint on `S` exactly when its degrees on `S`
form a chain. -/
theorem IsGapless.isMonotoneOn_iff_isChain_degree (hd : d.IsGapless) :
    d.IsMonotoneOn S ↔ IsChain (· ⊆ ·) (Set.range (d.degree S)) := by
  rw [hd.eq_ofExtension, isMonotoneOn_ofExtension_iff, ← hd.eq_ofExtension]
  refine ⟨?_, fun hc C₁ h₁ C₂ h₂ a b ha hb hb' ↦ ?_⟩
  · rintro h _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ -
    by_contra hn
    obtain ⟨hn₁, hn₂⟩ := not_or.1 hn
    obtain ⟨X₁, h₁, ha, hb⟩ := not_degree_subset_degree_iff.1 hn₁
    obtain ⟨X₂, h₂, hb', ha'⟩ := not_degree_subset_degree_iff.1 hn₂
    exact ha' (h X₁ h₁ X₂ h₂ a b ha hb hb')
  · rcases hc.total (Set.mem_range_self a) (Set.mem_range_self b) with h | h
    exacts [absurd (h ⟨h₁, ha⟩).2 hb, (h ⟨h₂, hb'⟩).2]

/-- Where the degrees form a chain, some class of `S` puts `a` and not `b` in the positive
extension exactly when the degree of `a` is strictly above the degree of `b`. -/
theorem exists_mem_notMem_iff_degree_ssubset (hc : IsChain (· ⊆ ·) (Set.range (d.degree S))) :
    (∃ X ∈ S, a ∈ d X ∧ b ∉ d X) ↔ d.degree S b ⊂ d.degree S a := by
  rw [← not_degree_subset_degree_iff, Set.ssubset_def]
  exact ⟨fun h ↦ ⟨(hc.total (Set.mem_range_self a) (Set.mem_range_self b)).resolve_left h, h⟩,
    And.right⟩

/-- On a gapless delineation under the consistency constraint, the ordering within a class is
the strict ordering of the degrees on its subclasses. -/
theorem IsGapless.outranks_iff_degree_ssubset (hd : d.IsGapless) (hm : d.IsMonotoneOn (𝒫 C)) :
    d.Outranks C a b ↔ d.degree (𝒫 C) b ⊂ d.degree (𝒫 C) a := by
  rw [← exists_mem_notMem_iff_degree_ssubset (hd.isMonotoneOn_iff_isChain_degree.1 hm)]
  exact exists_congr fun X ↦ and_congr_right fun _ ↦ and_congr_right fun _ ↦ hd.mem_neg_iff

end Degree

/-- A gapless delineation meets the consistency constraint on a set `S` of classes exactly when
some measure into a linear order and some standard give its positive extension relative to each
class of `S`, and the measure can be taken to order two entities as the classes of `S` that
separate them do. -/
theorem IsGapless.isMonotoneOn_iff_exists_ofStandard.{u} {E : Type u} {d : Delineation E}
    (hd : d.IsGapless) (S : Set (Set E)) :
    d.IsMonotoneOn S ↔ ∃ (D : Type u) (_ : LinearOrder D) (m : E → D) (σ : Set E → UpperSet D),
      (∀ X ∈ S, d X = ofStandard m σ X) ∧
        ∀ a b, (∃ X ∈ S, a ∈ d X ∧ b ∈ d.neg X) ↔ m b < m a := by
  classical
  refine ⟨fun hm ↦ ?_, ?_⟩
  · have hc := hd.isMonotoneOn_iff_isChain_degree.1 hm
    let _ : LinearOrder (Set.range (d.degree S)) :=
      { (inferInstance : PartialOrder (Set.range (d.degree S))) with
        le_total := fun p q ↦ hc.total p.2 q.2
        toDecidableLE := Classical.decRel _ }
    refine ⟨Set.range (d.degree S), inferInstance, Set.rangeFactorization (d.degree S),
      fun X ↦ ⟨{p | X ∈ p.1}, fun _ _ hpq hp ↦ hpq hp⟩, fun X hX ↦ Set.ext fun x ↦ ?_,
      fun a b ↦ ?_⟩
    · exact ⟨fun hx ↦ ⟨hX, hx⟩, And.right⟩
    · simp only [hd.mem_neg_iff, exists_mem_notMem_iff_degree_ssubset hc]
      exact Iff.rfl
  · rintro ⟨D, _, m, σ, h, -⟩
    have hmono := (d.exists_forall_eq_ofStandard_iff S m).1 ⟨σ, h⟩
    refine hd.isMonotoneOn_iff_isChain_degree.2 ?_
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ -
    exact (le_total (m a) (m b)).imp (hmono ·) (hmono ·)

/-- A gapless delineation meets the consistency constraint exactly when it is the delineation of
a measure into a linear order and a standard, and the measure can be taken to represent the
comparative. -/
theorem IsGapless.isMonotone_iff_exists_ofStandard.{u} {E : Type u} {d : Delineation E}
    (hd : d.IsGapless) :
    d.IsMonotone ↔ ∃ (D : Type u) (_ : LinearOrder D) (m : E → D) (σ : Set E → UpperSet D),
      d = ofStandard m σ ∧ ∀ a b, d.Comparative a b ↔ m b < m a := by
  rw [IsMonotone, hd.isMonotoneOn_iff_exists_ofStandard]
  refine exists₄_congr fun D _ m σ ↦ and_congr ⟨fun h ↦ ?_, fun h X _ ↦ h ▸ rfl⟩
    (forall₂_congr fun a b ↦ by simp [Comparative])
  rw [hd.eq_ofExtension]
  exact congrArg ofExtension (funext fun X ↦ h X trivial)

/-! ### The delineation of a measure

`ofMeasure` maps threshold semantics into delineation semantics, and `outranks_ofMeasure_iff`
says the map is faithful to the comparative. -/

section Measure

variable {D : Type*} [LinearOrder D] (μ : E → D)

/-- The delineation a measure induces is gapless and puts `x` in the positive extension relative
to `C` when `x` measures strictly more than some member of `C`. -/
def ofMeasure : Delineation E := ofExtension fun C ↦ {x | ∃ y ∈ C, μ y < μ x}

@[simp] theorem mem_ofMeasure : x ∈ ofMeasure μ C ↔ ∃ y ∈ C, μ y < μ x :=
  Iff.rfl

@[simp] theorem mem_neg_ofMeasure : x ∈ (ofMeasure μ).neg C ↔ ∀ y ∈ C, μ x ≤ μ y := by
  simp [ofMeasure]

/-- The delineation of a measure is its delineation at the standard of the degrees above some
member of the class. -/
theorem ofStandard_iInf_Ioi :
    (ofStandard μ fun C ↦ ⨅ y ∈ C, UpperSet.Ioi (μ y)) = ofMeasure μ := by
  rw [ofStandard, ofMeasure]
  congr 1
  refine funext fun C ↦ Set.ext fun x ↦ ?_
  simp

theorem isGapless_ofMeasure : (ofMeasure μ).IsGapless := isGapless_ofExtension _

theorem isMonotone_ofMeasure : (ofMeasure μ).IsMonotone := by
  rw [← ofStandard_iInf_Ioi μ]
  exact isMonotone_ofStandard μ _

theorem monotone_ofMeasure : Monotone (ofMeasure μ).pos :=
  fun _ _ hle _ ⟨y, hy, hlt⟩ ↦ ⟨y, hle hy, hlt⟩

/-- When some member of the class falls short of a standard, whatever meets the standard measures
above some member. -/
theorem ofStandard_subset_ofMeasure {σ : Set E → UpperSet D}
    (h : (C ∩ (ofStandard μ σ).neg C).Nonempty) : ofStandard μ σ C ⊆ ofMeasure μ C :=
  let ⟨y, hy, hyσ⟩ := h
  fun _ hx ↦ ⟨y, hy, lt_of_not_ge fun hle ↦ hyσ ((σ C).upper hle hx)⟩

/-- Under a measure-induced delineation, the ordering of two members of a comparison class is
degree comparison. -/
theorem outranks_ofMeasure_iff {a b : E} (ha : a ∈ C) (hb : b ∈ C) :
    (ofMeasure μ).Outranks C a b ↔ μ b < μ a := by
  refine ⟨fun ⟨_, _, ⟨y, hy, hlt⟩, hneg⟩ ↦ ((mem_neg_ofMeasure μ).1 hneg y hy).trans_lt hlt,
    fun hlt ↦ ⟨{a, b}, Set.insert_subset ha (Set.singleton_subset_iff.2 hb),
      ⟨b, Set.mem_insert_of_mem _ rfl, hlt⟩, (mem_neg_ofMeasure μ).2 ?_⟩⟩
  rintro y (hy | hy) <;> subst hy
  exacts [hlt.le, le_rfl]

end Measure

/-! ### Degree modifiers as narrowings of the comparison class -/

variable (d) in
/-- Klein's *very A* ((42)) evaluates *A* relative to the members of `C` that *A* holds of. -/
def very : Delineation E :=
  ⟨fun C ↦ d (d C), fun C ↦ d.neg (d C), fun C ↦ d.disjoint_pos_neg (d C)⟩

variable (d) in
/-- Klein's *fairly A* ((43)) evaluates *A* relative to the members of `C` that *very A* does not
hold of. -/
def fairly : Delineation E :=
  ⟨fun C ↦ d (C \ d.very C), fun C ↦ d.neg (C \ d.very C),
    fun C ↦ d.disjoint_pos_neg (C \ d.very C)⟩

theorem very_subset (hcc : ∀ C, d C ⊆ C) (C : Set E) : d.very C ⊆ d C :=
  hcc _

theorem fairly_disjoint_very (hcc : ∀ C, d C ⊆ C) (C : Set E) : Disjoint (d.fairly C) (d.very C) :=
  Set.disjoint_left.2 fun _ hf ↦ (hcc _ hf).2

/-! ### The equative -/

variable (d) in
/-- In the equative preorder `u ≤ v` holds when every comparison class whose positive extension
contains `v` also contains `u`, so `u ≤ v` says that *u is as A as v*: the degree of `u` on all
classes contains that of `v`. -/
abbrev preorder : Preorder E :=
  Preorder.lift fun u ↦ OrderDual.toDual (d.degree Set.univ u)

theorem preorder_le_iff : (d.preorder).le u v ↔ ∀ C, v ∈ d C → u ∈ d C :=
  degree_subset_degree_iff.trans ⟨fun h C ↦ h C trivial, fun h C _ ↦ h C⟩

/-! ### Faithfulness to a scalar relation

A delineation is sound for a scalar relation `R` when separation by a comparison class entails
`R`, which is Bochnak's second consistency constraint; it is complete when every pair related by
`R` is separated by some class, closer to Burnett's axioms. Both are classical: under the
tolerant semantics of Cobreros and colleagues, similar pairs would defeat strict separation. -/

section Faithfulness

variable (d) in
/-- A delineation is sound for a scalar relation `R` when every class that puts `x` in the
positive and `y` in the negative extension witnesses `R x y`. -/
def IsSoundFor (R : E → E → Prop) : Prop :=
  ∀ C x y, x ∈ d C → y ∈ d.neg C → R x y

variable (d) in
/-- A delineation is complete for a scalar relation `R` when every pair related by `R` is
separated by some comparison class. -/
def IsCompleteFor (R : E → E → Prop) : Prop :=
  ∀ x y, R x y → d.Comparative x y

theorem comparative_iff_of_isSoundFor_of_isCompleteFor {R : E → E → Prop} (hs : d.IsSoundFor R)
    (hc : d.IsCompleteFor R) {x y : E} : d.Comparative x y ↔ R x y :=
  ⟨fun ⟨C, hpos, hneg⟩ ↦ hs C x y hpos hneg, hc x y⟩

variable {D : Type*} [LinearOrder D] (μ : E → D)

/-- Whatever a class puts in the positive extension of a standard measures above whatever it puts
in the negative one. -/
theorem isSoundFor_ofStandard (σ : Set E → UpperSet D) :
    (ofStandard μ σ).IsSoundFor fun a b ↦ μ b < μ a :=
  fun C _ _ ha hb ↦ lt_of_not_ge fun h ↦ hb ((σ C).upper h ha)

theorem isSoundFor_ofMeasure : (ofMeasure μ).IsSoundFor fun a b ↦ μ b < μ a := by
  rw [← ofStandard_iInf_Ioi μ]
  exact isSoundFor_ofStandard μ _

theorem isCompleteFor_ofMeasure : (ofMeasure μ).IsCompleteFor fun a b ↦ μ b < μ a :=
  fun x y hR ↦ (comparative_iff_outranks_univ _).2
    ((outranks_ofMeasure_iff μ (Set.mem_univ x) (Set.mem_univ y)).2 hR)

theorem comparative_ofMeasure_iff {x y : E} : (ofMeasure μ).Comparative x y ↔ μ y < μ x :=
  comparative_iff_of_isSoundFor_of_isCompleteFor (isSoundFor_ofMeasure μ)
    (isCompleteFor_ofMeasure μ)

end Faithfulness

end Delineation
