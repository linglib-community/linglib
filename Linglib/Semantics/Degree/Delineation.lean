module

public import Linglib.Logic.Trivalent.Basic

/-!
# Delineation semantics

In delineation semantics a gradable adjective has no degree argument. A delineation sends each
comparison class, a set of entities the adjective is evaluated against, to a positive and a
negative extension relative to it. The two are disjoint, and what lies in neither is the extension
gap, the borderline cases. *a is taller than b* holds when some comparison class puts `a` in the
positive extension and `b` in the negative one; Klein develops this analysis from Kamp's account
of the comparative. Within a comparison class `C` the ordering this induces is a strict partial
order as soon as no subclass of `C` reverses a ranking another subclass makes, Klein's consistency
constraint. If moreover every subclass whose members `C` tells apart has members in both
extensions, any two members of `C` are ranked one way or the other or are nondistinct, so the
ordering is linear where nondistinct members are equivalent, that is, where no more determinate
delineation tells them apart.

A delineation without gaps is fixed by its positive extensions (`Delineation.ofExtension`), and
nothing is more determinate than it, so it is complete. A measure function induces one, whose
ordering within a class is degree comparison. Its positive extension at a class holds what
measures above the least member of the class, so the measure embeds the comparative, not the
threshold semantics of the positive form.

## Main definitions

* `Degree.Delineation`: disjoint positive and negative extensions relative to comparison classes,
  ordered by determinacy.
* `Degree.Delineation.ofExtension`, `Degree.Delineation.IsGapless`: the delineations without gaps.
* `Degree.Delineation.Comparative`, `Degree.Delineation.Outranks`: Klein's comparative and the
  ordering within a comparison class.
* `Degree.Delineation.IsMonotoneOn`, `Degree.Delineation.IsNontrivialOn`: Klein's constraints on
  admissible delineations.
* `Degree.Delineation.Nondistinct`, `Degree.Delineation.Equivalent`,
  `Degree.Delineation.IsComplete`, `Degree.Delineation.IsLinear`: no subclass tells two entities
  apart; no more determinate admissible delineation does; the two agree at a class; they agree at
  every class.
* `Degree.Delineation.ofMeasure`: the delineation a measure function induces.
* `Degree.Delineation.very`, `Degree.Delineation.fairly`: the modifiers *very* and *fairly*.

## Main statements

* `Degree.Delineation.IsMonotoneOn.isStrictOrder_outranks`: under the consistency constraint the
  ordering is a strict partial order.
* `Degree.Delineation.equivalent_or_outranks_or_outranks`: at a complete class meeting the second
  constraint any two members are equivalent or ranked.
* `Degree.Delineation.IsGapless.isComplete`: a delineation without gaps is complete, and
  `Degree.Delineation.IsGapless.isStrictWeakOrder_outranks`: its ordering is a strict weak order.
* `Degree.Delineation.outranks_ofMeasure_iff`: under a measure-induced delineation the ordering is
  degree comparison.

## Implementation notes

The comparison class of Klein's context is the parameter `C` of `Outranks`, and his constraints
are imposed on the subclasses of `C`, `𝒫 C`. A delineation is not required to leave entities
outside a class undecided, Klein's restriction of a valuation to its class; the results that need
it assume it. Klein's equivalence quantifies over the contexts at least as determinate as the
given one, which are here the delineations of an admissible family `𝒟` extending the given one.

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
    (hb : SignType.supervaluation S (b ∈ d ·) = 1) :
    SignType.supervaluation S (a ∈ d ·) = 1 := by
  rw [SignType.supervaluation_eq_one_iff] at hb ⊢
  obtain ⟨C₀, hC₀, haC₀, hbC₀⟩ := hdisc
  exact fun C hC ↦ (hmono C₀ hC₀ C hC a b haC₀ hbC₀).1 (hb C hC)

variable (d) in
theorem supervaluation_ne_true_of_comparative (hdisc : ∃ C ∈ S, a ∈ d C ∧ b ∈ d.neg C) :
    SignType.supervaluation S (b ∈ d ·) ≠ 1 := fun h ↦
  let ⟨C₀, hC₀, _, hb⟩ := hdisc
  d.notMem_neg_of_mem ((SignType.supervaluation_eq_one_iff ..).mp h C₀ hC₀) hb

end Supervaluation

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

theorem isGapless_ofMeasure : (ofMeasure μ).IsGapless := isGapless_ofExtension _

theorem isMonotone_ofMeasure : (ofMeasure μ).IsMonotone := by
  rw [IsMonotone, ofMeasure, isMonotoneOn_ofExtension_iff]
  rintro C₁ - C₂ - a b ⟨y₁, hy₁, hlt_a⟩ hnotb ⟨y₂, hy₂, hlt_b⟩
  have hle : μ b ≤ μ y₁ := not_lt.mp fun h ↦ hnotb ⟨y₁, hy₁, h⟩
  exact ⟨y₂, hy₂, hlt_b.trans (hle.trans_lt hlt_a)⟩

theorem monotone_ofMeasure : Monotone (ofMeasure μ).pos :=
  fun _ _ hle _ ⟨y, hy, hlt⟩ ↦ ⟨y, hle hy, hlt⟩

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
contains `v` also contains `u`, so `u ≤ v` says that *u is as A as v*. -/
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
