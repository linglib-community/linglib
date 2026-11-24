module

public import Linglib.Core.Order.Filter.AtBotOn
public import Linglib.Core.Order.Minimals
public import Linglib.Core.Order.PreorderLattice
public import Mathlib.Order.Concept

/-!
# The ordering a set of criteria induces

A set of criteria ranks the points of a type by which of the criteria they satisfy. Given any
relation `sat : α → C → Prop` and a set of criteria, `Preorder.ofCriteria sat criteria` ranks `a`
below `b` when `a` satisfies every criterion of the set that `b` satisfies. No structure is
assumed on the points or on the criteria.

The order is the pullback of `⊇` along the map sending a point to the criteria it satisfies,
`fun a ↦ {c ∈ criteria | sat a c}`, so it is one ranking of the points into a preordered type.
Minimal points and the filter of what holds toward the bottom of a domain are defined for any
such ranking, in `Preorder.minimals` and `Filter.atBotOn`, and the preferential consequence
relation of `Nonmonotonic.Preferential` is stated for any ranking. This file supplies the ranking
and what is special to it: adding a criterion meets the preorder with the preorder of that
criterion, the minimal points of a set are those satisfying every criterion when some point does,
and the bottom filter can be stated through the sets of criteria satisfied together, without the
points.

With propositions as criteria and truth as satisfaction this is the ordering a premise set induces
on worlds. With the negations of alternatives as criteria it is the order whose minimal worlds a
minimal-world exhaustifier keeps.

## Main definitions

* `Preorder.ofCriteria`: the preorder a set of criteria induces.
* `Preorder.ofCriterion`: the preorder of a single criterion.
* `≤[A]`, `w ≤[A] z`, `w <[A] z`: notation, in the scope `PremiseOrdering`, for the ordering a
  family of propositions induces, the criteria ordering with truth as satisfaction.
* `Preorder.lowerSets`: the lower sets of a preorder given as a term.

## Main results

* `Preorder.ofCriteria_eq_lift`: the preorder is the pullback of `⊇` along the map sending a point
  to the criteria it satisfies.
* `Preorder.gc_ofCriteria`: the ordering of a set of criteria and the criteria an ordering
  refines form a Galois connection.
* `Preorder.ofCriteria_insert`: adding a criterion meets the preorder with that of the criterion.
* `Preorder.gc_ofCriteria_mem_lowerSets`: the ordering of a family of propositions and the lower
  sets of an ordering form a Galois connection.
* `Preorder.ofCriteria_mem_eq_of_subset_lowerSets`: a family of lower sets of a preorder
  containing the principal ones has that preorder as its ordering.
* `Preorder.antisymmRel_ofCriteria_iff`: two points are equivalent just in case they satisfy the
  same criteria.
* `Preorder.minimals_ofCriteria_eq`: the minimal points are those satisfying every criterion,
  when some point does.
* `Filter.mem_atBotOn_satisfied_iff`: the bottom filter in terms of jointly satisfied criteria.

## Implementation notes

`Preorder.ofCriteria` is defined by its unfolded condition `∀ c ∈ criteria, sat b c → sat a c`
and not as `Preorder.lift` along that map, so that the order of an inserted criterion
unfolds to a conjunction and membership in the set of criteria is not repeated on both sides. The
two agree by `Preorder.ofCriteria_eq_lift`.

## References

* [kratzer-1981]
* [lewis-1981]
* [kraus-lehmann-magidor-1990]
-/

@[expose] public section

namespace Preorder

variable {α C : Type*}

/-- The criteria-derived preorder ranks `a` below `b` when `a` satisfies every criterion in
`criteria` that `b` satisfies. -/
@[reducible] def ofCriteria (sat : α → C → Prop) (criteria : Set C) :
    Preorder α where
  le a b := ∀ c ∈ criteria, sat b c → sat a c
  le_refl _ _ _ h := h
  le_trans _ _ _ hab hbc c hc h := hab c hc (hbc c hc h)

theorem ofCriteria_le_iff (sat : α → C → Prop) (criteria : Set C) (a b : α) :
    (ofCriteria sat criteria).le a b ↔ ∀ c ∈ criteria, sat b c → sat a c :=
  Iff.rfl

theorem ofCriteria_lt_iff (sat : α → C → Prop) (criteria : Set C) (a b : α) :
    (ofCriteria sat criteria).lt a b ↔
      (ofCriteria sat criteria).le a b ∧ ¬ (ofCriteria sat criteria).le b a :=
  Iff.rfl

theorem ofCriteria_le_iff_subset (sat : α → C → Prop) (criteria : Set C)
    (a b : α) :
    (ofCriteria sat criteria).le a b ↔
      {c ∈ criteria | sat b c} ⊆ {c ∈ criteria | sat a c} :=
  ⟨fun h _ hc ↦ ⟨hc.1, h _ hc.1 hc.2⟩, fun h _ hc hb ↦ (h ⟨hc, hb⟩).2⟩

/-! ### A single criterion -/

section ofCriterion

variable {p : Preorder α} {P : α → Prop} {a b : α}

/-- The preorder of a single criterion ranks `a` below `b` when `a` satisfies the criterion
whenever `b` does. It is defined directly rather than as `ofCriteria` on a singleton, so that its
meet with another preorder unfolds to a conjunction. -/
@[reducible] def ofCriterion (P : α → Prop) : Preorder α :=
  ofLE (fun a b ↦ P b → P a) (fun _ ↦ id) fun _ _ _ hab hbc h ↦ hab (hbc h)

theorem le_ofCriterion_iff : p ≤ ofCriterion P ↔ ∀ ⦃a b⦄, p.le a b → P b → P a :=
  Iff.rfl

/-- A preorder lies below the preorder of a criterion exactly when the elements satisfying the
criterion form a lower set. -/
theorem le_ofCriterion_iff_isLowerSet : p ≤ ofCriterion P ↔ @IsLowerSet α p.toLE {a | P a} :=
  ⟨fun h _ _ hba ↦ h hba, fun h _ _ hab ↦ h hab⟩

@[simp] theorem ofCriterion_const (q : Prop) : ofCriterion (fun _ : α ↦ q) = ⊤ :=
  top_unique fun _ _ _ ↦ id

/-- A preorder ranks `a` below `b` exactly when `a` satisfies every criterion that `b` satisfies
among the criteria whose satisfiers form a lower set. -/
theorem le_iff_forall_le_ofCriterion : p.le a b ↔ ∀ P, p ≤ ofCriterion P → P b → P a :=
  ⟨fun h _ hP ↦ hP h,
    fun h ↦ h (p.le · b) (fun _ _ hac hcb ↦ p.le_trans _ _ _ hac hcb) (p.le_refl b)⟩

theorem ofCriteria_singleton (sat : α → C → Prop) (c : C) :
    ofCriteria sat {c} = ofCriterion (sat · c) :=
  Preorder.ext fun _ _ ↦ forall_eq

/-- The ordering of a set of criteria and the criteria an ordering refines form a Galois
connection between sets of criteria and preorders. Both maps reverse inclusion, so the connection
is stated into the dual order, as mathlib states the connection between polars. -/
theorem gc_ofCriteria (sat : α → C → Prop) :
    GaloisConnection (OrderDual.toDual ∘ ofCriteria sat)
      (fun p ↦ {c | OrderDual.ofDual p ≤ ofCriterion (sat · c)}) :=
  fun _ _ ↦ ⟨fun h _ hc _ _ hab ↦ h hab _ hc, fun h _ _ hab _ hc ↦ h hc hab⟩

/-- An ordering refines the ordering of a set of criteria just in case it refines the ordering of
each criterion, that is, just in case the points satisfying each criterion form a lower set of
it. -/
theorem le_ofCriteria_iff {sat : α → C → Prop} {criteria : Set C} :
    p ≤ ofCriteria sat criteria ↔ ∀ c ∈ criteria, p ≤ ofCriterion (sat · c) :=
  gc_ofCriteria sat criteria (OrderDual.toDual p)

/-- More criteria give a finer ordering. -/
theorem ofCriteria_anti (sat : α → C → Prop) : Antitone (ofCriteria sat) :=
  fun _ _ h ↦ (gc_ofCriteria sat).monotone_l h

/-- No criteria give the order relating every two elements. -/
@[simp] theorem ofCriteria_empty (sat : α → C → Prop) : ofCriteria sat ∅ = ⊤ :=
  congrArg OrderDual.ofDual (gc_ofCriteria sat).l_bot

/-- The ordering of a union of sets of criteria is the meet of their orderings. -/
theorem ofCriteria_union (sat : α → C → Prop) (s t : Set C) :
    ofCriteria sat (s ∪ t) = ofCriteria sat s ⊓ ofCriteria sat t :=
  congrArg OrderDual.ofDual ((gc_ofCriteria sat).l_sup (a₁ := s) (a₂ := t))

/-- Adding a criterion meets the criteria-derived preorder with the preorder of that criterion. -/
theorem ofCriteria_insert (sat : α → C → Prop) (c : C) (criteria : Set C) :
    ofCriteria sat (insert c criteria) = ofCriteria sat criteria ⊓ ofCriterion (sat · c) := by
  rw [← Set.union_singleton, ofCriteria_union, ofCriteria_singleton]

/-- Criteria whose satisfiers are lower sets of the criteria-derived preorder can be added to the
criteria without changing it. -/
theorem ofCriteria_eq_of_subset {sat : α → C → Prop} {criteria criteria' : Set C}
    (h₁ : criteria ⊆ criteria')
    (h₂ : ∀ c ∈ criteria', ofCriteria sat criteria ≤ ofCriterion (sat · c)) :
    ofCriteria sat criteria' = ofCriteria sat criteria :=
  le_antisymm (le_ofCriteria_iff.2 fun c hc ↦ le_ofCriteria_iff.1 le_rfl c (h₁ hc))
    (le_ofCriteria_iff.2 h₂)

end ofCriterion

/-! ### The criteria a point satisfies -/

/-- The criteria-derived preorder is the pullback of `⊇` along the criteria a point satisfies. -/
theorem ofCriteria_eq_lift (sat : α → C → Prop) (criteria : Set C) :
    ofCriteria sat criteria =
      Preorder.lift fun a ↦ OrderDual.toDual {c ∈ criteria | sat a c} :=
  Preorder.ext fun a b ↦ ofCriteria_le_iff_subset sat criteria a b

/-- Two elements are equivalent under the criteria-derived preorder exactly when they satisfy the
same criteria. -/
theorem antisymmRel_ofCriteria_iff {sat : α → C → Prop} {criteria : Set C} {a b : α} :
    AntisymmRel (ofCriteria sat criteria).le a b ↔
      {c ∈ criteria | sat a c} = {c ∈ criteria | sat b c} :=
  ((ofCriteria_le_iff_subset sat criteria a b).and (ofCriteria_le_iff_subset sat criteria b a))
    |>.trans (and_comm.trans Set.Subset.antisymm_iff.symm)

instance (sat : α → C → Prop) (l : List C) [∀ a c, Decidable (sat a c)] (a b : α) :
    Decidable ({c ∈ {c | c ∈ l} | sat a c} ⊆ {c ∈ {c | c ∈ l} | sat b c}) :=
  decidable_of_iff (∀ c ∈ l, sat a c → sat b c) (by
    rw [← ofCriteria_le_iff_subset]
    simp only [ofCriteria_le_iff, Set.mem_ofPred_eq])

/-! ### Minimal points -/

section Minimals

variable {s : Set α}

/-- Under a criteria-derived preorder, when some element of the set satisfies every criterion,
the minimal elements are exactly those that do. -/
theorem minimals_ofCriteria_eq {C : Type*} {sat : α → C → Prop} {criteria : Set C}
    (hex : ∃ a ∈ s, ∀ c ∈ criteria, sat a c) :
    (Preorder.ofCriteria sat criteria).minimals s = {a ∈ s | ∀ c ∈ criteria, sat a c} :=
  let ⟨_, hb, hsat⟩ := hex
  Set.ext fun _ ↦
    ⟨fun ⟨ha, hmin⟩ ↦ ⟨ha, fun c hc ↦ hmin hb (fun c' hc' _ ↦ hsat c' hc') c hc (hsat c hc)⟩,
      fun ⟨ha, hall⟩ ↦ ⟨ha, fun _ _ _ c hc _ ↦ hall c hc⟩⟩

/-- Under the preorder of a criterion, when some element of the set satisfies the criterion, the
minimal elements are exactly those that do. -/
theorem minimals_ofCriterion {P : α → Prop} (hex : ∃ a ∈ s, P a) :
    (ofCriterion P).minimals s = {a ∈ s | P a} :=
  let ⟨_, hb, hPb⟩ := hex
  Set.ext fun _ ↦
    ⟨fun ⟨ha, hmin⟩ ↦ ⟨ha, hmin hb (fun _ ↦ hPb) hPb⟩, fun ⟨ha, hPa⟩ ↦ ⟨ha, fun _ _ _ _ ↦ hPa⟩⟩

end Minimals

end Preorder

/-! ### The ordering a family of propositions induces

With propositions as the criteria and truth as satisfaction, the ordering is that of a premise
set: `w` lies below `z` when every premise true at `z` is true at `w`. It is written `≤[A]`. -/

/-- `≤[A]` is the ordering a family `A` of propositions induces on the worlds, ranking `w` below
`z` when every proposition of `A` true at `z` is true at `w`. -/
scoped[PremiseOrdering] notation "≤[" A "]" => @Preorder.ofCriteria _ (Set _) (· ∈ ·) A

/-- `w ≤[A] z` says that `w` is at least as good as `z` under the premise set `A`, verifying every
premise of `A` that `z` verifies. -/
scoped[PremiseOrdering] notation:50 w " ≤[" A "] " z =>
  @LE.le _ (@Preorder.toLE _ (Preorder.ofCriteria (· ∈ ·) A)) w z

/-- `w <[A] z` says that `w` is strictly better than `z` under the premise set `A`. -/
scoped[PremiseOrdering] notation:50 w " <[" A "] " z =>
  @LT.lt _ (@Preorder.toLT _ (Preorder.ofCriteria (· ∈ ·) A)) w z

open scoped PremiseOrdering

namespace Preorder

variable {W : Type*} {A : Set (Set W)}

/-- The lower sets of a preorder given as a term. -/
def lowerSets (p : Preorder W) : Set (Set W) := {s | @IsLowerSet W p.toLE s}

@[simp] theorem mem_lowerSets {p : Preorder W} {s : Set W} :
    s ∈ p.lowerSets ↔ @IsLowerSet W p.toLE s := Iff.rfl

/-- The ordering a family of propositions induces and the lower sets of an ordering form a Galois
connection between families of propositions and preorders on the worlds. -/
theorem gc_ofCriteria_mem_lowerSets :
    GaloisConnection (fun A : Set (Set W) ↦ OrderDual.toDual (≤[A]))
      (fun p ↦ (OrderDual.ofDual p).lowerSets) :=
  fun A p ↦ (gc_ofCriteria (· ∈ ·) A p).trans
    (forall₂_congr fun _ _ ↦ le_ofCriterion_iff_isLowerSet)

/-- An ordering refines the ordering of `A` just in case every member of `A` is one of its lower
sets. -/
theorem le_ofCriteria_mem_iff {p : Preorder W} : p ≤ ≤[A] ↔ A ⊆ p.lowerSets :=
  gc_ofCriteria_mem_lowerSets A (OrderDual.toDual p)

/-- Every member of a family of propositions is a lower set of the ordering it induces. -/
theorem subset_lowerSets_ofCriteria_mem (A : Set (Set W)) : A ⊆ (≤[A]).lowerSets :=
  le_ofCriteria_mem_iff.1 le_rfl

/-- Let `r` be a reflexive relation on worlds. If every member of `A` is closed downward under
`r` and every set `{v | r v w}` is a member, then the ordering of `A` is `r`. No transitivity is
assumed: it follows. -/
theorem ofCriteria_mem_le_iff_of_refl {r : W → W → Prop} (hr : ∀ w, r w w)
    (hlow : ∀ p ∈ A, ∀ ⦃v w⦄, r v w → w ∈ p → v ∈ p) (hprin : ∀ w, {v | r v w} ∈ A) {v w : W} :
    (v ≤[A] w) ↔ r v w :=
  ⟨fun h ↦ h _ (hprin w) (hr w), fun h p hp hw ↦ hlow p hp h hw⟩

/-- A family of lower sets of a preorder that contains every principal lower set has that
preorder as its ordering. -/
theorem ofCriteria_mem_eq_of_subset_lowerSets (P : Preorder W) (hlow : A ⊆ P.lowerSets)
    (hprin : ∀ w, {v | P.le v w} ∈ A) : ≤[A] = P :=
  Preorder.ext fun _ _ ↦
    ofCriteria_mem_le_iff_of_refl P.le_refl (fun _ hp _ _ h hw ↦ hlow hp h hw) hprin

end Preorder

namespace Filter

variable {W : Type*} {s t : Set W}

/-! ### Premise semantics

Ranked by the criteria a point satisfies, more being better, the filter can be stated without
points: the sets of criteria satisfied together at some point of the domain stand in for the
points, and inclusion among them for the order. -/

/-- The order derived from criteria is the ranking by the criteria satisfied. -/
theorem atBotOn_ofCriteria {C : Type*} (sat : W → C → Prop) (crit : Set C) (s : Set W) :
    @atBotOn W W (Preorder.ofCriteria sat crit) id s =
      atBotOn (OrderDual.toDual ∘ (fun w ↦ {c ∈ crit | sat w c})) s := by
  ext t
  simp only [mem_atBotOn, Function.comp_apply, OrderDual.toDual_le_toDual,
    ← Preorder.ofCriteria_le_iff_subset sat crit, id]

/-- Ranked by the criteria satisfied, `t` holds toward the bottom of `s` exactly when every set of
criteria satisfied together at some point of `s` extends, within the criteria, to a set satisfied
together at some point of `s` and only at points of `t`. -/
theorem mem_atBotOn_satisfied_iff {C : Type*} {sat : W → C → Prop} {crit : Set C} :
    t ∈ atBotOn (OrderDual.toDual ∘ (fun w ↦ {c ∈ crit | sat w c})) s ↔
      ∀ B ⊆ crit, (∃ u ∈ s, ∀ c ∈ B, sat u c) → ∃ D ⊆ crit, (∃ v ∈ s, ∀ c ∈ D, sat v c) ∧
        B ⊆ D ∧ ∀ w ∈ s, (∀ c ∈ D, sat w c) → w ∈ t := by
  simp only [mem_atBotOn, Function.comp_apply, OrderDual.toDual_le_toDual,
    ← Preorder.ofCriteria_le_iff_subset sat crit, Preorder.ofCriteria_le_iff]
  refine ⟨fun h B hB ⟨u, hu, huB⟩ ↦ ?_, fun h u hu ↦ ?_⟩
  · obtain ⟨v, hv, hvu, hvt⟩ := h u hu
    exact ⟨(fun w ↦ {c ∈ crit | sat w c}) v, Set.sep_subset _ _, ⟨v, hv, fun _ hc ↦ hc.2⟩,
      fun c hc ↦ ⟨hB hc, hvu c (hB hc) (huB c hc)⟩,
      fun w hw hwD ↦ hvt w hw fun c hc hvc ↦ hwD c ⟨hc, hvc⟩⟩
  · obtain ⟨D, hD, ⟨v, hv, hvD⟩, hBD, hDt⟩ :=
      h ((fun w ↦ {c ∈ crit | sat w c}) u) (Set.sep_subset _ _) ⟨u, hu, fun _ hc ↦ hc.2⟩
    exact ⟨v, hv, fun c hc huc ↦ hvD c (hBD ⟨hc, huc⟩),
      fun w hw hwv ↦ hDt w hw fun c hc ↦ hwv c (hD hc) (hvD c hc)⟩

end Filter
