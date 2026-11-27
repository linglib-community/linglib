module

public import Linglib.Core.Order.Filter.AtBotOn
public import Linglib.Core.Order.Minimals
public import Linglib.Core.Order.PreorderLattice
public import Linglib.Logic.Nonmonotonic.PremiseOrdering.Defs
public import Mathlib.Order.Concept

/-!
# The ordering a family of propositions induces

A family `A` of sets orders the points: `a` lies below `b` when every member of `A` containing `b`
contains `a`. This preorder `≤[A]` is defined in `PremiseOrdering/Defs.lean`. With the propositions of an ordering source it is the
ordering of premise semantics; with a Hamblin set it ranks worlds by the answers true at them;
with the negations of alternatives it is the order whose minimal worlds a minimal-world
exhaustifier keeps.

Every member of `A` is a lower set of `≤[A]`, and `≤[A]` is the coarsest preorder of which that
holds. Every preorder is induced by the family of its own lower sets. So `≤[A]` and
`Preorder.lowerSets` form a Galois insertion between families of sets and preorders, from which
it follows that more sets give a finer preorder, no sets give the preorder relating every two
points, and a union of families gives the meet. A family indexed by another type induces the
ordering of its image. The members of `A` are generators: `≤[A]` is the specialization preorder
of the topology they generate, read with the more specific point lower, and the insertion is the
correspondence between preorders and the topologies in which the open sets are the lower sets.

Minimal points and the filter of what holds toward the bottom of a domain are defined for any
ranking of the points into a preordered type, in `Preorder.minimals` and `Filter.atBotOn`. Under
`≤[A]` the minimal points of a set are those in every member of `A` when some point is, and the
bottom filter can be stated through the subfamilies of `A` with a common point.

## Main definitions

* `Preorder.ofCriterion`: the ordering of a single predicate.
* `Preorder.lowerSets`: the lower sets of a preorder given as a term.
* `PremiseOrdering.gi`: the Galois insertion between families of sets and preorders.

## Main results

* `Preorder.le_ofLowerSets_iff`: a preorder refines `≤[A]` just in case every member of `A` is one
  of its lower sets.
* `Preorder.ofLowerSets_lowerSets`: every preorder is the ordering its lower sets induce.
* `Preorder.ofLowerSets_eq_of_subset_lowerSets`: a family of lower sets of a preorder containing
  the principal ones induces that preorder.
* `Preorder.ofLowerSets_insert`: adding a set meets the ordering with that of the set.
* `Preorder.minimals_ofLowerSets_eq`: the minimal points are those in every member of `A`, when
  some point is.
* `Filter.mem_atBotOn_satisfied_iff`: the bottom filter in terms of jointly satisfied criteria.

## TODO

* A family is the family of lower sets of the ordering it generates just in case it is closed
  under arbitrary intersections and arbitrary unions, so that the closure operator of
  `PremiseOrdering.gi` adds exactly these. The expressible propositions
  of `Studies/Chemla2011.lean` are a case of it.
* The family of preimages of the members of `A` under a map generates the pullback of `≤[A]`
  along it.
* Adding a set to a family is an operation on orderings, by `Preorder.ofLowerSets_insert`.
  Removing one is not: for independent `p` and `q`, the families `{p, q, p ∩ q}` and `{p, q}`
  generate the same ordering, and `{q, p ∩ q}` and `{q}` do not. Characterize the operations on
  families that descend to the orderings they generate.
* `Preorder.ofCriterion`, the decidability instance and `Filter.mem_atBotOn_satisfied_iff` are
  stated for a predicate or a relation and its criteria; restate them for families of sets.

## References

* [kratzer-1981]
* [lewis-1981]
* [kraus-lehmann-magidor-1990]
-/

@[expose] public section

open scoped PremiseOrdering

namespace Preorder

variable {α : Type*} {A B : Set (Set α)} {a b : α}

private theorem sep_subset_sep_iff {C : Type*} {sat : α → C → Prop} {crit : Set C} :
    {c ∈ crit | sat b c} ⊆ {c ∈ crit | sat a c} ↔ ∀ c ∈ crit, sat b c → sat a c :=
  ⟨fun h _ hc hb ↦ (h ⟨hc, hb⟩).2, fun h _ hc ↦ ⟨hc.1, h _ hc.1 hc.2⟩⟩

instance {C : Type*} (sat : α → C → Prop) (l : List C) [∀ a c, Decidable (sat a c)] (a b : α) :
    Decidable ({c ∈ {c | c ∈ l} | sat a c} ⊆ {c ∈ {c | c ∈ l} | sat b c}) :=
  decidable_of_iff (∀ c ∈ l, sat a c → sat b c)
    ⟨fun h _ hc ↦ ⟨hc.1, h _ hc.1 hc.2⟩, fun h _ hc ha ↦ (h ⟨hc, ha⟩).2⟩

/-! ### A single predicate -/

section ofCriterion

variable {p : Preorder α} {P : α → Prop}

/-- The preorder of a single predicate ranks `a` below `b` when `a` satisfies the predicate
whenever `b` does. It is defined directly rather than as the ordering of a singleton, so that its
meet with another preorder unfolds to a conjunction. -/
@[reducible] def ofCriterion (P : α → Prop) : Preorder α :=
  ofLE (fun a b ↦ P b → P a) (fun _ ↦ id) fun _ _ _ hab hbc h ↦ hab (hbc h)

theorem le_ofCriterion_iff : p ≤ ofCriterion P ↔ ∀ ⦃a b⦄, p.le a b → P b → P a :=
  Iff.rfl

/-- A preorder lies below the preorder of a predicate exactly when the elements satisfying the
predicate form a lower set. -/
theorem le_ofCriterion_iff_isLowerSet : p ≤ ofCriterion P ↔ @IsLowerSet α p.toLE {a | P a} :=
  ⟨fun h _ _ hba ↦ h hba, fun h _ _ hab ↦ h hab⟩

@[simp] theorem ofCriterion_const (q : Prop) : ofCriterion (fun _ : α ↦ q) = ⊤ :=
  top_unique fun _ _ _ ↦ id

/-- A preorder ranks `a` below `b` exactly when `a` satisfies every predicate that `b` satisfies
among the predicates whose satisfiers form a lower set. -/
theorem le_iff_forall_le_ofCriterion : p.le a b ↔ ∀ P, p ≤ ofCriterion P → P b → P a :=
  ⟨fun h _ hP ↦ hP h,
    fun h ↦ h (p.le · b) (fun _ _ hac hcb ↦ p.le_trans _ _ _ hac hcb) (p.le_refl b)⟩

theorem ofLowerSets_singleton (s : Set α) : ≤[{s}] = ofCriterion (· ∈ s) :=
  Preorder.ext fun _ _ ↦ forall_eq

end ofCriterion

/-! ### The Galois insertion with the lower sets of a preorder -/

/-- The lower sets of a preorder given as a term. -/
def lowerSets (p : Preorder α) : Set (Set α) := {s | @IsLowerSet α p.toLE s}

@[simp] theorem mem_lowerSets {p : Preorder α} {s : Set α} :
    s ∈ p.lowerSets ↔ @IsLowerSet α p.toLE s := Iff.rfl

/-- A preorder refines the ordering of `A` just in case every member of `A` is one of its lower
sets. -/
theorem le_ofLowerSets_iff {p : Preorder α} : p ≤ ≤[A] ↔ A ⊆ p.lowerSets :=
  ⟨fun h _ hs _ _ hba ha ↦ h hba _ hs ha, fun h _ _ hab _ hs hb ↦ h hs hab hb⟩

/-- Every member of a family is a lower set of the ordering it induces. -/
theorem subset_lowerSets_ofLowerSets (A : Set (Set α)) : A ⊆ (≤[A]).lowerSets :=
  le_ofLowerSets_iff.1 le_rfl

/-- If every member of `A` is closed downward under a relation `r`, then at a point `b` related to
itself, with `{a | r a b}` a member, the ordering of `A` is `r`. No transitivity is assumed. -/
theorem ofLowerSets_le_iff_of_mem {r : α → α → Prop}
    (hlow : ∀ s ∈ A, ∀ ⦃a b⦄, r a b → b ∈ s → a ∈ s) (hr : r b b) (hb : {a | r a b} ∈ A) :
    (a ≤[A] b) ↔ r a b :=
  ⟨fun h ↦ h _ hb hr, fun h s hs ↦ hlow s hs h⟩

/-- A family of lower sets of a preorder that contains every principal lower set induces that
preorder. -/
theorem ofLowerSets_eq_of_subset_lowerSets (p : Preorder α) (hlow : A ⊆ p.lowerSets)
    (hprin : ∀ b, {a | p.le a b} ∈ A) : ≤[A] = p :=
  Preorder.ext fun _ b ↦
    ofLowerSets_le_iff_of_mem (fun _ hs _ _ h hb ↦ hlow hs h hb) (p.le_refl b) (hprin b)

/-- Every preorder is the ordering its lower sets induce. -/
@[simp] theorem ofLowerSets_lowerSets (p : Preorder α) : ≤[p.lowerSets] = p :=
  ofLowerSets_eq_of_subset_lowerSets p subset_rfl
    fun b _ _ hab (ha : p.le _ b) ↦ p.le_trans _ _ _ hab ha

end Preorder

/-- The ordering a family of sets induces and the lower sets of a preorder form a Galois insertion
between families of sets and preorders: a preorder refines `≤[A]` just in case every member of `A`
is one of its lower sets, and every preorder is induced by its own lower sets. Both maps reverse
inclusion, so it is stated into the dual order. Its closure operator sends `A` to
`(≤[A]).lowerSets`, the largest family inducing the ordering of `A`. -/
protected def PremiseOrdering.gi {α : Type*} :
    GaloisInsertion (fun A : Set (Set α) ↦ OrderDual.toDual (≤[A]))
      (fun p ↦ (OrderDual.ofDual p).lowerSets) :=
  GaloisConnection.toGaloisInsertion (fun _ _ ↦ Preorder.le_ofLowerSets_iff)
    fun p ↦ (Preorder.ofLowerSets_lowerSets (OrderDual.ofDual p)).le

namespace Preorder

variable {α : Type*} {A B : Set (Set α)}

/-- More sets give a finer ordering. -/
theorem ofLowerSets_anti : Antitone (ofLowerSets (α := α)) :=
  fun _ _ h ↦ PremiseOrdering.gi.gc.monotone_l h

/-- No sets give the ordering relating every two points. -/
@[simp] theorem ofLowerSets_empty : ≤[(∅ : Set (Set α))] = ⊤ :=
  congrArg OrderDual.ofDual (PremiseOrdering.gi (α := α)).gc.l_bot

/-- The ordering of a union of families is the meet of their orderings. -/
theorem ofLowerSets_union (A B : Set (Set α)) : ≤[A ∪ B] = ≤[A] ⊓ ≤[B] :=
  congrArg OrderDual.ofDual (PremiseOrdering.gi.gc.l_sup (a₁ := A) (a₂ := B))

/-- Adding a set meets the ordering with the ordering of that set. -/
theorem ofLowerSets_insert (s : Set α) (A : Set (Set α)) :
    ≤[insert s A] = ≤[A] ⊓ ofCriterion (· ∈ s) := by
  rw [← Set.union_singleton, ofLowerSets_union, ofLowerSets_singleton]

/-- Sets that are lower sets of the ordering of `A` can be added to `A` without changing it. -/
theorem ofLowerSets_eq_of_subset (h₁ : A ⊆ B) (h₂ : ∀ s ∈ B, ≤[A] ≤ ofCriterion (· ∈ s)) :
    ≤[B] = ≤[A] :=
  le_antisymm (ofLowerSets_anti h₁)
    (le_ofLowerSets_iff.2 fun _ hs ↦ le_ofCriterion_iff_isLowerSet.1 (h₂ _ hs))

/-! ### Minimal points -/

section Minimals

variable {s : Set α}

/-- Under the ordering of `A`, when some element of the set lies in every member of `A`, the
minimal elements are exactly those that do. -/
theorem minimals_ofLowerSets_eq (hex : ∃ a ∈ s, ∀ t ∈ A, a ∈ t) :
    (≤[A]).minimals s = {a ∈ s | ∀ t ∈ A, a ∈ t} :=
  let ⟨_, hb, hsat⟩ := hex
  Set.ext fun _ ↦
    ⟨fun ⟨ha, hmin⟩ ↦ ⟨ha, fun c hc ↦ hmin hb (fun c' hc' _ ↦ hsat c' hc') c hc (hsat c hc)⟩,
      fun ⟨ha, hall⟩ ↦ ⟨ha, fun _ _ _ c hc _ ↦ hall c hc⟩⟩

/-- Under the preorder of a predicate, when some element of the set satisfies the predicate, the
minimal elements are exactly those that do. -/
theorem minimals_ofCriterion {P : α → Prop} (hex : ∃ a ∈ s, P a) :
    (ofCriterion P).minimals s = {a ∈ s | P a} :=
  let ⟨_, hb, hPb⟩ := hex
  Set.ext fun _ ↦
    ⟨fun ⟨ha, hmin⟩ ↦ ⟨ha, hmin hb (fun _ ↦ hPb) hPb⟩, fun ⟨ha, hPa⟩ ↦ ⟨ha, fun _ _ _ _ ↦ hPa⟩⟩

end Minimals

end Preorder

namespace Filter

variable {W : Type*} {s t : Set W}

/-! ### Premise semantics

Ranked by the criteria a point satisfies, more being better, the filter can be stated without
points: the sets of criteria satisfied together at some point of the domain stand in for the
points, and inclusion among them for the order. -/

/-- The ordering of a family of sets is the ranking by the members containing a point. -/
theorem atBotOn_ofLowerSets (A : Set (Set W)) (s : Set W) :
    atBotOn[Preorder.ofLowerSets A] s =
      atBotOn (OrderDual.toDual ∘ (fun w ↦ {p ∈ A | w ∈ p})) s := by
  ext t
  simp only [mem_atBotOn, Function.comp_apply, OrderDual.toDual_le_toDual,
    ← Preorder.ofLowerSets_le_iff_subset A, id]

/-- Ranked by the criteria satisfied, `t` holds toward the bottom of `s` exactly when every set of
criteria satisfied together at some point of `s` extends, within the criteria, to a set satisfied
together at some point of `s` and only at points of `t`. -/
theorem mem_atBotOn_satisfied_iff {C : Type*} {sat : W → C → Prop} {crit : Set C} :
    t ∈ atBotOn (OrderDual.toDual ∘ (fun w ↦ {c ∈ crit | sat w c})) s ↔
      ∀ B ⊆ crit, (∃ u ∈ s, ∀ c ∈ B, sat u c) → ∃ D ⊆ crit, (∃ v ∈ s, ∀ c ∈ D, sat v c) ∧
        B ⊆ D ∧ ∀ w ∈ s, (∀ c ∈ D, sat w c) → w ∈ t := by
  simp only [mem_atBotOn, Function.comp_apply, OrderDual.toDual_le_toDual,
    Preorder.sep_subset_sep_iff]
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
