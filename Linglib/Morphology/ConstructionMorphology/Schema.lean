/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Data.Fintype.Order
public import Linglib.Core.Data.Sum.Basic
public import Linglib.Core.Logic.Function.FactorsThrough
public import Linglib.Core.Order.Flat
public import Linglib.Core.Order.PartialUnify
public import Mathlib.Order.Lattice

/-!
# Constructional schemas

This file defines the schemas of Construction Morphology and Relational Morphology, which are
lexical entries with variables. A schema assigns each slot a value in a partial order with a
bottom `⊥`. A slot above `⊥` is a constant and a slot at `⊥` is a variable, open if the schema
marks it and closed otherwise. An item instantiates a schema if it lies above the schema's
description at every slot.

Unification is the partial join of descriptions and Structural Intersection is their meet. The
instances of a successful unification are
[the common instances of its arguments](##instantiates_iff_of_unify_eq_coe), and the intersection
of two items [instantiates exactly the schemas that both instantiate](##instantiates_inf_iff). It
is their least general generalization in Plotkin's sense, which Jackendoff and Audring compare to
Albright and Hayes's minimal generalization.

Over a lexicon of stored items, a schema relates the stored items that instantiate it and
generates the instances whose closed variables take fillers attested among those stored items, so
it [relates exactly the stored items it generates](##relates_iff_mem_and_generates). A schema is
productive if it has no closed variable, which holds exactly when
[it generates its own description over the empty lexicon](##isProductive_iff_generates_empty).

## Main definitions

* `Schema`: A schema is a slot-indexed description with a set of variables marked open.
* `Schema.Instantiates`: An item lies above a schema's description at every slot.
* `Schema.InstantiatesAt`: An item instantiates a schema through a map from positions to slots.
* `Schema.Relates`: A schema relates a stored item that instantiates it.
* `Schema.Generates`: A schema generates an instance whose closed variables take attested fillers.
* `Schema.IsProductive`: A schema has no closed variable.
* `Instantiation`: Two items agree except at some slots, where the second is strictly above.
* `Contrast`: Two items agree except at some slots, where they are incompatible.

## Implementation notes

Openness is marked on variables rather than on a schema as a whole, following Jackendoff and
Audring. Only a variable can be marked open, so a schema is determined by its description and its
open variables. The items a schema generates form
[a product of slotwise filler sets](##generates_iff_mem_pi), so a schema with two closed variables
generates unstored combinations of attested fillers. The toponym and idiom schemas that motivate
closed variables have one each.

## References

* [jackendoff-audring-2020]
* [culicover-jackendoff-2012]
* [booij-2010]
* [booij-2010-compass]
* [plotkin-1970]
* [albright-hayes-2003]
-/

@[expose] public section

namespace ConstructionMorphology

variable {V P Q P₁ P₂ α : Type*}

/-- A schema is a slot-indexed description `body` together with a set `opens` of variables marked
open, where a slot at `⊥` is a variable and a slot above `⊥` is a constant. -/
@[ext]
structure Schema (V α : Type*) [Bot α] where
  /-- The slot-indexed description. -/
  body : V → α
  /-- The variables marked open. -/
  opens : Set V
  /-- Only variables are marked open. -/
  opens_subset : opens ⊆ {v | body v = ⊥}

namespace Schema

/-! ### Variables, constructors and pullback -/

section Bot
variable [Bot α] {s : Schema V α} {v : V}

/-- The variables of `s` are its slots at `⊥`. -/
def vars (s : Schema V α) : Set V := {v | s.body v = ⊥}

/-- The closed variables of `s` are its variables not marked open. -/
def closed (s : Schema V α) : Set V := s.vars \ s.opens

@[simp] theorem mem_vars : v ∈ s.vars ↔ s.body v = ⊥ := Iff.rfl

@[simp] theorem mem_closed : v ∈ s.closed ↔ s.body v = ⊥ ∧ v ∉ s.opens := Iff.rfl

/-- The schema with description `body` and every variable open. -/
def productive (body : V → α) : Schema V α := ⟨body, {v | body v = ⊥}, subset_rfl⟩

/-- The schema with description `body` and every variable closed. -/
def nonproductive (body : V → α) : Schema V α := ⟨body, ∅, Set.empty_subset _⟩

@[simp] theorem productive_body (body : V → α) : (productive body).body = body := rfl

@[simp] theorem productive_opens (body : V → α) :
    (productive body).opens = {v | body v = ⊥} :=
  rfl

@[simp] theorem nonproductive_body (body : V → α) : (nonproductive body).body = body := rfl

@[simp] theorem nonproductive_opens (body : V → α) : (nonproductive body).opens = ∅ := rfl

@[simp] theorem closed_productive (body : V → α) : (productive body).closed = ∅ :=
  Set.sdiff_self

@[simp] theorem closed_nonproductive (body : V → α) :
    (nonproductive body).closed = {v | body v = ⊥} :=
  Set.sdiff_empty

/-- Pull back the schema `s` along the subscripting `pos`, forgetting which positions are
coindexed. -/
def comap (s : Schema V α) (pos : P → V) : Schema P α :=
  ⟨s.body ∘ pos, pos ⁻¹' s.opens, fun _ hp ↦ s.opens_subset hp⟩

@[simp] theorem comap_body (s : Schema V α) (pos : P → V) :
    (s.comap pos).body = s.body ∘ pos :=
  rfl

@[simp] theorem comap_opens (s : Schema V α) (pos : P → V) :
    (s.comap pos).opens = pos ⁻¹' s.opens :=
  rfl

@[simp] theorem comap_id (s : Schema V α) : s.comap id = s := rfl

theorem comap_comp (s : Schema V α) (pos : P → V) (σ : Q → P) :
    (s.comap pos).comap σ = s.comap (pos ∘ σ) :=
  rfl

@[simp] theorem closed_comap (s : Schema V α) (pos : P → V) :
    (s.comap pos).closed = pos ⁻¹' s.closed :=
  rfl

@[simp] theorem comap_productive (body : V → α) (pos : P → V) :
    (productive body).comap pos = productive (body ∘ pos) :=
  rfl

/-- A schema is productive if it has no closed variable. -/
def IsProductive (s : Schema V α) : Prop := s.closed = ∅

theorem isProductive_iff_opens_eq : s.IsProductive ↔ s.opens = s.vars :=
  Set.sdiff_eq_empty.trans ⟨fun h ↦ s.opens_subset.antisymm h, fun h ↦ h.ge⟩

theorem isProductive_productive (body : V → α) : (productive body).IsProductive :=
  closed_productive body

end Bot

/-! ### Instantiation -/

section PartialOrder
variable [PartialOrder α] [OrderBot α] {s t : Schema V α} {w w₁ w₂ : V → α}

/-- An item `w` instantiates the schema `s` if `w` lies above the description of `s` at every
slot. -/
def Instantiates (s : Schema V α) (w : V → α) : Prop := s.body ≤ w

theorem instantiates_iff : s.Instantiates w ↔ s.body ≤ w := Iff.rfl

instance decidablePredInstantiates [DecidableLE (V → α)] (s : Schema V α) :
    DecidablePred s.Instantiates :=
  fun w ↦ inferInstanceAs (Decidable (s.body ≤ w))

theorem instantiates_body (s : Schema V α) : s.Instantiates s.body := le_rfl

theorem Instantiates.trans_le (h : s.Instantiates w₁) (hw : w₁ ≤ w₂) :
    s.Instantiates w₂ :=
  h.trans hw

theorem instantiates_iff_eq_of_forall_isMax (h : ∀ v, IsMax (s.body v)) :
    s.Instantiates w ↔ w = s.body :=
  ⟨fun hw ↦ funext fun v ↦ le_antisymm (h v (hw v)) (hw v), fun hw ↦ hw ▸ le_rfl⟩

theorem body_le_body_iff :
    t.body ≤ s.body ↔ ∀ ⦃w⦄, s.Instantiates w → t.Instantiates w :=
  ⟨fun h _ hw ↦ h.trans hw, fun h ↦ h s.instantiates_body⟩

end PartialOrder

/-! ### Unification and Structural Intersection -/

section Unify
variable [Fintype V] [PartialOrder α] [OrderBot α] [PartialUnify α] {s t u : Schema V α}
  {w : V → α}

/-- An item instantiates a schema exactly when unifying it with the description returns the
item. -/
theorem instantiates_iff_unify : s.Instantiates w ↔ PartialUnify.unify s.body w = ↑w :=
  PartialUnify.unify_eq_right.symm

/-- The instances of a successful unification of two descriptions are their common instances. -/
theorem instantiates_iff_of_unify_eq_coe (h : PartialUnify.unify s.body t.body = ↑u.body) :
    u.Instantiates w ↔ s.Instantiates w ∧ t.Instantiates w := by
  rw [instantiates_iff, ← WithTop.coe_le_coe, ← h, PartialUnify.unify_le_coe_iff]
  rfl

end Unify

/-- The Structural Intersection of two items instantiates exactly the schemas that both
instantiate. -/
theorem instantiates_inf_iff [SemilatticeInf α] [OrderBot α] {s : Schema V α} {w₁ w₂ : V → α} :
    s.Instantiates (w₁ ⊓ w₂) ↔ s.Instantiates w₁ ∧ s.Instantiates w₂ :=
  le_inf_iff

/-! ### The generality order of a family -/

section Generality
variable {ι : Type*} [PartialOrder α] [OrderBot α]

/-- The generality order on a family of schemas with distinct descriptions, in which `i ≤ j` when
the description of `j` lies below that of `i`. -/
abbrev generalityOrder (family : ι → Schema V α)
    (hinj : Function.Injective fun i ↦ (family i).body) : PartialOrder ι :=
  PartialOrder.lift (fun i ↦ OrderDual.toDual (family i).body)
    (OrderDual.toDual.injective.comp hinj)

/-- The generality order is decidable when the order on descriptions is. -/
abbrev decidableLEGeneralityOrder [DecidableLE (V → α)] (family : ι → Schema V α)
    (hinj : Function.Injective fun i ↦ (family i).body) :
    @DecidableLE ι (generalityOrder family hinj).toLE :=
  fun i j ↦ inferInstanceAs (Decidable ((family j).body ≤ (family i).body))

end Generality

/-! ### Positions and coindexation

An item over positions is read against a schema over variables through a subscripting, which is
a map from positions to variables. Positions with the same subscript are coindexed and must be
filled alike. Two items form a paired instantiation when their sum instantiates the schema through
the sum of their subscriptings. Once two pairs fill a coindexed position differently, the pairs
are [not a product of conditions on the items separately](##setOf_instantiatesAt_elim_ne_prod),
so no schema over single items, such as one dominating both, states the pairing. -/

section Positions
variable [PartialOrder α] [OrderBot α] {s : Schema V α} {pos : P → V} {w : P → α}

/-- An item `w` over positions instantiates `s` through the subscripting `pos` if `w = u ∘ pos`
for some instance `u` of `s`. -/
def InstantiatesAt (s : Schema V α) (pos : P → V) (w : P → α) : Prop :=
  ∃ u, s.Instantiates u ∧ w = u ∘ pos

theorem Instantiates.instantiatesAt {u : V → α} (h : s.Instantiates u) (pos : P → V) :
    s.InstantiatesAt pos (u ∘ pos) :=
  ⟨u, h, rfl⟩

@[simp] theorem instantiatesAt_id {w : V → α} : s.InstantiatesAt id w ↔ s.Instantiates w :=
  ⟨fun ⟨_, hu, hw⟩ ↦ hw ▸ hu, fun h ↦ ⟨w, h, rfl⟩⟩

theorem InstantiatesAt.comp (h : s.InstantiatesAt pos w) (σ : Q → P) :
    s.InstantiatesAt (pos ∘ σ) (w ∘ σ) := by
  obtain ⟨u, hu, rfl⟩ := h
  exact ⟨u, hu, rfl⟩

theorem InstantiatesAt.factorsThrough (h : s.InstantiatesAt pos w) : w.FactorsThrough pos := by
  obtain ⟨u, -, rfl⟩ := h
  exact fun _ _ h ↦ congrArg u h

/-- An item instantiates a schema through a subscripting exactly when it instantiates the
pulled-back description and fills coindexed positions alike. -/
theorem instantiatesAt_iff :
    s.InstantiatesAt pos w ↔ (s.comap pos).Instantiates w ∧ w.FactorsThrough pos := by
  refine ⟨fun h ↦ ⟨?_, h.factorsThrough⟩, fun ⟨hc, hf⟩ ↦ ?_⟩
  · obtain ⟨u, hu, rfl⟩ := h
    exact fun p ↦ hu (pos p)
  · refine ⟨Function.extend pos w s.body, fun v ↦ ?_, (hf.extend_comp _).symm⟩
    by_cases hv : ∃ p, pos p = v
    · obtain ⟨p, rfl⟩ := hv
      rw [hf.extend_apply]
      exact hc p
    · rw [Function.extend_apply' _ _ _ hv]

instance decidableInstantiatesAt [Fintype P] [DecidableEq V] [DecidableEq α] [DecidableLE α] :
    Decidable (s.InstantiatesAt pos w) :=
  decidable_of_iff _ instantiatesAt_iff.symm

/-- Through an injective subscripting, which coindexes nothing, an item instantiates a schema
exactly when it instantiates the pulled-back description. -/
theorem instantiatesAt_iff_of_injective (h : pos.Injective) :
    s.InstantiatesAt pos w ↔ (s.comap pos).Instantiates w :=
  instantiatesAt_iff.trans (and_iff_left (h.factorsThrough w))

theorem instantiatesAt_comp_equiv (e : Q ≃ P) :
    s.InstantiatesAt (pos ∘ e) (w ∘ e) ↔ s.InstantiatesAt pos w :=
  exists_congr fun u ↦ and_congr_right' <|
    e.surjective.injective_comp_right.eq_iff (a := w) (b := u ∘ pos)

variable {pos₁ : P₁ → V} {pos₂ : P₂ → V} {w₁ : P₁ → α} {w₂ : P₂ → α}

/-- Two items are a paired instantiation exactly when they are one instance of the description
read through each subscripting. -/
theorem instantiatesAt_elim_iff_exists :
    s.InstantiatesAt (Sum.elim pos₁ pos₂) (Sum.elim w₁ w₂) ↔
      ∃ u, s.Instantiates u ∧ w₁ = u ∘ pos₁ ∧ w₂ = u ∘ pos₂ := by
  simp only [InstantiatesAt, Sum.comp_elim, Sum.elim_eq_iff]

/-- Two items are a paired instantiation exactly when each instantiates the schema through its
own subscripting and the two agree wherever their subscripts coincide. -/
theorem instantiatesAt_elim_iff :
    s.InstantiatesAt (Sum.elim pos₁ pos₂) (Sum.elim w₁ w₂) ↔
      s.InstantiatesAt pos₁ w₁ ∧ s.InstantiatesAt pos₂ w₂ ∧
        ∀ a b, pos₁ a = pos₂ b → w₁ a = w₂ b := by
  have h : (s.comap (Sum.elim pos₁ pos₂)).Instantiates (Sum.elim w₁ w₂) ↔
      (s.comap pos₁).Instantiates w₁ ∧ (s.comap pos₂).Instantiates w₂ := by
    simp only [instantiates_iff, comap_body, Sum.comp_elim, Pi.le_def, Sum.forall, Sum.elim_inl,
      Sum.elim_inr]
  rw [instantiatesAt_iff, Function.factorsThrough_sumElim_iff, h, instantiatesAt_iff,
    instantiatesAt_iff]
  tauto

theorem InstantiatesAt.sumElim_apply_eq
    (h : s.InstantiatesAt (Sum.elim pos₁ pos₂) (Sum.elim w₁ w₂)) (a : P₁) (b : P₂)
    (hab : pos₁ a = pos₂ b) : w₁ a = w₂ b :=
  (instantiatesAt_elim_iff.1 h).2.2 a b hab

/-- The pairs of a paired instantiation are not the product of a set of first items and a set of
second items once a position of each is coindexed and two pairs fill those positions
differently. -/
theorem setOf_instantiatesAt_elim_ne_prod {w₁' : P₁ → α} {w₂' : P₂ → α}
    (h : s.InstantiatesAt (Sum.elim pos₁ pos₂) (Sum.elim w₁ w₂))
    (h' : s.InstantiatesAt (Sum.elim pos₁ pos₂) (Sum.elim w₁' w₂')) {a : P₁} {b : P₂}
    (hab : pos₁ a = pos₂ b) (hne : w₁ a ≠ w₂' b) (A : Set (P₁ → α)) (B : Set (P₂ → α)) :
    {p : (P₁ → α) × (P₂ → α) | s.InstantiatesAt (Sum.elim pos₁ pos₂) (Sum.elim p.1 p.2)} ≠
      A ×ˢ B := fun hAB ↦ by
  have hm x y := Set.ext_iff.1 hAB (x, y)
  exact hne (((hm w₁ w₂').2 ⟨((hm _ _).1 h).1, ((hm _ _).1 h').2⟩).sumElim_apply_eq a b hab)

theorem instantiatesAt_elim_swap :
    s.InstantiatesAt (Sum.elim pos₂ pos₁) (Sum.elim w₂ w₁) ↔
      s.InstantiatesAt (Sum.elim pos₁ pos₂) (Sum.elim w₁ w₂) := by
  rw [← instantiatesAt_comp_equiv (Equiv.sumComm P₁ P₂), Equiv.sumComm_apply, Sum.elim_swap,
    Sum.elim_swap]

/-- If two injective subscriptings coincide exactly outside `S`, a paired instantiation is a pair
of instances of the pulled-back descriptions that agree outside `S`. -/
theorem instantiatesAt_elim_iff_eqOn {pos₁ pos₂ : P → V} {w₁ w₂ : P → α} {S : Set P}
    (h₁ : pos₁.Injective) (h₂ : pos₂.Injective)
    (h : ∀ a b, pos₁ a = pos₂ b ↔ a = b ∧ a ∉ S) :
    s.InstantiatesAt (Sum.elim pos₁ pos₂) (Sum.elim w₁ w₂) ↔
      (s.comap pos₁).Instantiates w₁ ∧ (s.comap pos₂).Instantiates w₂ ∧
        Set.EqOn w₁ w₂ Sᶜ := by
  rw [instantiatesAt_elim_iff, instantiatesAt_iff_of_injective h₁,
    instantiatesAt_iff_of_injective h₂]
  refine and_congr_right fun _ ↦ and_congr_right fun _ ↦
    ⟨fun hc a ha ↦ hc a a ((h a a).2 ⟨rfl, ha⟩), fun he a b hab ↦ ?_⟩
  obtain ⟨rfl, ha⟩ := (h a b).1 hab
  exact he ha

end Positions

/-! ### Filling the variables over the flat order

Over the flat order every constant is maximal, so an instance of a schema is determined by what
fills its variables: [the instances of a schema are its fillings](##instantiates_iff_exists_fill).
-/

section Fill
variable {β : Type*} {s : Schema V (Flat β)} {x u : V → Flat β} {pos : P → V} {w : P → Flat β}

/-- The instance of `s` whose variables are filled by `x` and whose constants stay. -/
def fill (s : Schema V (Flat β)) (x : V → Flat β) (v : V) : Flat β := (s.body v).or (x v)

@[simp] theorem fill_apply (v : V) : s.fill x v = (s.body v).or (x v) := rfl

theorem instantiates_fill (s : Schema V (Flat β)) (x : V → Flat β) : s.Instantiates (s.fill x) :=
  fun _ ↦ Flat.le_or_left _ _

theorem Instantiates.fill_eq (h : s.Instantiates u) : s.fill u = u :=
  funext fun v ↦ Flat.or_eq_right.2 (h v)

/-- Over the flat order the instances of a schema are its fillings. -/
theorem instantiates_iff_exists_fill : s.Instantiates u ↔ ∃ x, u = s.fill x :=
  ⟨fun h ↦ ⟨u, h.fill_eq.symm⟩, fun ⟨x, hx⟩ ↦ hx ▸ s.instantiates_fill x⟩

theorem instantiatesAt_iff_exists_fill : s.InstantiatesAt pos w ↔ ∃ x, w = s.fill x ∘ pos :=
  ⟨fun ⟨u, hu, hw⟩ ↦ ⟨u, hu.fill_eq.symm ▸ hw⟩, fun ⟨x, hw⟩ ↦ ⟨_, s.instantiates_fill x, hw⟩⟩

variable {pos₁ : P₁ → V} {pos₂ : P₂ → V} {w₁ : P₁ → Flat β} {w₂ : P₂ → Flat β}

/-- Two items are a paired instantiation over the flat order exactly when they are one filling
of the schema read through each subscripting. -/
theorem instantiatesAt_elim_iff_exists_fill :
    s.InstantiatesAt (Sum.elim pos₁ pos₂) (Sum.elim w₁ w₂) ↔
      ∃ x, w₁ = s.fill x ∘ pos₁ ∧ w₂ = s.fill x ∘ pos₂ := by
  rw [instantiatesAt_elim_iff_exists]
  exact ⟨fun ⟨u, hu, h⟩ ↦ ⟨u, hu.fill_eq.symm ▸ h⟩, fun ⟨x, h⟩ ↦ ⟨_, s.instantiates_fill x, h⟩⟩

end Fill

/-! ### The relational and the generative role -/

section Roles
variable [PartialOrder α] [OrderBot α] {s : Schema V α} {w : V → α} {Λ Λ' : Set (V → α)}
  {v : V}

/-- A schema `s` relates `w` over the lexicon `Λ` if `w` is stored in `Λ` and instantiates `s`. -/
def Relates (s : Schema V α) (Λ : Set (V → α)) (w : V → α) : Prop :=
  w ∈ Λ ∧ s.Instantiates w

theorem Relates.instantiates (h : s.Relates Λ w) : s.Instantiates w := h.2

theorem Relates.mono (h : Λ ⊆ Λ') (hw : s.Relates Λ w) : s.Relates Λ' w := ⟨h hw.1, hw.2⟩

theorem Instantiates.relates_insert (h : s.Instantiates w) : s.Relates (insert w Λ) w :=
  ⟨Set.mem_insert _ _, h⟩

/-- The fillers attested at slot `v` are the values that the stored instances of `s` take at
`v`. -/
def attested (s : Schema V α) (Λ : Set (V → α)) (v : V) : Set α :=
  (· v) '' {w | s.Relates Λ w}

@[simp]
theorem mem_attested {a : α} : a ∈ s.attested Λ v ↔ ∃ w, s.Relates Λ w ∧ w v = a :=
  Iff.rfl

theorem Relates.apply_mem_attested (h : s.Relates Λ w) (v : V) : w v ∈ s.attested Λ v :=
  Set.mem_image_of_mem _ h

theorem attested_mono (h : Λ ⊆ Λ') (v : V) : s.attested Λ v ⊆ s.attested Λ' v :=
  Set.image_mono fun _ hw ↦ hw.mono h

/-- A schema `s` generates `w` over the lexicon `Λ` if `w` instantiates `s` and fills each closed
variable of `s` with a filler attested in `Λ`. The item `w` need not be stored. -/
def Generates (s : Schema V α) (Λ : Set (V → α)) (w : V → α) : Prop :=
  s.Instantiates w ∧ ∀ v ∈ s.closed, w v ∈ s.attested Λ v

theorem Generates.instantiates (h : s.Generates Λ w) : s.Instantiates w := h.1

/-- The values a schema admits at slot `v` over the lexicon `Λ` are any value at an open variable,
an attested filler at a closed one, and any value above a constant. -/
def fillers (s : Schema V α) (Λ : Set (V → α)) (v : V) : Set α :=
  {a | s.body v ≤ a ∧ (v ∈ s.closed → a ∈ s.attested Λ v)}

/-- The items a schema generates are the product of its slotwise filler sets. -/
theorem generates_iff_mem_pi : s.Generates Λ w ↔ w ∈ Set.pi Set.univ (s.fillers Λ) := by
  simp only [Generates, instantiates_iff, Pi.le_def, Set.mem_univ_pi, fillers, Set.mem_ofPred_eq,
    forall_and]

theorem Relates.generates (h : s.Relates Λ w) : s.Generates Λ w :=
  ⟨h.2, fun v _ ↦ h.apply_mem_attested v⟩

/-- A schema relates exactly the stored items it generates. -/
theorem relates_iff_mem_and_generates : s.Relates Λ w ↔ w ∈ Λ ∧ s.Generates Λ w :=
  ⟨fun h ↦ ⟨h.1, h.generates⟩, fun h ↦ ⟨h.1, h.2.instantiates⟩⟩

theorem Generates.relates_insert (h : s.Generates Λ w) : s.Relates (insert w Λ) w :=
  h.instantiates.relates_insert

theorem Generates.mono (h : Λ ⊆ Λ') (hw : s.Generates Λ w) : s.Generates Λ' w :=
  ⟨hw.1, fun v hv ↦ attested_mono h v (hw.2 v hv)⟩

theorem IsProductive.generates_iff (hs : s.IsProductive) :
    s.Generates Λ w ↔ s.Instantiates w :=
  ⟨Generates.instantiates, fun h ↦ ⟨h, fun v hv ↦ (Set.notMem_empty v (hs ▸ hv)).elim⟩⟩

/-- A schema is productive exactly when it generates its own description over the empty
lexicon. -/
theorem isProductive_iff_generates_empty : s.IsProductive ↔ s.Generates ∅ s.body :=
  ⟨fun hs ↦ hs.generates_iff.2 s.instantiates_body, fun h ↦
    Set.eq_empty_of_forall_notMem fun v hv ↦ (h.2 v hv).elim fun _ ⟨⟨hw, _⟩, _⟩ ↦ hw⟩

theorem isProductive_iff_forall_generates_iff :
    s.IsProductive ↔
      ∀ (Λ : Set (V → α)) (w : V → α), s.Generates Λ w ↔ s.Instantiates w :=
  ⟨fun hs _ _ ↦ hs.generates_iff,
    fun h ↦ isProductive_iff_generates_empty.2 ((h ∅ _).2 s.instantiates_body)⟩

end Roles

end Schema

/-! ### Relational links

Two items over the same positions are the same except at `S` when they agree outside `S`. The link
between them is an *instantiation* if the second is strictly above the first at every position of
`S`, and a *contrast* if the two are incompatible at every position of `S`. An elaboration is an
instantiation from an item that is `⊥` throughout `S`. -/

section RelationalLinks
variable [PartialOrder α] {f g : P → α} {S : Set P}

/-- `Instantiation f g S` holds when `g` agrees with `f` outside `S` and is strictly above `f` at
every position of `S`. This is the link from a schema's description to its instances. -/
def Instantiation (f g : P → α) (S : Set P) : Prop :=
  Set.EqOn f g Sᶜ ∧ ∀ p ∈ S, f p < g p

/-- `Contrast f g S` holds when `f` and `g` agree outside `S` and are incompatible at every position
of `S`. This is the link between sister words. -/
def Contrast (f g : P → α) (S : Set P) : Prop :=
  Set.EqOn f g Sᶜ ∧ ∀ p ∈ S, ¬ Compat (f p) (g p)

theorem Contrast.symm (h : Contrast f g S) : Contrast g f S :=
  ⟨h.1.symm, fun p hp hc ↦ h.2 p hp hc.symm⟩

variable [OrderBot α]

theorem Instantiation.instantiates {s : Schema P α} {w : P → α}
    (h : Instantiation s.body w S) : s.Instantiates w := fun p ↦
  (em (p ∈ S)).elim (fun hp ↦ (h.2 p hp).le) fun hp ↦ (h.1 hp).le

theorem contrast_iff_of_forall_isMax (hα : ∀ a : α, a ≠ ⊥ → IsMax a) :
    Contrast f g S ↔
      Set.EqOn f g Sᶜ ∧ ∀ p ∈ S, f p ≠ ⊥ ∧ g p ≠ ⊥ ∧ f p ≠ g p :=
  and_congr_right' (forall₂_congr fun _ _ ↦ not_compat_iff_of_forall_isMax hα)

end RelationalLinks

end ConstructionMorphology
