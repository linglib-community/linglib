/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Data.Fintype.Order
public import Linglib.Core.Data.Sum.Basic
public import Linglib.Core.Order.PartialUnify
public import Mathlib.Order.Lattice

/-!
# Constructional schemas

This file defines the schemas of Construction Morphology and Relational Morphology: lexical
entries with variables. A *schema* assigns each slot a value in a partial order with a bottom `⊥`
and marks some slots as open. A slot above `⊥` is a *constant*; a slot at `⊥` is a *variable*,
*open* if marked and *closed* otherwise. An item *instantiates* a schema if it lies above the
schema's description at every slot; equivalently, unifying the two returns the item.

Over a lexicon of stored items, a schema *relates* the stored items that instantiate it and
*generates* the possibly novel items whose closed variables take fillers attested among those
stored instances. Every related item is generated, a generated item is related once stored, and a
schema is productive (every variable open) iff it generates its own description over the empty
lexicon.

## Main declarations

* `Schema`: a slot-indexed description with a set of open variables.
* `Schema.Instantiates`: instantiation, equivalently unification (`Schema.instantiates_iff_unify`).
* `Schema.InstantiatesAt`: instantiation by an item whose positions are coindexed with variables.
* `Schema.generalityOrder`: a family of schemas ordered by generality.
* `Schema.Relates`, `Schema.Generates`, `Schema.IsProductive`: the two roles, and productivity.
* `Instantiation`, `Contrast`: links between two items that agree outside a set of slots.
* `Schema.instantiates_inf_iff`: the meet of two items is their least general generalization,
  the Structural Intersection of Relational Morphology.

## Implementation notes

Productivity is a property of variables rather than of a schema as a whole: constants need no
attested fillers, and `Schema.IsProductive` is the case in which every variable is open. Marking a
constant slot as open has no effect.

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

/-- A schema is a slot-indexed description `body` together with a set `opens` of slots marked as
open variables. A slot at `⊥` is a variable and a slot above `⊥` is a constant. -/
@[ext]
structure Schema (V α : Type*) where
  /-- The slot-indexed description. -/
  body : V → α
  /-- The slots marked as open variables. -/
  opens : Set V

namespace Schema

section PartialOrder
variable [PartialOrder α] {s t : Schema V α} {w w₁ w₂ : V → α}

/-- An item `w` instantiates the schema `s` if `w` lies above the description of `s` at every slot,
so that it matches each constant and fills each variable. -/
def Instantiates (s : Schema V α) (w : V → α) : Prop := s.body ≤ w

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

/-- An item instantiates a schema exactly when unifying it with the description returns the
item. -/
theorem instantiates_iff_unify [Fintype V] [PartialUnify α] :
    s.Instantiates w ↔ PartialUnify.unify s.body w = ↑w :=
  PartialUnify.unify_eq_right.symm

/-- The instances of a unified description are the common instances of its two conjuncts. -/
theorem instantiates_iff_of_unify_eq_coe [Fintype V] [PartialUnify α] {u : Schema V α}
    (h : PartialUnify.unify s.body t.body = ↑u.body) :
    u.Instantiates w ↔ s.Instantiates w ∧ t.Instantiates w := by
  rw [Instantiates, ← WithTop.coe_le_coe, ← h, PartialUnify.unify_le_coe_iff]
  rfl

end PartialOrder

/-! ### The generality order of a family -/

/-- In the generality order of a family of schemas with distinct descriptions, `i ≤ j` when the
description of `j` lies below that of `i`, so that `j` is at least as general. The schemas of a
hierarchical lexicon inherit defeasible properties by default inheritance along this order. -/
abbrev generalityOrder {ι : Type*} [PartialOrder α] (family : ι → Schema V α)
    (hinj : Function.Injective fun i ↦ (family i).body) : PartialOrder ι :=
  PartialOrder.lift (fun i ↦ OrderDual.toDual (family i).body)
    (OrderDual.toDual.injective.comp hinj)

/-! ### Positions and coindexation

An item over positions is read against a schema over variables through a *subscripting*, a map
from positions to variables; positions with the same subscript are *coindexed* and must be filled
alike. Two items form a *paired instantiation* when their sum instantiates the schema through the
sum of their subscriptings; the relation is symmetric. -/

/-- Pull the schema `s` back along the subscripting `pos`, reading its description and open
variables at positions and forgetting which positions are coindexed. -/
def comap (s : Schema V α) (pos : P → V) : Schema P α :=
  ⟨s.body ∘ pos, pos ⁻¹' s.opens⟩

@[simp] theorem comap_body (s : Schema V α) (pos : P → V) :
    (s.comap pos).body = s.body ∘ pos :=
  rfl

@[simp] theorem comap_opens (s : Schema V α) (pos : P → V) :
    (s.comap pos).opens = pos ⁻¹' s.opens :=
  rfl

section Positions
variable [PartialOrder α] {s : Schema V α} {pos : P → V} {w : P → α}

/-- An item `w` over positions instantiates `s` through the subscripting `pos` if `w = u ∘ pos`
for some instance `u` of `s`. -/
def InstantiatesAt (s : Schema V α) (pos : P → V) (w : P → α) : Prop :=
  ∃ u, s.Instantiates u ∧ w = u ∘ pos

theorem Instantiates.instantiatesAt {u : V → α} (h : s.Instantiates u) (pos : P → V) :
    s.InstantiatesAt pos (u ∘ pos) :=
  ⟨u, h, rfl⟩

@[simp] theorem instantiatesAt_id {w : V → α} : s.InstantiatesAt id w ↔ s.Instantiates w :=
  ⟨fun ⟨_, hu, hw⟩ ↦ hw ▸ hu, fun h ↦ ⟨w, h, rfl⟩⟩

/-- An item instantiates a schema through a subscripting exactly when it instantiates the
pulled-back description and fills coindexed positions alike. -/
theorem instantiatesAt_iff :
    s.InstantiatesAt pos w ↔ (s.comap pos).Instantiates w ∧ w.FactorsThrough pos := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨fun p ↦ hu (pos p), fun _ _ h ↦ congrArg u h⟩
  · rintro ⟨hc, hf⟩
    refine ⟨Function.extend pos w s.body, fun v ↦ ?_, (hf.extend_comp _).symm⟩
    by_cases hv : ∃ p, pos p = v
    · obtain ⟨p, rfl⟩ := hv
      rw [hf.extend_apply]
      exact hc p
    · rw [Function.extend_apply' _ _ _ hv]

theorem instantiatesAt_comp_equiv (e : Q ≃ P) :
    s.InstantiatesAt (pos ∘ e) (w ∘ e) ↔ s.InstantiatesAt pos w := by
  constructor
  · rintro ⟨u, hu, hw⟩
    refine ⟨u, hu, funext fun p ↦ ?_⟩
    simpa using congrFun hw (e.symm p)
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, hu, rfl⟩

variable {pos₁ : P₁ → V} {pos₂ : P₂ → V} {w₁ : P₁ → α} {w₂ : P₂ → α}

/-- Two items are a paired instantiation through their subscriptings exactly when each
instantiates its pulled-back description, each fills its own coindexed positions alike, and
the two agree wherever their subscripts coincide. -/
theorem instantiatesAt_elim_iff :
    s.InstantiatesAt (Sum.elim pos₁ pos₂) (Sum.elim w₁ w₂) ↔
      (s.comap pos₁).Instantiates w₁ ∧ (s.comap pos₂).Instantiates w₂ ∧
        w₁.FactorsThrough pos₁ ∧ w₂.FactorsThrough pos₂ ∧
          ∀ a b, pos₁ a = pos₂ b → w₁ a = w₂ b := by
  have h : (s.comap (Sum.elim pos₁ pos₂)).Instantiates (Sum.elim w₁ w₂) ↔
      (s.comap pos₁).Instantiates w₁ ∧ (s.comap pos₂).Instantiates w₂ := by
    simp only [Instantiates, comap_body, Sum.comp_elim, Pi.le_def, Sum.forall, Sum.elim_inl,
      Sum.elim_inr]
  rw [instantiatesAt_iff, Function.factorsThrough_sumElim_iff, h, and_assoc]

theorem instantiatesAt_elim_swap :
    s.InstantiatesAt (Sum.elim pos₂ pos₁) (Sum.elim w₂ w₁) ↔
      s.InstantiatesAt (Sum.elim pos₁ pos₂) (Sum.elim w₁ w₂) := by
  rw [← instantiatesAt_comp_equiv (Equiv.sumComm P₁ P₂)]
  have h₁ : Sum.elim pos₂ pos₁ ∘ ⇑(Equiv.sumComm P₁ P₂) = Sum.elim pos₁ pos₂ :=
    funext fun p ↦ by cases p <;> rfl
  have h₂ : Sum.elim w₂ w₁ ∘ ⇑(Equiv.sumComm P₁ P₂) = Sum.elim w₁ w₂ :=
    funext fun p ↦ by cases p <;> rfl
  rw [h₁, h₂]

/-- If two injective subscriptings coincide exactly outside `S`, a paired instantiation is a pair
of instances of the pulled-back descriptions that agree outside `S`. -/
theorem instantiatesAt_elim_iff_eqOn {pos₁ pos₂ : P → V} {w₁ w₂ : P → α} {S : Set P}
    (h₁ : pos₁.Injective) (h₂ : pos₂.Injective)
    (h : ∀ a b, pos₁ a = pos₂ b ↔ a = b ∧ a ∉ S) :
    s.InstantiatesAt (Sum.elim pos₁ pos₂) (Sum.elim w₁ w₂) ↔
      (s.comap pos₁).Instantiates w₁ ∧ (s.comap pos₂).Instantiates w₂ ∧
        Set.EqOn w₁ w₂ Sᶜ := by
  rw [instantiatesAt_elim_iff]
  refine and_congr_right fun _ ↦ and_congr_right fun _ ↦ ⟨fun hc a ha ↦ ?_, fun he ↦ ?_⟩
  · exact hc.2.2 a a ((h a a).2 ⟨rfl, ha⟩)
  · refine ⟨h₁.factorsThrough _, h₂.factorsThrough _, fun a b hab ↦ ?_⟩
    obtain ⟨rfl, ha⟩ := (h a b).1 hab
    exact he ha

end Positions

/-! ### The relational role -/

section PartialOrder
variable [PartialOrder α] {s : Schema V α} {w : V → α} {Λ Λ' : Set (V → α)} {v : V}

/-- In its relational role, a schema `s` relates `w` over the lexicon `Λ` if `w` is stored in `Λ`
and instantiates `s`. -/
def Relates (s : Schema V α) (Λ : Set (V → α)) (w : V → α) : Prop :=
  w ∈ Λ ∧ s.Instantiates w

theorem Relates.instantiates (h : s.Relates Λ w) : s.Instantiates w := h.2

theorem Relates.mono (h : Λ ⊆ Λ') (hw : s.Relates Λ w) : s.Relates Λ' w := ⟨h hw.1, hw.2⟩

theorem Instantiates.relates_insert (h : s.Instantiates w) : s.Relates (insert w Λ) w :=
  ⟨Set.mem_insert _ _, h⟩

/-- The fillers attested at slot `v` are the values the stored instances of `s` take at `v`. A
closed variable admits only these. -/
def attested (s : Schema V α) (Λ : Set (V → α)) (v : V) : Set α :=
  {a | ∃ w, s.Relates Λ w ∧ w v = a}

@[simp]
theorem mem_attested {a : α} : a ∈ s.attested Λ v ↔ ∃ w, s.Relates Λ w ∧ w v = a :=
  Iff.rfl

theorem Relates.apply_mem_attested (h : s.Relates Λ w) (v : V) : w v ∈ s.attested Λ v :=
  ⟨w, h, rfl⟩

theorem attested_mono (h : Λ ⊆ Λ') (v : V) : s.attested Λ v ⊆ s.attested Λ' v := by
  rintro a ⟨w, hw, rfl⟩
  exact ⟨w, hw.mono h, rfl⟩

end PartialOrder

/-- A schema is instantiated by the meet of two items exactly when it is instantiated by both, so
the meet is their least general generalization, the Structural Intersection of Relational
Morphology. -/
theorem instantiates_inf_iff [SemilatticeInf α] {s : Schema V α} {w₁ w₂ : V → α} :
    s.Instantiates (w₁ ⊓ w₂) ↔ s.Instantiates w₁ ∧ s.Instantiates w₂ :=
  le_inf_iff

/-! ### The generative role -/

section OrderBot
variable [PartialOrder α] [OrderBot α] {s : Schema V α} {w : V → α} {Λ Λ' : Set (V → α)}

/-- The schema with description `body` and every variable open. -/
def productive (body : V → α) : Schema V α := ⟨body, {v | body v = ⊥}⟩

@[simp] theorem productive_body (body : V → α) : (productive body).body = body := rfl

@[simp] theorem productive_opens (body : V → α) :
    (productive body).opens = {v | body v = ⊥} :=
  rfl

/-- In its generative role, a schema `s` generates `w` over the lexicon `Λ` if `w` instantiates `s`
and fills each closed variable of `s` (a slot at `⊥` not marked open) with a filler attested in `Λ`.
The item `w` need not be stored. -/
def Generates (s : Schema V α) (Λ : Set (V → α)) (w : V → α) : Prop :=
  s.Instantiates w ∧ ∀ v, s.body v = ⊥ → v ∉ s.opens → w v ∈ s.attested Λ v

theorem Generates.instantiates (h : s.Generates Λ w) : s.Instantiates w := h.1

/-- The values a schema admits at slot `v` over the lexicon `Λ` are any value at an open variable,
an attested filler at a closed one, and any value above a constant. -/
def fillers (s : Schema V α) (Λ : Set (V → α)) (v : V) : Set α :=
  {a | s.body v ≤ a ∧ (s.body v = ⊥ → v ∉ s.opens → a ∈ s.attested Λ v)}

/-- The items a schema generates are the product of its slotwise filler sets. -/
theorem generates_iff_mem_pi : s.Generates Λ w ↔ w ∈ Set.pi Set.univ (s.fillers Λ) := by
  simp only [Generates, Set.mem_univ_pi, fillers, Set.mem_ofPred_eq, Instantiates, Pi.le_def]
  exact ⟨fun h v ↦ ⟨h.1 v, h.2 v⟩, fun h ↦ ⟨fun v ↦ (h v).1, fun v ↦ (h v).2⟩⟩

theorem fillers_eq_singleton_of_forall_isMax (hα : ∀ a : α, a ≠ ⊥ → IsMax a)
    {v : V} (hv : s.body v ≠ ⊥) :
    s.fillers Λ v = {s.body v} := by
  ext a
  simp only [fillers, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  exact ⟨fun h ↦ le_antisymm (hα _ hv h.1) h.1,
    fun h ↦ ⟨h.ge, fun h' ↦ absurd h' hv⟩⟩

theorem Relates.generates (h : s.Relates Λ w) : s.Generates Λ w :=
  ⟨h.2, fun v _ _ ↦ h.apply_mem_attested v⟩

theorem Generates.relates_insert (h : s.Generates Λ w) : s.Relates (insert w Λ) w :=
  h.instantiates.relates_insert

theorem Generates.mono (h : Λ ⊆ Λ') (hw : s.Generates Λ w) : s.Generates Λ' w :=
  ⟨hw.1, fun v hv hvo ↦ attested_mono h v (hw.2 v hv hvo)⟩

/-- A schema is productive if every variable (every slot at `⊥`) is open. -/
def IsProductive (s : Schema V α) : Prop := ∀ v, s.body v = ⊥ → v ∈ s.opens

theorem isProductive_productive (body : V → α) : (productive body).IsProductive := fun _ h ↦ h

theorem IsProductive.generates_iff (hs : s.IsProductive) :
    s.Generates Λ w ↔ s.Instantiates w :=
  ⟨Generates.instantiates, fun h ↦ ⟨h, fun v hv hvo ↦ absurd (hs v hv) hvo⟩⟩

/-- A schema is productive exactly when it generates its own description over the empty
lexicon. -/
theorem isProductive_iff_generates_empty : s.IsProductive ↔ s.Generates ∅ s.body := by
  refine ⟨fun hs ↦ ⟨le_rfl, fun v hv hvo ↦ absurd (hs v hv) hvo⟩, fun h v hv ↦ ?_⟩
  by_contra hvo
  obtain ⟨w, ⟨hw, -⟩, -⟩ := h.2 v hv hvo
  exact hw

theorem isProductive_iff_forall_generates_iff :
    s.IsProductive ↔
      ∀ (Λ : Set (V → α)) (w : V → α), s.Generates Λ w ↔ s.Instantiates w :=
  ⟨fun hs _ _ ↦ hs.generates_iff,
    fun h ↦ isProductive_iff_generates_empty.2 ((h ∅ _).2 s.instantiates_body)⟩

end OrderBot

end Schema

/-! ### Relational links

Two items over the same positions are the same except at `S` when they agree outside `S`. The link
between them is an *instantiation* if the second is strictly above the first at every position of
`S`, and a *contrast* if the two are incompatible at every position of `S`. An elaboration, one
item the same as the other plus something more, is an instantiation read from the elaborated item.
If every value other than `⊥` is maximal, a filled item instantiates a schema iff it is an
instantiation of the description at the variables
(`Schema.instantiates_iff_instantiation_of_forall_isMax`). -/

section RelationalLinks
variable {f g : P → α} {S : Set P}

section PartialOrder
variable [PartialOrder α]

/-- `Instantiation f g S` holds when `g` agrees with `f` outside `S` and is strictly above `f` at
every position of `S`. This is the link from a schema's description to its instances. -/
def Instantiation (f g : P → α) (S : Set P) : Prop :=
  Set.EqOn f g Sᶜ ∧ StrongLT (S.domRestrict f) (S.domRestrict g)

/-- `Contrast f g S` holds when `f` and `g` agree outside `S` and are incompatible at every position
of `S`. This is the link between sister words. -/
def Contrast (f g : P → α) (S : Set P) : Prop :=
  Set.EqOn f g Sᶜ ∧ ∀ p ∈ S, ¬ Compat (f p) (g p)

theorem Contrast.symm (h : Contrast f g S) : Contrast g f S :=
  ⟨h.1.symm, fun p hp hc ↦ h.2 p hp hc.symm⟩

theorem Instantiation.instantiates {s : Schema P α} {w : P → α}
    (h : Instantiation s.body w S) : s.Instantiates w := by
  intro p
  by_cases hp : p ∈ S
  · exact (h.2 ⟨p, hp⟩).le
  · exact (h.1 hp).le

end PartialOrder

section OrderBot
variable [PartialOrder α] [OrderBot α]

theorem contrast_iff_of_forall_isMax (hα : ∀ a : α, a ≠ ⊥ → IsMax a) :
    Contrast f g S ↔
      Set.EqOn f g Sᶜ ∧ ∀ p ∈ S, f p ≠ ⊥ ∧ g p ≠ ⊥ ∧ f p ≠ g p :=
  and_congr_right' (forall₂_congr fun _ _ ↦ not_compat_iff_of_forall_isMax hα)

namespace Schema

theorem instantiates_iff_instantiation_of_forall_isMax
    (hα : ∀ a : α, a ≠ ⊥ → IsMax a) {s : Schema P α} {w : P → α}
    (hw : ∀ p, w p ≠ ⊥) :
    s.Instantiates w ↔ Instantiation s.body w {p | s.body p = ⊥} := by
  refine ⟨fun h ↦ ⟨fun p hp ↦ ?_, fun p ↦ ?_⟩, Instantiation.instantiates⟩
  · simp only [Set.mem_compl_iff, Set.mem_ofPred_eq] at hp
    exact le_antisymm (h p) (hα _ hp (h p))
  · have hp : s.body p = ⊥ := p.2
    show s.body p < w p
    rw [hp]
    exact bot_lt_iff_ne_bot.2 (hw p)

end Schema

end OrderBot

end RelationalLinks

end ConstructionMorphology
