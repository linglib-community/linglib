/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Lattice.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Logic.Equiv.Defs

/-!
# Element Theory

In Element Theory a segment is built from six privative elements, |A I U ʔ H L|, rather than from
binary features. A melodic expression is a set of elements, some of which are its heads, and a
segment has one expression at each of its manner, place and laryngeal nodes. Expressions are
ordered by containment, a headed element lying above its unheaded self, and they form a
distributive lattice. Its join is the union by which elements combine, so that docking a floating
expression onto a host is `host ⊔ floating`, and what a set of segments shares is their meet.

## Main definitions

* `ElementTheory.Element`, `ElementTheory.Element.gridEquiv`: the six elements, which are three
  antagonistic pairs with a dark and a light member each.
* `ElementTheory.Element.AntagonismFree`: a set of elements holding at most one of each pair.
* `ElementTheory.MR`: a melodic expression.
* `ElementTheory.Segment`: an expression at each node.
* `ElementTheory.Segment.WellFormed`: each node holds only elements that it hosts.

## Main results

* `ElementTheory.MR.simplex_lt_headedSimplex`: a headed element properly contains its unheaded
  self.
* `ElementTheory.Segment.WellFormed.sup`: docking preserves well-formedness.

## Implementation notes

* The heads of an expression are a set of its elements, so that the rival conditions on heads
  are predicates on one type. Most versions of the theory allow an expression one head,
  `m.heads.card ≤ 1`. Backley's later proposal allows one for each fundamental,
  `Element.AntagonismFree m.heads`, which the former implies
  (`Element.AntagonismFree.of_card_le_one`).
* Antagonism is a predicate and not a condition on expressions, since languages differ in which
  antagonistic pairs they let combine.
* The inventory, the pairs and the fundamentals are Backley's, and the three nodes with the
  elements they host follow Harris as Cavirani and Vanden Wyngaerd adopt them.

## References

* [backley-2011]
* [backley-2017]
* [harris-1994]
* [kaye-lowenstamm-vergnaud-1985]
* [cavirani-vandenwyngaerd-2026]
-/

@[expose] public section

namespace ElementTheory

/-! ### The six elements -/

/-- The three fundamentals of spoken language to which the elements refer. -/
inductive Fundamental
  /-- Colour, with |U| dark and |I| bright. -/
  | colour
  /-- Resonance, with |A| resonant and |ʔ| not. -/
  | resonance
  /-- Frequency, with |L| low and |H| high. -/
  | frequency
  deriving DecidableEq, Repr

/-- The two opposing values of a fundamental. -/
inductive Polarity
  | dark
  | light
  deriving DecidableEq, Repr

/-- The six privative elements. -/
inductive Element
  /-- The element |A| of aperture, a high first formant. -/
  | A
  /-- The element |I| of palatality, a high second formant. -/
  | I
  /-- The element |U| of labiality and velarity, a lowering of all formants. -/
  | U
  /-- The element |ʔ| of occlusion, an abrupt and sustained drop in amplitude. -/
  | glottal
  /-- The element |H| of noise, voicelessness and high tone, high-frequency energy. -/
  | H
  /-- The element |L| of nasality, voicing and low tone, low-frequency energy. -/
  | L
  deriving DecidableEq, Repr

namespace Element

/-- The elements are three antagonistic pairs, one for each fundamental, and each pair has a dark
and a light member. -/
def gridEquiv : Element ≃ Fundamental × Polarity where
  toFun
    | .A => (.resonance, .dark)    | .I => (.colour, .light)
    | .U => (.colour, .dark)       | .glottal => (.resonance, .light)
    | .H => (.frequency, .light)   | .L => (.frequency, .dark)
  invFun
    | (.colour, .dark) => .U       | (.colour, .light) => .I
    | (.resonance, .dark) => .A    | (.resonance, .light) => .glottal
    | (.frequency, .dark) => .L    | (.frequency, .light) => .H
  left_inv e := by cases e <;> rfl
  right_inv := by rintro ⟨f, p⟩; cases f <;> cases p <;> rfl

/-- The fundamental to which an element refers. -/
def fundamental (e : Element) : Fundamental := (gridEquiv e).1

/-- The value that an element marks on its fundamental. -/
def polarity (e : Element) : Polarity := (gridEquiv e).2

/-- A set of elements is antagonism-free if it holds at most one element of each antagonistic
pair. -/
def AntagonismFree (s : Finset Element) : Prop := Set.InjOn fundamental ↑s

instance (s : Finset Element) : Decidable (AntagonismFree s) :=
  inferInstanceAs (Decidable (Set.InjOn _ _))

theorem AntagonismFree.subset {s t : Finset Element} (ht : AntagonismFree t) (h : s ⊆ t) :
    AntagonismFree s :=
  Set.InjOn.mono (Finset.coe_subset.2 h) ht

theorem AntagonismFree.of_card_le_one {s : Finset Element} (h : s.card ≤ 1) : AntagonismFree s :=
  fun a ha b hb _ ↦ Finset.card_le_one.1 h a ha b hb

end Element

/-! ### Melodic expressions -/

/-- A melodic expression is a set of elements, some of which are its heads. -/
@[ext]
structure MR where
  /-- The elements of the expression. -/
  elements : Finset Element
  /-- The heads of the expression. -/
  heads : Finset Element
  /-- The heads are among the elements. -/
  heads_subset : heads ⊆ elements

namespace MR

variable {m m₁ m₂ : MR} {e e' : Element}

/-- An expression as the pair of its elements and its heads. -/
def toProd (m : MR) : Finset Element × Finset Element := (m.elements, m.heads)

theorem toProd_injective : Function.Injective toProd :=
  fun _ _ h ↦ MR.ext (congrArg Prod.fst h) (congrArg Prod.snd h)

instance : DecidableEq MR := toProd_injective.decidableEq

instance : LE MR := ⟨fun m₁ m₂ ↦ m₁.elements ⊆ m₂.elements ∧ m₁.heads ⊆ m₂.heads⟩

instance : LT MR := ⟨fun m₁ m₂ ↦ m₁ ≤ m₂ ∧ ¬ m₂ ≤ m₁⟩

theorem le_def : m₁ ≤ m₂ ↔ m₁.elements ⊆ m₂.elements ∧ m₁.heads ⊆ m₂.heads := .rfl

instance : DecidableLE MR := fun _ _ ↦ decidable_of_iff' _ le_def

instance : DecidableLT MR := fun _ _ ↦ inferInstanceAs (Decidable (_ ∧ _))

instance : Max MR :=
  ⟨fun m₁ m₂ ↦ ⟨m₁.elements ∪ m₂.elements, m₁.heads ∪ m₂.heads,
    Finset.union_subset_union m₁.heads_subset m₂.heads_subset⟩⟩

instance : Min MR :=
  ⟨fun m₁ m₂ ↦ ⟨m₁.elements ∩ m₂.elements, m₁.heads ∩ m₂.heads,
    Finset.inter_subset_inter m₁.heads_subset m₂.heads_subset⟩⟩

instance : DistribLattice MR :=
  toProd_injective.distribLattice _ .rfl .rfl (fun _ _ ↦ rfl) fun _ _ ↦ rfl

/-- The empty expression is least. -/
instance : OrderBot MR where
  bot := ⟨∅, ∅, subset_rfl⟩
  bot_le _ := ⟨Finset.empty_subset _, Finset.empty_subset _⟩

@[simp] theorem sup_elements (m₁ m₂ : MR) : (m₁ ⊔ m₂).elements = m₁.elements ∪ m₂.elements := rfl

@[simp] theorem sup_heads (m₁ m₂ : MR) : (m₁ ⊔ m₂).heads = m₁.heads ∪ m₂.heads := rfl

@[simp] theorem inf_elements (m₁ m₂ : MR) : (m₁ ⊓ m₂).elements = m₁.elements ∩ m₂.elements := rfl

@[simp] theorem inf_heads (m₁ m₂ : MR) : (m₁ ⊓ m₂).heads = m₁.heads ∩ m₂.heads := rfl

@[simp] theorem bot_elements : (⊥ : MR).elements = ∅ := rfl

@[simp] theorem bot_heads : (⊥ : MR).heads = ∅ := rfl

/-- The simplex expression |e| is the element `e` alone, unheaded. -/
def simplex (e : Element) : MR := ⟨{e}, ∅, Finset.empty_subset _⟩

/-- The headed simplex expression is the element `e` alone, as head. -/
def headedSimplex (e : Element) : MR := ⟨{e}, {e}, subset_rfl⟩

@[simp] theorem simplex_elements (e : Element) : (simplex e).elements = {e} := rfl

@[simp] theorem simplex_heads (e : Element) : (simplex e).heads = ∅ := rfl

@[simp] theorem headedSimplex_elements (e : Element) : (headedSimplex e).elements = {e} := rfl

@[simp] theorem headedSimplex_heads (e : Element) : (headedSimplex e).heads = {e} := rfl

@[simp] theorem simplex_le_iff : simplex e ≤ m ↔ e ∈ m.elements := by simp [le_def]

@[simp] theorem headedSimplex_le_iff : headedSimplex e ≤ m ↔ e ∈ m.heads := by
  simpa [le_def] using fun h ↦ m.heads_subset h

theorem simplex_lt_headedSimplex (e : Element) : simplex e < headedSimplex e :=
  ⟨by simp, by simp [le_def]⟩

end MR

/-! ### Segments -/

/-- A segment has a melodic expression at each of its manner, place and laryngeal nodes, empty
unless given. -/
@[ext]
structure Segment where
  /-- The expression at the manner node. -/
  manner : MR := ⊥
  /-- The expression at the place node. -/
  place : MR := ⊥
  /-- The expression at the laryngeal node. -/
  laryngeal : MR := ⊥

namespace Segment

variable {s s₁ s₂ : Segment}

/-- A segment as the triple of the expressions at its nodes. -/
def toProd (s : Segment) : MR × MR × MR := (s.manner, s.place, s.laryngeal)

theorem toProd_injective : Function.Injective toProd :=
  fun _ _ h ↦ Segment.ext (congrArg Prod.fst h) (congrArg (·.2.1) h) (congrArg (·.2.2) h)

instance : DecidableEq Segment := toProd_injective.decidableEq

instance : LE Segment :=
  ⟨fun s₁ s₂ ↦ s₁.manner ≤ s₂.manner ∧ s₁.place ≤ s₂.place ∧ s₁.laryngeal ≤ s₂.laryngeal⟩

instance : LT Segment := ⟨fun s₁ s₂ ↦ s₁ ≤ s₂ ∧ ¬ s₂ ≤ s₁⟩

theorem le_def :
    s₁ ≤ s₂ ↔ s₁.manner ≤ s₂.manner ∧ s₁.place ≤ s₂.place ∧ s₁.laryngeal ≤ s₂.laryngeal := .rfl

instance : DecidableLE Segment := fun _ _ ↦ decidable_of_iff' _ le_def

instance : DecidableLT Segment := fun _ _ ↦ inferInstanceAs (Decidable (_ ∧ _))

instance : Max Segment :=
  ⟨fun s₁ s₂ ↦ ⟨s₁.manner ⊔ s₂.manner, s₁.place ⊔ s₂.place, s₁.laryngeal ⊔ s₂.laryngeal⟩⟩

instance : Min Segment :=
  ⟨fun s₁ s₂ ↦ ⟨s₁.manner ⊓ s₂.manner, s₁.place ⊓ s₂.place, s₁.laryngeal ⊓ s₂.laryngeal⟩⟩

instance : DistribLattice Segment :=
  toProd_injective.distribLattice _ .rfl .rfl (fun _ _ ↦ rfl) fun _ _ ↦ rfl

/-- The segment with every node empty is least. -/
instance : OrderBot Segment where
  bot := {}
  bot_le _ := ⟨bot_le, bot_le, bot_le⟩

@[simp] theorem sup_manner (s₁ s₂ : Segment) : (s₁ ⊔ s₂).manner = s₁.manner ⊔ s₂.manner := rfl

@[simp] theorem sup_place (s₁ s₂ : Segment) : (s₁ ⊔ s₂).place = s₁.place ⊔ s₂.place := rfl

@[simp] theorem sup_laryngeal (s₁ s₂ : Segment) :
    (s₁ ⊔ s₂).laryngeal = s₁.laryngeal ⊔ s₂.laryngeal := rfl

@[simp] theorem inf_manner (s₁ s₂ : Segment) : (s₁ ⊓ s₂).manner = s₁.manner ⊓ s₂.manner := rfl

@[simp] theorem inf_place (s₁ s₂ : Segment) : (s₁ ⊓ s₂).place = s₁.place ⊓ s₂.place := rfl

@[simp] theorem inf_laryngeal (s₁ s₂ : Segment) :
    (s₁ ⊓ s₂).laryngeal = s₁.laryngeal ⊓ s₂.laryngeal := rfl

@[simp] theorem bot_manner : (⊥ : Segment).manner = ⊥ := rfl

@[simp] theorem bot_place : (⊥ : Segment).place = ⊥ := rfl

@[simp] theorem bot_laryngeal : (⊥ : Segment).laryngeal = ⊥ := rfl

/-! ### Well-formedness -/

/-- A segment is well-formed if each node holds only elements that it hosts: |ʔ H L A| at the
manner node, |I U A| at the place node and |L H| at the laryngeal node. -/
def WellFormed (s : Segment) : Prop :=
  s.manner.elements ⊆ {Element.glottal, .H, .L, .A} ∧ s.place.elements ⊆ {Element.I, .U, .A} ∧
    s.laryngeal.elements ⊆ {Element.L, .H}

instance : DecidablePred WellFormed := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem wellFormed_bot : WellFormed ⊥ := by simp [WellFormed]

theorem WellFormed.sup (h₁ : s₁.WellFormed) (h₂ : s₂.WellFormed) : (s₁ ⊔ s₂).WellFormed :=
  ⟨Finset.union_subset h₁.1 h₂.1, Finset.union_subset h₁.2.1 h₂.2.1,
    Finset.union_subset h₁.2.2 h₂.2.2⟩

end Segment

end ElementTheory
