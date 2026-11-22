/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Basic.Rel
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Fintype.Card

/-!
# Correspondences

A correspondence between two structures is a finite relation $ℜ$ between their positions. We
define `Correspondence ι κ` as `Finset (ι × κ)`, with the relation `Correspondence.rel` it
denotes, its converse `Correspondence.inv`, the composite `Correspondence.comp` of two
correspondences, and the correspondence `Correspondence.graph f` of a map of positions.

## Implementation notes

A `Correspondence ι κ` is a `Finset (ι × κ)` for any two position types, as mathlib's `SetRel`
is a `Set`, so that violation counts compute; `Correspondence.rel` is the same relation as a
`SetRel`, in whose vocabulary the characterizations are stated. The positions of a list are
`Fin` of its length.

## References

* [J. J. McCarthy and A. Prince, *Faithfulness and Reduplicative Identity*
  (1995)][mccarthy-prince-1995]
* [A. Payne, M. H. Vu and J. Heinz, *A Formal Analysis of Correspondence Theory*
  (2017)][payne-vu-heinz-2017]
-/

@[expose] public section

namespace OptimalityTheory

/-- A *correspondence* between two position types is a finite relation between them. -/
abbrev Correspondence (ι κ : Type*) := Finset (ι × κ)

namespace Correspondence

open scoped SetRel

variable {ι κ μ : Type*}

/-! ### The relation, its converse, and composition -/

/-- `R.rel` is the correspondence `R` as a `SetRel`. -/
def rel (R : Correspondence ι κ) : SetRel ι κ := (↑R : Set (ι × κ))

@[simp] theorem mem_rel {R : Correspondence ι κ} {i : ι} {j : κ} : i ~[R.rel] j ↔ (i, j) ∈ R :=
  Iff.rfl

theorem rel_injective : Function.Injective (rel : Correspondence ι κ → SetRel ι κ) :=
  Finset.coe_injective

/-- `R.inv` is the converse of the correspondence `R`. -/
def inv (R : Correspondence ι κ) : Correspondence κ ι := R.map (Equiv.prodComm ι κ).toEmbedding

@[simp] theorem mem_inv {R : Correspondence ι κ} {i : ι} {j : κ} : (j, i) ∈ R.inv ↔ (i, j) ∈ R := by
  simp [inv]

@[simp] theorem inv_inv (R : Correspondence ι κ) : R.inv.inv = R := by
  ext ⟨i, j⟩; simp

@[simp] theorem inv_empty : (∅ : Correspondence ι κ).inv = ∅ := rfl

theorem inv_injective : Function.Injective (inv : Correspondence ι κ → Correspondence κ ι) :=
  Function.LeftInverse.injective inv_inv

@[simp] theorem rel_inv (R : Correspondence ι κ) : R.inv.rel = R.rel.inv := by
  ext ⟨j, i⟩; simp

theorem card_filter_inv (R : Correspondence ι κ) (q : κ × ι → Prop) [DecidablePred q] :
    (R.inv.filter q).card = (R.filter fun p ↦ q p.swap).card := by
  rw [inv, Finset.filter_map, Finset.card_map]
  rfl

theorem image_fst_inv [DecidableEq κ] (R : Correspondence ι κ) :
    R.inv.image Prod.fst = R.image Prod.snd := by
  ext j; simp

theorem dom_rel [DecidableEq ι] (R : Correspondence ι κ) : R.rel.dom = ↑(R.image Prod.fst) := by
  ext i; simp

theorem cod_rel [DecidableEq κ] (R : Correspondence ι κ) : R.rel.cod = ↑(R.image Prod.snd) := by
  ext j; simp

section comp

variable [DecidableEq ι] [DecidableEq κ] [DecidableEq μ]

/-- `R.comp S` relates `i` to `k` when `R` relates `i` to some `j` that `S` relates to `k`. -/
def comp (R : Correspondence ι κ) (S : Correspondence κ μ) : Correspondence ι μ :=
  ((R ×ˢ S).filter fun p ↦ p.1.2 = p.2.1).image fun p ↦ (p.1.1, p.2.2)

@[simp] theorem mem_comp {R : Correspondence ι κ} {S : Correspondence κ μ} {i : ι} {k : μ} :
    (i, k) ∈ R.comp S ↔ ∃ j, (i, j) ∈ R ∧ (j, k) ∈ S := by
  simp only [comp, Finset.mem_image, Finset.mem_filter, Finset.mem_product, Prod.exists,
    Prod.mk.injEq]
  constructor
  · rintro ⟨a, b, b', c, ⟨⟨h₁, h₂⟩, rfl⟩, rfl, rfl⟩
    exact ⟨_, h₁, h₂⟩
  · rintro ⟨j, h₁, h₂⟩
    exact ⟨i, j, j, k, ⟨⟨h₁, h₂⟩, rfl⟩, rfl, rfl⟩

@[simp] theorem rel_comp (R : Correspondence ι κ) (S : Correspondence κ μ) :
    (R.comp S).rel = R.rel ○ S.rel := by
  ext ⟨i, k⟩; simp

theorem inv_comp (R : Correspondence ι κ) (S : Correspondence κ μ) :
    (R.comp S).inv = S.inv.comp R.inv :=
  rel_injective <| by simp [SetRel.inv_comp]

theorem comp_assoc {ν : Type*} [DecidableEq ν] (R : Correspondence ι κ) (S : Correspondence κ μ)
    (T : Correspondence μ ν) : (R.comp S).comp T = R.comp (S.comp T) :=
  rel_injective <| by simp [SetRel.comp_assoc]

end comp

/-- `graph f` is the correspondence in which each position `i` has the single correspondent
`f i`. -/
def graph [Fintype ι] (f : ι → κ) : Correspondence ι κ :=
  Finset.univ.map ⟨fun i ↦ (i, f i), fun _ _ h ↦ congrArg Prod.fst h⟩

@[simp] theorem mem_graph [Fintype ι] {f : ι → κ} {i : ι} {j : κ} : (i, j) ∈ graph f ↔ f i = j := by
  simp [graph, eq_comm]

@[simp] theorem rel_graph [Fintype ι] (f : ι → κ) : (graph f).rel = Function.graph f :=
  Set.ext fun _ ↦ mem_graph

theorem mem_iff_of_graph {R : Correspondence ι κ} {f : ι → κ} (hf : R.rel = Function.graph f)
    {i : ι} {j : κ} : (i, j) ∈ R ↔ f i = j := by
  rw [← mem_rel, hf, Function.mem_graph]

end Correspondence

end OptimalityTheory
