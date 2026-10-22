/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Autosegmental.Basic

/-!
# Factors and banned-subgraph grammars

A factor occurs in a representation at per-tier offsets when its words are windows of the host's
and its lines transport shifted, Jardine's subgraph embedding in position coordinates.
Embedding is a preorder, the analogue of mathlib's `SimpleGraph.IsContained` with contiguous
tier windows. A banned-subgraph grammar is a list of forbidden factors, and a string is a
one-tier representation without lines.

## Main definitions

* `AR.IsFactorAt`, `AR.FactorEmbeds` (`⊑`): factor occurrence at given offsets, and its
  existential closure.
* `AR.Free`: avoidance of every factor of a banned-subgraph grammar.
* `AR.ofList`: a string as a one-tier representation.

## Main results

* `AR.FactorEmbeds.refl`, `AR.FactorEmbeds.trans`: embedding is a preorder.
* `AR.factorEmbeds_iff_bounded`: embedding is a bounded search over offsets.
* `AR.factorEmbeds_iff_infix_of_link_free`: for link-free factors, embedding is
  independent per-tier infix occurrence.
* `AR.factorEmbeds_ofList_iff`: one string embeds in another iff it is an infix.

## Implementation notes

Jardine's grammars ban only connected subgraphs. `IsFactorAt` places the
windows of a factor's tiers independently, so a factor with two nonempty tiers and no line
embeds whenever its tier words occur anywhere; `Free` admits such factors, and its languages
contain Jardine's.

## References

* [jardine-2017]
* [jardine-2016b]
* [jardine-2019]
-/

@[expose] public section

namespace Autosegmental

variable {ι : Type*} {τ : ι → Type*}
variable (F X : AR τ)

namespace AR

/-- `F` occurs in `X` at per-tier offsets `o`. -/
structure IsFactorAt (o : ι → ℕ) : Prop where
  /-- Each word of `F` is the window of `X`'s at the tier's offset. -/
  window : ∀ i p, p < (F.word i).length → (X.word i)[p + o i]? = (F.word i)[p]?
  /-- Lines transport by the offsets. -/
  link_map : ∀ i j p q, F.Link i j p q → X.Link i j (p + o i) (q + o j)

/-- `F` subgraph-embeds in `X` when some offsets place it as a factor
    ([jardine-2017]'s connected-subgraph embedding). -/
def FactorEmbeds : Prop := ∃ o : ι → ℕ, F.IsFactorAt X o

/-- `X` avoids every forbidden factor of a banned-subgraph grammar
    ([jardine-2016b] Ch. 5's `L^NL_G`). -/
def Free (B : List (AR τ)) : Prop := ∀ F ∈ B, ¬ F.FactorEmbeds X

variable {F X} {o : ι → ℕ}

@[simp] theorem free_nil : X.Free [] := fun _ h => (List.not_mem_nil h).elim

/-- A grammar tests its forbidden factors one by one. -/
theorem free_cons {F : AR τ} {B : List (AR τ)} :
    X.Free (F :: B) ↔ ¬ F.FactorEmbeds X ∧ X.Free B :=
  List.forall_mem_cons

/-- Factor occurrences compose, offsets adding. -/
theorem IsFactorAt.trans {Y : AR τ} {o' : ι → ℕ} (h : F.IsFactorAt X o)
    (h' : X.IsFactorAt Y o') : F.IsFactorAt Y fun i => o i + o' i where
  window i p hp := by
    have hlt : p + o i < (X.word i).length := by
      have h1 : (X.word i)[p + o i]? = some (F.word i)[p] :=
        (h.window i p hp).trans (List.getElem?_eq_getElem hp)
      exact (List.getElem?_eq_some_iff.mp h1).1
    rw [← Nat.add_assoc, h'.window i (p + o i) hlt]
    exact h.window i p hp
  link_map i j p q hl := by
    simpa [Nat.add_assoc] using h'.link_map i j _ _ (h.link_map i j p q hl)

/-- Factor embedding is transitive. -/
theorem FactorEmbeds.trans {Y : AR τ} (h : F.FactorEmbeds X) (h' : X.FactorEmbeds Y) :
    F.FactorEmbeds Y :=
  have ⟨_, h⟩ := h
  have ⟨_, h'⟩ := h'
  ⟨_, h.trans h'⟩

/-- A representation occurs in itself at offset zero. -/
theorem IsFactorAt.refl (X : AR τ) : X.IsFactorAt X 0 where
  window _ _ _ := by simp
  link_map _ _ _ _ h := by simpa using h

@[refl] theorem FactorEmbeds.refl (X : AR τ) : X.FactorEmbeds X :=
  ⟨0, IsFactorAt.refl X⟩

attribute [trans] FactorEmbeds.trans

/-- `F ⊑ X` says that `F` embeds in `X`, in the notation of mathlib's `SimpleGraph.IsContained`. -/
scoped infixl:50 " ⊑ " => FactorEmbeds

/-- On a tier where the factor is nonempty, the window equations force the offset
    in bounds. -/
theorem IsFactorAt.offset_le (h : F.IsFactorAt X o) {i : ι} (hi : (F.word i).length ≠ 0) :
    o i ≤ (X.word i).length := by
  have h0 := (h.window i 0 (Nat.pos_of_ne_zero hi)).trans
    (List.getElem?_eq_some_iff.mpr ⟨Nat.pos_of_ne_zero hi, rfl⟩)
  have := (List.getElem?_eq_some_iff.mp h0).1
  omega

/-- Offsets clamp to the host's tier lengths; the clamp only moves offsets on
    tiers where the factor is empty. -/
theorem IsFactorAt.clamp (h : F.IsFactorAt X o) :
    F.IsFactorAt X fun i => min (o i) (X.word i).length where
  window i p hp := by
    show (X.word i)[p + min (o i) (X.word i).length]? = (F.word i)[p]?
    rw [Nat.min_eq_left (h.offset_le (i := i) (by omega))]
    exact h.window i p hp
  link_map i j p q hl := by
    have hpF := hl.lt_left
    have hqF := hl.lt_right
    show X.Link i j (p + min (o i) (X.word i).length) (q + min (o j) (X.word j).length)
    rw [Nat.min_eq_left (h.offset_le (i := i) (by omega)),
      Nat.min_eq_left (h.offset_le (i := j) (by omega))]
    exact h.link_map i j p q hl

/-- `FactorEmbeds` is a bounded search over offsets. -/
theorem factorEmbeds_iff_bounded :
    F.FactorEmbeds X ↔
      ∃ o : ι → ℕ, (∀ i, o i ≤ (X.word i).length) ∧ F.IsFactorAt X o :=
  ⟨fun ⟨_, h⟩ => ⟨_, fun _ => min_le_right _ _, h.clamp⟩, fun ⟨o, _, h⟩ => ⟨o, h⟩⟩

/-- For a link-free factor, embedding reduces to independent per-tier infix
    occurrences ([jardine-2019]'s link-free fragment). -/
theorem factorEmbeds_iff_infix_of_link_free (hF : ∀ i j p q, ¬ F.Link i j p q) :
    F.FactorEmbeds X ↔ ∀ i, F.word i <:+: X.word i := by
  constructor
  · rintro ⟨o, h⟩ i
    rcases Nat.eq_zero_or_pos (F.word i).length with h0 | hpos
    · rw [List.length_eq_zero_iff.mp h0]; exact List.nil_infix
    refine List.infix_iff_getElem?.mpr ⟨o i, ?_, fun p hp ↦ ?_⟩
    · have hlast := (h.window i _ (Nat.sub_lt hpos Nat.one_pos)).trans
        (List.getElem?_eq_getElem (Nat.sub_lt hpos Nat.one_pos))
      have := (List.getElem?_eq_some_iff.mp hlast).1
      omega
    · exact (h.window i p hp).trans (List.getElem?_eq_getElem hp)
  · intro h
    choose o ho using fun i ↦ List.infix_iff_getElem?.mp (h i)
    exact ⟨o, fun i p hp ↦ ((ho i).2 p hp).trans (List.getElem?_eq_getElem hp).symm,
      fun i j p q hl ↦ absurd hl (hF i j p q)⟩

/-! ### Strings as one-tier representations -/

section OfList

variable {α : Type*}

/-- A string is a representation with one tier and no association lines. -/
def ofList (w : List α) : AR fun _ : Unit ↦ α := ⟨fun _ ↦ w, ⊥, bot_le, inferInstance⟩

@[simp] theorem word_ofList (w : List α) (i : Unit) : (ofList w).word i = w := rfl

@[simp] theorem not_link_ofList (w : List α) (i j : Unit) (p q : ℕ) :
    ¬ (ofList w).Link i j p q := fun h ↦ h.2.2

/-- One string embeds in another as a factor iff it is an infix. -/
@[simp] theorem factorEmbeds_ofList_iff (f w : List α) :
    (ofList f).FactorEmbeds (ofList w) ↔ f <:+: w := by
  rw [factorEmbeds_iff_infix_of_link_free (not_link_ofList f)]
  simp

end OfList

end AR

end Autosegmental
