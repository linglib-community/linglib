/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Autosegmental.Basic

/-!
# Factors and banned-subgraph grammars

A factor occurs in a representation at per-tier offsets when each of its words begins the host's
word at the tier's offset and its lines are lines of the host there, Jardine's subgraph embedding
in position coordinates. Embedding [is a preorder](##Autosegmental.AR.FactorEmbeds.trans), the
analogue of mathlib's `SimpleGraph.IsContained` with contiguous tier windows, and both factors of
a concatenation [embed in it](##Autosegmental.AR.factorEmbeds_mul_left). A banned-subgraph
grammar is a list of forbidden factors, and what embeds in a representation free of a grammar
[is free of it](##Autosegmental.AR.Free.of_factorEmbeds). A factor without lines embeds exactly
when [each of its words is an infix](##Autosegmental.AR.factorEmbeds_iff_infix_of_link_free) of
the host's, so that on strings, the one-tier representations without lines, embedding
[is the infix order](##Autosegmental.AR.factorEmbeds_ofList_iff).

## Implementation notes

Two choices separate `AR.FactorEmbeds` from the connected subgraphs that [jardine-2019] bans.

* `IsFactorAt` places the windows of a factor's tiers independently, so a factor with two
  nonempty tiers and no line embeds whenever its tier words occur anywhere. Jardine's grammars
  ban only connected subgraphs; `Free` admits unconnected factors as well.
* A factor's tier is a word, so its positions are consecutive in the host and carry every
  successor arc between them. A subgraph in Jardine's sense may leave out arcs of the host, as
  it may leave out lines, so that two nodes of one tier with no arc between them embed at any
  distance; such a subgraph is not a factor.

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
  /-- Each word of `F` begins the word of `X` at the tier's offset. -/
  window : ∀ i, F.word i <+: (X.word i).drop (o i)
  /-- Lines transport by the offsets. -/
  link_map : ∀ i j p q, F.Link i j p q → X.Link i j (p + o i) (q + o j)

/-- `F` subgraph-embeds in `X` when some offsets place it as a factor
    ([jardine-2017]'s connected-subgraph embedding). -/
def FactorEmbeds : Prop := ∃ o : ι → ℕ, F.IsFactorAt X o

/-- `X` avoids every forbidden factor of a banned-subgraph grammar
    ([jardine-2016b] Ch. 5's `L^NL_G`). -/
def Free (B : List (AR τ)) : Prop := ∀ F ∈ B, ¬ F.FactorEmbeds X

/-- `F ⊑ X` says that `F` embeds in `X`, in the notation of mathlib's `SimpleGraph.IsContained`. -/
scoped infixl:50 " ⊑ " => FactorEmbeds

variable {F X} {Y : AR τ} {o o' : ι → ℕ} {B : List (AR τ)}

/-! ### Occurrences at given offsets -/

/-- A representation occurs in itself at offset zero. -/
theorem IsFactorAt.refl (X : AR τ) : X.IsFactorAt X 0 where
  window _ := by simp
  link_map _ _ _ _ h := by simpa using h

/-- Factor occurrences compose, offsets adding. -/
theorem IsFactorAt.trans (h : F.IsFactorAt X o) (h' : X.IsFactorAt Y o') :
    F.IsFactorAt Y (o + o') where
  window i := (h.window i).trans <| by
    simpa [List.drop_drop, Nat.add_comm] using (h'.window i).drop (o i)
  link_map i j p q hl := by
    simpa [Nat.add_assoc] using h'.link_map i j _ _ (h.link_map i j p q hl)

/-- The left factor of a concatenation occurs in it at offset zero. -/
theorem isFactorAt_mul_right (X Y : AR τ) : X.IsFactorAt (X * Y) 0 where
  window _ := by simp
  link_map i j p q h := by simpa using (link_mul i j p q).2 (.inl h)

/-- The right factor of a concatenation occurs in it past the words of the left one. -/
theorem isFactorAt_mul_left (X Y : AR τ) : Y.IsFactorAt (X * Y) fun i ↦ (X.word i).length where
  window _ := by simp
  link_map i j p q h := (link_mul i j _ _).2 <| .inr ⟨by omega, by omega, by simpa using h⟩

/-- A nonempty word of a factor fits in the host's word past the offset. -/
theorem IsFactorAt.length_add_le (h : F.IsFactorAt X o) (i : ι) (hi : F.word i ≠ []) :
    (F.word i).length + o i ≤ (X.word i).length := by
  have := (h.window i).length_le
  have := List.length_pos_iff.2 hi
  rw [List.length_drop] at *
  omega

theorem IsFactorAt.offset_le (h : F.IsFactorAt X o) {i : ι} (hi : F.word i ≠ []) :
    o i ≤ (X.word i).length :=
  (Nat.le_add_left _ _).trans (h.length_add_le i hi)

theorem IsFactorAt.clamp (h : F.IsFactorAt X o) :
    F.IsFactorAt X fun i ↦ min (o i) (X.word i).length where
  window i := by
    rcases le_total (o i) (X.word i).length with hi | hi
    · rw [Nat.min_eq_left hi]
      exact h.window i
    · rw [Nat.min_eq_right hi, List.drop_length, ← List.drop_eq_nil_of_le hi]
      exact h.window i
  link_map i j p q hl := by
    rw [Nat.min_eq_left (h.offset_le (List.ne_nil_of_length_pos (Nat.zero_lt_of_lt hl.lt_left))),
      Nat.min_eq_left (h.offset_le (List.ne_nil_of_length_pos (Nat.zero_lt_of_lt hl.lt_right)))]
    exact h.link_map i j p q hl

/-! ### Embedding -/

@[refl] theorem FactorEmbeds.refl (X : AR τ) : X ⊑ X := ⟨0, .refl X⟩

/-- Factor embedding is transitive. -/
@[trans] theorem FactorEmbeds.trans : F ⊑ X → X ⊑ Y → F ⊑ Y := fun ⟨_, h⟩ ⟨_, h'⟩ ↦ ⟨_, h.trans h'⟩

instance : IsPreorder (AR τ) FactorEmbeds where
  refl := .refl
  trans _ _ _ := .trans

theorem factorEmbeds_mul_right (X Y : AR τ) : X ⊑ X * Y := ⟨_, isFactorAt_mul_right X Y⟩

/-- Both factors of a concatenation embed in it. -/
theorem factorEmbeds_mul_left (X Y : AR τ) : Y ⊑ X * Y := ⟨_, isFactorAt_mul_left X Y⟩

/-- `FactorEmbeds` is a bounded search over offsets. -/
theorem factorEmbeds_iff_bounded :
    F ⊑ X ↔ ∃ o : ι → ℕ, (∀ i, o i ≤ (X.word i).length) ∧ F.IsFactorAt X o :=
  ⟨fun ⟨_, h⟩ ↦ ⟨_, fun _ ↦ min_le_right _ _, h.clamp⟩, fun ⟨o, _, h⟩ ↦ ⟨o, h⟩⟩

/-- For a link-free factor, embedding reduces to independent per-tier infix
    occurrences ([jardine-2019]'s link-free fragment). -/
theorem factorEmbeds_iff_infix_of_link_free (hF : ∀ i j p q, ¬ F.Link i j p q) :
    F ⊑ X ↔ ∀ i, F.word i <:+: X.word i := by
  refine ⟨fun ⟨o, h⟩ i ↦ (h.window i).isInfix.trans (List.drop_suffix _ _).isInfix, fun h ↦ ?_⟩
  choose t ht using fun i ↦ List.infix_iff_prefix_suffix.1 (h i)
  exact ⟨fun i ↦ (X.word i).length - (t i).length,
    fun i ↦ List.suffix_iff_eq_drop.1 (ht i).2 ▸ (ht i).1, fun i j p q hl ↦ absurd hl (hF i j p q)⟩

/-! ### Grammars -/

@[simp] theorem free_nil : X.Free [] := fun _ h ↦ (List.not_mem_nil h).elim

theorem free_cons : X.Free (F :: B) ↔ ¬ F ⊑ X ∧ X.Free B :=
  List.forall_mem_cons

/-- What embeds in a representation free of a grammar is free of it. -/
theorem Free.of_factorEmbeds (hY : Y.Free B) (h : X ⊑ Y) : X.Free B :=
  fun F hF hFX ↦ hY F hF (hFX.trans h)

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
