/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Autosegmental.TwoTier

/-!
# Morphs

In a theory of morphologically conditioned phonology each tier element is sponsored by a
morpheme, and the labels of a two-tier representation are `Sponsored` autosegments and slots.
A morph, the material that the morphology inserts as the exponent of one morpheme and cannot
alter, is a representation with one sponsor. Unlike Haspelmath's segmental morph it may be a
floating tone or feature alone, and a word's underlying form is the product of its morphs.

## References

* [goldsmith-1976]
* [bermudez-otero-2012]
* [bye-svenonius-2012]
* [zimmermann-2024]
* [lieber-1983]
* [wolf-2007]
* [zimmermann-2017]
* [pulleyblank-1986]
* [rolle-2018]
* [mccarthy-mullin-smith-2012]
* [mcpherson-lamont-2026]
* [laoide-kemp-2026]
* [jardine-heinz-2015]
* [jardine-2016b]
* [jardine-2019]
-/

@[expose] public section

namespace Autosegmental

/-- A `Sponsored α M` is a tier element of type `α` together with the morpheme of type `M`
that sponsors it. On the upper tier the element is an autosegment, on the lower tier a
slot. -/
structure Sponsored (α M : Type*) where
  /-- The autosegment or slot. -/
  value : α
  /-- The sponsoring morpheme. -/
  morpheme : M
  deriving DecidableEq, Repr

/-- The element relabeled by `φ`, with the same sponsor. -/
def Sponsored.map {α β M : Type*} (φ : α → β) (x : Sponsored α M) : Sponsored β M :=
  ⟨φ x.value, x.morpheme⟩

@[simp] theorem Sponsored.value_map {α β M : Type*} (φ : α → β) (x : Sponsored α M) :
    (x.map φ).value = φ x.value := rfl

@[simp] theorem Sponsored.morpheme_map {α β M : Type*} (φ : α → β) (x : Sponsored α M) :
    (x.map φ).morpheme = x.morpheme := rfl

namespace AR

open Tier

/-! ### Morphemes -/

section Sponsor

universe u
variable {S T M : Type u} (X : AR (TwoTier (Sponsored T M) (Sponsored S M)))

/-- `morphemes X` is the set of morphemes sponsoring an element of either tier. -/
def morphemes [DecidableEq M] : Finset M :=
  ((X.word lower).map Sponsored.morpheme).toFinset ∪
    ((X.word upper).map Sponsored.morpheme).toFinset

/-- `lowerOfMorpheme X m` lists the slots sponsored by `m` in tier order. -/
def lowerOfMorpheme [DecidableEq M] (m : M) : List (Fin (X.word lower).length) :=
  (List.finRange (X.word lower).length).filter fun i ↦ (X.word lower)[i].morpheme = m

@[simp] theorem mem_lowerOfMorpheme [DecidableEq M] {m : M} {i : Fin (X.word lower).length} :
    i ∈ X.lowerOfMorpheme m ↔ (X.word lower)[i].morpheme = m := by
  simp [lowerOfMorpheme]

/-- A line is tautomorphemic when its autosegment and its slot have the same sponsor. Such
lines are the ones `*TAUTDOCK` penalises. -/
def IsTautomorphemic (l : Fin (X.word upper).length × Fin (X.word lower).length) : Prop :=
  (X.word upper)[l.1].morpheme = (X.word lower)[l.2].morpheme

instance [DecidableEq M] (l : Fin (X.word upper).length × Fin (X.word lower).length) :
    Decidable (X.IsTautomorphemic l) :=
  inferInstanceAs (Decidable (_ = _))

/-! ### Morphs -/

variable (m : M) (us : List T) (ls : List S) (lines : Finset (ℕ × ℕ))

/-- `morph m us ls lines` is the morph of the morpheme `m`: the autosegments `us` over
the slots `ls`, all sponsored by `m`, with a line for each pair in `lines` of a position of
`us` and a position of `ls`. It is [bermudez-otero-2012]'s morph (p. 50), a piece of
phonological material that the morphology concatenates and cannot alter. In [rolle-2018]'s
typology of underlying tone (Table 1, p. 16), a slot with a line is valued, one without is
unvalued, and an autosegment without a line floats. Harmonic serialism under richness of the base
takes `lines` empty in every language ([mccarthy-mullin-smith-2012], p. 285), while a stratal
phonology hands partially linked morphs, such as the Poko stem /Mᴴ/, to the postlexical level
([mcpherson-lamont-2026], (3) and p. 5). -/
def morph : AR (TwoTier (Sponsored T M) (Sponsored S M)) :=
  ofLines (us.map (⟨·, m⟩)) (ls.map (⟨·, m⟩)) lines

@[simp] theorem word_morph_upper : (morph m us ls lines).word upper = us.map (⟨·, m⟩) := rfl

@[simp] theorem word_morph_lower : (morph m us ls lines).word lower = ls.map (⟨·, m⟩) := rfl

/-- The lines of a morph are the given pairs within range of its tiers. -/
@[simp] theorem lines_morph : (morph m us ls lines).lines upper lower =
    lines.filter fun p ↦ p.1 < us.length ∧ p.2 < ls.length := by
  simp [morph]

variable {m us ls lines} in
@[simp] theorem mem_links_morph {p : Fin ((morph m us ls lines).word upper).length ×
    Fin ((morph m us ls lines).word lower).length} :
    p ∈ (morph m us ls lines).links upper lower ↔ (p.1.val, p.2.val) ∈ lines := by
  rw [mem_links, lines_morph, Finset.mem_filter, and_iff_left_iff_imp]
  exact fun _ ↦ ⟨by simpa using p.1.isLt, by simpa using p.2.isLt⟩

@[simp] theorem links_morph_empty : (morph m us ls ∅).links upper lower = ∅ :=
  Finset.eq_empty_of_forall_notMem fun _ h ↦ Finset.notMem_empty _ (mem_links_morph.1 h)

end Sponsor

end AR

end Autosegmental
