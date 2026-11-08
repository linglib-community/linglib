/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Autosegmental.TwoTier
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fin.Embedding

/-!
# Forms and morphs

This file defines forms, two-tier autosegmental representations in position coordinates: an
upper tier of autosegments over a lower tier of slots, each element sponsored by a morpheme, with
a finite set of association lines between the tiers. Forms concatenate by juxtaposing the tiers,
and presentation as a representation is a monoid hom, so the No-Crossing Constraint on the lines
is the constraint on the representation. A morph, the material that the morphology inserts as
the exponent of one morpheme and cannot alter, is a form with one sponsor. Unlike Haspelmath's
segmental morph it may be a floating tone or feature alone, and a word's underlying form is the
product of its morphs.

## Main definitions

* `Sponsored α M`: a tier element with the morpheme that sponsors it.
* `Form S T M`: a representation with slots in `S`, autosegments in `T`, and sponsors in `M`;
  `Form.concat` and `Form.empty` make the forms a monoid.
* `Form.links`: the lines of a form as pairs of its positions, which candidates edit.
* `Form.morph`: the morph of a morpheme, from its autosegments, its slots, and its lines.
* `Form.IsTautomorphemic`: a line whose autosegment and slot share a sponsor.
* `Form.toAR`: the representation a form presents, through `AR.ofWords`.

## Main results

* `Form.noCrossing_toAR_iff`: the presented representation obeys the NCC iff the lines are
  non-crossing.
* `Form.toARHom`: presentation is a monoid hom from forms to representations.
* `Form.isNonCrossing_lines_concat`: concatenation preserves the No-Crossing Constraint.

## Implementation notes

A form stores its lines as pairs of natural numbers with a proof that they are in range, as a
`Finset` stores a multiset with a proof that it has no duplicates, so concatenation is a union
and a shift. `Form.links` views the lines as pairs of positions in `Fin` over the tier lengths,
whose numerals need a `NeZero` instance that a study supplies by `decide`. `Form.morph` drops the
pairs out of range, as `SimpleGraph.fromEdgeSet` drops loops. `Form.toAR` needs the three label
types in one universe, as `TwoTier` does.

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

/-- A `Form S T M` is a two-tier autosegmental representation with slots in `S`, autosegments
in `T`, and sponsors in `M`. Its association lines are pairs of a position of the upper tier
and a position of the lower tier. -/
@[ext] structure Form (S T M : Type*) where
  /-- The upper tier, of autosegments in tier order. -/
  upper : List (Sponsored T M)
  /-- The lower tier, of slots in tier order. -/
  lower : List (Sponsored S M)
  /-- The association lines, each from a position of the upper tier to one of the lower. -/
  lines : Finset (ℕ × ℕ)
  lt_of_mem_lines {p : ℕ × ℕ} : p ∈ lines → p.1 < upper.length ∧ p.2 < lower.length

namespace Form

variable {S T M : Type*} (f g : Form S T M)

instance [DecidableEq S] [DecidableEq T] [DecidableEq M] : DecidableEq (Form S T M) :=
  fun _ _ ↦ decidable_of_iff _ Form.ext_iff.symm

/-- The lines of a form as pairs of its positions, the view that candidates edit. -/
def links : Finset (Fin f.upper.length × Fin f.lower.length) :=
  Finset.univ.filter fun p ↦ (p.1.val, p.2.val) ∈ f.lines

variable {f} in
@[simp] theorem mem_links {p : Fin f.upper.length × Fin f.lower.length} :
    p ∈ f.links ↔ (p.1.val, p.2.val) ∈ f.lines := by
  simp [links]

theorem map_links : f.links.map (Fin.valEmbedding.prodMap Fin.valEmbedding) = f.lines := by
  ext ⟨a, b⟩
  simp only [Finset.mem_map, mem_links, Function.Embedding.prodMap, Prod.exists,
    Function.Embedding.coeFn_mk, Prod.map, Fin.valEmbedding_apply, Prod.mk.injEq]
  constructor
  · rintro ⟨k, i, h, rfl, rfl⟩
    exact h
  · intro h
    exact ⟨⟨a, (f.lt_of_mem_lines h).1⟩, ⟨b, (f.lt_of_mem_lines h).2⟩, h, rfl, rfl⟩

theorem isNonCrossing_lines_iff :
    IsNonCrossing (f.lines : SetRel ℕ ℕ) ↔
      IsNonCrossing (f.links : SetRel (Fin f.upper.length) (Fin f.lower.length)) := by
  rw [← map_links, Finset.coe_map, isNonCrossing_image]
  rfl

/-! ### Morphemes -/

/-- `morphemes f` is the set of morphemes sponsoring an element of either tier. -/
def morphemes [DecidableEq M] : Finset M :=
  (f.lower.map Sponsored.morpheme).toFinset ∪ (f.upper.map Sponsored.morpheme).toFinset

/-- `lowerOfMorpheme f m` lists the slots sponsored by `m` in tier order. -/
def lowerOfMorpheme [DecidableEq M] (m : M) : List (Fin f.lower.length) :=
  (List.finRange f.lower.length).filter fun i ↦ f.lower[i].morpheme = m

@[simp] theorem mem_lowerOfMorpheme [DecidableEq M] {m : M} {i : Fin f.lower.length} :
    i ∈ f.lowerOfMorpheme m ↔ f.lower[i].morpheme = m := by
  simp [lowerOfMorpheme]

/-- A line is tautomorphemic when its autosegment and its slot have the same sponsor. Such
lines are the ones `*TAUTDOCK` penalises. -/
def IsTautomorphemic (l : Fin f.upper.length × Fin f.lower.length) : Prop :=
  f.upper[l.1].morpheme = f.lower[l.2].morpheme

instance [DecidableEq M] (l : Fin f.upper.length × Fin f.lower.length) :
    Decidable (f.IsTautomorphemic l) :=
  inferInstanceAs (Decidable (_ = _))

/-! ### Concatenation

Concatenation juxtaposes the tiers and shifts the right factor's lines past the left factor's
tiers, so the forms are a monoid with the empty form as unit. -/

/-- `shift a b` moves a line `a` positions along the upper tier and `b` along the lower. -/
def shift (a b : ℕ) : ℕ × ℕ ↪ ℕ × ℕ := (addLeftEmbedding a).prodMap (addLeftEmbedding b)

@[simp] theorem shift_apply (a b : ℕ) (p : ℕ × ℕ) : shift a b p = (a + p.1, b + p.2) := rfl

/-- `concat f g` juxtaposes the tiers of `f` and `g` and shifts the lines of `g` past the tiers
of `f`. -/
def concat : Form S T M where
  upper := f.upper ++ g.upper
  lower := f.lower ++ g.lower
  lines := f.lines ∪ g.lines.map (shift f.upper.length f.lower.length)
  lt_of_mem_lines {p} hp := by
    simp only [Finset.mem_union, Finset.mem_map] at hp
    rcases hp with hp | ⟨q, hq, rfl⟩
    · have := f.lt_of_mem_lines hp
      simp only [List.length_append]
      omega
    · have := g.lt_of_mem_lines hq
      simp only [shift_apply, List.length_append]
      omega

/-- The empty form has empty tiers and no lines. -/
def empty : Form S T M := ⟨[], [], ∅, nofun⟩

@[simp] theorem concat_upper : (f.concat g).upper = f.upper ++ g.upper := rfl

@[simp] theorem concat_lower : (f.concat g).lower = f.lower ++ g.lower := rfl

@[simp] theorem concat_lines :
    (f.concat g).lines = f.lines ∪ g.lines.map (shift f.upper.length f.lower.length) := rfl

@[simp] theorem empty_upper : (empty : Form S T M).upper = [] := rfl

@[simp] theorem empty_lower : (empty : Form S T M).lower = [] := rfl

@[simp] theorem empty_lines : (empty : Form S T M).lines = ∅ := rfl

theorem concat_assoc (h : Form S T M) : (f.concat g).concat h = f.concat (g.concat h) := by
  refine Form.ext (List.append_assoc ..) (List.append_assoc ..) ?_
  simp only [concat_lines, concat_upper, concat_lower, List.length_append, Finset.map_union,
    Finset.map_map, Finset.union_assoc]
  congr 3
  ext <;> simp [Nat.add_assoc]

theorem empty_concat : empty.concat f = f := by
  ext p
  · simp
  · simp
  · simp [Finset.mem_map]

theorem concat_empty : f.concat empty = f := by
  ext p
  · simp
  · simp
  · simp

/-- Forms are a monoid under concatenation, with the empty form as unit. -/
instance instMonoid : Monoid (Form S T M) where
  mul := concat
  one := empty
  mul_assoc := concat_assoc
  one_mul := empty_concat
  mul_one := concat_empty

@[simp] theorem mul_eq_concat : f * g = f.concat g := rfl

@[simp] theorem one_eq_empty : (1 : Form S T M) = empty := rfl

/-! ### Morphs -/

section Morph

variable (m : M) (upper : List T) (lower : List S) (lines : Finset (ℕ × ℕ))

/-- `morph m upper lower lines` is the morph of the morpheme `m`: the autosegments `upper` over
the slots `lower`, all sponsored by `m`, with a line for each pair in `lines` of a position of
`upper` and a position of `lower`. It is [bermudez-otero-2012]'s morph (p. 50), a piece of
phonological material that the morphology concatenates and cannot alter. In [rolle-2018]'s
typology of underlying tone (Table 1, p. 16), a slot with a line is valued, one without is
unvalued, and an autosegment without a line floats. Harmonic serialism under richness of the base
takes `lines` empty in every language ([mccarthy-mullin-smith-2012], p. 285), while a stratal
phonology hands partially linked morphs, such as the Poko stem /Mᴴ/, to the postlexical level
([mcpherson-lamont-2026], (3) and p. 5). -/
def morph : Form S T M where
  upper := upper.map (⟨·, m⟩)
  lower := lower.map (⟨·, m⟩)
  lines := lines.filter fun p ↦ p.1 < upper.length ∧ p.2 < lower.length
  lt_of_mem_lines h := by simpa using (Finset.mem_filter.1 h).2

@[simp] theorem morph_upper : (morph m upper lower lines).upper = upper.map (⟨·, m⟩) := rfl

@[simp] theorem morph_lower : (morph m upper lower lines).lower = lower.map (⟨·, m⟩) := rfl

/-- The lines of a morph are the given pairs within range of its tiers. -/
@[simp] theorem lines_morph :
    (morph m upper lower lines).lines =
      lines.filter fun p ↦ p.1 < upper.length ∧ p.2 < lower.length := rfl

variable {m upper lower lines} in
@[simp] theorem mem_links_morph {p : Fin (morph m upper lower lines).upper.length ×
    Fin (morph m upper lower lines).lower.length} :
    p ∈ (morph m upper lower lines).links ↔ (p.1.val, p.2.val) ∈ lines := by
  rw [mem_links, lines_morph, Finset.mem_filter, and_iff_left_iff_imp]
  exact fun _ ↦ ⟨by simpa using p.1.isLt, by simpa using p.2.isLt⟩

@[simp] theorem links_morph_empty : (morph m upper lower ∅ : Form S T M).links = ∅ :=
  Finset.eq_empty_of_forall_notMem fun _ h ↦ Finset.notMem_empty _ (mem_links_morph.1 h)

end Morph

end Form

section Presentation

universe u
variable {S T M : Type u} (f g : Form S T M)

namespace Form

/-- The representation a form presents, with the sponsors on its labels. -/
def toAR : AR (TwoTier (Sponsored T M) (Sponsored S M)) :=
  AR.ofWords f.upper f.lower fun p q ↦ (p, q) ∈ f.lines

@[simp] theorem word_toAR_true : f.toAR.word true = f.upper := rfl

@[simp] theorem word_toAR_false : f.toAR.word false = f.lower := rfl

@[simp] theorem link_toAR {p q : ℕ} : f.toAR.Link true false p q ↔ (p, q) ∈ f.lines :=
  AR.link_ofWords.trans
    ⟨fun h ↦ h.2.2, fun h ↦ ⟨(f.lt_of_mem_lines h).1, (f.lt_of_mem_lines h).2, h⟩⟩

/-- The presented representation obeys the NCC iff the lines are non-crossing. -/
theorem noCrossing_toAR_iff : f.toAR.NoCrossing ↔ IsNonCrossing (f.lines : SetRel ℕ ℕ) := by
  refine AR.noCrossing_ofWords_iff.trans ?_
  congr! 1
  ext ⟨p, q⟩
  exact ⟨fun h ↦ h.2.2, fun h ↦ ⟨(f.lt_of_mem_lines h).1, (f.lt_of_mem_lines h).2, h⟩⟩

theorem toAR_concat : (f.concat g).toAR = f.toAR * g.toAR :=
  AR.ext_of_true_false rfl rfl fun p q ↦ by
    rw [AR.link_mul]
    simp only [link_toAR, word_toAR_true, word_toAR_false, concat_lines, Finset.mem_union,
      Finset.mem_map, shift_apply, Prod.ext_iff]
    constructor
    · rintro (h | ⟨⟨a, b⟩, h, rfl, rfl⟩)
      · exact .inl h
      · exact .inr ⟨by omega, by omega, by simpa using h⟩
    · rintro (h | ⟨hp, hq, h⟩)
      · exact .inl h
      · exact .inr ⟨_, h, by omega, by omega⟩

theorem toAR_empty : (empty : Form S T M).toAR = 1 :=
  AR.ext_of_true_false rfl rfl fun p q ↦ by simp

/-- Presentation is a monoid hom from forms to representations. -/
@[simps] def toARHom : Form S T M →* AR (TwoTier (Sponsored T M) (Sponsored S M)) where
  toFun := toAR
  map_one' := toAR_empty
  map_mul' := toAR_concat

/-- Concatenation preserves the No-Crossing Constraint, as concatenation of representations
does ([jardine-2016b] Theorem 4). -/
theorem isNonCrossing_lines_concat (h₁ : IsNonCrossing (f.lines : SetRel ℕ ℕ))
    (h₂ : IsNonCrossing (g.lines : SetRel ℕ ℕ)) :
    IsNonCrossing ((f.concat g).lines : SetRel ℕ ℕ) := by
  rw [← noCrossing_toAR_iff, toAR_concat]
  exact ((noCrossing_toAR_iff f).2 h₁).mul ((noCrossing_toAR_iff g).2 h₂)

end Form

end Presentation

end Autosegmental
