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
* `Form.morph`: the morph of a morpheme, from its autosegments, its slots, and its lines.
* `Form.IsTautomorphemic`: a line whose autosegment and slot share a sponsor.
* `Form.toAR`: the representation a form presents, through `AR.ofWords`.

## Main results

* `Form.noCrossing_toAR_iff`: the presented representation obeys the NCC iff the lines are
  non-crossing.
* `Form.toARHom`: presentation is a monoid hom from forms to representations.
* `Form.isNonCrossing_links_concat`: concatenation preserves the No-Crossing Constraint.

## Implementation notes

Positions are elements of `Fin` over the tier lengths, so every line is in bounds, and numerals
for positions of a concrete form need a `NeZero` instance for its tier lengths, which a study
supplies by `decide`. `Form.morph` takes its lines as pairs of natural numbers and drops those
out of range, as `SimpleGraph.fromEdgeSet` drops loops. `Form.toAR` needs the three label types
in one universe, as `TwoTier` does.

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

/-- A `Form S T M` is a two-tier autosegmental representation with slots in `S`, autosegments
in `T`, and sponsors in `M`. Its association lines run from positions of the upper tier to
positions of the lower tier. -/
structure Form (S T M : Type*) where
  /-- The upper tier, of autosegments in tier order. -/
  upper : List (Sponsored T M)
  /-- The lower tier, of slots in tier order. -/
  lower : List (Sponsored S M)
  /-- The association lines, each from an autosegment to a slot. -/
  links : Finset (Fin upper.length × Fin lower.length)

namespace Form

variable {S T M : Type*} (f g : Form S T M)

/-- Forms are compared tier by tier and then on their lines, which live over the same
positions once the tiers agree. -/
instance [DecidableEq S] [DecidableEq T] [DecidableEq M] : DecidableEq (Form S T M)
  | ⟨u, l, ls⟩, ⟨u', l', ls'⟩ =>
    if h : u = u' then
      if h' : l = l' then by subst h h'; exact decidable_of_iff (ls = ls') (by simp)
      else isFalse fun he ↦ h' (congrArg lower he)
    else isFalse fun he ↦ h (congrArg upper he)

theorem ext {f g : Form S T M} (hu : f.upper = g.upper) (hl : f.lower = g.lower)
    (h : ∀ p, p ∈ f.links ↔
      (finCongr (congrArg List.length hu) p.1, finCongr (congrArg List.length hl) p.2)
        ∈ g.links) : f = g := by
  obtain ⟨u, l, ls⟩ := f
  obtain ⟨u', l', ls'⟩ := g
  cases hu
  cases hl
  simp only [finCongr_refl, Equiv.refl_apply] at h
  rw [Finset.ext_iff.2 h]

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

/-- The positions of `a` as the left block of `a ++ b`. -/
def castAppend {α : Type*} (a b : List α) : Fin a.length ↪ Fin (a ++ b).length :=
  ⟨fun i ↦ ⟨i, by simp; omega⟩, fun _ _ h ↦ Fin.ext (Fin.mk.inj h)⟩

/-- The positions of `b` as the right block of `a ++ b`. -/
def natAddAppend {α : Type*} (a b : List α) : Fin b.length ↪ Fin (a ++ b).length :=
  ⟨fun i ↦ ⟨a.length + i, by simp⟩, fun _ _ h ↦ Fin.ext (by have := Fin.mk.inj h; omega)⟩

@[simp] theorem val_castAppend {α : Type*} {a b : List α} (i : Fin a.length) :
    (castAppend a b i : ℕ) = i := rfl

@[simp] theorem val_natAddAppend {α : Type*} {a b : List α} (i : Fin b.length) :
    (natAddAppend a b i : ℕ) = a.length + i := rfl

/-- `concat f g` juxtaposes the tiers of `f` and `g` and shifts the lines of `g` past the tiers
of `f`. -/
def concat : Form S T M where
  upper := f.upper ++ g.upper
  lower := f.lower ++ g.lower
  links :=
    f.links.map ((castAppend f.upper g.upper).prodMap (castAppend f.lower g.lower)) ∪
      g.links.map ((natAddAppend f.upper g.upper).prodMap (natAddAppend f.lower g.lower))

/-- The empty form has empty tiers and no lines. -/
def empty : Form S T M := ⟨[], [], ∅⟩

@[simp] theorem concat_upper : (f.concat g).upper = f.upper ++ g.upper := rfl

@[simp] theorem concat_lower : (f.concat g).lower = f.lower ++ g.lower := rfl

@[simp] theorem empty_upper : (empty : Form S T M).upper = [] := rfl

@[simp] theorem empty_lower : (empty : Form S T M).lower = [] := rfl

@[simp] theorem empty_links : (empty : Form S T M).links = ∅ := rfl

variable {f g} in
theorem mem_links_concat {p : Fin (f.concat g).upper.length × Fin (f.concat g).lower.length} :
    p ∈ (f.concat g).links ↔
      (∃ q ∈ f.links, q.1.val = p.1.val ∧ q.2.val = p.2.val) ∨
        ∃ q ∈ g.links, f.upper.length + q.1.val = p.1.val ∧
          f.lower.length + q.2.val = p.2.val := by
  obtain ⟨p₁, p₂⟩ := p
  simp [concat, Finset.mem_map, Function.Embedding.prodMap, Prod.ext_iff, Fin.ext_iff]

theorem concat_assoc (h : Form S T M) : (f.concat g).concat h = f.concat (g.concat h) := by
  refine ext (List.append_assoc ..) (List.append_assoc ..) fun p ↦ ?_
  have e₁ : (f.concat g).upper.length = f.upper.length + g.upper.length :=
    List.length_append ..
  have e₂ : (f.concat g).lower.length = f.lower.length + g.lower.length :=
    List.length_append ..
  rw [mem_links_concat (f := f.concat g) (g := h), mem_links_concat (f := f) (g := g.concat h)]
  simp only [finCongr_apply, Fin.val_cast]
  constructor
  · rintro (⟨q, hq, h₁, h₂⟩ | ⟨q, hq, h₁, h₂⟩)
    · rcases mem_links_concat.1 hq with ⟨r, hr, h₃, h₄⟩ | ⟨r, hr, h₃, h₄⟩
      · exact .inl ⟨r, hr, by omega, by omega⟩
      · exact .inr ⟨(castAppend _ _ r.1, castAppend _ _ r.2),
          mem_links_concat.2 (.inl ⟨r, hr, rfl, rfl⟩), by simp; omega, by simp; omega⟩
    · exact .inr ⟨(natAddAppend _ _ q.1, natAddAppend _ _ q.2),
        mem_links_concat.2 (.inr ⟨q, hq, rfl, rfl⟩), by simp; omega, by simp; omega⟩
  · rintro (⟨q, hq, h₁, h₂⟩ | ⟨q, hq, h₁, h₂⟩)
    · exact .inl ⟨(castAppend _ _ q.1, castAppend _ _ q.2),
        mem_links_concat.2 (.inl ⟨q, hq, rfl, rfl⟩), by simp; omega, by simp; omega⟩
    · rcases mem_links_concat.1 hq with ⟨r, hr, h₃, h₄⟩ | ⟨r, hr, h₃, h₄⟩
      · exact .inl ⟨(natAddAppend _ _ r.1, natAddAppend _ _ r.2),
          mem_links_concat.2 (.inr ⟨r, hr, rfl, rfl⟩), by simp; omega, by simp; omega⟩
      · exact .inr ⟨r, hr, by omega, by omega⟩

theorem empty_concat : empty.concat f = f := by
  refine ext (List.nil_append _) (List.nil_append _) fun p ↦ ?_
  rw [mem_links_concat]
  constructor
  · rintro (⟨q, hq, -⟩ | ⟨q, hq, h₁, h₂⟩)
    · exact absurd hq (Finset.notMem_empty _)
    · convert hq using 1
      exact Prod.ext (Fin.ext (by simpa using h₁.symm)) (Fin.ext (by simpa using h₂.symm))
  · intro hp
    exact .inr ⟨_, hp, by simp, by simp⟩

theorem concat_empty : f.concat empty = f := by
  refine ext (List.append_nil _) (List.append_nil _) fun p ↦ ?_
  rw [mem_links_concat]
  constructor
  · rintro (⟨q, hq, h₁, h₂⟩ | ⟨q, hq, -⟩)
    · convert hq using 1
      exact Prod.ext (Fin.ext (by simp; omega)) (Fin.ext (by simp; omega))
    · exact absurd hq (Finset.notMem_empty _)
  · intro hp
    exact .inl ⟨_, hp, by simp, by simp⟩

/-- Forms are a monoid under concatenation, with the empty form as unit. -/
instance instMonoid : Monoid (Form S T M) where
  mul := concat
  one := empty
  mul_assoc := concat_assoc
  one_mul := empty_concat
  mul_one := concat_empty

@[simp] theorem mul_eq_concat : f * g = f.concat g := rfl

@[simp] theorem one_eq_empty : (1 : Form S T M) = empty := rfl

/-! ### The presented representation

A form presents the two-tier representation `AR.ofWords` builds from its tiers and its lines in
`ℕ` coordinates. -/

/-- The lines of a form in `ℕ` coordinates. -/
def lines : Finset (ℕ × ℕ) := f.links.map (Fin.valEmbedding.prodMap Fin.valEmbedding)

variable {f} in
@[simp] theorem mem_lines {p : ℕ × ℕ} :
    p ∈ f.lines ↔ ∃ q ∈ f.links, (q.1 : ℕ) = p.1 ∧ (q.2 : ℕ) = p.2 := by
  obtain ⟨p₁, p₂⟩ := p
  simp [lines, Function.Embedding.prodMap, Prod.ext_iff]

theorem lt_of_mem_lines {p : ℕ × ℕ} (h : p ∈ f.lines) :
    p.1 < f.upper.length ∧ p.2 < f.lower.length := by
  obtain ⟨q, -, h₁, h₂⟩ := mem_lines.1 h
  exact ⟨h₁ ▸ q.1.isLt, h₂ ▸ q.2.isLt⟩

theorem isNonCrossing_lines_iff :
    IsNonCrossing (f.lines : SetRel ℕ ℕ) ↔
      IsNonCrossing (f.links : SetRel (Fin f.upper.length) (Fin f.lower.length)) := by
  rw [lines, Finset.coe_map, isNonCrossing_image]
  rfl

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
  links := Finset.univ.filter fun p ↦ (p.1.val, p.2.val) ∈ lines

@[simp] theorem morph_upper : (morph m upper lower lines).upper = upper.map (⟨·, m⟩) := rfl

@[simp] theorem morph_lower : (morph m upper lower lines).lower = lower.map (⟨·, m⟩) := rfl

variable {m upper lower lines} in
@[simp] theorem mem_links_morph {p} :
    p ∈ (morph m upper lower lines).links ↔ (p.1.val, p.2.val) ∈ lines := by
  simp [morph]

/-- The lines of a morph are the given pairs within range of its tiers. -/
@[simp] theorem lines_morph :
    (morph m upper lower lines).lines =
      lines.filter fun p ↦ p.1 < upper.length ∧ p.2 < lower.length := by
  ext ⟨a, b⟩
  simp only [mem_lines, mem_links_morph, Finset.mem_filter]
  constructor
  · rintro ⟨⟨k, i⟩, h, rfl, rfl⟩
    exact ⟨h, by simpa using k.isLt, by simpa using i.isLt⟩
  · rintro ⟨h, ha, hb⟩
    exact ⟨(⟨a, by simpa⟩, ⟨b, by simpa⟩), h, rfl, rfl⟩

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
theorem noCrossing_toAR_iff :
    f.toAR.NoCrossing ↔
      IsNonCrossing (f.links : SetRel (Fin f.upper.length) (Fin f.lower.length)) := by
  refine AR.noCrossing_ofWords_iff.trans ?_
  rw [← isNonCrossing_lines_iff]
  congr! 1
  ext ⟨p, q⟩
  simp only [Set.mem_ofPred_eq, Finset.mem_coe]
  exact ⟨fun h ↦ h.2.2, fun h ↦ ⟨(f.lt_of_mem_lines h).1, (f.lt_of_mem_lines h).2, h⟩⟩

theorem toAR_concat : (f.concat g).toAR = f.toAR * g.toAR :=
  AR.ext_of_true_false rfl rfl fun p q ↦ by
    rw [AR.link_mul]
    simp only [link_toAR, word_toAR_true, word_toAR_false, mem_lines, mem_links_concat]
    constructor
    · rintro ⟨r, (⟨s, hs, h₁, h₂⟩ | ⟨s, hs, h₁, h₂⟩), rfl, rfl⟩
      · exact .inl ⟨s, hs, h₁, h₂⟩
      · exact .inr ⟨by omega, by omega, s, hs, by omega, by omega⟩
    · rintro (⟨s, hs, h₁, h₂⟩ | ⟨hp, hq, s, hs, h₁, h₂⟩)
      · exact ⟨(castAppend _ _ s.1, castAppend _ _ s.2), .inl ⟨s, hs, rfl, rfl⟩,
          by simpa using h₁, by simpa using h₂⟩
      · exact ⟨(natAddAppend _ _ s.1, natAddAppend _ _ s.2), .inr ⟨s, hs, rfl, rfl⟩,
          by simp; omega, by simp; omega⟩

theorem toAR_empty : (empty : Form S T M).toAR = 1 :=
  AR.ext_of_true_false rfl rfl fun p q ↦ by simp [lines, empty]

/-- Presentation is a monoid hom from forms to representations. -/
@[simps] def toARHom : Form S T M →* AR (TwoTier (Sponsored T M) (Sponsored S M)) where
  toFun := toAR
  map_one' := toAR_empty
  map_mul' := toAR_concat

/-- Concatenation preserves the No-Crossing Constraint, as concatenation of representations
does ([jardine-2016b] Theorem 4). -/
theorem isNonCrossing_links_concat
    (h₁ : IsNonCrossing (f.links : SetRel (Fin f.upper.length) (Fin f.lower.length)))
    (h₂ : IsNonCrossing (g.links : SetRel (Fin g.upper.length) (Fin g.lower.length))) :
    IsNonCrossing ((f.concat g).links :
      SetRel (Fin (f.concat g).upper.length) (Fin (f.concat g).lower.length)) := by
  rw [← noCrossing_toAR_iff, toAR_concat]
  exact ((noCrossing_toAR_iff f).2 h₁).mul ((noCrossing_toAR_iff g).2 h₂)

end Form

end Presentation

end Autosegmental
