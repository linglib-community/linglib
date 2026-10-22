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
# Floating autosegmental forms

A form is a two-tier autosegmental representation in position coordinates: an upper tier of
autosegments over a lower tier of slots, each element sponsored by a morpheme, and a finite set
of association lines between positions of the two tiers. Forms concatenate by juxtaposing the
tiers and shifting the right factor's lines, and they form a monoid. A form is a computable
presentation of a representation, `Form.toAR`, and presentation is a monoid hom, so the
No-Crossing Constraint on its lines is the constraint on the representation.

A candidate of a form records the autosegments deleted so far and the current surface lines,
the state of a serial optimality-theoretic derivation. GEN acts on candidates and never on the
form, so faithfulness constraints compare the surface lines with the form's lines. An
autosegment that is neither deleted nor linked on the surface is floating.

## Main definitions

* `Sponsored α M`: a tier element with the morpheme that sponsors it.
* `Form S T M`: a representation with slots in `S`, autosegments in `T`, and sponsors in `M`;
  `Form.concat` and `Form.empty` make the forms a monoid.
* `Form.toAR`: the representation a form presents, through `AR.ofWords`.
* `Form.IsTautomorphemic`: a line whose autosegment and slot share a sponsor.
* `Candidate u`: the surface state of a derivation from the form `u`; `Candidate.input` is
  the faithful candidate, and `Candidate.gen` the one-step GEN.

## Main results

* `Form.noCrossing_toAR_iff`: the presented representation obeys the NCC iff the lines are
  non-crossing.
* `Form.toARHom`: presentation is a monoid hom from forms to representations.
* `Form.isNonCrossing_links_concat`: concatenation preserves the No-Crossing Constraint.
* `Candidate.isNonCrossing_links_of_mem_gen`: GEN is closed on the No-Crossing Constraint.

## Implementation notes

Positions are elements of `Fin` over the tier lengths, so a candidate shares its form's
tiers by type and every line is in bounds. Numerals for positions of a concrete form need a
`NeZero` instance for its tier lengths, which a study supplies by `decide`. The readings of
the surface are `List.finRange` filters, which reduce under kernel `decide`, because
`Finset.sort` does not unfold structurally. `Form.toAR` needs the three label types in one
universe, as `TwoTier` does.

## References

* [goldsmith-1976]
* [pulleyblank-1986]
* [wolf-2007]
* [mccarthy-mullin-smith-2012]
* [mcpherson-lamont-2026]
* [lieber-1983]
* [laoide-kemp-2026]
* [zimmermann-2017]
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

/-- Two forms are equal when their tiers agree and their lines correspond across the
resulting identification of positions. -/
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
/-- A line of a concatenation is a line of the left factor, or a line of the right factor
shifted past the left factor's tiers. -/
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

/-- Presenting a concatenation gives the concatenation of the presentations. -/
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

/-- The empty form presents the empty representation. -/
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

/-- A `Candidate u` is the surface state of a derivation from the form `u`, recording the
    autosegments deleted so far and the current surface lines. The faithful candidate is
    `Candidate.input u`, and GEN edits candidates while `u` stays fixed. -/
@[ext] structure Candidate {S T M : Type*} (u : Form S T M) where
  /-- The autosegments deleted on the surface. -/
  deleted : Finset (Fin u.upper.length)
  /-- The surface association lines. -/
  links : Finset (Fin u.upper.length × Fin u.lower.length)

namespace Candidate

variable {S T M : Type*} {u : Form S T M} (c : Candidate u) {k j : Fin u.upper.length}
  {i : Fin u.lower.length} {l : Fin u.upper.length × Fin u.lower.length}

/-- Candidates are compared on their positions alone, whatever the labels of the form. -/
instance : DecidableEq (Candidate u) := fun _ _ ↦ decidable_of_iff _ Candidate.ext_iff.symm

/-- `input u` is the faithful candidate of `u`, with nothing deleted and the form's lines as
    its surface lines. -/
@[simps] def input (u : Form S T M) : Candidate u := ⟨∅, u.links⟩

/-! ### Surface predicates -/

/-- Autosegment `k` is linked when it bears a surface line. -/
def IsLinked (k : Fin u.upper.length) : Prop := ∃ l ∈ c.links, l.1 = k

/-- Slot `i` is linked when it bears a surface line. -/
def IsLinkedLower (i : Fin u.lower.length) : Prop := ∃ l ∈ c.links, l.2 = i

/-- Autosegment `k` is floating when it is not deleted and bears no surface line. -/
def IsFloating (k : Fin u.upper.length) : Prop := k ∉ c.deleted ∧ ¬ c.IsLinked k

/-- `insertedLinks c` is the set of surface lines absent from the form, which GEN has
    inserted and `DEP` counts. -/
def insertedLinks : Finset (Fin u.upper.length × Fin u.lower.length) := c.links \ u.links

/-- `deletedLinks c` is the set of the form's lines absent from the surface, which GEN has
    deleted and `MAX` counts. -/
def deletedLinks : Finset (Fin u.upper.length × Fin u.lower.length) := u.links \ c.links

instance : Decidable (c.IsLinked k) := inferInstanceAs (Decidable (∃ _ ∈ _, _))

instance : Decidable (c.IsLinkedLower i) := inferInstanceAs (Decidable (∃ _ ∈ _, _))

instance : Decidable (c.IsFloating k) := inferInstanceAs (Decidable (_ ∧ _))

variable {c}

theorem isLinked_iff : c.IsLinked k ↔ ∃ i, (k, i) ∈ c.links :=
  ⟨fun ⟨⟨_, i⟩, h, rfl⟩ ↦ ⟨i, h⟩, fun ⟨_, h⟩ ↦ ⟨_, h, rfl⟩⟩

theorem isLinkedLower_iff : c.IsLinkedLower i ↔ ∃ k, (k, i) ∈ c.links :=
  ⟨fun ⟨⟨k, _⟩, h, rfl⟩ ↦ ⟨k, h⟩, fun ⟨_, h⟩ ↦ ⟨_, h, rfl⟩⟩

@[simp] theorem mem_insertedLinks : l ∈ c.insertedLinks ↔ l ∈ c.links ∧ l ∉ u.links :=
  Finset.mem_sdiff

@[simp] theorem mem_deletedLinks : l ∈ c.deletedLinks ↔ l ∈ u.links ∧ l ∉ c.links :=
  Finset.mem_sdiff

/-- The faithful candidate has no inserted line. -/
@[simp] theorem insertedLinks_input : (input u).insertedLinks = ∅ := by
  simp [insertedLinks]

/-- The faithful candidate has no deleted line. -/
@[simp] theorem deletedLinks_input : (input u).deletedLinks = ∅ := by
  simp [deletedLinks]

/-! ### Reading the surface

The readings of the surface are lists over `List.finRange` in tier order, which reduce under
kernel `decide`. -/

variable (c)

/-- `linksTo c i` lists the autosegments linked to slot `i` on the surface, in tier order. -/
def linksTo (i : Fin u.lower.length) : List (Fin u.upper.length) :=
  (List.finRange u.upper.length).filter fun k ↦ (k, i) ∈ c.links

/-- `tierValues c i` lists the values of the autosegments linked to slot `i` on the surface,
    in tier order. -/
def tierValues (i : Fin u.lower.length) : List T :=
  (c.linksTo i).map fun k ↦ u.upper[k].value

/-- `alive c` lists the undeleted autosegments in tier order. -/
def alive : List (Fin u.upper.length) := (List.finRange u.upper.length).filter (· ∉ c.deleted)

variable {c}

@[simp] theorem mem_linksTo : k ∈ c.linksTo i ↔ (k, i) ∈ c.links := by
  simp [linksTo]

variable (c) in
theorem nodup_linksTo (i : Fin u.lower.length) : (c.linksTo i).Nodup :=
  (List.nodup_finRange _).filter _

@[simp] theorem mem_tierValues {t : T} :
    t ∈ c.tierValues i ↔ ∃ k, (k, i) ∈ c.links ∧ u.upper[k].value = t := by
  simp [tierValues]

@[simp] theorem mem_alive : k ∈ c.alive ↔ k ∉ c.deleted := by
  simp [alive]

/-! ### The atomic GEN operations -/

variable (c)

/-- `deleteTierElem c k` deletes autosegment `k` on the surface, together with every surface
    line it bears. -/
@[simps] def deleteTierElem (k : Fin u.upper.length) : Candidate u :=
  ⟨insert k c.deleted, c.links.filter (·.1 ≠ k)⟩

/-- `insertLink c k i` inserts the surface line from autosegment `k` to slot `i`. -/
@[simps] def insertLink (k : Fin u.upper.length) (i : Fin u.lower.length) : Candidate u :=
  ⟨c.deleted, insert (k, i) c.links⟩

/-- `deleteLink c k i` deletes the surface line from autosegment `k` to slot `i`. -/
@[simps] def deleteLink (k : Fin u.upper.length) (i : Fin u.lower.length) : Candidate u :=
  ⟨c.deleted, c.links.erase (k, i)⟩

variable {c}

@[simp] theorem isLinked_deleteTierElem :
    (c.deleteTierElem k).IsLinked j ↔ j ≠ k ∧ c.IsLinked j := by
  simp only [isLinked_iff, deleteTierElem_links, Finset.mem_filter]
  aesop

@[simp] theorem isLinked_insertLink : (c.insertLink k i).IsLinked j ↔ j = k ∨ c.IsLinked j := by
  simp only [isLinked_iff, insertLink_links, Finset.mem_insert, Prod.mk.injEq]
  aesop

@[simp] theorem isLinkedLower_insertLink {i' : Fin u.lower.length} :
    (c.insertLink k i).IsLinkedLower i' ↔ i' = i ∨ c.IsLinkedLower i' := by
  simp only [isLinkedLower_iff, insertLink_links, Finset.mem_insert, Prod.mk.injEq]
  aesop

@[simp] theorem isFloating_deleteTierElem :
    (c.deleteTierElem k).IsFloating j ↔ j ≠ k ∧ c.IsFloating j := by
  simp only [IsFloating, deleteTierElem_deleted, Finset.mem_insert, isLinked_deleteTierElem]
  tauto

@[simp] theorem isFloating_insertLink :
    (c.insertLink k i).IsFloating j ↔ j ≠ k ∧ c.IsFloating j := by
  simp only [IsFloating, insertLink_deleted, isLinked_insertLink]
  tauto

theorem links_deleteTierElem_subset : (c.deleteTierElem k).links ⊆ c.links :=
  Finset.filter_subset _ _

theorem links_subset_insertLink : c.links ⊆ (c.insertLink k i).links :=
  Finset.subset_insert _ _

/-! ### One-step GEN -/

section Gen

variable {c' : Candidate u}

/-- `gen c` is the one-step GEN of harmonic serialism. It contains `c` itself, the deletion of
    each undeleted autosegment, and each line from a floating autosegment to a slot in its
    window, which crosses no surface line; insert-and-associate and shift are omitted. -/
def gen (c : Candidate u) : Finset (Candidate u) :=
  insert c <|
    (Finset.univ.filter (· ∉ c.deleted)).image c.deleteTierElem ∪
      ((Finset.univ.filter c.IsFloating ×ˢ Finset.univ).filter
        fun p ↦ p.2 ∈ window (c.links : SetRel (Fin u.upper.length) (Fin u.lower.length)) p.1).image
          fun p ↦ c.insertLink p.1 p.2

theorem mem_gen : c' ∈ c.gen ↔ c' = c ∨ (∃ k ∉ c.deleted, c' = c.deleteTierElem k) ∨
    ∃ k i, c.IsFloating k ∧
      i ∈ window (c.links : SetRel (Fin u.upper.length) (Fin u.lower.length)) k ∧
        c' = c.insertLink k i := by
  simp only [gen, Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_product, and_true, Prod.exists, and_assoc,
    eq_comm (a := c')]

@[simp] theorem self_mem_gen : c ∈ c.gen := Finset.mem_insert_self _ _

theorem deleteTierElem_mem_gen (hd : k ∉ c.deleted) : c.deleteTierElem k ∈ c.gen :=
  mem_gen.2 (.inr (.inl ⟨k, hd, rfl⟩))

theorem insertLink_mem_gen (hk : c.IsFloating k)
    (hx : i ∈ window (c.links : SetRel (Fin u.upper.length) (Fin u.lower.length)) k) :
    c.insertLink k i ∈ c.gen :=
  mem_gen.2 (.inr (.inr ⟨k, i, hk, hx, rfl⟩))

/-- GEN never resurrects a deleted autosegment. -/
theorem deleted_subset_of_mem_gen (hc : c' ∈ c.gen) : c.deleted ⊆ c'.deleted := by
  rcases mem_gen.1 hc with rfl | ⟨_, -, rfl⟩ | ⟨_, _, -, -, rfl⟩
  exacts [subset_rfl, Finset.subset_insert _ _, subset_rfl]

/-- GEN is closed on the No-Crossing Constraint, since deletion shrinks the surface lines and
    each inserted line ends in its node's window. -/
theorem isNonCrossing_links_of_mem_gen
    (h : IsNonCrossing (c.links : SetRel (Fin u.upper.length) (Fin u.lower.length)))
    (hc : c' ∈ c.gen) :
    IsNonCrossing (c'.links : SetRel (Fin u.upper.length) (Fin u.lower.length)) := by
  rcases mem_gen.1 hc with rfl | ⟨_, -, rfl⟩ | ⟨_, _, -, hx, rfl⟩
  · exact h
  · exact h.subset (Finset.coe_subset.2 links_deleteTierElem_subset)
  · simpa using h.insert_of_mem_window hx

end Gen

end Candidate

end Autosegmental
