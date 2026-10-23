/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.OCP

/-!
# Consonantal roots

A consonantal root is the ordered melody of consonants that a root-and-pattern morphology stores
apart from its vocalism and its template, the nonconcatenative counterpart of a linear `Morph`.
The type of segments is a parameter, so that a root may be a list of feature bundles, of IPA
symbols or of coarser classes. In autosegmental terms a root is an unlinked melody on the
consonantal tier, and `TemplateMatch` associates it with a template.

The roots of other programs live under their owners: a root over `Morph` is a morph of a primary
word (`Morphology/Root/Basic.lean`), and `DistributedMorphology.Root` and `Semantics.Root` are
the acategorial terminal and the lexical-semantic root.

## Main definitions

* `Morphology.ConsonantalRoot`: a root, as the list of its segments.
* `Morphology.ConsonantalRoot.IsOCPClean`: no two adjacent segments of the root are identical.

## References

* [mccarthy-1981]
-/

@[expose] public section

namespace Morphology

/-- A consonantal root: an ordered list of segments. -/
structure ConsonantalRoot (α : Type*) where
  /-- The root segments, in order. -/
  segments : List α
  deriving Repr, DecidableEq

namespace ConsonantalRoot

variable {α : Type*}

/-- The number of root segments. -/
def arity (r : ConsonantalRoot α) : ℕ := r.segments.length

/-- The root with each segment relabeled. -/
def map {β : Type*} (f : α → β) (r : ConsonantalRoot α) : ConsonantalRoot β := ⟨r.segments.map f⟩

@[simp] theorem segments_map {β : Type*} (f : α → β) (r : ConsonantalRoot α) :
    (r.map f).segments = r.segments.map f := rfl

/-- Position `i` of a root is nonfinal when some position of the root follows it. -/
def IsNonfinal (r : ConsonantalRoot α) (i : ℕ) : Prop := i + 1 < r.arity

instance (r : ConsonantalRoot α) (i : ℕ) : Decidable (r.IsNonfinal i) :=
  inferInstanceAs (Decidable (_ < _))

/-- A root is OCP-clean when no two adjacent segments are identical, which is the segment tier
being `OCP.IsClean`; tier-relative variants go through `OCP.IsCleanOn`. -/
def IsOCPClean [DecidableEq α] (r : ConsonantalRoot α) : Prop :=
  OCP.IsClean r.segments

instance instDecidablePredIsOCPClean [DecidableEq α] :
    DecidablePred (IsOCPClean (α := α)) :=
  fun r ↦ inferInstanceAs (Decidable (OCP.IsClean r.segments))

end ConsonantalRoot
end Morphology
