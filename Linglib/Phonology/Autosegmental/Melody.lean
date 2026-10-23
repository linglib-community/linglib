/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Autosegmental.Floating

/-!
# Lexical melodies

This file defines the melody of a morpheme, its underlying autosegmental contribution as a
form built from lists.

A melody consists of the autosegments and slots that one morpheme sponsors, with its lexical
pre-linking in melody-local coordinates. Pre-linking is a matter of analysis. A melody with
no lines is the universally unlinked underlying form of harmonic serialism, and a partially
linked one is a stratal form such as `/M^H/`. The valued, unvalued, and floating
autosegments of Rolle's typology of grammatical tone are the linked slots, the unlinked
slots, and the floating autosegments of a candidate. A word is the product of the melodies
of its morphemes in the concatenation monoid, as in the Generalized Nonlinear Affixation
program.

## Main definitions

* `Form.melody`: the form of one morpheme's autosegments, slots, and pre-links, the
  pre-links given as pairs of natural numbers.

## Implementation notes

Consistency of Exponence, that GEN never alters morphemic affiliation, holds by the typing of
`Candidate`, whose tiers are those of its form.

## References

* [rolle-2018]
* [wolf-2007]
* [pulleyblank-1986]
* [mccarthy-mullin-smith-2012]
* [mcpherson-lamont-2026]
* [jardine-heinz-2015]
* [bermudez-otero-2012]
* [bye-svenonius-2012]
* [zimmermann-2024]
-/

@[expose] public section

namespace Autosegmental

namespace Form

variable {S T M : Type*} (m : M) (tones : List T) (tbus : List S) (links : Finset (ℕ × ℕ))

/-- `melody m tones tbus links` is the form of the morpheme `m`, with the autosegments
    `tones` over the slots `tbus` and the pre-links `links` in melody-local coordinates,
    given as pairs of positions. -/
def melody : Form S T M where
  upper := tones.map (⟨·, m⟩)
  lower := tbus.map (⟨·, m⟩)
  links := Finset.univ.filter fun p ↦ (p.1.val, p.2.val) ∈ links

@[simp] theorem melody_upper :
    (melody m tones tbus links).upper = tones.map (⟨·, m⟩) := rfl

@[simp] theorem melody_lower :
    (melody m tones tbus links).lower = tbus.map (⟨·, m⟩) := rfl

variable {m tones tbus links} in
@[simp] theorem mem_links_melody {p} :
    p ∈ (melody m tones tbus links).links ↔ (p.1.val, p.2.val) ∈ links := by
  simp [melody]

@[simp] theorem melody_upper_morpheme (k : Fin (melody m tones tbus links).upper.length) :
    (melody m tones tbus links).upper[k].morpheme = m := by
  obtain ⟨x, -, hx⟩ := List.mem_map.1 (List.getElem_mem (l := (melody m tones tbus links).upper)
    k.isLt)
  rw [Fin.getElem_fin, ← hx]

@[simp] theorem melody_lower_morpheme (i : Fin (melody m tones tbus links).lower.length) :
    (melody m tones tbus links).lower[i].morpheme = m := by
  obtain ⟨x, -, hx⟩ := List.mem_map.1 (List.getElem_mem (l := (melody m tones tbus links).lower)
    i.isLt)
  rw [Fin.getElem_fin, ← hx]

end Form

end Autosegmental
