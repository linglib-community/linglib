module

public import Linglib.Fragments.Indonesian.Phonology
public import Linglib.Phonology.Segmental.NaturalClass
public import Linglib.Data.Wordlist.Sneddon1996

/-!
# Sneddon (1996): the prefixes *meN-* and *peN-*

Sneddon's grammar of Indonesian gives rules for the nasal that ends the prefixes *meN-* and
*peN-*, by the first sound of the base. The nasal is velar before a vowel and before *g*, *k*,
*h* and *kh*, takes the place of the other obstruents, replaces an initial *p*, *t*, *k* or *s*,
and is lost before the other sonorant consonants. In borrowings an initial *s* may be kept, after
*n*. This file checks the Indonesian phonology fragment against these rules, and against the
forms Sneddon gives for them, each read through the glyphs of PHOIBLE's Indonesian inventory.

## Main results

* `juncture_of_vowel_or_h`, `juncture_of_obstruent`, `juncture_of_sonorant`, `fuse_eq`: the
  rules for each class of base-initial sound.
* `voicelessObstruents_sdiff_substituting`: the voiceless obstruents that keep their place are
  *c* and the fricatives of loans.
* `junctureRetained_s`: the nasal before a kept *s* is *n*.
* `relations_prefixed`: each derived form in the table is its prefix on its base.

## References

* [sneddon-1996]
-/

@[expose] public section

namespace Sneddon1996

open Phonology Indonesian.Phonology Sneddon1996.Wordlist CLDF.Wordlist

/-! ### The rules -/

/-- The voiceless obstruents. -/
def voicelessObstruent : Segment :=
  Segment.ofSpecs [(.consonantal, true), (.sonorant, false), (.voice, false)]

/-- The substituting consonants are voiceless obstruents. -/
theorem substituting_subset :
    substituting ⊆ voicelessObstruent.naturalClass consonants := by
  decide +kernel

/-- The voiceless obstruents that do not substitute are `c` and the loan fricatives (p. 10). -/
theorem voicelessObstruents_sdiff_substituting :
    voicelessObstruent.naturalClass consonants \ substituting = {c, f, sy, kh} := by
  decide +kernel

/-- A substituting consonant is replaced by one nasal. -/
theorem juncture_of_mem_substituting {x : Segment} (hx : x ∈ substituting) :
    juncture x = fuse x := by
  simp only [juncture, hx, ↓reduceIte]

/-- The nasal is lost before *l*, *r*, *m*, *n*, *ny*, *ng*, *w* and *y*, "other initial
sounds" (p. 10). -/
theorem juncture_of_sonorant :
    ∀ x ∈ consonants, sonorantConsonant ≤ x → juncture x = [x] := by
  decide +kernel

/-- "N becomes *ng* before a vowel" (p. 9), and before *h* (p. 10). -/
theorem juncture_of_vowel_or_h : ∀ x ∈ insert h vowels, juncture x = [ng, x] := by
  decide +kernel

/-- Before an obstruent that does not substitute, the nasal and the obstruent both surface. -/
theorem juncture_of_obstruent :
    ∀ x ∈ consonants, x.IsObstruent → x ∉ substituting → juncture x = assimilate [ng, x] := by
  decide +kernel

/-- Before every obstruent but `s`, the juncture nasal agrees with the obstruent in every place
feature but [strident] (pp. 9–10). -/
theorem juncture_head_agrees :
    ∀ x ∈ consonants, x.IsObstruent → x ≠ s →
      ∀ N ∈ (juncture x).head?, N.IsNasal ∧
        ∀ ft ∈ FeatureClass.place.erase .strident, N ft = x ft := by
  decide +kernel

/-- The fused nasals are phonemes, the nasal of the place of each stop and the palatal for
`s` (pp. 9–10). -/
theorem fuse_eq : fuse p = [m] ∧ fuse t = [n] ∧ fuse k = [ng] ∧ fuse s = [ny] := by
  decide +kernel

/-! ### Kept initials in borrowings -/

/-- The juncture with a base that keeps its initial consonant, as borrowings may (pp. 11–12),
where there is no fusion. -/
def junctureRetained (x : Segment) : List Segment :=
  if sonorantConsonant ≤ x then [x] else assimilate [ng, x]

/-- "If *s* is not lost N becomes *n*", as in *mensukseskan* (pp. 11–12). -/
theorem junctureRetained_s : junctureRetained s = [n, s] := by
  decide +kernel

/-- The place class alone makes the nasal before `s` strident, and the redundancy rule
restores `n`. -/
theorem placeAssimilation_s :
    (NasalSubstitution.placeAssimilation trigger).apply [ng, s]
        = [n.setFeature .strident true, s] ∧
      assimilate [ng, s] = [n, s] := by
  decide +kernel

/-! ### The forms -/

/-- The segment of a glyph of PHOIBLE's Standard Indonesian inventory. -/
def ofGlyph (g : String) : Option Segment :=
  (Data.PHOIBLE.Inventories.Indonesian.ind.phonemes.find? (·.glyph = g)).map
    (Segment.ofChart ·.features)

/-- The segments of a form, each read through its PHOIBLE glyph. -/
def segmentsOf (w : Form Cell) : Option (List Segment) := w.segments.mapM ofGlyph

/-- A relation of the table attaches *meN-*, *peN-*, or *meN-* with *per-* to a base, and after
*meN-* "the initial *p* of *per-* is not lost" (p. 11). -/
def prefixed : String → List Segment → Option (List Segment)
  | "meN-", w => some (meN w)
  | "peN-", w => some (peN w)
  | "meN- per-", w => some (assimilate ([m, e, ng] ++ [p, e, r] ++ w))
  | _, _ => none

/-- Each derived form is its prefix on its base, as in *mengajar* (pp. 9–10), *penulis* (p. 11) and
*memperbesar* (p. 26). -/
theorem relations_prefixed :
    ∀ r ∈ relations, (segmentsOf r.form).bind (prefixed r.relation) = segmentsOf r.target := by
  decide +kernel

end Sneddon1996
