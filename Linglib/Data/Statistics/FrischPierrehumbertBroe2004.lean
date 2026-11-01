module

public import Linglib.Data.Statistics.Schema

/-!
# FrischPierrehumbertBroe2004: statistics (generated)

Auto-generated from `Linglib/Data/Statistics/FrischPierrehumbertBroe2004.json` by
`scripts/gen_statistics.py`. Do not edit by hand: edit the JSON and re-run the generator.

Frisch, Pierrehumbert and Broe's printed results for the consonants of Arabic verbal roots, counted
in the 2,674 roots of Cowan (1979): the natural-classes similarity of every pair of consonants
(Table III), observed and expected co-occurrence by similarity for adjacent and non-adjacent pairs
(Table IV), the fits of five models of OCP-Place (Table V), and the three root types that illustrate
the O/E measure (p. 185).

## References

* [frisch-pierrehumbert-broe-2004]
-/

@[expose] public section

namespace FrischPierrehumbertBroe2004

open Data.Statistics

/-- The consonants of matrix (8), in its column order. -/
inductive Consonant where
  /-- b: ب -/
  | b
  /-- f: ف -/
  | f
  /-- m: م -/
  | m
  /-- t: ت -/
  | t
  /-- d: د -/
  | d
  /-- tˤ: ط -/
  | tEmph
  /-- dˤ: ض -/
  | dEmph
  /-- θ: ث -/
  | theta
  /-- ð: ذ -/
  | edh
  /-- s: س -/
  | s
  /-- z: ز -/
  | z
  /-- sˤ: ص -/
  | sEmph
  /-- zˤ: ظ, /ðˤ/ in the standard language -/
  | zEmph
  /-- ʃ: ش -/
  | esh
  /-- k: ك -/
  | k
  /-- g: ج, /dʒ/ in the standard language, which the paper writes as a dorsal stop -/
  | g
  /-- q: ق -/
  | q
  /-- χ: خ -/
  | chi
  /-- ʁ: غ -/
  | gamma
  /-- ħ: ح -/
  | hbar
  /-- ʕ: ع -/
  | ayin
  /-- h: ه -/
  | h
  /-- ʔ: ء -/
  | glottal
  /-- l: ل -/
  | l
  /-- r: ر -/
  | r
  /-- n: ن -/
  | n
  /-- w: و -/
  | w
  /-- j: ي -/
  | j
  deriving DecidableEq, Repr, Fintype

/-- The positions of a pair of consonants in a triliteral root. -/
inductive Distance where
  /-- Adjacent: first and second, or second and third -/
  | adjacent
  /-- Non-adjacent: first and third -/
  | nonAdjacent
  deriving DecidableEq, Repr, Fintype

/-- The similarity intervals of Table IV. -/
inductive SimilarityBin where
  /-- 0: nonhomorganic pairs -/
  | zero
  /-- 0–0.1: similarity above 0 up to 0.1 -/
  | upTo01
  /-- 0.1–0.2: 0.1 to 0.2 -/
  | upTo02
  /-- 0.2–0.3: 0.2 to 0.3 -/
  | upTo03
  /-- 0.3–0.4: 0.3 to 0.4 -/
  | upTo04
  /-- 0.4–0.5: 0.4 to 0.5 -/
  | upTo05
  /-- 0.5–0.6: 0.5 to 0.6 -/
  | upTo06
  /-- 0.8: /l, r/ alone -/
  | pointEight
  /-- 1: identical pairs -/
  | one
  deriving DecidableEq, Repr, Fintype

/-- The models of OCP-Place compared in Table V. -/
inductive Model where
  /-- Frequency: no OCP-Place effect: co-occurrence at random -/
  | frequency
  /-- Categorical: a categorical ban on consonants of one major class of (2) -/
  | categorical
  /-- Soft Model: a categorical ban on adjacent identical consonants and a constant O/E for
  consonants of one major class -/
  | soft
  /-- Feature Model: O/E a decreasing function of similarity computed over the features of (8) -/
  | feature
  /-- Natural Classes: O/E a decreasing function of the natural-classes similarity -/
  | naturalClasses
  deriving DecidableEq, Repr, Fintype

/-- The number of roots in the lexicon, from the dictionary of Cowan (1979). (p. 185; checked
against the page images.) -/
def lexiconRoots : ℕ := 2674

/-- A row of Table III, pp. 202–203: the natural-classes similarity of a pair of consonants, the
upper triangle of the symmetric table with the diagonal. -/
structure Similarity where
  /-- The first consonant. -/
  c1 : Consonant
  /-- The second consonant, not before the first in (8). -/
  c2 : Consonant
  /-- The similarity. -/
  similarity : Decimal
  deriving DecidableEq, Repr

/-- The 406 rows of Table III, pp. 202–203, in the paper's order; fitted or simulated by a model;
checked against the PDF text layer only. -/
def similarities : List Similarity :=
  [⟨.b, .b, ⟨1, 0⟩⟩,
   ⟨.b, .f, ⟨38, 2⟩⟩,
   ⟨.b, .m, ⟨5, 1⟩⟩,
   ⟨.b, .t, ⟨0, 0⟩⟩,
   ⟨.b, .d, ⟨0, 0⟩⟩,
   ⟨.b, .tEmph, ⟨0, 0⟩⟩,
   ⟨.b, .dEmph, ⟨0, 0⟩⟩,
   ⟨.b, .theta, ⟨0, 0⟩⟩,
   ⟨.b, .edh, ⟨0, 0⟩⟩,
   ⟨.b, .s, ⟨0, 0⟩⟩,
   ⟨.b, .z, ⟨0, 0⟩⟩,
   ⟨.b, .sEmph, ⟨0, 0⟩⟩,
   ⟨.b, .zEmph, ⟨0, 0⟩⟩,
   ⟨.b, .esh, ⟨0, 0⟩⟩,
   ⟨.b, .k, ⟨0, 0⟩⟩,
   ⟨.b, .g, ⟨0, 0⟩⟩,
   ⟨.b, .q, ⟨0, 0⟩⟩,
   ⟨.b, .chi, ⟨0, 0⟩⟩,
   ⟨.b, .gamma, ⟨0, 0⟩⟩,
   ⟨.b, .hbar, ⟨0, 0⟩⟩,
   ⟨.b, .ayin, ⟨0, 0⟩⟩,
   ⟨.b, .h, ⟨0, 0⟩⟩,
   ⟨.b, .glottal, ⟨0, 0⟩⟩,
   ⟨.b, .l, ⟨0, 0⟩⟩,
   ⟨.b, .r, ⟨0, 0⟩⟩,
   ⟨.b, .n, ⟨0, 0⟩⟩,
   ⟨.b, .w, ⟨22, 2⟩⟩,
   ⟨.b, .j, ⟨0, 0⟩⟩,
   ⟨.f, .f, ⟨1, 0⟩⟩,
   ⟨.f, .m, ⟨22, 2⟩⟩,
   ⟨.f, .t, ⟨0, 0⟩⟩,
   ⟨.f, .d, ⟨0, 0⟩⟩,
   ⟨.f, .tEmph, ⟨0, 0⟩⟩,
   ⟨.f, .dEmph, ⟨0, 0⟩⟩,
   ⟨.f, .theta, ⟨0, 0⟩⟩,
   ⟨.f, .edh, ⟨0, 0⟩⟩,
   ⟨.f, .s, ⟨0, 0⟩⟩,
   ⟨.f, .z, ⟨0, 0⟩⟩,
   ⟨.f, .sEmph, ⟨0, 0⟩⟩,
   ⟨.f, .zEmph, ⟨0, 0⟩⟩,
   ⟨.f, .esh, ⟨0, 0⟩⟩,
   ⟨.f, .k, ⟨0, 0⟩⟩,
   ⟨.f, .g, ⟨0, 0⟩⟩,
   ⟨.f, .q, ⟨0, 0⟩⟩,
   ⟨.f, .chi, ⟨0, 0⟩⟩,
   ⟨.f, .gamma, ⟨0, 0⟩⟩,
   ⟨.f, .hbar, ⟨0, 0⟩⟩,
   ⟨.f, .ayin, ⟨0, 0⟩⟩,
   ⟨.f, .h, ⟨0, 0⟩⟩,
   ⟨.f, .glottal, ⟨0, 0⟩⟩,
   ⟨.f, .l, ⟨0, 0⟩⟩,
   ⟨.f, .r, ⟨0, 0⟩⟩,
   ⟨.f, .n, ⟨0, 0⟩⟩,
   ⟨.f, .w, ⟨25, 2⟩⟩,
   ⟨.f, .j, ⟨0, 0⟩⟩,
   ⟨.m, .m, ⟨1, 0⟩⟩,
   ⟨.m, .t, ⟨0, 0⟩⟩,
   ⟨.m, .d, ⟨0, 0⟩⟩,
   ⟨.m, .tEmph, ⟨0, 0⟩⟩,
   ⟨.m, .dEmph, ⟨0, 0⟩⟩,
   ⟨.m, .theta, ⟨0, 0⟩⟩,
   ⟨.m, .edh, ⟨0, 0⟩⟩,
   ⟨.m, .s, ⟨0, 0⟩⟩,
   ⟨.m, .z, ⟨0, 0⟩⟩,
   ⟨.m, .sEmph, ⟨0, 0⟩⟩,
   ⟨.m, .zEmph, ⟨0, 0⟩⟩,
   ⟨.m, .esh, ⟨0, 0⟩⟩,
   ⟨.m, .k, ⟨0, 0⟩⟩,
   ⟨.m, .g, ⟨0, 0⟩⟩,
   ⟨.m, .q, ⟨0, 0⟩⟩,
   ⟨.m, .chi, ⟨0, 0⟩⟩,
   ⟨.m, .gamma, ⟨0, 0⟩⟩,
   ⟨.m, .hbar, ⟨0, 0⟩⟩,
   ⟨.m, .ayin, ⟨0, 0⟩⟩,
   ⟨.m, .h, ⟨0, 0⟩⟩,
   ⟨.m, .glottal, ⟨0, 0⟩⟩,
   ⟨.m, .l, ⟨0, 0⟩⟩,
   ⟨.m, .r, ⟨0, 0⟩⟩,
   ⟨.m, .n, ⟨0, 0⟩⟩,
   ⟨.m, .w, ⟨38, 2⟩⟩,
   ⟨.m, .j, ⟨0, 0⟩⟩,
   ⟨.t, .t, ⟨1, 0⟩⟩,
   ⟨.t, .d, ⟨42, 2⟩⟩,
   ⟨.t, .tEmph, ⟨26, 2⟩⟩,
   ⟨.t, .dEmph, ⟨17, 2⟩⟩,
   ⟨.t, .theta, ⟨21, 2⟩⟩,
   ⟨.t, .edh, ⟨14, 2⟩⟩,
   ⟨.t, .s, ⟨32, 2⟩⟩,
   ⟨.t, .z, ⟨19, 2⟩⟩,
   ⟨.t, .sEmph, ⟨12, 2⟩⟩,
   ⟨.t, .zEmph, ⟨8, 2⟩⟩,
   ⟨.t, .esh, ⟨12, 2⟩⟩,
   ⟨.t, .k, ⟨0, 0⟩⟩,
   ⟨.t, .g, ⟨0, 0⟩⟩,
   ⟨.t, .q, ⟨0, 0⟩⟩,
   ⟨.t, .chi, ⟨0, 0⟩⟩,
   ⟨.t, .gamma, ⟨0, 0⟩⟩,
   ⟨.t, .hbar, ⟨0, 0⟩⟩,
   ⟨.t, .ayin, ⟨0, 0⟩⟩,
   ⟨.t, .h, ⟨0, 0⟩⟩,
   ⟨.t, .glottal, ⟨0, 0⟩⟩,
   ⟨.t, .l, ⟨1, 1⟩⟩,
   ⟨.t, .r, ⟨1, 1⟩⟩,
   ⟨.t, .n, ⟨18, 2⟩⟩,
   ⟨.t, .w, ⟨0, 0⟩⟩,
   ⟨.t, .j, ⟨0, 0⟩⟩,
   ⟨.d, .d, ⟨1, 0⟩⟩,
   ⟨.d, .tEmph, ⟨16, 2⟩⟩,
   ⟨.d, .dEmph, ⟨3, 1⟩⟩,
   ⟨.d, .theta, ⟨13, 2⟩⟩,
   ⟨.d, .edh, ⟨21, 2⟩⟩,
   ⟨.d, .s, ⟨17, 2⟩⟩,
   ⟨.d, .z, ⟨32, 2⟩⟩,
   ⟨.d, .sEmph, ⟨8, 2⟩⟩,
   ⟨.d, .zEmph, ⟨13, 2⟩⟩,
   ⟨.d, .esh, ⟨7, 2⟩⟩,
   ⟨.d, .k, ⟨0, 0⟩⟩,
   ⟨.d, .g, ⟨0, 0⟩⟩,
   ⟨.d, .q, ⟨0, 0⟩⟩,
   ⟨.d, .chi, ⟨0, 0⟩⟩,
   ⟨.d, .gamma, ⟨0, 0⟩⟩,
   ⟨.d, .hbar, ⟨0, 0⟩⟩,
   ⟨.d, .ayin, ⟨0, 0⟩⟩,
   ⟨.d, .h, ⟨0, 0⟩⟩,
   ⟨.d, .glottal, ⟨0, 0⟩⟩,
   ⟨.d, .l, ⟨15, 2⟩⟩,
   ⟨.d, .r, ⟨15, 2⟩⟩,
   ⟨.d, .n, ⟨31, 2⟩⟩,
   ⟨.d, .w, ⟨0, 0⟩⟩,
   ⟨.d, .j, ⟨0, 0⟩⟩,
   ⟨.tEmph, .tEmph, ⟨1, 0⟩⟩,
   ⟨.tEmph, .dEmph, ⟨4, 1⟩⟩,
   ⟨.tEmph, .theta, ⟨24, 2⟩⟩,
   ⟨.tEmph, .edh, ⟨14, 2⟩⟩,
   ⟨.tEmph, .s, ⟨14, 2⟩⟩,
   ⟨.tEmph, .z, ⟨9, 2⟩⟩,
   ⟨.tEmph, .sEmph, ⟨41, 2⟩⟩,
   ⟨.tEmph, .zEmph, ⟨21, 2⟩⟩,
   ⟨.tEmph, .esh, ⟨13, 2⟩⟩,
   ⟨.tEmph, .k, ⟨21, 2⟩⟩,
   ⟨.tEmph, .g, ⟨11, 2⟩⟩,
   ⟨.tEmph, .q, ⟨36, 2⟩⟩,
   ⟨.tEmph, .chi, ⟨12, 2⟩⟩,
   ⟨.tEmph, .gamma, ⟨7, 2⟩⟩,
   ⟨.tEmph, .hbar, ⟨0, 0⟩⟩,
   ⟨.tEmph, .ayin, ⟨0, 0⟩⟩,
   ⟨.tEmph, .h, ⟨0, 0⟩⟩,
   ⟨.tEmph, .glottal, ⟨0, 0⟩⟩,
   ⟨.tEmph, .l, ⟨5, 2⟩⟩,
   ⟨.tEmph, .r, ⟨5, 2⟩⟩,
   ⟨.tEmph, .n, ⟨9, 2⟩⟩,
   ⟨.tEmph, .w, ⟨0, 0⟩⟩,
   ⟨.tEmph, .j, ⟨3, 2⟩⟩,
   ⟨.dEmph, .dEmph, ⟨1, 0⟩⟩,
   ⟨.dEmph, .theta, ⟨13, 2⟩⟩,
   ⟨.dEmph, .edh, ⟨23, 2⟩⟩,
   ⟨.dEmph, .s, ⟨9, 2⟩⟩,
   ⟨.dEmph, .z, ⟨14, 2⟩⟩,
   ⟨.dEmph, .sEmph, ⟨2, 1⟩⟩,
   ⟨.dEmph, .zEmph, ⟨42, 2⟩⟩,
   ⟨.dEmph, .esh, ⟨7, 2⟩⟩,
   ⟨.dEmph, .k, ⟨11, 2⟩⟩,
   ⟨.dEmph, .g, ⟨24, 2⟩⟩,
   ⟨.dEmph, .q, ⟨17, 2⟩⟩,
   ⟨.dEmph, .chi, ⟨7, 2⟩⟩,
   ⟨.dEmph, .gamma, ⟨14, 2⟩⟩,
   ⟨.dEmph, .hbar, ⟨0, 0⟩⟩,
   ⟨.dEmph, .ayin, ⟨0, 0⟩⟩,
   ⟨.dEmph, .h, ⟨0, 0⟩⟩,
   ⟨.dEmph, .glottal, ⟨0, 0⟩⟩,
   ⟨.dEmph, .l, ⟨9, 2⟩⟩,
   ⟨.dEmph, .r, ⟨9, 2⟩⟩,
   ⟨.dEmph, .n, ⟨16, 2⟩⟩,
   ⟨.dEmph, .w, ⟨0, 0⟩⟩,
   ⟨.dEmph, .j, ⟨6, 2⟩⟩,
   ⟨.theta, .theta, ⟨1, 0⟩⟩,
   ⟨.theta, .edh, ⟨45, 2⟩⟩,
   ⟨.theta, .s, ⟨4, 1⟩⟩,
   ⟨.theta, .z, ⟨24, 2⟩⟩,
   ⟨.theta, .sEmph, ⟨45, 2⟩⟩,
   ⟨.theta, .zEmph, ⟨24, 2⟩⟩,
   ⟨.theta, .esh, ⟨37, 2⟩⟩,
   ⟨.theta, .k, ⟨0, 0⟩⟩,
   ⟨.theta, .g, ⟨0, 0⟩⟩,
   ⟨.theta, .q, ⟨0, 0⟩⟩,
   ⟨.theta, .chi, ⟨0, 0⟩⟩,
   ⟨.theta, .gamma, ⟨0, 0⟩⟩,
   ⟨.theta, .hbar, ⟨0, 0⟩⟩,
   ⟨.theta, .ayin, ⟨0, 0⟩⟩,
   ⟨.theta, .h, ⟨0, 0⟩⟩,
   ⟨.theta, .glottal, ⟨0, 0⟩⟩,
   ⟨.theta, .l, ⟨15, 2⟩⟩,
   ⟨.theta, .r, ⟨15, 2⟩⟩,
   ⟨.theta, .n, ⟨7, 2⟩⟩,
   ⟨.theta, .w, ⟨0, 0⟩⟩,
   ⟨.theta, .j, ⟨0, 0⟩⟩,
   ⟨.edh, .edh, ⟨1, 0⟩⟩,
   ⟨.edh, .s, ⟨25, 2⟩⟩,
   ⟨.edh, .z, ⟨44, 2⟩⟩,
   ⟨.edh, .sEmph, ⟨24, 2⟩⟩,
   ⟨.edh, .zEmph, ⟨44, 2⟩⟩,
   ⟨.edh, .esh, ⟨21, 2⟩⟩,
   ⟨.edh, .k, ⟨0, 0⟩⟩,
   ⟨.edh, .g, ⟨0, 0⟩⟩,
   ⟨.edh, .q, ⟨0, 0⟩⟩,
   ⟨.edh, .chi, ⟨0, 0⟩⟩,
   ⟨.edh, .gamma, ⟨0, 0⟩⟩,
   ⟨.edh, .hbar, ⟨0, 0⟩⟩,
   ⟨.edh, .ayin, ⟨0, 0⟩⟩,
   ⟨.edh, .h, ⟨0, 0⟩⟩,
   ⟨.edh, .glottal, ⟨0, 0⟩⟩,
   ⟨.edh, .l, ⟨26, 2⟩⟩,
   ⟨.edh, .r, ⟨26, 2⟩⟩,
   ⟨.edh, .n, ⟨13, 2⟩⟩,
   ⟨.edh, .w, ⟨0, 0⟩⟩,
   ⟨.edh, .j, ⟨0, 0⟩⟩,
   ⟨.s, .s, ⟨1, 0⟩⟩,
   ⟨.s, .z, ⟨44, 2⟩⟩,
   ⟨.s, .sEmph, ⟨35, 2⟩⟩,
   ⟨.s, .zEmph, ⟨2, 1⟩⟩,
   ⟨.s, .esh, ⟨3, 1⟩⟩,
   ⟨.s, .k, ⟨0, 0⟩⟩,
   ⟨.s, .g, ⟨0, 0⟩⟩,
   ⟨.s, .q, ⟨0, 0⟩⟩,
   ⟨.s, .chi, ⟨0, 0⟩⟩,
   ⟨.s, .gamma, ⟨0, 0⟩⟩,
   ⟨.s, .hbar, ⟨0, 0⟩⟩,
   ⟨.s, .ayin, ⟨0, 0⟩⟩,
   ⟨.s, .h, ⟨0, 0⟩⟩,
   ⟨.s, .glottal, ⟨0, 0⟩⟩,
   ⟨.s, .l, ⟨16, 2⟩⟩,
   ⟨.s, .r, ⟨16, 2⟩⟩,
   ⟨.s, .n, ⟨8, 2⟩⟩,
   ⟨.s, .w, ⟨0, 0⟩⟩,
   ⟨.s, .j, ⟨0, 0⟩⟩,
   ⟨.z, .z, ⟨1, 0⟩⟩,
   ⟨.z, .sEmph, ⟨2, 1⟩⟩,
   ⟨.z, .zEmph, ⟨35, 2⟩⟩,
   ⟨.z, .esh, ⟨17, 2⟩⟩,
   ⟨.z, .k, ⟨0, 0⟩⟩,
   ⟨.z, .g, ⟨0, 0⟩⟩,
   ⟨.z, .q, ⟨0, 0⟩⟩,
   ⟨.z, .chi, ⟨0, 0⟩⟩,
   ⟨.z, .gamma, ⟨0, 0⟩⟩,
   ⟨.z, .hbar, ⟨0, 0⟩⟩,
   ⟨.z, .ayin, ⟨0, 0⟩⟩,
   ⟨.z, .h, ⟨0, 0⟩⟩,
   ⟨.z, .glottal, ⟨0, 0⟩⟩,
   ⟨.z, .l, ⟨27, 2⟩⟩,
   ⟨.z, .r, ⟨27, 2⟩⟩,
   ⟨.z, .n, ⟨13, 2⟩⟩,
   ⟨.z, .w, ⟨0, 0⟩⟩,
   ⟨.z, .j, ⟨0, 0⟩⟩,
   ⟨.sEmph, .sEmph, ⟨1, 0⟩⟩,
   ⟨.sEmph, .zEmph, ⟨42, 2⟩⟩,
   ⟨.sEmph, .esh, ⟨33, 2⟩⟩,
   ⟨.sEmph, .k, ⟨11, 2⟩⟩,
   ⟨.sEmph, .g, ⟨6, 2⟩⟩,
   ⟨.sEmph, .q, ⟨17, 2⟩⟩,
   ⟨.sEmph, .chi, ⟨15, 2⟩⟩,
   ⟨.sEmph, .gamma, ⟨9, 2⟩⟩,
   ⟨.sEmph, .hbar, ⟨0, 0⟩⟩,
   ⟨.sEmph, .ayin, ⟨0, 0⟩⟩,
   ⟨.sEmph, .h, ⟨0, 0⟩⟩,
   ⟨.sEmph, .glottal, ⟨0, 0⟩⟩,
   ⟨.sEmph, .l, ⟨9, 2⟩⟩,
   ⟨.sEmph, .r, ⟨9, 2⟩⟩,
   ⟨.sEmph, .n, ⟨4, 2⟩⟩,
   ⟨.sEmph, .w, ⟨0, 0⟩⟩,
   ⟨.sEmph, .j, ⟨4, 2⟩⟩,
   ⟨.zEmph, .zEmph, ⟨1, 0⟩⟩,
   ⟨.zEmph, .esh, ⟨17, 2⟩⟩,
   ⟨.zEmph, .k, ⟨7, 2⟩⟩,
   ⟨.zEmph, .g, ⟨13, 2⟩⟩,
   ⟨.zEmph, .q, ⟨9, 2⟩⟩,
   ⟨.zEmph, .chi, ⟨1, 1⟩⟩,
   ⟨.zEmph, .gamma, ⟨21, 2⟩⟩,
   ⟨.zEmph, .hbar, ⟨0, 0⟩⟩,
   ⟨.zEmph, .ayin, ⟨0, 0⟩⟩,
   ⟨.zEmph, .h, ⟨0, 0⟩⟩,
   ⟨.zEmph, .glottal, ⟨0, 0⟩⟩,
   ⟨.zEmph, .l, ⟨14, 2⟩⟩,
   ⟨.zEmph, .r, ⟨14, 2⟩⟩,
   ⟨.zEmph, .n, ⟨7, 2⟩⟩,
   ⟨.zEmph, .w, ⟨0, 0⟩⟩,
   ⟨.zEmph, .j, ⟨9, 2⟩⟩,
   ⟨.esh, .esh, ⟨1, 0⟩⟩,
   ⟨.esh, .k, ⟨0, 0⟩⟩,
   ⟨.esh, .g, ⟨0, 0⟩⟩,
   ⟨.esh, .q, ⟨0, 0⟩⟩,
   ⟨.esh, .chi, ⟨0, 0⟩⟩,
   ⟨.esh, .gamma, ⟨0, 0⟩⟩,
   ⟨.esh, .hbar, ⟨0, 0⟩⟩,
   ⟨.esh, .ayin, ⟨0, 0⟩⟩,
   ⟨.esh, .h, ⟨0, 0⟩⟩,
   ⟨.esh, .glottal, ⟨0, 0⟩⟩,
   ⟨.esh, .l, ⟨9, 2⟩⟩,
   ⟨.esh, .r, ⟨9, 2⟩⟩,
   ⟨.esh, .n, ⟨5, 2⟩⟩,
   ⟨.esh, .w, ⟨0, 0⟩⟩,
   ⟨.esh, .j, ⟨0, 0⟩⟩,
   ⟨.k, .k, ⟨1, 0⟩⟩,
   ⟨.k, .g, ⟨38, 2⟩⟩,
   ⟨.k, .q, ⟨32, 2⟩⟩,
   ⟨.k, .chi, ⟨12, 2⟩⟩,
   ⟨.k, .gamma, ⟨7, 2⟩⟩,
   ⟨.k, .hbar, ⟨0, 0⟩⟩,
   ⟨.k, .ayin, ⟨0, 0⟩⟩,
   ⟨.k, .h, ⟨0, 0⟩⟩,
   ⟨.k, .glottal, ⟨0, 0⟩⟩,
   ⟨.k, .l, ⟨0, 0⟩⟩,
   ⟨.k, .r, ⟨0, 0⟩⟩,
   ⟨.k, .n, ⟨0, 0⟩⟩,
   ⟨.k, .w, ⟨0, 0⟩⟩,
   ⟨.k, .j, ⟨12, 2⟩⟩,
   ⟨.g, .g, ⟨1, 0⟩⟩,
   ⟨.g, .q, ⟨15, 2⟩⟩,
   ⟨.g, .chi, ⟨7, 2⟩⟩,
   ⟨.g, .gamma, ⟨15, 2⟩⟩,
   ⟨.g, .hbar, ⟨0, 0⟩⟩,
   ⟨.g, .ayin, ⟨0, 0⟩⟩,
   ⟨.g, .h, ⟨0, 0⟩⟩,
   ⟨.g, .glottal, ⟨0, 0⟩⟩,
   ⟨.g, .l, ⟨0, 0⟩⟩,
   ⟨.g, .r, ⟨0, 0⟩⟩,
   ⟨.g, .n, ⟨0, 0⟩⟩,
   ⟨.g, .w, ⟨0, 0⟩⟩,
   ⟨.g, .j, ⟨24, 2⟩⟩,
   ⟨.q, .q, ⟨1, 0⟩⟩,
   ⟨.q, .chi, ⟨32, 2⟩⟩,
   ⟨.q, .gamma, ⟨15, 2⟩⟩,
   ⟨.q, .hbar, ⟨8, 2⟩⟩,
   ⟨.q, .ayin, ⟨4, 2⟩⟩,
   ⟨.q, .h, ⟨4, 2⟩⟩,
   ⟨.q, .glottal, ⟨9, 2⟩⟩,
   ⟨.q, .l, ⟨0, 0⟩⟩,
   ⟨.q, .r, ⟨0, 0⟩⟩,
   ⟨.q, .n, ⟨0, 0⟩⟩,
   ⟨.q, .w, ⟨0, 0⟩⟩,
   ⟨.q, .j, ⟨4, 2⟩⟩,
   ⟨.chi, .chi, ⟨1, 0⟩⟩,
   ⟨.chi, .gamma, ⟨42, 2⟩⟩,
   ⟨.chi, .hbar, ⟨23, 2⟩⟩,
   ⟨.chi, .ayin, ⟨13, 2⟩⟩,
   ⟨.chi, .h, ⟨14, 2⟩⟩,
   ⟨.chi, .glottal, ⟨1, 1⟩⟩,
   ⟨.chi, .l, ⟨0, 0⟩⟩,
   ⟨.chi, .r, ⟨0, 0⟩⟩,
   ⟨.chi, .n, ⟨0, 0⟩⟩,
   ⟨.chi, .w, ⟨0, 0⟩⟩,
   ⟨.chi, .j, ⟨13, 2⟩⟩,
   ⟨.gamma, .gamma, ⟨1, 0⟩⟩,
   ⟨.gamma, .hbar, ⟨12, 2⟩⟩,
   ⟨.gamma, .ayin, ⟨17, 2⟩⟩,
   ⟨.gamma, .h, ⟨14, 2⟩⟩,
   ⟨.gamma, .glottal, ⟨9, 2⟩⟩,
   ⟨.gamma, .l, ⟨0, 0⟩⟩,
   ⟨.gamma, .r, ⟨0, 0⟩⟩,
   ⟨.gamma, .n, ⟨0, 0⟩⟩,
   ⟨.gamma, .w, ⟨0, 0⟩⟩,
   ⟨.gamma, .j, ⟨27, 2⟩⟩,
   ⟨.hbar, .hbar, ⟨1, 0⟩⟩,
   ⟨.hbar, .ayin, ⟨55, 2⟩⟩,
   ⟨.hbar, .h, ⟨5, 1⟩⟩,
   ⟨.hbar, .glottal, ⟨27, 2⟩⟩,
   ⟨.hbar, .l, ⟨0, 0⟩⟩,
   ⟨.hbar, .r, ⟨0, 0⟩⟩,
   ⟨.hbar, .n, ⟨0, 0⟩⟩,
   ⟨.hbar, .w, ⟨0, 0⟩⟩,
   ⟨.hbar, .j, ⟨0, 0⟩⟩,
   ⟨.ayin, .ayin, ⟨1, 0⟩⟩,
   ⟨.ayin, .h, ⟨56, 2⟩⟩,
   ⟨.ayin, .glottal, ⟨3, 1⟩⟩,
   ⟨.ayin, .l, ⟨0, 0⟩⟩,
   ⟨.ayin, .r, ⟨0, 0⟩⟩,
   ⟨.ayin, .n, ⟨0, 0⟩⟩,
   ⟨.ayin, .w, ⟨0, 0⟩⟩,
   ⟨.ayin, .j, ⟨0, 0⟩⟩,
   ⟨.h, .h, ⟨1, 0⟩⟩,
   ⟨.h, .glottal, ⟨38, 2⟩⟩,
   ⟨.h, .l, ⟨0, 0⟩⟩,
   ⟨.h, .r, ⟨0, 0⟩⟩,
   ⟨.h, .n, ⟨0, 0⟩⟩,
   ⟨.h, .w, ⟨0, 0⟩⟩,
   ⟨.h, .j, ⟨0, 0⟩⟩,
   ⟨.glottal, .glottal, ⟨1, 0⟩⟩,
   ⟨.glottal, .l, ⟨0, 0⟩⟩,
   ⟨.glottal, .r, ⟨0, 0⟩⟩,
   ⟨.glottal, .n, ⟨0, 0⟩⟩,
   ⟨.glottal, .w, ⟨0, 0⟩⟩,
   ⟨.glottal, .j, ⟨0, 0⟩⟩,
   ⟨.l, .l, ⟨1, 0⟩⟩,
   ⟨.l, .r, ⟨8, 1⟩⟩,
   ⟨.l, .n, ⟨33, 2⟩⟩,
   ⟨.l, .w, ⟨0, 0⟩⟩,
   ⟨.l, .j, ⟨0, 0⟩⟩,
   ⟨.r, .r, ⟨1, 0⟩⟩,
   ⟨.r, .n, ⟨33, 2⟩⟩,
   ⟨.r, .w, ⟨0, 0⟩⟩,
   ⟨.r, .j, ⟨0, 0⟩⟩,
   ⟨.n, .n, ⟨1, 0⟩⟩,
   ⟨.n, .w, ⟨0, 0⟩⟩,
   ⟨.n, .j, ⟨0, 0⟩⟩,
   ⟨.w, .w, ⟨1, 0⟩⟩,
   ⟨.w, .j, ⟨0, 0⟩⟩,
   ⟨.j, .j, ⟨1, 0⟩⟩]

/-- A row of Table IV, p. 203: the observed and expected co-occurrence of the consonant pairs in
a similarity interval. -/
structure Cooccurrence where
  /-- The pairs observed. -/
  observed : ℕ
  /-- The pairs expected at random. -/
  expected : Decimal
  /-- Observed over expected. -/
  oe : Decimal
  deriving DecidableEq, Repr

/-- The cells of Table IV, p. 203, by bin and distance; counted in a dictionary or lexical
database; checked against the page images. -/
def cooccurrence : SimilarityBin → Distance → Cooccurrence
  | .zero, .adjacent => ⟨4222, ⟨34568, 1⟩, ⟨122, 2⟩⟩
  | .zero, .nonAdjacent => ⟨1909, ⟨17158, 1⟩, ⟨111, 2⟩⟩
  | .upTo01, .adjacent => ⟨484, ⟨4596, 1⟩, ⟨105, 2⟩⟩
  | .upTo01, .nonAdjacent => ⟨252, ⟨2472, 1⟩, ⟨102, 2⟩⟩
  | .upTo02, .adjacent => ⟨378, ⟨4538, 1⟩, ⟨83, 2⟩⟩
  | .upTo02, .nonAdjacent => ⟨226, ⟨2313, 1⟩, ⟨98, 2⟩⟩
  | .upTo03, .adjacent => ⟨167, ⟨2827, 1⟩, ⟨59, 2⟩⟩
  | .upTo03, .nonAdjacent => ⟨102, ⟨1307, 1⟩, ⟨78, 2⟩⟩
  | .upTo04, .adjacent => ⟨91, ⟨2813, 1⟩, ⟨32, 2⟩⟩
  | .upTo04, .nonAdjacent => ⟨139, ⟨1542, 1⟩, ⟨90, 2⟩⟩
  | .upTo05, .adjacent => ⟨3, ⟨925, 1⟩, ⟨3, 2⟩⟩
  | .upTo05, .nonAdjacent => ⟨10, ⟨299, 1⟩, ⟨25, 2⟩⟩
  | .upTo06, .adjacent => ⟨2, ⟨317, 1⟩, ⟨6, 2⟩⟩
  | .upTo06, .nonAdjacent => ⟨9, ⟨191, 1⟩, ⟨47, 2⟩⟩
  | .pointEight, .adjacent => ⟨0, ⟨532, 1⟩, ⟨0, 0⟩⟩
  | .pointEight, .nonAdjacent => ⟨11, ⟨226, 1⟩, ⟨49, 2⟩⟩
  | .one, .adjacent => ⟨1, ⟨2365, 1⟩, ⟨1, 2⟩⟩
  | .one, .nonAdjacent => ⟨16, ⟨1130, 1⟩, ⟨14, 2⟩⟩

/-- A row of Table V, p. 207: the fit of a model to the O/E of every consonant pair in every
position. -/
structure ModelFit where
  /-- The proportion of variance explained. -/
  rSquared : Decimal
  /-- The residual sum of squares. -/
  residualSS : ℕ
  /-- The residual sum of squares over homorganic pairs. -/
  homorganicSS : ℕ
  /-- The residual sum of squares over pairs of one major class. -/
  majorClassSS : ℕ
  /-- The number of parameters. -/
  parameters : ℕ
  deriving DecidableEq, Repr

/-- The cells of Table V, p. 207, by model; fitted or simulated by a model; checked against the
page images. -/
def modelFits : Model → ModelFit
  | .frequency => ⟨⟨57, 2⟩, 14476, 8697, 7101, 0⟩  -- O = E
  | .categorical => ⟨⟨70, 2⟩, 10008, 4805, 3189, 2⟩  -- O/E = 0 for homorganic, O/E = 1.17 otherwise
  | .soft =>  -- O/E = 0 for adjacent ident, O/E = 0.38 for maj class, O/E = 1.17 otherwise
    ⟨⟨73, 2⟩,
     8918,
     3716,
     2100,
     3⟩
  | .feature => ⟨⟨71, 2⟩, 9737, 4573, 3018, 8⟩  -- O/E = 1.20 to 0
  | .naturalClasses => ⟨⟨75, 2⟩, 8489, 3286, 1335, 11⟩  -- O/E = 1.22 to 0

/-- A row of p. 185: roots of the form C1 C2 C, counted with the two consonants in first and
second position. -/
structure RootType where
  /-- The first consonant. -/
  c1 : Consonant
  /-- The second consonant. -/
  c2 : Consonant
  /-- The roots observed. -/
  observed : ℕ
  /-- The roots expected at random. -/
  expected : Decimal
  /-- Observed over expected. -/
  oe : Decimal
  deriving DecidableEq, Repr

/-- The 3 rows of p. 185, in the paper's order; counted in a dictionary or lexical database;
checked against the page images. -/
def rootTypes : List RootType :=
  [⟨.d, .t, 0, ⟨23, 1⟩, ⟨0, 0⟩⟩,
   ⟨.d, .s, 2, ⟨29, 1⟩, ⟨69, 2⟩⟩,
   ⟨.d, .g, 4, ⟨33, 1⟩, ⟨121, 2⟩⟩]

end FrischPierrehumbertBroe2004
