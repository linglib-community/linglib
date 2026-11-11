module

public import Linglib.Fragments.Indonesian.Phonology
public import Linglib.Phonology.Segmental.NaturalClass
public import Linglib.Data.Wordlist.Sneddon1996

/-!
# Sneddon (1996): sound changes in complex words

Sneddon's grammar of Indonesian gives the nasal that ends the prefixes *meN-* and *peN-* by
lists of the sounds a base may begin with: *m* before *b*, *p*, *f*; *n* before *d*, *t*, *c*,
*j*, *sy*, *z*; *ny* before *s*; *ng* before a vowel and before *g*, *k*, *h*, *kh*; and no
nasal before the other consonants, with an initial *p*, *t*, *s* or *k* lost. The Indonesian
phonology fragment derives the nasal from the place of the following obstruent, and [the two
agree on every phoneme](##juncture_eq_of_mem_rules): each list's nasal [is homorganic with its
obstruents](##homorganic_iff_of_mem_rules), the palatal before *s* excepted. Since *k* and *s*
are lost, [a derived form does not determine its base](##prefixN_k_cons). A base that keeps
its initial, as borrowings may, has [the nasal of the same place](##junctureRetained_eq_iff),
so that a kept *s* follows *n*. The prefixes *ber-*, *per-* and *ter-* lose their *r* before a
base in *r* and before one such as *serta*. Of the derivations the grammar prints for these
rules and their exceptions, [the rules give all but those it calls irregular](##derived_iff).

## Implementation notes

* The grammar states its rules in spelling. The nasal before *c*, *j* and *sy* is the *n* it
  writes, and the two vowels spelled *e* are told apart in the segments of each form.
* A form is read through its glyphs in PHOIBLE's Standard Indonesian inventory, which lacks
  the palatal glide. [Every form is read](##segmentsOf_all), so no derivation holds for want of
  a reading.
* The bases marked as borrowed are the eight the grammar gives as borrowings that keep their
  initial. Where the grammar calls a loss irregular, of the *p* of a base such as *percaya*
  after *meN-* or of the *r* of a prefix before one, both outcomes are allowed.

## TODO

* The *menge-* of one-syllable bases and the nasal kept on a reduplicated base.

## References

* [sneddon-1996]
* [mcdonnell-wu-mckinnon-adelaar-2024]
-/

@[expose] public section

namespace Sneddon1996

open Phonology Indonesian.Phonology Sneddon1996.Wordlist CLDF.Wordlist

/-! ### The rules -/

/-- The rules for N: each list of base-initial sounds with the nasal that N becomes before
them, `none` where N is lost (pp. 9–10). -/
def rules : List (Finset Segment × Option Segment) :=
  [(vowels, some ng), ({b, p, f}, some m), ({d, t, c, j, sy, z}, some n), ({s}, some ny),
    ({g, k, h, kh}, some ng), ({l, r, m, n, ny, ng, w, y}, none)]

-- one rule applies to each phoneme
theorem pairwise_disjoint_rules : rules.Pairwise (Function.onFun Disjoint Prod.fst) := by
  decide +kernel

theorem sup_rules : rules.toFinset.sup Prod.fst = consonants ∪ vowels := by
  decide +kernel

/-- The juncture of the fragment is that of the rules: before a sound of a rule's list the
nasal is the rule's, and the sound follows it unless it is *p*, *t*, *s* or *k*, which are
lost (pp. 9–10). -/
theorem juncture_eq_of_mem_rules : ∀ r ∈ rules, ∀ x ∈ r.1,
    juncture x = r.2.toList ++ if x ∈ substituting then [] else [x] := by
  decide +kernel

/-- The nasal of each rule is homorganic with the obstruents of its list, except the palatal
*ny* before *s*. -/
theorem homorganic_iff_of_mem_rules : ∀ r ∈ rules, ∀ N ∈ r.2, ∀ x ∈ r.1, trigger ≤ x →
    (N.Homorganic x ↔ x ≠ s) := by
  decide +kernel

/-- The voiceless obstruents. -/
def voicelessObstruent : Segment :=
  Segment.ofSpecs [(.consonantal, true), (.sonorant, false), (.voice, false)]

theorem substituting_subset :
    substituting ⊆ voicelessObstruent.naturalClass consonants := by
  decide +kernel

-- the voiceless obstruents that are not lost are `c` and the loan fricatives (pp. 9–10)
theorem voicelessObstruents_sdiff_substituting :
    voicelessObstruent.naturalClass consonants \ substituting = {c, f, sy, kh} := by
  decide +kernel

/-- "The initial sound of the base cannot be predicted from the form of the derived verb"
(p. 10): a base in *k* and a vowel has the derived form of the base without the *k*, as
*mengarang* from *karang* and from *arang* (p. 11). -/
theorem prefixN_k_cons (pre : List Segment) {v : Segment} (hv : v ∈ vowels) (w : List Segment) :
    prefixN juncture pre (k :: v :: w) = prefixN juncture pre (v :: w) := by
  have hk : juncture k = [ng] := by decide +kernel
  have h : ∀ v ∈ vowels, juncture v = [ng, v] := by decide +kernel
  simp [hk, h v hv]

-- *menyewa* from *sewa* and *menyanyi* from *nyanyi* (pp. 10–11)
theorem prefixN_s_cons (pre w : List Segment) :
    prefixN juncture pre (s :: w) = prefixN juncture pre (ny :: w) := by
  have hs : juncture s = [ny] := by decide +kernel
  have hny : juncture ny = [ny] := by decide +kernel
  simp [hs, hny]

/-- "If *s* is not lost N becomes *n*" (p. 11): before a kept *p*, *t*, *s* or *k* the nasal is
the one the consonant fuses into, except before *s*. -/
theorem junctureRetained_eq_iff :
    ∀ x ∈ substituting, junctureRetained x = [fuse x, x] ↔ x ≠ s := by
  decide +kernel

/-! ### The forms -/

/-- The phoneme written with a glyph of PHOIBLE's Standard Indonesian inventory, or with that of
the palatal glide, which the inventory lacks. -/
def segment? (g : String) : Option Segment :=
  if g = "j" then some y else Data.PHOIBLE.Inventories.Indonesian.ind.segment? g

/-- The segments of a form, each read through its glyph. -/
def segmentsOf (w : Form Cell) : Option (List Segment) :=
  w.segments.mapM segment?

-- every form is read, as phonemes of the fragment
theorem segmentsOf_all :
    ∀ w ∈ all, ∃ ss ∈ segmentsOf w, ∀ x ∈ ss, x ∈ consonants ∪ vowels := by
  decide +kernel

/-- The segments of a prefix before its nasal or its *r*. -/
def Wordlist.Prefix.segments : Prefix → List Segment
  | .meN => [m, e]
  | .peN | .per => [p, e]
  | .ber => [b, e]
  | .ter => [t, e]

/-- The prefixes that end in the nasal. -/
def Wordlist.Prefix.IsNasal (pre : Prefix) : Prop := pre = .meN ∨ pre = .peN

instance : DecidablePred Prefix.IsNasal := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- The segments of the prefix *per-* after a nasal prefix. -/
def Wordlist.Inner.segments : Inner → List Segment
  | .per => [p, e, r]

/-- The segments of a suffix. -/
def Wordlist.Suffix.segments : Suffix → List Segment
  | .kan => [k, a, n]
  | .i => [Indonesian.Phonology.i]
  | .an => [a, n]

/-- `build stem a base` is the form that the analysis `a` builds on `base`: its prefix, attached
as `stem` gives to *per-*, where the analysis has it, and the base, and then the suffix. An
analysis without a prefix builds none. -/
def build (stem : Prefix → List Segment → List Segment) (a : Analysis) (base : List Segment) :
    Option (List Segment) :=
  a.pre.map fun pre ↦
    stem pre (a.inner.elim [] Inner.segments ++ base) ++ a.suffix.elim [] Suffix.segments

/-- The form the rules give. "If prefix *meN-* is followed by prefix *per-* the initial *p* of
*per-* is not lost", and it "is lost following prefix *peN-*" (p. 11). -/
def regular (a : Analysis) : List Segment → Option (List Segment) :=
  build (fun pre ↦
    if pre.IsNasal then
      prefixN (if pre = .meN ∧ a.inner = some .per then junctureRetained else juncture)
        pre.segments
    else prefixR pre.segments) a

/-- The form that keeps what the rules drop, the sound after a nasal prefix or the *r* of the
prefix. -/
def retained : Analysis → List Segment → Option (List Segment) :=
  build fun pre ↦
    if pre.IsNasal then prefixN junctureRetained pre.segments else (pre.segments ++ r :: ·)

/-- A base may keep its initial when the grammar gives it as a borrowing. One that begins with
a consonant, the schwa, *r* and a consonant may keep its *p* after *meN-*, where "the initial
*p* is lost irregularly" (p. 11), and may keep the *r* of *ber-*, *per-* and *ter-*, whose loss
"is not entirely regular" (p. 9). The base has the analysis `b` and the derived form the
analysis `a`. -/
def MayRetain (b a : Analysis) (base : List Segment) : Prop :=
  b.origin = some .borrowed ∨
    (a.pre = some .meN ∧ base.head? = some p ∨ ∃ pre ∈ a.pre, ¬ pre.IsNasal) ∧ BeginsCerC base

instance (b a : Analysis) (base : List Segment) : Decidable (MayRetain b a base) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- A relation is derived when its target is the form the rules give for its base, or the form
that keeps the initial of a base that may keep it. -/
def Derived (r : FormRelation Analysis) : Prop :=
  ∃ base ∈ segmentsOf r.form.form, ∃ w ∈ segmentsOf r.target.form,
    regular r.target base = some w ∨
      MayRetain r.form r.target base ∧ retained r.target base = some w

instance : DecidablePred Derived := fun _ ↦ inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- The forms the grammar sets apart from its rules (pp. 9, 12–13): *telanjur* and *telantar*,
which lose the *r* of *ter-* before *l*, and *belajar* and *pelajaran*, which have *l* for the
*r*; *mempengaruhi*, *mempunyai* and the *mengkaji* of research, which keep the initial of a
base it does not give as borrowed; the *peng-* of *penglihatan*, *pengrajin* and *penglepasan*;
and *menyair* and *penyair*, which lose an initial *sy*. -/
def exceptions : List (Form Cell) :=
  [telanjur, telantar, belajar, pelajaran, mempengaruhi, mempunyai, mengkaji, pengkajian,
    penglihatan, pengrajin, penglepasan, menyair, penyair]

/-- The rules derive each form the grammar prints for them and for their exceptions in *per-*
and in borrowings, and none of the forms it sets apart (pp. 8–13, 26). -/
theorem derived_iff : ∀ r ∈ analysisRelations, Derived r ↔ r.target.form ∉ exceptions := by
  decide +kernel

end Sneddon1996
