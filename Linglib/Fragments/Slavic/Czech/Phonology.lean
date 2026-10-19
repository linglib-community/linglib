module

public import Linglib.Data.PHOIBLE.Inventories.Czech
public import Linglib.Phonology.Segmental.PHOIBLE

/-!
# Czech phonology

This file defines the phonemes of Czech as segments, after Short's description of the language,
with the second palatalization of velars and the reading of Czech spelling as phonemes. Czech
has five vowels, each short and long, and twenty-five consonantal phonemes. The second
palatalization replaces *k* by *c*, *h* and *g* by *z*, and *ch* by *š*.

The spelling is close to the phonemes. A palatal *ď*, *ť* or *ň* is written on a following *ě*
or *i*, as in *dě* and *di*, a labial before *ě* is followed by /j/ and *m* by /ň/, and *i* and
*y* write one vowel.

## Main definitions

* `Czech.Phonology.a`, `Czech.Phonology.ch` and the like: the phonemes, named by the letters
  Short writes them with, and `Czech.Phonology.inventory` the set of them.
* `Czech.Phonology.palatalizing`, `Czech.Phonology.secondPalatalization`: the segments the second
  palatalization of velars changes, *k*, *g*, *h* and *ch*, and the rule.
* `Czech.Phonology.letterValues`: the phonemes each letter writes, with `valuesBeforeĚ` and
  `valuesBeforeI` for the letters a following *ě* or *i* reads differently.
* `Czech.Phonology.ofString?`, `Czech.Phonology.letter`: the phonemes a word writes, and the
  letter that writes a phoneme.

## Main results

* `Czech.Phonology.exists_mem_ces`: each phoneme is the segment of a phoneme of PHOIBLE's Czech
  inventory.
* `Czech.Phonology.isSome_letter`: each phoneme has a letter.

## Implementation notes

The inventory is PHOIBLE 1140, whose consonants are Short's twenty-five and whose vowels are
his five short and five long vowels and three diphthongs. PHOIBLE marks /oː/ and the diphthongs
/au/ and /eu/ marginal, the three that Short confines to loan-words (p. 456). PHOIBLE's other
Czech inventories, 2274 and 2480, add the glottal stop and the voiced affricate [dž], which
Short counts as not phonemic (p. 457).

Hayes's features have no length, so a long vowel is two segments of its quality, and a
diphthong, which the chart omits as contour-valued, is its two vowels. A vowel keeps the
features that distinguish the five, since the chart gives the short high vowel as the lax [ɪ]
and the long one as the tense [iː]. The chart's *t*, *d* and *n* are alveolar where Short calls
them dental, a difference in [distributed] on which no Czech contrast depends.

`ofString?` reads the phonemes and not their realization: the final devoicing and the voicing
assimilation of obstruents (p. 458) are left out, so that *oběd* 'lunch' is /objed/ where Short
writes /objet/. It follows Short's rules for the palatals without exception, so a loan-word in
which *di*, *ti* or *ni* writes a plain dental is misread, and it reads *x* as [ks], one of
Short's two readings.

## References

* [short-1993-czech]
* [hayes-2009]
* [moran-mccloy-2019]
-/

@[expose] public section

open Phonology Data.PHOIBLE

namespace Czech.Phonology

/-! ### Phonemes

The phonemes are Short's (pp. 456–457), each named by the letter he writes it with, so that
`ť` is [c], `c` is [ts] and `h` is [ɦ]. -/

/-- The features that distinguish the five vowels, with [syllabic] marking them as vowels. -/
def contrastive : Finset Phonology.Feature := {.syllabic, .high, .low, .back, .round}

/-- A vowel is its chart entry's segment on the features that distinguish the five vowels. -/
def vowel (m : FeatureMatrix) : Segment := .ofChart m ⊥ contrastive

/-- The low vowel /a/, long /aː/ written *á*. -/
def a : Segment := vowel .«a»

/-- The mid front vowel /e/, [ɛ] in PHOIBLE's inventory, long /eː/ written *é*. -/
def e : Segment := vowel .«ɛ»

/-- The high front vowel /i/, written *i* or *y* and long *í* or *ý*, the letters with *y*
going back to Proto-Indo-European *ū* (p. 456). PHOIBLE's inventory gives it as the lax [ɪ]
short and the tense [iː] long. -/
def i : Segment := vowel .«ɪ»

/-- The mid back vowel /o/. Its long counterpart /oː/, written *ó*, occurs only in loan-words
(p. 456). -/
def o : Segment := vowel .«o»

/-- The high back vowel /u/, long /uː/ written *ú* and, where it developed from /oː/, *ů*
(p. 456). -/
def u : Segment := vowel .«u»

/-- The voiceless labial occlusive /p/. -/
def p : Segment := .ofChart .«p»

/-- The voiced labial occlusive /b/. -/
def b : Segment := .ofChart .«b»

/-- The labial nasal occlusive /m/. -/
def m : Segment := .ofChart .«m»

/-- The voiceless dental occlusive /t/. -/
def t : Segment := .ofChart .«t»

/-- The voiced dental occlusive /d/. -/
def d : Segment := .ofChart .«d»

/-- The dental nasal occlusive /n/. -/
def n : Segment := .ofChart .«n»

/-- The voiceless palatal occlusive /ť/, [c]. -/
def ť : Segment := .ofChart .«c»

/-- The voiced palatal occlusive /ď/, [ɟ]. -/
def ď : Segment := .ofChart .«ɟ»

/-- The palatal nasal occlusive /ň/, [ɲ]. -/
def ň : Segment := .ofChart .«ɲ»

/-- The voiceless velar occlusive /k/. -/
def k : Segment := .ofChart .«k»

/-- The voiced velar occlusive /g/. Original /g/ changed regularly into /h/, so /g/ is
restricted to borrowings (p. 457). -/
def g : Segment := .ofChart .«ɡ»

/-- The voiceless alveolar semi-occlusive /c/, [ts]. -/
def c : Segment := .ofChart .«ts»

/-- The voiceless post-alveolar semi-occlusive /č/, [tʃ]. -/
def č : Segment := .ofChart .«t̠ʃ»

/-- The voiceless labio-dental fricative /f/, largely confined to loans (p. 458). -/
def f : Segment := .ofChart .«f»

/-- The voiced labio-dental fricative /v/. -/
def v : Segment := .ofChart .«v»

/-- The voiceless alveolar fricative /s/. -/
def s : Segment := .ofChart .«s»

/-- The voiced alveolar fricative /z/. -/
def z : Segment := .ofChart .«z»

/-- The voiceless post-alveolar fricative /š/, [ʃ], formerly palatal. -/
def š : Segment := .ofChart .«ʃ»

/-- The voiced post-alveolar fricative /ž/, [ʒ], formerly palatal. -/
def ž : Segment := .ofChart .«ʒ»

/-- The palatal /j/, which Short lists with the fricatives and the chart gives as the glide. -/
def j : Segment := .ofChart .«j»

/-- The voiceless velar fricative /ch/, [x], whose letter is one letter of the alphabet
(p. 459). -/
def ch : Segment := .ofChart .«x»

/-- The laryngeal fricative /h/, [ɦ], "voiced (!)" in Short's list. -/
def h : Segment := .ofChart .«ɦ»

/-- The lateral /l/, "almost frictionless". -/
def l : Segment := .ofChart .«l»

/-- The alveolar roll /r/. -/
def r : Segment := .ofChart .«r»

/-- The post-alveolar vibrant /ř/, "with considerable friction", the chart's raised trill
[r̝]. -/
def ř : Segment := .ofChart .«r̝»

/-- The phonemes, Short's five vowels and twenty-five consonantal phonemes, pairwise
distinct. -/
def inventory : Finset Segment :=
  ⟨↑[a, e, i, o, u, p, b, m, t, d, n, ť, ď, ň, k, g, c, č, f, v, s, z, š, ž, j, ch, h, l, r, ř],
    by decide +kernel⟩

/-- The vowels of the inventory. -/
def vowels : Finset Segment := inventory.filter (·.IsVowel)

/-- The consonantal phonemes of the inventory. -/
def consonants : Finset Segment := inventory.filter (¬ ·.IsVowel)

/-- The segment of a PHOIBLE phoneme, as a vowel where PHOIBLE classes it with the vowels. -/
def ofPhoneme (y : Data.PHOIBLE.Phoneme) : Segment :=
  if y.segmentClass = .vowel then vowel y.features else .ofChart y.features

/-- Each phoneme is the segment of a phoneme of PHOIBLE's Czech inventory. -/
theorem exists_mem_ces :
    ∀ x ∈ inventory, ∃ y ∈ Inventories.Czech.ces.phonemes, x = ofPhoneme y := by
  decide +kernel

/-! ### The second palatalization -/

/-- The segments that the second palatalization changes, *k*, *g*, *h* and *ch* (p. 462). -/
def palatalizing : Finset Segment := {k, g, h, ch}

/-- The second palatalization of velars, "*k* › *c*; *h* › *z*; *ch* › *š* (NB not *s*). Here
too the reflex of *g* has de-affricated from *dz* to *z*" (p. 462). Every other segment is left
as it is. -/
def secondPalatalization (x : Segment) : Segment :=
  if x = k then c else if x = g ∨ x = h then z else if x = ch then š else x

/-! ### Spelling -/

/-- The letters of the Czech alphabet, *ch* being one (p. 459). -/
def alphabet : List String :=
  ["a", "b", "c", "č", "d", "e", "f", "g", "h", "ch", "i", "j", "k", "l", "m", "n", "o", "p", "q",
    "r", "ř", "s", "š", "t", "u", "v", "w", "x", "y", "z", "ž"]

/-- The phonemes each letter writes where no neighbouring letter changes its reading. A long
vowel is two segments, *ě* on its own writes /e/, and *q*, *w* and *x* write [kv], [v] and [ks] in
loan-words (p. 459). -/
def letterValues : List (Char × List Segment) :=
  [('a', [a]), ('á', [a, a]), ('b', [b]), ('c', [c]), ('č', [č]), ('d', [d]), ('ď', [ď]),
    ('e', [e]), ('ě', [e]), ('é', [e, e]), ('f', [f]), ('g', [g]), ('h', [h]), ('i', [i]),
    ('y', [i]), ('í', [i, i]), ('ý', [i, i]), ('j', [j]), ('k', [k]), ('l', [l]), ('m', [m]),
    ('n', [n]), ('ň', [ň]), ('o', [o]), ('ó', [o, o]), ('p', [p]), ('q', [k, v]), ('r', [r]),
    ('ř', [ř]), ('s', [s]), ('š', [š]), ('t', [t]), ('ť', [ť]), ('u', [u]), ('ú', [u, u]),
    ('ů', [u, u]), ('v', [v]), ('w', [v]), ('x', [k, s]), ('z', [z]), ('ž', [ž])]

/-- The letters whose reading *ě* changes, with what they write before it. There *d*, *t* and *n*
write /ď/, /ť/ and /ň/, *b*, *p*, *v* and *f* are followed by /j/, and *m* by /ň/ (p. 459). -/
def valuesBeforeĚ : List (Char × List Segment) :=
  [('d', [ď]), ('t', [ť]), ('n', [ň]), ('b', [b, j]), ('p', [p, j]), ('v', [v, j]), ('f', [f, j]),
    ('m', [m, ň])]

/-- The letters whose reading *i* or *í* changes, *d*, *t* and *n*, which write /ď/, /ť/ and /ň/
before it (p. 459). -/
def valuesBeforeI : List (Char × List Segment) := [('d', [ď]), ('t', [ť]), ('n', [ň])]

/-- The phonemes a letter writes where no neighbouring letter changes its reading. -/
def ofChar (x : Char) : Option (List Segment) := letterValues.lookup x

/-- The phonemes a letter writes before *ě*. -/
def ofCharBeforeĚ (x : Char) : Option (List Segment) := (valuesBeforeĚ.lookup x).or (ofChar x)

/-- The phonemes a letter writes before *i* or *í*. -/
def ofCharBeforeI (x : Char) : Option (List Segment) := (valuesBeforeI.lookup x).or (ofChar x)

/-- `ofChars w` is the phonemes that the letters `w` write, if they are all Czech letters. The
letters *c* and *h* together write /ch/, and a letter before *ě*, *i* or *í* writes what it
writes there. -/
def ofChars : List Char → Option (List Segment)
  | 'c' :: 'h' :: w => (ch :: ·) <$> ofChars w
  | x :: 'ě' :: w => do return (← ofCharBeforeĚ x) ++ e :: (← ofChars w)
  | x :: 'i' :: w => do return (← ofCharBeforeI x) ++ i :: (← ofChars w)
  | x :: 'í' :: w => do return (← ofCharBeforeI x) ++ i :: i :: (← ofChars w)
  | x :: w => do return (← ofChar x) ++ (← ofChars w)
  | [] => some []

/-- `ofString? w` is the phonemes that the word `w` writes, if its letters are all Czech. -/
def ofString? (w : String) : Option (List Segment) := ofChars w.toList

/-- The letter that writes a phoneme on its own, the first in the alphabet that does, or the
palatal *ď*, *ť* or *ň*. -/
def letter (x : Segment) : Option String :=
  (alphabet ++ ["ď", "ť", "ň"]).find? (ofString? · = some [x])

/-- Each phoneme has a letter. -/
theorem isSome_letter : ∀ x ∈ inventory, (letter x).isSome := by decide +kernel

end Czech.Phonology
