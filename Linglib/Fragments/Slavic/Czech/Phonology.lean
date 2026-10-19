module

public import Linglib.Data.PHOIBLE.Inventories.Czech
public import Linglib.Phonology.Segmental.NaturalClass
public import Linglib.Phonology.Segmental.PHOIBLE

/-!
# Czech phonology

This file defines the phonemes of Czech as segments, the natural classes of its velar
alternations, the second palatalization of velars and the reading of Czech spelling as
phonemes, after Short's description of the language. Czech has five vowels, each short and
long, and twenty-five consonantal phonemes. The second palatalization replaces *k* by *c*, *h*
and *g* by *z*, and *ch* by *š*. Short files *h* among the laryngeals, and in the features of
the PHOIBLE chart it is not dorsal, so the four segments the rule changes are not the dorsals.
They are a natural class all the same, the obstruents that are neither labial nor coronal.

The spelling is close to the phonemes. A palatal *ď*, *ť* or *ň* is written on a following *ě*
or *i*, as in *dě* and *di*, a labial before *ě* is followed by /j/ and *m* by /ň/, and *i* and
*y* write one vowel.

## Main definitions

* `Czech.Phonology.a`, `Czech.Phonology.ch` and the like: the phonemes, named by the letters
  Short writes them with, and `Czech.Phonology.inventory` the set of them.
* `Czech.Phonology.dorsals`, `Czech.Phonology.palatalizing`: the velars *k*, *g* and *ch*, and
  these with *h*.
* `Czech.Phonology.secondPalatalization`: the second palatalization of velars.
* `Czech.Phonology.letterValues`: the phonemes each letter writes, with `valuesBeforeĚ` and
  `valuesBeforeI` for the letters a following *ě* or *i* reads differently.
* `Czech.Phonology.ofString?`, `Czech.Phonology.letter`: the phonemes a word writes, and the
  letter that writes a phoneme.

## Main results

* `Czech.Phonology.exists_mem_ces`, `Czech.Phonology.ofPhoneme_mem_iff`: the phonemes are those
  of PHOIBLE's Czech inventory, save its three diphthongs.
* `Czech.Phonology.naturalClass_palatalizing`: the segments the second palatalization changes
  are the obstruents that are neither labial nor coronal.
* `Czech.Phonology.voiced_mem_iff`, `Czech.Phonology.devoiced_mem_iff`: the obstruents paired
  in [voice], all but *c*, *č*, *ch* and *h*.
* `Czech.Phonology.secondPalatalization_g`, `Czech.Phonology.not_exists_merge_eq`: the reflex
  of *g* is that of *k* voiced and de-affricated, so no one feature change gives the rule.
* `Czech.Phonology.forall_mem_values`, `Czech.Phonology.mem_inventory_of_mem_ofString?`: the
  spelling writes phonemes of the inventory.

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

/-- The vowels are the five. -/
theorem vowels_eq : vowels = {a, e, i, o, u} := by decide +kernel

/-- "There are twenty-five consonantal phonemes" (p. 457). -/
theorem card_consonants : consonants.card = 25 := by decide +kernel

/-- The segment of a PHOIBLE phoneme, as a vowel where PHOIBLE classes it with the vowels. -/
def ofPhoneme (y : Data.PHOIBLE.Phoneme) : Segment :=
  if y.segmentClass = .vowel then vowel y.features else .ofChart y.features

/-- Each phoneme is the segment of a phoneme of PHOIBLE's Czech inventory. -/
theorem exists_mem_ces :
    ∀ x ∈ inventory, ∃ y ∈ Inventories.Czech.ces.phonemes, x = ofPhoneme y := by
  decide +kernel

/-- Every phoneme of PHOIBLE's Czech inventory has the segment of one here, a long vowel that of
its short counterpart, save the three diphthongs, whose height changes. -/
theorem ofPhoneme_mem_iff : ∀ y ∈ Inventories.Czech.ces.phonemes,
    ofPhoneme y ∈ inventory ↔ y.glyph ∉ ["au", "ou", "ɛu"] := by
  decide +kernel

/-! ### Natural classes -/

/-- The description of the velar obstruents, dorsal and not coronal. -/
def velar : Segment := Segment.ofSpecs [(.sonorant, false), (.dorsal, true), (.coronal, false)]

/-- The dorsals, the natural class of the velar obstruents. -/
def dorsals : Finset Segment := velar.naturalClass inventory

/-- The dorsals are Short's velars *k*, *g* and *ch*. -/
theorem dorsals_eq : dorsals = {k, g, ch} := by decide +kernel

/-- The dorsals are a natural class. -/
theorem isNaturalClass_dorsals : IsNaturalClass inventory dorsals :=
  isNaturalClass_naturalClass ⟨k, by decide +kernel⟩

/-- The segments that the second palatalization changes, *k*, *g*, *h* and *ch* (p. 462). -/
def palatalizing : Finset Segment := {k, g, h, ch}

/-- The palatalizing segments are the dorsals and *h*, which is not dorsal. Short files it
among the laryngeals (p. 457), although it alternates with *z* as *g* does (p. 462). -/
theorem palatalizing_eq : palatalizing = insert h dorsals ∧ h.HasValue .dorsal false := by
  decide +kernel

/-- The palatalizing segments are nonetheless a natural class, the obstruents that are neither
labial nor coronal: every other obstruent of the inventory is labial or coronal. -/
theorem naturalClass_palatalizing :
    (Segment.ofSpecs [(.sonorant, false), (.labial, false), (.coronal, false)]).naturalClass
      inventory = palatalizing := by
  decide +kernel

/-- The palatalizing segments are a natural class. -/
theorem isNaturalClass_palatalizing : IsNaturalClass inventory palatalizing :=
  naturalClass_palatalizing ▸ isNaturalClass_naturalClass ⟨k, by decide +kernel⟩

/-! ### Voicing pairs -/

/-- The voiceless obstruents whose counterpart in [voice] is a phoneme are all but *c*, *č* and
*ch*, whose counterparts [dz], [dž] and [ɣ] occur only as positional variants
(pp. 457–458). -/
theorem voiced_mem_iff : ∀ x ∈ inventory, x.HasValue .sonorant false → x.HasValue .voice false →
    (x.setFeature .voice true ∈ inventory ↔ x ≠ c ∧ x ≠ č ∧ x ≠ ch) := by
  decide +kernel

/-- The counterparts in [voice] of *c*, *č* and *ch* are [dz], [dž] and [ɣ]. Where /x/ might
assimilate, "it voices not to /h/, but to [ɣ]" (p. 458). -/
theorem setFeature_voice_c_č_ch :
    c.setFeature .voice true = .ofChart .«dz» ∧ č.setFeature .voice true = .ofChart .«d̠ʒ» ∧
      ch.setFeature .voice true = .ofChart .«ɣ» := by
  decide +kernel

/-- The voiced obstruents whose counterpart in [voice] is a phoneme are all but *h*, whose
counterpart is the voiceless glottal [h]. Where voice is neutralized Short gives /x/ as the
voiceless counterpart of /h/ (p. 458), which differs from it in more than [voice]. -/
theorem devoiced_mem_iff : ∀ x ∈ inventory, x.HasValue .sonorant false →
    x.HasValue .voice true → (x.setFeature .voice false ∈ inventory ↔ x ≠ h) := by
  decide +kernel

/-- *h* and *ch*, "a nearly matching pair of fricatives" (p. 462), differ in [voice],
[spread glottis] and [consonantal], and in [dorsal] and the tongue-body features that go with
it. -/
theorem h_ch : Finset.univ.filter (fun ft ↦ h ft ≠ ch ft) =
    {.consonantal, .voice, .spreadGlottis, .dorsal, .high, .low, .front, .back} := by
  decide +kernel

/-! ### The second palatalization -/

/-- The second palatalization of velars, "*k* › *c*; *h* › *z*; *ch* › *š* (NB not *s*). Here
too the reflex of *g* has de-affricated from *dz* to *z*" (p. 462). Every other segment is left
as it is. -/
def secondPalatalization (x : Segment) : Segment :=
  if x = k then c else if x = g ∨ x = h then z else if x = ch then š else x

/-- The second palatalization leaves every segment but the four as it is. -/
theorem secondPalatalization_of_notMem {x : Segment} (hx : x ∉ palatalizing) :
    secondPalatalization x = x := by
  simp only [palatalizing, Finset.mem_insert, Finset.mem_singleton, not_or] at hx
  simp [secondPalatalization, hx]

/-- The reflexes are *c*, *z* and *š*. -/
theorem image_secondPalatalization : palatalizing.image secondPalatalization = {c, z, š} := by
  decide +kernel

/-- The reflex of a palatalizing segment is a phoneme, a coronal strident that is not dorsal,
and has its voicing. -/
theorem secondPalatalization_mem : ∀ x ∈ palatalizing,
    secondPalatalization x ∈ inventory ∧ (secondPalatalization x).HasValue .coronal true ∧
      (secondPalatalization x).HasValue .strident true ∧
      (secondPalatalization x).HasValue .dorsal false ∧
      secondPalatalization x .voice = x .voice := by
  decide +kernel

/-- The reflex of *g* is that of *k* voiced, [dz], de-affricated, and *h*, the Czech reflex of
Proto-Slavic *g* (p. 461), shares it. *k* and *g* differ in [voice] alone, and their reflexes in
[continuant] as well. -/
theorem secondPalatalization_g :
    (secondPalatalization k).setFeature .voice true = .ofChart .«dz» ∧
      (Segment.ofChart .«dz»).setFeature .continuant true = secondPalatalization g ∧
      secondPalatalization h = secondPalatalization g ∧
      Finset.univ.filter (fun ft ↦ k ft ≠ g ft) = {.voice} ∧
      Finset.univ.filter (fun ft ↦ secondPalatalization k ft ≠ secondPalatalization g ft) =
        {.continuant, .voice} := by
  decide +kernel

/-- No one feature change, merging the same values into each segment, takes both *k* and *g* to
their reflexes, since the two agree in [continuant] and their reflexes do not. -/
theorem not_exists_merge_eq :
    ¬ ∃ d : Segment, (fun f ↦ (d f).or (k f)) = secondPalatalization k ∧
      (fun f ↦ (d f).or (g f)) = secondPalatalization g := by
  rintro ⟨d, hk, hg⟩
  have h₁ := congrFun hk .continuant
  have h₂ := congrFun hg .continuant
  revert h₁ h₂
  cases d .continuant with
  | bot => decide +kernel
  | coe v => cases v <;> decide +kernel

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

/-- Every letter writes phonemes of the inventory, before *ě*, *i* and *í* as elsewhere. -/
theorem forall_mem_values : ∀ p ∈ letterValues ++ valuesBeforeĚ ++ valuesBeforeI,
    ∀ x ∈ p.2, x ∈ inventory := by
  decide +kernel

private theorem mem_inventory_of_lookup {l : List (Char × List Segment)}
    (hl : ∀ p ∈ l, p ∈ letterValues ++ valuesBeforeĚ ++ valuesBeforeI) {y : Char}
    {w : List Segment} (h : l.lookup y = some w) : ∀ x ∈ w, x ∈ inventory := by
  obtain ⟨l₁, l₂, rfl, -⟩ := List.lookup_eq_some_iff.1 h
  exact forall_mem_values _ (hl _ (List.mem_append_right _ List.mem_cons_self))

private theorem mem_inventory_of_mem_ofChar {y : Char} {w : List Segment}
    (h : ofChar y = some w) : ∀ x ∈ w, x ∈ inventory :=
  mem_inventory_of_lookup (fun _ hp ↦ by simp [hp]) h

private theorem mem_inventory_of_mem_ofCharBeforeĚ {y : Char} {w : List Segment}
    (h : ofCharBeforeĚ y = some w) : ∀ x ∈ w, x ∈ inventory := by
  rcases Option.or_eq_some_iff.1 h with h | ⟨-, h⟩
  · exact mem_inventory_of_lookup (fun _ hp ↦ by simp [hp]) h
  · exact mem_inventory_of_mem_ofChar h

private theorem mem_inventory_of_mem_ofCharBeforeI {y : Char} {w : List Segment}
    (h : ofCharBeforeI y = some w) : ∀ x ∈ w, x ∈ inventory := by
  rcases Option.or_eq_some_iff.1 h with h | ⟨-, h⟩
  · exact mem_inventory_of_lookup (fun _ hp ↦ by simp [hp]) h
  · exact mem_inventory_of_mem_ofChar h

/-- The letters write phonemes of the inventory. -/
theorem mem_inventory_of_mem_ofChars {w : List Char} {l : List Segment}
    (h : ofChars w = some l) : ∀ x ∈ l, x ∈ inventory := by
  fun_induction ofChars w generalizing l <;>
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Option.map_eq_map,
      Option.map_eq_some_iff] at h
  next _ ih =>
    obtain ⟨l, hl, rfl⟩ := h
    exact List.forall_mem_cons.2 ⟨by decide +kernel, ih hl⟩
  next _ _ ih =>
    obtain ⟨l₁, h₁, l, hl, rfl⟩ := h
    exact List.forall_mem_append.2
      ⟨mem_inventory_of_mem_ofCharBeforeĚ h₁, List.forall_mem_cons.2 ⟨by decide +kernel, ih hl⟩⟩
  next _ _ ih =>
    obtain ⟨l₁, h₁, l, hl, rfl⟩ := h
    exact List.forall_mem_append.2
      ⟨mem_inventory_of_mem_ofCharBeforeI h₁, List.forall_mem_cons.2 ⟨by decide +kernel, ih hl⟩⟩
  next _ _ ih =>
    obtain ⟨l₁, h₁, l, hl, rfl⟩ := h
    exact List.forall_mem_append.2 ⟨mem_inventory_of_mem_ofCharBeforeI h₁,
      List.forall_mem_cons.2 ⟨by decide +kernel, List.forall_mem_cons.2 ⟨by decide +kernel, ih hl⟩⟩⟩
  next _ _ _ _ _ _ ih =>
    obtain ⟨l₁, h₁, l, hl, rfl⟩ := h
    exact List.forall_mem_append.2 ⟨mem_inventory_of_mem_ofChar h₁, ih hl⟩
  next =>
    subst h
    simp

/-- The spelling writes phonemes of the inventory. -/
theorem mem_inventory_of_mem_ofString? {w : String} {l : List Segment}
    (h : ofString? w = some l) : ∀ x ∈ l, x ∈ inventory :=
  mem_inventory_of_mem_ofChars h

/-- Length is phonemic, as in Short's pairs *dal* 'he gave' and *dál* 'further', *dul* 'blew'
and *důl* 'mine', and *ryby* 'fish' and *rybí* 'fish-', where *y* and *i* write one vowel
(p. 456). -/
theorem ofString?_length :
    ofString? "dal" = some [d, a, l] ∧ ofString? "dál" = some [d, a, a, l] ∧
      ofString? "dul" = some [d, u, l] ∧ ofString? "důl" = some [d, u, u, l] ∧
      ofString? "ryby" = some [r, i, b, i] ∧ ofString? "rybí" = some [r, i, b, i, i] := by
  decide +kernel

/-- The diphthong of *soud* 'court' against the vowel of *sud* 'barrel' (p. 456). -/
theorem ofString?_diphthong :
    ofString? "sud" = some [s, u, d] ∧ ofString? "soud" = some [s, o, u, d] := by
  decide +kernel

/-- *b*, *p*, *v* and *f* before *ě* are followed by /j/, and *m* by /ň/, in Short's *pěna*
/pjena/ 'foam', *věno* /vjeno/ 'dowry', *harfě* /harfje/ 'harp' and *město* /mňesto/ 'town',
and in *oběd* 'lunch', whose /objet/ has the final devoicing that `ofString?` leaves out
(p. 459). -/
theorem ofString?_labial_ě :
    ofString? "pěna" = some [p, j, e, n, a] ∧ ofString? "věno" = some [v, j, e, n, o] ∧
      ofString? "harfě" = some [h, a, r, f, j, e] ∧ ofString? "město" = some [m, ň, e, s, t, o] ∧
      ofString? "oběd" = some [o, b, j, e, d] := by
  decide +kernel

/-- The alternation of *d* with *ď* before a front vowel, in Short's *mladý*, *mladí*, *mladě*
'young' (p. 462), and *ď* written with the háček before a back vowel, as in *ďábel* 'devil'
(p. 459). -/
theorem ofString?_d_ď :
    ofString? "mladý" = some [m, l, a, d, i, i] ∧ ofString? "mladí" = some [m, l, a, ď, i, i] ∧
      ofString? "mladě" = some [m, l, a, ď, e] ∧ ofString? "ďábel" = some [ď, a, a, b, e, l] := by
  decide +kernel

/-- The alternation of *t* with *ť*, in Short's *krutý*, *krutí*, *krutě* 'cruel' (p. 462), and
*ť* before a back vowel, as in *ťuhýk* 'shrike' (p. 459). -/
theorem ofString?_t_ť :
    ofString? "krutý" = some [k, r, u, t, i, i] ∧ ofString? "krutí" = some [k, r, u, ť, i, i] ∧
      ofString? "krutě" = some [k, r, u, ť, e] ∧ ofString? "ťuhýk" = some [ť, u, h, i, i, k] := by
  decide +kernel

/-- The alternation of *n* with *ň*, in Short's *plný*, *plně* 'full' (p. 462). -/
theorem ofString?_n_ň :
    ofString? "plný" = some [p, l, n, i, i] ∧ ofString? "plně" = some [p, l, ň, e] := by
  decide +kernel

end Czech.Phonology
