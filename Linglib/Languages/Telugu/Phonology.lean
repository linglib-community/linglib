module

public import Linglib.Data.PHOIBLE.Inventories.Telugu
public import Linglib.Phonology.Prosody.Syllable
public import Linglib.Phonology.Segmental.PHOIBLE
public import Linglib.Phonology.Segmental.Sonority.Basic

/-!
# Telugu phonemes

Standard Telugu has thirty-three consonants and eleven vowels. The stops and the affricates come
in five places, each voiceless and voiced, plain and aspirated; the aspirates, /f/ and the
sibilants other than /s/ came in with borrowed vocabulary, and speech without them has seventeen
consonants. The vowels are five pairs of a short and a long vowel and a long low front vowel. The
feature values of a phoneme are not listed: each phoneme names its glyph in the PHOIBLE chart,
and its segment is the segment of that chart entry. A form in the romanization of the other
Telugu language files is [transcribed](##transcribe) letter by letter, and its
[first syllable](##initialSyllable) is light when it ends in a short vowel.

## Implementation notes

* The inventory is PHOIBLE's of standard Telugu, whose phonemes are those of Krishnamurti and
  Gwynn's chart of the standard language one for one. It writes the palatal series as stops;
  the grammar writes them *c* and *j*, and Aitha describes them as postalveolar affricates.
* A segment carries no length, so a long vowel is transcribed as two of its vowel, the string
  `Prosody.Syllable.ofLongVowel` yields.
* The romanization is the one Aitha's examples use, with a macron for a long vowel and a dot
  under a retroflex. Krishnamurti and Gwynn double the letter of a long vowel and write the
  retroflexes with capitals.

## References

* [krishnamurti-gwynn-1985]
* [moran-mccloy-2019]
* [aitha-2026]
-/

@[expose] public section

open Phonology Data.PHOIBLE

namespace Telugu.Phonology

/-! ### Phonemes -/

/-- The voiceless bilabial stop /p/. -/
def p : Segment := .ofChart .«p»

/-- The aspirated voiceless bilabial stop. -/
def ph : Segment := .ofChart .«pʰ»

/-- The voiced bilabial stop /b/. -/
def b : Segment := .ofChart .«b»

/-- The breathy voiced bilabial stop. -/
def bh : Segment := .ofChart .«b̤»

/-- The voiceless dental stop. -/
def t : Segment := .ofChart .«t̪»

/-- The aspirated voiceless dental stop. -/
def th : Segment := .ofChart .«t̪ʰ»

/-- The voiced dental stop. -/
def d : Segment := .ofChart .«d̪»

/-- The breathy voiced dental stop. -/
def dh : Segment := .ofChart .«d̪̤»

/-- The voiceless retroflex stop. -/
def «ṭ» : Segment := .ofChart .«ʈ»

/-- The aspirated voiceless retroflex stop. -/
def «ṭh» : Segment := .ofChart .«ʈʰ»

/-- The voiced retroflex stop. -/
def «ḍ» : Segment := .ofChart .«ɖ»

/-- The breathy voiced retroflex stop. -/
def «ḍh» : Segment := .ofChart .«ɖ̤»

/-- The voiceless palatal stop, an affricate in pronunciation. -/
def c : Segment := .ofChart .«c»

/-- The aspirated voiceless palatal stop. -/
def ch : Segment := .ofChart .«cʰ»

/-- The voiced palatal stop, an affricate in pronunciation. -/
def j : Segment := .ofChart .«ɟ»

/-- The breathy voiced palatal stop. -/
def jh : Segment := .ofChart .«ɟ̤»

/-- The voiceless velar stop /k/. -/
def k : Segment := .ofChart .«k»

/-- The aspirated voiceless velar stop. -/
def kh : Segment := .ofChart .«kʰ»

/-- The voiced velar stop /ɡ/. -/
def g : Segment := .ofChart .«ɡ»

/-- The breathy voiced velar stop. -/
def gh : Segment := .ofChart .«ɡ̤»

/-- The labiodental fricative /f/. -/
def f : Segment := .ofChart .«f»

/-- The dental sibilant. -/
def s : Segment := .ofChart .«s̪»

/-- The retroflex sibilant. -/
def «ṣ» : Segment := .ofChart .«ʂ»

/-- The palatal sibilant. -/
def «ś» : Segment := .ofChart .«ʃ»

/-- The glottal fricative /h/. -/
def h : Segment := .ofChart .«h»

/-- The bilabial nasal /m/. -/
def m : Segment := .ofChart .«m»

/-- The dental nasal. -/
def n : Segment := .ofChart .«n̪»

/-- The retroflex nasal. -/
def «ṇ» : Segment := .ofChart .«ɳ»

/-- The dental lateral. -/
def l : Segment := .ofChart .«l̪»

/-- The retroflex lateral. -/
def «ḷ» : Segment := .ofChart .«ɭ»

/-- The trill or tap. -/
def r : Segment := .ofChart .«r̪»

/-- The labial glide, transcribed *w* or *v*. -/
def v : Segment := .ofChart .«w»

/-- The palatal glide. -/
def y : Segment := .ofChart .«j»

/-- The low vowel /a/. -/
def a : Segment := .ofChart .«a»

/-- The high front vowel /i/. -/
def i : Segment := .ofChart .«i»

/-- The high back vowel /u/. -/
def u : Segment := .ofChart .«u»

/-- The mid front vowel /e/. -/
def e : Segment := .ofChart .«e»

/-- The mid back vowel /o/. -/
def o : Segment := .ofChart .«o»

/-- The low front vowel, which is always long. -/
def «ǣ» : Segment := .ofChart .«æː»

/-- The Telugu phonemes by their letters in the romanization, the long vowels aside. -/
def phonemes : List (String × Segment) :=
  [("p", p), ("ph", ph), ("b", b), ("bh", bh), ("t", t), ("th", th), ("d", d), ("dh", dh),
    ("ṭ", «ṭ»), ("ṭh", «ṭh»), ("ḍ", «ḍ»), ("ḍh", «ḍh»), ("c", c), ("ch", ch), ("j", j),
    ("jh", jh), ("k", k), ("kh", kh), ("g", g), ("gh", gh), ("f", f), ("s", s), ("ṣ", «ṣ»),
    ("ś", «ś»), ("h", h), ("m", m), ("n", n), ("ṇ", «ṇ»), ("l", l), ("ḷ", «ḷ»), ("r", r),
    ("v", v), ("y", y), ("a", a), ("i", i), ("u", u), ("e", e), ("o", o)]

/-- The segments of the Telugu phonemes, pairwise distinct. -/
def inventory : Finset Segment :=
  ⟨↑(phonemes.map Prod.snd ++ [«ǣ»]), by decide⟩

/-- The phonemes are segments of PHOIBLE's inventory of standard Telugu. -/
theorem subset_tel : inventory ⊆ Inventories.Telugu.tel.segments :=
  Inventory.subset_segments_iff.2 (by decide)

theorem isVowel_iff :
    ∀ x ∈ inventory, x.IsVowel ↔ x ∈ ({a, i, u, e, o, «ǣ»} : Finset Segment) := by
  decide

/-! ### Romanization -/

/-- The long vowels by their letters, each as two of its vowel. -/
def longVowels : List (String × List Segment) :=
  [("ā", [a, a]), ("ī", [i, i]), ("ū", [u, u]), ("ē", [e, e]), ("ō", [o, o]),
    ("ǣ", [«ǣ», «ǣ»])]

/-- The segments a letter or digraph of the romanization transcribes. -/
def ofLetter? (c : String) : Option (List Segment) :=
  ((phonemes.lookup c).map ([·])).orElse fun _ ↦ longVowels.lookup c

/-- The segments of a romanized form, when every letter is Telugu: a stop letter with a following
*h* is its aspirate. -/
def transcribe : List Char → Option (List Segment)
  | [] => some []
  | [c] => ofLetter? (String.ofList [c])
  | c₁ :: c₂ :: cs =>
    match ofLetter? (String.ofList [c₁, c₂]) with
    | some s => (transcribe cs).map (s ++ ·)
    | none => (ofLetter? (String.ofList [c₁])).bind fun s ↦ (transcribe (c₂ :: cs)).map (s ++ ·)

/-! ### The first syllable -/

/-- The first syllable of a form. Its nucleus is the first vowel, with a second mora when the
vowel is long. A consonant after the vowel closes the syllable, with a mora of its own, unless it
begins the next syllable, alone before a vowel or with a following consonant of higher sonority,
as the *dr* of *samudram* 'ocean'. -/
def initialSyllable (w : List Segment) : Prosody.Syllable :=
  let (onset, nucleus, rest) := Prosody.nucleusSplit w
  let coda : List Segment :=
    match rest with
    | [] => []
    | [c] => [c]
    | c₁ :: c₂ :: rest =>
      if c₂.IsSyllabic ∨ Sonority.ofSegment c₁ < Sonority.ofSegment c₂ ∧
          (rest.head?.any (·.IsSyllabic)) then [] else [c₁]
  ⟨onset, nucleus.take 1, (nucleus.drop 1).map ([·]) ++ if coda = [] then [] else [coda]⟩

end Telugu.Phonology
