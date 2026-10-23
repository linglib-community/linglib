module

public import Linglib.Data.Examples.Embick2015
public import Linglib.Fragments.Korean.Phonology
public import Linglib.Morphology.DistributedMorphology.VocabularyInsertion.InsideOut

/-!
# Embick (2015): The Morpheme: A Theoretical Introduction

This file formalizes Embick's procedure of Vocabulary Insertion in a complex head: insertion
proceeds from the inside out (§4.5, the condition (C3) of §7.3), substitutes an exponent for the
Q variable of each functional morpheme (§4.2), leaves the morpheme's synsem features in place
(§4.2.2), and lets a contextual item see the concatenated neighbours of its morpheme, null
exponents pruned (§7.3.2). The procedure is the substrate's `ComplexHead.insertAll`, and this file
runs it on the book's own material. The fragment of the Latin conjugation (§4.6) derives the four
tenses of *laudāre* in (40) from the Vocabulary Items (36), (37) and (42): the perfect-specific
agreement endings are inserted only where the deleted T[−past] leaves Agr concatenated with
Asp[perf], the overt tense of the pluperfect intervening (§7.3.2.1), and the first singular *-m*
of the imperfect and pluperfect reads T[+past]. Under rewriting, where insertion deletes the
synsem features of the morpheme it realizes, both conditionings are lost, and Agr would have to
refer to the exponents *-rā* and *-bā*, and to each allomorph of Asp[perf], one by one; that is
the book's argument for non-deletion (§4.6.3). The Hungarian plural of (7) and (8) looks outward
at the possessive, and the Korean nominative of (10) and (11) looks inward at whether its host
ends in a consonant or a vowel. The predictions of (C3) in (43) are that outward conditioning
sees synsem features only, the possessive being bare when the plural is realized, while inward
conditioning may see the phonological features of a realized exponent.

## Implementation notes

* The book's rule (38) deletes T[−past] outright; here T[−past] receives a null exponent and is
  pruned from the concatenation statements, the alternative the book itself offers for
  transparent zero morphemes in §7.3.2, so that the four tenses share the one spine
  ROOT-v-(Asp)-T-Agr of (35).
* The theme vowel is the exponent of v, as in (36a), spelled out in the context of the root's
  conjugation feature [+I].
* (42) prints the number feature of the *-m* item as [−sg] where (39) has [−pl], and omits the
  third singular *-t* of (33a); both are restored.
* The Korean hosts are transcribed into the segments of `Fragments.Korean.Phonology`, so that the
  consonant-final or vowel-final shape an item refers to is read off the [consonantal] value of
  the final segment rather than listed per host.
* The examples are `Data.Examples.Embick2015`.

## References

* [embick-2015]
* [halle-marantz-1993]
* [bobaljik-2000]
* [carstairs-1987]
-/

@[expose] public section

namespace Embick2015

open DistributedMorphology Embick2015.Examples

/-! ### The Latin fragment -/

namespace Latin

/-- The root of *laudāre* with its conjugation feature [+I], and the features of v, Asp[perf],
T[±past] and Agr[±1, ±2, ±pl]. -/
inductive Feature
  | laud
  | conjI
  | v
  | asp
  | perf
  | tense
  | past
  | agr
  | first (b : Bool)
  | second (b : Bool)
  | pl (b : Bool)
  deriving DecidableEq, Repr

open Feature

/-- The Vocabulary Items (36), (37) and (42) are the theme vowel of v in conjugation I, Asp[perf]
*-vi*, T[+past] *-rā* after Asp[perf] and *-bā* otherwise, the null T[−past] of (38), and the
agreement endings, the perfect-specific set after Asp[perf], *-m* after T[+past], the defaults
elsewhere. -/
def vocab : List (VocabularyItem Feature String) :=
  [⟨{(0, v), (-1, conjI)}, "ā"⟩, {asp, perf} ⟷ "vi",
   ⟨{(0, tense), (0, past), (-1, asp), (-1, perf)}, "rā"⟩, {tense, past} ⟷ "bā", {tense} ⟷ "",
   ⟨{(0, agr), (0, first true), (0, second false), (0, pl false), (-1, asp), (-1, perf)}, "ī"⟩,
   ⟨{(0, agr), (0, first false), (0, second true), (0, pl false), (-1, asp), (-1, perf)}, "stī"⟩,
   ⟨{(0, agr), (0, first false), (0, second true), (0, pl true), (-1, asp), (-1, perf)}, "stis"⟩,
   ⟨{(0, agr), (0, first false), (0, second false), (0, pl true), (-1, asp), (-1, perf)}, "ērunt"⟩,
   ⟨{(0, agr), (0, first true), (0, second false), (0, pl false), (-1, tense), (-1, past)}, "m"⟩,
   {agr, first true, second false, pl false} ⟷ "ō",
   {agr, first true, second false, pl true} ⟷ "mus",
   {agr, first false, second true, pl false} ⟷ "s",
   {agr, first false, second true, pl true} ⟷ "tis",
   {agr, first false, second false, pl true} ⟷ "nt",
   {agr, first false, second false, pl false} ⟷ "t"]

/-- The four tenses of (40). -/
inductive Tense
  | present
  | imperfect
  | perfect
  | pluperfect
  deriving DecidableEq, Repr

/-- The Asp and T morphemes of a tense, with Asp[perf] in the perfects only (§4.6.1). -/
def Tense.heads : Tense → List (Morpheme Feature String)
  | .present => [⟨{tense}, none, .after⟩]
  | .imperfect => [⟨{tense, past}, none, .after⟩]
  | .perfect => [⟨{asp, perf}, none, .after⟩, ⟨{tense}, none, .after⟩]
  | .pluperfect => [⟨{asp, perf}, none, .after⟩, ⟨{tense, past}, none, .after⟩]

/-- ROOT-v-(Asp)-T-Agr, (35). -/
def word (t : Tense) (p₁ p₂ pl : Bool) :
    ComplexHead (Morpheme Feature String) (Morpheme Feature String) :=
  ⟨⟨{laud, conjI}, some "laud", .after⟩,
   ⟨{v}, none, .after⟩ :: t.heads ++
     [⟨{agr, first p₁, second p₂, Feature.pl pl}, none, .after⟩]⟩

/-- The surface morphs after inside-out insertion with the given discharge, the pruned T[−past]
dropped. -/
def morphs (dis : ComplexHead.Discharge)
    (w : ComplexHead (Morpheme Feature String) (Morpheme Feature String)) : List String :=
  (w.insertAll (· = "") vocab .concatenation (fun _ ↦ ∅) dis).exponents.filter (· ≠ "")

/-- The tenses as named in the rows. -/
def tenseTable : List (String × Tense) :=
  [("present", .present), ("imperfect", .imperfect), ("perfect", .perfect),
    ("pluperfect", .pluperfect)]

/-- The persons as named in the rows, as [±1, ±2]. -/
def personTable : List (String × (Bool × Bool)) :=
  [("1", (true, false)), ("2", (false, true)), ("3", (false, false))]

/-- The numbers as named in the rows, as [±pl]. -/
def numberTable : List (String × Bool) := [("sg", false), ("pl", true)]

/-- A row of (40) as its complex head and its morphs. -/
def ofRow (ex : Datum) :
    Option (ComplexHead (Morpheme Feature String) (Morpheme Feature String) × List String) := do
  let t ← ex.parse? "tense" tenseTable
  let (p₁, p₂) ← ex.parse? "person" personTable
  let pl ← ex.parse? "number" numberTable
  pure (word t p₁ p₂ pl, ["m1", "m2", "m3", "m4", "m5"].filterMap ex.feature?)

theorem ofRow_isSome : ∀ ex ∈ Examples.all, ex.language = "lati1261" → (ofRow ex).isSome := by
  decide

/-- The twenty-four forms of (40). -/
def rows : List (ComplexHead (Morpheme Feature String) (Morpheme Feature String) × List String) :=
  (Examples.all.filter (·.language = "lati1261")).filterMap ofRow

/-- With T[−past] pruned, the four tenses of (40) derive with Agr adjacent to Asp[perf] in the
perfect and to T[+past] in the pluperfect (§7.3.2.1). -/
theorem rows_morphs : ∀ r ∈ rows, morphs .nondeletion r.1 = r.2 := by decide +kernel

/-- If insertion deleted synsem features, the first singular of the imperfect and the perfect would
wrongly take the default *-ō* (§4.6.3). -/
theorem rewriting_loses_conditioning :
    morphs .rewriting (word .imperfect true false false) = ["laud", "ā", "bā", "ō"] ∧
      morphs .rewriting (word .perfect true false false) = ["laud", "ā", "vi", "ō"] := by
  decide

end Latin

/-! ### Outward conditioning: the Hungarian plural -/

namespace Hungarian

/-- The plural and possessive features. -/
inductive Feature
  | pl
  | poss
  deriving DecidableEq, Repr

open Feature

/-- In (8), with the concatenation of (28), the plural is *-((j)a)i-* before a possessive and
*-(V)k* otherwise; the first singular possessive is *-m*. -/
def vocab : List (VocabularyItem Feature String) :=
  [⟨{(0, pl), (1, poss)}, "ai"⟩, {pl} ⟷ "k", {poss} ⟷ "m"]

/-- Noun-[+pl], or Noun-[+pl]-[+poss] when possessed. -/
def word (r : String) (possessed : Bool) :
    ComplexHead (Morpheme Feature String) (Morpheme Feature String) :=
  ⟨⟨∅, some r, .after⟩,
   ⟨{pl}, none, .after⟩ :: if possessed then [⟨{poss}, none, .after⟩] else []⟩

/-- The exponent of the plural after inside-out insertion. -/
def plural (w : ComplexHead (Morpheme Feature String) (Morpheme Feature String)) : Option String :=
  (w.insertAll (· = "") vocab .concatenation (fun _ ↦ ∅) .nondeletion).heads[0]? >>= (·.exp)

/-- Possession as named in the rows. -/
def possTable : List (String × Bool) := [("yes", true), ("no", false)]

/-- A row of (7) as its complex head and the exponent of its plural. -/
def ofRow (ex : Datum) :
    Option (ComplexHead (Morpheme Feature String) (Morpheme Feature String) × String) := do
  pure (word (← ex.feature? "root") (← ex.parse? "poss" possTable), ← ex.feature? "plExponent")

theorem ofRow_isSome : ∀ ex ∈ Examples.all, ex.language = "hung1274" → (ofRow ex).isSome := by
  decide

/-- The plural and possessed plural of the three nouns of (7). -/
def rows : List (ComplexHead (Morpheme Feature String) (Morpheme Feature String) × String) :=
  (Examples.all.filter (·.language = "hung1274")).filterMap ofRow

/-- The rows of (7) show outward conditioning by the possessive's feature. -/
theorem rows_plural : ∀ r ∈ rows, plural r.1 = some r.2 := by decide

/-- When the plural is reached it sees outward only the features of the still-bare possessive (43a,
b). -/
theorem outward_features_only :
    ∀ r ∈ rows, (r.1.contextAt (· = "") .concatenation (fun _ ↦ ∅) 0).rightCtx =
      (r.1.heads.drop 1).map (·.feats) := by
  decide

end Hungarian

/-! ### Inward phonological conditioning: the Korean nominative -/

namespace Korean

/-- The nominative, and the shape of its host. -/
inductive Feature
  | nom
  | cFinal
  | vFinal
  deriving DecidableEq, Repr

open Feature

/-- In (11) the nominative is *-i* after a consonant and *-ka* after a vowel. -/
def vocab : List (VocabularyItem Feature String) :=
  [⟨{(0, nom), (-1, cFinal)}, "i"⟩, ⟨{(0, nom), (-1, vFinal)}, "ka"⟩]

/-- The hosts of (10), transcribed into the segments of the fragment. -/
def segments : List (String × List Phonology.Segment) :=
  [("pap", [Korean.p, Korean.a, Korean.p]), ("ai", [Korean.a, Korean.i])]

/-- The phonological feature a realized exponent presents to insertion is whether its final
segment is a consonant. -/
def shape (e : String) : Finset Feature :=
  match (segments.lookup e).bind List.getLast? with
  | some s => if s.IsConsonant then {cFinal} else {vFinal}
  | none => ∅

/-- Noun-[nom]. -/
def word (r : String) : ComplexHead (Morpheme Feature String) (Morpheme Feature String) :=
  ⟨⟨∅, some r, .after⟩, [⟨{nom}, none, .after⟩]⟩

/-- The exponent of the nominative after inside-out insertion. -/
def nominative (w : ComplexHead (Morpheme Feature String) (Morpheme Feature String)) :
    Option String :=
  (w.insertAll (· = "") vocab .concatenation shape .nondeletion).heads[0]? >>= (·.exp)

/-- A row of (10) as its complex head and the exponent of its nominative. -/
def ofRow (ex : Datum) :
    Option (ComplexHead (Morpheme Feature String) (Morpheme Feature String) × String) := do
  pure (word (← ex.feature? "root"), ← ex.feature? "nomExponent")

theorem ofRow_isSome : ∀ ex ∈ Examples.all, ex.language = "kore1280" → (ofRow ex).isSome := by
  decide

/-- The two hosts of (10). -/
def rows : List (ComplexHead (Morpheme Feature String) (Morpheme Feature String) × String) :=
  (Examples.all.filter (·.language = "kore1280")).filterMap ofRow

/-- The rows of (10) show the inward conditioning of (43d), by the host's phonology as visible
through its realized exponent. -/
theorem rows_nominative : ∀ r ∈ rows, nominative r.1 = some r.2 := by decide

end Korean

end Embick2015
