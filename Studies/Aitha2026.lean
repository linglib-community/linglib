module

public import Linglib.Core.Order.OrdConnected
public import Linglib.Data.Examples.Aitha2026
public import Linglib.Data.Examples.Gloss
public import Linglib.Data.Examples.Readers
public import Linglib.Fragments.Telugu.Adpositions
public import Linglib.Fragments.Telugu.Case
public import Linglib.Fragments.Telugu.Phonology
public import Linglib.Morphology.DistributedMorphology.VocabularyInsertion.Basic
public import Linglib.Morphology.DistributedMorphology.VocabularyInsertion.InsideOut
public import Linglib.Morphology.Word.Leipzig
public import Linglib.Phonology.OptimalityTheory.Grammar
public import Linglib.Phonology.OptimalityTheory.Stratal
public import Linglib.Phonology.OptimalityTheory.Filtration
public import Linglib.Phonology.OptimalityTheory.Candidate
public import Linglib.Phonology.Prosody.Foot
public import Mathlib.Tactic.DeriveFintype
public import Studies.Caha2009

/-!
# The nouns that say -ni

Telugu nouns show two stem alternations. In the strong one (*il-lu* ~ *in-ṭi* 'house') the
exponent of the nominalizer n is chosen by Vocabulary Insertion in the context of [ACC], the head
that every nonnominative case contains under Caha's containment, as McFadden proposes; a
vocabulary that reads case heads can only
[cut a paradigm into contiguous stretches](##isContiguous_strongN). The weak one
(*samudr-am* ~ *samudr-āni* 'ocean') has the nominative form again in the genitive, so
[no such vocabulary derives it](##weakN_ne_subsetPrinciple), and it reads the weight of
the next syllable inside the prosodic word. Nor can an exponent of n be chosen by that syllable:
insertion runs from the root outward, and
[n is realized before anything outside it has an exponent](##light_notMem_contextAt). The
alternation is the phonology of one underlying *-am-ni*,
derived in Kiparsky's Stratal OT from prespecified stress on the singular suffix *-ni*. The
two strata rank the constraints differently: the consonant that deletes inside the word is kept
before a postposition, and
[no ranking makes the winners of both strata's tableaux optimal](##wordGrammar_inf_phraseGrammar).

## Implementation notes

The cells of a paradigm are the cases of `Telugu.Case` and a postposition. A case has its place
in the Case sequence of `Studies/Caha2009.lean` and the postposition is above them all; the heads
a cell's representation contains are the cells at or below it, the nominative having none.

The paper's Vocabulary Items for the strong nouns list the roots each exponent follows. A list is
one feature here, borne by the roots on it, so each exponent has one item, and the items cover
every row of the paper's table of strong nouns, which gives entries for two of its rows.

The Word- and Phrase-level rankings are the paper's Hasse diagrams, given by their edges, and a
tableau is evaluated under every total ranking that extends its stratum's diagram. The
Word-level diagram has ONSET, which the paper ranks below IDENT-STRESS, below *DIST-0 as well:
the winner of the quantifier tableau is optimal under a ranking only if *DIST-0 dominates ONSET
(`onset_dominated`). A stratum is also a grammar in the sense of `OptimalityTheory.Grammar`, the
rankings under which the winners of its tableaux are optimal, and the diagram's grammar lies
below it.

Each tableau is proved to have a comparative tableau, a row for each losing candidate with the
constraints that prefer the winner and those that prefer the loser, and what is said of the
rankings is read off those rows.

A candidate is written as the paper prints it and read against the segments of its input, which
gives the positions it deletes and the vowels it lengthens, and every mark is computed from that
by the paper's definitions of the constraints; the Phrase-level input of the quantified form is
the Word-level winner. A candidate therefore also bears the marks of constraints its tableau has
no column for. In the printed
columns the computed marks are the printed cells, except that MAX counts one segment for the two
dative candidates that delete /n/, ALIGN-RIGHT marks the nominative candidate ending in *mn* and
no candidate of the postpositional tableau, IDENT-STRESS does not mark the last candidate of the
Phrase-level quantifier tableau, FT-BIN marks each non-bimoraic foot and ALL-FT-LEFT each
syllable between a foot and the left edge.

Syllable weight is that of `Telugu.Phonology.initialSyllable` on the transcribed form of the
morpheme after the noun stem.

## TODO

* The strong items read [ACC] on the bundle of n, which stands for the case heads outside it;
  they are not run through `DistributedMorphology.ComplexHead.insertAll`, and the paper's
  contrast between the strong alternation, which reaches across a postposed quantifier, and the
  weak one, which needs adjacency, is not stated on the engine's two localities.
* The Stem-level tableaux for the sandhi of *pandem* 'bet' and *peḷḷām* 'wife' and the Stem-level
  Hasse diagram are not formalized.

## References

* [aitha-2026]
* [caha-2009]
* [mcfadden-2018]
* [kiparsky-2000]
* [bobaljik-2000]
-/

@[expose] public section

namespace Aitha2026

open DistributedMorphology Morphology Phonology Prosody OptimalityTheory
open Examples (Alternation Alternant Follower)

/-! ### Case containment -/

/-- A cell of a paradigm is a case or a postposition. -/
inductive Cell where
  /-- A case of `Telugu.Case`. -/
  | case (c : Telugu.Case)
  /-- A postposition, *lō* 'in' in the paper's paradigms. -/
  | postposition
  deriving DecidableEq, Fintype, Repr

/-- The place of a cell on the hierarchy (3): a case has its place in Caha's Case sequence, and
the postposition is above every case. -/
def Cell.place : Cell → WithTop (Fin 6)
  | .case c => (((List.finRange 6).find? (Caha2009.sequence · = c.label)).map WithTop.some).getD ⊤
  | .postposition => ⊤

theorem sequence_place : ∀ c : Telugu.Case, ∃ i : Fin 6,
    Cell.place (.case c) = WithTop.some i ∧ Caha2009.sequence i = c.label := by
  decide

/-- The cells are ordered by containment, a cell containing the cells before it. -/
instance : Preorder Cell := Preorder.lift Cell.place

instance : DecidableLE Cell := fun a b ↦ inferInstanceAs (Decidable (a.place ≤ b.place))

instance : DecidableLT Cell := fun a b ↦ inferInstanceAs (Decidable (a.place < b.place))

/-- The heads the representation of a cell contains: those of the cells it contains, the
nominative having no head of its own. -/
def Cell.heads (c : Cell) : Finset Cell := {h | .case .nom < h ∧ h ≤ c}

theorem Cell.heads_mono : Monotone Cell.heads := fun _ _ h ↦
  Finset.monotone_filter_right _ fun _ _ hx ↦ ⟨hx.1, hx.2.trans h⟩

/-! ### The strong alternation -/

/-- The exponents of n in the strong nouns of (2). -/
inductive Exponent where
  | u | lu | nu | «ḍu» | ru | li | yi | «ṭi» | ti | i
  deriving DecidableEq, Fintype, Repr

/-- The exponent as the paper transcribes it. -/
def Exponent.form : Exponent → String
  | .u => "u" | .lu => "lu" | .nu => "nu" | .«ḍu» => "ḍu" | .ru => "ru" | .li => "li"
  | .yi => "yi" | .«ṭi» => "ṭi" | .ti => "ti" | .i => "i"

/-- The nominative exponent of a row of (2). -/
def nominative : Alternation → Exponent
  | .u => .u | .lu => .lu | .nu => .nu | .du => .«ḍu» | .ru => .ru | .li => .li | .yi => .yi

/-- The oblique exponent of a row of (2). -/
def oblique : Alternation → Exponent
  | .u => .i
  | .yi => .ti
  | _ => .«ṭi»

/-- The features at the n head: the root is on the list of roots an exponent follows, and the
case heads above the noun. -/
inductive Feature where
  | listed (e : Exponent)
  | head (h : Cell)
  deriving DecidableEq, Repr

/-- (4): a nominative exponent is inserted after the roots on its list, and an oblique exponent
after the roots on its list in the context of [ACC]. -/
def strongItems : RuleSet (VocabularyItem Feature Exponent) :=
  [.ru, .lu, .nu, .«ḍu», .li, .yi, .u].map (fun e ↦ {.listed e} ⟷ e) ++
    [.«ṭi», .ti, .i].map fun e ↦ {.listed e, .head (.case .acc)} ⟷ e

/-- The n head of a noun of the row `k` in the cell `c`: the root is on the lists of the row's
two exponents, under the case heads of the cell. -/
def site (k : Alternation) (c : Cell) : Finset Feature :=
  {.listed (nominative k), .listed (oblique k)} ∪ c.heads.image .head

/-- The exponent of n for a noun of the row `k` in the cell `c`. -/
def strongN (k : Alternation) (c : Cell) : Option Exponent := subsetPrinciple strongItems (site k c)

theorem antihomophonous_strongItems : RuleSet.Antihomophonous strongItems := by decide

theorem monotone_site (k : Alternation) :
    Monotone fun c ↦ (site k c : Neighborhood (Finset Feature)) := fun _ _ h ↦
  Neighborhood.ofBundle_subset_iff.2 <|
    Finset.union_subset_union_right (Finset.image_subset_image (Cell.heads_mono h))

/-- The strong paradigm of every row of (2) is contiguous on the containment hierarchy: an
exponent inserted in two cells is inserted in every cell between them. -/
theorem isContiguous_strongN (k : Alternation) : IsContiguous (strongN k) :=
  (isContiguous_subsetPrinciple antihomophonous_strongItems).comp_monotone (monotone_site k)

-- (1), (2): the nominative exponent in the nominative, the oblique one wherever [ACC] is
theorem strongN_eq :
    ∀ k c, strongN k c = some (if .case .acc ≤ c then oblique k else nominative k) := by
  decide

/-! ### The weak alternation -/

/-- The weight of the first syllable of a romanized form. -/
def weight? (s : List Char) : Option Syllable.Weight :=
  (Telugu.Phonology.transcribe s).map fun w ↦ (Telugu.Phonology.initialSyllable w).weight

/-- What follows the n exponent: the kind of the morpheme and the weight of its first
syllable. -/
structure Following where
  kind : Follower
  weight : Syllable.Weight
  deriving DecidableEq, Repr

/-- (29): a postposition is outside the noun's prosodic word, and the case suffixes, the
agreement suffixes, the plural suffix and a postposed quantifier are inside it. -/
def Following.Inside (f : Following) : Prop := f.kind ≠ .postposition

instance : DecidablePred Following.Inside := fun f ↦ inferInstanceAs (Decidable (f.kind ≠ _))

/-- The long form is triggered by a light syllable that follows inside the prosodic word. -/
def Long (f : Option Following) : Prop := ∃ x ∈ f, x.Inside ∧ x.weight = .light

instance : DecidablePred Long := fun f ↦ inferInstanceAs (Decidable (∃ x ∈ f, _))

/-- What follows n in a cell of the paradigm: the first exponent of the case, if it has one, or
the postposition *lō*. -/
def Cell.following : Cell → Option Following
  | .case c => c.exponents.head?.bind fun m ↦ (weight? m.form.toList).map (⟨.case, ·⟩)
  | .postposition =>
    Telugu.Adpositions.lō.morphs.head?.bind fun m ↦
      (weight? m.form.toList).map (⟨.postposition, ·⟩)

/-- The form of a singular weak noun in a cell: long before a light syllable inside the prosodic
word, and short otherwise. -/
def weakN (c : Cell) : Alternant := if Long c.following then .long else .short

-- (8): the weak paradigm is ABA, the nominative form resurfacing in the genitive
theorem not_isContiguous_weakN : ¬ IsContiguous weakN :=
  fun h ↦ absurd (h (i := .case .nom) (j := .case .acc) (k := .case .gen) (by decide) (by decide)
    (by decide)) (by decide)

/-- No Vocabulary Items conditioned by case derive the weak paradigm: whatever the features and
the items, if no two items share an exponent and a cell presents the features of the cells it
contains, the Subset Principle does not insert the long and short forms where the weak nouns have
them. -/
theorem weakN_ne_subsetPrinciple {F E : Type*} [DecidableEq F]
    {items : RuleSet (VocabularyItem F E)} (hv : items.Antihomophonous)
    {site : Cell → Neighborhood (Finset F)} (hs : Monotone site) {exp : Alternant → E}
    (hexp : Function.Injective exp) :
    (fun c ↦ subsetPrinciple items (site c)) ≠ fun c ↦ some (exp (weakN c)) := fun h ↦ by
  have hc : IsContiguous fun c ↦ subsetPrinciple items (site c) :=
    (isContiguous_subsetPrinciple hv).comp_monotone hs
  rw [h] at hc
  exact not_isContiguous_weakN <| (isContiguous_comp_iff (h := fun a ↦ some (exp a))
    ((Option.some_injective E).comp hexp)).1 hc

/-! ### The rows -/

/-- The word of a row that bears the noun: the word glossed with n or with a postposed
quantifier. -/
def noun? (e : Datum) : Option GlossedWord :=
  e.glossedWords.find? fun w ↦
    "n".toList ∈ w.glosses ∨
      ∃ g ∈ w.glosses.flatMap Gloss.elements, g ∈ ["all".toList, "whole".toList]

/-- The exponent of n in a row: the morph glossed n. -/
def nMorph? (e : Datum) : Option (List Char) :=
  (noun? e).bind fun w ↦ (w.glossedMorphemes.find? (·.gloss = "n".toList)).map (·.morpheme)

/-- The case of the noun of a row: the case its last morpheme is glossed with, and the nominative
for a predicate noun glossed with the person of its subject. -/
def case? (e : Datum) : Option Telugu.Case :=
  (noun? e).bind fun w ↦
    let fs := Features.ofLabels
      (((w.glosses.getLast?.map Gloss.elements).getD []).filter (decide <| Gloss.IsLabel ·))
    ([Telugu.Case.nom, .acc, .gen, .dat].find? fun c ↦ fs .case = Flat.some c.label).orElse
      fun _ ↦ if (w.features .person).isSome then some .nom else none

/-- The cell of a row: a postposition, or the case of its noun. -/
def cell? (e : Datum) : Option Cell :=
  if Examples.follower e = some .postposition then some .postposition else (case? e).map .case

/-- What follows the noun stem in a row: the morph after n, or after the stem where n is not
segmented, with the kind the row records. -/
def following? (e : Datum) : Option Following := do
  let w ← noun? e
  let k ← Examples.follower e
  let i := (w.glosses.idxOf? "n".toList).getD 0
  let m ← w.morphs[i + 1]?
  let x ← weight? m
  pure ⟨k, x⟩

-- (1), (2), fn. 6
theorem strong_rows :
    ∀ e ∈ Examples.all, ∀ k ∈ Examples.alternation e,
      ∃ c ∈ cell? e, ∃ x ∈ strongN k c, nMorph? e = some x.form.toList := by
  decide

/-- Every singular weak noun of the paper has its long form exactly before a light syllable
inside the prosodic word, with case suffixes, agreement suffixes, postpositions and a postposed
quantifier alike. -/
theorem weak_rows :
    ∀ e ∈ Examples.all, ∀ a ∈ Examples.alternant e, (a = .long ↔ Long (following? e)) := by
  decide

-- (8): the paradigm of the cells is the attested one
theorem weakN_rows :
    ∀ e ∈ [Examples.ocean_nom, Examples.ocean_acc, Examples.ocean_gen, Examples.ocean_dat,
        Examples.ocean_p],
      ∃ c ∈ cell? e, Examples.alternant e = some (weakN c) := by
  decide

-- (8), (13): the nominative has both forms
theorem weak_not_function_of_case :
    ¬ ∃ f : Telugu.Case → Alternant,
      ∀ e ∈ Examples.all, ∀ c ∈ case? e, ∀ a ∈ Examples.alternant e, f c = a := by
  rintro ⟨f, h⟩
  have h₁ := h Examples.ocean_nom (by decide) .nom (by decide) .short (by decide)
  have h₂ := h Examples.ocean_1sg (by decide) .nom (by decide) .long (by decide)
  exact absurd (h₁.symm.trans h₂) (by decide)

-- (33), (35), (36): the oblique stem across a postposed quantifier goes by the overall case
theorem oblique_across_quantifier :
    ∀ e ∈ Examples.all, Examples.nounClass e = some .strong →
      Examples.follower e = some .quantifier →
        ∃ w ∈ noun? e, ∃ c ∈ case? e,
          (e.judgment = .acceptable ↔
            ("OBL".toList ∈ w.labels ↔ Cell.case .acc ≤ .case c)) := by
  decide

/-! ### Stem-level phonology -/

/-- (49): the metrical parses of *samudr-am* leave the final heavy syllable unparsed, form three
degenerate feet, or form two bimoraic trochees. -/
inductive StemCandidate where
  | unparsedFinal
  | degenerate
  | trochees
  deriving DecidableEq, Repr, Fintype

/-- The feet of a parse. -/
def StemCandidate.toFooting : StemCandidate → Footing Syllable.Weight
  | .unparsedFinal => [.inl ⟨[.light, .light], 0⟩, .inr .heavy]
  | .degenerate => [.inl ⟨[.light], 0⟩, .inl ⟨[.light], 0⟩, .inl ⟨[.heavy], 0⟩]
  | .trochees => [.inl ⟨[.light, .light], 0⟩, .inl ⟨[.heavy], 0⟩]

/-- (46)–(48): FT-BIN(μ) ≫ PARSE-SYL ≫ ALL-FT-LEFT, each read off a parse's footing as its
non-bimoraic feet, its stray syllables, and the feet's distances from the left edge. -/
def stemRanking : List (Constraint StemCandidate) :=
  [fun c ↦ (c.toFooting.nonBimoraicFeet id).length, fun c ↦ c.toFooting.strays.length,
    fun c ↦ c.toFooting.footOffsets.sum]

-- (49)
theorem stem_optimal : Constraint.eval Finset.univ stemRanking = {.trochees} := by decide

/-! ### The rankings of the Word and the Phrase -/

/-- The constraints of (64) and (68). -/
inductive Con where
  | distZero | alignR | identStress | ftBin | complexCoda | maxMora | max | identLength | onset
  deriving DecidableEq, Repr, Fintype

/-- (64): the edges of the Word-level diagram. *DIST-0, ALIGN-RIGHT, IDENT-STRESS, FT-BIN and
*COMPLEX-CODA are above MAX(μ), which is above MAX and IDENT-length, and IDENT-STRESS and *DIST-0
are above ONSET. -/
def word (a b : Con) : Prop :=
  match b with
  | .maxMora => a ∈ [Con.distZero, .alignR, .identStress, .ftBin, .complexCoda]
  | .max | .identLength => a = .maxMora
  | .onset => a ∈ [Con.distZero, .identStress]
  | _ => False

/-- (68): the edges of the Phrase-level diagram. FT-BIN, ONSET, IDENT-length and MAX are above
IDENT-STRESS, which is above *DIST-0, which is above ALIGN-RIGHT and MAX(μ). -/
def phrase (a b : Con) : Prop :=
  match b with
  | .identStress => a ∈ [Con.ftBin, .onset, .identLength, .max]
  | .distZero => a = .identStress
  | .alignR | .maxMora => a = .distZero
  | _ => False

instance : DecidableRel word := fun a b ↦ by unfold word; cases b <;> exact inferInstance

instance : DecidableRel phrase := fun a b ↦ by unfold phrase; cases b <;> exact inferInstance

/-- The order a diagram generates: `a` is above `b` when edges lead from `a` down to `b`. -/
abbrev Above (R : Con → Con → Prop) [DecidableRel R] (a b : Con) : Prop := b ∈ below R a

example : (Ranking.Enumeration.ofList
    [Con.distZero, .alignR, .identStress, .ftBin, .complexCoda, .maxMora,
    .max, .identLength, .onset]).IsLinearExtension word := by decide

example : (Ranking.Enumeration.ofList
    [Con.ftBin, .onset, .identLength, .max, .identStress, .distZero,
    .alignR, .maxMora, .complexCoda]).IsLinearExtension phrase := by decide

variable {σ : Ranking Con}

/-! ### Candidates

A candidate is written as the paper prints it, with feet in parentheses, syllables separated by
periods and stress marks, and is read against the segments of its input: each of its segments has
the position of the input segment it continues, a long vowel taking one position twice. Its marks
are computed from that. -/

/-- A syllable of a candidate: its segments with their positions in the input, and whether it
is printed with a stress mark. -/
structure Syl where
  segs : List (Segment × ℕ)
  stressed : Bool
  deriving DecidableEq

/-- A parse: feet, each a list of syllables, and syllables outside the feet. -/
abbrev Printed := List (List Syl ⊕ Syl)

/-- The stress marks. -/
def stressMarks : List Char := ['ˈ', 'ˌ']

/-- The feet and stray syllables of a printed form, as strings. -/
def split : List Char → List Char → Option (List (List Char)) →
    List (List (List Char) ⊕ List Char)
  | [], cur, _ => if cur = [] then [] else [.inr cur.reverse]
  | '(' :: cs, _, _ => split cs [] (some [])
  | ')' :: cs, cur, some f => .inl (cur.reverse :: f).reverse :: split cs [] none
  | c :: cs, cur, foot =>
    if c = '.' ∨ c = ' ' then
      match foot with
      | some f => split cs [] (some (if cur = [] then f else cur.reverse :: f))
      | none => if cur = [] then split cs [] none else .inr cur.reverse :: split cs [] none
    else split cs (c :: cur) foot

/-- The segments of a romanized form. -/
def segments (s : List Char) : List Segment := (Telugu.Phonology.transcribe s).getD []

/-- Each segment of a candidate with the position of the next input segment like it; the second
half of a long vowel shares the position of the first. -/
def assign (input : List Segment) : ℕ → Option (Segment × ℕ) → List Segment → List (Segment × ℕ)
  | _, _, [] => []
  | i, prev, x :: xs =>
    if ∃ p ∈ prev, p.1 = x ∧ x.IsSyllabic ∧ input[i]? ≠ some x then
      ((prev.map (·.2)).getD 0 |> (x, ·)) :: assign input i none xs
    else
      let k := i + (input.drop i).idxOf x
      (x, k) :: assign input (k + 1) (some (x, k)) xs

/-- A list cut into consecutive stretches of the given lengths. -/
def chunk {α : Type*} : List α → List ℕ → List (List α)
  | _, [] => []
  | l, n :: ns => l.take n :: chunk (l.drop n) ns

/-- The syllables `l` grouped as the printed feet and strays `raw`. -/
def regroup : List (List (List Char) ⊕ List Char) → List Syl → Printed
  | [], _ => []
  | .inl f :: r, l => .inl (l.take f.length) :: regroup r (l.drop f.length)
  | .inr _ :: r, l => (l.head?.map Sum.inr).toList ++ regroup r l.tail

/-- The parse of a printed form against the segments of an input. -/
def read (input : List Segment) (s : String) : Printed :=
  let raw := split s.toList [] none
  let σs := raw.flatMap (Sum.elim id ([·]))
  let segs := σs.map fun σ ↦ segments (σ.filter (· ∉ stressMarks))
  regroup raw <| ((chunk (assign input 0 none segs.flatten) (segs.map List.length)).zip σs).map
    fun p ↦ ⟨p.1, p.2.any (· ∈ stressMarks)⟩

namespace Syl

/-- The consonants before the vowel. -/
def onset (s : Syl) : List (Segment × ℕ) := s.segs.takeWhile (¬ ·.1.IsSyllabic)

/-- The vowel and what follows it. -/
def rime (s : Syl) : List (Segment × ℕ) := s.segs.dropWhile (¬ ·.1.IsSyllabic)

/-- The consonants after the vowel. -/
def coda (s : Syl) : List (Segment × ℕ) := s.rime.dropWhile (·.1.IsSyllabic)

/-- The morae of a syllable: one for each half of its vowel, and one for a coda. -/
def morae (s : Syl) : ℕ := (s.rime.takeWhile (·.1.IsSyllabic)).length + if s.coda = [] then 0 else 1

end Syl

namespace Printed

/-- The syllables of a parse, in order. -/
def syllables (p : Printed) : List Syl := p.flatMap (Sum.elim id ([·]))

/-- The segments of a parse. -/
def output (p : Printed) : List Segment := p.syllables.flatMap fun s ↦ s.segs.map (·.1)

end Printed

namespace Syl

/-- The vowel of a syllable, its halves if it is long. -/
def vowel (s : Syl) : List (Segment × ℕ) := s.rime.takeWhile (·.1.IsSyllabic)

/-- The slots of a syllable: its segments, a long vowel one slot, each with the input positions
it stands for. -/
def slots (s : Syl) : List (Segment × List ℕ) :=
  s.onset.map (fun x ↦ (x.1, [x.2])) ++
    (s.vowel.head?.map fun v ↦ (v.1, s.vowel.map (·.2))).toList ++ s.coda.map fun x ↦ (x.1, [x.2])

end Syl

/-- Each syllable with the slot of its nucleus, the first syllable starting at slot `o`. -/
def nuclei : List Syl → ℕ → List (ℕ × Syl)
  | [], _ => []
  | s :: r, o => (o + s.onset.length, s) :: nuclei r (o + s.slots.length)

/-- The feet of a parse as the indices of their syllables, the next syllable being the `k`-th. -/
def feetIdx : Printed → ℕ → List (List ℕ)
  | [], _ => []
  | .inl f :: r, k => (List.range f.length).map (k + ·) :: feetIdx r (k + f.length)
  | .inr _ :: r, k => feetIdx r (k + 1)

/-- The parse a printed form stands for: a mora for each half of a vowel and one for a coda,
headed by its first consonant; the printed feet; and a grid mark on each stressed syllable. -/
def Printed.toParse (p : Printed) : Parse Segment :=
  let ns := nuclei p.syllables 0
  { form := Prosody.MoraicForm.ofLines (p.syllables.flatMap fun s ↦ s.slots.map (·.1))
      (syllableMora := (ns.flatMap fun x ↦
        [(x.1, Prosody.Mora.of x.1)] ++ (if 2 ≤ x.2.vowel.length then [(x.1, .of x.1 1)] else []) ++
          if x.2.coda = [] then [] else [(x.1, .of (x.1 + 1))]).toFinset)
      (syllableSegment := (ns.flatMap fun x ↦
        (List.range x.2.onset.length).map (fun j ↦ (x.1, x.1 - x.2.onset.length + j)) ++
          (List.range (x.2.coda.length - 1)).map fun j ↦ (x.1, x.1 + 2 + j)).toFinset)
      (moraSegment := (ns.flatMap fun x ↦
        [(Prosody.Mora.of x.1, x.1)] ++ (if 2 ≤ x.2.vowel.length then [(.of x.1 1, x.1)] else []) ++
          if x.2.coda = [] then [] else [(.of (x.1 + 1), x.1 + 1)]).toFinset)
    above := (feetIdx p 0).map fun f ↦
      .node ⟨.ft, 0⟩ (f.map fun j ↦ .node ⟨.syl, ((ns.map (·.1)).getD j 0)⟩ [])
    grid := p.syllables.map fun s ↦ if s.stressed then 1 else 0 }

/-- The candidate of a printed output `c` for a printed input `I`: slots correspond when they
stand for a common position, and morae in order. -/
def candidate (I c : Printed) : Candidate Segment :=
  let si := I.syllables.flatMap Syl.slots
  let so := c.syllables.flatMap Syl.slots
  Candidate.withOrderMoraCorr
    { io := .ofPairs (fun | .lhs => si.map (·.1) | .rhs => so.map (·.1))
        [(.lhs, .rhs, si.zipIdx.flatMap fun x ↦ so.zipIdx.filterMap fun y ↦
          if ∃ q ∈ x.1.2, q ∈ y.1.2 then some (x.2, y.2) else none)]
      input := I.toParse
      output := c.toParse }

/-- The stress of a slot, where its syllable is in a foot or stressed. -/
def specified (P : Parse Segment) (i : ℕ) : Option ℕ :=
  if P.stressAt i ≠ 0 ∨ ∃ t ∈ P.feet, ∃ s ∈ Prosody.syllableLeaves t, i ∈ P.form.yield s
  then some (P.stressAt i) else none

/-- The marks of a candidate whose first `stem` input slots are the Stem.
* (58) *DIST-0: a coda consonant before an onset consonant of the same sonority.
* (60) ALIGN-RIGHT(Stem, σ): the last segment of the Stem is not the last of a syllable.
* (61) IDENT-STRESS: a mora whose stress differs from that of its input mora.
* FT-BIN(μ): a foot that does not have two morae.
* *COMPLEXCODA: a coda of two consonants.
* MAX(μ): a mora of the input without one in the candidate.
* MAX: a segment of the input without one in the candidate.
* IDENT-length: a vowel of the candidate longer than in the input.
* ONSET: a syllable that begins with its vowel. -/
def marksOf (stem : ℕ) (c : Candidate Segment) : Con → ℕ :=
  let X := c.output.form
  let σs := c.output.syllableList
  fun
  | .distZero => (σs.zip σs.tail).countP fun p : ℕ × ℕ ↦ decide <|
      ∃ x ∈ X.coda p.1, (∀ z ∈ X.coda p.1, z ≤ x) ∧ ∃ y ∈ X.onset p.2, (∀ z ∈ X.onset p.2, y ≤ z) ∧
        ∃ a ∈ X.melody[x]?, ∃ b ∈ X.melody[y]?, Sonority.ofSegment a = Sonority.ofSegment b
  | .alignR =>
      if ∀ e ∈ ((c.pairs.filter fun p : ℕ × ℕ ↦ p.1 < stem).map Prod.snd).max?,
        ∃ s ∈ X.syllables, e ∈ X.yield s ∧ ∀ z ∈ X.yield s, z ≤ e then 0 else 1
  | .identStress => c.pairs.countP fun p : ℕ × ℕ ↦ decide <|
      (X.moraeAt p.2).Nonempty ∧ ∃ b ∈ specified c.input p.1, b ≠ c.output.stressAt p.2
  | .ftBin => c.output.ftBinViol
  | .complexCoda => c.output.complexCodaViol
  | .maxMora => c.maxMoraViol
  | .max => c.io.maxViol .lhs .rhs
  | .identLength => c.identViol fun P i ↦
      (P.form.melody[i]?).bind fun x ↦ if x.IsSyllabic then some (P.weightAt i) else none
  | .onset => c.output.onsetViol

/-- A tableau as the paper prints it: the input, the candidates and the winner. -/
structure Evaluation where
  input : String
  candidates : List String
  winner : String
  deriving DecidableEq

namespace Evaluation

variable (t : Evaluation)

/-- The segments of the input. -/
def segs : List Segment := segments (t.input.toList.filter (· ∉ "(). ".toList ++ stressMarks))

/-- The Stem of the paper's tableaux, *samudr-am*. -/
def stem : ℕ := (segments "samudram".toList).length

/-- The Stem in slots of the input. -/
def stemSlots : ℕ :=
  ((read t.segs t.input).syllables.flatMap Syl.slots).countP fun x ↦ ∀ q ∈ x.2, q < stem

/-- The candidate a printed form stands for. -/
def candidate (c : String) : Candidate Segment :=
  Aitha2026.candidate (read t.segs t.input) (read t.segs c)

/-- The marks of the tableau. -/
def marks (c : String) : Con → ℕ := marksOf t.stemSlots (t.candidate c)

/-- The optimal candidates under a ranking: those that survive filtration along it. -/
def optimal (σ : Ranking Con) : Finset String :=
  filtration t.marks t.candidates.toFinset (List.ofFn σ)

/-- The comparative tableau: the ERC of the winner against each other candidate. -/
def comparative : List (ERC Con) :=
  OptimalityTheory.comparative t.marks t.winner (t.candidates.filter (· ≠ t.winner))

/-- The grammar of the tableau: the rankings that satisfy its comparative tableau, those under
which its winner is optimal. -/
def grammar : Grammar Con := .ofERCs {α | α ∈ t.comparative}

/-- The segments of the winner. -/
def output : List Segment := (read t.segs t.winner).output

variable {t} {R : Con → Con → Prop}

theorem mem_extent_grammar (h : t.winner ∈ t.candidates) :
    σ ∈ t.grammar.extent ↔ t.winner ∈ t.optimal σ := by
  rw [grammar, comparative, Grammar.Enumeration.ofERCs_comparative]
  exact Grammar.Enumeration.mem_extent_ofWinner (List.mem_toFinset.2 h)

-- a winner whose comparative tableau holds of a diagram and has no neutral row is the sole
-- optimal candidate under every total ranking extending the diagram
theorem optimal_eq (hw : t.winner ∈ t.candidates) (hle : .ofRel R ≤ t.grammar)
    (hne : ∀ α ∈ t.comparative, ∃ k, α k ≠ .e) (hσ : σ.IsLinearExtension R) :
    t.optimal σ = {t.winner} :=
  filtration_eq_singleton_of_comparative ((mem_extent_grammar hw).1 <|
    Concept.extent_subset_extent_iff.2 hle (Grammar.Enumeration.mem_extent_ofRel.2 hσ)) hne

end Evaluation

/-! ### The tableaux

The inputs are syllabified here where the paper prints the unparsed suffixes as one string. -/

/-- (59): the dativeWord, where /m/ deletes and /a/ lengthens. -/
def dativeWord : Evaluation where
  input := "(ˈsa.mu).(ˌdram).ˌni.ki"
  candidates :=
    ["(ˈsa.mu).(ˌdram).(ˌni.ki)", "(ˈsa.mu).dra.(ˌmi.ki)", "(ˈsa.mu).dra.(ˌni.ki)",
      "(ˈsa.mu).(ˌdrā).(ˌni.ki)", "(ˈsa.mu).(ˌdrā).(ˌmi.ki)"]
  winner := "(ˈsa.mu).(ˌdrā).(ˌni.ki)"

/-- (62): the nominativeWord, where word-final stressed *-ni* cannot head a binary foot and
deletes. -/
def nominativeWord : Evaluation where
  input := "(ˈsa.mu).(ˌdram).ˌni"
  candidates :=
    ["(ˈsa.mu).(ˌdram).ni", "(ˈsa.mu).(ˌdram).(ˌni)", "(ˈsa.mu).(ˌdramn)", "(ˈsa.mu).(ˌdran)",
      "(ˈsa.mu).(ˌdram)"]
  winner := "(ˈsa.mu).(ˌdram)"

/-- (63): the noun with a postposed quantifier at the Word level. -/
def quantifiedWord : Evaluation where
  input := "(ˈsa.mu).(ˌdram).ˌni.an.ta.ṭi.ni"
  candidates :=
    ["(ˈsa.mu).(ˌdram).ni.(ˌan).(ˌta.ṭi).ni", "(ˈsa.mu).(ˌdram).(ˌni).(ˌan).(ˌta.ṭi).ni",
      "(ˈsa.mu).(ˌdram).(ˌnan).(ˌta.ṭi).ni", "(ˈsa.mu).(ˌdran).(ˌan).(ˌta.ṭi).ni",
      "(ˈsa.mu).(ˌdram).(ˌan).(ˌta.ṭi).ni", "(ˈsa.mu).dra.(ˌnan).(ˌta.ṭi).ni"]
  winner := "(ˈsa.mu).(ˌdram).(ˌan).(ˌta.ṭi).ni"

/-- (66): the noun before the postposition *nunci* 'from', where the /mn/ contact stays. -/
def postpositional : Evaluation where
  input := "(ˈsa.mu).(ˌdram) (ˈnun).(ci)"
  candidates :=
    ["(ˈsa.mu).(ˌdrā) (ˈnun).(ci)", "(ˈsa.mu).dra (ˈnun).(ci)", "(ˈsa.mu).(ˌdram) (ˈun).(ci)",
      "(ˈsa.mu).(ˌdram) (ˈnun).(ci)"]
  winner := "(ˈsa.mu).(ˌdram) (ˈnun).(ci)"

/-- (67): the Word-level output of (63) at the Phrase level, where /m/ becomes the onset of
*an*. -/
def quantifiedPhrase : Evaluation where
  input := quantifiedWord.winner
  candidates :=
    ["(ˈsa.mu).(ˌdram).(ˌan).(ˌta.ṭi).ni", "(ˈsa.mu).dra.(ˌman).(ˌta.ṭi).ni",
      "(ˈsa.mu).(ˌdrā).(ˌman).(ˌta.ṭi).ni", "(ˈsa.mu).(ˌdra).(ˌman).(ˌta.ṭi).ni"]
  winner := "(ˈsa.mu).dra.(ˌman).(ˌta.ṭi).ni"

/-! ### The comparative tableaux

Each tableau as its comparative tableau: a row for each losing candidate, with the constraints
that prefer the winner and those that prefer the loser. Everything said of the rankings below is
read off these rows. -/

-- (59)
theorem comparative_dativeWord : dativeWord.comparative =
    [.ofWL [.distZero] [.max, .identLength],
      .ofWL [.alignR, .identStress, .maxMora] [.identLength],
      .ofWL [.identStress, .maxMora] [.identLength],
      .ofWL [.alignR] []] := by
  decide +kernel

-- (62)
theorem comparative_nominativeWord : nominativeWord.comparative =
    [.ofWL [.distZero, .identStress] [.maxMora, .max],
      .ofWL [.distZero, .ftBin] [.maxMora, .max],
      .ofWL [.alignR, .complexCoda] [.max],
      .ofWL [.alignR] []] := by
  decide +kernel

-- (63)
theorem comparative_quantifiedWord : quantifiedWord.comparative =
    [.ofWL [.distZero, .identStress] [.maxMora, .max],
      .ofWL [.distZero, .ftBin] [.maxMora, .max],
      .ofWL [.distZero] [.max, .onset],
      .ofWL [.alignR] [],
      .ofWL [.identStress, .maxMora] [.onset]] := by
  decide +kernel

-- (66)
theorem comparative_postpositional : postpositional.comparative =
    [.ofWL [.max, .identLength] [.distZero],
      .ofWL [.identStress, .maxMora, .max] [.distZero],
      .ofWL [.max, .onset] [.distZero]] := by
  decide +kernel

-- (67)
theorem comparative_quantifiedPhrase : quantifiedPhrase.comparative =
    [.ofWL [.onset] [.alignR, .identStress, .maxMora],
      .ofWL [.identLength] [.identStress, .maxMora],
      .ofWL [.ftBin] [.identStress]] := by
  decide +kernel

/-- The rows of the Word-level tableaux (59), (62) and (63). -/
def wordRows : List (ERC Con) :=
  dativeWord.comparative ++ nominativeWord.comparative ++ quantifiedWord.comparative

/-- The rows of the Phrase-level tableaux (66) and (67). -/
def phraseRows : List (ERC Con) := postpositional.comparative ++ quantifiedPhrase.comparative

-- (64) suffices for the Word level: every row holds of it
theorem holds_word : ∀ α ∈ wordRows, α.Holds (Above word) := by
  rw [wordRows, comparative_dativeWord, comparative_nominativeWord, comparative_quantifiedWord]
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, forall_eq, or_imp,
    forall_and]
  decide +kernel

-- (68) suffices for the Phrase level
theorem holds_phrase : ∀ α ∈ phraseRows, α.Holds (Above phrase) := by
  rw [phraseRows, comparative_postpositional, comparative_quantifiedPhrase]
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, forall_eq, or_imp,
    forall_and]
  decide +kernel

-- no losing candidate ties a winner: no row is neutral throughout
theorem exists_ne_e : ∀ α ∈ wordRows ++ phraseRows, ∃ k, α k ≠ .e := by
  rw [wordRows, phraseRows, comparative_dativeWord, comparative_nominativeWord,
    comparative_quantifiedWord, comparative_postpositional, comparative_quantifiedPhrase]
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, forall_eq, or_imp,
    forall_and]
  decide +kernel

-- any ranking under which the winner of (63) is optimal has *DIST-0 above ONSET
theorem onset_dominated (h : quantifiedWord.winner ∈ quantifiedWord.optimal σ) :
    σ.Dominates .distZero .onset :=
  ERC.SatisfiedBy.dominates (α := .ofWL [.distZero] [.max, .onset])
    ((quantifiedWord.mem_extent_grammar (by decide)).2 h
      (show _ ∈ quantifiedWord.comparative by rw [comparative_quantifiedWord]; decide +kernel))
    (by decide) (by decide)

/-- The morphs of the noun of a row, without the null ones. -/
def surface? (e : Datum) : Option (List Char) :=
  (noun? e).map fun w ↦ (w.morphs.filter (· ≠ "ø".toList)).flatten

-- (57), (65): the outputs of the strata are the attested nominative, dative and quantified forms
theorem outputs_attested :
    (surface? Examples.ocean_nom).map segments = some nominativeWord.output ∧
      (surface? Examples.ocean_dat).map segments = some dativeWord.output ∧
      (surface? Examples.ocean_whole_acc).map segments = some quantifiedPhrase.output := by
  decide +kernel

/-! ### Insertion from the root outward -/

/-- The features of the morphemes of a weak noun, and of their exponents once inserted. -/
inductive PF where
  /-- The root is on the list of roots the n exponent *-am* follows. -/
  | weak
  /-- The nominalizer. -/
  | n
  /-- Singular Num. -/
  | num
  /-- A case head. -/
  | case (c : Telugu.Case)
  /-- The exponent is *-am*. -/
  | am
  /-- The first syllable of the exponent is light. -/
  | light
  deriving DecidableEq, Repr

/-- An inserted exponent presents whether it is *-am* and whether its first syllable is light. -/
def expFeatures (e : String) : Finset PF :=
  (if e = "am" then {.am} else ∅) ∪
    if weight? e.toList = some Syllable.Weight.light then {.light} else ∅

/-- The case suffixes of `Telugu.Case`, null where a case has none. -/
def caseItems : List (VocabularyItem PF String) :=
  [Telugu.Case.nom, .acc, .gen, .dat].map fun c ↦
    {.case c} ⟷ (c.exponents.head?.map (·.form)).getD ""

/-- The Vocabulary Items of a weak noun: n is *-am* after the roots on its list, and (40) Num is
*-ni* after the exponent *-am* and null elsewhere. -/
def weakItems : List (VocabularyItem PF String) :=
  [⟨{(0, .n), (-1, .weak)}, "am"⟩, ⟨{(0, .num), (-1, .am)}, "ni"⟩, {.num} ⟷ ""] ++ caseItems

/-- (30): the rejected analysis has a second exponent of n, *-āni*, before a light syllable. -/
def pcsaItems : List (VocabularyItem PF String) :=
  [⟨{(0, .n), (-1, .weak)}, "am"⟩, ⟨{(0, .n), (-1, .weak), (1, .light)}, "āni"⟩] ++ caseItems

/-- The complex head of *samudram* 'ocean' with the heads `hs` above its root. -/
def ocean (hs : List (Finset PF)) : ComplexHead (Morpheme PF String) (Morpheme PF String) :=
  ⟨⟨{.weak}, some "samudr", .after⟩, hs.map fun fs ↦ ⟨fs, none, .after⟩⟩

/-- The exponents of a complex head after insertion from the root outward. -/
def spell (voc : List (VocabularyItem PF String))
    (w : ComplexHead (Morpheme PF String) (Morpheme PF String)) : List String :=
  (w.insertAll (· = "") voc .hierarchical expFeatures .nondeletion).exponents

-- (41), (57): insertion gives the inputs of the Word-level tableaux, *-ni* after *-am*
theorem spell_weakItems :
    segments ((spell weakItems (ocean [{.n}, {.num}, {.case .dat}])).flatMap (·.toList)) =
        dativeWord.segs ∧
      segments ((spell weakItems (ocean [{.n}, {.num}, {.case .nom}])).flatMap (·.toList)) =
        nominativeWord.segs := by
  decide +kernel

/-- When n is inserted the morphemes outside it are bare and present no exponent, so an item of n
that asks for a light syllable after it does not apply, whatever follows. -/
theorem light_notMem_contextAt (w : ComplexHead (Morpheme PF String) (Morpheme PF String))
    (hw : ∀ s ∈ w.heads, s.exp = none) (hl : ∀ s ∈ w.heads, PF.light ∉ s.feats) :
    ((1 : ℤ), PF.light) ∉ w.contextAt (· = "") .hierarchical expFeatures 0 := by
  have h := w.nth_contextAt_hierarchical (· = "") (expFeatures := expFeatures) (i := 0) (j := 1)
    (Nat.zero_le _) one_ne_zero
  simp only [Nat.cast_one, Nat.cast_zero, sub_zero] at h
  rw [Neighborhood.mem_def, h, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases hs : w.heads[1]? with
  | none => simp
  | some s =>
    have hm := List.mem_of_getElem? hs
    simp [ComplexHead.visible_of_exp_none (hw s hm), hl s hm]

-- (30) inserts *-am* in every case, the dativeWord and accusative included
theorem spell_pcsaItems :
    ∀ c : Telugu.Case, (spell pcsaItems (ocean [{.n}, {.case c}]))[1]? = some "am" := by
  decide +kernel

/-! ### The grammars of the strata -/

open Stratal

/-- The grammar of the Word level: the rankings under which the winners of (59), (62) and (63)
are optimal. -/
def wordGrammar : Grammar Con :=
  dativeWord.grammar ⊓ nominativeWord.grammar ⊓ quantifiedWord.grammar

/-- The grammar of the Phrase level: the rankings under which the winners of (66) and (67) are
optimal. -/
def phraseGrammar : Grammar Con := postpositional.grammar ⊓ quantifiedPhrase.grammar

-- the grammars of the diagrams lie below the grammars of the strata
theorem ofRel_word_le : .ofRel word ≤ wordGrammar :=
  le_inf (le_inf
    (Grammar.Enumeration.ofRel_le_ofERCs_of_holds_below fun α hα ↦
      holds_word α (List.mem_append_left _ (List.mem_append_left _ hα)))
    (Grammar.Enumeration.ofRel_le_ofERCs_of_holds_below fun α hα ↦
      holds_word α (List.mem_append_left _ (List.mem_append_right _ hα))))
    (Grammar.Enumeration.ofRel_le_ofERCs_of_holds_below fun α hα ↦
      holds_word α (List.mem_append_right _ hα))

theorem ofRel_phrase_le : .ofRel phrase ≤ phraseGrammar :=
  le_inf
    (Grammar.Enumeration.ofRel_le_ofERCs_of_holds_below fun α hα ↦
      holds_phrase α (List.mem_append_left _ hα))
    (Grammar.Enumeration.ofRel_le_ofERCs_of_holds_below fun α hα ↦
      holds_phrase α (List.mem_append_right _ hα))

-- (59), (62), (63): the winners are the sole optimal candidates under every ranking of (64)
theorem optimal_word (hσ : σ.IsLinearExtension word) :
    dativeWord.optimal σ = {dativeWord.winner} ∧
      nominativeWord.optimal σ = {nominativeWord.winner} ∧
      quantifiedWord.optimal σ = {quantifiedWord.winner} :=
  ⟨Evaluation.optimal_eq (by decide) (ofRel_word_le.trans (inf_le_left.trans inf_le_left))
      (fun α hα ↦ exists_ne_e α (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ hα)))) hσ,
    Evaluation.optimal_eq (by decide) (ofRel_word_le.trans (inf_le_left.trans inf_le_right))
      (fun α hα ↦ exists_ne_e α (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_right _ hα)))) hσ,
    Evaluation.optimal_eq (by decide) (ofRel_word_le.trans inf_le_right)
      (fun α hα ↦ exists_ne_e α (List.mem_append_left _ (List.mem_append_right _ hα))) hσ⟩

-- (66), (67): the winners are the sole optimal candidates under every ranking of (68)
theorem optimal_phrase (hσ : σ.IsLinearExtension phrase) :
    postpositional.optimal σ = {postpositional.winner} ∧
      quantifiedPhrase.optimal σ = {quantifiedPhrase.winner} :=
  ⟨Evaluation.optimal_eq (by decide) (ofRel_phrase_le.trans inf_le_left)
      (fun α hα ↦ exists_ne_e α (List.mem_append_right _ (List.mem_append_left _ hα))) hσ,
    Evaluation.optimal_eq (by decide) (ofRel_phrase_le.trans inf_le_right)
      (fun α hα ↦ exists_ne_e α (List.mem_append_right _ (List.mem_append_right _ hα))) hσ⟩

/-- A ranking of the Word-level constraints with ALIGN-RIGHT last. -/
def alignRLast : Ranking Con :=
  .ofList [.distZero, .identStress, .ftBin, .complexCoda, .maxMora, .max, .identLength, .onset,
    .alignR]

-- the three tableaux do not fix the place of ALIGN-RIGHT, which the diagram puts above MAX(μ):
-- every row is satisfied with it ranked last
theorem satisfiedBy_alignRLast : ∀ α ∈ wordRows, α.SatisfiedBy alignRLast := by
  rw [wordRows, comparative_dativeWord, comparative_nominativeWord, comparative_quantifiedWord]
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, forall_eq, or_imp,
    forall_and]
  decide +kernel

theorem not_wordGrammar_le : ¬ wordGrammar ≤ .ofRel word := fun h ↦ by
  have hmem : alignRLast ∈ wordGrammar.extent :=
    ⟨⟨fun α hα ↦ satisfiedBy_alignRLast α (List.mem_append_left _ (List.mem_append_left _ hα)),
      fun α hα ↦ satisfiedBy_alignRLast α (List.mem_append_left _ (List.mem_append_right _ hα))⟩,
      fun α hα ↦ satisfiedBy_alignRLast α (List.mem_append_right _ hα)⟩
  have hext : alignRLast.IsLinearExtension word :=
    Grammar.Enumeration.mem_extent_ofRel.1 (Concept.extent_subset_extent_iff.2 h hmem)
  exact absurd hext (by decide)

instance : Nonempty Con := ⟨.max⟩

-- (59), (66): the dative winner needs *DIST-0 above MAX and IDENT-length, the postpositional
-- winner one of them above *DIST-0, and the two rows fuse to one with no winner-preferring
-- constraint
theorem dativeWord_inf_postpositional : dativeWord.grammar ⊓ postpositional.grammar = ⊥ :=
  Grammar.Enumeration.ofERCs_inf_ofERCs_eq_bot (α := .ofWL [.distZero] [.max, .identLength])
    (β := .ofWL [.max, .identLength] [.distZero])
    (show _ ∈ dativeWord.comparative by rw [comparative_dativeWord]; decide +kernel)
    (show _ ∈ postpositional.comparative by rw [comparative_postpositional]; decide +kernel)
    (by decide +kernel)

/-- The strata are different grammars: no ranking of the constraints makes the winners of the
Word-level tableaux and those of the Phrase-level tableaux all optimal. The consonant that
deletes inside the word is kept before a postposition. -/
theorem wordGrammar_inf_phraseGrammar : wordGrammar ⊓ phraseGrammar = ⊥ :=
  eq_bot_mono (inf_le_inf (inf_le_left.trans inf_le_left) inf_le_left)
    dativeWord_inf_postpositional

-- (68): *DIST-0 and ALIGN-RIGHT against MAX, the prosodic against the segmental faithfulness
-- constraints, and IDENT-STRESS against ONSET
theorem reranked :
    Reranked (Above word) (Above phrase) .distZero .max ∧
      Reranked (Above word) (Above phrase) .alignR .max ∧
      Reranked (Above word) (Above phrase) .identStress .max ∧
      Reranked (Above word) (Above phrase) .maxMora .identLength ∧
      Reranked (Above word) (Above phrase) .identStress .onset := by
  decide +kernel

-- the Word-level diagram does not rank FT-BIN and *DIST-0
example : ¬ Reranked (Above word) (Above phrase) .distZero .ftBin := by decide +kernel

end Aitha2026
