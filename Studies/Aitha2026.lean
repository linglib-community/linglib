module

public import Linglib.Core.Order.OrdConnected
public import Linglib.Data.Examples.Aitha2026
public import Linglib.Data.Examples.Gloss
public import Linglib.Data.Examples.Readers
public import Linglib.Fragments.Telugu.Adpositions
public import Linglib.Fragments.Telugu.Case
public import Linglib.Morphology.DistributedMorphology.VocabularyInsertion.Basic
public import Linglib.Morphology.Word.Leipzig
public import Linglib.Phonology.OptimalityTheory.Stratal
public import Linglib.Phonology.OptimalityTheory.Tableau
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
the next syllable inside the prosodic word. It is the phonology of one underlying *-am-ni*,
derived in Kiparsky's Stratal OT from prespecified stress on the singular suffix *-ni*. The
strata are needed: the consonant that deletes inside the word is kept before a postposition, and
[no single ranking of the constraints selects both outputs](##not_exists_ranking).

## Implementation notes

The cells of a paradigm are the cases of `Telugu.Case` and a postposition. A case has its place
in the Case sequence of `Studies/Caha2009.lean` and the postposition is above them all; the heads
a cell's representation contains are the cells at or below it, the nominative having none.

The paper's Vocabulary Items for the strong nouns list the roots each exponent follows. A list is
one feature here, borne by the roots on it, so each exponent has one item, and the items cover
every row of the paper's table of strong nouns, which gives entries for two of its rows.

The Word- and Phrase-level rankings are the paper's Hasse diagrams, as relations on the
constraints, and a tableau is evaluated under every total ranking that extends its stratum's
diagram. The Word-level diagram has ONSET, which the paper ranks below IDENT-STRESS, below
*DIST-0 as well: the quantifier tableau, with ONSET marked on each candidate whose *an* has no
onset, has the paper's winner under a ranking only if both dominate ONSET
(`onset_dominated`).

The marks of the Stem-level tableau are computed from each parse's feet by the paper's
definitions of the three constraints, a mark of FT-BIN for each foot that is not bimoraic and a
mark of ALL-FT-LEFT for each syllable between a foot and the left edge. The marks of the other
tableaux are the printed cells.

Syllable weight is read off the transcription: a syllable is heavy when its vowel is long or a
consonant closes it.

## TODO

* The paper's argument that the weak alternation cannot be allomorphy conditioned by the
  following syllable rests on insertion from the root outward; it is not stated on
  `DistributedMorphology.ComplexHead.insertAll`.
* The Stem-level tableaux for the sandhi of *pandem* 'bet' and *peḷḷām* 'wife' and the Stem-level
  Hasse diagram are not formalized.
* The marks of the Word- and Phrase-level tableaux are not computed from representations of the
  candidates.

## References

* [aitha-2026]
* [caha-2009]
* [mcfadden-2018]
* [kiparsky-2000]
* [bobaljik-2000]
-/

@[expose] public section

namespace Aitha2026

open DistributedMorphology Morphology Prosody OptimalityTheory
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

/-- The long vowels of the transcription. -/
def longVowels : List Char := "āīūēōǣ".toList

/-- The short vowels of the transcription. -/
def shortVowels : List Char := "aiueo".toList

/-- The weight of the first syllable of a transcribed form: heavy when its vowel is long or a
consonant closes it, and light otherwise. -/
def weight (s : List Char) : Syllable.Weight :=
  match s.dropWhile (· ∉ shortVowels ++ longVowels) with
  | [] => .light
  | v :: rest =>
    if v ∈ longVowels ∨ (rest.take 2).all (· ∉ shortVowels ++ longVowels) ∧ rest ≠ [] then .heavy
    else .light

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
  | .case c => c.exponents.head?.map fun m ↦ ⟨.case, weight m.form.toList⟩
  | .postposition =>
    Telugu.Adpositions.lō.morphs.head?.map fun m ↦ ⟨.postposition, weight m.form.toList⟩

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

/-! ### The singular suffix -/

/-- The exponent of n that the singular suffix follows. -/
inductive NExponent where
  | am
  deriving DecidableEq, Repr

/-- The exponents of Num in the singular. -/
inductive NumExponent where
  | ni | null
  deriving DecidableEq, Repr

/-- (40): Num is *-ni* after the exponent *-am* of n and null elsewhere. The context is the
morpheme to the left, already realized when Num is. -/
def numItems : RuleSet (VocabularyItem NExponent NumExponent) :=
  [⟨{(-1, .am)}, .ni⟩, ∅ ⟷ .null]

-- (41)
theorem numItems_am :
    subsetPrinciple numItems { focus := ∅, leftCtx := [{.am}] } = some .ni ∧
      subsetPrinciple numItems { focus := ∅, leftCtx := [∅] } = some .null := by
  decide

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
  pure ⟨k, weight m⟩

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
theorem stem_optimal : (Tableau.ofList Finset.univ stemRanking).optimal = {.trochees} := by decide

/-! ### The rankings of the Word and the Phrase -/

/-- The constraints of (64) and (68). -/
inductive Con where
  | distZero | alignR | identStress | ftBin | complexCoda | maxMora | max | identLength | onset
  deriving DecidableEq, Repr, Fintype

/-- (64): the Word-level ranking. *DIST-0, ALIGN-RIGHT, IDENT-STRESS, FT-BIN and *COMPLEX-CODA
dominate MAX(μ), which dominates MAX and IDENT-length, and IDENT-STRESS and *DIST-0 dominate
ONSET. -/
def word (a b : Con) : Prop :=
  a = b ∨
    match b with
    | .maxMora => a ∈ [Con.distZero, .alignR, .identStress, .ftBin, .complexCoda]
    | .max | .identLength =>
      a ∈ [Con.distZero, .alignR, .identStress, .ftBin, .complexCoda, .maxMora]
    | .onset => a ∈ [Con.distZero, .identStress]
    | _ => False

/-- (68): the Phrase-level ranking. FT-BIN, ONSET, IDENT-length and MAX dominate IDENT-STRESS,
which dominates *DIST-0, which dominates ALIGN-RIGHT and MAX(μ). -/
def phrase (a b : Con) : Prop :=
  a = b ∨
    match b with
    | .identStress => a ∈ [Con.ftBin, .onset, .identLength, .max]
    | .distZero => a ∈ [Con.ftBin, .onset, .identLength, .max, .identStress]
    | .alignR | .maxMora => a ∈ [Con.ftBin, .onset, .identLength, .max, .identStress, .distZero]
    | _ => False

instance : DecidableRel word := fun a b ↦ by unfold word; cases b <;> exact inferInstance

instance : DecidableRel phrase := fun a b ↦ by unfold phrase; cases b <;> exact inferInstance

instance : IsPartialOrder Con word where
  refl _ := .inl rfl
  trans := by decide
  antisymm := by decide

instance : IsPartialOrder Con phrase where
  refl _ := .inl rfl
  trans := by decide
  antisymm := by decide

example : ∃ σ : Ranking Con 9, σ.IsLinearExtension word :=
  Ranking.exists_isLinearExtension word (by decide)

example : ∃ σ : Ranking Con 9, σ.IsLinearExtension phrase :=
  Ranking.exists_isLinearExtension phrase (by decide)

variable {σ : Ranking Con 9}

/-! ### Word-level phonology -/

/-- (59): the candidates for dative *samudr-am-ní-ki* keep /mn/, delete /n/ or /m/ with the mora,
or delete /m/ or /n/ with compensatory lengthening. -/
inductive WordCandDat where
  | faithful | deleteN | deleteM | deleteMLengthen | deleteNLengthen
  deriving DecidableEq, Repr, Fintype

/-- The marks of (59). -/
def WordCandDat.marks : ConstraintSet WordCandDat Con
  | .distZero, .faithful => 1
  | .alignR, .deleteN | .maxMora, .deleteN => 1
  | .max, .deleteN => 2
  | .maxMora, .deleteM | .max, .deleteM => 1
  | .max, .deleteMLengthen | .identLength, .deleteMLengthen => 1
  | .alignR, .deleteNLengthen | .identLength, .deleteNLengthen => 1
  | .max, .deleteNLengthen => 2
  | _, _ => 0

/-- The segments of a candidate of (59). -/
def WordCandDat.form : WordCandDat → String
  | .faithful => "samudramniki"
  | .deleteN => "samudramiki"
  | .deleteM => "samudraniki"
  | .deleteMLengthen => "samudrāniki"
  | .deleteNLengthen => "samudrāmiki"

-- (59): /m/ deletes and /a/ lengthens, the long form *samudrāniki*
theorem wordDat_optimal (hσ : σ.IsLinearExtension word) :
    (Tableau.ofRanking WordCandDat.marks σ Finset.univ).optimal = {.deleteMLengthen} :=
  Tableau.ofRanking_optimal_eq_singleton_of_rel hσ.le_dominates (Finset.mem_univ _) (by decide)

/-- (62): the candidates for nominative *samudr-am-ní* destress *-ni*, foot it alone, delete /i/
into a coda cluster, delete /i/ and /m/, or delete /ni/. -/
inductive WordCandNom where
  | destress | degenerateFoot | deleteI | deleteIM | deleteNi
  deriving DecidableEq, Repr, Fintype

/-- The marks of (62). -/
def WordCandNom.marks : ConstraintSet WordCandNom Con
  | .identStress, .destress => 1
  | .ftBin, .degenerateFoot => 1
  | .complexCoda, .deleteI | .maxMora, .deleteI | .max, .deleteI => 1
  | .alignR, .deleteIM | .maxMora, .deleteIM => 1
  | .max, .deleteIM => 2
  | .maxMora, .deleteNi => 1
  | .max, .deleteNi => 2
  | _, _ => 0

/-- The segments of a candidate of (62). -/
def WordCandNom.form : WordCandNom → String
  | .destress | .degenerateFoot => "samudramni"
  | .deleteI => "samudramn"
  | .deleteIM => "samudran"
  | .deleteNi => "samudram"

-- (62): word-final stressed *-ni* cannot head a binary foot and deletes, the short form
theorem wordNom_optimal (hσ : σ.IsLinearExtension word) :
    (Tableau.ofRanking WordCandNom.marks σ Finset.univ).optimal = {.deleteNi} :=
  Tableau.ofRanking_optimal_eq_singleton_of_rel hσ.le_dominates (Finset.mem_univ _) (by decide)

/-- (63): the candidates for *samudr-am-ní-antaṭi-ni* with a postposed quantifier destress *-ni*,
foot it alone, delete /i/ into /mn/, delete /i/ and /m/ with /n/ as coda, delete /ni/, or delete
/i/ and /m/ with /n/ resyllabified as onset. -/
inductive WordCandQ where
  | destress | degenerateFoot | deleteI | deleteIM | deleteNi | deleteIMResyllabify
  deriving DecidableEq, Repr, Fintype

/-- The marks of (63), with ONSET marked on every candidate whose *an* lacks an onset. -/
def WordCandQ.marks : ConstraintSet WordCandQ Con
  | .identStress, .destress | .onset, .destress => 1
  | .ftBin, .degenerateFoot | .onset, .degenerateFoot => 1
  | .distZero, .deleteI | .max, .deleteI => 1
  | .alignR, .deleteIM | .onset, .deleteIM => 1
  | .max, .deleteIM => 2
  | .onset, .deleteNi => 1
  | .max, .deleteNi => 2
  | .identStress, .deleteIMResyllabify => 1
  | .max, .deleteIMResyllabify => 2
  | _, _ => 0

/-- The segments of a candidate of (63). -/
def WordCandQ.form : WordCandQ → String
  | .destress | .degenerateFoot => "samudramniantaṭini"
  | .deleteI => "samudramnantaṭini"
  | .deleteIM | .deleteIMResyllabify => "samudranantaṭini"
  | .deleteNi => "samudramantaṭini"

-- (63)
theorem wordQ_optimal (hσ : σ.IsLinearExtension word) :
    (Tableau.ofRanking WordCandQ.marks σ Finset.univ).optimal = {.deleteNi} :=
  Tableau.ofRanking_optimal_eq_singleton_of_rel hσ.le_dominates (Finset.mem_univ _) (by decide)

/-- Any ranking that selects the winner of (63) has IDENT-STRESS and *DIST-0 above ONSET. -/
theorem onset_dominated
    (h : (Tableau.ofRanking WordCandQ.marks σ Finset.univ).optimal = {.deleteNi}) :
    σ.Dominates .identStress .onset ∧ σ.Dominates .distZero .onset :=
  ⟨Tableau.dominates_of_ofRanking_optimal_eq_singleton h (d := .deleteIMResyllabify)
      (Finset.mem_univ _) (by decide) (by decide) (by decide),
    Tableau.dominates_of_ofRanking_optimal_eq_singleton h (d := .deleteI)
      (Finset.mem_univ _) (by decide) (by decide) (by decide)⟩

/-! ### Phrase-level phonology -/

/-- (66): the candidates for *samudram nunci* 'from the ocean' delete /m/ with or without
lengthening, delete the postposition's /n/, or keep the /mn/ contact. -/
inductive PhraseCandP where
  | deleteMLengthen | deleteM | deleteN | faithful
  deriving DecidableEq, Repr, Fintype

/-- The marks of (66). -/
def PhraseCandP.marks : ConstraintSet PhraseCandP Con
  | .max, .deleteMLengthen => 1
  | .identStress, .deleteM | .max, .deleteM => 1
  | .max, .deleteN | .alignR, .deleteN => 1
  | .distZero, .faithful => 1
  | .alignR, .faithful => 2
  | _, _ => 0

-- (66)
theorem phraseP_optimal (hσ : σ.IsLinearExtension phrase) :
    (Tableau.ofRanking PhraseCandP.marks σ Finset.univ).optimal = {.faithful} :=
  Tableau.ofRanking_optimal_eq_singleton_of_rel hσ.le_dominates (Finset.mem_univ _) (by decide)

/-- (67): the candidates for the Word-level output of (63) keep the onsetless *an*, resyllabify
/m/ as its onset, lengthen /a/ and resyllabify, or foot the shortened *dra* alone. -/
inductive PhraseCandQ where
  | faithful | resyllabify | lengthen | degenerateFoot
  deriving DecidableEq, Repr, Fintype

/-- The marks of (67). -/
def PhraseCandQ.marks : ConstraintSet PhraseCandQ Con
  | .onset, .faithful => 1
  | .identStress, .resyllabify | .alignR, .resyllabify | .maxMora, .resyllabify => 1
  | .identLength, .lengthen | .alignR, .lengthen => 1
  | .ftBin, .degenerateFoot | .identStress, .degenerateFoot | .alignR, .degenerateFoot
  | .maxMora, .degenerateFoot => 1
  | _, _ => 0

/-- The segments of a candidate of (67). -/
def PhraseCandQ.form : PhraseCandQ → String
  | .lengthen => "samudrāmantaṭini"
  | _ => "samudramantaṭini"

-- (67)
theorem phraseQ_optimal (hσ : σ.IsLinearExtension phrase) :
    (Tableau.ofRanking PhraseCandQ.marks σ Finset.univ).optimal = {.resyllabify} :=
  Tableau.ofRanking_optimal_eq_singleton_of_rel hσ.le_dominates (Finset.mem_univ _) (by decide)

/-! ### The outputs -/

/-- The morphs of the noun of a row, without the null ones. -/
def surface? (e : Datum) : Option (List Char) :=
  (noun? e).map fun w ↦ (w.morphs.filter (· ≠ "ø".toList)).flatten

-- (57), (65): the outputs of the strata are the attested nominative, dative and quantified forms
theorem outputs_attested :
    surface? Examples.ocean_nom = some WordCandNom.deleteNi.form.toList ∧
      surface? Examples.ocean_dat = some WordCandDat.deleteMLengthen.form.toList ∧
      surface? Examples.ocean_whole_acc = some PhraseCandQ.resyllabify.form.toList ∧
      WordCandQ.deleteNi.form = PhraseCandQ.faithful.form := by
  decide

/-! ### Reranking -/

open Stratal

/-- No single ranking of the constraints selects both the dative with /m/ deleted inside the
word and the postpositional phrase with /m/ kept: the first needs *DIST-0 above MAX and the
second MAX above *DIST-0. -/
theorem not_exists_ranking :
    ¬ ∃ σ : Ranking Con 9,
      (Tableau.ofRanking WordCandDat.marks σ Finset.univ).optimal = {.deleteMLengthen} ∧
        (Tableau.ofRanking PhraseCandP.marks σ Finset.univ).optimal = {.faithful} := by
  rintro ⟨σ, hw, hp⟩
  have h₁ : σ.Dominates .distZero .max :=
    Tableau.dominates_of_ofRanking_optimal_eq_singleton hw (d := .faithful)
      (Finset.mem_univ _) (by decide) (by decide) (by decide)
  have h₂ : σ.Dominates .max .distZero :=
    Tableau.dominates_of_ofRanking_optimal_eq_singleton hp (d := .deleteMLengthen)
      (Finset.mem_univ _) (by decide) (by decide) (by decide)
  exact lt_asymm h₁ h₂

-- (63), (67): nor does one ranking leave *an* without an onset in the word and give it one after
theorem not_exists_ranking_onset :
    ¬ ∃ σ : Ranking Con 9,
      (Tableau.ofRanking WordCandQ.marks σ Finset.univ).optimal = {.deleteNi} ∧
        (Tableau.ofRanking PhraseCandQ.marks σ Finset.univ).optimal = {.resyllabify} := by
  rintro ⟨σ, hw, hp⟩
  have h₂ : σ.Dominates .onset .identStress :=
    Tableau.dominates_of_ofRanking_optimal_eq_singleton hp (d := .faithful)
      (Finset.mem_univ _) (by decide) (by decide) (by decide)
  exact lt_asymm (onset_dominated hw).1 h₂

-- (68): *DIST-0 and ALIGN-RIGHT against MAX, the prosodic against the segmental faithfulness
-- constraints, and IDENT-STRESS against ONSET
theorem reranked :
    Reranked word phrase .distZero .max ∧ Reranked word phrase .alignR .max ∧
      Reranked word phrase .identStress .max ∧ Reranked word phrase .maxMora .identLength ∧
      Reranked word phrase .identStress .onset := by
  decide

-- neither diagram ranks FT-BIN and *DIST-0 at the Word level
example : ¬ Reranked word phrase .distZero .ftBin := by decide

end Aitha2026
