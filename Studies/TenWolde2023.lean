module

public import Mathlib.Order.Interval.Set.OrdConnected
public import Mathlib.Order.UpperLower.Basic
public import Mathlib.Data.Fintype.Sum
public import Linglib.Syntax.ConstructionGrammar.Constructicon
public import Studies.Traugott2010

/-!
# ten Wolde (2023): The English Binominal Noun Phrase: A Cognitive-Functional Approach

This file formalizes ten Wolde's account of the English *of*-binominal as a grammaticalization
path from the prototypical N+PP (*the hell of his own invention*) through the head-classifier
(*a hell of loneliness*) and the evaluative binominal noun phrase (*a hell of a hotel*) to the
evaluative modifier (*a hell of a man*) and the binominal intensifier (*a hell of a large sum*)
(`Stage`). The features of the book's two overview tables hold over intervals of the path, with
one exception (`ordConnected_span_iff`): the second determiner is lost in the head-classifier and
reappears in the evaluative binominal, which the book explains by inheritance from the N+PP, and
which the network derives (`inherited_secondDeterminer`). A
feature that holds over an interval is never lost once gained if it holds at the last stage
(`isUpperSet_span_of_top_mem`), and the features together tell every two stages apart
(`profile_injective`).

Every first noun of the case studies and of the corpus study is attested at all stages below the
ones it has reached (`isLowerSet_stages`). In the constructional network every later stage
inherits from the N+PP mother node, the horizontal metaphorical links are the covering relation of
the path (`metaphorical_iff_covBy`), and the step onto the evaluative stages is a subjectification
in Traugott's sense.

## Implementation notes

* The spans of the diagnostics are read off the feature rows of Tables 3.2 and 4.2, the path off
  Figure 6.1, the semantic classes off Table 2.1, the attestations off Figures 5.1 and 5.2 and
  the summary of chapter 6, and the links off the network figures of chapter 8.
* A diagnostic is the set of stages at which it holds. The second determiner of the N+PP is an
  open determiner slot, which is counted here as marking number.
* A noun records the pseudo-partitive separately from its stages. Figure 6.1 draws that
  construction as an optional detour between the head-classifier and the evaluative binominal,
  not as a stage of the path.

## References

* [ten-wolde-2023]
* [traugott-2010]
-/

@[expose] public section

namespace TenWolde2023

/-! ### The path -/

/-- The constructions on the grammaticalization path, from the most lexical to the most
grammaticalized. -/
inductive Stage where
  /-- The first noun denotes a referent and the prepositional phrase ascribes a property to it,
  as in *the hell of his own invention*. -/
  | nPP
  /-- The second noun classifies the type or material of the first, as in *a hell of loneliness*. -/
  | headClassifier
  /-- The first noun ascribes an evaluative property to the referent of the second, as in *a hell
  of a hotel*. -/
  | evaluative
  /-- The chunk [N₁ *of a*] is a modifier evaluating the second noun, as in *a hell of a man*. -/
  | evaluativeModifier
  /-- The chunk [N₁ *of a*] intensifies a following adjective or quantifier, as in *a hell of
  a large sum*. -/
  | binominalIntensifier
  deriving DecidableEq, Fintype, Repr

/-- The stages are ordered as they are listed. -/
instance : LinearOrder Stage := LinearOrder.lift' Stage.ctorIdx (by decide)

instance : BoundedOrder Stage where
  top := .binominalIntensifier
  le_top := by decide
  bot := .nPP
  bot_le := by decide

/-- The path, from the first stage to the last. -/
def Stage.path : List Stage :=
  [nPP, headClassifier, evaluative, evaluativeModifier, binominalIntensifier]

theorem Stage.path_isChain : Stage.path.IsChain (· ⋖ ·) := by decide

/-! ### Diagnostics -/

/-- The features that separate the constructions in the book's overview tables. -/
inductive Diagnostic where
  /-- *of* has prepositional meaning, such as 'out of', 'with' or 'from'. -/
  | ofMeaningful
  /-- *of* can be left out or fused, where elsewhere it is mandatory. -/
  | ofOmissible
  /-- The first determiner can be absent. -/
  | det₁Omissible
  /-- There is a second determiner. -/
  | det₂
  /-- The second determiner marks number. -/
  | det₂Number
  /-- The first noun is the semantic, syntactic and discourse head. -/
  | n₁Head
  /-- The second noun is the syntactic head, beyond being the semantic and discourse head. -/
  | n₂SyntacticHead
  /-- The first noun ascribes an evaluative property to the second or evaluates its referent. -/
  | n₁Evaluative
  /-- [N₁ *of a*] functions as a unit, a modifier or an intensifier. -/
  | chunk
  /-- The first determiner is selected by the first noun and does not scope over the whole. -/
  | det₁ScopeN₁
  /-- The *of*-phrase can be moved and coordinated. -/
  | ofPhraseMoves
  /-- The first noun can be plural. -/
  | n₁Plural
  /-- The first noun is modified without restriction to a limited set of modifiers. -/
  | n₁FullModification
  /-- The first noun can be modified at all. -/
  | n₁Modification
  /-- The two nouns agree in number without exception. -/
  | strictAgreement
  /-- The two nouns agree in number at least as a rule. -/
  | agreement
  /-- The second noun must be a count or collective noun. -/
  | n₂CountOnly
  deriving DecidableEq, Fintype, Repr

open Stage in
/-- The stages at which a diagnostic holds. -/
def Diagnostic.span : Diagnostic → Set Stage
  | .ofMeaningful | .ofPhraseMoves => Set.Iic nPP
  | .n₁Head | .det₁ScopeN₁ => Set.Iic headClassifier
  | .n₁Plural | .n₁FullModification => Set.Iic evaluative
  | .n₁Modification => Set.Iic evaluativeModifier
  | .n₁Evaluative => Set.Ici evaluative
  | .det₁Omissible | .n₂SyntacticHead | .chunk => Set.Ici evaluativeModifier
  | .ofOmissible => Set.Ici binominalIntensifier
  | .strictAgreement => Set.Icc evaluative evaluative
  | .agreement | .n₂CountOnly => Set.Icc evaluative evaluativeModifier
  | .det₂ => {nPP} ∪ Set.Ici evaluative
  | .det₂Number => {nPP, evaluative}

instance (d : Diagnostic) : DecidablePred (· ∈ d.span) := fun _ ↦ by
  cases d <;> unfold Diagnostic.span <;> infer_instance

theorem ordConnected_span_iff (d : Diagnostic) :
    d.span.OrdConnected ↔ d ≠ .det₂ ∧ d ≠ .det₂Number := by
  have gap {s : Set Stage} (h₁ : Stage.nPP ∈ s) (h₂ : Stage.evaluative ∈ s)
      (h₃ : Stage.headClassifier ∉ s) : ¬ s.OrdConnected :=
    fun h ↦ h₃ (h.out h₁ h₂ ⟨by decide, by decide⟩)
  cases d
  case det₂ => exact iff_of_false (gap (by decide) (by decide) (by decide)) (by decide)
  case det₂Number => exact iff_of_false (gap (by decide) (by decide) (by decide)) (by decide)
  all_goals exact iff_of_true (by unfold Diagnostic.span; infer_instance) (by decide)

theorem isUpperSet_span_of_top_mem {d : Diagnostic} (hd : d.span.OrdConnected)
    (h : ⊤ ∈ d.span) : IsUpperSet d.span :=
  fun _ _ hab ha ↦ hd.out ha h ⟨hab, le_top⟩

theorem isLowerSet_span_of_bot_mem {d : Diagnostic} (hd : d.span.OrdConnected)
    (h : ⊥ ∈ d.span) : IsLowerSet d.span :=
  fun _ _ hba ha ↦ hd.out h ha ⟨bot_le, hba⟩

theorem strictAgreement_span : Diagnostic.strictAgreement.span = {.evaluative} :=
  Set.Icc_self _

theorem n₂CountOnly_not_upper_not_lower :
    ¬ IsUpperSet Diagnostic.n₂CountOnly.span ∧ ¬ IsLowerSet Diagnostic.n₂CountOnly.span :=
  ⟨fun h ↦ absurd (h (b := .binominalIntensifier) (by decide)
      (show Stage.evaluativeModifier ∈ _ by decide)) (by decide),
    fun h ↦ absurd (h (b := .nPP) (by decide) (show Stage.evaluative ∈ _ by decide)) (by decide)⟩

theorem n₁Head_span_compl : Diagnostic.n₁Head.spanᶜ = Diagnostic.n₁Evaluative.span := by
  ext s; cases s <;> decide

theorem n₁Plural_span_compl : Diagnostic.n₁Plural.spanᶜ = Diagnostic.chunk.span := by
  ext s; cases s <;> decide

/-- The diagnostics that hold at a stage. -/
def Stage.profile (s : Stage) : Finset Diagnostic := {d | s ∈ d.span}

theorem profile_injective : Function.Injective Stage.profile := by decide

/-! ### First nouns -/

/-- The semantic classes of first nouns. -/
inductive SemanticClass where
  /-- Inanimate concrete nouns such as *cake*, *nub*, *breeze* and *husk*. -/
  | inanimate
  /-- Animate nouns such as *beast*, *snake* and *whale*. -/
  | animate
  /-- Abstract nouns, among them mythical beings and expletives, such as *hell* and *bitch*. -/
  | abstract
  deriving DecidableEq, Repr

/-- A first noun with the constructions it is attested in. -/
structure Noun where
  semanticClass : SemanticClass
  /-- The stages of the path the noun is attested at. -/
  stages : Finset Stage
  /-- Whether the noun has pseudo-partitive uses, as in *a hell of microwaves*. -/
  pseudoPartitive : Bool
  /-- The orthographically reduced form of [N₁ *of a*], if there is one. -/
  fused : Option String := none
  deriving DecidableEq

namespace Noun

/-- The case-study noun *hell* is attested at every stage and fuses to *helluva*. -/
def hell : Noun := ⟨.abstract, Finset.univ, true, some "helluva"⟩

/-- The case-study noun *beast* is attested at every stage and has no pseudo-partitive uses. -/
def beast : Noun := ⟨.animate, Finset.univ, false, none⟩

/-- The case-study noun *cake* is attested up to the evaluative modifier. -/
def cake : Noun :=
  ⟨.inanimate, {.nPP, .headClassifier, .evaluative, .evaluativeModifier}, true, none⟩

/-- The noun *whale* is attested at every stage and fuses to *whaleuva*. -/
def whale : Noun := ⟨.animate, Finset.univ, false, some "whaleuva"⟩

/-- The noun *bitch* is attested at every stage, at the intensifier by a single token. -/
def bitch : Noun := ⟨.abstract, Finset.univ, false, none⟩

/-- The noun *nub* is attested up to the evaluative binominal. -/
def nub : Noun := ⟨.inanimate, {.nPP, .headClassifier, .evaluative}, true, none⟩

/-- The noun *breeze* is attested up to the evaluative binominal. -/
def breeze : Noun := ⟨.inanimate, {.nPP, .headClassifier, .evaluative}, true, none⟩

/-- The noun *husk* is attested up to the evaluative binominal. -/
def husk : Noun := ⟨.inanimate, {.nPP, .headClassifier, .evaluative}, true, none⟩

/-- The noun *snake* is animate and yet has pseudo-partitive uses. -/
def snake : Noun := ⟨.animate, {.nPP, .headClassifier, .evaluative}, true, none⟩

/-- The nouns of the three case studies. -/
def caseStudies : List Noun := [cake, beast, hell]

/-- The nouns of the case studies and of the corpus study. -/
def all : List Noun := caseStudies ++ [whale, bitch, nub, breeze, husk, snake]

end Noun

theorem isLowerSet_stages : ∀ n ∈ Noun.all, IsLowerSet (n.stages : Set Stage) := by
  simp only [IsLowerSet, Finset.mem_coe]; decide

theorem pseudoPartitive_of_inanimate :
    ∀ n ∈ Noun.all, n.semanticClass = .inanimate → n.pseudoPartitive := by decide

theorem pseudoPartitive_iff :
    ∀ n ∈ Noun.all, n.pseudoPartitive ↔
      n.semanticClass = .inanimate ∨ n = .snake ∨ n = .hell := by decide

theorem exists_mem_chunk_of_fused :
    ∀ n ∈ Noun.all, n.fused.isSome → ∃ s ∈ n.stages, s ∈ Diagnostic.chunk.span := by decide

/-! ### The constructional network -/

open ConstructionGrammar

/-- The form of the construction at each stage; the optional *a* of the modifier and the
intensifier is left out. -/
def Stage.construction : Stage → Construction Unit
  | .nPP => ⟨[{ filler := .open_ .DET }, { filler := .open_ .NOUN, isHead := true },
      { filler := .fixed "of" }, { filler := .open_ .DET }, { filler := .open_ .NOUN }], (), false⟩
  | .headClassifier => ⟨[{ filler := .open_ .DET }, { filler := .open_ .NOUN, isHead := true },
      { filler := .fixed "of" }, { filler := .open_ .NOUN }], (), false⟩
  | .evaluative => ⟨[{ filler := .open_ .DET }, { filler := .open_ .NOUN },
      { filler := .fixed "of" }, { filler := .fixed "a" },
      { filler := .open_ .NOUN, isHead := true }], (), false⟩
  | .evaluativeModifier => ⟨[{ filler := .open_ .DET }, { filler := .open_ .NOUN },
      { filler := .fixed "of" }, { filler := .open_ .NOUN, isHead := true }], (), false⟩
  | .binominalIntensifier => ⟨[{ filler := .open_ .DET }, { filler := .open_ .NOUN },
      { filler := .fixed "of" }, { filler := .open_ .ADJ },
      { filler := .open_ .NOUN, isHead := true }], (), false⟩

/-- The simple noun phrase, whose classifying and evaluative premodifiers share their function
with the binominals. -/
def simpleNP : Construction Unit :=
  ⟨[{ filler := .open_ .DET }, { filler := .open_ .NOUN, isHead := true }], (), false⟩

/-- The adjective phrase, whose intensifiers share their function with the binominal
intensifier. -/
def adjectivePhrase : Construction Unit :=
  ⟨[{ filler := .open_ .ADV }, { filler := .open_ .ADJ, isHead := true }], (), false⟩

/-- The nodes of the network: the constructions of the path, the simple noun phrase and the
adjective phrase. -/
inductive Node where
  | stage (s : Stage)
  | simpleNP
  | adjectivePhrase
  deriving DecidableEq, Fintype

/-- The construction at each node. -/
def construction : Node → Construction Unit
  | .stage s => s.construction
  | .simpleNP => simpleNP
  | .adjectivePhrase => adjectivePhrase

open Stage in
/-- The network of the *of*-binominals (chapter 8). Every construction after the N+PP has a
taxonomic link to the schematic N+PP mother node, weakened for the evaluative modifier and the
binominal intensifier (the dotted links of Figures 8.11 and 8.13). The horizontal links, which pass
no information down, are the metaphorical extensions along the path at the micro-construction
level, and the polysemy links from the head-classifier, the evaluative binominal and the evaluative
modifier to the simple noun phrase, whose premodifiers share their function (*a book of poetry*
and *a poetry book*), and from the binominal intensifier to the adjective phrase. -/
def network : Constructicon Node Unit where
  cxn := construction
  mothers
    | .stage nPP => []
    | .stage _ => [(.stage nPP, none)]
    | _ => []
  related
    | .stage nPP => [(.stage headClassifier, some .metaphorical)]
    | .stage headClassifier =>
        [(.stage evaluative, some .metaphorical), (.simpleNP, some .polysemy)]
    | .stage evaluative =>
        [(.stage evaluativeModifier, some .metaphorical), (.simpleNP, some .polysemy)]
    | .stage evaluativeModifier =>
        [(.stage binominalIntensifier, some .metaphorical), (.simpleNP, some .polysemy)]
    | .stage binominalIntensifier => [(.adjectivePhrase, some .polysemy)]
    | _ => []

/-- The depth of a node below the N+PP mother node. -/
def Node.rank : Node → ℕ
  | .stage .nPP | .simpleNP | .adjectivePhrase => 0
  | .stage _ => 1

instance : PartialOrder Node := network.partialOrder Node.rank (by decide)

instance : DecidableLE Node := network.decidableLE [.stage .nPP] (by decide)

theorem metaphorical_iff_covBy (s t : Stage) :
    (.stage t, some .metaphorical) ∈ network.related (.stage s) ↔ s ⋖ t := by
  revert s t; decide

/-- Whether a construction states a second determiner: the N+PP has one, the head-classifier has
none ("no Det2", Figure 8.6), and the constructions after it state nothing of their own. -/
def secondDeterminer : Node → Option Bool
  | .stage .nPP => some true
  | .stage .headClassifier => some false
  | _ => none

/-- Whether a construction states that its second determiner marks number: the N+PP's does, the
head-classifier has none, and the evaluative modifier's "no longer marks number for N2" (Figure
8.10), nor does the binominal intensifier's. -/
def secondDeterminerNumber : Node → Option Bool
  | .stage .nPP => some true
  | .stage .headClassifier | .stage .evaluativeModifier | .stage .binominalIntensifier =>
      some false
  | _ => none

open DefaultInheritance in
/-- "The inheritance link between the EBNP and the N+PP would explain the reappearance of the
indefinite article in the second determiner position in the EBNP" (p. 226): the stages that
inherit a second determiner through the network are exactly those at which the overview tables
record one, the head-classifier excepted. -/
theorem inherited_secondDeterminer (s : Stage) :
    true ∈ inherited secondDeterminer (.stage s) ↔ s ∈ Diagnostic.det₂.span := by
  revert s; decide

open DefaultInheritance in
theorem inherited_secondDeterminerNumber (s : Stage) :
    true ∈ inherited secondDeterminerNumber (.stage s) ↔ s ∈ Diagnostic.det₂Number.span := by
  revert s; decide

theorem head_before_of_iff (s : Stage) :
    ((s.construction.form.takeWhile (·.filler ≠ .fixed "of")).any (·.isHead)) ↔
      s ∈ Diagnostic.n₁Head.span := by
  revert s; decide

/-! ### Subjectification -/

/-- The coded level of the first noun's meaning at a stage is nonsubjective while the noun
ascribes an objective property and subjective once it expresses the speaker's evaluation. -/
def Stage.level (s : Stage) : Traugott2010.SubjectivityLevel :=
  if s ∈ Diagnostic.n₁Evaluative.span then .subjective else .nonSubjective

theorem path_unidirectional :
    Traugott2010.Unidirectional (Stage.path.map Stage.level) := by
  decide

end TenWolde2023
