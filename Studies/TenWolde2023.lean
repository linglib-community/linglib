module

public import Mathlib.Order.Interval.Set.OrdConnected
public import Mathlib.Order.UpperLower.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.List.MinMax
public import Linglib.Syntax.ConstructionGrammar.Constructicon
public import Linglib.Logic.Nonmonotonic.Inheritance
public import Studies.Traugott2010
public import Linglib.Data.Examples.TenWolde2023
public import Linglib.Data.Statistics.TenWolde2023

/-!
# ten Wolde (2023): The English Binominal Noun Phrase: A Cognitive-Functional Approach

The English *of*-binominal follows a grammaticalization path from the prototypical N+PP (*the hell
of his own invention*) through the head-classifier (*a hell of loneliness*) and the evaluative
binominal noun phrase (*a hell of a hotel*) to the evaluative modifier (*a hell of a man*) and the
binominal intensifier (*a hell of a large sum*). We order these constructions as a five-element
chain `Stage`. A diagnostic of the book's overview tables is the set of stages at which it holds,
`Diagnostic.span`. Every span is an interval of the path except those of the second determiner
(`ordConnected_span_iff`): the head-classifier has none and the evaluative binominal has one again,
which the constructional network derives by inheritance from the N+PP
(`inherited_secondDeterminer`). The diagnostics together tell every two stages apart
(`profile_injective`).

For nine first nouns we define `first n c`, the time at which the noun `n` is first recorded in
the construction `c`: the year of its earliest dated example, or the first decade in which the
corpus frequency tables count a token. Every noun is recorded at all stages below the ones it has
reached (`isLowerSet_stages`), and `first n` is monotone along the path for all nouns but *snake*
and *bitch* (`monotone_first_iff`). In the network every later stage inherits from the N+PP mother
node, the horizontal metaphorical links are the covering relation of the path
(`metaphorical_iff_covBy`), and the levels of subjectivity coded along the path follow Traugott's
cline (`path_followsCline`).

## Implementation notes

* The second determiner of the N+PP is an open determiner slot, which is counted here as marking
  number.
* The pseudo-partitive is a row of the frequency tables and not a `Stage`. The book draws it as an
  optional detour between the head-classifier and the evaluative binominal.
* `first` compares years of single examples with first years of decades. The two never meet for
  one noun, since the frequency tables cover six nouns and the dated examples the other three.
* The corpus begins in 1810, after all six nouns of the frequency tables had entered English, so
  an early `first` is a lower bound on the age of a construction only within the corpus.

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

-- A feature that holds over an interval and at the last stage is never lost once gained.
theorem isUpperSet_of_top_mem {s : Set Stage} (hs : s.OrdConnected) (h : ⊤ ∈ s) : IsUpperSet s :=
  fun _ _ hab ha ↦ hs.out ha h ⟨hab, le_top⟩

-- A feature that holds over an interval and at the first stage is never regained once lost.
theorem isLowerSet_of_bot_mem {s : Set Stage} (hs : s.OrdConnected) (h : ⊥ ∈ s) : IsLowerSet s :=
  fun _ _ hba ha ↦ hs.out h ha ⟨bot_le, hba⟩

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

open Examples (Example)

/-- The row of the frequency tables that records a stage of the path. -/
def Stage.category : Stage → Category
  | .nPP => .nPP
  | .headClassifier => .headClassifier
  | .evaluative => .ebnp
  | .evaluativeModifier => .em
  | .binominalIntensifier => .bi

/-- The nouns of the case studies among the first nouns. -/
def Examples.Noun.toNoun : Examples.Noun → TenWolde2023.Noun
  | .cake => .cake
  | .beast => .beast
  | .hell => .hell

/-- The row of the frequency tables that records a construction. -/
def Examples.Construction.category : Examples.Construction → Category
  | .nPP => .nPP
  | .headClassifier => .headClassifier
  | .pseudoPartitive => .pseudoPartitive
  | .ebnp => .ebnp
  | .em => .em
  | .bi => .bi

/-- The first year of the first decade in which the frequency tables record a token of the noun
in the construction, and `⊤` if they record none. -/
def firstDecade (n : Noun) (c : Category) : WithTop ℕ :=
  match (periods n).start, (frequencies n c).counts with
  | some y, some l => (l.findIdx? (0 < ·)).elim ⊤ fun i ↦ ((y + 10 * i : ℕ) : WithTop ℕ)
  | _, _ => ⊤

/-- The year of the earliest dated example of the noun in the construction, and `⊤` if there is
none. -/
def firstExample (n : Noun) (c : Category) : WithTop ℕ :=
  ((Example.all.filter fun x ↦
    x.noun.map Examples.Noun.toNoun = some n ∧
      x.construction.map Examples.Construction.category = some c).filterMap
      (·.datum.nat? "year")).minimum

/-- The time at which the noun is first recorded in the construction, by a dated example or in
the frequency tables. -/
def first (n : Noun) (c : Category) : WithTop ℕ := firstDecade n c ⊓ firstExample n c

/-- The stages of the path at which the noun is recorded. -/
def Noun.stages (n : Noun) : Set Stage := {s | first n s.category ≠ ⊤}

instance (n : Noun) : DecidablePred (· ∈ n.stages) := fun s ↦
  inferInstanceAs (Decidable (first n s.category ≠ ⊤))

/-- Every first noun is recorded at all stages of the path below the ones it has reached. -/
theorem isLowerSet_stages (n : Noun) : IsLowerSet n.stages := by
  have h : ∀ a b : Stage, b ≤ a → a ∈ n.stages → b ∈ n.stages := by cases n <;> decide +kernel
  exact fun a b hba ha ↦ h a b hba ha

/-- The constructions of a first noun are first recorded in the order of the path, except that
*snake* is recorded in the head-classifier before the N+PP and *bitch* in the evaluative binominal
before the head-classifier. -/
theorem monotone_first_iff (n : Noun) :
    Monotone (fun s : Stage ↦ first n s.category) ↔ n ≠ .snake ∧ n ≠ .bitch := by
  cases n <;> decide +kernel

-- The evaluative constructions are first recorded in the order of the path for every noun.
theorem monotoneOn_first (n : Noun) :
    MonotoneOn (fun s : Stage ↦ first n s.category) (Set.Ici .evaluative) := by
  have h : ∀ a b : Stage, .evaluative ≤ a → a ≤ b → first n a.category ≤ first n b.category := by
    cases n <;> decide +kernel
  exact fun a ha b _ hab ↦ h a b ha hab

-- The pseudo-partitive of *cake* is older than its head-classifier (section 6.4.5).
theorem first_headClassifier_le_iff (n : Noun) :
    first n .headClassifier ≤ first n .pseudoPartitive ↔ n ≠ .cake := by
  cases n <;> decide +kernel

theorem first_pseudoPartitive_ne_top_iff (n : Noun) :
    first n .pseudoPartitive ≠ ⊤ ↔
      (nouns n).semanticClass = .inanimate ∨ n = .snake ∨ n = .hell := by
  cases n <;> decide +kernel

/-! ### The constructional network -/

open ConstructionGrammar

/-- The form of the construction at each stage; the optional *a* of the modifier and the
intensifier is left out. -/
def Stage.construction : Stage → Construction Unit
  | .nPP => ⟨[{ filler := .open_ .DET }, { filler := .open_ .NOUN, isHead := true },
      { filler := .fixed "of" }, { filler := .open_ .DET }, { filler := .open_ .NOUN }], ()⟩
  | .headClassifier => ⟨[{ filler := .open_ .DET }, { filler := .open_ .NOUN, isHead := true },
      { filler := .fixed "of" }, { filler := .open_ .NOUN }], ()⟩
  | .evaluative => ⟨[{ filler := .open_ .DET }, { filler := .open_ .NOUN },
      { filler := .fixed "of" }, { filler := .fixed "a" },
      { filler := .open_ .NOUN, isHead := true }], ()⟩
  | .evaluativeModifier => ⟨[{ filler := .open_ .DET }, { filler := .open_ .NOUN },
      { filler := .fixed "of" }, { filler := .open_ .NOUN, isHead := true }], ()⟩
  | .binominalIntensifier => ⟨[{ filler := .open_ .DET }, { filler := .open_ .NOUN },
      { filler := .fixed "of" }, { filler := .open_ .ADJ },
      { filler := .open_ .NOUN, isHead := true }], ()⟩

/-- The simple noun phrase, whose classifying and evaluative premodifiers share their function
with the binominals. -/
def simpleNP : Construction Unit :=
  ⟨[{ filler := .open_ .DET }, { filler := .open_ .NOUN, isHead := true }], ()⟩

/-- The adjective phrase, whose intensifiers share their function with the binominal
intensifier. -/
def adjectivePhrase : Construction Unit :=
  ⟨[{ filler := .open_ .ADV }, { filler := .open_ .ADJ, isHead := true }], ()⟩

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

instance : PartialOrder Node := network.partialOrder (by decide)

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
/-- The stages inheriting a second determiner through the network are exactly those where the
overview tables record one, except the head-classifier (p. 226). -/
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

theorem level_monotone : Monotone Stage.level := by decide

theorem path_followsCline : Traugott2010.FollowsCline (Stage.path.map Stage.level) := by
  decide

end TenWolde2023
