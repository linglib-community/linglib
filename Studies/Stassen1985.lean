module

public import Linglib.Syntax.Comparative
public import Linglib.Data.UD.Features
public import Linglib.Fragments.Japanese.Comparison
public import Linglib.Fragments.Korean.Comparison
public import Linglib.Fragments.Turkish.Comparison
public import Linglib.Fragments.HindiUrdu.Comparison
public import Linglib.Fragments.Mandarin.Comparison
public import Linglib.Fragments.English.Comparison
public import Linglib.Fragments.Swahili.Comparison
public import Linglib.Fragments.Korean.Clause
public import Linglib.Fragments.Turkish.Clause

/-!
# Stassen (1985): Comparison and Universal Grammar

This file formalizes Stassen's typology of comparative constructions and his explanation of it
by temporal chaining. A comparative assigns its standard noun phrase derived case, the case of
the comparee, or a fixed case, and a fixed-case standard is the direct object of a verb of
exceeding or an adverbial in a separative, allative or locative case, which gives six types. A
temporal chain is consecutive or simultaneous and is balanced, both predicates keeping their
rank, or deranked, one predicate reduced, either only under identity of subjects or absolutely,
and an absolutely deranked consecutive chain reduces its anterior or its posterior predicate,
which gives the seven syntactic types of chaining. The book's thesis is that a language models
its comparative on one of its chains, and its chaining-based universals follow from the
modelling. Over the fragments, Japanese, Korean, Turkish and Hindi-Urdu have the separative
comparative the book lists them under, Mandarin and Swahili the exceed one, Swahili also a
secondary conjoined one and English the particle one, and the converbs of Korean and Turkish
derank their chains as a separative comparative requires.

## Main definitions

* `Stassen1985.Type1985`, `Stassen1985.type1985`: the six comparative types and the type of a
  construction, read off its anatomy
* `Stassen1985.ChainType`: the seven syntactic types of temporal chaining, with their
  `temporality`, `strategy`, `conditionality` and `direction`
* `Stassen1985.Models`: the chains a comparative type is modelled on
* `Stassen1985.strategy`: the strategy a medial verb form shows

## Main results

* `Stassen1985.toWALS_type1985`, `caseAssignment_type1985`, `spatialCase_type1985`: the type
  agrees with the construction's anatomy and collapses to the type of the atlas
* `Stassen1985.universal1A` to `Stassen1985.universal4`: the chaining-based universals
* `Stassen1985.separative_fragments`, `mandarin_exceed`, `english_particle`,
  `swahili_double_option`: the fragments' constructions under the typology
* `Stassen1985.korean_consistent`, `Stassen1985.turkish_consistent`: the chains a separative
  comparative is modelled on have the strategy the converbs show

## Implementation notes

* The universals are stated over the modelling relation, as the book states them of a
  language that has a comparative of the type, so each says that a chain the type is modelled
  on has the property. The chaining data of the sample that Part Two of the book tests the
  universals against are not transcribed, and the language types of §4.7 under the Principle
  of Parallel Chaining and the procedure-based universals of chapter 15 are not formalized.
* A clause-chaining fragment records the form of a medial verb but neither the conditionality
  of its deranking nor the direction of the reduced predicate, so it yields a strategy and not
  a chain type.
* The mixed comparatives of §2.5, the conjoined exceed comparatives of Fulani, Acholi, Motu,
  Tamazight and Temne, have no type here, and neither has an adverbial standard in no spatial
  case, such as the Finnish partitive or the Swahili *kuliko* the book calls indeterminate.

## References

* [L. Stassen, *Comparison and Universal Grammar* (1985)][stassen-1985]
* [L. Stassen, *Comparative Constructions* (2013)][stassen-2013]
-/

@[expose] public section

namespace Stassen1985

open Comparative

/-! ### The six comparative types -/

/-- The comparative types are the three adverbial types, by the spatial case of the
standard, the exceed type, and the two derived-case types. -/
inductive Type1985
  | separative
  | allative
  | locative
  | exceed
  | conjoined
  | particle
  deriving DecidableEq, Repr, Fintype

namespace Type1985

/-- The type of the atlas, which collapses the adverbial types into one. -/
def toWALS : Type1985 → ComparativeType
  | .separative | .allative | .locative => .locational
  | .exceed => .exceed
  | .conjoined => .conjoined
  | .particle => .particle

/-- The case assignment of a type is derived for the conjoined and particle types and fixed
otherwise. -/
def caseAssignment : Type1985 → CaseAssignment
  | .conjoined | .particle => .derived
  | _ => .fixed

/-- The encoding of a fixed-case standard. -/
def fixedEncoding : Type1985 → Option FixedCaseEncoding
  | .exceed => some .directObject
  | .separative | .allative | .locative => some .adverbial
  | .conjoined | .particle => none

/-- The spatial case of an adverbial standard. -/
def spatialCase : Type1985 → Option Case
  | .separative => some .abl
  | .allative => some .all
  | .locative => some .loc
  | _ => none

theorem caseAssignment_eq_derived_iff :
    ∀ t : Type1985, t.caseAssignment = .derived ↔ t = .particle ∨ t = .conjoined := by decide

theorem fixedEncoding_eq_adverbial_iff :
    ∀ t : Type1985, t.fixedEncoding = some .adverbial ↔ t.spatialCase.isSome := by decide

end Type1985

/-- The type of a construction, read off its anatomy; `none` for an adverbial standard in no
spatial case. -/
def type1985 (c : Comparative) : Option Type1985 :=
  match c.caseAssignment, c.fixedEncoding, c.standardCase with
  | .derived, _, _ => some (if c.standardMarker = [] then .conjoined else .particle)
  | .fixed, some .directObject, _ => some .exceed
  | .fixed, _, some .abl => some .separative
  | .fixed, _, some .all => some .allative
  | .fixed, _, some .loc => some .locative
  | .fixed, _, _ => none

theorem toWALS_type1985 {c : Comparative} {t : Type1985} (h : type1985 c = some t) :
    t.toWALS = c.type := by
  obtain ⟨m, ca, fe, sc, _⟩ := c
  cases ca
  · cases m <;> simp_all [type1985, Comparative.type, Type1985.toWALS] <;> (subst h; rfl)
  · rcases fe with _ | _ | _ <;> rcases sc with _ | k <;> (try cases k) <;>
      simp_all [type1985, Comparative.type, Type1985.toWALS] <;> (subst h; rfl)

theorem caseAssignment_type1985 {c : Comparative} {t : Type1985} (h : type1985 c = some t) :
    t.caseAssignment = c.caseAssignment := by
  obtain ⟨m, ca, fe, sc, _⟩ := c
  cases ca
  · cases m <;> simp_all [type1985, Type1985.caseAssignment] <;> (subst h; rfl)
  · rcases fe with _ | _ | _ <;> rcases sc with _ | k <;> (try cases k) <;>
      simp_all [type1985, Type1985.caseAssignment] <;> (subst h; rfl)

theorem spatialCase_type1985 {c : Comparative} {t : Type1985} (h : type1985 c = some t)
    (hs : t.spatialCase.isSome) : t.spatialCase = c.standardCase := by
  obtain ⟨m, ca, fe, sc, _⟩ := c
  cases ca
  · cases m <;> simp_all [type1985, Type1985.spatialCase] <;> (subst h; simp at hs)
  · rcases fe with _ | _ | _ <;> rcases sc with _ | k <;> (try cases k) <;>
      simp_all [type1985, Type1985.spatialCase] <;>
      (subst h; first | rfl | simp at hs)

/-! ### Temporal chaining -/

/-- A chain is consecutive, one event after the other, or simultaneous. -/
inductive Temporality
  | consecutive
  | simultaneous
  deriving DecidableEq, Repr, Fintype

/-- A chain is balanced, both predicates keeping their structural rank, or deranked, one
predicate reduced. -/
inductive Strategy
  | balancing
  | deranking
  deriving DecidableEq, Repr, Fintype

/-- A deranked chain reduces a predicate only under identity of the subjects, or absolutely. -/
inductive Conditionality
  | conditional
  | absolute
  deriving DecidableEq, Repr, Fintype

/-- A deranked consecutive chain reduces its anterior or its posterior predicate. -/
inductive Direction
  | anterior
  | posterior
  deriving DecidableEq, Repr, Fintype

/-- The seven syntactic types of temporal chaining (§4.6). A consecutive chain is balanced,
conditionally deranked with its posterior predicate reduced, or absolutely deranked with its
anterior or its posterior predicate reduced, and a simultaneous chain is balanced, conditionally
deranked or absolutely deranked. -/
inductive ChainType
  | consecutiveBalanced
  | consecutiveConditional
  | consecutiveAnterior
  | consecutivePosterior
  | simultaneousBalanced
  | simultaneousConditional
  | simultaneousAbsolute
  deriving DecidableEq, Repr, Fintype

namespace ChainType

/-- The temporality of a chain type. -/
def temporality : ChainType → Temporality
  | .consecutiveBalanced | .consecutiveConditional | .consecutiveAnterior
  | .consecutivePosterior => .consecutive
  | .simultaneousBalanced | .simultaneousConditional | .simultaneousAbsolute => .simultaneous

/-- The strategy of a chain type. -/
def strategy : ChainType → Strategy
  | .consecutiveBalanced | .simultaneousBalanced => .balancing
  | _ => .deranking

/-- The conditionality of a deranked chain type. -/
def conditionality : ChainType → Option Conditionality
  | .consecutiveConditional | .simultaneousConditional => some .conditional
  | .consecutiveAnterior | .consecutivePosterior | .simultaneousAbsolute => some .absolute
  | .consecutiveBalanced | .simultaneousBalanced => none

/-- The direction of a deranked consecutive chain type, posterior for the conditionally
deranked one. -/
def direction : ChainType → Option Direction
  | .consecutiveConditional | .consecutivePosterior => some .posterior
  | .consecutiveAnterior => some .anterior
  | _ => none

theorem conditionality_isSome_iff (ct : ChainType) :
    ct.conditionality.isSome ↔ ct.strategy = .deranking := by
  cases ct <;> decide

theorem direction_isSome_iff (ct : ChainType) :
    ct.direction.isSome ↔ ct.temporality = .consecutive ∧ ct.strategy = .deranking := by
  cases ct <;> decide

end ChainType

/-- The book's thesis is that a comparative is modelled on a temporal chain. A particle
comparative is modelled on a balanced chain of either temporality, a conjoined comparative on
the balanced simultaneous chain, an exceed comparative on a conditionally deranked chain,
usually the simultaneous one, and the three adverbial comparatives on the absolutely deranked
chains, the separative on the anterior consecutive, the allative on the posterior consecutive
and the locative on the simultaneous one. -/
inductive Models : ChainType → Type1985 → Prop
  | particleConsecutive : Models .consecutiveBalanced .particle
  | particleSimultaneous : Models .simultaneousBalanced .particle
  | conjoined : Models .simultaneousBalanced .conjoined
  | exceedConsecutive : Models .consecutiveConditional .exceed
  | exceedSimultaneous : Models .simultaneousConditional .exceed
  | separative : Models .consecutiveAnterior .separative
  | allative : Models .consecutivePosterior .allative
  | locative : Models .simultaneousAbsolute .locative

instance (ct : ChainType) (t : Type1985) : Decidable (Models ct t) := by
  cases ct <;> cases t <;> first
    | exact isTrue (by constructor)
    | exact isFalse (by intro h; cases h)

theorem exists_models : ∀ t : Type1985, ∃ ct, Models ct t := by decide

/-! ### The chaining-based universals (§5.2) -/

variable {ct : ChainType} {t : Type1985}

theorem universal1A (h : Models ct t) (hd : t.caseAssignment = .derived) :
    ct.strategy = .balancing := by
  revert ct t; decide

theorem universal1B (h : Models ct t) (hf : t.caseAssignment = .fixed) :
    ct.strategy = .deranking := by
  revert ct t; decide

theorem universal2A (h : Models ct .exceed) : ct.conditionality = some .conditional := by
  revert ct; decide

theorem universal2B (h : Models ct t) (ha : t.fixedEncoding = some .adverbial) :
    ct.conditionality = some .absolute := by
  revert ct t; decide

theorem universal3A (h : Models ct .separative) : ct = .consecutiveAnterior := by
  revert ct; decide

theorem universal3B (h : Models ct .allative) : ct = .consecutivePosterior := by
  revert ct; decide

theorem universal3C (h : Models ct .locative) : ct = .simultaneousAbsolute := by
  revert ct; decide

theorem universal4 (h : Models ct .conjoined) : ct = .simultaneousBalanced := by
  revert ct; decide

/-! ### The fragments -/

/-- The strategy a medial verb form shows is balancing when the form is finite and deranking
otherwise. -/
def strategy : UD.VerbForm → Strategy
  | .Fin => .balancing
  | _ => .deranking

theorem separative_fragments :
    ∀ c ∈ [Japanese.Comparison.yori, Korean.Comparison.boda, Turkish.Comparison.dan,
      HindiUrdu.Comparison.se], type1985 c = some .separative := by
  decide

theorem mandarin_exceed : type1985 Mandarin.Comparison.bi = some .exceed := by decide

/-- English has a particle comparative, the construction of §9.4. -/
theorem english_particle : type1985 English.Comparison.than = some .particle := by decide

theorem swahili_double_option :
    type1985 Swahili.Comparison.kushinda = some .exceed ∧
      type1985 Swahili.Comparison.conjoined = some .conjoined ∧
      type1985 Swahili.Comparison.kuliko = none := by
  decide

theorem korean_consistent :
    ∀ ct, Models ct .separative →
      ∀ c : Korean.Converb, ct.strategy = strategy c.verbForm := by
  decide

theorem turkish_consistent :
    ∀ ct, Models ct .separative →
      ∀ c : Turkish.Converb, ct.strategy = strategy c.verbForm := by
  decide

end Stassen1985
