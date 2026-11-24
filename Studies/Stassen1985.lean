module

public import Linglib.Data.Examples.Stassen1985
public import Linglib.Fragments.Arabic.ModernStandard.Comparison
public import Linglib.Fragments.Finnish.Comparison
public import Linglib.Fragments.HindiUrdu.Comparison
public import Linglib.Fragments.Japanese.Comparison
public import Linglib.Fragments.Korean.Clause
public import Linglib.Fragments.Korean.Comparison
public import Linglib.Fragments.Mandarin.Comparison
public import Linglib.Fragments.Romance.French.Comparison
public import Linglib.Fragments.Slavic.Russian.Comparison
public import Linglib.Fragments.Swahili.Comparison
public import Linglib.Fragments.Turkish.Clause
public import Linglib.Fragments.Turkish.Comparison
public import Linglib.Fragments.Yoruba.Comparison
public import Linglib.Syntax.Feature.Case.Spatial
public import Mathlib.Basic.PEquiv
public import Mathlib.Basic.Rel

/-!
# Stassen (1985): Comparison and Universal Grammar

Stassen classifies comparative constructions by the encoding of the standard of comparison. A
standard whose case is derived from the comparee's belongs to a conjoined comparative, two
independent clauses, or to a particle comparative. A standard in a fixed case is the direct
object of a verb of exceeding, the exceed comparative, or part of an adverbial phrase, and the
adverbial comparative is separative, allative or locative as the phrase is one of source, of
goal or of location. We define the type of a construction from the encoding of its standard, by
the direction of the case of an adverbial standard.

A temporal chain expresses two events as consecutive or as simultaneous. It is balanced, both
predicates keeping their rank, or deranked, one predicate reduced, either only under identity
of subjects or absolutely, and an absolutely deranked consecutive chain reduces its anterior or
its posterior predicate. These parameters give seven types of chaining construction.

The book's hypothesis is that a comparative is modelled on a chaining construction of its
language. We define the modelling relation `models` between the types of chain and the types of
comparative, and for a language with the chaining constructions `C` and the comparatives `T` we
state the book's eight chaining-based universals as `Universals C T`. We prove that the
universals hold exactly when every comparative of the language is modelled on one of its
chains, `T ⊆ models.image C`, and that every type of chain models some comparative and every
type of comparative is modelled on some chain.

The examples are comparatives of the book whose construction a fragment records. The type each
fragment construction has by the encoding of its standard is the type the book classes the
example under, for every recorded example but the Finnish partitive.

## Main definitions

* `Stassen1985.adverbialType`: the adverbial comparative of a spatial relation
* `Stassen1985.typeOf`: the type of a construction
* `Stassen1985.ChainType`: the seven types of temporal chaining
* `Stassen1985.models`: the modelling relation between chains and comparatives
* `Stassen1985.Universals`: the chaining-based universals of a language

## Implementation notes

* The six types are the levels of the examples' typed feature, `Examples.ComparativeType`, and
  the typology is stated on that type.
* A language is a set of chaining constructions and a set of comparatives, since the book
  allows a language several of each. A universal whose consequent is that the language is
  balancing or deranking, or has conditional or absolute deranking, is read as saying that the
  language has a chain of that kind, the reading under which the book takes a chaining type to
  be a necessary and not a sufficient condition for a comparative type.
* An adverbial standard is classed by the direction of its case, `Case.dirOf`, extended to the
  non-spatial cases the book classes by the localist analysis. The partitive is none of these,
  so the Finnish partitive standard, which the book lists as a secondary separative
  comparative, gets no type.
* The rows name the fragment's construction by a lexeme. The transcriptions of the book's
  sources are not compared with the fragments' forms.

## TODO

* The language types of the Principle of Parallel Chaining and the word orders the book
  associates with each type of deranking are not formalized, nor are the mixed comparatives,
  the chaining data of the sample that Part Two tests the universals against, and the
  procedure-based universals of Part Three.
* The Korean separative of the book marks the standard with *-eso*, which the fragment does
  not record.

## References

* [L. Stassen, *Comparison and Universal Grammar* (1985)][stassen-1985]
* [L. Stassen, *Comparative Constructions* (2013)][stassen-2013]
-/

@[expose] public section

namespace Stassen1985

open Comparative Examples
open scoped SetRel

/-! ### The types of comparative -/

namespace Examples.ComparativeType

/-- The type of the atlas, which collapses the three adverbial types into one. -/
def toWALS : ComparativeType → Data.WALS.F121A.ComparativeType
  | .separative | .allative | .locative => .locational
  | .exceed => .exceed
  | .conjoined => .conjoined
  | .particle => .particle

/-- The standard of a conjoined or a particle comparative takes its case from the comparee;
the other four types fix the case of the standard. -/
def IsDerivedCase (t : ComparativeType) : Prop := t = .conjoined ∨ t = .particle

instance : DecidablePred IsDerivedCase := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

end Examples.ComparativeType

/-- The adverbial comparative of a spatial relation: the separative for a source, the allative
for a goal and the locative for a place. -/
def adverbialType : Spatial.Path.Direction ≃. ComparativeType where
  toFun
    | .source => some .separative
    | .goal => some .allative
    | .place => some .locative
    | .route => none
  invFun
    | .separative => some .source
    | .allative => some .goal
    | .locative => some .place
    | _ => none
  inv := by decide

/-- A comparative is adverbial when it is separative, allative or locative. -/
def Examples.ComparativeType.IsAdverbial (t : ComparativeType) : Prop :=
  (adverbialType.symm t).isSome

instance : DecidablePred ComparativeType.IsAdverbial := fun _ ↦
  inferInstanceAs (Decidable (Option.isSome _ = true))

theorem toWALS_of_mem_adverbialType {d : Spatial.Path.Direction} {t : ComparativeType}
    (h : t ∈ adverbialType d) : t.toWALS = .locational := by
  revert d t; decide

/-- The spatial relation that classes an adverbial standard in the case `k`: the direction of a
spatial case and, by the localist analysis, the source for an instrumental, the goal for a
dative or a benefactive and the place for a comitative. -/
def spatialRelation? (k : Case) : Option Spatial.Path.Direction :=
  k.dirOf <|> match k with
    | .inst => some .source
    | .dat | .ben => some .goal
    | .com => some .place
    | _ => none

theorem spatialRelation?_of_dirOf {k : Case} {d : Spatial.Path.Direction}
    (h : k.dirOf = some d) : spatialRelation? k = some d := by
  simp [spatialRelation?, h]

/-- The type of a construction, by the encoding of its standard. A derived-case standard gives
a particle comparative when a marker flags it and a conjoined one otherwise, a direct object an
exceed comparative, and an adverbial standard the adverbial comparative of the spatial relation
of its case, if it has one. -/
def typeOf (c : Comparative) : Option ComparativeType :=
  match c.standard with
  | .derived => some (if c.standardMarker = [] then .conjoined else .particle)
  | .directObject => some .exceed
  | .adverbial k => (k.bind spatialRelation?).bind adverbialType

variable {c : Comparative} {t : ComparativeType}

/-- The type of a construction collapses to its type in the atlas. -/
theorem toWALS_of_mem_typeOf (h : t ∈ typeOf c) : t.toWALS = c.type := by
  cases hs : c.standard <;> simp only [typeOf, Comparative.type, hs] at h ⊢
  · obtain rfl := Option.mem_some_iff.mp h
    split <;> rfl
  · obtain rfl := Option.mem_some_iff.mp h
    rfl
  · obtain ⟨d, -, hd⟩ := Option.mem_bind_iff.mp h
    exact toWALS_of_mem_adverbialType hd

theorem isAdverbial_iff : t.IsAdverbial ↔ t = .separative ∨ t = .allative ∨ t = .locative := by
  revert t; decide

theorem isAdverbial_of_mem_adverbialType {d : Spatial.Path.Direction} (h : t ∈ adverbialType d) :
    t.IsAdverbial :=
  Option.isSome_iff_exists.mpr ⟨d, adverbialType.mem_iff_mem.mpr h⟩

theorem isDerivedCase_iff_of_mem_typeOf (h : t ∈ typeOf c) :
    t.IsDerivedCase ↔ c.standard = .derived := by
  cases hs : c.standard <;> simp only [typeOf, hs] at h
  · obtain rfl := Option.mem_some_iff.mp h
    split <;> simp [ComparativeType.IsDerivedCase]
  · obtain rfl := Option.mem_some_iff.mp h
    simp [ComparativeType.IsDerivedCase]
  · obtain ⟨d, -, hd⟩ := Option.mem_bind_iff.mp h
    rcases isAdverbial_iff.mp (isAdverbial_of_mem_adverbialType hd) with rfl | rfl | rfl <;>
      simp [ComparativeType.IsDerivedCase]

theorem isAdverbial_iff_of_mem_typeOf (h : t ∈ typeOf c) :
    t.IsAdverbial ↔ ∃ k, c.standard = .adverbial k := by
  cases hs : c.standard <;> simp only [typeOf, hs] at h
  · obtain rfl := Option.mem_some_iff.mp h
    split <;> simp [isAdverbial_iff]
  · obtain rfl := Option.mem_some_iff.mp h
    simp [isAdverbial_iff]
  · obtain ⟨d, -, hd⟩ := Option.mem_bind_iff.mp h
    simpa using isAdverbial_of_mem_adverbialType hd

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
inductive Directionality
  | anterior
  | posterior
  deriving DecidableEq, Repr, Fintype

/-- The seven syntactic types of temporal chaining. A consecutive chain is balanced,
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

/-- The directionality of a deranked consecutive chain type, posterior for the conditionally
deranked one. -/
def directionality : ChainType → Option Directionality
  | .consecutiveConditional | .consecutivePosterior => some .posterior
  | .consecutiveAnterior => some .anterior
  | _ => none

theorem conditionality_isSome_iff (ct : ChainType) :
    ct.conditionality.isSome ↔ ct.strategy = .deranking := by
  cases ct <;> decide

theorem directionality_isSome_iff (ct : ChainType) :
    ct.directionality.isSome ↔ ct.temporality = .consecutive ∧ ct.strategy = .deranking := by
  cases ct <;> decide

end ChainType

/-! ### The modelling of comparatives on chains -/

/-- The modelling relation: `c ~[models] t` when a comparative of type `t` is modelled on a
chain of type `c`. A particle comparative is modelled on a balanced chain of either
temporality, a conjoined comparative on the balanced simultaneous chain, an exceed comparative
on a conditionally deranked chain of either temporality, and the adverbial comparatives on the
absolutely deranked chains, the separative on the anterior consecutive, the allative on the
posterior consecutive and the locative on the simultaneous one. -/
def models : SetRel ChainType ComparativeType :=
  {(.consecutiveBalanced, .particle), (.simultaneousBalanced, .particle),
    (.simultaneousBalanced, .conjoined), (.consecutiveConditional, .exceed),
    (.simultaneousConditional, .exceed), (.consecutiveAnterior, .separative),
    (.consecutivePosterior, .allative), (.simultaneousAbsolute, .locative)}

instance (c : ChainType) (t : ComparativeType) : Decidable (c ~[models] t) :=
  inferInstanceAs (Decidable ((c, t) ∈ ({_, _, _, _, _, _, _, _} : Set _)))

/-- Every type of chain models some comparative and every type of comparative is modelled on
some chain. -/
theorem dom_models_cod_models : models.dom = Set.univ ∧ models.cod = Set.univ :=
  ⟨Set.eq_univ_of_forall (by decide), Set.eq_univ_of_forall (by decide)⟩

variable {ct : ChainType}

@[simp] theorem models_particle_iff : ct ~[models] .particle ↔ ct.strategy = .balancing := by
  revert ct; decide

@[simp] theorem models_conjoined_iff : ct ~[models] .conjoined ↔ ct = .simultaneousBalanced := by
  revert ct; decide

@[simp] theorem models_exceed_iff :
    ct ~[models] .exceed ↔ ct.conditionality = some .conditional := by
  revert ct; decide

@[simp] theorem models_separative_iff : ct ~[models] .separative ↔ ct = .consecutiveAnterior := by
  revert ct; decide

@[simp] theorem models_allative_iff : ct ~[models] .allative ↔ ct = .consecutivePosterior := by
  revert ct; decide

@[simp] theorem models_locative_iff : ct ~[models] .locative ↔ ct = .simultaneousAbsolute := by
  revert ct; decide

-- A chain is balanced exactly when the comparatives modelled on it have a derived-case standard.
theorem strategy_eq_balancing_iff_of_models (h : ct ~[models] t) :
    ct.strategy = .balancing ↔ t.IsDerivedCase := by
  revert ct t; decide

-- A chain is absolutely deranked exactly when the comparatives modelled on it are adverbial.
theorem conditionality_eq_absolute_iff_of_models (h : ct ~[models] t) :
    ct.conditionality = some .absolute ↔ t.IsAdverbial := by
  revert ct t; decide

variable {C : Set ChainType} {T : Set ComparativeType}

/-- The chaining-based universals of a language with the chaining constructions `C` and the
comparatives `T`. -/
structure Universals (C : Set ChainType) (T : Set ComparativeType) : Prop where
  /-- Universal 1A: a language with a derived-case comparative is balancing. -/
  balancing_of_derivedCase : ∀ t ∈ T, t.IsDerivedCase → ∃ c ∈ C, c.strategy = .balancing
  /-- Universal 1B: a language with a fixed-case comparative is deranking. -/
  deranking_of_fixedCase : ∀ t ∈ T, ¬ t.IsDerivedCase → ∃ c ∈ C, c.strategy = .deranking
  /-- Universal 2A: a language with an exceed comparative has conditional deranking. -/
  conditional_of_exceed : .exceed ∈ T → ∃ c ∈ C, c.conditionality = some .conditional
  /-- Universal 2B: a language with an adverbial comparative has absolute deranking. -/
  absolute_of_adverbial : ∀ t ∈ T, t.IsAdverbial → ∃ c ∈ C, c.conditionality = some .absolute
  /-- Universal 3A: a language with a separative comparative has an absolutely deranked
  anterior consecutive construction. -/
  anterior_of_separative : .separative ∈ T → .consecutiveAnterior ∈ C
  /-- Universal 3B: a language with an allative comparative has an absolutely deranked
  posterior consecutive construction. -/
  posterior_of_allative : .allative ∈ T → .consecutivePosterior ∈ C
  /-- Universal 3C: a language with a locative comparative has an absolutely deranked
  simultaneous construction. -/
  simultaneous_of_locative : .locative ∈ T → .simultaneousAbsolute ∈ C
  /-- Universal 4: a language with a conjoined comparative has a balanced simultaneous
  construction. -/
  balanced_of_conjoined : .conjoined ∈ T → .simultaneousBalanced ∈ C

/-- The chaining-based universals hold of a language exactly when each of its comparatives is
modelled on one of its chaining constructions. -/
theorem universals_iff : Universals C T ↔ T ⊆ models.image C := by
  refine ⟨fun h t ht ↦ ?_, fun h ↦ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · cases t
    · simpa using h.anterior_of_separative ht
    · simpa using h.posterior_of_allative ht
    · simpa using h.simultaneous_of_locative ht
    · simpa using h.conditional_of_exceed ht
    · simpa using h.balanced_of_conjoined ht
    · simpa using h.balancing_of_derivedCase _ ht (.inr rfl)
  · rintro t ht hd
    obtain ⟨ct, hct, hm⟩ := h ht
    exact ⟨ct, hct, (strategy_eq_balancing_iff_of_models hm).mpr hd⟩
  · rintro t ht hd
    obtain ⟨ct, hct, hm⟩ := h ht
    refine ⟨ct, hct, ?_⟩
    have := (strategy_eq_balancing_iff_of_models hm).not.mpr hd
    cases hs : ct.strategy <;> simp_all
  · exact fun ht ↦ by simpa using h ht
  · rintro t ht hd
    obtain ⟨ct, hct, hm⟩ := h ht
    exact ⟨ct, hct, (conditionality_eq_absolute_iff_of_models hm).mpr hd⟩
  · exact fun ht ↦ by simpa using h ht
  · exact fun ht ↦ by simpa using h ht
  · exact fun ht ↦ by simpa using h ht
  · exact fun ht ↦ by simpa using h ht

-- The universals of a language hold of any language with more chaining constructions and
-- fewer comparatives.
theorem Universals.mono {C' : Set ChainType} {T' : Set ComparativeType} (h : Universals C T)
    (hC : C ⊆ C') (hT : T' ⊆ T) : Universals C' T' :=
  universals_iff.mpr <| hT.trans <| (universals_iff.mp h).trans <| SetRel.image_mono hC

/-! ### The examples -/

/-- The fragment's construction for each lexeme of the rows. -/
def Examples.Lexeme.entry : Lexeme → Comparative
  | .dan => Turkish.Comparison.dan
  | .se => HindiUrdu.Comparison.se
  | .yori => Japanese.Comparison.yori
  | .min => Arabic.ModernStandard.Comparison.min
  | .bi => Mandarin.Comparison.bi
  | .ju => Yoruba.Comparison.ju
  | .kushinda => Swahili.Comparison.kushinda
  | .kuliko => Swahili.Comparison.kuliko
  | .chem => Russian.Comparison.chem
  | .que => French.Comparison.que
  | .kuin => Finnish.Comparison.kuin
  | .juxtaposition => Swahili.Comparison.conjoined
  | .partitive => Finnish.Comparison.partitive

/-- The type of the fragment's construction is the type the book classes the example under, for
each example but that of the Finnish partitive standard, which the book classes as separative
and whose case has no spatial relation. -/
theorem typeOf_entry :
    ∀ x : Example, ∀ l ∈ x.lexemes .standard,
      (typeOf l.entry = x.comparativeType ↔ x ≠ .ex_10_54a) := by
  decide

-- Korean and Turkish have a fixed-case comparative and, as Universal 1B requires of them,
-- medial verb forms that are not finite.
theorem deranking_fragments :
    (∀ c ∈ [Korean.Comparison.boda, Turkish.Comparison.dan], ∀ t ∈ typeOf c, ¬ t.IsDerivedCase) ∧
      (∃ m : Korean.Converb, m.verbForm ≠ .Fin) ∧ ∃ m : Turkish.Converb, m.verbForm ≠ .Fin := by
  decide

end Stassen1985
