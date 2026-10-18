/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Syntax.Voice.Basic

/-!
# Reciprocal constructions: morphosyntactic typology

Cross-linguistic vocabulary for reciprocal constructions: the marking strategy
([nordlinger-2023]'s synthesis of [konig-kokutani-2006], [nedjalkov-2007a], and
[evans-2008]), the site it codes and the valency it derives, the formation locus
of reciprocal verbs ([siloni-2008], [siloni-2012]), and the reciprocal markers, from which a
language's inventory is built.

## Main definitions

* `Strategy`, `CodingSite`, `Strategy.codingSite`, `Strategy.IsNominal` — the
  strategy and the site it marks.
* `Strategy.voice`, `Strategy.defaultValency` — the voice a predicate-marking
  strategy realizes (`Voice.reciprocal`) and the valency it therefore derives.
* `Indicator`, `Construction` — the morphosyntactic indicators of valency, and a
  construction as its exponent together with what each indicator reports;
  `Construction.Mixed` is [evans-et-al-2007]'s mixed transitivity effect.
* `Formation` — lexical vs syntactic formation of reciprocal verbs.
* `Marker` — a reciprocal exponent with its strategy.

## Implementation notes

The strategy fixes the coding site, and the default valency follows from the
site: argument strategies leave the base verb's frame intact, while predicate
and multipredicate strategies realize the denucleativizing reciprocal voice
alternation, whose derived construction is intransitive. The valency a
construction actually shows is read off its indicators one at a time, since
they can disagree: a Kuuk Thaayorre reciprocal can keep ergative on its subject
with no object slot, a Dalabon one takes intransitive agreement yet incorporates
the patient ([evans-et-al-2007]). A construction records only the indicators
a source reports, and a language may override the default: a Tonga verb-marked reciprocal keeps
both reciprocants as arguments, a construction Maslova calls very rare and of somewhat
controversial status ([maslova-2008] (9), p. 230). Hurst's Malagasy case, bivalent at f-structure
and monovalent at c-structure ([hurst-2012]), splits levels rather than indicators and is not
representable here. A bound reciprocal pronoun (Warlpiri *-nyanu*) fills an argument slot and is
an argument strategy. The clitic of a syntactically formed reciprocal verb (French *se*) is not an
object ([siloni-2012]) and marks the predicate, as do German clitic *sich*, the only *sich* with a
reciprocal reading ([gast-haas-2008]), and Wambaya *-ngg-*, which sits in the object position of
the auxiliary but reduces valency ([evans-et-al-2007]).

## TODO

`Strategy` omits the conjunct and modifier strategies of [evans-2008] (§3.3, §3.4). A reciprocal
adverb shows no link to the predicate and does not distribute like an argument, so it has no
`CodingSite`; in European languages it mostly disambiguates a polysemous clitic, as Spanish
*se … mutuamente* and German *sich gegenseitig* do.

## References

* [nordlinger-2023]
* [konig-kokutani-2006]
* [nedjalkov-2007a]
* [nedjalkov-2007b]
* [evans-2008]
* [siloni-2008]
* [siloni-2012]
* [gast-haas-2008]
* [reinhart-siloni-2005]
* [creissels-2024]
* [evans-et-al-2007]
* [maslova-2008]
* [hurst-2012]
-/

@[expose] public section

namespace Reciprocal

/-- Morphosyntactic strategy for encoding reciprocity ([nordlinger-2023]'s
compression of [konig-kokutani-2006], [nedjalkov-2007a], and [evans-2008]). -/
inductive Strategy where
  /-- Bipartite quantifier NP (English *each other*, Icelandic *hvort annað*). -/
  | bipartiteNP
  /-- Free reciprocal pronoun (Hausa *jūnan-mù*, German *einander*). -/
  | recipPronoun
  /-- Bound reciprocal pronoun in the object slot of the pronominal complex (Warlpiri *-nyanu*;
      [evans-2008]). -/
  | boundPronoun
  /-- A clitic that marks the predicate rather than filling an argument slot, though it may sit
      where an object clitic would: French and Czech *se* ([siloni-2012]), German clitic *sich*
      ([gast-haas-2008]), Wambaya *-ngg-* ([evans-et-al-2007]). -/
  | recipClitic
  /-- Verbal affix (Swahili *-an-*, Hungarian *-óz-*). -/
  | verbalAffix
  /-- Reciprocal auxiliary (Warrwa *wanji-* 'exchange', [evans-2008]). -/
  | verbalAuxiliary
  /-- Inherently reciprocal predicate (English *quarrel*, *meet*). -/
  | lexical
  /-- Compound verb (Mandarin *dǎ-lái-dǎ-qù*, [konig-kokutani-2006]). -/
  | compoundVerb
  deriving DecidableEq, Repr

/-- A strategy codes reciprocity in an argument position or on the predicate, the argument- and
predicate-marking strategies of a single clause in [evans-2008] (§3.1, §3.2), or in a fused
multipredicate structure (§4.3). -/
inductive CodingSite where
  /-- A nonsubject argument position, as an NP or a bound pronominal. -/
  | argument
  /-- The predicate: an affix, auxiliary, or clitic, or the lexical entry itself. -/
  | predicate
  /-- A fused multipredicate structure. -/
  | multiclausal
  deriving DecidableEq, Repr

/-- Coding site of each strategy. -/
def Strategy.codingSite : Strategy → CodingSite
  | .bipartiteNP | .recipPronoun | .boundPronoun => .argument
  | .recipClitic | .verbalAffix | .verbalAuxiliary | .lexical => .predicate
  | .compoundVerb => .multiclausal

/-- A nominal strategy marks a nonsubject argument position
([konig-kokutani-2006]). -/
def Strategy.IsNominal (s : Strategy) : Prop := s.codingSite = .argument

instance : DecidablePred Strategy.IsNominal :=
  fun s ↦ inferInstanceAs (Decidable (s.codingSite = .argument))

/-- What a valency indicator reports of a reciprocal construction
([nordlinger-2023]). -/
inductive Valency where
  /-- The base verb's two argument slots preserved. -/
  | bivalent
  /-- The reciprocants form a single subject NP. -/
  | monovalent
  deriving DecidableEq, Fintype, Repr

open Voice in
/-- Every strategy marking the predicate or a multipredicate structure realizes the cumulating
`Voice.reciprocal`; argument strategies leave the frame intact and realize no voice. -/
def Strategy.voice (s : Strategy) : Option Voice :=
  if s.IsNominal then none else some reciprocal

/-- Default valency, derived from the transitivity of the realized voice's derived frame; a
tendency that languages may override ([maslova-2008], [hurst-2012]). -/
def Strategy.defaultValency (s : Strategy) : Valency :=
  match s.voice with
  | some a => if a.derived.IsTransitive then .bivalent else .monovalent
  | none => .bivalent

/-- Nominal strategies preserve valency by default. -/
theorem Strategy.defaultValency_eq_bivalent_iff (s : Strategy) :
    s.defaultValency = .bivalent ↔ s.IsNominal := by
  cases s <;> decide

/-- Predicate-marking strategies reduce valency by default. -/
theorem Strategy.defaultValency_eq_monovalent_iff (s : Strategy) :
    s.defaultValency = .monovalent ↔ ¬ s.IsNominal := by
  cases s <;> decide

/-! ### Valency indicators -/

/-- A morphosyntactic indicator of a clause's valency ([evans-et-al-2007],
[nordlinger-2023]). -/
inductive Indicator where
  /-- A nonsubject argument slot: an object NP or a bound pronominal in the
      object position of the pronominal complex. -/
  | objectSlot
  /-- Case on the subject NP, ergative for a transitive clause. -/
  | subjectCase
  /-- The subject agreement series, transitive or intransitive. -/
  | agreement
  /-- Incorporation of the patient nominal into the verb. -/
  | incorporation
  deriving DecidableEq, Fintype, Repr

/-- Reciprocal verbs are formed in the lexicon, by θ-role bundling, or in the syntax
([siloni-2008], [siloni-2012]; [reinhart-siloni-2005]'s lex-syn parameter). -/
inductive Formation where
  | lexical
  | syntactic
  deriving DecidableEq, Repr

/-! ### Marker inventories -/

/-- A reciprocal marker is an exponent with its strategy. Whether it also expresses the reflexive
meaning is whether its form is one of the language's reflexive exponents. -/
structure Marker where
  /-- The exponent, in surface order, a romanization where the language has a native script. -/
  morphs : List Morphology.Morph
  /-- The spelling in the native script. -/
  script : Option String := none
  /-- Morphosyntactic strategy of the exponent. -/
  strategy : Strategy
  deriving DecidableEq

/-! ### Constructions -/

/-- A reciprocal construction is its exponent together with what each valency indicator a
description reports says of the clause, `none` where nothing is reported. -/
structure Construction where
  /-- The exponent of reciprocity. -/
  marker : Marker
  /-- What each reported indicator says of the clause's valency. -/
  valency : Indicator → Option Valency := fun _ ↦ none

namespace Construction

variable (c : Construction)

/-- The strategy of the construction's exponent. -/
def strategy : Strategy := c.marker.strategy

/-- Some indicator reports the valency `v`. -/
def Reads (v : Valency) : Prop := ∃ i, c.valency i = some v

/-- Every reporting indicator agrees on `v`. -/
def Unanimous (v : Valency) : Prop := ∀ w, c.Reads w → w = v

/-- The indicators disagree, the mixed transitivity effect of [evans-et-al-2007]. -/
def Mixed : Prop := c.Reads .bivalent ∧ c.Reads .monovalent

instance (v : Valency) : Decidable (c.Reads v) := Fintype.decidableExistsFintype
instance (v : Valency) : Decidable (c.Unanimous v) := Fintype.decidableForallFintype
instance : Decidable c.Mixed := instDecidableAnd

theorem not_mixed_of_unanimous {v : Valency} (h : c.Unanimous v) : ¬ c.Mixed :=
  fun ⟨hb, hm⟩ ↦ absurd ((h _ hb).trans (h _ hm).symm) (by decide)

end Construction

end Reciprocal
