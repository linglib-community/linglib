module

public import Linglib.Data.WALS.Features.F115A
public import Linglib.Data.Examples.VanDerAuweraVanAlsenoy2016
public import Mathlib.Order.Basic
public import Mathlib.Data.Fintype.Prod
public import Linglib.Syntax.Clause.Basic

/-!
# van der Auwera and Van Alsenoy (2016): On the Typology of Negative Concord

This file formalizes [van-der-auwera-van-alsenoy-2016], a typology of negative concord, a
semantically single negation expressed both by a clausal negator and by a negative indefinite,
(1), over a variety sample of 179 languages. A negative indefinite is an indefinite whose dominant
use is negation, as against a negatively polar or a neutral indefinite, `Indefinite`, and a
language's way of negating with an indefinite is one of Kahrel's five strategies,
`Strategy`. The paper's first claim is that negative concord is not frequent: the impression that
it is rests on [haspelmath-1997]'s deliberately wide notion of negative indefinite, so that the
co-occurrence value of WALS 115A, [haspelmath-2013], covers the neutral and polar strategies as
well as concord, `toWALS`, `toWALS_eq_predicateNegationAlsoPresent_iff`. The second claim is that
strict concord is far more frequent than non-strict, and that non-strict concord is not one
pattern but many. A concord system records, for a negative indefinite before and after the finite
verb, whether the clausal negator is absent, optional or obligatory, or the position unavailable,
`System`, the paper's formulas (19), (26), (28), (30), (32), (36), (38), (39): strict
concord is obligatory marking in both positions, `IsStrict`, and non-strict concord is concord
that is not strict, `IsNonStrict`. [jespersen-1917]'s Negative Early principle, that the clausal
negator appears first where the negative indefinite comes late, orders the two positions,
`NegativeEarly`, and the four subtypes of Table 9 are exactly the non-strict systems with both
positions available that respect it, `nonStrict_negativeEarly_iff`. The diachrony of Table 6 from
Latin to modern Slavic is a chain on the strictness scale, `stages_isChain`, each stage respecting
Negative Early, `negativeEarly_of_mem_stages`, whereas Catalan moves from strict to the Spanish
subtype, the other way along the scale, `informalCatalan_lt_formalCatalan`.

## Implementation notes

The strictness scale orders the markings excluded, optional, obligatory, and a system is a pair of
optional markings, the asterisk of the paper's formulas being `none`; Georgian's immediate
precedence, (36), Welsh's compound verbs, (43), and Yiddish's emphatic omission, (45), are
recorded as rows, since they parametrize concord by something other than the position relative
to the finite verb. The frequencies of Tables 1 to 3, the areal distribution, and the
morpho-syntactic composition of Table 4 are reported in the paper and not formalized. The
examples are the rows of `Data.Examples.VanDerAuweraVanAlsenoy2016`.

## References

* [van-der-auwera-van-alsenoy-2016]
* [haspelmath-1997]
* [haspelmath-2013]
* [kahrel-1996]
* [giannakidou-1998]
* [jespersen-1917]
* [de-swart-2010]
-/

@[expose] public section

namespace VanDerAuweraVanAlsenoy2016

open Data.WALS

/-! ### Indefinites and strategies -/

/-- The indefinite used in a negative clause, by its dominant use: neutral, at home in positive
and negative contexts alike, negatively polar, licensed by negation among other contexts, or
negative, used predominantly for negation. -/
inductive Indefinite where
  | neutral
  | negativelyPolar
  | negative
  deriving DecidableEq, Repr

/-- [kahrel-1996]'s strategies for a single negation with an indefinite, Table 1: a verbal negator
with a neutral or a negatively polar indefinite, a negative indefinite alone, negative concord,
and another construction such as a negative existential. -/
inductive Strategy where
  | verbalNegatorNeutral
  | verbalNegatorPolar
  | negativeIndefiniteAlone
  | concord
  | other
  deriving DecidableEq, Repr, Fintype

/-- The indefinite each strategy uses, if any. -/
def Strategy.indefinite : Strategy → Option Indefinite
  | .verbalNegatorNeutral => some .neutral
  | .verbalNegatorPolar => some .negativelyPolar
  | .negativeIndefiniteAlone | .concord => some .negative
  | .other => none

/-- The WALS 115A value a strategy falls under: [haspelmath-2013]'s co-occurrence of predicate
negation with a negative indefinite, in the wide sense of [haspelmath-1997], covers every
strategy with a verbal negator. -/
def Strategy.toWALS : Strategy → F115A.NegativeIndefiniteType
  | .verbalNegatorNeutral | .verbalNegatorPolar | .concord => .predicateNegationAlsoPresent
  | .negativeIndefiniteAlone => .noPredicateNegation
  | .other => .negativeExistentialConstruction

theorem toWALS_eq_predicateNegationAlsoPresent_iff (s : Strategy) :
    s.toWALS = .predicateNegationAlsoPresent ↔
      s = .verbalNegatorNeutral ∨ s = .verbalNegatorPolar ∨ s = .concord := by
  cases s <;> simp [Strategy.toWALS]

/-! ### Strict and non-strict negative concord -/

/-- A negative concord system: whether the clausal negator accompanies a preverbal and a
postverbal negative indefinite, excluded (the formula V), optional ((N) V) or obligatory (N V),
ordered as the strictness scale, and `none` when the position is unavailable, the asterisk of the
formulas. -/
structure System where
  preverbal : Option Clause.Occurrence
  postverbal : Option Clause.Occurrence
  deriving DecidableEq, Repr

/-- A pattern with both positions available, the systems of Tables 6 and 9. -/
abbrev Pattern := Clause.Occurrence × Clause.Occurrence

/-- The system of a pattern. -/
def Pattern.toSystem (p : Pattern) : System := ⟨some p.1, some p.2⟩

/-- Concord is available in some construction. -/
def System.HasConcord (s : System) : Prop :=
  (∃ m, s.preverbal = some m ∧ m ≠ .excluded) ∨ (∃ m, s.postverbal = some m ∧ m ≠ .excluded)

/-- Strict negative concord: the clausal negator is obligatory whatever the position of the
negative indefinite, (14). -/
def System.IsStrict (s : System) : Prop :=
  s.preverbal = some .obligatory ∧ s.postverbal = some .obligatory

/-- Non-strict negative concord: concord in some construction but not in all, (15). -/
def System.IsNonStrict (s : System) : Prop := s.HasConcord ∧ ¬ s.IsStrict

instance (s : System) : Decidable s.HasConcord := by unfold System.HasConcord; infer_instance
instance (s : System) : Decidable s.IsStrict := by unfold System.IsStrict; infer_instance
instance (s : System) : Decidable s.IsNonStrict := by unfold System.IsNonStrict; infer_instance

theorem System.IsStrict.hasConcord {s : System} (h : s.IsStrict) : s.HasConcord :=
  Or.inl ⟨.obligatory, h.1, by decide⟩

/-- The Negative Early principle: a postverbal negative indefinite, which leaves the negation
late, calls for the clausal negator at least as much as a preverbal one. -/
def Pattern.NegativeEarly (p : Pattern) : Prop := p.1 ≤ p.2

instance : DecidablePred Pattern.NegativeEarly := λ p => inferInstanceAs (Decidable (p.1 ≤ p.2))

/-- (19): the Spanish subtype, no negator with a preverbal negative indefinite and an obligatory
one with a postverbal one. -/
def spanish : Pattern := (.excluded, .obligatory)

/-- (30): Belgian Brabantic Dutch, an optional negator with a postverbal negative indefinite. -/
def brabanticDutch : Pattern := (.excluded, .optional)

/-- (32): French and African American English, the negator optional in both positions. -/
def french : Pattern := (.optional, .optional)

/-- (28): older Slavic and Catalan, the negator optional preverbally and obligatory
postverbally. -/
def olderSlavic : Pattern := (.optional, .obligatory)

/-- Table 9: the non-strict subtypes with both positions available. -/
def nonStrictSubtypes : List Pattern := [brabanticDutch, french, spanish, olderSlavic]

/-- Table 9 is exactly the non-strict patterns respecting Negative Early. -/
theorem nonStrict_negativeEarly_iff (p : Pattern) :
    p.toSystem.IsNonStrict ∧ p.NegativeEarly ↔ p ∈ nonStrictSubtypes := by
  revert p
  decide

/-- Table 6: the diachrony from Latin, with negative indefinites alone, through older Romance,
Spanish and older Slavic to modern Slavic and Romanian, with strict concord. -/
def stages : List Pattern :=
  [(.excluded, .excluded), (.excluded, .optional), spanish, olderSlavic, (.obligatory, .obligatory)]

theorem stages_isChain : stages.IsChain (· ≤ ·) := by decide

theorem negativeEarly_of_mem_stages : ∀ p ∈ stages, p.NegativeEarly := by decide

/-- (29): informal Catalan has the Spanish subtype, formal Catalan strict concord. -/
def informalCatalan : Pattern := spanish

def formalCatalan : Pattern := (.obligatory, .obligatory)

theorem informalCatalan_lt_formalCatalan :
    informalCatalan ≤ formalCatalan ∧ informalCatalan ≠ formalCatalan := by decide

/-! ### Systems with an unavailable position -/

/-- (26): Icelandic *neinn*, no preverbal position and obligatory concord postverbally. -/
def icelandic : System := ⟨none, some .obligatory⟩

/-- (39): Welsh, no preverbal position and optional concord postverbally. -/
def welsh : System := ⟨none, some .optional⟩

/-- (38): Western Armenian, optional concord preverbally and no postverbal position. -/
def westernArmenian : System := ⟨some .optional, none⟩

/-- Table 8: the subtypes with one position unavailable are non-strict, concord depending on
word order even where it is obligatory. -/
theorem isNonStrict_table8 :
    icelandic.IsNonStrict ∧ welsh.IsNonStrict ∧ westernArmenian.IsNonStrict := by
  decide

end VanDerAuweraVanAlsenoy2016
