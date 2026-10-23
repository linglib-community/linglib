module

public import Linglib.Syntax.Minimalist.Category.FunctionalSequence
public import Linglib.Syntax.Voice.Basic
public import Linglib.Fragments.Norwegian.Verbs
public import Linglib.Data.Examples.Dendikken1995

/-!
# den Dikken (1995): Particles

This file formalizes the analysis of verb-particle constructions in chapter 2 of den Dikken's
*Particles*. A particle is an ergative, non-lexical preposition heading a small clause in the
verb's complement, so the "object" of a verb-particle construction originates as the particle's
complement and receives no Case from it. The noun phrase is licensed in one of two ways. It
raises to the specifier of the particle's small clause, where the verb governs it, which gives the
outer order V-NP-Prt; or it stays in situ and receives the verb's Case through reanalysis of verb
and particle, an abstract incorporation that extends the verb's government by Baker's Government
Transparency Corollary, which gives the inner order V-Prt-NP. Reanalysis fails when the particle's
complement is a barrier, a nominal or adjectival small clause, when the noun phrase is a weak
pronoun, and when the particle carries a bare modifier such as *right*; placing the particle after
the predicate of the small clause has no derivation at all. The predicate of that small clause
extracts only across a verb-particle complex, the sole lexical governor of its trace.

Norwegian complex particle constructions pattern exactly as the English ones do, which den
Dikken takes to show that the analysis belongs to the core theory. Languages differ instead in
whether the particle may also incorporate overtly and surface as a prefix on the verb: never in
English, in the passive in Norwegian and Swedish, and in the active as well in Danish. The
chapter's English, Norwegian, Swedish and Danish examples are the rows of `Examples.all`, and
the calculus predicts the judgment of every row it covers.

## Main definitions

* `Complement`: the particle's complement, an object or a small clause headed by a lexical category.
* `Strategy`, `Strategy.placement`: raising, reanalysis and overt incorporation, and the placement
  of the particle each yields.
* `Licensed`, `Derivable`: the strategies a configuration licenses and the placements it derives.
* `PredicateExtractable`, `PredicateExtractableFrom`: extraction of the predicate of the inner
  small clause, by strategy and by placement.
* `Language.incorporates`, `participleContext`: the voices, `Voice.active` or `Voice.passive`,
  in which a language incorporates its particles overtly, Norwegian's read off the contexts
  that take the compound participle in `Norwegian.Verb.participle`.

## Main results

* `derivable_inner_iff`, `derivable_outer`, `not_derivable_final`, `derivable_prefixed_iff`: the
  placements a configuration derives.
* `complex_paradigm`, `weak_pronoun_outer_only`, `modified_outer_only`: the chapter's paradigms.
* `predicateExtractableFrom_iff`: the predicate extracts exactly from a derivable non-outer
  placement.
* `rows_derivable`, `rows_predicateExtraction`, `rows_subextraction`: every English and Norwegian
  row is judged as the calculus predicts.
* `rows_prefixed`: every prefixed particle is judged by the voices its language incorporates in.
* `norwegian_incorporates`: Norwegian incorporates in the passive only, as the chapter states.
* `rows_participle`: Åfarli's *sparke ut* rows show the participle the fragment gives for their
  auxiliary exactly when they are judged acceptable.

## Implementation notes

The calculus is stated over the parameters the chapter's principles read, not over trees: the
particle's complement, with the infinitival marker *to* counted prepositional; whether the object
is a weak pronoun; whether the particle carries a bare modifier; and whether overt incorporation
is available. Overt incorporation is the third strategy, licensed by the language and the voice
alone, and the extracted predicate's trace is taken to be governed by the overtly incorporated
complex as by the reanalysed one, a point the chapter has no data on. Danish has no inner order,
which the chapter records without deriving, so the Danish rows enter only `rows_prefixed`. The
Norwegian prefixed forms, *utsparka* after *vart* and not after *har*, are the compound
participles of the reference grammar, which puts them after *være* and *bli* and not after *ha*
whatever the voice, so the voices Norwegian incorporates in are read off the fragment through
the auxiliary each voice has in the rows, and the *sparke ut* rows are checked against the forms
the fragment conjugates. The Bokmål rows were constructed and judged by Arnfinn
Vonen and Alma Næss for den Dikken; the Nynorsk rows are Åfarli's. The arguments from
small-clause constituency, from verb-particle idioms and from the ergativity of the particle,
and Herslund's observation that Danish incorporation is lexically conditioned, are recorded in
the rows and not formalized.

## References

* [dendikken-1995]
* [afarli-1985]
* [herslund-1984]
* [faarlund-lie-vannebo-1997]
* [baker-1988]
* [burzio-1986]
* [kayne-1984]
* [kayne-1985]
* [johnson-1991]
-/

@[expose] public section

namespace Dendikken1995

open Minimalist

/-- The particle's complement is the object of a simplex construction or the inner small clause
of a complex one, whose predicate is headed by the given lexical category; the infinitival marker
*to* counts as prepositional, (58). -/
inductive Complement
  /-- The object NP of a simplex particle construction. -/
  | np
  /-- The inner small clause of a complex particle construction. -/
  | sc (pred : CatFamily)
  deriving DecidableEq

/-- A particle is a non-lexical preposition and does not L-mark its complement, so a small
clause complement is a barrier unless its head is categorially non-distinct from the particle,
(59). -/
def Complement.IsBarrier : Complement → Prop
  | .np => False
  | .sc c => c ≠ .adpositional

instance : DecidablePred Complement.IsBarrier
  | .np => inferInstanceAs (Decidable False)
  | .sc c => inferInstanceAs (Decidable (c ≠ .adpositional))

/-- A strategy licenses the noun phrase in the particle's complement and places the particle.
Raising moves the noun phrase to the specifier of the particle's small clause, where the verb
governs it, (48); reanalysis of verb and particle transmits the verb's Case to the noun phrase in
situ, (57); overt incorporation adjoins the particle to the verb in the syntax, which English
lacks and the Scandinavian languages have in some voices. -/
inductive Strategy
  | raising
  | reanalysis
  | incorporation
  deriving DecidableEq

/-- The surface position of the particle relative to the noun phrase and to the predicate of
the inner small clause. -/
inductive Placement
  /-- V-Prt-NP(-Pred), the "inner particle" order. -/
  | inner
  /-- V-NP-Prt(-Pred), the "outer particle" order. -/
  | outer
  /-- V-NP-Pred-Prt. -/
  | final
  /-- Prt-V, the particle a prefix on the verb. -/
  | prefixed
  deriving DecidableEq

/-- A raised noun phrase precedes the particle, an in-situ one follows it, and an overtly
incorporated particle precedes the verb. No strategy places the particle after the predicate of
the inner small clause, since small clauses do not move, heads do not adjoin to maximal
projections, and adjoining the predicate would leave the trace of the noun phrase improperly
bound. -/
def Strategy.placement : Strategy → Placement
  | .raising => .outer
  | .reanalysis => .inner
  | .incorporation => .prefixed

section Licensing

variable (k : Complement) (overt weak modified : Prop)

/-- A strategy is licensed in a configuration. Raising always is. Reanalysis transmits the
verb's Case along the incorporation chain, which requires that the particle's complement not be
a barrier, (59), that the noun phrase not be a weak pronoun, which must agree directly with an
Agr head, (163), and that the particle carry no bare modifier, which incorporation cannot
strand, (169). Overt incorporation is licensed where the language has it. -/
def Licensed : Strategy → Prop
  | .raising => True
  | .reanalysis => ¬ k.IsBarrier ∧ ¬ weak ∧ ¬ modified
  | .incorporation => overt

/-- A placement is derivable when a licensed strategy yields it; by Economy the derivation uses
exactly one strategy. -/
def Derivable (p : Placement) : Prop := ∃ s, Licensed k overt weak modified s ∧ s.placement = p

variable {overt weak modified}

theorem derivable_outer : Derivable k overt weak modified .outer := ⟨.raising, trivial, rfl⟩

theorem derivable_inner_iff :
    Derivable k overt weak modified .inner ↔ ¬ k.IsBarrier ∧ ¬ weak ∧ ¬ modified :=
  ⟨fun ⟨s, hs, hp⟩ ↦ by cases s <;> simp_all [Strategy.placement, Licensed],
    fun h ↦ ⟨.reanalysis, h, rfl⟩⟩

theorem not_derivable_final : ¬ Derivable k overt weak modified .final :=
  fun ⟨s, _, hp⟩ ↦ by cases s <;> cases hp

theorem derivable_prefixed_iff : Derivable k overt weak modified .prefixed ↔ overt :=
  ⟨fun ⟨s, hs, hp⟩ ↦ by cases s <;> simp_all [Strategy.placement, Licensed],
    fun h ↦ ⟨.incorporation, h, rfl⟩⟩

variable [Decidable overt] [Decidable weak] [Decidable modified]

instance : DecidablePred (Licensed k overt weak modified)
  | .raising => inferInstanceAs (Decidable True)
  | .reanalysis => inferInstanceAs (Decidable (¬ k.IsBarrier ∧ ¬ weak ∧ ¬ modified))
  | .incorporation => inferInstanceAs (Decidable overt)

instance : DecidablePred (Derivable k overt weak modified)
  | .inner => decidable_of_iff _ (derivable_inner_iff k).symm
  | .outer => isTrue (derivable_outer k)
  | .final => isFalse (not_derivable_final k)
  | .prefixed => decidable_of_iff _ (derivable_prefixed_iff k).symm

end Licensing

/-! ### The English paradigms -/

/-- In (49)–(53), nominal and adjectival complex particle constructions have the outer order
only, prepositional and infinitival ones both, and none the clause-final order. -/
theorem complex_paradigm (overt : Prop) (c : CatFamily) :
    Derivable (.sc c) overt False False .outer ∧
      (Derivable (.sc c) overt False False .inner ↔ c = .adpositional) ∧
      ¬ Derivable (.sc c) overt False False .final :=
  ⟨derivable_outer _, by rw [derivable_inner_iff]; simp [Complement.IsBarrier],
    not_derivable_final _⟩

/-- In (155), a simplex construction has both orders with a full noun phrase, but *look up it*
has no derivation, since a weak pronoun cannot be Case-marked through the reanalysis chain; a
stressed, conjoined or deictic pronoun is not weak and patterns with full noun phrases, (156). -/
theorem weak_pronoun_outer_only (overt : Prop) :
    Derivable .np overt False False .inner ∧ Derivable .np overt True False .outer ∧
      ¬ Derivable .np overt True False .inner :=
  ⟨(derivable_inner_iff _).2 (by simp [Complement.IsBarrier]), derivable_outer _,
    fun h ↦ ((derivable_inner_iff _).1 h).2.1 trivial⟩

/-- In (161) and (162), the ban on weak pronouns carries over to the inner order of
prepositional and infinitival complex constructions, where the same reanalysis licenses the
in-situ noun phrase. -/
theorem weak_pronoun_complex (overt : Prop) :
    ¬ Derivable (.sc .adpositional) overt True False .inner :=
  fun h ↦ ((derivable_inner_iff _).1 h).2.1 trivial

/-- In (167), *look the information right up* is derivable and *look right up the information*
is not, (169), the modified particle being unable to incorporate. -/
theorem modified_outer_only (overt : Prop) :
    Derivable .np overt False True .outer ∧ ¬ Derivable .np overt False True .inner :=
  ⟨derivable_outer _, fun h ↦ ((derivable_inner_iff _).1 h).2.2 trivial⟩

/-! ### Extraction of the predicate of the inner small clause -/

/-- By (66), the trace of an extracted predicate of the inner small clause is lexically
governed, as the ECP demands, only by a verb-particle complex, reanalysed or overtly
incorporated, since the particle itself is not a lexical governor; subextraction from the
predicate is governed by the predicate's own head and always possible, (61), (63) and (65). -/
def PredicateExtractable : Strategy → Prop
  | .raising => False
  | .reanalysis => True
  | .incorporation => True

instance : DecidablePred PredicateExtractable
  | .raising => inferInstanceAs (Decidable False)
  | .reanalysis => inferInstanceAs (Decidable True)
  | .incorporation => inferInstanceAs (Decidable True)

section Extraction

variable (k : Complement) {overt weak modified : Prop}

/-- In a nominal complex particle construction of a language without overt incorporation, (60),
the predicate cannot be extracted whatever the surface position of the particle, since no
licensed derivation forms a verb-particle complex. -/
theorem not_predicateExtractable_of_isBarrier (hk : k.IsBarrier) {s : Strategy}
    (hs : Licensed k overt weak modified s) (ho : ¬ overt) : ¬ PredicateExtractable s := by
  cases s
  · exact id
  · exact fun _ ↦ hs.1 hk
  · exact fun _ ↦ ho hs

/-- The predicate is extractable from a placement when a licensed strategy yields the placement
and leaves the trace governed. -/
def PredicateExtractableFrom (overt weak modified : Prop) (p : Placement) : Prop :=
  ∃ s, Licensed k overt weak modified s ∧ s.placement = p ∧ PredicateExtractable s

/-- By (67), the predicate extracts exactly from a derivable placement other than the outer
one, which only raising yields. Verb-adjacent placement in a prepositional construction renders
the predicate extractable, (62a) and (64a), and the outer order does not, (62b) and (64b). -/
theorem predicateExtractableFrom_iff (p : Placement) :
    PredicateExtractableFrom k overt weak modified p ↔
      Derivable k overt weak modified p ∧ p ≠ .outer := by
  constructor
  · rintro ⟨s, hs, rfl, he⟩
    exact ⟨⟨s, hs, rfl⟩, by cases s <;> simp_all [Strategy.placement, PredicateExtractable]⟩
  · rintro ⟨⟨s, hs, rfl⟩, hp⟩
    exact ⟨s, hs, rfl, by cases s <;> simp_all [Strategy.placement, PredicateExtractable]⟩

instance [Decidable overt] [Decidable weak] [Decidable modified] :
    DecidablePred (PredicateExtractableFrom k overt weak modified) :=
  fun p ↦ decidable_of_iff _ (predicateExtractableFrom_iff k p).symm

end Extraction

/-! ### Overt incorporation across languages -/

/-- The languages of the chapter's particle data. -/
inductive Language
  | english
  | norwegian
  | swedish
  | danish
  deriving DecidableEq

/-- The context of the participle in a Norwegian row of a voice: the passive rows have *bli*
or *verte*, the active ones the perfect with *ha*. -/
def participleContext (v : Voice) : Norwegian.ParticipleContext :=
  if v = Voice.passive then .copular else .perfect

/-- The voices in which a language incorporates its particle overtly into the verb. English
never does, (133); Norwegian does where the reference grammar puts the compound participle,
after *bli* and *verte* and not after *ha*, (134)–(135), Swedish in the passive, (136), and
Danish in the active as well, (138). -/
def Language.incorporates : Language → Set Voice
  | .english => ∅
  | .norwegian => {v | (participleContext v).IsCompound}
  | .swedish => {Voice.passive}
  | .danish => Set.univ

instance : ∀ L : Language, DecidablePred (· ∈ L.incorporates)
  | .english => fun _ ↦ isFalse fun h ↦ h
  | .norwegian => fun v ↦ inferInstanceAs (Decidable (participleContext v).IsCompound)
  | .swedish => fun v ↦ inferInstanceAs (Decidable (v = Voice.passive))
  | .danish => fun _ ↦ isTrue trivial

theorem norwegian_incorporates : Language.incorporates .norwegian = {Voice.passive} := by
  ext v
  by_cases h : v = Voice.passive <;>
    simp [Language.incorporates, participleContext, Norwegian.ParticipleContext.IsCompound, h]

/-! ### The rows -/

/-- The language of a row; both written standards of Norwegian, Bokmål and Nynorsk, count as
Norwegian. -/
def languageOf (r : Datum) : Option Language :=
  match r.language with
  | "stan1293" => some .english
  | "norw1259" | "norw1262" => some .norwegian
  | "swed1254" => some .swedish
  | "dani1285" => some .danish
  | _ => none

/-- The particle's complement as a row's `construction` and `predicate` features record it. -/
def complementOf (r : Datum) : Option Complement :=
  match r.feature? "construction", r.feature? "predicate" with
  | some "simplex", _ => some .np
  | some "complex", some "nominal" => some (.sc .nominal)
  | some "complex", some "adjectival" => some (.sc .adjectival)
  | some "complex", some "prepositional" => some (.sc .adpositional)
  | some "complex", some "infinitival" => some (.sc .adpositional)
  | _, _ => none

/-- The particle's placement as a row's `placement` feature records it. -/
def placementOf (r : Datum) : Option Placement :=
  r.parse? "placement"
    [("inner", .inner), ("outer", .outer), ("final", .final), ("prefixed", .prefixed)]

/-- The voice of a row's clause, active unless its `voice` feature says passive. -/
def voiceOf (r : Datum) : Voice :=
  if r.feature? "voice" = some "passive" then Voice.passive else Voice.active

/-- The row's object is a weak pronoun. -/
def Weak (r : Datum) : Prop := r.feature? "object" = some "pronoun"

/-- The row's particle carries a bare modifier. -/
def Modified (r : Datum) : Prop := r.feature? "modifier" = some "right"

instance (r : Datum) : Decidable (Weak r) := inferInstanceAs (Decidable (_ = _))
instance (r : Datum) : Decidable (Modified r) := inferInstanceAs (Decidable (_ = _))

/-- Every English and Norwegian row of the placement paradigms is judged acceptable exactly
when the calculus derives its placement; the Norwegian rows (70), (73) and (134) pattern with
the English ones. Danish, whose lack of the inner order (137b) the chapter records without
deriving, is left out. -/
theorem rows_derivable :
    ∀ r ∈ Examples.all, r.feature? "diagnostic" = none → r.language ≠ "dani1285" →
      ∀ k ∈ complementOf r, ∀ p ∈ placementOf r, ∀ L ∈ languageOf r,
        (r.judgment = .acceptable ↔
          Derivable k (voiceOf r ∈ L.incorporates) (Weak r) (Modified r) p) := by
  decide +kernel

/-- Every row testing extraction of the predicate of the inner small clause, English (60), (62)
and (64) and Norwegian (71) and (74), is judged acceptable exactly when the predicate is
extractable from its placement. -/
theorem rows_predicateExtraction :
    ∀ r ∈ Examples.all, r.feature? "diagnostic" = some "predicateExtraction" →
      ∀ k ∈ complementOf r, ∀ p ∈ placementOf r, ∀ L ∈ languageOf r,
        (r.judgment = .acceptable ↔
          PredicateExtractableFrom k (voiceOf r ∈ L.incorporates) (Weak r) (Modified r)
            p) := by
  decide +kernel

/-- Every row testing subextraction from the predicate of the inner small clause, English (61),
(63) and (65) and Norwegian (72) and (75), is acceptable whatever the particle's position;
subextraction from the subject of a small clause, (13), is not. -/
theorem rows_subextraction :
    ∀ r ∈ Examples.all, r.feature? "diagnostic" = some "subextraction" →
      (placementOf r).isSome → r.judgment = .acceptable := by
  decide +kernel

/-- Every row with the particle prefixed to the verb, Norwegian (134) and (135), Swedish (136)
and Danish (138), is judged acceptable exactly when its language incorporates overtly in its
voice. -/
theorem rows_prefixed :
    ∀ r ∈ Examples.all, placementOf r = some .prefixed →
      ∀ L ∈ languageOf r,
        (r.judgment = .acceptable ↔ voiceOf r ∈ L.incorporates) := by
  decide +kernel

/-- The fragment's verb of a row of Åfarli's (134a) and (135a), Nynorsk *sparke ut*. The rows
of (134b) and (134c) have none: the grammar's lists do not place *klippe*, and the book spells
Åfarli's *køyrt* as Bokmål *kjørt*. -/
def verbOf (r : Datum) : Option Norwegian.Verb :=
  match r.reportedIn with
  | some ⟨_, "(134a)"⟩ | some ⟨_, "(135a)"⟩ => some Norwegian.Verbs.Nynorsk.sparkeUt
  | _ => none

theorem rows_participle :
    ∀ r ∈ Examples.all, ∀ v ∈ verbOf r, placementOf r ≠ some .outer →
      (r.judgment = .acceptable ↔
        (v.participle (participleContext (voiceOf r))).toList <:+: r.primaryText.toList) := by
  decide +kernel

end Dendikken1995
