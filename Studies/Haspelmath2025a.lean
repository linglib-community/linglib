module

public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Set.Insert
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Data.Examples.Gloss
public import Linglib.Data.Examples.Haspelmath2025a
public import Linglib.Fragments.Finnish.Morphotactics
public import Linglib.Fragments.Turkish.Morphotactics
public import Linglib.Semantics.Reference.Definiteness
public import Linglib.Syntax.Case.Spatial
public import Linglib.Data.Examples.Readers
public import Studies.Heine1997

/-!
# Haspelmath (2025): Nonverbal Clause Constructions

Haspelmath defines by meaning eight types of clause that lack a typical verb, two duonominal, four
locopossessional, the attributional and the hyparctic, and [four of the eight divide into a
subject and a predicate](##predicational_iff). A copula links the argument positions of an
equational, ascriptive or locational clause and an existive is a copula restricted to existential
and predpossessive clauses, so [an existive is a form found in existential clauses and otherwise
only in predpossessive ones](##isExistive_iff). Strategies are defined by form, and [the three
predpossessive strategies the paper names are the forms of Heine's Action, Companion and Location
Schemas](##predpossessiveStrategy?_eq_some_iff).

## Implementation notes

* The definiteness of the second nominal, and of the nominal located or possessed, is an argument
  of the constructor, so the grid of the four locopossessional types holds by construction and the
  cover terms are conditions on the arguments.
* A form is represented by the set of constructions it occurs in as a link, so `IsCopula` and
  `IsExistive` are conditions on such a set; that a copula is overt is not represented. The Hamar
  form printed in bold in two rows is taken to be one form.
* The construction of a row is the type the paper gives the example, or the type its strategy
  builds.
* A predpossessive strategy is read off Heine's formula for a source schema, which gives the
  participant made the subject and the flag of the other.
* The Turkish fragment follows Göksel and Kerslake in taking -(y)DI as the past copular marker,
  its y the buffer consonant after a vowel; the paper, citing Kornfilt, bolds the y alone.

## Errata

* Table 1 places the hyparctic type in neither its predicational nor its nonpredicational row,
  while the abstract and §13 count it among the four nonpredicational types; `Predicational`
  follows the text.
* Table 1 lists three subtypes of the equational type, without the tautotic type that §2 and (12)
  give as the fourth.
* The Hamar form of (61) and (66) is glossed as an existive, but (66) is a hyparctic clause and an
  existive is a copula found in no clauses but existential and predpossessive ones, so [by the
  definitions the form is a copula and not an existive](##hamar_existive).
* Appendix 1 points the characterizational example to (25a) for (35a), the locopossessional entry
  to Table 2 "in §11" for §13, and the presentational entry to n. 13 for n. 16.

## TODO

* The rows hold the examples that introduce the types, the duonominal pairs, the strategy
  examples, the Turkish and Spanish examples of the section on copulas, the Mandinka example, the
  Hamar existential and the hyparctic examples. The paper's other examples are not entered, nor
  are the subtypes of the equational and existential types or the minor predicate types.
* Only the predpossessive strategies are given forms, and only the locative flag of the Finnish
  rows is checked against a fragment.

## References

* [haspelmath-2025a]
* [heine-1997]
* [clark-1978]
* [goksel-kerslake-2005]
* [kornfilt-1997]
-/

@[expose] public section

namespace Haspelmath2025a

/-! ### The eight constructions -/

/-- The two domains of a locopossessional clause. -/
inductive Domain where
  | locational
  | possessional
  deriving DecidableEq, Repr, Fintype

/-- The nonverbal clause constructions. A duonominal clause carries the definiteness of its
second nominal, and a locopossessional clause its domain and the definiteness of the nominal
that is located or possessed. -/
inductive Construction where
  /-- Two nominals in correspondence. -/
  | duonominal (second : Definiteness)
  /-- A property ascribed to the subject, *The bird is small*. -/
  | attributional
  /-- A clause about location or possession, [clark-1978]'s locationals. -/
  | locopossessional (domain : Domain) (d : Definiteness)
  /-- Existence regardless of location, *God exists*. -/
  | hyparctic
  deriving DecidableEq, Repr, Fintype

namespace Construction

/-- A definite subject and an indefinite classificatory nominal, *Lee is a baker*. -/
abbrev classificational : Construction := duonominal .indefinite

/-- Two definite nominals, *Kim is my mother*. -/
abbrev equational : Construction := duonominal .definite

/-- A definite nominal located by a locative phrase, *The bird is on the roof*. -/
abbrev predlocative : Construction := locopossessional .locational .definite

/-- An indefinite nominal said to be in a location, *There is a bird on the roof*. -/
abbrev existential : Construction := locopossessional .locational .indefinite

/-- A definite nominal said to belong to a possessor, *The boat belongs to me*. -/
abbrev appertentive : Construction := locopossessional .possessional .definite

/-- An indefinite nominal said to be possessed, *I have a boat*. -/
abbrev predpossessive : Construction := locopossessional .possessional .indefinite

variable (t : Construction)

/-! ### Cover terms -/

/-- An ascriptive clause ascribes a concept to its subject. -/
def Ascriptive : Prop := t = classificational ∨ t = attributional

/-- A locational clause is about location. -/
def Locational : Prop := ∃ d, t = locopossessional .locational d

/-- A possessional clause is about possession. -/
def Possessional : Prop := ∃ d, t = locopossessional .possessional d

instance : DecidablePred Ascriptive := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

instance : DecidablePred Locational := fun _ ↦ inferInstanceAs (Decidable (∃ _, _))

instance : DecidablePred Possessional := fun _ ↦ inferInstanceAs (Decidable (∃ _, _))

theorem locational_iff : t.Locational ↔ t = predlocative ∨ t = existential := by
  decide +revert

theorem possessional_iff : t.Possessional ↔ t = appertentive ∨ t = predpossessive := by
  decide +revert

/-! ### Predicational clauses -/

/-- A predicational clause divides into a subject and a predicate. A duonominal clause does when
its second nominal is indefinite, and a locopossessional clause when the located or possessed
nominal is definite, the locative phrase or the possessor then being the predicate. The
hyparctic type does not, as the abstract and §13 have it. -/
def Predicational : Construction → Prop
  | duonominal d => d = .indefinite
  | attributional => True
  | locopossessional _ d => d = .definite
  | hyparctic => False

instance : DecidablePred Predicational
  | duonominal _ | locopossessional _ _ => inferInstanceAs (Decidable (_ = _))
  | attributional => .isTrue trivial
  | hyparctic => .isFalse id

/-- The predicational types are the classificational, attributional, predlocative and
appertentive ones; the equational, existential, predpossessive and hyparctic types are not. -/
theorem predicational_iff : t.Predicational ↔
    t = classificational ∨ t = attributional ∨ t = predlocative ∨ t = appertentive := by
  decide +revert

/-! ### The types that define a copula -/

/-- A clause is copular when its type is one of those that define a copula, the equational, the
ascriptive and the locational types. -/
def Copular : Prop := t = equational ∨ t.Ascriptive ∨ t.Locational

instance : DecidablePred Copular := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

theorem copular_iff : t.Copular ↔ t = equational ∨ t = classificational ∨ t = attributional ∨
    t = predlocative ∨ t = existential := by
  decide +revert

variable {t}

theorem Possessional.not_copular (h : t.Possessional) : ¬ t.Copular := by
  decide +revert

end Construction

open Construction

/-! ### Copulas and existives -/

section Forms

variable {S T : Set Construction}

/-- A copula links the two argument positions of an equational, ascriptive or locational clause,
`S` being the set of constructions the form occurs in as a link. -/
def IsCopula (S : Set Construction) : Prop := ∃ t ∈ S, t.Copular

/-- An existive is a copula that occurs in no clauses but existential and predpossessive ones. -/
def IsExistive (S : Set Construction) : Prop := IsCopula S ∧ S ⊆ {existential, predpossessive}

theorem IsCopula.mono (h : S ⊆ T) : IsCopula S → IsCopula T := fun ⟨t, ht, hc⟩ ↦ ⟨t, h ht, hc⟩

theorem not_isCopula_of_possessional (h : ∀ t ∈ S, t.Possessional) : ¬ IsCopula S :=
  fun ⟨t, ht, hc⟩ ↦ (h t ht).not_copular hc

/-- A form is an existive exactly when it occurs in existential clauses and in no clauses but
existential and predpossessive ones, since of the two types only the existential defines a
copula. -/
theorem isExistive_iff : IsExistive S ↔ existential ∈ S ∧ S ⊆ {existential, predpossessive} := by
  refine ⟨fun ⟨⟨t, ht, hc⟩, h⟩ ↦ ⟨?_, h⟩, fun ⟨h, h'⟩ ↦ ⟨⟨_, h, by decide⟩, h'⟩⟩
  rcases h ht with rfl | rfl
  exacts [ht, absurd hc (by decide)]

theorem IsExistive.hyparctic_notMem (h : IsExistive S) : hyparctic ∉ S :=
  fun hm ↦ by simpa using h.2 hm

-- A 'have' found only in predpossessive and existential clauses is an existive, so the
-- transpossessive-existential strategy then uses one.
theorem isExistive_pair : IsExistive {existential, predpossessive} :=
  isExistive_iff.2 ⟨by simp, subset_rfl⟩

end Forms

/-! ### Strategies -/

/-- The strategies the paper names, each a way of building one construction that is defined by
form. -/
inductive Strategy where
  /-- A transitive verb 'have' with the possessor as its subject. -/
  | transpossessive
  /-- A comitative flag on the possessum. -/
  | compossessive
  /-- A locative flag on the possessor. -/
  | locpossessive
  /-- An oblique flag on the possessor. -/
  | obliquePossessor
  /-- A special independent-possessor form. -/
  | independentPossessor
  /-- An existive. -/
  | existiveCopula
  /-- The 'have' verb of a transpossessive clause. -/
  | transpossessiveExistential
  /-- A prolocative form, a short form whose meaning elsewhere is 'here' or 'there'. -/
  | prolocative
  /-- The existent placed after the locative phrase. -/
  | existentPostposing
  deriving DecidableEq, Repr

/-- The construction a strategy builds. -/
def Strategy.construction : Strategy → Construction
  | .transpossessive | .compossessive | .locpossessive => predpossessive
  | .obliquePossessor | .independentPossessor => appertentive
  | .existiveCopula | .transpossessiveExistential | .prolocative | .existentPostposing =>
    existential

/-! ### The predpossessive strategies and Heine's event schemas -/

section Heine

open Heine1997 (Formula Schema)

/-- The predpossessive strategy whose form a [heine-1997] formula has, if it is one the paper
names: a possessor subject with the possessum as its object is transpossessive and with a
comitative possessum compossessive, and a possessum subject with the possessor flagged by a case
of place is locpossessive. -/
def predpossessiveStrategy? (f : Formula) : Option Strategy :=
  match f.subject, f.entry with
  | .possessor, .object => some .transpossessive
  | .possessor, e => if e.case = some .com then some .compossessive else none
  | .possessee, e => if e.case.bind Case.dirOf = some .place then some .locpossessive else none

/-- The three predpossessive strategies the paper names are the forms of three of
[heine-1997]'s event schemas, the transpossessive of the Action Schema, the compossessive of the
Companion Schema and the locpossessive of the Location Schema; the Genitive, Goal, Source, Topic
and Equation Schemas have none of the three forms. -/
theorem predpossessiveStrategy?_eq_some_iff (s : Schema) (σ : Strategy) :
    predpossessiveStrategy? s.formula = some σ ↔ s = .action ∧ σ = .transpossessive ∨
      s = .companion ∧ σ = .compossessive ∨ s = .location ∧ σ = .locpossessive := by
  cases s <;> cases σ <;> decide

end Heine

/-! ### The examples -/

/-- The names of the constructions in the rows. -/
def constructionNames : List (String × Construction) :=
  [("classificational", classificational), ("equational", equational),
    ("attributional", attributional), ("predlocative", predlocative),
    ("existential", existential), ("predpossessive", predpossessive),
    ("appertentive", appertentive), ("hyparctic", hyparctic)]

/-- The names of the strategies in the rows. -/
def strategyNames : List (String × Strategy) :=
  [("transpossessive", .transpossessive), ("compossessive", .compossessive),
    ("locpossessive", .locpossessive), ("oblique-possessor", .obliquePossessor),
    ("independent-possessor", .independentPossessor), ("existive-copula", .existiveCopula),
    ("transpossessive-existential", .transpossessiveExistential),
    ("prolocative", .prolocative), ("existent-postposing", .existentPostposing)]

/-- The constructions of an example are the types the paper prints with it and the type its
strategy builds. -/
def constructions (row : Datum) : List Construction :=
  (row.features "construction").filterMap (List.lookup · constructionNames) ++
    ((row.parse? "strategy" strategyNames).map (·.construction)).toList

/-- A row's bold form has a morph glossed as an existive. -/
def GlossesExistive (row : Datum) : Prop :=
  ∃ g ∈ row.features "boldGloss", "EXV".toList ∈ Gloss.segments g

instance : DecidablePred GlossesExistive := fun _ ↦ inferInstanceAs (Decidable (∃ _ ∈ _, _))

open Examples

theorem labels_parse : ∀ row ∈ all,
    (∀ v ∈ row.features "construction", (List.lookup v constructionNames).isSome) ∧
      ((row.feature? "strategy").isSome → (row.parse? "strategy" strategyNames).isSome) := by
  decide +kernel

theorem english_predicational :
    [ex1, ex2, ex3, ex4, ex5, ex6, ex7].filter (∃ t ∈ constructions ·, t.Predicational) =
      [ex1, ex3, ex4, ex7] := by
  decide +kernel

theorem duonominal_coding :
    ex8a.features "bold" = ex8b.features "bold" ∧ ex9a.features "bold" ≠ ex9b.features "bold" ∧
      ex10a.features "bold" = [] ∧ ex10b.features "bold" ≠ [] := by
  decide +kernel

theorem copula_gloss_copular : ∀ row ∈ all,
    (∃ g ∈ row.features "boldGloss", g = "COP" ∨ g = "LCOP") →
      ∀ t ∈ constructions row, t.Copular := by
  decide +kernel

/-- The Mandinka clause (57) is predlocative or existential as its nominal is read definite or
indefinite, so its types are exactly the locational ones: it is general locational
predication. -/
theorem mandinka_general_location : ∀ t, t ∈ constructions ex57 ↔ t.Locational := by
  decide +kernel

-- The 'have' of the Seychelles Creole existential (51) links an existential clause, so it is a
-- copula whatever else it occurs in; one found only in possessional clauses is not.
theorem seychelles_have {S : Set Construction} (h : ∀ t ∈ constructions ex51, t ∈ S) :
    "have" ∈ ex51.features "boldGloss" ∧ IsCopula S :=
  ⟨by decide +kernel, existential, h _ (by decide +kernel), by decide⟩

theorem existive_gloss : ∀ row ∈ all, GlossesExistive row →
    constructions row = [existential] ∨ row = ex66 ∧ constructions row = [hyparctic] := by
  decide +kernel

/-- The Hamar form the paper glosses as an existive occurs in the existential clause (61) and in
the hyparctic clause (66), so by the paper's definitions it is a copula but not an existive. -/
theorem hamar_existive {S : Set Construction}
    (h : ∀ t ∈ constructions ex61 ++ constructions ex66, t ∈ S) :
    GlossesExistive ex61 ∧ GlossesExistive ex66 ∧ IsCopula S ∧ ¬ IsExistive S :=
  ⟨by decide +kernel, by decide +kernel, ⟨existential, h _ (by decide +kernel), by decide⟩,
    fun hS ↦ hS.hyparctic_notMem (h _ (by decide +kernel))⟩

/-! ### The fragments -/

/-- The segments a glossed word writes, read letter by letter by `ofChar` once its morph
boundaries are dropped and it is lowercased. -/
def spell (ofChar : Char → Option Phonology.Segment) (w : String) :
    Option (List Phonology.Segment) :=
  ((Gloss.segments w).flatten.map Char.toLower).mapM ofChar

section Finnish

open Phonology Finnish Finnish.Nominal Subregular.LocalRewrite

-- The possessor of the locpossessive example (25) and the location of the existent-postposing
-- example (53) are the adessives of *Pekka* and *katto* in the Finnish fragment, after consonant
-- gradation, and the adessive is a case of place, the flag the locpossessive strategy puts on the
-- possessor.
theorem finnish_adessive :
    (realize [p, e, k, k, a] [⟨_, .case .ade⟩]).map (derive consonantGradation) =
        (ex25.surfaceTokens.head?.bind (spell Finnish.ofChar)).toList ∧
      (realize [k, a, t, t, o] [⟨_, .case .ade⟩]).map (derive consonantGradation) =
        (ex53.surfaceTokens.head?.bind (spell Finnish.ofChar)).toList ∧
      Finnish.Case.ade.label.dirOf = some .place := by
  decide

end Finnish

section Turkish

open Phonology Turkish Turkish.Phonology

-- The word of (31) is the fragment's realization of *satıcı* with the past copular marker and
-- the first person singular.
theorem turkish_affixal_copula :
    ex31.surfaceTokens.map (spell ofChar) = [some (Turkish.realize [s, a, t, ı, c, ı]
      [Verb.Exponent.pastCopula.form,
        (Verb.Exponent.person .one (.personNumber .first .singular)).form])] := by
  decide

end Turkish

end Haspelmath2025a
