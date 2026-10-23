module

public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Set.Insert
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Data.Examples.Haspelmath2025a
public import Linglib.Fragments.Finnish.Morphotactics
public import Linglib.Fragments.Turkish.Morphotactics
public import Linglib.Semantics.Reference.Definiteness
public import Linglib.Syntax.Case.Spatial

/-!
# Haspelmath (2025): Nonverbal Clause Constructions

Haspelmath surveys the clauses that lack a typical verb and fixes a term for each of eight types,
defined by meaning. A duonominal clause puts two nominals in correspondence: it is
classificational when the second nominal is indefinite and equational when it is definite. An
attributional clause ascribes a property. A locopossessional clause is about location or
possession: it is predlocative or appertentive when the nominal that is located or possessed is
definite, and existential or predpossessive when it is indefinite. A hyparctic clause expresses
existence regardless of location. Four of the eight types divide into a subject and a predicate.

Forms are classified by the types they occur in. A copula links the two argument positions of
an equational, ascriptive or locational clause, and an existive is a copula found only in
existential and predpossessive clauses. A strategy is a way of building one type that is
defined by form.

## Main statements

* `Construction.predicational_iff`: the types with a subject and a predicate are the
  classificational, attributional, predlocative and appertentive ones.
* `isExistive_iff`: a form is an existive exactly when it occurs in existential clauses and in
  no clauses but existential and predpossessive ones.
* `existive_gloss_hyparctic`: the Hamar form the paper glosses as an existive occurs in a
  hyparctic clause, which the definition of an existive excludes.
* `finnish_adessive`: the possessor and the location of the Finnish examples are adessives of
  the Finnish fragment, and the adessive is a place case.

## Implementation notes

* The definiteness of the second nominal, and of the located or possessed nominal, is an
  argument of the constructor. The grid of the four locopossessional types then holds by
  construction, and the cover terms are conditions on the arguments.
* A form is represented by the set of constructions it occurs in, so `IsCopula` and
  `IsExistive` are conditions on such a set. That a copula is an overt form is not represented.
* The construction of a row is the type the paper prints with the example, or the type its
  strategy builds.

## TODO

* The rows hold the examples that introduce the types, the duonominal pairs, the strategy
  examples, the Turkish and Spanish examples of the section on copulas, the Mandinka example
  and the hyparctic ones. The paper's other examples are not entered, nor are the subtypes of
  the equational and existential types or the minor predicate types.
* The conditions that define the strategies are not stated over rows. Only the locative flag of
  the Finnish examples is checked, against the fragment.

## References

* [haspelmath-2025a]
* [clark-1978]
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
nominal is definite, the locative phrase or the possessor then being the predicate. -/
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
`S` being the set of constructions the form occurs in. -/
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
  /-- The verb of a transpossessive clause. -/
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

theorem mandinka_general_location : constructions ex57 = [predlocative, existential] := by
  decide +kernel

theorem seychelles_have :
    "have" ∈ ex51.features "boldGloss" ∧ constructions ex51 = [existential] := by
  decide +kernel

theorem existive_gloss : ∀ row ∈ all, "EXV" ∈ row.features "boldGloss" →
    constructions row = [existential] ∨ row = ex66 ∧ constructions row = [hyparctic] := by
  decide +kernel

/-- The Hamar form glossed as an existive occurs in a hyparctic clause, so whatever other clauses
it occurs in, it is not an existive as defined. -/
theorem existive_gloss_hyparctic {S : Set Construction} (h : ∀ t ∈ constructions ex66, t ∈ S) :
    "EXV" ∈ ex66.features "boldGloss" ∧ ¬ IsExistive S :=
  ⟨by decide +kernel, fun hS ↦ hS.hyparctic_notMem (h _ (by decide +kernel))⟩

/-! ### The fragments -/

section Finnish

open Phonology Finnish Finnish.Nominal Subregular.LocalRewrite

/-- The possessor of the locpossessive example and the location of the existent-postposing one
are the adessives of *Pekka* and *katto* in the Finnish fragment, after consonant gradation, and
the adessive is a place case: the locative flag of the locpossessive strategy. -/
theorem finnish_adessive :
    (realize [p, e, k, k, a] [⟨_, .case .ade⟩]).map (derive consonantGradation) =
        (Finnish.ofString? "pekalla").toList ∧
      (realize [k, a, t, t, o] [⟨_, .case .ade⟩]).map (derive consonantGradation) =
        (Finnish.ofString? "katolla").toList ∧
      Finnish.Case.ade.label.dirOf = some .place := by
  decide

end Finnish

section Turkish

open Phonology Turkish Turkish.Phonology

theorem turkish_affixal_copula :
    ofSegmented? "satıcı-y-dı-m" = some (Turkish.realize [s, a, t, ı, c, ı]
      [Verb.Exponent.pastCopula.form,
        (Verb.Exponent.person .one (.personNumber .first .singular)).form]) := by
  decide

end Turkish

end Haspelmath2025a
