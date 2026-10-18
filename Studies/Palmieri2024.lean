module

public import Linglib.Syntax.Reciprocal
public import Linglib.Semantics.Plurality.Reciprocal
public import Studies.Siloni2012
public import Studies.Winter2018
public import Linglib.Fragments.Romance.Portuguese.Verbs
public import Linglib.Fragments.Romance.Catalan.Verbs
public import Linglib.Fragments.Romance.Italian.Verbs
public import Linglib.Fragments.Romance.Spanish.Verbs
public import Linglib.Fragments.Swahili.Verbs

/-!
# Palmieri (2024): Lexical and Grammatical Reciprocity

This file formalizes the second chapter of Palmieri's thesis, on lexical reciprocity in
Romance. Against Siloni's (2012) language-level parameter, on which Romance forms its
reciprocals in the syntax, verbs fall into three classes by the entries they carry: reciprocal
intransitives with a lexical reciprocal entry only, plain transitives with a transitive entry
only, and verbs like 'hug' with both, whose reciprocal reading requires *se* in most
environments but emerges without it in language-specific ones, Brazilian Portuguese finite
clauses, analytic causatives everywhere, and Spanish and Catalan absolute participials
(`VerbClass.formations`, `SeOmissible`). The columns of Table 2.1 follow from the entries: a
class combines with *se* iff it has a transitive entry and expresses reciprocity by itself
iff it has a lexical one (`table21`, `romance_not_monolithic`). The readings follow too: with
*se* the transitive entry contributes the grammatical reciprocal and reflexive readings and
the lexical entry its pseudo-reciprocal reading, so a class-3 *se*-clause is three-ways
ambiguous, and without *se* only the lexical entry contributes, so the grammatical readings
disappear and the pseudo-reciprocal reading survives exactly for the classes with a lexical
entry (`grammatical_needs_se`, `pseudo_without_se_iff`). A Romance lexical reciprocal is a
verb with some construction in which a reciprocal interpretation emerges without *se*, the
chapter's definition (44), which is having a lexical entry, in every language
(`lexicalReciprocalIn_iff`). Grammatical reciprocity is Strong Reciprocity of the binary
relation, *x and y kissed each other* being *x kissed y and y kissed x* (50), and so plain in
Winter's (2018) sense for any relation (`strongReciprocity_plainReciprocity`), whereas the
collective predicate of a lexical entry is not so constrained, 'divorce' and 'kiss' failing one
direction each (53), (54). The reciprocal 'with'-construction tracks the lexical entry,
Kemmer's (1993) generalization, including non-symmetric members and the *si*-retaining Italian
cases that refine Siloni's French-based restriction (`withConstruction_iff_lexical`).

## Implementation notes

The entries are primitive and the class tables derived. Appendix A's verbs are entries of the
Romance Fragments (`appendixA`), and Appendix C pairs the Swahili lexical reciprocals of the
fourth chapter with their bases (`appendixC`), from which one theorem records that lexical
reciprocity need not be derivational. The Swahili chapters and the questionnaires are not
otherwise formalized.

## References

* [palmieri-2024]
* [siloni-2012]
* [winter-2018]
* [kemmer-1993]
-/

@[expose] public section

namespace Palmieri2024

open Reciprocal

/-! ### The verb classes and their entries (Table 2.1) -/

/-- Romance verbs fall into three classes, those like 'chat', with no transitive entry (31),
those like 'describe', unambiguously transitive (32), and those like 'hug', transitive with a
lexical reciprocal entry besides (34), (38), (40), (42). -/
inductive VerbClass where
  | reciprocalIntransitive
  | plainTransitive
  | reciprocalTransitive
  deriving DecidableEq

/-- The entries a class carries, the two-entry proposal: a lexical reciprocal entry, a
transitive entry fed by the grammatical *se* strategy, or both. -/
def VerbClass.formations : VerbClass → List Formation
  | .reciprocalIntransitive => [.lexical]
  | .plainTransitive => [.syntactic]
  | .reciprocalTransitive => [.lexical, .syntactic]

/-- By the first column of Table 2.1, a class combines with *se* iff it has a transitive
entry. -/
def VerbClass.CombinesWithSe (c : VerbClass) : Prop := Formation.syntactic ∈ c.formations

/-- By the second column of Table 2.1, a class expresses reciprocity by itself iff it has a
lexical entry. -/
def VerbClass.ReciprocityByItself (c : VerbClass) : Prop := Formation.lexical ∈ c.formations

instance : DecidablePred VerbClass.CombinesWithSe :=
  fun c ↦ inferInstanceAs (Decidable (Formation.syntactic ∈ c.formations))

instance : DecidablePred VerbClass.ReciprocityByItself :=
  fun c ↦ inferInstanceAs (Decidable (Formation.lexical ∈ c.formations))

/-- In Table 2.1 as printed, the intransitives express reciprocity by themselves and reject
*se*, the plain transitives the reverse, and the third class both. -/
theorem table21 :
    (¬ VerbClass.reciprocalIntransitive.CombinesWithSe ∧
        VerbClass.reciprocalIntransitive.ReciprocityByItself) ∧
      (VerbClass.plainTransitive.CombinesWithSe ∧
        ¬ VerbClass.plainTransitive.ReciprocityByItself) ∧
      (VerbClass.reciprocalTransitive.CombinesWithSe ∧
        VerbClass.reciprocalTransitive.ReciprocityByItself) := by
  decide

/-! ### The *se*-less environments (Table 2.2) -/

/-- The four Romance languages of the chapter. -/
inductive Language where
  | brazilianPortuguese
  | italian
  | spanish
  | catalan
  deriving DecidableEq

/-- The constructions in which a class-3 verb may express reciprocity without *se* (§3):
finite clauses (34), analytic causatives (38), (40), and absolute participials (42). -/
inductive Environment where
  | finiteClause
  | analyticCausative
  | absoluteParticipial
  deriving DecidableEq

/-- Table 2.2 records whether the language lets a class-3 verb receive a reciprocal
interpretation without *se* in the environment. -/
def SeOmissible : Language → Environment → Prop
  | .brazilianPortuguese, .absoluteParticipial => False
  | .brazilianPortuguese, _ => True
  | .italian, .analyticCausative => True
  | .italian, _ => False
  | .spanish, .finiteClause => False
  | .spanish, _ => True
  | .catalan, .finiteClause => False
  | .catalan, _ => True

instance : ∀ (l : Language) (e : Environment), Decidable (SeOmissible l e) := by
  intro l e; cases l <;> cases e <;> unfold SeOmissible <;> infer_instance

/-- Analytic causatives are the pan-Romance diagnostic: every language omits *se* there. -/
theorem every_language_diagnosable (l : Language) : SeOmissible l .analyticCausative := by
  cases l <;> decide

/-- The verbs of Appendix A, class 3 verbs with a lexical reciprocal entry beside their
transitive one. -/
def appendixA : Language → List Verb
  | .brazilianPortuguese =>
      [Portuguese.Verbs.abracar, Portuguese.Verbs.beijar, Portuguese.Verbs.casar,
        Portuguese.Verbs.consultar, Portuguese.Verbs.cumprimentar, Portuguese.Verbs.encontrar,
        Portuguese.Verbs.namorar]
  | .italian =>
      [Italian.Verbs.abbracciare, Italian.Verbs.baciare, Italian.Verbs.coccolare,
        Italian.Verbs.conoscere, Italian.Verbs.consultare, Italian.Verbs.frequentare,
        Italian.Verbs.incontrare, Italian.Verbs.incrociare, Italian.Verbs.lasciare,
        Italian.Verbs.sposare, Italian.Verbs.trovare, Italian.Verbs.vedere].map (·.toVerb)
  | .spanish =>
      [Spanish.Verbs.abrazar, Spanish.Verbs.acurrucar, Spanish.Verbs.besar, Spanish.Verbs.casar,
        Spanish.Verbs.consultar, Spanish.Verbs.cruzar, Spanish.Verbs.dejar,
        Spanish.Verbs.encontrar]
  | .catalan =>
      [Catalan.Verbs.abracar, Catalan.Verbs.casar, Catalan.Verbs.deixar, Catalan.Verbs.petonejar,
        Catalan.Verbs.topar, Catalan.Verbs.trobar]

/-- The divergence from Siloni's parameter: Italian carries lexical reciprocal entries,
*abbracciare* 'hug' (40) among them, though the parameter classifies it as syntax-set. -/
theorem romance_not_monolithic :
    "abbracciare" ∈ (appendixA .italian).map Verb.form ∧
      Siloni2012.Language.italian.formation = Formation.syntactic :=
  ⟨by decide, rfl⟩

/-! ### Readings with and without *se* (§4.3) -/

/-- The readings of a plural-subject clause: the pseudo-reciprocal reading of a lexical entry,
a single collective event, and the grammatical reciprocal and reflexive readings of a
transitive entry under *se*. -/
inductive SeReading where
  | pseudoReciprocal
  | grammaticalReciprocal
  | grammaticalReflexive
  deriving DecidableEq

/-- The readings an entry contributes under *se*: the lexical entry its pseudo-reciprocal
reading, the transitive entry the two grammatical readings (55), (56a), (57a). -/
def Formation.readingsWithSe : Formation → List SeReading
  | .lexical => [.pseudoReciprocal]
  | .syntactic => [.grammaticalReciprocal, .grammaticalReflexive]

/-- The readings an entry contributes without *se*: only the lexical entry contributes
(56b), (57b). -/
def Formation.readingsWithoutSe : Formation → List SeReading
  | .lexical => [.pseudoReciprocal]
  | .syntactic => []

/-- The readings of a *se*-clause of the class, when the class combines with *se* at all. -/
def VerbClass.readingsWithSe (c : VerbClass) : List SeReading :=
  if c.CombinesWithSe then c.formations.flatMap Formation.readingsWithSe else []

/-- The readings of a *se*-less clause of the class. -/
def VerbClass.readingsWithoutSe (c : VerbClass) : List SeReading :=
  c.formations.flatMap Formation.readingsWithoutSe

/-- A class-3 *se*-clause is three-ways ambiguous (56a), (57a). -/
theorem class3_three_ways :
    VerbClass.reciprocalTransitive.readingsWithSe =
      [.pseudoReciprocal, .grammaticalReciprocal, .grammaticalReflexive] := by
  decide

/-- Without *se* no grammatical reading survives, for any class: the reflexive and the
accumulated-events reciprocal readings need the grammatical strategy. -/
theorem grammatical_needs_se (c : VerbClass) :
    SeReading.grammaticalReciprocal ∉ c.readingsWithoutSe ∧
      SeReading.grammaticalReflexive ∉ c.readingsWithoutSe := by
  cases c <;> decide

/-- The pseudo-reciprocal reading survives without *se* exactly for the classes with a lexical
entry. -/
theorem pseudo_without_se_iff (c : VerbClass) :
    SeReading.pseudoReciprocal ∈ c.readingsWithoutSe ↔ c.ReciprocityByItself := by
  cases c <;> decide

/-- By definition (44), a class is a lexical reciprocal in a language iff some construction of
that language lets a reciprocal interpretation emerge without *se*. -/
def LexicalReciprocalIn (l : Language) (c : VerbClass) : Prop :=
  ∃ e, SeOmissible l e ∧ SeReading.pseudoReciprocal ∈ c.readingsWithoutSe

/-- Lexical reciprocity in the sense of (44) is having a lexical entry, in every language. -/
theorem lexicalReciprocalIn_iff (l : Language) (c : VerbClass) :
    LexicalReciprocalIn l c ↔ c.ReciprocityByItself :=
  ⟨fun ⟨_, _, h⟩ ↦ (pseudo_without_se_iff c).1 h,
    fun h ↦ ⟨.analyticCausative, every_language_diagnosable l, (pseudo_without_se_iff c).2 h⟩⟩

/-! ### Pseudo-reciprocity against plain reciprocity (§4.3) -/

/-- Grammatical reciprocity (50), Strong Reciprocity over the participants, is plain in
[winter-2018]'s sense for every relation, symmetric or not: plain reciprocity is agreement with
Strong Reciprocity on pairs. -/
theorem strongReciprocity_plainReciprocity {A : Type*} (R : A → A → Prop) :
    Winter2018.PlainReciprocity (StrongReciprocity R) R :=
  fun _ _ ↦ .rfl

/-- A lexical entry's collective predicate is not so constrained: for any relation some
collective predicate fails plain reciprocity for it, the room in which 'divorce' fails the
collective-to-unidirectional direction (53) and 'kiss' the converse (54). -/
theorem exists_collective_not_plain (R : Bool → Bool → Prop) :
    ∃ P : Finset Bool → Prop, ¬ Winter2018.PlainReciprocity P R :=
  ⟨fun X ↦ ¬ StrongReciprocity R X, fun h ↦ iff_not_self (h {true, false} (by decide)).symm⟩

/-! ### The reciprocal 'with'-construction (§4.4) -/

/-- Whether the class allows the reciprocal 'with'-construction, the observation of §4.4:
both classes with a lexical entry do, including non-symmetric members, *consultarsi con*,
*lasciarsi con* (59), and the attested *baciarsi con*, *abbracciarsi con* (60), and the
plain transitives do not, *ringraziarsi con* (61). Italian retains *si* in the construction,
unlike French. -/
def VerbClass.AllowsWithConstruction : VerbClass → Prop
  | .plainTransitive => False
  | _ => True

/-- The generalization of [kemmer-1993] over the class system: the 'with'-construction is
available exactly where a lexical entry is. -/
theorem withConstruction_iff_lexical (c : VerbClass) :
    c.AllowsWithConstruction ↔ c.ReciprocityByItself := by
  cases c <;> simp [VerbClass.AllowsWithConstruction, VerbClass.ReciprocityByItself,
    VerbClass.formations]

/-! ### Swahili (fourth chapter) -/

/-- The Swahili lexical reciprocals (169), verbs in *-an-* whose suffix is lexicalized as part
of the stem, each with its binary base as Appendix C gives it. -/
def appendixC : List (Verb × Option Verb) :=
  [(Swahili.Verbs.achana, some Swahili.Verbs.acha),
    (Swahili.Verbs.gawana, some Swahili.Verbs.gawa),
    (Swahili.Verbs.gombana, some Swahili.Verbs.gomba),
    (Swahili.Verbs.gongana, some Swahili.Verbs.gonga),
    (Swahili.Verbs.jibizana, none),
    (Swahili.Verbs.pambana, some Swahili.Verbs.pamba),
    (Swahili.Verbs.patana, some Swahili.Verbs.pata),
    (Swahili.Verbs.pigana, some Swahili.Verbs.piga),
    (Swahili.Verbs.shindana, some Swahili.Verbs.shinda),
    (Swahili.Verbs.tengana, some Swahili.Verbs.tenga)]

/-- Each lexical reciprocal with a base is the base with *-an-* before its final vowel. -/
theorem appendixC_form :
    ∀ p ∈ appendixC, ∀ b ∈ p.2, p.1.form.toList = b.form.toList.dropLast ++ ['a', 'n', 'a'] := by
  decide

/-- Swahili lexical reciprocals may lack a binary base altogether: *jibizana* 'discuss' has
none, so lexical reciprocity is not always derivational, the Bantu analogue of the Romance
intransitive class. -/
theorem jibizana_no_binary_base : ∃ p ∈ appendixC, p.1.form = "jibizana" ∧ p.2.isNone := by
  decide

end Palmieri2024
