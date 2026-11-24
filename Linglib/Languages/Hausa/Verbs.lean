module

public import Linglib.Syntax.Category.Verb.Basic
public import Linglib.Phonology.Tone.Basic
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Fintype.Basic

/-!
# Hausa verbs

Hausa verbs fall into morphological classes called grades, each defined by a tone pattern and a
termination, a final vowel or in a few grades a final *-aC*: *dafā̀* 'cook' is grade 1, *zā̀gā*
'insult' grade 2, *kōmō* 'return here' grade 6. A verb base operates in several grades, as *sàyā*
'buy' (grade 2) appears as *sayḕ* 'buy up' (grade 4), *sayar̃* 'sell' (grade 5), *sayō* 'buy and
bring' (grade 6) and *sàyu* 'be well bought' (grade 7). Within its grade a verb has up to four
forms by syntactic context: the A-form with no object after it, the B-form before a personal
pronoun direct object, the C-form before any other direct object, and the D-form before an
indirect object, where grades 2, 3 and 7 have no form of their own and add the pre-dative suffix
instead. Grades 0 to 3 are primary; grade 3 is exclusively intransitive and grade 2 exclusively
transitive. The secondary grades carry meanings: grade 4 action totally done, grade 5, the
efferential, action directed away from the speaker, grade 6, the ventive, action toward the
speaker, and grade 7, the sustentative, an agentless passive or middle ([newman-2000]).

## Main definitions

* `Hausa.Grade`, `Hausa.Grade.terminations`, `Hausa.Grade.melody` — the grades and their
  terminations and tones by form
* `Hausa.Grade.HasObjectForms`, `Hausa.Grade.UsesPreDative` — a grade has forms before a direct
  object; it adds the pre-dative suffix before an indirect object
* `Hausa.Verb` — a verb with its grade

## Main results

* `Hausa.Grade.usesPreDative_iff` — the grades that add the pre-dative suffix are grade 2 and the
  grades with no form before a direct object
* `Hausa.Grade.changing_iff` — grade 2 is the one grade whose A-, B- and C-forms all differ
* `Hausa.Verb.isIntransitive_of_not_hasObjectForms` — the entries of a grade with no form before a
  direct object are intransitive

## Implementation notes

The terminations and tones are those of [newman-2000]'s table of the grade system, for finite
verbs outside the imperative. A grade's melody is its tone pattern on a verb of two syllables,
spreading from the right, so that a lone high covers every syllable; the tone of a third syllable,
which differs between forms in grades 1, 2 and 4, is not recorded. The particle *dà* that follows
some grade 5 forms is not part of the verb and is left out, and the grade 5 form with no
termination is written *-Ø*.

## References

* [newman-2000]
-/

@[expose] public section

namespace Hausa

open Tone (TRN)

/-- The grades. -/
inductive Grade where
  | gr0 | gr1 | gr2 | gr3 | gr3a | gr3b | gr4 | gr5 | gr5d | gr6 | gr7
  deriving DecidableEq, Repr, Fintype

/-- The forms of a verb by syntactic context. -/
inductive VerbForm where
  /-- With no object after the verb. -/
  | A
  /-- Before a personal pronoun direct object. -/
  | B
  /-- Before any other direct object. -/
  | C
  /-- Before an indirect object. -/
  | D
  deriving DecidableEq, Repr, Fintype

namespace Grade

/-- The terminations of a grade in a form; empty where the grade has no such form. -/
def terminations : Grade → VerbForm → Finset String
  | gr0, .A | gr0, .C => {"-i", "-ā", "-ō"}
  | gr0, .B => {"-ī", "-ā", "-ō"}
  | gr0, .D => {"-i", "-ī", "-ā", "-ō"}
  | gr1, .C => {"-a"}
  | gr1, _ => {"-ā"}
  | gr2, .A => {"-ā"}
  | gr2, .B => {"-ē"}
  | gr2, .C => {"-i"}
  | gr3, .A | gr3a, .A => {"-a"}
  | gr3b, .A => {"-i", "-u", "-a"}
  | gr4, .C => {"-e", "-ē", "-nye", "-nyē"}
  | gr4, _ => {"-ē", "-nyē"}
  | gr5, .A | gr5, .D => {"-ar̃"}
  | gr5, .B => {"-ar̃", "-shē", "-Ø"}
  | gr5, .C => {"-ar̃", "-Ø"}
  | gr5d, .C => {"-dà"}
  | gr5d, _ => {"-dā"}
  | gr6, _ => {"-ō"}
  | gr7, .A => {"-u"}
  | _, _ => ∅

/-- The tone pattern of a grade on a verb of two syllables. -/
def melody : Grade → List TRN
  | gr0 | gr3a | gr5 | gr6 => [.H]
  | gr1 | gr3b | gr4 | gr5d => [.H, .L]
  | gr2 | gr3 | gr7 => [.L, .H]

/-- The grade has forms before a direct object. -/
def HasObjectForms (g : Grade) : Prop :=
  (g.terminations .B).Nonempty ∧ (g.terminations .C).Nonempty

instance (g : Grade) : Decidable g.HasObjectForms := inferInstanceAs (Decidable (_ ∧ _))

/-- The grade has no D-form and adds the pre-dative suffix before an indirect object. -/
def UsesPreDative (g : Grade) : Prop := g.terminations .D = ∅

instance (g : Grade) : Decidable g.UsesPreDative := inferInstanceAs (Decidable (_ = _))

/-- The grades that add the pre-dative suffix are grade 2 and those with no form before a direct
object, grades 3, 3a, 3b and 7. -/
theorem usesPreDative_iff : ∀ g : Grade, g.UsesPreDative ↔ g = gr2 ∨ ¬ g.HasObjectForms := by
  decide

/-- Grade 2 is the one grade whose A-, B- and C-forms all differ. -/
theorem changing_iff : ∀ g : Grade,
    (g.HasObjectForms ∧ Disjoint (g.terminations .A) (g.terminations .B) ∧
      Disjoint (g.terminations .B) (g.terminations .C) ∧
      Disjoint (g.terminations .A) (g.terminations .C)) ↔ g = gr2 := by
  decide

end Grade

/-- A Hausa verb, cited in its A-form, with the grade it operates in. -/
structure Verb extends _root_.Verb where
  grade : Grade

/-- *ci* 'eat'. -/
def ci : Verb := { morphs := [.root "ci"], valency := .ofFrame .np, grade := .gr0 }

/-- *jā* 'pull'. -/
def ja : Verb := { morphs := [.root "jā"], valency := .ofFrame .np, grade := .gr0 }

/-- *dafā̀* 'cook'. -/
def dafa : Verb := { morphs := [.root "dafā̀"], valency := .ofFrame .np, grade := .gr1 }

/-- *zā̀gā* 'insult'. -/
def zaga : Verb := { morphs := [.root "zā̀gā"], valency := .ofFrame .np, grade := .gr2 }

/-- *sàyā* 'buy', C-form *sàyi*. -/
def saya : Verb := { morphs := [.root "sàyā"], valency := .ofFrame .np, grade := .gr2 }

/-- *fita* 'go out'. -/
def fita : Verb := { morphs := [.root "fita"], valency := .ofFrame .intransitive, grade := .gr3 }

/-- *ƙaura* 'migrate'. -/
def kaura : Verb := { morphs := [.root "ƙaura"], valency := .ofFrame .intransitive, grade := .gr3a }

/-- *guɗù* 'run away'. -/
def gudu : Verb := { morphs := [.root "guɗù"], valency := .ofFrame .intransitive, grade := .gr3b }

/-- *sayḕ* 'buy up'. -/
def saye : Verb := { morphs := [.root "sayḕ"], valency := .ofFrame .np, grade := .gr4 }

/-- *sayar̃* 'sell'. -/
def sayar : Verb := { morphs := [.root "sayar̃"], valency := .ofFrame .np, grade := .gr5 }

/-- *sayō* 'buy and bring'. -/
def sayo : Verb := { morphs := [.root "sayō"], valency := .ofFrame .np, grade := .gr6 }

/-- *kōmō* 'return here'. -/
def komo : Verb := { morphs := [.root "kōmō"], valency := .ofFrame .intransitive, grade := .gr6 }

/-- *sàyu* 'be well bought'. -/
def sayu : Verb := { morphs := [.root "sàyu"], valency := .ofFrame .intransitive, grade := .gr7 }

/-- *gyā̀ru* 'be well repaired'. -/
def gyaru : Verb := { morphs := [.root "gyā̀ru"], valency := .ofFrame .intransitive, grade := .gr7 }

/-- The verbs. -/
def verbs : List Verb :=
  [ci, ja, dafa, zaga, saya, fita, kaura, gudu, saye, sayar, sayo, komo, sayu, gyaru]

/-- The verbs of a grade with no form before a direct object are intransitive. -/
theorem Verb.isIntransitive_of_not_hasObjectForms :
    ∀ v ∈ verbs, ¬ v.grade.HasObjectForms → v.IsIntransitive := by
  decide

end Hausa
