module

public import Studies.Imanishi2014

/-!
# Imanishi (2020): Parameterizing Split Ergativity in Mayan

This file formalizes [imanishi-2020], the journal account of the alignment puzzle of
[imanishi-2014]: the non-perfective clause of Kaqchikel, Chol and Q'anjob'al is an aspectual
predicate embedding a nominalized clause, yet Kaqchikel cross-references the subject with the
set B marker and the transitive object with set A, (4), where Chol and Q'anjob'al do the
reverse, (5). The Restriction on Nominalization (63), that nominalized verbs lack a
syntactically projected external argument, is the dissertation's requirement
(`Imanishi2014.URN`) restated as a selectional property of the nominalizing head. Under it a
transitive base must be independently intransitivized, by passivization, antipassivization or
(pseudo) noun incorporation (`Strategy`), and the subject is base-generated as the argument of
the matrix predicate (`Matrix`): absolutive from Infl under the intransitive *ajin*, inherent
ergative from transitive v under *chäp* 'begin'. A `Clause` records these choices, and
`Clause.subject` and `Clause.object` say what licenses each argument (`Licensing`): genitive
from the D of the nominalized clause goes to its highest Case-less DP, absolutive to the object
from Voice or from the Q'anjob'al suffix *-on*. `Clause.WellFormed` collects the conditions the
derivations rely on, among them the semantic control of the matrix subject into an external
θ-role of the base, which excludes unaccusative and passive bases under *ajin*, (92) and (94).
The summary (117) is `subjectMarker_setB_iff` and `objectMarker_setA_iff`, and `case_eq_caseOf`
shows that the progressive derivations assign the dissertation's Cases.

## Implementation notes

* That nominalized verbs of Kaqchikel must be intransitivized is not derived from the
  restriction, as the paper conjectures it may be; it is a clause of `WellFormed`.
* The closing generalization, that the restriction fails exactly when the verbal domain of the
  nominalized clause has a structural Case assigner, is not stated: in the dissertation's survey
  Tojolabal is low absolutive yet subject to the requirement, so the criterion cannot be read
  off `Mayan.ABSPosition`.
* The Case-licensing of the relational noun by the preposition *chi*, (87) and (88), and the
  third person set B marker for the nominalized clause on the aspectual predicate are outside
  the model.

## References

* [imanishi-2020]
* [imanishi-2014]
* [coon-mateo-pedro-preminger-2014]
* [alexiadou-2001]
-/

@[expose] public section

namespace Imanishi2020

open Imanishi2014 Mayan

/-- The base verb of a nominalization, by the arguments it projects. -/
inductive Base
  | transitive
  | unergative
  | unaccusative
  | passive
  deriving DecidableEq

/-- The base has an external θ-role for the matrix subject to control into (Section 3.2.2); a
passive base has it suppressed. -/
def Base.HasExternal (b : Base) : Prop := b = .transitive ∨ b = .unergative

/-- How a transitive base is intransitivized under the restriction (Sections 3.2.1 and 3.3):
passivization leaves the object as the only DP of the nominalized clause, antipassivization
demotes it to an oblique under a relational noun, and (pseudo) noun incorporation Case-licenses
it under adjacency. -/
inductive Strategy
  | passive
  | antipassive
  | incorporation
  deriving DecidableEq

/-- The predicate embedding the nominalized clause: the intransitive aspectual predicate *ajin*
of the Kaqchikel progressive, whose subject sits in its specifier, the transitive verb *chäp*
'begin', or an aspectual predicate such as Chol *choñkol* and Q'anjob'al *lanan* that takes the
nominalized clause as its sole argument. -/
inductive Matrix
  | ajin
  | chap
  | aspectual
  deriving DecidableEq

/-- What licenses an argument of the nominalized verb: genitive from the D of the nominalized
clause, absolutive from Voice or the suffix inside it, absolutive from the matrix Infl,
inherent ergative from the transitive matrix v, genitive from a relational noun, or (pseudo)
noun incorporation. -/
inductive Licensing
  | gen
  | absVoice
  | absInfl
  | ergV
  | oblique
  | incorporated
  deriving DecidableEq

/-- The Case an argument receives, if any. -/
def Licensing.case : Licensing → Option Case
  | .gen | .oblique => some .gen
  | .absVoice | .absInfl => some .abs
  | .ergV => some .erg
  | .incorporated => none

/-- The agreement set cross-referencing the argument on the verbal complex, ergative and
genitive both spelled out as set A. An oblique is cross-referenced on its relational noun and an
incorporated object not at all. -/
def Licensing.marker : Licensing → Option MarkerSet
  | .gen | .ergV => some .setA
  | .absVoice | .absInfl => some .setB
  | .oblique | .incorporated => none

/-- A nominalized clause: the language's nominalization parameters, the base verb, the
intransitivizing strategy if any, and the embedding predicate, `none` for a nominalized clause
in argument position, (64)–(71). -/
structure Clause where
  lang : Nominalization
  base : Base
  strategy : Option Strategy
  matrix : Option Matrix

namespace Clause

variable (c : Clause)

/-- The restriction bans the base's external argument from the nominalized clause. -/
def Restricted : Prop := c.lang.urn = .required ∧ c.base.HasExternal

instance : Decidable c.Restricted := by unfold Restricted Base.HasExternal; infer_instance

/-- Licensing of the subject, the external argument or the internal argument of an unaccusative
or passive base. Under the restriction it is base-generated as the argument of the matrix
predicate and licensed there; otherwise it is the highest DP of the nominalized clause and
receives genitive from D. -/
def subject : Option Licensing :=
  if c.Restricted then
    match c.matrix with
    | some .ajin => some .absInfl
    | some .chap => some .ergV
    | some .aspectual | none => none
  else some .gen

/-- Licensing of the object of a transitive base: by the intransitivizing strategy under the
restriction, and otherwise by the Case assigner in the verbal domain of the nominalized clause,
Voice of a low absolutive language or the suffix, if there is one. -/
def object : Option Licensing :=
  if c.base = .transitive then
    match c.strategy with
    | some .passive => some .gen
    | some .antipassive => some .oblique
    | some .incorporation => some .incorporated
    | none => if c.lang.absPos = .low ∨ c.lang.suffix then some .absVoice else none
  else none

/-- The agreement set cross-referencing the subject. -/
def subjectMarker : Option MarkerSet := c.subject.bind Licensing.marker

/-- The agreement set cross-referencing the object. -/
def objectMarker : Option MarkerSet := c.object.bind Licensing.marker

/-- The conditions the derivations rely on: a transitive base is intransitivized exactly under
the restriction (Section 3.1), the subject of *ajin* and *chäp* semantically controls an
external θ-role of the base (Section 3.2.2), an embedded clause licenses its subject, and a
transitive object is licensed. -/
def WellFormed : Prop :=
  (c.strategy ≠ none ↔ c.Restricted ∧ c.base = .transitive) ∧
  (c.matrix = some .ajin ∨ c.matrix = some .chap → c.base.HasExternal) ∧
  (c.subject ≠ none ∨ c.matrix = none) ∧ (c.base = .transitive → c.object ≠ none)

instance : Decidable c.WellFormed := by unfold WellFormed Base.HasExternal; infer_instance

/-- The Kaqchikel progressive of a transitive, (85): a passive nominalization under *ajin*. -/
def kaqchikelProgressive : Clause := ⟨.kaqchikel, .transitive, some .passive, some .ajin⟩

/-- The Kaqchikel progressive of an unergative, (91). -/
def kaqchikelUnergative : Clause := ⟨.kaqchikel, .unergative, none, some .ajin⟩

/-- The Kaqchikel progressive of an unaccusative, (92). -/
def kaqchikelUnaccusative : Clause := ⟨.kaqchikel, .unaccusative, none, some .ajin⟩

/-- The Kaqchikel progressive of a passive verb, (94). -/
def kaqchikelPassive : Clause := ⟨.kaqchikel, .passive, none, some .ajin⟩

/-- A nominalized unaccusative in subject position, (69). -/
def kaqchikelSubjectNominal : Clause := ⟨.kaqchikel, .unaccusative, none, none⟩

/-- A passive nominalization under *chäp* 'begin', (98). -/
def kaqchikelBegin : Clause := ⟨.kaqchikel, .transitive, some .passive, some .chap⟩

/-- An antipassive nominalization under *chäp*, (100). -/
def kaqchikelAntipassive : Clause := ⟨.kaqchikel, .transitive, some .antipassive, some .chap⟩

/-- The incorporating *-oj* nominalization under *ajin*, (102). -/
def kaqchikelIncorporation : Clause :=
  ⟨.kaqchikel, .transitive, some .incorporation, some .ajin⟩

/-- The Chol progressive of a transitive, (60a). -/
def cholProgressive : Clause := ⟨.chol, .transitive, none, some .aspectual⟩

/-- The Chol progressive of an intransitive, (60b). -/
def cholIntransitive : Clause := ⟨.chol, .unaccusative, none, some .aspectual⟩

/-- The Q'anjob'al progressive of a transitive, (73a), the object licensed by *-on*. -/
def qanjobalProgressive : Clause := ⟨.qanjobal, .transitive, none, some .aspectual⟩

-- (4)
theorem kaqchikelProgressive_markers :
    kaqchikelProgressive.WellFormed ∧ kaqchikelProgressive.subjectMarker = some .setB ∧
      kaqchikelProgressive.objectMarker = some .setA := by
  decide

-- (91)
theorem kaqchikelUnergative_markers :
    kaqchikelUnergative.WellFormed ∧ kaqchikelUnergative.subjectMarker = some .setB ∧
      kaqchikelUnergative.objectMarker = none := by
  decide

-- (92), (94)
theorem not_wellFormed_unaccusative_passive :
    ¬ kaqchikelUnaccusative.WellFormed ∧ ¬ kaqchikelPassive.WellFormed := by
  decide

-- (69)
theorem kaqchikelSubjectNominal_subject :
    kaqchikelSubjectNominal.WellFormed ∧ kaqchikelSubjectNominal.subject = some .gen := by
  decide

-- (98)
theorem kaqchikelBegin_markers :
    kaqchikelBegin.WellFormed ∧ kaqchikelBegin.subjectMarker = some .setA ∧
      kaqchikelBegin.objectMarker = some .setA := by
  decide

-- (100), (102), (104)
theorem no_gen_antipassive_incorporation :
    kaqchikelAntipassive.WellFormed ∧ kaqchikelAntipassive.objectMarker = none ∧
      kaqchikelIncorporation.WellFormed ∧ kaqchikelIncorporation.objectMarker = none := by
  decide

-- (5)
theorem chol_qanjobal_markers :
    cholProgressive.WellFormed ∧ cholProgressive.subjectMarker = some .setA ∧
      cholProgressive.objectMarker = some .setB ∧
    cholIntransitive.WellFormed ∧ cholIntransitive.subjectMarker = some .setA ∧
    qanjobalProgressive.WellFormed ∧ qanjobalProgressive.subjectMarker = some .setA ∧
      qanjobalProgressive.objectMarker = some .setB := by
  decide

-- (66), (68)
theorem subject_ne_gen (h : c.Restricted) : c.subject ≠ some .gen := by
  simp only [subject, ite_eq_left h]
  split <;> simp

-- (59), (60)
theorem absPos_low_or_suffix_of_object (h : c.object = some .absVoice) :
    c.lang.absPos = .low ∨ c.lang.suffix := by
  unfold object at h
  split at h
  · split at h <;> simp_all
    exact or_iff_not_imp_left.2 h
  · simp at h

/-- (117): under a progressive predicate the subject is cross-referenced by set B exactly when
the restriction holds. -/
theorem subjectMarker_setB_iff (h : c.WellFormed) (hb : c.base.HasExternal)
    (hm : c.matrix = some .ajin ∨ c.matrix = some .aspectual) :
    c.subjectMarker = some .setB ↔ c.lang.urn = .required := by
  obtain ⟨-, -, hs, -⟩ := h
  rcases c with ⟨⟨urn, absPos, suffix⟩, base, strategy, matrix⟩
  cases urn <;> rcases hm with hm | hm <;> subst hm <;>
    simp_all [subjectMarker, subject, Restricted, Licensing.marker]

/-- (117): the object of a passive nominalization or of an unrestricted transitive is
cross-referenced by set A exactly when the restriction holds. -/
theorem objectMarker_setA_iff (h : c.WellFormed) (ht : c.base = .transitive)
    (ha : c.strategy ≠ some .antipassive) (hi : c.strategy ≠ some .incorporation) :
    c.objectMarker = some .setA ↔ c.lang.urn = .required := by
  obtain ⟨hst, -, -, ho⟩ := h
  rcases c with ⟨⟨urn, absPos, suffix⟩, base, strategy, matrix⟩
  subst ht
  cases urn <;> cases absPos <;> rcases strategy with _ | (_ | _ | _) <;> by_cases hs : suffix <;>
    simp_all [objectMarker, object, Restricted, Base.HasExternal, Licensing.marker]

theorem case_eq_caseOf (h : c.WellFormed) (ht : c.base = .transitive)
    (hm : c.matrix = some .ajin ∨ c.matrix = some .aspectual)
    (ha : c.strategy ≠ some .antipassive) (hi : c.strategy ≠ some .incorporation) :
    c.subject.bind Licensing.case = c.lang.caseOf .A ∧
      c.object.bind Licensing.case = c.lang.caseOf .P := by
  obtain ⟨hst, -, hs, ho⟩ := h
  rcases c with ⟨⟨urn, absPos, suffix⟩, base, strategy, matrix⟩
  subst ht
  cases urn <;> cases absPos <;> rcases strategy with _ | (_ | _ | _) <;> by_cases hs : suffix <;>
    rcases hm with hm | hm <;> subst hm <;>
    simp_all [subject, object, Restricted, Base.HasExternal, Licensing.case,
      Nominalization.caseOf, Nominalization.phaseHead, Nominalization.caseless,
      Nominalization.VerbAssignsAbs]

end Clause

end Imanishi2020
