/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Option.NAry

/-!
# Landau (2004): The Scale of Finiteness and the Calculus of Control

Landau's calculus of control: each clausal head, I and C, may carry slots for `[T]` and `[Agr]`, and
the R-assignment rule applies to a head that has both. A head both of whose features are positive
is assigned `[+R]`, and a head with both slots and a negative value `[−R]`; a head lacking a slot,
as in the complements of raising and ECM verbs and in small clauses, is assigned nothing. The
subject of the clause checks the `[R]` of I: a lexical noun phrase or *pro* is `[+R]`, and PRO is
`[−R]`. So a clause whose I is `[−R]` [licenses PRO and no referential
subject](##Landau2004.Finiteness.licensesPRO_and_not_licensesReferential_iff), which is obligatory
control, and a clause whose I is `[+R]` licenses a referential subject. When C is `[+R]` as well,
the two cancel and PRO is licensed too, so that such a clause [licenses both
subjects](##Landau2004.Finiteness.licensesPRO_and_licensesReferential_iff): the free subjunctives
of the Balkan languages and the subjunctives of Hebrew have these features, and a null subject
there is PRO [only where the language has no *pro* to put
there](##Landau2004.Finiteness.nullSubject_isPRO_iff), as Hebrew has none in the third person.

The tense a complement's verb selects fixes `[T]` on both heads, and `EmbeddedTense.toFiniteness`
builds the features of a tense at given agreement values, from which obligatory control is computed.

## Implementation notes

The licensing conditions are those of the derivations for indicatives, the two Balkan
subjunctives, Hebrew subjunctives and infinitives with exhaustive and partial control, as the
paper's two feature tables classify them. A clause both of whose heads are `[−R]`, the paper's
uncontrolled inflected infinitive of Hungarian, is not treated: `LicensesPRO` holds of it.
[landau-2013] states the calculus as a rule on I alone, with the cancellation in a footnote.
The calculus is superseded in its author's later work: [landau-2015] replaces the `[±T]` split by
the attitude and nonattitude contexts of the two tiers of control (`Studies/Landau2015.lean`), and
[landau-2024a] describes the `[−R]` account of where PRO occurs as a redescription of the
problem and lists the interaction of agreement with control among the open questions.

## References

* [landau-2004]
* [landau-2013]
* [landau-2015]
* [landau-2024a]
-/

@[expose] public section

namespace Landau2004

/-- A clausal head as the calculus sees it: its `[T]` and `[Agr]` values, `none` where the head
has no slot for the feature. -/
structure Finiteness.Head where
  /-- Semantic tense, `[±T]`, `none` without a `[T]` slot. -/
  tense : Option Bool
  /-- Agreement, `[±Agr]`, `none` without an `[Agr]` slot. -/
  agr : Option Bool
  deriving DecidableEq, Repr

/-- (39): the R-assignment rule. A head with both slots is assigned `[+R]` when both features are
positive and `[−R]` otherwise, and a head lacking a slot is assigned nothing. -/
def Finiteness.Head.r (h : Finiteness.Head) : Option Bool :=
  Option.map₂ (· && ·) h.tense h.agr

theorem Finiteness.Head.r_eq_some_true_iff {h : Finiteness.Head} :
    h.r = some true ↔ h.tense = some true ∧ h.agr = some true := by
  obtain ⟨_ | t, _ | a⟩ := h <;> simp [Finiteness.Head.r]

theorem Finiteness.Head.r_eq_none_iff {h : Finiteness.Head} :
    h.r = none ↔ h.tense = none ∨ h.agr = none := by
  obtain ⟨_ | t, _ | a⟩ := h <;> simp [Finiteness.Head.r]

/-- The finiteness of a clause as the calculus sees it: the features of its inflectional and
complementizer heads. -/
structure Finiteness where
  /-- The inflectional head. -/
  i : Finiteness.Head
  /-- The complementizer head. -/
  c : Finiteness.Head
  deriving DecidableEq, Repr

/-- A clause licenses PRO when its I is `[−R]`, which PRO checks, or when its I and its C are
both `[+R]` and check each other. -/
def Finiteness.LicensesPRO (cl : Finiteness) : Prop :=
  cl.i.r = some false ∨ cl.i.r = some true ∧ cl.c.r = some true

/-- A clause licenses a referential subject, a lexical noun phrase or *pro*, when its I is
`[+R]`. -/
def Finiteness.LicensesReferential (cl : Finiteness) : Prop := cl.i.r = some true

instance (cl : Finiteness) : Decidable cl.LicensesPRO :=
  inferInstanceAs (Decidable (_ ∨ _ ∧ _))

instance (cl : Finiteness) : Decidable cl.LicensesReferential :=
  inferInstanceAs (Decidable (_ = _))

/-- Obligatory control: a clause licenses PRO and no referential subject exactly when its I is
`[−R]`. -/
theorem Finiteness.licensesPRO_and_not_licensesReferential_iff {cl : Finiteness} :
    cl.LicensesPRO ∧ ¬ cl.LicensesReferential ↔ cl.i.r = some false := by
  simp only [LicensesPRO, LicensesReferential]
  rcases cl.i.r with _ | _ | _ <;> simp

/-- A clause licenses both PRO and a referential subject exactly when its I and its C are both
`[+R]`, as in a Balkan free subjunctive and a Hebrew subjunctive. -/
theorem Finiteness.licensesPRO_and_licensesReferential_iff {cl : Finiteness} :
    cl.LicensesPRO ∧ cl.LicensesReferential ↔ cl.i.r = some true ∧ cl.c.r = some true := by
  simp only [LicensesPRO, LicensesReferential]
  rcases cl.i.r with _ | _ | _ <;> simp

theorem Finiteness.not_licensesPRO_of_r_eq_none {cl : Finiteness} (h : cl.i.r = none) :
    ¬ cl.LicensesPRO := by
  simp [Finiteness.LicensesPRO, h]

-- (34)
/-- A null subject is PRO or, in a language that has it, *pro*. In a clause that licenses PRO it
must be PRO exactly when the clause licenses no referential subject or the language has no
*pro*. -/
theorem Finiteness.nullSubject_isPRO_iff {cl : Finiteness} (h : cl.LicensesPRO) (hasPro : Prop) :
    ¬ (cl.LicensesReferential ∧ hasPro) ↔ cl.i.r = some false ∨ ¬ hasPro := by
  simp only [LicensesPRO, LicensesReferential] at h ⊢
  rcases hi : cl.i.r with _ | _ | _ <;> simp_all

/-! ### The tense of a complement -/

/-- (35): the tense of a complement clause. Anaphoric tense is identical to the matrix tense,
`[−T]` on I and C; dependent tense is selected by the matrix verb, `[+T]` on I and C; independent
tense is free, `[+T]` on I and nothing on C. The criterion is semantic: a clause may be untensed
despite its tense morphology, as the controlled subjunctives of the Balkan languages are, which
have anaphoric tense, where the free subjunctives have dependent tense. -/
inductive EmbeddedTense where
  /-- `[−T]` on I and C. -/
  | anaphoric
  /-- `[+T]` on I and C. -/
  | dependent
  /-- `[+T]` on I, no `[T]` on C. -/
  | independent
  deriving DecidableEq, Repr

/-- The tense determined by two observables of a clause type: unrestricted tense, aspect and mood
marks independent tense, and among the restricted clauses a tense of the clause's own separates
dependent from anaphoric tense. -/
def EmbeddedTense.ofFiniteness (unrestrictedTAM independentTense : Prop)
    [Decidable unrestrictedTAM] [Decidable independentTense] : EmbeddedTense :=
  if unrestrictedTAM then .independent
  else if independentTense then .dependent else .anaphoric

/-- (35), (37), (38): the clause of a tense, at the agreement value `agr` of I and, for dependent
tense, `cAgr` of C. Agreement on C needs `[+T]` there. An indicative is the clause of independent
tense with agreement on I. -/
def EmbeddedTense.toFiniteness (t : EmbeddedTense) (agr : Bool) (cAgr : Bool := false) :
    Finiteness :=
  match t with
  | .anaphoric => ⟨⟨some false, some agr⟩, ⟨some false, none⟩⟩
  | .dependent => ⟨⟨some true, some agr⟩, ⟨some true, if cAgr then some true else none⟩⟩
  | .independent => ⟨⟨some true, some agr⟩, ⟨none, none⟩⟩

/-- A complement of a tense shows obligatory control when its clause licenses PRO and no
referential subject. -/
def EmbeddedTense.HasOC (t : EmbeddedTense) (agr : Bool) (cAgr : Bool := false) : Prop :=
  (t.toFiniteness agr cAgr).LicensesPRO ∧ ¬ (t.toFiniteness agr cAgr).LicensesReferential

instance (t : EmbeddedTense) (agr cAgr : Bool) : Decidable (t.HasOC agr cAgr) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Anaphoric tense gives obligatory control whatever the agreement, and a tensed complement
gives it exactly without agreement on I, whatever C carries: tense and agreement together are what
cancel control. -/
theorem EmbeddedTense.hasOC_iff (t : EmbeddedTense) (agr cAgr : Bool) :
    t.HasOC agr cAgr ↔ t = .anaphoric ∨ agr = false := by
  cases t <;> cases agr <;> cases cAgr <;> decide

-- (38), (69)
theorem EmbeddedTense.dependent_licenses_both :
    (EmbeddedTense.dependent.toFiniteness true true).LicensesPRO ∧
      (EmbeddedTense.dependent.toFiniteness true true).LicensesReferential := by
  decide

end Landau2004
