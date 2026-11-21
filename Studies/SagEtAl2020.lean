module

public import Linglib.Syntax.HPSG.Construction

/-!
# Sag et al. (2020): Lessons from the English Auxiliary System

In some English clauses, such as polar questions, the auxiliary comes before the subject. This
file formalizes the paper's constructional analysis of this subject-auxiliary inversion.

## The analysis

The *aux-initial* construction requires the head daughter of a clause to be an invertible finite
auxiliary, a word marked `[INV +]`. It says nothing about meaning. Following Fillmore, the
aux-initial clauses share no semantics. Each kind gets its meaning from the clause type it also
belongs to: the polar interrogative from the interrogative clauses, and the aux-initial
exclamative from the exclamative clauses.

A polar interrogative is built directly by its construction. It is not derived from an
uninverted clause, which is why the auxiliary puzzle of structure dependence does not arise.

## What is proved

The construction is one principle over the RSRL construct hierarchy of
`Syntax/HPSG/Construction` (`auxInitialPrinciple`). The two clauses are sorts below both the
aux-initial construction and a clause type (`sai_cross_classify`).

A worked construct of either sort satisfies the grammar exactly when its head is inverted and
its mother carries the semantics of its clause type (`polarInterrogative_models`,
`auxInitialExclamative_models`).

## Implementation notes

The construction also has valence conditions: the valents of the head daughter are its sisters,
and the mother is valence-saturated. These are not in the RSRL signature and are not modelled;
only the `[INV +]` head is.

The paper's other constructions, the inflectional and negation constructions and contraction,
are not formalized.

## References

* [sag-etal-2020]
* [sag-2010]
* [ginzburg-sag-2000]
-/

@[expose] public section

namespace SagEtAl2020

open HPSG.RSRL HPSG.Construction

/-- The aux-initial construction requires the head daughter to be an inverted verb. -/
def auxInitialPrinciple : Constraint sig where
  sort := .auxInitialCxt
  body := .sortAssign (.path [.HDDTR, .CAT, .INV]) .plus

/-- The filler-gap grammar extended with the aux-initial construction. -/
abbrev saiGrammar : Grammar sig :=
  .ofList ((constraints ++ [auxInitialPrinciple]).map Constraint.toDescription)

theorem sai_cross_classify :
    (Srt.auxInitialCxt ≤ .headedCxt ∧ Srt.fillerHeadCxt ≤ .headedCxt) ∧
      (Srt.polarIntCl ≤ .auxInitialCxt ∧ Srt.polarIntCl ≤ .interrogativeCl) ∧
      (Srt.auxInitialExclCl ≤ .auxInitialCxt ∧ Srt.auxInitialExclCl ≤ .exclamativeCl) := by
  decide

/-! ### Worked aux-initial constructs -/

/-- The entities of a worked aux-initial construct are the construct, its mother and head
daughter, the verbal category they share with its inversion value and finite verb form, and the
mother's semantic object. An aux-initial construct has no filler daughter. -/
inductive SAIEnt where
  | cxt
  | mtr
  | hd
  | cat
  | inv
  | vform
  | sem
  deriving DecidableEq, Fintype, Repr

/-- A finite aux-initial construct of sort `cxtSort` whose head daughter has inversion value
`invSort` and whose mother has semantic type `semSort`. -/
@[reducible] def saiConstruct (cxtSort invSort semSort : Srt) : Interpretation sig SAIEnt where
  S := fun
    | .cxt => cxtSort
    | .mtr | .hd => .overtExpr
    | .cat => .verb
    | .inv => invSort
    | .vform => .fin
    | .sem => semSort
  A := fun a u ↦ match a, u with
    | .MTR, .cxt => some .mtr
    | .HDDTR, .cxt => some .hd
    | .CAT, .mtr | .CAT, .hd => some .cat
    | .INV, .cat => some .inv
    | .VFORM, .cat => some .vform
    | .SEM, .mtr => some .sem
    | _, _ => none
  R := noRel

theorem saiConstruct_isWellTyped :
    ∀ i ∈ [Srt.plus, .minus], ∀ σ ∈ [Srt.question, .fact, .austinean],
      ∀ c ∈ [Srt.polarIntCl, .auxInitialExclCl], (saiConstruct c i σ).IsWellTyped := by
  decide +kernel

theorem polarInterrogative_models :
    (saiConstruct .polarIntCl .plus .question).Models saiGrammar ∧
      ¬ (saiConstruct .polarIntCl .minus .question).Models saiGrammar ∧
      ¬ (saiConstruct .polarIntCl .plus .austinean).Models saiGrammar := by
  decide

theorem auxInitialExclamative_models :
    (saiConstruct .auxInitialExclCl .plus .fact).Models saiGrammar ∧
      ¬ (saiConstruct .auxInitialExclCl .minus .fact).Models saiGrammar ∧
      ¬ (saiConstruct .auxInitialExclCl .plus .question).Models saiGrammar := by
  decide

end SagEtAl2020
