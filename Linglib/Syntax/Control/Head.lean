/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/

module

/-!
# The Calculus of Control

[landau-2004]'s calculus, as codified in [landau-2013] ((137)/(178)): each
clausal head — I and C — may carry slots for `[T]` and `[Agr]`, and the
R-assignment rule applies to a head that has both. A head both of whose
features are positive is assigned `[+R]`, licensing an independent referential
subject; a head with both slots and a negative value is assigned `[−R]`; a head
lacking a slot, as in the defective complements of raising, ECM and small
clauses, is assigned nothing, and the calculus says nothing about control there
(`Clause.not_hasControl_of_r_eq_none`). Control is the *elsewhere* case among
clauses whose I is fully specified. Mutual cancellation ([landau-2013] fn. 6):
when C is `[+T, +Agr]` as well as I, R-assignment cancels and OC re-emerges —
the Hebrew subjunctive effect, inexpressible on a flat tense scale.
[landau-2004]'s scale of finiteness (`ClauseClass`) abbreviates clauses with a
fully specified I, and `ClauseClass.HasOC` is derived from the calculus via
`ClauseClass.toClause`.

## Main definitions

- `Control.Head`, `Control.Head.r`, `Control.Clause`
- `Control.Clause.HasControl`: control as the elsewhere condition
- `Control.ClauseClass`: the scale of finiteness, with derived
  `ClauseClass.HasOC`

## References

* [landau-2004]
* [landau-2013]
* [landau-2015]
* [ostrove-2026]
-/

@[expose] public section

namespace Control

/-- A clausal head as the calculus sees it: its `[T]` and `[Agr]` values, `none`
    where the head has no slot for the feature ([landau-2004]; [landau-2013]
    (137)). -/
structure Head where
  /-- Semantic tense, `[±T]`, `none` without a `[T]` slot. -/
  tense : Option Bool
  /-- Agreement, `[±Agr]`, `none` without an `[Agr]` slot. -/
  agr : Option Bool
  deriving DecidableEq, Repr

/-- The R-assignment rule ([landau-2013] (137)): a head with both slots is
    assigned `[+R]` when both features are positive and `[−R]` otherwise, and a
    head lacking a slot is assigned nothing. -/
def Head.r (h : Head) : Option Bool :=
  h.tense.bind fun t ↦ h.agr.map (t && ·)

theorem Head.r_eq_some_true_iff {h : Head} :
    h.r = some true ↔ h.tense = some true ∧ h.agr = some true := by
  obtain ⟨_ | t, _ | a⟩ := h <;> simp [Head.r]

theorem Head.r_eq_none_iff {h : Head} : h.r = none ↔ h.tense = none ∨ h.agr = none := by
  obtain ⟨_ | t, _ | a⟩ := h <;> simp [Head.r]

/-- A clause as the calculus sees it: its inflectional and complementizer
    heads. -/
structure Clause where
  /-- The inflectional head. -/
  i : Head
  /-- The complementizer head. -/
  c : Head
  deriving DecidableEq, Repr

/-- Control is the elsewhere case ([landau-2013] (178) with fn. 6): a clause
    whose I has both slots has control unless I is `[+R]`, and with a `[+R]` I
    keeps it only when C is `[+R]` too — mutual cancellation. -/
def Clause.HasControl (cl : Clause) : Prop :=
  cl.i.r = some false ∨ cl.i.r = some true ∧ cl.c.r = some true

instance (cl : Clause) : Decidable cl.HasControl :=
  inferInstanceAs (Decidable (_ ∨ _ ∧ _))

/-- Mutual cancellation: a fully specified `[+R]` C restores OC in a clause whose
    I is fully specified — Hebrew subjunctives ([landau-2013] fn. 6). -/
theorem Clause.hasControl_of_c_r_eq_some_true {cl : Clause} (hi : cl.i.r.isSome)
    (hc : cl.c.r = some true) : cl.HasControl := by
  obtain ⟨_ | _, hb⟩ := Option.isSome_iff_exists.1 hi
  · exact .inl hb
  · exact .inr ⟨hb, hc⟩

/-- A clause whose I lacks a slot falls outside the R-assignment rule, so the
    calculus gives it no control, whatever its C ([landau-2013] (137)). -/
theorem Clause.not_hasControl_of_r_eq_none {cl : Clause} (h : cl.i.r = none) :
    ¬ cl.HasControl := by
  simp [Clause.HasControl, h]

/-! ### Clause classes -/

/-- [landau-2004]'s scale positions, in [ostrove-2026]'s terminology:
    C-subjunctives are `[−T]` complements (OC whatever the Agr value),
    F-subjunctives `[+T]` complements (OC unless `[+Agr]`, per the OC-NC
    generalization), and `finite` the fully finite remainder. The positions are tense cells,
    not mood or finiteness categories — `[−T]` covers bare infinitives
    and untensed subjunctives alike, and OC occurs in inflected
    complements. [landau-2015] subsumes the `[±T]` split under
    attitude/nonattitude (the tier reading lives with
    `Studies/Landau2015.lean`). -/
inductive ClauseClass where
  /-- `[−T]` complement: OC at any Agr value -/
  | cSubjunctive
  /-- `[+T]` complement: OC unless `[+Agr]` -/
  | fSubjunctive
  /-- Fully finite: `[+T, +Agr]` on I. No control unless C is fully specified
      too (mutual cancellation, `Clause.hasControl_of_c_r_eq_some_true`) -/
  | finite
  deriving DecidableEq, Repr

/-- The scale position determined by the two clause-typology observables
    of [ostrove-2026]-style fragments: unrestricted TAM marks a fully
    finite clause; among the TAM-restricted clauses, independent tense
    separates `[+T]` from `[−T]` ([landau-2004]'s feature, diagnosed by
    temporal mismatch). Per-language scale maps derive from this single
    classifier rather than restating the case table. -/
def ClauseClass.ofFiniteness (unrestrictedTAM independentTense : Bool) : ClauseClass :=
  if unrestrictedTAM then .finite
  else if independentTense then .fSubjunctive else .cSubjunctive

/-- The clause a scale position abbreviates, at a given Agr value: an I with both
    slots, `[±T]` per the position, and a C with neither. The scale cannot express
    a fully specified C — mutual cancellation needs the calculus directly. -/
def ClauseClass.toClause (c : ClauseClass) (agr : Bool) : Clause :=
  ⟨⟨some (decide (c ≠ .cSubjunctive)), some (if c = .finite then true else agr)⟩, ⟨none, none⟩⟩

/-- OC is realized in a clause class iff the calculus leaves control at
    the clause it abbreviates: the elsewhere condition on `toClause`. -/
def ClauseClass.HasOC (c : ClauseClass) (agr : Bool) : Prop :=
  (c.toClause agr).HasControl

instance (c : ClauseClass) (agr : Bool) : Decidable (c.HasOC agr) :=
  inferInstanceAs (Decidable (Clause.HasControl _))

theorem ClauseClass.hasOC_iff (c : ClauseClass) (agr : Bool) :
    c.HasOC agr ↔ c = .cSubjunctive ∨ (c = .fSubjunctive ∧ agr = false) := by
  cases c <;> cases agr <;> decide

end Control
