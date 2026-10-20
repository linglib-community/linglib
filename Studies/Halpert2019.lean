module

public import Linglib.Syntax.Minimalist.Probe.Basic

/-!
# Halpert (2019): Raising, Unphased

This file formalizes Halpert's derivation of cross-linguistic variation in
raising-to-subject without the Phase Impenetrability Condition. Two properties of a clausal
complement do the work, `Clause`: whether it is a φ-goal that matrix T interacts with, and
whether it can satisfy the EPP by moving to Spec,TP, together with whether T has an EPP at all.
The engine is `Syntax/Minimalist/Probe/Basic.lean`'s `Probe`, whose search a φ-bearing clause
halts, `Probe.sat`, and which Agrees with the goal it halts on when that goal can occupy Spec,TP,
`Probe.int`, so the matrix-T EPP probe is `eppProbe` and the derivation it drives is
`raisingOutcome`. When the closest clause interacts but cannot satisfy the EPP it
absorbs the probe, and T probes a second time, after Rackowski and Richards, reaching the embedded
subject, hyper-raising, when it genuinely Agreed with the clause (section 4.3), and stalling in
defective intervention when it did not, the English `that`-clause of section 5.3. The attested
profiles follow from the engine: English, `english_profile`; Zulu, `zulu_profile`; Uyghur,
`uyghur_profile` (section 4.5); and Makhuwa and Matengo, which lack the EPP, `makhuwa_no_raising`
(section 5.1). Phasehood is thereby relativized to φ-probes rather than a fixed condition
(`Syntax/Minimalist/Phase.lean`): finite CPs and nonfinite TPs of the same size get opposite
raising outcomes across languages, `finite_cp_outcome_not_size_driven` and
`nonfinite_tp_outcome_not_size_driven`.

## Implementation notes

`raisingOutcome` is deterministic, so the optionality of Zulu hyper-raising out of a finite
clause, where an expletive non-raising variant coexists with it, is abstracted over, as are the
`tend`, `happen`, and `keep` selection matrix and the adjectival versus verbal small-clause split
of English.

## References

* [halpert-2019]
* [deal-2015a-nels]
* [rackowski-richards-2005]
-/

@[expose] public section

namespace Halpert2019

open Minimalist

/-- A clausal complement, classified by the three probe-relevant
    properties Halpert's account turns on. -/
structure Clause where
  /-- T's φ-probe halts on it, as on a φ-goal or a defective nominal
      intervener (the English `that`-CP). Transparent clauses (English
      nonfinite TP, small clauses) are not interveners. -/
  interacts : Bool
  /-- T can Agree with it (copy φ) — a genuine φ-goal. The English
      `that`-CP interacts but has no φ to copy ([moulton-2009]). -/
  canAgree : Bool
  /-- It can satisfy the EPP by moving to Spec,TP (Zulu infinitival TP,
      Uyghur DP-nominalization), vs. clauses barred from Spec,TP (Zulu
      finite CP, Uyghur NP-nominalization). -/
  canSatisfyEPP : Bool
  deriving DecidableEq, Repr

/-- A goal the matrix-T EPP probe ranges over, in c-command order the
    clausal complement (closest) and then the embedded subject. -/
inductive Goal
  | clause (c : Clause)
  | subject
  deriving DecidableEq, Repr

/-- The matrix-T EPP probe, whose search an intervening φ-bearing clause halts and which Agrees
with the goal it halts on when that goal can occupy Spec,TP. The embedded subject is a movable
φ-goal, halting and EPP-satisfying. [deal-2015a-nels]'s interaction is the halting here and
satisfaction the Agree, the reverse of [deal-2025a]'s algorithm, on which the second probing of
section 4.3 is one `Probe.agree` whose interacting clause does not satisfy the probe. -/
def eppProbe : Probe Goal where
  int := fun g => match g with | .clause c => c.canSatisfyEPP | .subject => true
  sat := fun g => match g with | .clause c => c.interacts | .subject => true

/-- The clause c-commands the embedded subject. -/
def goals (c : Clause) : List Goal := [.clause c, .subject]

/-- The five raising outcomes Halpert's typology distinguishes. -/
inductive RaisingOutcome
  /-- Without an EPP, T Agrees with the clause in situ and nothing moves (Makhuwa,
      Matengo). -/
  | noRaising
  /-- In ordinary raising the embedded subject moves to matrix Spec,TP
      (English nonfinite TP). -/
  | subjectRaises
  /-- The whole clause satisfies the EPP and moves (Zulu infinitival TP,
      Uyghur DP-nominalization). -/
  | clauseRaises
  /-- A second Agree reaches the embedded subject (Zulu finite CP,
      Uyghur NP-nominalization). -/
  | hyperRaises
  /-- A defective intervener stalls the probe (English finite CP). -/
  | blocked
  deriving DecidableEq, Repr

/-- The derivation, run through the canonical `Probe` engine. With no EPP
    nothing moves. With an EPP, matrix T runs `eppProbe.goal` over
    `[clause, subject]`. A transparent clause is skipped and the subject
    raises; a clause that satisfies the EPP is Agreed-with and raises
    whole; an interacting clause that cannot satisfy the EPP absorbs the
    probe (`Probe.goal_eq_none_of_not_int`), and the licensed second
    probe reaches the embedded subject (`hyperRaises`) iff T genuinely
    Agreed with the clause, else stalls (`blocked`). -/
def raisingOutcome (c : Clause) (hasEPP : Bool) : RaisingOutcome :=
  if hasEPP then
    match eppProbe.goal (goals c) with
    | some .subject => .subjectRaises
    | some (.clause _) => .clauseRaises
    | none => if c.canAgree then .hyperRaises else .blocked
  else .noRaising

/-! ### The derivation, from the `Probe` engine -/

private theorem search_clause {c : Clause} (h : c.interacts = true) :
    eppProbe.search (goals c) = some (.clause c) := by
  simp only [Probe.search, goals, eppProbe, List.find?_cons_of_pos, h]

private theorem search_subject {c : Clause} (h : c.interacts = false) :
    eppProbe.search (goals c) = some .subject := by
  simp only [Probe.search, goals, eppProbe, List.find?_cons_of_neg, h,
    List.find?_cons_of_pos, Bool.false_eq_true, not_false_eq_true]

/-- No EPP ⇒ no raising, whatever the clause. -/
theorem raisingOutcome_eq_noRaising (c : Clause) :
    raisingOutcome c false = .noRaising := rfl

/-- A transparent clause (not an intervener) lets T reach the embedded
    subject, which is ordinary raising. -/
theorem raisingOutcome_eq_subjectRaises {c : Clause} (h : c.interacts = false) :
    raisingOutcome c true = .subjectRaises := by
  have : eppProbe.goal (goals c) = some .subject :=
    Probe.goal_eq_some_iff.mpr ⟨search_subject h, rfl⟩
  simp only [raisingOutcome, this, ite_true]

/-- A φ-goal that satisfies the EPP raises as a whole clause; the
    embedded subject does not move. -/
theorem raisingOutcome_eq_clauseRaises {c : Clause} (hi : c.interacts = true)
    (he : c.canSatisfyEPP = true) : raisingOutcome c true = .clauseRaises := by
  have : eppProbe.goal (goals c) = some (.clause c) :=
    Probe.goal_eq_some_iff.mpr ⟨search_clause hi, he⟩
  simp only [raisingOutcome, this, ite_true]

/-- A φ-goal that interacts but cannot satisfy the EPP absorbs the first
    Agree; the licensed second probe reaches the embedded subject. -/
theorem raisingOutcome_eq_hyperRaises {c : Clause} (hi : c.interacts = true)
    (ha : c.canAgree = true) (he : c.canSatisfyEPP = false) :
    raisingOutcome c true = .hyperRaises := by
  have : eppProbe.goal (goals c) = none :=
    Probe.goal_eq_none_of_not_int (search_clause hi) he
  simp only [raisingOutcome, this, ha, ite_true]

/-- A defective intervener (interacts, but T cannot Agree with it) stalls
    the probe, with no second Agree and no raising. -/
theorem raisingOutcome_eq_blocked {c : Clause} (hi : c.interacts = true)
    (ha : c.canAgree = false) (he : c.canSatisfyEPP = false) :
    raisingOutcome c true = .blocked := by
  have : eppProbe.goal (goals c) = none :=
    Probe.goal_eq_none_of_not_int (search_clause hi) he
  simp only [raisingOutcome, this, ha, ite_true, ite_false, Bool.false_eq_true]

/-! ### Cross-linguistic raising profiles -/

/-- The English nonfinite TP is transparent, not an intervener. -/
def englishNonfiniteTP : Clause := ⟨false, false, false⟩
/-- The English finite `that`-CP is a defective intervener, visible but with no φ to
    Agree, and cannot move ([moulton-2009]). -/
def englishFiniteCP : Clause := ⟨true, false, false⟩
/-- The Zulu small clause is transparent. -/
def zuluSmallClause : Clause := ⟨false, false, false⟩
/-- The Zulu infinitival TP is a φ-goal that satisfies the EPP. -/
def zuluInfinitiveTP : Clause := ⟨true, true, true⟩
/-- The Zulu finite `ukuthi`-CP is a φ-goal that cannot satisfy the EPP. -/
def zuluFiniteCP : Clause := ⟨true, true, false⟩
/-- The Uyghur DP-nominalization (non-modal adjective) is a φ-goal that satisfies the
    EPP ([asarina-2011]). -/
def uyghurDP : Clause := ⟨true, true, true⟩
/-- The Uyghur NP-nominalization (modal adjective) is a φ-goal that cannot satisfy
    the EPP. -/
def uyghurNP : Clause := ⟨true, true, false⟩

/-- In the English raising profile ([halpert-2019]) raising is *required* out of
    a nonfinite TP and *blocked* out of a finite CP. (Models the
    `seem`/`be likely` predicates; the `tend`/`happen`/`keep` selection
    matrix and the AP/NP-vs-VP small-clause split are not modelled.) -/
theorem english_profile :
    raisingOutcome englishNonfiniteTP true = .subjectRaises ∧
    raisingOutcome englishFiniteCP true = .blocked :=
  ⟨raisingOutcome_eq_subjectRaises rfl, raisingOutcome_eq_blocked rfl rfl rfl⟩

/-- The Zulu raising profile ([halpert-2019], building on [ura-1994]'s
    hyper-raising) has hyper-raising out of a finite CP, the whole clause
    raises out of a nonfinite TP (so the subject does not), and the
    subject raises out of a small clause. The finite-CP case is in fact
    *optional* — an expletive `ku-` non-raising variant coexists with
    hyper-raising, and the `ku-`/`u-` morphology spells out first- vs.
    second-Agree — an optionality this deterministic `RaisingOutcome`
    abstracts over. -/
theorem zulu_profile :
    raisingOutcome zuluFiniteCP true = .hyperRaises ∧
    raisingOutcome zuluInfinitiveTP true = .clauseRaises ∧
    raisingOutcome zuluSmallClause true = .subjectRaises :=
  ⟨raisingOutcome_eq_hyperRaises rfl rfl rfl, raisingOutcome_eq_clauseRaises rfl rfl,
   raisingOutcome_eq_subjectRaises rfl⟩

/-- In the Uyghur raising profile ([asarina-2011], [halpert-2019]) a
    DP-nominalization raises whole and an NP-nominalization hyper-raises the
    embedded subject. -/
theorem uyghur_profile :
    raisingOutcome uyghurDP true = .clauseRaises ∧
    raisingOutcome uyghurNP true = .hyperRaises :=
  ⟨raisingOutcome_eq_clauseRaises rfl rfl, raisingOutcome_eq_hyperRaises rfl rfl rfl⟩

/-- In Makhuwa and Matengo, removing just the EPP from the Zulu setting kills
    raising entirely, even out of a finite-CP φ-goal. -/
theorem makhuwa_no_raising (c : Clause) : raisingOutcome c false = .noRaising :=
  raisingOutcome_eq_noRaising c

/-! ### Raising is unphased -/

/-- The thesis is that a finite CP yields hyper-raising in Zulu but is blocked in
    English — same clause "size", opposite outcomes — because the split is
    φ-goal status (`canAgree`), not a size-driven phase boundary. -/
theorem finite_cp_outcome_not_size_driven :
    raisingOutcome zuluFiniteCP true ≠ raisingOutcome englishFiniteCP true := by
  decide

/-- Likewise, out of a nonfinite TP the whole clause raises in Zulu but the
    subject raises in English, since the split is EPP-satisfaction
    (`canSatisfyEPP`), not clause size. -/
theorem nonfinite_tp_outcome_not_size_driven :
    raisingOutcome zuluInfinitiveTP true ≠ raisingOutcome englishNonfiniteTP true := by
  decide

end Halpert2019
