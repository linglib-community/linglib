module

public import Linglib.Semantics.Presupposition.SyntacticEnvironment
public import Linglib.Semantics.Presupposition.QuantifiedLocalContext

/-!
# Quantified clauses

A quantified clause `(Q R. S)` is a quantifier on the tree of numbers with a restrictor and a
nuclear scope, formulas of the propositional fragment whose atoms denote sets of world–individual
pairs (`Presupposition.QuantifiedClause`). Its truth set is that of the nuclear scope's quantified
sentence, with the restrictor and the scope read off the formulas' denotations
(`QuantifiedClause.truth`).

A trigger of the clause sits in one argument of the quantifier, with the other argument given: in
the restrictor before the scope, or in the scope after the restrictor (`QuantifiedClause.Arg`). Its
environment is that argument together with the trigger's environment inside the argument's formula
(`QuantifiedClause.Env`), and its meaning is the function from the gap's denotation to the clause's
truth set. A good final of the clause may replace the scope after a restrictor and keeps the
restrictor before a scope, as meanings (`QuantifiedClause.Arg.finals`) and as strings
(`QuantifiedClause.Env.SameInitialString`). The triggers of a clause are listed with
their environments by `QuantifiedClause.occurrences`, and filling the gap of each gives back the
clause (`QuantifiedClause.fill_of_mem_occurrences`).

## Implementation notes

* A clause is the root of its sentence, so a sentence holds one quantifier, whose arguments are
  propositional.
* After a restrictor every predicate is a possible scope, not only those a formula denotes, as
  Expressivity has it.

## References

* [schlenker-2009]
* [van-benthem-1984]
-/

@[expose] public section

namespace Presupposition

open Quantifier

variable {Atom W E : Type*}

/-- A quantified clause `(Q R. S)`: a quantifier with a restrictor and a nuclear scope, formulas
whose atoms denote sets of world–individual pairs. -/
structure QuantifiedClause (Atom : Type*) where
  /-- The quantifier. -/
  quantifier : NumberTree
  /-- The restrictor. -/
  restrictor : Formula Atom
  /-- The nuclear scope. -/
  scope : Formula Atom

namespace QuantifiedClause

/-- The argument of a quantifier that holds a gap: the restrictor, followed by the scope `S`, or
the scope, preceded by the restrictor `R`. -/
inductive Arg (Atom : Type*) where
  | restrictor (S : Formula Atom)
  | scope (R : Formula Atom)
  deriving DecidableEq

/-- A quantified clause with a gap: the environment of the gap inside one argument of the
quantifier. -/
structure Env (Atom : Type*) where
  /-- The quantifier. -/
  quantifier : NumberTree
  /-- The argument that holds the gap, with the other argument. -/
  arg : Arg Atom
  /-- The environment of the gap inside the argument's formula. -/
  inner : SyntacticEnvironment Atom

variable (I : Atom → Set (W × E))

/-- The truth set of a clause. -/
def truth (c : QuantifiedClause Atom) : Set W :=
  scopeTruth c.quantifier (fun w e ↦ (w, e) ∈ c.restrictor.truth I) (c.scope.truth I)

namespace Arg

/-- Fill the argument that holds the gap. -/
def fill (q : NumberTree) : Arg Atom → Formula Atom → QuantifiedClause Atom
  | restrictor S, X => ⟨q, X, S⟩
  | scope R, X => ⟨q, R, X⟩

/-- The truth set of the clause as a function of the denotation of the argument that holds the
gap. -/
def truth (q : NumberTree) : Arg Atom → Set (W × E) → Set W
  | restrictor S => restrictorTruth q fun w e ↦ (w, e) ∈ S.truth I
  | scope R => scopeTruth q fun w e ↦ (w, e) ∈ R.truth I

/-- The meanings that a good final of the clause gives the argument that holds the gap: one for
each scope after a restrictor, the clause's own before a scope. -/
def finals (q : NumberTree) : Arg Atom → Set (Set (W × E) → Set W)
  | restrictor _ => Set.range (restrictorTruth q)
  | scope R => {scopeTruth q fun w e ↦ (w, e) ∈ R.truth I}

theorem truth_mem_finals (q : NumberTree) (a : Arg Atom) : a.truth I q ∈ a.finals I q := by
  cases a
  · exact Set.mem_range_self _
  · rfl

/-- Two arguments have the same initial string when a good final may turn one into the other: it
may replace the scope after a restrictor, and keeps the restrictor before a scope. -/
inductive SameInitialString : Arg Atom → Arg Atom → Prop
  | restrictor (S S' : Formula Atom) : SameInitialString (.restrictor S) (.restrictor S')
  | scope (R : Formula Atom) : SameInitialString (.scope R) (.scope R)

end Arg

namespace Env

/-- Fill the gap of a clause's environment. -/
def fill (k : Env Atom) (X : Formula Atom) : QuantifiedClause Atom :=
  k.arg.fill k.quantifier (k.inner.fill X)

/-- The meaning of a clause's environment as a function of the gap's denotation. -/
def truth (k : Env Atom) (d : Set (W × E)) : Set W :=
  k.arg.truth I k.quantifier (k.inner.truth I d)

theorem truth_fill (k : Env Atom) (X : Formula Atom) :
    (k.fill X).truth I = k.truth I (X.truth I) := by
  obtain ⟨q, a, K⟩ := k
  cases a <;> simp [fill, truth, Arg.fill, Arg.truth, QuantifiedClause.truth,
    SyntacticEnvironment.truth_fill, scopeTruth, restrictorTruth]

/-- `SameInitialString k k'` holds when `k'` keeps the material of `k` before the gap and replaces
what follows it: the quantifier, a restrictor before the scope, and the material before the gap
inside the argument stay. -/
def SameInitialString (k k' : Env Atom) : Prop :=
  k.quantifier = k'.quantifier ∧ k.arg.SameInitialString k'.arg ∧
    k.inner.SameInitialString k'.inner

/-- The material after the gap of a clause's environment contains no trigger: none after the gap
inside the argument, and none in a scope after a restrictor. -/
def TriggerFreeFinal (k : Env Atom) : Prop :=
  k.inner.TriggerFreeFinal ∧ ∀ S, k.arg = .restrictor S → S.occurrences = []

end Env

/-- The triggers of a clause, each with its environment and its presupposition and assertion. -/
def occurrences (c : QuantifiedClause Atom) : List (Env Atom × Atom × Atom) :=
  c.restrictor.occurrences.map (fun o ↦ (⟨c.quantifier, .restrictor c.scope, o.1⟩, o.2)) ++
    c.scope.occurrences.map fun o ↦ (⟨c.quantifier, .scope c.restrictor, o.1⟩, o.2)

theorem fill_of_mem_occurrences {c : QuantifiedClause Atom} {o : Env Atom × Atom × Atom}
    (h : o ∈ c.occurrences) : o.1.fill (.trigger o.2.1 o.2.2) = c := by
  obtain ⟨q, R, S⟩ := c
  rcases List.mem_append.1 h with h | h <;> obtain ⟨o', ho', rfl⟩ := List.mem_map.1 h
  · simp [Env.fill, Arg.fill, Formula.fill_of_mem_occurrences ho']
  · simp [Env.fill, Arg.fill, Formula.fill_of_mem_occurrences ho']

end QuantifiedClause

end Presupposition
