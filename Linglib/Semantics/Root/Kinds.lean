module

public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Order.Closure
public import Mathlib.Order.UpperLower.Closure
public import Mathlib.Tactic.DeriveFintype

/-!
# Root kind signatures

Which templatic components a root entails, the coarse, between-class half of a
root's meaning; the fine, within-class half is `Root.Content`. The root typology
of Beavers and Koontz-Garboden (§5.4.1) records which of four kinds of
lexical entailment a root carries — state, manner, result, cause —
under two collocational restrictions, that a change entails a state and a cause
entails a change. The restrictions are the partial order `state ≤ result ≤ cause`
on `Root.Kind`, with `manner` isolated. A root's kind signature is a
`Finset Root.Kind`; it is well-formed when it is a lower set of that order, and
the closure operator `close` sends any signature to its lower closure, the least
well-formed signature containing it. The named signatures are the attested rows
of the typology's display (12).

## Main declarations

* `Root.Kind`, with the collocational `PartialOrder`
* `Root.Kinds`, `Root.Kinds.WellFormed`
* `Root.Kinds.close`: the collocational closure, a `ClosureOperator` whose closed
  signatures are the well-formed ones
* `Root.Kinds.propertyConcept`, `pureResult`, `causativeResult`, `pureManner`,
  `fullSpec`

## References

* [beavers-koontz-garboden-2020]: The Roots of Verbal Meaning.
-/

@[expose] public section

namespace Semantics

/-! ### Kinds -/

/-- The kinds of lexical entailment in the root typology of
[beavers-koontz-garboden-2020]. -/
inductive Root.Kind where
  | state
  | manner
  | result
  | cause
  deriving DecidableEq, Fintype, Repr

namespace Root.Kind

/-- The collocational order, `state ≤ result ≤ cause` with `manner` isolated, since a
change entails a state and a cause entails a change. -/
protected inductive LE : Kind → Kind → Prop
  | refl (a) : Kind.LE a a
  | state_result : Kind.LE state result
  | state_cause : Kind.LE state cause
  | result_cause : Kind.LE result cause

instance : LE Kind := ⟨Kind.LE⟩

instance : DecidableLE Kind := fun a b => by
  cases a <;> cases b <;> first | exact isTrue (by constructor) | exact isFalse (by rintro ⟨_⟩)

instance : PartialOrder Kind where
  le_refl := .refl
  le_trans := by decide
  le_antisymm := by decide

end Root.Kind

/-! ### Signatures -/

/-- A root kind signature, the set of kinds a root carries. -/
abbrev Root.Kinds := Finset Root.Kind

namespace Root.Kinds

open Finset

variable {s : Kinds} {k : Kind}

/-- A signature is well-formed if it respects the collocational restrictions, that is,
if it is a lower set of the kind order. -/
def WellFormed (s : Kinds) : Prop := IsLowerSet (s : Set Kind)

instance : DecidablePred WellFormed := fun s =>
  inferInstanceAs (Decidable (∀ a b : Kind, b ≤ a → a ∈ s → b ∈ s))

/-- The collocational closure of a signature, its lower closure in the kind order, whose
closed signatures are the well-formed ones. -/
@[simps! isClosed]
def close : ClosureOperator Kinds := .ofPred (fun s ↦ univ.filter (∃ j ∈ s, · ≤ j)) WellFormed
  (fun _ k hk ↦ by simpa using ⟨k, hk, le_rfl⟩)
  (fun _ _ _ hba ha ↦ by
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at ha ⊢
    exact ha.imp fun _ hj ↦ ⟨hj.1, hba.trans hj.2⟩)
  (fun _ _ hst ht _ hk ↦ by
    obtain ⟨_, hj, hkj⟩ := by simpa using hk
    exact ht hkj (hst hj))

@[simp] theorem mem_close : k ∈ close s ↔ ∃ j ∈ s, k ≤ j := by
  rw [show close s = univ.filter (∃ j ∈ s, · ≤ j) from rfl]; simp

@[simp, norm_cast] theorem coe_close (s : Kinds) :
    (close s : Set Kind) = lowerClosure (s : Set Kind) := by
  ext; simp

/-! ### The attested rows of the typology -/

/-- The signature of property-concept roots (√flat). -/
def propertyConcept : Kinds := {.state}

/-- The signature of result roots without causation (√blossom). -/
def pureResult : Kinds := {.state, .result}

/-- The signature of caused-result roots (√crack). -/
def causativeResult : Kinds := {.state, .result, .cause}

/-- The signature of pure manner roots (√jog). -/
def pureManner : Kinds := {.manner}

/-- The signature of roots carrying every kind (√hand, √drown). -/
def fullSpec : Kinds := univ

end Root.Kinds

end Semantics
