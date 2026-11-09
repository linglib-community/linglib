module

public import Linglib.Semantics.ArgumentStructure.Root.Kinds
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Order.Closure
public import Mathlib.Order.UpperLower.Closure

/-!
# Verbal roots

As far as grammar reads it, the meaning of a verbal root in the sense of Beavers and
Koontz-Garboden is the set of kinds of lexical entailment it carries (§5.2.1); what tells a root
apart from the other members of its class is idiosyncratic content that each study describes in
its own paper's terms. A root is well formed when it is a lower set of the collocational order,
and [the collocational closure](##ArgumentStructure.Root.close) sends a root to the least
well-formed one containing it. A root composes with `v` as its complement, the result position of
√flat and √drown, or adjoined to it, the manner position of √jog and √hand (§4.5.3–4.5.4); this
is where a root merges rather than what it means, so it is `Root.Position`, not part of `Root`.

## References

* [beavers-koontz-garboden-2020]
-/

@[expose] public section

namespace ArgumentStructure

/-- The meaning of a verbal root, the kinds of lexical entailment it carries, `∅` where
unannotated. -/
abbrev Root := Finset Root.Kind

namespace Root

open Finset

variable {r : Root} {k : Kind}

/-- A root is well formed if it respects the collocational restrictions, that is, if it is a
lower set of the kind order. -/
def WellFormed (r : Root) : Prop := IsLowerSet (r : Set Kind)

instance : DecidablePred WellFormed := fun r =>
  inferInstanceAs (Decidable (∀ a b : Kind, b ≤ a → a ∈ r → b ∈ r))

/-- The collocational closure of a set of kinds, its lower closure in the kind order, whose
closed sets are the well-formed roots. -/
@[simps! isClosed]
def close : ClosureOperator (Finset Kind) :=
  .ofPred (fun s ↦ univ.filter (∃ j ∈ s, · ≤ j)) WellFormed
    (fun _ k hk ↦ by simpa using ⟨k, hk, le_rfl⟩)
    (fun _ _ _ hba ha ↦ by
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at ha ⊢
      exact ha.imp fun _ hj ↦ ⟨hj.1, hba.trans hj.2⟩)
    (fun _ _ hst ht _ hk ↦ by
      obtain ⟨_, hj, hkj⟩ := by simpa using hk
      exact ht hkj (hst hj))

@[simp] theorem mem_close : k ∈ close r ↔ ∃ j ∈ r, k ≤ j := by
  rw [show close r = univ.filter (∃ j ∈ r, · ≤ j) from rfl]; simp

theorem mem_close_iff_of_isMax (hk : IsMax k) : k ∈ close r ↔ k ∈ r :=
  ⟨fun h ↦ let ⟨_, hj, hkj⟩ := mem_close.1 h; le_antisymm (hk hkj) hkj ▸ hj,
    fun h ↦ mem_close.2 ⟨k, h, le_rfl⟩⟩

@[simp, norm_cast] theorem coe_close (r : Root) :
    (close r : Set Kind) = lowerClosure (r : Set Kind) := by
  ext; simp

/-! ### The attested rows of the typology -/

/-- Property-concept roots (√flat). -/
def propertyConcept : Root := {.state}

/-- Result roots without causation (√blossom). -/
def pureResult : Root := {.state, .result}

/-- Caused-result roots (√crack). -/
def causativeResult : Root := {.state, .result, .cause}

/-- Pure manner roots (√jog). -/
def pureManner : Root := {.manner}

/-- Roots carrying every kind (√hand, √drown). -/
def fullSpec : Root := univ

/-- The position in which a verbal root composes with `v`. -/
inductive Position where
  /-- The complement of `v`, the result position. -/
  | complement
  /-- Adjoined to `v` as a modifier, the manner position. -/
  | adjoined
  deriving DecidableEq, Fintype, Repr

end Root

end ArgumentStructure
