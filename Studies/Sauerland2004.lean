module

public import Linglib.Pragmatics.NeoGricean.Basic
public import Linglib.Core.Data.Fintype.Sets
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod

/-!
# Sauerland (2004): Scalar Implicatures in Complex Sentences

The paper splits Gazdar's scalar implicatures into two tiers. A scalar alternative `ψ` that
asymmetrically entails the assertion yields the primary implicature `¬Kψ` (42), and `K¬ψ` is a
secondary implicature when it is consistent with the assertion and all primary implicatures (43);
these are `NeoGricean.primaryImplicatures` and `NeoGricean.IsSecondaryImplicature`. Disjunction
sits on the scale (40) of *or*, the operators `L` and `R` of (39) that keep one disjunct, and
*and*, and the scalar alternatives of a sentence are all substitutions of scale-mates for its
scalar items (19).

Of *A or B* only the exclusiveness implicature `K¬(A and B)` is secondary, the strengthenings
`K¬A` and `K¬B` being blocked (46). Of *Kai had the broccoli or some of the peas* they are
`K¬(broccoli and some)` and `K¬(all)` (49), with `K¬(broccoli and all)`, which `K¬(all)`
entails, so the scalar item under disjunction gets the implicature earlier accounts missed. Of
*A or (B or C)* they are the three pairwise exclusiveness implicatures and two that these entail
(52).

## Main statements

* `isSecondaryImplicature_ab_iff`: (46).
* `isSecondaryImplicature_kai_iff`: (49).
* `isSecondaryImplicature_abc_iff`: (52).

## Implementation notes

A world is a valuation of the atoms, or for (47) whether Kai had the broccoli and whether he had
none, some but not all, or all of the peas. Alternatives are indexed by the scale-mates
substituted, so one proposition can carry several indices, as *A* does in (51).

## Errata

(51) lists nine primary implicatures of *A or (B or C)*, but the cross product (19) of the two
disjunctions' scales also yields *A or B*, *A or C* and *A or (B and C)*, which asymmetrically
entail the assertion. Their primary implicatures block no secondary implicature, so (52) holds
over all twelve stronger alternatives (`isSecondaryImplicature_abc_iff`).

## References

* [sauerland-2004]
-/

@[expose] public section

namespace Sauerland2004

open NeoGricean Set

attribute [local instance] Set.decidableSubsetOfFintype Set.decidableSSubsetOfFintype

/-- The scale of disjunction (40). -/
inductive Connective where
  | or
  /-- The operator `L` of (39), which keeps the left disjunct. -/
  | L
  /-- The operator `R` of (39), which keeps the right disjunct. -/
  | R
  | and
  deriving DecidableEq, Fintype

/-- The proposition a connective forms from two propositions. -/
def Connective.apply {W : Type*} : Connective → Set W → Set W → Set W
  | .or, A, B => A ∪ B
  | .L, A, _ => A
  | .R, _, B => B
  | .and, A, B => A ∩ B

instance {W : Type*} (c : Connective) (A B : Set W) [DecidablePred (· ∈ A)]
    [DecidablePred (· ∈ B)] : DecidablePred (· ∈ c.apply A B) := by
  cases c <;> unfold Connective.apply <;> infer_instance

/-- The `i`th atomic sentence, true at the valuations that make it true. -/
def atom {n : ℕ} (i : Fin n) : Set (Fin n → Bool) := {w | w i}

instance {n : ℕ} (i : Fin n) : DecidablePred (· ∈ atom i) :=
  fun w ↦ inferInstanceAs (Decidable (w i = true))

/-! ### Disjunction (Section 3.2) -/

/-- *A `c` B*, the scalar alternative of *A or B* with `c` for *or* (19). -/
def ab (c : Connective) : Set (Fin 2 → Bool) := c.apply (atom 0) (atom 1)

instance (c : Connective) : DecidablePred (· ∈ ab c) :=
  fun w ↦ inferInstanceAs (Decidable (w ∈ c.apply (atom 0) (atom 1)))

/-- (46): the only secondary implicature of *A or B* is exclusiveness. -/
theorem isSecondaryImplicature_ab_iff (c : Connective) :
    IsSecondaryImplicature (ab .or) (range ab) (ab c) ↔ c = .and := by
  rw [isSecondaryImplicature_range_iff]
  cases c <;> decide

/-! ### A scalar item under disjunction (Section 3.3) -/

/-- The scale of the peas quantifier. -/
inductive Quantity where
  | some
  | all
  deriving DecidableEq, Fintype

/-- Whether Kai had the broccoli, and whether he had none, some but not all, or all of the
peas. -/
abbrev Meal := Bool × Fin 3

/-- *Kai had `q` of the peas.* -/
def Quantity.peas : Quantity → Set Meal
  | .some => {w | 1 ≤ w.2}
  | .all => {w | w.2 = 2}

instance (q : Quantity) : DecidablePred (· ∈ q.peas) := by
  cases q <;> unfold Quantity.peas <;> infer_instance

/-- *Kai had the broccoli `a.1` `a.2` of the peas*, the scalar alternative of (47) with `a.1` for
*or* and `a.2` for *some* (19). -/
def kai (a : Connective × Quantity) : Set Meal := a.1.apply {w | w.1} a.2.peas

instance (a : Connective × Quantity) : DecidablePred (· ∈ kai a) :=
  fun w ↦ inferInstanceAs (Decidable (w ∈ a.1.apply {w : Meal | w.1} a.2.peas))

/-- (48)–(49): of the six primary implicatures of *Kai had the broccoli or some of the peas*,
those of the two conjunctions and of *Kai had all of the peas* strengthen. -/
theorem isSecondaryImplicature_kai_iff (c : Connective) (q : Quantity) :
    IsSecondaryImplicature (kai (.or, .some)) (range kai) (kai (c, q)) ↔
      c = .and ∨ (c = .R ∧ q = .all) := by
  rw [isSecondaryImplicature_range_iff]
  simp only [Prod.forall]
  cases c <;> cases q <;> decide

/-! ### Multiple disjunction -/

/-- *A `a.1` (B `a.2` C)*, the scalar alternative of *A or (B or C)* (50) with `a.1` for the outer
and `a.2` for the inner *or* (19). -/
def abc (a : Connective × Connective) : Set (Fin 3 → Bool) :=
  a.1.apply (atom 0) (a.2.apply (atom 1) (atom 2))

instance (a : Connective × Connective) : DecidablePred (· ∈ abc a) :=
  fun w ↦ inferInstanceAs (Decidable (w ∈ a.1.apply (atom 0) (a.2.apply (atom 1) (atom 2))))

/-- (51)–(52): the secondary implicatures of *A or (B or C)* are `K¬(B and C)` and those of the
alternatives whose outer connective is *and*. -/
theorem isSecondaryImplicature_abc_iff (c d : Connective) :
    IsSecondaryImplicature (abc (.or, .or)) (range abc) (abc (c, d)) ↔
      c = .and ∨ (c = .R ∧ d = .and) := by
  rw [isSecondaryImplicature_range_iff]
  simp only [Prod.forall]
  cases c <;> cases d <;> decide

end Sauerland2004
