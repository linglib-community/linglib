module

public import Linglib.Semantics.Focus.Particles
public import Linglib.Data.Examples.Francescotti1995
public import Linglib.Data.Examples.Readers

/-!
# Francescotti (1995): Even: The Conventional Implicature Approach Reconsidered

This file formalizes [francescotti-1995]'s felicity condition for *even*: the sentence without
*even* must be more surprising than most of its contextually determined true neighbors, against
[bennett-1982]'s one neighbor and [karttunen-peters-1979]'s all. The three conditions are one
threshold on the number of neighbors the prejacent surpasses (`Meets`); they are ordered
(`meets_most_of_universal`, `meets_existential_of_most`), and the paper's two counterexamples
are the two gaps between them: surpassing exactly one of several neighbors meets Bennett's
condition but not the majority (`not_meets_most_of_one`), and surpassing all but one meets the
majority but not Karttunen and Peters' (`meets_most_of_all_but_one`). The universal threshold
is the scalar presupposition `Focus.Particles.evenPresup`.

## Implementation notes

Neighbors are a list of alternatives with a surprise comparison, and the thresholds read the
count of neighbors the prejacent surpasses, so the vagueness of *most* is the threshold itself;
the paper's second gradient, the margin of surprise, is not formalized. The rows record the
paper's scenarios by the counts its descriptions fix: how many neighbors the prejacent surpasses
and how many there are.

## References

* [francescotti-1995]
* [bennett-1982]
* [karttunen-peters-1979]
* [kay-1990]
* [lycan-1991]
-/

@[expose] public section

namespace Francescotti1995

open Focus.Particles

/-- How many true neighbors the prejacent must surpass in surprise: at least one, all, or
most. -/
inductive Threshold
  | existential
  | universal
  | most
  deriving DecidableEq, Repr

/-- Surpassing `k` of `n` neighbors meets the threshold. -/
def Meets : Threshold → ℕ → ℕ → Prop
  | .existential, k, _ => 0 < k
  | .universal, k, n => k = n
  | .most, k, n => n < 2 * k

instance (t : Threshold) (k n : ℕ) : Decidable (Meets t k n) := by
  unfold Meets; cases t <;> infer_instance

theorem meets_most_of_universal {k n : ℕ} (hn : 0 < n) (h : Meets .universal k n) :
    Meets .most k n := by
  simp only [Meets] at h ⊢; omega

theorem meets_existential_of_most {k n : ℕ} (h : Meets .most k n) : Meets .existential k n := by
  simp only [Meets] at h ⊢; omega

theorem not_meets_most_of_one {n : ℕ} (hn : 2 ≤ n) :
    Meets .existential 1 n ∧ ¬ Meets .most 1 n := by
  simp only [Meets]; omega

theorem meets_most_of_all_but_one {n : ℕ} (hn : 3 ≤ n) :
    Meets .most (n - 1) n ∧ ¬ Meets .universal (n - 1) n := by
  simp only [Meets]; omega

theorem not_meets_most_of_half {k : ℕ} : ¬ Meets .most k (2 * k) := by
  simp only [Meets]; omega

section Neighbors

variable {α : Type*} (prejacent : α) (neighbors : List α) (moreSurprising : α → α → Prop)
  [DecidableRel moreSurprising]

/-- The number of neighbors the prejacent surpasses in surprise. -/
def surpassed : ℕ := neighbors.countP λ a => decide (moreSurprising prejacent a)

/-- The felicity condition at a threshold. -/
def Felicitous (t : Threshold) : Prop :=
  Meets t (surpassed prejacent neighbors moreSurprising) neighbors.length

theorem surpassed_le : surpassed prejacent neighbors moreSurprising ≤ neighbors.length :=
  List.countP_le_length

theorem felicitous_existential_iff :
    Felicitous prejacent neighbors moreSurprising .existential ↔
      ∃ a ∈ neighbors, moreSurprising prejacent a := by
  simp [Felicitous, Meets, surpassed, List.countP_pos_iff]

theorem felicitous_universal_iff :
    Felicitous prejacent neighbors moreSurprising .universal ↔
      ∀ a ∈ neighbors, moreSurprising prejacent a := by
  simp [Felicitous, Meets, surpassed, List.countP_eq_length]

theorem evenPresup_iff_universal {W α : Type*} [PartialOrder α]
    [DecidableRel (α := α) (· < ·)] (μ : Set W → α) (p : Set W) (alts : List (Set W)) :
    evenPresup μ p {q | q ∈ alts} ↔ Felicitous p alts (μ · < μ ·) .universal :=
  (felicitous_universal_iff p alts (μ · < μ ·)).symm

end Neighbors

/-! ### The paper's scenarios -/

/-- A scenario of the data: how many true neighbors the prejacent surpasses in surprise, how many
there are, and whether the *even*-sentence is felicitous. -/
structure Row where
  surpassed : ℕ
  neighbors : ℕ
  felicitous : Bool
  deriving DecidableEq

def Row.ofDatum (ex : Datum) : Option Row := do
  let k ← ex.nat? "surpassed"
  let n ← ex.nat? "neighbors"
  let f ← ex.parse? "felicitous" [("yes", true), ("no", false)]
  pure ⟨k, n, f⟩

def rows : List Row := Examples.all.filterMap Row.ofDatum

theorem rows_most : ∀ r ∈ rows, (r.felicitous = true ↔ Meets .most r.surpassed r.neighbors) := by
  decide

theorem rows_not_existential :
    ¬ ∀ r ∈ rows, (r.felicitous = true ↔ Meets .existential r.surpassed r.neighbors) := by
  decide

theorem rows_not_universal :
    ¬ ∀ r ∈ rows, (r.felicitous = true ↔ Meets .universal r.surpassed r.neighbors) := by
  decide

end Francescotti1995
