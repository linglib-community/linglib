module

public import Linglib.Logic.Assignment
public import Mathlib.Logic.Function.DependsOn

/-!
# Assignment-relative denotations

This file defines the denotation of binders relative to a variable assignment `g : ℕ → E`, which
gives each index a value. In the textbook of Heim and Kratzer, the Traces and Pronouns Rule has a
pronoun or trace with index `n` denote `g n`, the evaluation `Function.eval n` of the assignment,
and Predicate Abstraction has a binder at `n` abstract over the value of `n` by updating `g`. An
assignment-relative denotation in `α` is a function `Assignment E → α`, a computation of Lean's
reader monad `ReaderM (Assignment E)`. Charlow factors the standard theory through this monad: its
`pure`, `<*>` and `joinM` are his lift `ρ`, application `⊛` and flattener `μ`, and `lambdaAbsG` is
his categorematic abstraction `Λᵢ`.

The indices a denotation reads are those it depends on, in the sense of mathlib's `DependsOn`. An
abstraction over `n` reads the indices its body reads other than `n`, and abstracting over an
index the body does not read gives a constant function.

## Main definitions

* `lambdaAbsG`: abstraction over an index.

## Main results

* `dependsOn_lambdaAbsG`: abstraction over `n` removes `n` from the indices a body depends on.
* `lambdaAbsG_eq_const_iff`: abstraction over `n` is constant at every assignment exactly when
  the body does not depend on `n`.

## Implementation notes

Assignments are total, where Heim and Kratzer's are partial, so a pronoun denotes at every
assignment. Nothing fixes `E` to entities: at an assignment of situations, a pronoun is a
situation pronoun.

## References

* [I. Heim, A. Kratzer, *Semantics in Generative Grammar* (1998)][heim-kratzer-1998]
* [S. Charlow, *A modular theory of pronouns and binding* (2018)][charlow-2018]
-/

@[expose] public section

namespace Montague

open Function
open scoped Assignment

variable {E α : Type*} {n : ℕ}

/-- `lambdaAbsG n body` is the abstraction of `body` over index `n`, which at the assignment `g`
maps `x` to the value of `body` at `g[n ↦ x]`. -/
def lambdaAbsG (n : ℕ) (body : Assignment E → α) : Assignment E → E → α :=
  fun g x ↦ body (g[n ↦ x])

@[simp]
theorem lambdaAbsG_apply (body : Assignment E → α) (g : Assignment E) (x : E) :
    lambdaAbsG n body g x = body (g[n ↦ x]) := rfl

/-- Abstraction over `n` binds `n`, so the abstract depends only on the indices other than `n`
that its body depends on. -/
theorem dependsOn_lambdaAbsG {s : Set ℕ} {body : Assignment E → α} (h : DependsOn body s)
    (n : ℕ) : DependsOn (lambdaAbsG n body) (s \ {n}) := by
  refine fun g g' hg ↦ funext fun x ↦ h fun i hi ↦ ?_
  obtain rfl | hin := eq_or_ne i n
  · simp
  · simp [update_of_ne hin, hg i ⟨hi, hin⟩]

/-- Abstraction over `n` is vacuous, the constant function at the body's value at every
assignment, exactly when the body does not depend on `n`. -/
theorem lambdaAbsG_eq_const_iff {body : Assignment E → α} :
    (∀ g, lambdaAbsG n body g = const E (body g)) ↔ DependsOn body {n}ᶜ := by
  refine ⟨fun h g g' hg ↦ ?_, fun h g ↦ funext fun x ↦ h fun i hi ↦ update_of_ne hi ..⟩
  rw [(eq_update_iff.2 ⟨rfl, hg⟩ : g = g'[n ↦ g n])]
  exact congrFun (h g') (g n)

end Montague
