module

public import Linglib.Logic.Assignment
public import Mathlib.Logic.Function.DependsOn

/-!
# Assignment-relative denotations

This file defines the denotations of pronouns and binders relative to a variable assignment
`g : ℕ → E`, which gives each index a value. In the textbook of Heim and Kratzer, the Traces and
Pronouns Rule has a pronoun or trace with index `n` denote `g n`, and Predicate Abstraction has a
binder at `n` abstract over the value of `n` by updating `g`. An assignment-relative denotation in
`α` is a function `Assignment E → α`, a computation of Lean's reader monad
`ReaderM (Assignment E)`. Charlow factors the standard theory through this monad: its `pure`,
`<*>` and `joinM` are his lift `ρ`, application `⊛` and flattener `μ`, and `lambdaAbsG` is his
categorematic abstraction `Λᵢ`.

The indices a denotation reads are those it depends on, in the sense of mathlib's `DependsOn`. A
pronoun reads its own index, an abstraction over `n` reads the indices its body reads other than
`n`, and abstracting over an index the body does not read gives a constant function.

## Main definitions

* `interpPronoun`: the denotation of a pronoun or trace.
* `lambdaAbsG`: abstraction over an index.

## Main results

* `dependsOn_interpPronoun`: a pronoun depends only on its index.
* `dependsOn_lambdaAbsG`: abstraction over `n` removes `n` from the indices a body depends on.
* `lambdaAbsG_eq_const_iff`: abstraction over `n` is constant at every assignment exactly when
  the body does not depend on `n`.

## Implementation notes

Assignments are total, where Heim and Kratzer's are partial, so a pronoun denotes at every
assignment. Nothing fixes `E` to entities: at an assignment of situations, `interpPronoun`
is a situation pronoun.

## References

* [I. Heim, A. Kratzer, *Semantics in Generative Grammar* (1998)][heim-kratzer-1998]
* [S. Charlow, *A modular theory of pronouns and binding* (2018)][charlow-2018]
-/

@[expose] public section

namespace Montague

open Function
open scoped Assignment

variable {E α : Type*} {n : ℕ}

/-- `interpPronoun n` is the denotation of a pronoun or trace with index `n`, the value `g n` of
the index under the assignment `g`. -/
def interpPronoun (n : ℕ) : Assignment E → E := fun g ↦ g n

@[simp]
theorem interpPronoun_apply (g : Assignment E) : interpPronoun n g = g n := rfl

/-- `lambdaAbsG n body` is the abstraction of `body` over index `n`, which at the assignment `g`
maps `x` to the value of `body` at `g[n ↦ x]`. -/
def lambdaAbsG (n : ℕ) (body : Assignment E → α) : Assignment E → E → α :=
  fun g x ↦ body (g[n ↦ x])

@[simp]
theorem lambdaAbsG_apply (body : Assignment E → α) (g : Assignment E) (x : E) :
    lambdaAbsG n body g x = body (g[n ↦ x]) := rfl

/-- A pronoun depends only on its index. -/
theorem dependsOn_interpPronoun (n : ℕ) : DependsOn (interpPronoun (E := E) n) {n} :=
  fun _ _ h ↦ h n rfl

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
