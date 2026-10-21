/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins

[UPSTREAM] candidate: `Mathlib.Computability.TransitionMonoid`.
-/
module

public import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Submonoid.Operations
public import Mathlib.Basic.Finite.Prod
public import Mathlib.Computability.DFA

/-!
# The transition monoid of a DFA

Each word induces a transformation of the states of a DFA, and reading one word after another
composes these transformations. The monoid they generate is the *transition monoid*, the basic
algebraic invariant of an automaton. It is finite when the automaton is.

## Main definitions

- `DFA.transitionHom`: the monoid homomorphism sending a word to the transformation it induces
- `DFA.transitionMonoid`: the transition monoid, the range of `DFA.transitionHom`

## Main results

- `DFA.instFiniteTransitionMonoid`: the transition monoid of a finite-state DFA is finite

## Implementation notes

A word `w` acts on a state `s` by `s ↦ M.evalFrom s w`, and `evalFrom_of_append` makes this a
*right* action, written `q · u` in the literature. Since `Function.End` composes on the left, that
is an anti-homomorphism, so the target of `DFA.transitionHom` is the opposite monoid
`(Function.End σ)ᵐᵒᵖ`. Its domain stays `FreeMonoid α`, so that its kernel is a congruence on
words, comparable with the syntactic congruence.

Pin's deterministic automata are partial, so the transition monoid there sits in the monoid of
*partial* transformations. `DFA` has a total `step`, so the transformations here are total.

## References

* [pin-mfa]
-/

@[expose] public section

namespace DFA

variable {α σ : Type*} (M : DFA α σ)

/-- `M.transitionHom w` is the transformation of states induced by the word `w`. -/
def transitionHom : FreeMonoid α →* (Function.End σ)ᵐᵒᵖ where
  toFun w := .op fun s ↦ M.evalFrom s w.toList
  map_one' := rfl
  map_mul' _ _ := MulOpposite.unop_injective <| funext fun s ↦ M.evalFrom_of_append s _ _

@[simp]
theorem unop_transitionHom_apply (w : FreeMonoid α) (s : σ) :
    (M.transitionHom w).unop s = M.evalFrom s w.toList := rfl

theorem transitionHom_eq_iff {u v : FreeMonoid α} : M.transitionHom u = M.transitionHom v ↔
    ∀ s : σ, M.evalFrom s u.toList = M.evalFrom s v.toList :=
  MulOpposite.unop_inj.symm.trans funext_iff

/-- `M.transitionMonoid` is the monoid of transformations of the states of `M` induced by words. -/
def transitionMonoid : Submonoid (Function.End σ)ᵐᵒᵖ := MonoidHom.mrange M.transitionHom

instance instFiniteTransitionMonoid [Finite σ] : Finite M.transitionMonoid :=
  .of_injective (β := σ → σ) (·.1.unop) fun _ _ h ↦ Subtype.ext (MulOpposite.unop_injective h)

end DFA
