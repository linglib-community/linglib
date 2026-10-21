/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.Reference.Rigidity

/-!
# Characters

A *character* is a function from contexts to contents, a content being an intension from
worlds to extensions: the two-stage semantics of [kaplan-1989], on which the linguistic
meaning of an expression fixes, at each context of utterance, what the expression says there.
A character is *directly referential* when its content at every context is rigid
(`Character.IsDirectlyReferential`). Kaplan's rigidifier `dthat` makes a directly referential
character out of any context-dependent choice of individual (`Character.dthat`): the pure
indexicals are its instances at a coordinate of the context, and `dthat` of a description
evaluated at the context world is Kaplan's `dthat[the φ]`. A proper name has the constant
character (`Character.const`), rigid also as a function of the context in the sense of
`IsRigid`.

## Main definitions

* `Character C W E`, `Content W E`
* `Character.IsDirectlyReferential`
* `Character.dthat`, `Character.const`

## References

* [kaplan-1989]
* [kripke-1980]
-/

@[expose] public section

namespace Kaplan

/-- A content is an intension from worlds to extensions, what an expression says at a context. -/
abbrev Content (W E : Type*) := W → E

/-- A Kaplanian character is the linguistic meaning of an expression, assigning a content to each
context. -/
abbrev Character (C W E : Type*) := C → Content W E

namespace Character

variable {C W E : Type*}

/-- A character is directly referential when its content at every context is rigid. -/
def IsDirectlyReferential (χ : Character C W E) : Prop := ∀ c, IsRigid (χ c)

/-- Kaplan's rigidifier is the character that at context `c` rigidly designates `f c`. -/
def dthat (f : C → E) : Character C W E := fun c _ ↦ f c

/-- The constant character at `e` is the character of a proper name for `e`. -/
def const (e : E) : Character C W E := fun _ _ ↦ e

@[simp] theorem dthat_apply (f : C → E) (c : C) (w : W) :
    (dthat f : Character C W E) c w = f c :=
  rfl

@[simp] theorem const_apply (e : E) (c : C) (w : W) : (const e : Character C W E) c w = e := rfl

theorem dthat_isDirectlyReferential (f : C → E) :
    (dthat f : Character C W E).IsDirectlyReferential :=
  fun c ↦ isRigid_const (f c)

theorem const_isDirectlyReferential (e : E) :
    (const e : Character C W E).IsDirectlyReferential :=
  dthat_isDirectlyReferential _

/-- Rigidifying at a context differs from the description whenever the description varies. -/
theorem dthat_ne {f : W → E} {w₀ w₁ : W} (h : f w₁ ≠ f w₀) :
    (dthat f : Character W W E) w₀ ≠ f :=
  fun e ↦ h (congrFun e w₁).symm

end Character

end Kaplan
