/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.Reference.Rigidity

/-!
# Characters

This file defines characters. Let `C` be a type of contexts, `W` a type of worlds and `E` a type
of values. A content is a function `W → E`, and a character is a function `C → W → E`, which
gives the content of an expression at each context. For a sentence `E` is `Prop`, and its content
at a context is a proposition.

For example, the sentence *I am hungry* has a character that sends a context `c` and a world `w`
to the proposition that the agent of `c` is hungry in `w`. When Ann says it, its content is that
Ann is hungry, and when Bo says it, its content is that Bo is hungry.

A character is directly referential if its content at every context is rigid, that is, has the
same value at every world. Let `ι : C → W` give the world of each context. The diagonal of a
character `χ` along `ι` sends a context `c` to the value of `χ` at `c` and `ι c`. A sentence is a
priori if its diagonal holds at every context, and it is necessary at a context if its content
there holds at every world.

## Main definitions

* `Character C W E`: the type `C → W → E` of characters.
* `Character.IsDirectlyReferential χ`: the content `χ c` is rigid for every context `c`.
* `Character.dthat f`: the character whose content at a context `c` has the value `f c` at every
  world.
* `Character.const e`: the character with the value `e` at every context and world.
* `Character.diag ι χ`: the function `fun c ↦ χ c (ι c)`.
* `Character.IsAPriori ι χ`: the diagonal of `χ` along `ι` holds at every context.
* `Character.IsNecessaryAt χ c`: the content `χ c` holds at every world.
* `Character.IsNecessary χ`: `χ` is necessary at every context.

## Main results

* `Character.dthat_isDirectlyReferential`: the character `dthat f` is directly referential.
* `Character.IsNecessary.isAPriori`: a necessary sentence is a priori.

## Implementation notes

A character and a content are the functions that represent them in Kaplan's formal system. Two
expressions with the same value at every context and world have the same character here. A
difference of linguistic meaning finer than that, which structured characters and structured
propositions are meant to capture, is not represented.

The type `W` may be any type of indices. Stalnaker's propositional concepts are the characters
whose contexts are the worlds themselves.

## References

* [kaplan-1989]
* [kripke-1980]
* [stalnaker-1978]
-/

@[expose] public section


/-- A **character** is a function from contexts to contents, where a **content** is a function
from worlds to values. It represents the linguistic meaning of an expression, which fixes what the
expression says at each context. -/
abbrev Character (C W E : Type*) := C → W → E

namespace Character

variable {C W E : Type*}

/-- A character is **directly referential** if its content at every context is rigid. -/
def IsDirectlyReferential (χ : Character C W E) : Prop := ∀ c, IsRigid (χ c)

/-- The **rigidifier** `dthat f` is the character whose content at a context `c` has the value
`f c` at every world. -/
def dthat (f : C → E) : Character C W E := fun c _ ↦ f c

/-- The **constant character** at `e` has the value `e` at every context and world. It is the
character of a proper name for `e`. -/
def const (e : E) : Character C W E := fun _ _ ↦ e

@[simp] theorem dthat_apply (f : C → E) (c : C) (w : W) :
    (dthat f : Character C W E) c w = f c :=
  rfl

@[simp] theorem const_apply (e : E) (c : C) (w : W) : (const e : Character C W E) c w = e := rfl

theorem dthat_isDirectlyReferential (f : C → E) :
    (dthat f : Character C W E).IsDirectlyReferential :=
  fun c ↦ Function.IsConst.const (f c)

theorem const_isDirectlyReferential (e : E) :
    (const e : Character C W E).IsDirectlyReferential :=
  dthat_isDirectlyReferential _

/-! ### The diagonal -/

/-- The **diagonal** of a character `χ` along `ι`, where `ι c` is the world of the context `c`,
sends `c` to the value of `χ` at `c` and `ι c`. For a sentence it holds at the contexts where the
sentence, said there, is true. -/
def diag (ι : C → W) (χ : Character C W E) : C → E := fun c ↦ χ c (ι c)

@[simp] theorem diag_apply (ι : C → W) (χ : Character C W E) (c : C) : χ.diag ι c = χ c (ι c) :=
  rfl

@[simp] theorem diag_dthat (ι : C → W) (f : C → E) : (dthat f : Character C W E).diag ι = f := rfl

@[simp] theorem diag_const (ι : C → W) (e : E) :
    (const e : Character C W E).diag ι = fun _ ↦ e :=
  rfl

/-! ### A priori and necessary truth -/

/-- A sentence is **a priori** if its diagonal holds at every context. A sentence is valid in
Kaplan's logic of demonstratives if it is a priori in every structure. -/
def IsAPriori (ι : C → W) (χ : Character C W Prop) : Prop := ∀ c, χ.diag ι c

/-- A sentence is **necessary at a context** `c` if its content at `c` holds at every world. -/
def IsNecessaryAt (χ : Character C W Prop) (c : C) : Prop := ∀ w, χ c w

/-- A sentence is **necessary** if it is necessary at every context. -/
def IsNecessary (χ : Character C W Prop) : Prop := ∀ c w, χ c w

theorem isNecessary_iff_forall_isNecessaryAt {χ : Character C W Prop} :
    χ.IsNecessary ↔ ∀ c, χ.IsNecessaryAt c :=
  Iff.rfl

theorem IsNecessaryAt.diag {χ : Character C W Prop} {c : C} (h : χ.IsNecessaryAt c)
    (ι : C → W) : χ.diag ι c :=
  h _

theorem IsNecessary.isAPriori {χ : Character C W Prop} (h : χ.IsNecessary) (ι : C → W) :
    χ.IsAPriori ι :=
  fun c ↦ h c _

end Character

