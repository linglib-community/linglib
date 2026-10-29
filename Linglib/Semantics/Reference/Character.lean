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

Given the world, or more generally the index, of each context, a character has a *diagonal*: the
value at each context of what is said there, evaluated at the context's own index
(`Character.diag`). For a sentence it is truth at a context, and when the contexts are the
worlds themselves it is the diagonal proposition of [stalnaker-1978]'s propositional concepts. A
sentence is *a priori*, valid in Kaplan's logic of demonstratives, when its diagonal holds at
every context, and *necessary at a context* when what it says there is true at every world. The
two notions come apart in both directions: an a priori sentence can say something contingent,
and a sentence necessary at a context need not be a priori; a sentence necessary at every context
is a priori (`Character.IsNecessary.isAPriori`).

## Main definitions

* `Character C W E`, `Content W E`
* `Character.IsDirectlyReferential`
* `Character.dthat`, `Character.const`
* `Character.diag`: the diagonal along the index of the context.
* `Character.IsAPriori`, `Character.IsNecessaryAt`, `Character.IsNecessary`

## References

* [kaplan-1989]
* [kripke-1980]
* [stalnaker-1978]
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

/-! ### The diagonal -/

/-- The diagonal of a character along `ι`, the index of each context, is the value at each
context of what is said there, at the context's own index: the truth of a sentence at a context,
and the diagonal proposition when contexts are worlds. -/
def diag (ι : C → W) (χ : Character C W E) : C → E := fun c ↦ χ c (ι c)

@[simp] theorem diag_apply (ι : C → W) (χ : Character C W E) (c : C) : χ.diag ι c = χ c (ι c) :=
  rfl

@[simp] theorem diag_dthat (ι : C → W) (f : C → E) : (dthat f : Character C W E).diag ι = f := rfl

@[simp] theorem diag_const (ι : C → W) (e : E) :
    (const e : Character C W E).diag ι = fun _ ↦ e :=
  rfl

/-! ### A priori and necessary truth -/

/-- A sentence is a priori, valid in the logic of demonstratives, when its diagonal holds at every
context. -/
def IsAPriori (ι : C → W) (χ : Character C W Prop) : Prop := ∀ c, χ.diag ι c

/-- A sentence is necessary at a context when what it says there is true at every world. -/
def IsNecessaryAt (χ : Character C W Prop) (c : C) : Prop := ∀ w, χ c w

/-- A sentence is necessary when what it says at every context is true at every world. -/
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

end Kaplan
