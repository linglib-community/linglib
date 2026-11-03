/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Order.Setoid.Basic
public import Mathlib.Order.Monotone.Defs
public import Linglib.Logic.Modal.Defs
public import Linglib.Semantics.Tense.Defs

/-!
# T × W tense-modal logic: frames, language and satisfaction

A T × W frame has worlds sharing one time order and, at each time, historical equivalence, an
equivalence relation on worlds, agreement up to that time, that gets finer as time advances. Its
object language has the linear tenses `G` and `H`, historical necessity `N` along historical
equivalence and `box` over all worlds. Each of the four is necessity along a relation, so the
logic is a multimodal Kripke logic by construction.

## Main definitions

* `TWFrame`: a frame, with historical equivalence an antitone family of setoids.
* `TWFrame.alt`: historical equivalence at a time as an accessibility relation.
* `TWFrame.ofDatedFacts`: the frame of worlds agreeing on the facts dated by each time.
* `OForm`, `TWFrame.sat`: the object language and satisfaction.
* `OForm.M`, `OForm.Fut`, `OForm.Pst`, `OForm.dia`: the dual operators.

## References

* [thomason-1984]
* [von-kutschera-1997]
* [dimaio-zanardo-1994]
-/

@[expose] public section


namespace Temporal

universe u v

/-- A T × W frame ([thomason-1984], [von-kutschera-1997]) has, at each time, historical
equivalence on worlds, which gets finer as time advances. -/
structure TWFrame (World : Type v) (T : Type u) [Preorder T] where
  /-- Historical equivalence `∼ₜ`, relating worlds that share their history up to `t`. -/
  sim : T → Setoid World
  /-- Worlds that share their history up to a time share it up to every earlier time. -/
  antitone_sim : Antitone sim

namespace TWFrame

variable {T : Type u} {World : Type v} [Preorder T]

/-- Historical equivalence at `t` as an accessibility relation. -/
def alt (F : TWFrame World T) (t : T) : SetRel World World := {p | F.sim t p.1 p.2}

/-- Over a stock of dated facts, worlds are historically equivalent up to a time when they agree
on every fact dated at or before it, the world–time model of [thomason-1984]. -/
def ofDatedFacts {Fact : Type*} (time : Fact → T) (holds : World → Fact → Prop) :
    TWFrame World T where
  sim t := ⟨fun w w' ↦ ∀ f, time f ≤ t → (holds w f ↔ holds w' f),
    ⟨fun _ _ _ ↦ Iff.rfl, fun h f hf ↦ (h f hf).symm, fun h₁ h₂ f hf ↦ (h₁ f hf).trans (h₂ f hf)⟩⟩
  antitone_sim _ _ hle _ _ h f hf := h f (hf.trans hle)

end TWFrame

/-- The object language `L` of T × W logic ([von-kutschera-1997] §1). -/
inductive OForm (Atom : Type*) where
  /-- A sentential constant. -/
  | atom : Atom → OForm Atom
  /-- Negation. -/
  | neg : OForm Atom → OForm Atom
  /-- Conjunction. -/
  | and : OForm Atom → OForm Atom → OForm Atom
  /-- `G` — "it will always be that" (∀ later times, same world). -/
  | G : OForm Atom → OForm Atom
  /-- `H` — "it has always been that" (∀ earlier times, same world). -/
  | H : OForm Atom → OForm Atom
  /-- `N` — historical necessity (∀ `∼ₜ`-alternatives, same time). -/
  | N : OForm Atom → OForm Atom
  /-- `box` — truth in all worlds (von Kutschera's `N₄`). -/
  | box : OForm Atom → OForm Atom
  deriving DecidableEq

namespace TWFrame

variable {T : Type u} {World : Type v} {Atom : Type*} [Preorder T]

open scoped ModalLogic Denotes in
/-- Satisfaction `V_{t,w}(A)` ([von-kutschera-1997]) relative to an atomic valuation `V`.
    `G`/`H`/`N`/`box` are the Kripke boxes `□` along, respectively, the relations of the future
    and past tense cells, historical equivalence `sim t`, and the universal relation — making the
    object logic a multimodal Kripke logic by construction. -/
def sat (F : TWFrame World T) (V : Atom → T → World → Prop) :
    OForm Atom → T → World → Prop
  | .atom p,  t, w => V p t w
  | .neg a,   t, w => ¬ F.sat V a t w
  | .and a b, t, w => F.sat V a t w ∧ F.sat V b t w
  | .G a,     t, w => □[Tense.toSetRel ⟦Tense.future⟧] (fun t' => F.sat V a t' w) t
  | .H a,     t, w => □[Tense.toSetRel ⟦Tense.past⟧] (fun t' => F.sat V a t' w) t
  | .N a,     t, w => □[F.alt t] (fun w' => F.sat V a t w') w
  | .box a,   t, w => □[.univ] (fun w' => F.sat V a t w') w

/-- In a model `a` entails `b` when `b` holds wherever `a` does. -/
def entails (F : TWFrame World T) (V : Atom → T → World → Prop) (a b : OForm Atom) : Prop :=
  ∀ t w, F.sat V a t w → F.sat V b t w

end TWFrame

/-! ### Derived (dual) operators -/

variable {Atom : Type*}

/-- Historical possibility `M = ¬N¬` (the Ockhamist `◇`). -/
def OForm.M (a : OForm Atom) : OForm Atom := .neg (.N (.neg a))

/-- Tense `F` — "it will at some point be that" (`¬G¬`). -/
def OForm.Fut (a : OForm Atom) : OForm Atom := .neg (.G (.neg a))

/-- Tense `P` — "it was at some point that" (`¬H¬`). -/
def OForm.Pst (a : OForm Atom) : OForm Atom := .neg (.H (.neg a))

/-- Possibility in all worlds `◇ = ¬□¬`. -/
def OForm.dia (a : OForm Atom) : OForm Atom := .neg (.box (.neg a))

end Temporal
