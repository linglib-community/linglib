/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Order.Setoid.Basic
public import Mathlib.Order.Monotone.Defs
public import Linglib.Logic.Modal.Defs
public import Linglib.Logic.Modal.Index

/-!
# T × W tense-modal logic: frames, language and satisfaction

A *T × W frame* is a family of equivalence relations on worlds indexed by times, *historical
equivalence*, that is antitone in the time. This file defines frames (`TWFrame`), the formulas
of T × W logic (`Formula`), with the tenses `G` and `H`, historical necessity `N` and necessity
over all worlds `box`, and satisfaction at a world–time index (`TWFrame.sat`), where each
operator is necessity along a relation between indices.

## Implementation notes

* [von-kutschera-1997] takes negation and material implication as the primitive connectives;
  `Formula` takes negation and conjunction, with `Formula.imp` and `Formula.or` derived.
* The sources order time linearly. A frame here is over any preorder, and the theorems that
  need linearity assume it.

## References

* [thomason-1984]
* [von-kutschera-1997]
-/

@[expose] public section

namespace Temporal

/-- A *T × W frame* on worlds `World` and times `T` is an antitone family of equivalence relations
on `World` indexed by `T` ([thomason-1984], [von-kutschera-1997]). -/
structure TWFrame (World T : Type*) [Preorder T] where
  /-- Historical equivalence `∼ₜ`, relating worlds that share their history up to `t`. -/
  sim : T → Setoid World
  /-- Worlds that share their history up to a time share it up to every earlier time. -/
  antitone_sim : Antitone sim

namespace TWFrame

variable {T World : Type*} [Preorder T]

/-- `F.alt t` is historical equivalence at `t` as a relation between worlds. -/
def alt (F : TWFrame World T) (t : T) : SetRel World World := {(w, v) | F.sim t w v}

/-- The frame in which two worlds are historically equivalent at `t` when they agree on every
fact dated at or before `t`. -/
def ofDatedFacts {Fact : Type*} (time : Fact → T) (holds : World → Fact → Prop) :
    TWFrame World T where
  sim t := ⟨fun w w' ↦ ∀ f, time f ≤ t → (holds w f ↔ holds w' f),
    ⟨fun _ _ _ ↦ Iff.rfl, fun h f hf ↦ (h f hf).symm, fun h₁ h₂ f hf ↦ (h₁ f hf).trans (h₂ f hf)⟩⟩
  antitone_sim _ _ hle _ _ h f hf := h f (hf.trans hle)

end TWFrame

/-- The formulas of T × W logic ([von-kutschera-1997] §1). -/
inductive Formula (Atom : Type*) where
  /-- A sentential constant. -/
  | atom : Atom → Formula Atom
  /-- Negation. -/
  | neg : Formula Atom → Formula Atom
  /-- Conjunction. -/
  | and : Formula Atom → Formula Atom → Formula Atom
  /-- `G` — "it will always be that" (∀ later times, same world). -/
  | G : Formula Atom → Formula Atom
  /-- `H` — "it has always been that" (∀ earlier times, same world). -/
  | H : Formula Atom → Formula Atom
  /-- `N` — historical necessity (∀ `∼ₜ`-alternatives, same time). -/
  | N : Formula Atom → Formula Atom
  /-- `box` — truth in all worlds (von Kutschera's `N₄`). -/
  | box : Formula Atom → Formula Atom
  deriving DecidableEq

namespace TWFrame

variable {T World Atom : Type*} [Preorder T]

/-- `F.historical` relates an index `⟨w, t⟩` to the indices `⟨v, t⟩` with `v` historically
equivalent to `w` at `t`. -/
abbrev historical (F : TWFrame World T) : SetRel (Index World T) (Index World T) :=
  Index.modal F.alt

end TWFrame

/-- `Index.future` relates an index `⟨w, t⟩` to the indices `⟨w, u⟩` with `t < u`. -/
abbrev _root_.Index.future {World T : Type*} [LT T] : SetRel (Index World T) (Index World T) :=
  Index.temporal {x : T × T | x.1 < x.2}

/-- `Index.past` relates an index `⟨w, t⟩` to the indices `⟨w, u⟩` with `u < t`. -/
abbrev _root_.Index.past {World T : Type*} [LT T] : SetRel (Index World T) (Index World T) :=
  Index.temporal {x : T × T | x.2 < x.1}

@[simp] theorem _root_.Index.inv_past {World T : Type*} [LT T] :
    (Index.past : SetRel (Index World T) (Index World T)).inv = Index.future := by
  rw [Index.inv_temporal]
  rfl

@[simp] theorem _root_.Index.inv_future {World T : Type*} [LT T] :
    (Index.future : SetRel (Index World T) (Index World T)).inv = Index.past := by
  rw [Index.inv_temporal]
  rfl

namespace TWFrame

variable {T World Atom : Type*} [Preorder T]

open scoped ModalLogic in
/-- `F.sat V a i` is the truth of the formula `a` at the index `i` under the valuation `V`. The
operators `G`, `H`, `N` and `box` are necessity along `Index.future`, `Index.past`,
`F.historical` and the relation between all indices at one time. -/
def sat (F : TWFrame World T) (V : Atom → T → World → Prop) :
    Formula Atom → Index World T → Prop
  | .atom p,  i => V p i.time i.world
  | .neg a,   i => ¬ F.sat V a i
  | .and a b, i => F.sat V a i ∧ F.sat V b i
  | .G a,     i => □[Index.future] (F.sat V a) i
  | .H a,     i => □[Index.past] (F.sat V a) i
  | .N a,     i => □[F.historical] (F.sat V a) i
  | .box a,   i => □[Index.modal fun _ ↦ .univ] (F.sat V a) i

end TWFrame

/-! ### Derived (dual) operators -/

variable {Atom : Type*}

/-- Historical possibility, `¬N¬`. -/
def Formula.M (a : Formula Atom) : Formula Atom := .neg (.N (.neg a))

/-- The future tense `F`, `¬G¬`. -/
def Formula.Fut (a : Formula Atom) : Formula Atom := .neg (.G (.neg a))

/-- The past tense `P`, `¬H¬`. -/
def Formula.Pst (a : Formula Atom) : Formula Atom := .neg (.H (.neg a))

/-- Possibility over all worlds, `¬□¬`. -/
def Formula.dia (a : Formula Atom) : Formula Atom := .neg (.box (.neg a))

/-- Material implication, `¬(a ∧ ¬b)`. -/
def Formula.imp (a b : Formula Atom) : Formula Atom := .neg (.and a (.neg b))

/-- Disjunction, `¬(¬a ∧ ¬b)`. -/
def Formula.or (a b : Formula Atom) : Formula Atom := .neg (.and (.neg a) (.neg b))

end Temporal
