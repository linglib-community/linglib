/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Derivation.Replay

/-!
# Licensing a derivation

A licensing of Merge gives each lexical item a state in a commutative magma with zero, `0` being
the failure of Merge, and the trace of a moved object a state that depends on the object's own.
Over a derivation whose traces are numbered by its movers, a licensing [extends to a morphism of
magmas](##Minimalist.Licensing.hom), and the derivation is licensed, `Derivation.LicensedBy`, when
every stage is in its domain, the object under construction and every copy extracted from it. The
derived object alone does not show this: a moved item leaves a trace, so whether it was merged
before it was saturated shows only at the stages before it moved. A morphism of licensings
[commutes with their extensions](##Minimalist.Licensing.comp_hom), so [the finer licensing licenses
what the coarser one does](##Minimalist.Derivation.LicensedBy.of_hom).

## Implementation notes

* The bare trace and a trace numbered past the movers name no object and are read as `0`.
-/

@[expose] public section

namespace Minimalist

open SyntacticObject

variable {β γ : Type*} [CommMagma β] [Zero β] [CommMagma γ] [Zero γ]

/-- A licensing of Merge into `β`: the state of a lexical item, and the state of the trace a moved
object leaves, given the object's own. -/
structure Licensing (β : Type*) where
  /-- The state of a lexical item. -/
  lex : LexicalItem.Token → β
  /-- The state of the trace of a moved object in the given state. -/
  trace : β → β

namespace Licensing

variable (L : Licensing β) (L' : Licensing γ)

/-- The morphism a licensing gives once its numbered traces have states. -/
def eval (states : List β) : SyntacticObject (ι := ℕ) →ₙ* β :=
  FreeCommMagma.lift (Leaf.elim L.lex fun u ↦ (u.bind (states[·]?)).getD 0)

/-- The states of the traces of the objects moved, in order: each the trace of its object, read
with the traces of the objects moved before it. -/
def traceStates (movers : List (SyntacticObject (ι := ℕ))) : List β :=
  movers.foldl (fun states m ↦ states ++ [L.trace (L.eval states m)]) []

/-- A licensing over a derivation: the morphism of magmas reading each lexical item by its state
and each numbered trace as the trace of the mover it numbers. -/
def hom (d : Derivation ℕ) : SyntacticObject (ι := ℕ) →ₙ* β :=
  L.eval (L.traceStates d.movedItems)

variable {L L'} {π : β →ₙ* γ}

theorem comp_eval (h0 : π 0 = 0) (hlex : ∀ a, π (L.lex a) = L'.lex a) (states : List β) :
    π.comp (L.eval states) = L'.eval (states.map π) :=
  FreeCommMagma.hom_ext fun ℓ ↦ by
    rcases ℓ with a | _ | i
    · exact hlex a
    · exact h0
    · show π ((states[i]?).getD 0) = ((states.map π)[i]?).getD 0
      rw [List.getElem?_map]
      cases states[i]? <;> simp [h0]

theorem traceStates_map (h0 : π 0 = 0) (hlex : ∀ a, π (L.lex a) = L'.lex a)
    (htrace : ∀ x, π (L.trace x) = L'.trace (π x)) (movers : List (SyntacticObject (ι := ℕ))) :
    L'.traceStates movers = (L.traceStates movers).map π := by
  suffices h : ∀ states : List β,
      movers.foldl (fun states m ↦ states ++ [L'.trace (L'.eval states m)]) (states.map π) =
        (movers.foldl (fun states m ↦ states ++ [L.trace (L.eval states m)]) states).map π from
    h []
  induction movers with
  | nil => exact fun _ ↦ rfl
  | cons m movers ih =>
    intro states
    rw [List.foldl_cons, List.foldl_cons, ← ih, List.map_append, List.map_singleton, htrace,
      ← comp_eval h0 hlex, MulHom.comp_apply]

/-- A morphism of licensings, preserving zero, the states of lexical items and traces, commutes
with their extensions over a derivation. -/
theorem comp_hom (h0 : π 0 = 0) (hlex : ∀ a, π (L.lex a) = L'.lex a)
    (htrace : ∀ x, π (L.trace x) = L'.trace (π x)) (d : Derivation ℕ) :
    π.comp (L.hom d) = L'.hom d := by
  rw [hom, hom, comp_eval h0 hlex, traceStates_map h0 hlex htrace]

end Licensing

namespace Derivation

variable (L : Licensing β) {L' : Licensing γ} {d : Derivation ℕ} {n : ℕ}

/-- `L` licenses stage `n` of `d`: the ordered configuration the replay reaches after `n` steps
is in its domain, the object and every copy on the stack. -/
def LicensedAt (d : Derivation ℕ) (n : ℕ) : Prop :=
  ∃ c ∈ (d.take n).replay? d.moverIndex,
    ∀ x ∈ c.current :: c.stack, L.hom d x.toSyntacticObject ≠ 0

instance [DecidableEq β] (d : Derivation ℕ) (n : ℕ) : Decidable (d.LicensedAt L n) :=
  inferInstanceAs (Decidable (∃ c ∈ (d.take n).replay? d.moverIndex, _))

/-- The stage licensing looks at is the derivation's own. -/
theorem LicensedAt.hom_stageAt_ne_zero (h : d.LicensedAt L n) :
    L.hom d (d.stageAt n d.moverIndex) ≠ 0 := by
  obtain ⟨c, hc, hall⟩ := h
  rw [stageAt, final, ← (d.take n).replay?_faithful hc, Cfg.map_current]
  exact hall c.current List.mem_cons_self

/-- `L` licenses `d` when it licenses every stage. -/
def LicensedBy (d : Derivation ℕ) : Prop := ∀ n ≤ d.length, d.LicensedAt L n

instance [DecidableEq β] (d : Derivation ℕ) : Decidable (d.LicensedBy L) :=
  inferInstanceAs (Decidable (∀ n ≤ d.length, _))

variable {L} {π : β →ₙ* γ}

/-- A licensing licenses the derivations that its image under a morphism of licensings licenses:
a coarser licensing's derivations are the finer one's. -/
theorem LicensedBy.of_hom (h0 : π 0 = 0) (hlex : ∀ a, π (L.lex a) = L'.lex a)
    (htrace : ∀ x, π (L.trace x) = L'.trace (π x)) (h : d.LicensedBy L') : d.LicensedBy L :=
  fun n hn ↦ (h n hn).imp fun c ⟨hc, hall⟩ ↦ ⟨hc, fun x hx hx0 ↦ hall x hx <| by
    rw [← Licensing.comp_hom h0 hlex htrace, MulHom.comp_apply, hx0, h0]⟩

end Derivation

/-! ### Triggered Merge -/

/-- The state of the trace of an object: its head with nothing left to select. -/
def SelectionState.saturate : SelectionState → SelectionState
  | ⟨some (a, _)⟩ => .of a []
  | ⟨none⟩ => 0

/-- Triggered Merge as a licensing: an item with its selectors, a trace the saturated head of the
object moved. -/
def SelectionState.licensing : Licensing SelectionState :=
  ⟨fun tok ↦ .of tok tok.item.sel, .saturate⟩

end Minimalist
