/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Order.BourbakiWitt
public import Mathlib.Order.FixedPoints

/-!
# ω-suprema in complete lattices

Every complete lattice is an ω-complete partial order (through `ChainCompletePartialOrder`), and
there the ω-supremum of a chain is its indexed supremum; on a product of complete lattices the
same holds for the product instance. Kleene's fixed-point theorem then takes a supremum form
that is independent of which of the two instances a continuity proof was carried out in
(`OrderHom.lfp_eq_iSup_iterate`). `[UPSTREAM]` candidate for
`Mathlib/Order/OmegaCompletePartialOrder.lean` and `Mathlib/Order/FixedPoints.lean`.
-/

@[expose] public section

open OmegaCompletePartialOrder

theorem CompleteLattice.ωSup_eq_iSup {L : Type*} [CompleteLattice L] (c : Chain L) :
    ωSup c = ⨆ n, c n :=
  le_antisymm (ωSup_le _ _ fun n => le_iSup (fun n => c n) n) (iSup_le fun n => le_ωSup c n)

theorem Pi.ωSup_eq_iSup {ι : Type*} {L : ι → Type*} [∀ i, CompleteLattice (L i)]
    (c : Chain (∀ i, L i)) : ωSup c = ⨆ n, c n := by
  funext i
  show ωSup (c.map (Pi.evalOrderHom i)) = _
  rw [CompleteLattice.ωSup_eq_iSup, iSup_apply]
  rfl

theorem OrderHom.lfp_eq_iSup_iterate {L : Type*} [CompleteLattice L] (f : L →o L)
    (hf : ∀ c : Chain L, f (⨆ n, c n) = ⨆ n, f (c n)) : f.lfp = ⨆ n, f^[n] ⊥ :=
  fixedPoints.lfp_eq_sSup_iterate f <| ωScottContinuous.of_monotone_map_ωSup
    ⟨f.monotone, fun c => by
      rw [CompleteLattice.ωSup_eq_iSup, hf c, CompleteLattice.ωSup_eq_iSup]; rfl⟩
