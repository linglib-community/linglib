/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Order.Filter.Ultrafilter.Defs

/-!
# Filters that decide every set

A filter contains every set or its complement exactly when it is the bottom filter or an atom of
the lattice of filters, that is, an ultrafilter.

## Main statements

* `Filter.forall_mem_or_compl_mem_iff`
-/

@[expose] public section

namespace Filter

variable {α : Type*} {f : Filter α}

theorem forall_mem_or_compl_mem_iff : (∀ s, s ∈ f ∨ sᶜ ∈ f) ↔ f = ⊥ ∨ IsAtom f := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · rcases eq_or_neBot f with hf | hf
    · exact .inl hf
    · exact .inr (Ultrafilter.ofComplNotMemIff f fun s ↦
        ⟨fun hs ↦ (h s).resolve_right hs, fun hs hsc ↦
          (f.empty_mem_iff_bot.not.2 hf.ne) (by simpa using f.inter_mem hs hsc)⟩).isAtom
  · rintro (rfl | hf) s
    · exact .inl (by simp)
    · exact (Ultrafilter.ofAtom f hf).mem_or_compl_mem s

end Filter
