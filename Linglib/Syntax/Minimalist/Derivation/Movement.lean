/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Derivation.Basic

/-!
# Movements

A movement is an object together with a proper term of it, the mover: the datum of an Internal
Merge. Its remainder is the object with the mover's occurrences replaced by the trace of its head,
and its result is the remainder merged with the mover, [what an Internal Merge step
builds](##Minimalist.Movement.result_eq_apply). In an object that pronounces no token twice, [the
remainder and the mover share no token](##Minimalist.Movement.disjoint_yield). A step of a
derivation that moves a proper term of its stage is a movement, `Derivation.movement?`, so that a
condition on one movement is a condition on a step.

## References

* [marcolli-chomsky-berwick-2025]
* [collins-stabler-2016]
-/

@[expose] public section

namespace Minimalist

open SyntacticObject

/-- An object and a proper term of it that moves. -/
structure Movement where
  /-- The object the mover moves in. -/
  source : SyntacticObject
  /-- The term that moves. -/
  mover : SyntacticObject
  /-- The mover is a proper term of the source. -/
  contains : Contains source mover

namespace Movement

variable (μ : Movement) (τ : SyntacticObject → Option LexicalItem.Token)

/-- The source with the mover's occurrences replaced by the trace of its head. -/
def remainder (τ : SyntacticObject → Option LexicalItem.Token := selHead) : SyntacticObject :=
  deleteAccessible μ.mover μ.source τ

/-- The remainder merged with the mover. -/
def result (τ : SyntacticObject → Option LexicalItem.Token := selHead) : SyntacticObject :=
  merge (μ.remainder τ) μ.mover

theorem mover_mem_terms : μ.mover ∈ μ.source.terms := mem_terms.2 μ.contains.to_reflTransGen

/-- The result of a movement is what the Internal Merge of its mover builds from its source. -/
theorem result_eq_apply (side : Edge) :
    μ.result τ = (Step.im μ.mover side).apply μ.source τ := rfl

variable {μ}

/-- The remainder and the mover pronounce the tokens of the source between them. -/
theorem yield_remainder_add_yield_mover (h : μ.source.yield.Nodup) :
    (μ.remainder τ).yield + μ.mover.yield = μ.source.yield :=
  yield_replace_add_yield h μ.mover_mem_terms (yield_headTrace _ _)

/-- The remainder and the mover share no token, in a source that pronounces none twice. -/
theorem disjoint_yield (h : μ.source.yield.Nodup) :
    Disjoint (μ.remainder τ).yield μ.mover.yield :=
  (Multiset.nodup_add.1 (yield_remainder_add_yield_mover τ h ▸ h)).2.2

end Movement

namespace Derivation

variable {d : Derivation} {steps : List Step} {i : ℕ} {μ : Movement}

/-- The movement of step `i`: its mover out of the stage it applies to, when the mover is a proper
term of that stage. -/
def movement? (d : Derivation) (i : ℕ) : Option Movement :=
  (d.mover? i).bind fun m ↦
    if h : Contains (d.stageAt i) m then some ⟨d.stageAt i, m, h⟩ else none

theorem mem_movement?_iff :
    μ ∈ d.movement? i ↔ μ.mover ∈ d.mover? i ∧ μ.source = d.stageAt i := by
  constructor
  · intro h
    obtain ⟨m, hm, h⟩ := Option.bind_eq_some_iff.1 h
    split at h
    · obtain rfl := Option.some.inj h; exact ⟨hm, rfl⟩
    · cases h
  · rintro ⟨hm, hs⟩
    obtain ⟨src, m, hc⟩ := μ
    obtain rfl : src = d.stageAt i := hs
    exact Option.bind_eq_some_iff.2 ⟨m, hm, by simp [hc]⟩

theorem lt_length_of_mem_movement? (h : μ ∈ d.movement? i) : i < d.length :=
  lt_length_of_mem_mover? (mem_movement?_iff.1 h).1

/-- The early steps of an extension have the original's movements. -/
theorem movement?_append_of_lt (hi : i < d.length) :
    (d.append steps).movement? i = d.movement? i := by
  rw [movement?, movement?, mover?_append_of_lt hi, stageAt_append_of_le hi.le]

end Derivation

end Minimalist
