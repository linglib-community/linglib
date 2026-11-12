/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Autosegmental.Factors

/-!
# Representations on two tiers

A representation on two tiers has a melody tier, indexed by `true`, over a timing tier, indexed
by `false`. Its lines all run between the two tiers, so the lines from the melody to the timing
tier [determine it](##Autosegmental.AR.ext_of_true_false), and every statement about its lines
reduces to that one pair of tiers: the No-Crossing Constraint
[is the constraint on them](##Autosegmental.AR.noCrossing_iff_two_tier), and one representation
embeds in another as a factor when its two words occur at
[a pair of bounded offsets](##Autosegmental.AR.factorEmbeds_iff_two_tier) at which its lines are
lines of the host. Embedding and freedom from a banned-subgraph grammar are therefore decidable.
`Form` presents such representations by their words and a finite set of lines.

## References

* [jardine-2016b]
* [jardine-2019]
-/

@[expose] public section

namespace Autosegmental

universe u

/-- The two-tier alphabet puts melody labels over `true` and timing labels over `false`. -/
abbrev TwoTier (α β : Type u) : Bool → Type u := fun b => bif b then α else β

instance {α β : Type u} [DecidableEq α] [DecidableEq β] : ∀ b, DecidableEq (TwoTier α β b)
  | true => inferInstanceAs (DecidableEq α)
  | false => inferInstanceAs (DecidableEq β)

namespace AR

variable {τ : Bool → Type*} {F X Y : AR τ}

/-! ### Lines -/

theorem link_iff_of_true_false (h : ∀ p q, X.Link true false p q ↔ Y.Link true false p q)
    (i j : Bool) (p q : ℕ) : X.Link i j p q ↔ Y.Link i j p q := by
  cases i <;> cases j
  · exact iff_of_false (fun h ↦ h.ne rfl) (fun h ↦ h.ne rfl)
  · exact link_comm.trans ((h q p).trans link_comm)
  · exact h p q
  · exact iff_of_false (fun h ↦ h.ne rfl) (fun h ↦ h.ne rfl)

/-- Two representations on two tiers are equal when their words are and they have the same lines
from the melody to the timing tier. -/
theorem ext_of_true_false (ht : X.word true = Y.word true) (hf : X.word false = Y.word false)
    (h : ∀ p q, X.Link true false p q ↔ Y.Link true false p q) : X = Y :=
  ext (funext fun b ↦ by cases b <;> assumption) (link_iff_of_true_false h)

/-! ### The No-Crossing Constraint -/

theorem noCrossing_iff_two_tier : X.NoCrossing ↔ IsNonCrossing (X.lines true false) := by
  refine ⟨fun h ↦ h true false, fun h i j ↦ ?_⟩
  cases i <;> cases j
  exacts [isNonCrossing_lines_self _, isNonCrossing_lines_comm.1 h, h, isNonCrossing_lines_self _]

/-- A representation with at most one timing slot obeys the NCC. -/
theorem noCrossing_of_length_false_le_one (h : (X.word false).length ≤ 1) : X.NoCrossing :=
  noCrossing_iff_two_tier.2 <| isNonCrossing_lines_iff.2 fun _ _ _ _ h₁ h₂ _ ↦ by
    have := h₁.lt_right
    have := h₂.lt_right
    omega

/-! ### Factor embedding -/

theorem isFactorAt_iff_two_tier {o : Bool → ℕ} : F.IsFactorAt X o ↔
    F.word true <+: (X.word true).drop (o true) ∧ F.word false <+: (X.word false).drop (o false) ∧
      ∀ p q, F.Link true false p q → X.Link true false (p + o true) (q + o false) := by
  refine ⟨fun h ↦ ⟨h.window true, h.window false, h.link_map true false⟩, fun ⟨ht, hf, hl⟩ ↦
    ⟨fun b ↦ by cases b <;> assumption, ?_⟩⟩
  rintro (_ | _) (_ | _) p q h
  exacts [absurd rfl h.ne, (hl q p h.symm).symm, hl p q h, absurd rfl h.ne]

/-- One representation embeds in another as a factor iff its words occur in the host's at a pair
of bounded offsets and its lines are lines of the host there. -/
theorem factorEmbeds_iff_two_tier : F ⊑ X ↔
    ∃ ot ≤ (X.word true).length, ∃ of ≤ (X.word false).length,
      F.word true <+: (X.word true).drop ot ∧ F.word false <+: (X.word false).drop of ∧
        ∀ p < (F.word true).length, ∀ q < (F.word false).length,
          F.Link true false p q → X.Link true false (p + ot) (q + of) := by
  rw [factorEmbeds_iff_bounded]
  constructor
  · rintro ⟨o, hb, h⟩
    obtain ⟨ht, hf, hl⟩ := isFactorAt_iff_two_tier.1 h
    exact ⟨o true, hb true, o false, hb false, ht, hf, fun p _ q _ ↦ hl p q⟩
  · rintro ⟨ot, hot, of, hof, ht, hf, hl⟩
    exact ⟨fun b ↦ bif b then ot else of, fun b ↦ by cases b <;> assumption,
      isFactorAt_iff_two_tier.2 ⟨ht, hf, fun p q h ↦ hl p h.lt_left q h.lt_right h⟩⟩

instance [∀ b, DecidableEq (τ b)] : Decidable (F ⊑ X) :=
  decidable_of_iff _ factorEmbeds_iff_two_tier.symm

instance [∀ b, DecidableEq (τ b)] (B : List (AR τ)) : Decidable (X.Free B) :=
  inferInstanceAs (Decidable (∀ F ∈ B, ¬ F ⊑ X))

/-! ### Surfacing -/

variable {α β : Type u} {X : AR (TwoTier α β)} {a : α} {j : ℕ}

variable (X a j) in
/-- Timing slot `j` surfaces with melody label `a` when some `a`-labelled melody node links to
it. -/
def SurfacesWith : Prop :=
  ∃ k, X.Link true false k j ∧ (X.word true)[k]? = some a

theorem SurfacesWith.lt (h : X.SurfacesWith a j) : j < (X.word false).length :=
  h.choose_spec.1.lt_right

end AR

end Autosegmental
