module

public import Linglib.Semantics.Modality.BranchingTime
public import Linglib.Semantics.Tense.Quantificational
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Order.Sum.Order

/-!
# Prior (1967): Past, Present and Future

Chapter III of Prior's book correlates the postulates of tense logic with the structure of time,
through the reading of `F`, `P`, `G` and `H` as quantifiers over later and earlier dates that
`Semantics/Tense/Quantificational.lean` takes as its definition. Time's density matters only to a
strict *later than*: [it refutes `CFpFFp` when discrete](##not_den_int), and
[a reflexive one verifies it regardless](##den_nonpast). A time with a beginning and no end
[keeps `CGpFp` and loses its mirror image](##mirror_image_fails). Prior's law `CMNMpNMp`
[holds exactly when time branches neither way](##cmnmpnmp_iff), which
[falls short of trichotomy](##cmnmpnmp_not_trichotomous), and `CFPpAApPpFp` and `CPFpAApPpFp`
[come apart on a fork](##fork_asymmetry).

## TODO

* The metric tense logic of Chapter VI, the Ockhamist and Peircean formalizations of Chapter VII
  (see `Semantics/Modality/BranchingTime.lean`), and the rest of the book.

## References

* [prior-1967]
-/

@[expose] public section

namespace Prior1967

open ModalLogic Tense
open scoped Denotes SetRel

-- `CFpFFp` on discrete time, p. 39: something can be the case for the last time at the next
-- moment.
theorem not_den_int : ¬ ((◇[toSetRel ⟦Tense.future⟧] : (ℤ → Prop) → ℤ → Prop) ≤
    ◇[toSetRel ⟦Tense.future⟧] ∘ ◇[toSetRel ⟦Tense.future⟧]) := fun h ↦ by
  obtain ⟨c, h₁, h₂⟩ := (diamond_future_den_iff.1 h).dense (0 : ℤ) 1 (by decide)
  omega

theorem den_rat : (◇[toSetRel ⟦Tense.future⟧] : (ℚ → Prop) → ℚ → Prop) ≤
    ◇[toSetRel ⟦Tense.future⟧] ∘ ◇[toSetRel ⟦Tense.future⟧] :=
  diamond_future_den_iff.2 inferInstance

/-- If *later than* were reflexive, `CFpFFp` would be verified even if time were not dense (p. 39).
The reflexive *later than* is the relation of the nonpast cell. -/
theorem den_nonpast {T : Type*} [LinearOrder T] :
    (◇[toSetRel nonpast] : (T → Prop) → T → Prop) ≤ ◇[toSetRel nonpast] ∘ ◇[toSetRel nonpast] :=
  have : (toSetRel nonpast : SetRel T T).IsRefl :=
    ⟨fun t ↦ mem_toSetRel_iff.2 ((compare_mem_nonpast t t).2 le_rfl)⟩
  diamond_den_iff.2 SetRel.left_subset_comp

/-- If time has a beginning and no end, it keeps `CGpFp` and loses the mirror image `CHpPp`, so the
mirror-image rule has to go (p. 40). -/
theorem mirror_image_fails :
    (Box (toSetRel ⟦Tense.future⟧) : (ℕ → Prop) → ℕ → Prop) ≤ Diamond (toSetRel ⟦Tense.future⟧) ∧
      ¬ ((Box (toSetRel ⟦Tense.past⟧) : (ℕ → Prop) → ℕ → Prop) ≤
        Diamond (toSetRel ⟦Tense.past⟧)) := by
  refine ⟨box_D_iff.2 (isSerial_toSetRel_future_iff.2 ⟨fun n ↦ ⟨n + 1, n.lt_succ_self⟩⟩),
    fun h ↦ ?_⟩
  obtain ⟨n, hn⟩ := (isSerial_toSetRel_past_iff.1 (box_D_iff.1 h)).exists_lt 0
  omega

variable {T : Type*} [PartialOrder T]

/-- `CMNMpNMp` (p. 38), with `M` the possibility of the unconstrained cell (`diamond_toSetRel_top`),
holds exactly when time branches neither way. -/
theorem cmnmpnmp_iff :
    (∀ (p : T → Prop) (t : T),
      ◇[toSetRel ⊤] (fun u ↦ ¬ ◇[toSetRel ⊤] p u) t → ¬ ◇[toSetRel ⊤] p t) ↔
        IsLeftLinear T ∧ IsLeftLinear Tᵒᵈ := by
  rw [← isEuclidean_toSetRel_top_iff, ← box_five_iff]
  refine ⟨fun h p t hp ↦ ?_, fun h p t hn hp ↦ ?_⟩
  · by_contra hb
    exact h p t (not_box.1 hb) hp
  · exact not_box.2 hn (h p t hp)

/-- `CMNMpNMp` holds on two unconnected lines, where a date of one is neither identical with, later
than nor earlier than a date of the other, so the law does not require trichotomy. -/
theorem cmnmpnmp_not_trichotomous :
    (∀ (p : ℕ ⊕ ℕ → Prop) (t : ℕ ⊕ ℕ),
      ◇[toSetRel ⊤] (fun u ↦ ¬ ◇[toSetRel ⊤] p u) t → ¬ ◇[toSetRel ⊤] p t) ∧
      ¬ ∀ a b : ℕ ⊕ ℕ, a < b ∨ a = b ∨ b < a := by
  refine ⟨cmnmpnmp_iff.2 ⟨⟨?_⟩, isLeftLinear_orderDual_iff.2 ?_⟩, fun h ↦ ?_⟩
  · rintro (a | a) (b | b) (c | c) ha hb <;> simp_all [le_total]
  · rintro (a | a) (b | b) (c | c) ha hb <;> simp_all [le_total]
  · simpa using h (.inl 0) (.inr 0)

/-- A time with a root and two branches. -/
abbrev Fork : Type := WithBot (Unit ⊕ Unit)

theorem isBranching_fork : IsBranching (⊥ : Fork) := by
  refine ⟨.some (.inl ()), ⟨WithBot.bot_lt_coe _, ?_⟩, .some (.inr ()), ⟨WithBot.bot_lt_coe _, ?_⟩,
    by simp⟩
  · rintro (_ | (_ | _)) h₁ h₂ <;> simp_all [WithBot.none_eq_bot, WithBot.some_eq_coe]
  · rintro (_ | (_ | _)) h₁ h₂ <;> simp_all [WithBot.none_eq_bot, WithBot.some_eq_coe]

/-- `CFPpAApPpFp` and `CPFpAApPpFp` (p. 52) come apart on a fork, where no time branches to the left
and one branches to the right. -/
theorem fork_asymmetry :
    (◇[toSetRel ⟦Tense.future⟧] ∘ ◇[toSetRel ⟦Tense.past⟧] : (Fork → Prop) → Fork → Prop) ≤
        ◇[toSetRel ⊤] ∧
      ¬ ((◇[toSetRel ⟦Tense.past⟧] ∘ ◇[toSetRel ⟦Tense.future⟧] : (Fork → Prop) → Fork → Prop) ≤
        ◇[toSetRel ⊤]) := by
  refine ⟨diamond_future_diamond_past_le_iff.2 ⟨?_⟩,
    BranchingTime.not_diamond_past_diamond_future_le isBranching_fork⟩
  rintro (_ | (_ | _)) (_ | (_ | _)) (_ | (_ | _)) h₁ h₂ <;>
    simp_all [WithBot.none_eq_bot, WithBot.some_eq_coe]

end Prior1967
