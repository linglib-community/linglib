/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.Plurality.Cardinality
public import Linglib.Semantics.Plurality.Number
public import Linglib.Syntax.Feature.Person.Configuration

/-!
# Number features on the configurations of a person

The referents with a given set of speech-act participants form a region, and Harbour's number
features act on it as on any region. `[+minimal]` selects [the one referent with the fewest
others](##Person.Configuration.atomize_ofParticipants_iff), the speaker alone, the addressee
alone, the speaker with the addressee, or a single other, and `[+minimal]` of `[−minimal]` the
referent with one more (`Person.Configuration.atomize_restrict_minimal_false_ofParticipants_iff`),
the unit augmented. [The atoms are the referents of one
member](##Person.Configuration.isAtom_iff_card_eq_one), so [the speaker with the addressee has no
singular](##Person.Configuration.not_atom_of_participants_eq_univ), and [the dual of a region is
its referents of two members](##Person.Configuration.dual_ofParticipants_iff).

These statements hold of the sets of individuals themselves, minimality passing between a set
and its configuration (`Syntax/Feature/Person/Referent.lean`).

## Main definitions

* `Person.Configuration.OfParticipants`: the region of the referents with given participants.

## References

* [harbour-2014]
* [corbett-2000]
* [cysouw-2003]
-/

@[expose] public section

namespace Person.Configuration

open SpeechAct Mereology Number

variable {x : Configuration} {s : Finset Role}

/-- The region of the referents whose participants are `s`. -/
def OfParticipants (s : Finset Role) : Set Configuration := {x | x.participants = s ∧ x ≠ ⊥}

theorem ofParticipants_iff : x ∈ OfParticipants s ↔ x.participants = s ∧ minimum s ≤ x.others :=
  ⟨fun ⟨h, hx⟩ ↦ ⟨h, h ▸ ne_bot_iff_minimum_le.1 hx⟩,
    fun ⟨h, hx⟩ ↦ ⟨h, ne_bot_iff_minimum_le.2 (h ▸ hx)⟩⟩

private theorem minimal_le_others_iff {k : ℕ} :
    Minimal (fun y : Configuration ↦ y.participants = s ∧ k ≤ y.others) x ↔ x = ⟨s, k⟩ := by
  obtain ⟨t, n⟩ := x
  constructor
  · rintro ⟨⟨rfl, hk⟩, hmin⟩
    have := (hmin (y := ⟨t, k⟩) ⟨rfl, le_rfl⟩ ⟨le_rfl, hk⟩).2
    exact Configuration.ext rfl (le_antisymm this hk)
  · rintro ⟨rfl, rfl⟩
    exact ⟨⟨rfl, le_rfl⟩, fun y hy _ ↦ ⟨hy.1.ge, hy.2⟩⟩

/-- `[+minimal]` of the region of a set of participants is its one referent with the fewest
others, the logical minimum. -/
theorem atomize_ofParticipants_iff : x ∈ atomize (OfParticipants s) ↔ x = ⟨s, minimum s⟩ := by
  rw [show OfParticipants s = {y | y.participants = s ∧ minimum s ≤ y.others} from
    Set.ext fun _ ↦ ofParticipants_iff]
  exact minimal_le_others_iff

/-- `[−minimal]` of the region of a set of participants is its referents with more than the
fewest others, the augmented. -/
theorem restrict_minimal_false_ofParticipants_iff :
    x ∈ Feature.restrict .minimal false (OfParticipants s) ↔
      x.participants = s ∧ minimum s < x.others := by
  simp only [Feature.mem_restrict_minimal_false, atomize_ofParticipants_iff, ofParticipants_iff,
    Configuration.ext_iff]
  exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ ↦ ⟨h1, lt_of_le_of_ne h2 fun h ↦ h3 ⟨h1, h.symm⟩⟩,
    fun ⟨h1, h2⟩ ↦ ⟨⟨h1, h2.le⟩, fun h ↦ h2.ne' h.2⟩⟩

/-- `[+minimal]` of `[−minimal]` is the referent with one other more than the fewest, the unit
augmented. -/
theorem atomize_restrict_minimal_false_ofParticipants_iff :
    x ∈ atomize (Feature.restrict .minimal false (OfParticipants s)) ↔
      x = ⟨s, minimum s + 1⟩ := by
  rw [show Feature.restrict .minimal false (OfParticipants s) =
      {y | y.participants = s ∧ minimum s + 1 ≤ y.others}
    from Set.ext fun _ ↦ restrict_minimal_false_ofParticipants_iff]
  exact minimal_le_others_iff

theorem ne_bot_iff_one_le_card : x ≠ ⊥ ↔ 1 ≤ x.card := by
  rw [Ne, eq_bot_iff_card_eq_zero]; omega

/-- The atoms are the configurations of one member: the speaker, the addressee, and a single
other. -/
theorem isAtom_iff_card_eq_one : IsAtom x ↔ x.card = 1 := by
  rw [isAtom_iff_le_of_ge]
  constructor
  · rintro ⟨hx, hmin⟩
    obtain ⟨s, n⟩ := x
    rcases s.eq_empty_or_nonempty with rfl | ⟨r, hr⟩
    · have h1 : 1 ≤ n := by simpa [card] using ne_bot_iff_one_le_card.1 hx
      have := (le_def.1
        (hmin ⟨∅, 1⟩ (ne_bot_iff_one_le_card.2 (by simp [card])) ⟨le_rfl, h1⟩)).2
      simp only [card, Finset.card_empty] at this ⊢
      omega
    · have := le_def.1 (hmin ⟨{r}, 0⟩ (ne_bot_iff_one_le_card.2 (by simp [card]))
        ⟨Finset.singleton_subset_iff.2 hr, Nat.zero_le _⟩)
      have hs : s = {r} := le_antisymm this.1 (Finset.singleton_subset_iff.2 hr)
      have hn : n = 0 := Nat.le_zero.1 this.2
      simp [card, hs, hn]
  · intro h
    refine ⟨ne_bot_iff_one_le_card.2 h.ge, fun y hy hyx ↦ ?_⟩
    have h1 := ne_bot_iff_one_le_card.1 hy
    obtain ⟨hp, hn⟩ := le_def.1 hyx
    have hc := Finset.card_le_card hp
    simp only [card] at h h1
    exact le_def.2 ⟨(Finset.eq_of_subset_of_card_le hp (by omega)).ge, by omega⟩

/-- The speaker with the addressee is no atom, whatever its others: the inclusive has no
singular. -/
theorem not_atom_of_participants_eq_univ (h : x.participants = Finset.univ) : ¬ IsAtom x := by
  intro ha
  have h1 := isAtom_iff_card_eq_one.1 ha
  have h2 : (Finset.univ : Finset Role).card = 2 := by decide
  rw [card, h, h2] at h1
  omega

/-- The dual of the region of a set of participants is its referents of two members. -/
theorem dual_ofParticipants_iff :
    x ∈ Feature.restrict .minimal true (Feature.restrict .atomic false (OfParticipants s)) ↔
      x.participants = s ∧ x.card = 2 := by
  have hs : s.card ≤ 2 := s.card_le_univ
  have hb : (minimum s = 0 ∧ 1 ≤ s.card) ∨ (minimum s = 1 ∧ s.card = 0) := by
    rcases s.eq_empty_or_nonempty with rfl | h
    · simp
    · exact Or.inl ⟨minimum_of_nonempty h, Finset.card_pos.2 h⟩
  have key : Feature.restrict .atomic false (OfParticipants s) =
      {y : Configuration | y.participants = s ∧ 2 ≤ s.card + y.others} := by
    ext y
    simp only [Feature.mem_restrict_atomic_false, isAtom_iff_card_eq_one, ofParticipants_iff, card,
      Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      rw [h1] at h3
      exact ⟨h1, by omega⟩
    · rintro ⟨h1, h2⟩
      rw [h1]
      exact ⟨⟨rfl, by omega⟩, by omega⟩
  rw [Feature.restrict_minimal_true, key, card, mem_atomize]
  obtain ⟨t, n⟩ := x
  constructor
  · rintro ⟨⟨h1, h2⟩, hmin⟩
    simp only at h1 h2
    subst h1
    refine ⟨rfl, ?_⟩
    by_contra hne
    simp only at hne
    have := (le_def.1
      (hmin (y := ⟨t, n - 1⟩) ⟨rfl, by simp only; omega⟩ ⟨le_rfl, Nat.sub_le n 1⟩)).2
    simp only at this
    omega
  · rintro ⟨h1, h2⟩
    simp only at h1 h2
    subst h1
    refine ⟨⟨rfl, by simp only; omega⟩, fun y hy hyx ↦ le_def.2 ⟨hy.1.ge, ?_⟩⟩
    have := hy.2
    simp only
    omega

end Person.Configuration

namespace Person.Category

/-- A category without others has exactly its participants, so a number label of fixed
cardinality covers it only at that cardinality. -/
theorem exactCard_eq_card_of_mem_ofPersonNumber :
    ∀ p cl n c, c ∈ ofPersonNumber p cl n → c.otherCount = 0 →
      ∀ k ∈ n.exactCard, (k : ℕ) = c.card := by
  decide

end Person.Category
