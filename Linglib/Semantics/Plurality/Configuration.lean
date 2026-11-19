/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Order.Minimal
public import Linglib.Semantics.Plurality.Cardinality
public import Linglib.Semantics.Plurality.Number
public import Linglib.Syntax.Person.Configuration

/-!
# Number features on the configurations of a person

The referents with a given set of speech-act participants form a region, and Harbour's number
features act on it as on any region. `[+minimal]` selects [the one referent with the fewest
others](##Person.Configuration.atomize_ofParticipants_iff), the speaker alone, the addressee
alone, the speaker with the addressee, or a single other, and `[+minimal]` of `[−minimal]`
[the referent with one more](##Person.Configuration.atomize_nonMinimalOf_ofParticipants_iff),
the unit augmented. [The atoms are the referents of one
member](##Person.Configuration.atom_iff_card_eq_one), so [the speaker with the addressee has no
singular](##Person.Configuration.not_atom_of_participants_eq_univ), and [the dual of a region is
its referents of two members](##Person.Configuration.dualOf_ofParticipants_iff).

Among finite sets of individuals, two of them the speaker and the addressee, a set is minimal
in a region defined by configuration [exactly when its configuration
is](##Person.Configuration.minimal_ofFinset_iff), so these statements hold of the referents
themselves.

## Main definitions

* `Person.Configuration.OfParticipants`: the region of the referents with given participants.
* `Person.Configuration.ofFinset`: the configuration of a finite set of individuals.

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
def OfParticipants (s : Finset Role) (x : Configuration) : Prop := x.participants = s ∧ x ≠ ⊥

theorem ofParticipants_iff : OfParticipants s x ↔ x.participants = s ∧ minimum s ≤ x.others :=
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
theorem atomize_ofParticipants_iff : atomize (OfParticipants s) x ↔ x = ⟨s, minimum s⟩ := by
  rw [show OfParticipants s = fun y ↦ y.participants = s ∧ minimum s ≤ y.others from
    funext fun _ ↦ propext ofParticipants_iff]
  exact minimal_le_others_iff

/-- `[−minimal]` of the region of a set of participants is its referents with more than the
fewest others, the augmented. -/
theorem nonMinimalOf_ofParticipants_iff :
    nonMinimalOf (OfParticipants s) x ↔ x.participants = s ∧ minimum s < x.others := by
  simp only [nonMinimalOf, atomize_ofParticipants_iff, ofParticipants_iff, Configuration.ext_iff]
  exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ ↦ ⟨h1, lt_of_le_of_ne h2 fun h ↦ h3 ⟨h1, h.symm⟩⟩,
    fun ⟨h1, h2⟩ ↦ ⟨⟨h1, h2.le⟩, fun h ↦ h2.ne' h.2⟩⟩

/-- `[+minimal]` of `[−minimal]` is the referent with one other more than the fewest, the unit
augmented. -/
theorem atomize_nonMinimalOf_ofParticipants_iff :
    atomize (nonMinimalOf (OfParticipants s)) x ↔ x = ⟨s, minimum s + 1⟩ := by
  rw [show nonMinimalOf (OfParticipants s) = fun y ↦ y.participants = s ∧ minimum s + 1 ≤ y.others
    from funext fun _ ↦ propext nonMinimalOf_ofParticipants_iff]
  exact minimal_le_others_iff

theorem not_isBot_iff_one_le_card : ¬ IsBot x ↔ 1 ≤ x.card := by
  rw [isBot_iff_eq_bot, eq_bot_iff_card_eq_zero]; omega

/-- The atoms are the configurations of one member: the speaker, the addressee, and a single
other. -/
theorem atom_iff_card_eq_one : Atom x ↔ x.card = 1 := by
  constructor
  · rintro ⟨hx, hmin⟩
    obtain ⟨s, n⟩ := x
    rcases s.eq_empty_or_nonempty with rfl | ⟨r, hr⟩
    · have h1 : 1 ≤ n := by simpa [card] using not_isBot_iff_one_le_card.1 hx
      have := (le_def.1
        (hmin (y := ⟨∅, 1⟩) (not_isBot_iff_one_le_card.2 (by simp [card])) ⟨le_rfl, h1⟩)).2
      simp only [card, Finset.card_empty] at this ⊢
      omega
    · have := le_def.1 (hmin (y := ⟨{r}, 0⟩) (not_isBot_iff_one_le_card.2 (by simp [card]))
        ⟨Finset.singleton_subset_iff.2 hr, Nat.zero_le _⟩)
      have hs : s = {r} := le_antisymm this.1 (Finset.singleton_subset_iff.2 hr)
      have hn : n = 0 := Nat.le_zero.1 this.2
      simp [card, hs, hn]
  · intro h
    refine ⟨not_isBot_iff_one_le_card.2 h.ge, fun y hy hyx ↦ ?_⟩
    have h1 := not_isBot_iff_one_le_card.1 hy
    obtain ⟨hp, hn⟩ := le_def.1 hyx
    have hc := Finset.card_le_card hp
    simp only [card] at h h1
    exact le_def.2 ⟨(Finset.eq_of_subset_of_card_le hp (by omega)).ge, by omega⟩

/-- The speaker with the addressee is no atom, whatever its others: the inclusive has no
singular. -/
theorem not_atom_of_participants_eq_univ (h : x.participants = Finset.univ) : ¬ Atom x := by
  intro ha
  have h1 := atom_iff_card_eq_one.1 ha
  have h2 : (Finset.univ : Finset Role).card = 2 := by decide
  rw [card, h, h2] at h1
  omega

/-- The dual of the region of a set of participants is its referents of two members. -/
theorem dualOf_ofParticipants_iff :
    dualOf (OfParticipants s) x ↔ x.participants = s ∧ x.card = 2 := by
  have hs : s.card ≤ 2 := s.card_le_univ
  have hb : (minimum s = 0 ∧ 1 ≤ s.card) ∨ (minimum s = 1 ∧ s.card = 0) := by
    rcases s.eq_empty_or_nonempty with rfl | h
    · simp
    · exact Or.inl ⟨minimum_of_nonempty h, Finset.card_pos.2 h⟩
  have key : nonAtomsOf (OfParticipants s) =
      fun y : Configuration ↦ y.participants = s ∧ 2 ≤ s.card + y.others := by
    funext y
    apply propext
    simp only [nonAtomsOf, atom_iff_card_eq_one, ofParticipants_iff, card]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      rw [h1] at h3
      exact ⟨h1, by omega⟩
    · rintro ⟨h1, h2⟩
      rw [h1]
      exact ⟨⟨rfl, by omega⟩, by omega⟩
  rw [dualOf, atomize, key, card]
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

/-! ### The configuration of a set of individuals -/

section Finset

variable {ι : Type*} [DecidableEq ι] (a b : ι) {u : Finset ι} {r : Role} {z : ι}

/-- The individual holding a role, `a` the speaker and `b` the addressee. -/
def holder : Role → ι
  | .speaker => a
  | .addressee => b

/-- The configuration of a set of individuals of whom `a` is the speaker and `b` the addressee:
the roles whose holders it contains and the number of its other members. -/
def ofFinset (u : Finset ι) : Configuration :=
  ⟨Finset.univ.filter fun r ↦ holder a b r ∈ u, ((u.erase a).erase b).card⟩

theorem mem_participants_ofFinset : r ∈ (ofFinset a b u).participants ↔ holder a b r ∈ u := by
  simp [ofFinset]

private theorem mem_erase_erase : z ∈ (u.erase a).erase b ↔ z ≠ b ∧ z ≠ a ∧ z ∈ u := by simp

theorem ofFinset_mono : Monotone (ofFinset a b (ι := ι)) := fun _ _ hvu ↦
  ⟨fun _ hr ↦ (mem_participants_ofFinset a b).2 (hvu ((mem_participants_ofFinset a b).1 hr)),
    Finset.card_le_card (Finset.erase_subset_erase _ (Finset.erase_subset_erase _ hvu))⟩

/-- A proper part of a set of individuals has a strictly smaller configuration. -/
theorem ofFinset_strictMono : StrictMono (ofFinset a b (ι := ι)) := fun v u hlt ↦ by
  refine lt_of_le_of_ne (ofFinset_mono a b hlt.le) fun h ↦
    hlt.ne (le_antisymm hlt.le fun z hz ↦ ?_)
  have hr : (ofFinset a b v).participants = (ofFinset a b u).participants :=
    congrArg participants h
  have ho : (v.erase a).erase b = (u.erase a).erase b :=
    Finset.eq_of_subset_of_card_le
      (Finset.erase_subset_erase _ (Finset.erase_subset_erase _ hlt.le))
      (congrArg others h).ge
  by_cases hza : z = a
  · subst hza
    exact (mem_participants_ofFinset z b (r := .speaker)).1
      (hr ▸ (mem_participants_ofFinset z b (r := .speaker)).2 hz)
  by_cases hzb : z = b
  · subst hzb
    exact (mem_participants_ofFinset a z (r := .addressee)).1
      (hr ▸ (mem_participants_ofFinset a z (r := .addressee)).2 hz)
  exact ((mem_erase_erase a b).1 (ho ▸ (mem_erase_erase a b).2 ⟨hzb, hza, hz⟩)).2.2

/-- Every configuration below that of a set of individuals is the configuration of a part of
it, the speaker and the addressee being distinct. -/
theorem exists_le_ofFinset_eq (hab : a ≠ b) {y : Configuration} (h : y ≤ ofFinset a b u) :
    ∃ v ≤ u, ofFinset a b v = y := by
  obtain ⟨t, m⟩ := y
  obtain ⟨ht, hm⟩ := h
  obtain ⟨o, ho, rfl⟩ := Finset.exists_subset_card_eq (show m ≤ ((u.erase a).erase b).card from hm)
  have hinj : Function.Injective (holder a b) := by
    intro r r' h
    cases r <;> cases r' <;> simp_all [holder]
  have ho' : ∀ z ∈ o, z ≠ b ∧ z ≠ a ∧ z ∈ u := fun z hz ↦ (mem_erase_erase a b).1 (ho hz)
  refine ⟨t.image (holder a b) ∪ o, fun z hz ↦ ?_, Configuration.ext ?_ ?_⟩
  · rcases Finset.mem_union.1 hz with hz | hz
    · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hz
      exact (mem_participants_ofFinset a b).1 (ht hr)
    · exact (ho' z hz).2.2
  · ext r
    simp only [mem_participants_ofFinset, Finset.mem_union, Finset.mem_image]
    constructor
    · rintro (⟨r', hr', h⟩ | h)
      · exact hinj h ▸ hr'
      · cases r
        · exact absurd rfl (ho' _ h).2.1
        · exact absurd rfl (ho' _ h).1
    · exact fun hr ↦ Or.inl ⟨r, hr, rfl⟩
  · change (((t.image (holder a b) ∪ o).erase a).erase b).card = o.card
    congr 1
    ext z
    simp only [mem_erase_erase, Finset.mem_union, Finset.mem_image]
    constructor
    · rintro ⟨hb, ha, ⟨r, -, rfl⟩ | h⟩
      · cases r
        · exact absurd rfl ha
        · exact absurd rfl hb
      · exact h
    · exact fun hz ↦ ⟨(ho' z hz).1, (ho' z hz).2.1, Or.inr hz⟩

/-- A set of individuals is minimal among those whose configuration lies in a region exactly
when its configuration is minimal in the region. -/
theorem minimal_ofFinset_iff (hab : a ≠ b) {P : Configuration → Prop} :
    Minimal (fun v ↦ P (ofFinset a b v)) u ↔ Minimal P (ofFinset a b u) :=
  minimal_comp_iff_of_strictMono (ofFinset_strictMono a b) fun _ _ ↦ exists_le_ofFinset_eq a b hab

end Finset

end Person.Configuration

namespace Person.Category

/-- A category without others has exactly its participants, so a number label of fixed
cardinality covers it only at that cardinality. -/
theorem exactCard_eq_card_of_mem_ofPersonNumber :
    ∀ p cl n c, c ∈ ofPersonNumber p cl n → c.otherCount = 0 →
      ∀ k ∈ n.exactCard, (k : ℕ) = c.card := by
  decide

end Person.Category
