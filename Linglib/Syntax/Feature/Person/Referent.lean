/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Order.Minimal
public import Linglib.Syntax.Feature.Person.Configuration

/-!
# The configuration of a set of individuals

This file defines the configuration of a finite set of individuals, given the individual holding
each speech-act role: the roles whose holders the set contains, together with the number of its
members holding no role. A part of a set has a configuration below it, strictly below when the
part is proper. Where the two roles have different holders, the configuration has as many members
as the set, every configuration below that of a set is the configuration of a part of it, and a
set is minimal among those whose configuration lies in a region exactly when its configuration is
minimal in the region. Statements about minimal configurations, such as the minimal and the unit
augmented number, then hold of the referents themselves.

## Main definitions

* `Person.Configuration.ofFinset`: the configuration of a finite set of individuals.
* `Person.Configuration.ofFinsetHom`: `ofFinset` as an order homomorphism.

## Main results

* `Person.Configuration.ofFinset_strictMono`: a proper part has a strictly smaller configuration.
* `Person.Configuration.card_ofFinset`: the configuration has as many members as the set.
* `Person.Configuration.minimal_ofFinset_iff`: minimality of a set and of its configuration.

## Implementation notes

The holders are a function `SpeechAct.Role → ι` and not an embedding: one individual may hold both
roles, as a speaker addressing themself does, and the order lemmas hold of any such function. The
lemmas that count members or build a part take the injectivity of the holders as a hypothesis.
-/

@[expose] public section

namespace Person.Configuration

open SpeechAct

variable {ι : Type*} [DecidableEq ι] (h : Role → ι) {u v : Finset ι} {r : Role}

/-- The configuration of a set of individuals, `h r` being the holder of the role `r`: the roles
whose holders it contains and the number of its members holding no role. -/
def ofFinset (u : Finset ι) : Configuration :=
  ⟨Finset.univ.filter (h · ∈ u), (u \ Finset.univ.image h).card⟩

@[simp] theorem mem_participants_ofFinset : r ∈ (ofFinset h u).participants ↔ h r ∈ u := by
  simp [ofFinset]

theorem participants_ofFinset_sdiff (u v : Finset ι) :
    (ofFinset h (u \ v)).participants =
      (ofFinset h u).participants \ (ofFinset h v).participants := by
  ext; simp

theorem ofFinset_mono : Monotone (ofFinset h) := fun _ _ hvu ↦
  ⟨fun _ hr ↦ (mem_participants_ofFinset h).2 (hvu ((mem_participants_ofFinset h).1 hr)),
    Finset.card_le_card (Finset.sdiff_subset_sdiff hvu subset_rfl)⟩

/-- `ofFinset` as an order homomorphism. -/
@[simps]
def ofFinsetHom : Finset ι →o Configuration := ⟨ofFinset h, ofFinset_mono h⟩

/-- A proper part of a set of individuals has a strictly smaller configuration. -/
theorem ofFinset_strictMono : StrictMono (ofFinset h) := fun v u hlt ↦ by
  refine lt_of_le_of_ne (ofFinset_mono h hlt.le) fun he ↦ hlt.ne (le_antisymm hlt.le fun z hz ↦ ?_)
  have ho : v \ Finset.univ.image h = u \ Finset.univ.image h :=
    Finset.eq_of_subset_of_card_le (Finset.sdiff_subset_sdiff hlt.le subset_rfl)
      (congrArg others he).ge
  by_cases hzr : z ∈ Finset.univ.image h
  · obtain ⟨r, -, rfl⟩ := Finset.mem_image.1 hzr
    exact (mem_participants_ofFinset h).1
      (congrArg participants he ▸ (mem_participants_ofFinset h).2 hz)
  · exact (Finset.mem_sdiff.1 (ho ▸ Finset.mem_sdiff.2 ⟨hz, hzr⟩)).1

section Injective

variable {h} (hh : Function.Injective h)

include hh

/-- With different holders for the two roles, the configuration of a set has as many members as
the set. -/
theorem card_ofFinset (u : Finset ι) : (ofFinset h u).card = u.card := by
  rw [card, ofFinset, ← Finset.card_image_of_injective _ hh,
    ← Finset.card_inter_add_card_sdiff u (Finset.univ.image h)]
  congr 2
  ext z
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter]
  exact ⟨fun ⟨r, hr, e⟩ ↦ ⟨e ▸ hr, r, e⟩, fun ⟨hz, r, e⟩ ↦ ⟨r, e ▸ hz, e⟩⟩

theorem others_ofFinset (u : Finset ι) :
    (ofFinset h u).others = u.card - (ofFinset h u).participants.card :=
  Nat.eq_sub_of_add_eq' (card_ofFinset hh u)

/-- Every configuration below that of a set of individuals is the configuration of a part of
it, the two roles having different holders. -/
theorem exists_le_ofFinset_eq {y : Configuration} (hle : y ≤ ofFinset h u) :
    ∃ v ≤ u, ofFinset h v = y := by
  obtain ⟨t, m⟩ := y
  obtain ⟨ht, hm⟩ := hle
  obtain ⟨o, ho, rfl⟩ := Finset.exists_subset_card_eq hm
  have ho' : ∀ z ∈ o, z ∈ u ∧ z ∉ Finset.univ.image h := fun z hz ↦ Finset.mem_sdiff.1 (ho hz)
  refine ⟨t.image h ∪ o, fun z hz ↦ ?_, Configuration.ext ?_ ?_⟩
  · rcases Finset.mem_union.1 hz with hz | hz
    · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hz
      exact (mem_participants_ofFinset h).1 (ht hr)
    · exact (ho' z hz).1
  · ext r
    simp only [mem_participants_ofFinset, Finset.mem_union, Finset.mem_image]
    exact ⟨fun hr ↦ hr.elim (fun ⟨r', hr', e⟩ ↦ hh e ▸ hr')
      fun hr ↦ absurd (Finset.mem_image_of_mem h (Finset.mem_univ r)) (ho' _ hr).2,
      fun hr ↦ Or.inl ⟨r, hr, rfl⟩⟩
  · change ((t.image h ∪ o) \ Finset.univ.image h).card = o.card
    congr 1
    ext z
    simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun ⟨hz, hzr⟩ ↦ hz.resolve_left fun ⟨r, _, e⟩ ↦ hzr ⟨r, e⟩,
      fun hz ↦ ⟨Or.inr hz, by simpa using (ho' z hz).2⟩⟩

/-- A set of individuals is minimal among those whose configuration lies in a region exactly
when its configuration is minimal in the region. -/
theorem minimal_ofFinset_iff {P : Configuration → Prop} :
    Minimal (fun v ↦ P (ofFinset h v)) u ↔ Minimal P (ofFinset h u) :=
  minimal_comp_iff_of_strictMono (ofFinset_strictMono h) fun _ _ ↦ exists_le_ofFinset_eq hh

end Injective

end Person.Configuration
