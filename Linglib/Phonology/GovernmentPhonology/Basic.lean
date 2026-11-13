/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Order.SuccPred.Nat
public import Mathlib.Order.WithBot

/-!
# Government Phonology: nuclei and government

In Government Phonology the syllabic position of a segment is defined by lateral relations
among positions, government and licensing, and not by the constituent it belongs to. In Strict
CV, where every syllable is a consonantal position followed by a vocalic one, the nuclei of a
domain form a sequence and contract these relations leftwards. This file gives the nuclei and
the relation of government between them. A nucleus governs the nucleus before it when that
nucleus is unexpressed, is not enclosed in a domain of infrasegmental government, and has a
melody no more complex than the governor is strong. Government is taken to be local, so that
each governor has one target, and a governed nucleus
[governs nothing](##GovernmentPhonology.Governs.not_governs), so the governing pairs of a domain
are disjoint pairs of neighbours. How strong each nucleus is varies with the language and is the
theory's parameter, its lateral actorship.

## Implementation notes

A domain is the list of its nuclei, each with its melody and whether it is phonetically
expressed, so that domains concatenate as lists. Government is local, between a nucleus and the
one before it, as [scheer-cyran-2018] state the theory after [brun-trigaud-scheer-2010].
[scheer-2004] lets government apply over a domain of infrasegmental government instead, and the
two agree on which nuclei are unexpressed when the enclosed nucleus is as strong as the nucleus
that supports its domain. Melody is ordered by complexity, and the strength of a nucleus is the
most complex melody it can govern. This generalises the complexity condition, which
[cavirani-2022] adopts as the case where a nucleus is as strong as its own melody is complex.
What may support a domain of infrasegmental government is open in [scheer-cyran-2018] and is a
field of the parameter. That a governed nucleus has no strength is [scheer-2004]'s position for
every nucleus and [cavirani-2022]'s for empty ones.

## TODO

Whether two consonants may contract infrasegmental government is a flag on the nucleus between
them and is not derived from their elements. Licensing ability is a yes or no, though a final
empty nucleus may act and yet be too weak a licensor for vowel length.

## References

* [lowenstamm-1996]
* [kaye-lowenstamm-vergnaud-1990]
* [charette-1991]
* [scheer-2004]
* [brun-trigaud-scheer-2010]
* [scheer-cyran-2018]
* [cavirani-2022]
-/

@[expose] public section

namespace GovernmentPhonology

/-! ### Nuclei -/

/-- The melody of a nucleus ([scheer-2004] (73)): none, melody that alternates with zero, or
melody that is always expressed. -/
inductive Melody
  /-- No melody. -/
  | empty
  /-- Melody that is expressed unless the nucleus is governed. -/
  | floating
  /-- Associated melody. -/
  | associated
  deriving DecidableEq, Repr

/-- The complexity of a melody. -/
def Melody.complexity : Melody → ℕ
  | .empty => 0
  | .floating => 1
  | .associated => 2

theorem Melody.complexity_injective : Function.Injective Melody.complexity := by
  rintro (_ | _ | _) (_ | _ | _) h <;> first | rfl | cases h

/-- Melodies are ordered by complexity. -/
instance : LinearOrder Melody := LinearOrder.lift' Melody.complexity Melody.complexity_injective

/-- A nucleus of a domain. -/
structure Nucleus where
  /-- The melody of the nucleus. -/
  melody : Melody
  /-- The nucleus is phonetically expressed. -/
  expressed : Bool := false
  /-- The consonants flanking the nucleus may contract infrasegmental government, the following
  one governing the preceding one ([scheer-2004] (49a)). -/
  cluster : Bool := false
  deriving DecidableEq, Repr

/-- The lateral actorship of a language: what each nucleus can do when it is not governed,
according to its melody, whether it is expressed, and whether it is final in its domain. -/
structure Actorship where
  /-- The most complex melody the nucleus can govern, `⊥` when it cannot govern. -/
  strength : Nucleus → Bool → WithBot Melody
  /-- The nucleus can license. -/
  licenses : Nucleus → Bool → Bool
  /-- The nucleus supports a domain of infrasegmental government whose governing consonant is
  its onset ([scheer-2004] (50)). -/
  supports : Nucleus → Bool → Bool
  /-- A final nucleus may be unexpressed, as in a language with consonant-final words. -/
  finalEmpty : Bool

/-- The actorship of [scheer-2004] (386) with local government. A full nucleus governs anything
and licenses. Schwa, a nucleus expressed without associated melody, and the unexpressed final
nucleus have the strengths `schwa` and `final` and license as `schwaLicenses` and
`finalLicenses` say; a final nucleus that governs only nuclei without melody ((378)) has the
strength of an empty melody. An empty nucleus that is unexpressed and not final, which in a
domain satisfying the Empty Category Principle is ungoverned only when it is enclosed, governs and
licenses as a full nucleus does, after [brun-trigaud-scheer-2010]. Expressed nuclei support a
domain of infrasegmental government, and the unexpressed final nucleus does where
`finalSupports`. That an epenthetic vowel acts as schwa does, and that an enclosed nucleus
governs alternating vowels, are choices no source makes. -/
def Actorship.ltp (schwa final : WithBot Melody)
    (schwaLicenses finalLicenses finalSupports : Bool) (finalEmpty : Bool := true) :
    Actorship where
  strength x isFinal :=
    if x.expressed then (if x.melody = .associated then ↑Melody.associated else schwa)
    else if isFinal then final
    else if x.melody = .empty then ↑Melody.associated else ⊥
  licenses x isFinal :=
    if x.expressed then (decide (x.melody = .associated) || schwaLicenses)
    else if isFinal then finalLicenses else decide (x.melody = .empty)
  supports x isFinal := x.expressed || (isFinal && finalSupports)
  finalEmpty := finalEmpty

variable (A : Actorship) (l : List Nucleus) {i j k : ℕ}

/-! ### Government between nuclei -/

/-- The first nucleus of a stretch is enclosed in a domain of infrasegmental government: it is
unexpressed and empty, its flanking consonants may contract government, and the next nucleus
supports the domain. -/
def EnclosedHead : List Nucleus → Prop
  | x :: y :: r => x.expressed = false ∧ x.melody = .empty ∧ x.cluster = true ∧
      A.supports y (decide (r = [])) = true
  | _ => False

instance : DecidablePred (EnclosedHead A)
  | [] | [_] => isFalse fun h ↦ h
  | _ :: _ :: _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- The first nucleus of a stretch is governed by the next: it is unexpressed and not enclosed,
and the next nucleus is not itself governed and is strong enough for its melody. -/
def GovernedHead : List Nucleus → Prop
  | [] => False
  | x :: r => x.expressed = false ∧ ¬ EnclosedHead A (x :: r) ∧ ¬ GovernedHead r ∧
      ∃ y ∈ r.head?, (x.melody : WithBot Melody) ≤ A.strength y (decide (r.tail = []))

instance instDecidablePredGovernedHead : DecidablePred (GovernedHead A)
  | [] => isFalse fun h ↦ h
  | _ :: r =>
    have := instDecidablePredGovernedHead r
    inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- Nucleus `i` is enclosed in a domain of infrasegmental government. -/
def Enclosed (i : ℕ) : Prop := EnclosedHead A (l.drop i)

/-- Nucleus `i` is governed. -/
def Governed (i : ℕ) : Prop := GovernedHead A (l.drop i)

/-- Nucleus `j` governs nucleus `i` ([scheer-2004] (19)). -/
def Governs (j i : ℕ) : Prop := i + 1 = j ∧ Governed A l i

/-- Nucleus `j` is a governor: it is not governed and has some strength. -/
def IsGovernor (j : ℕ) : Prop :=
  ¬ Governed A l j ∧ ∃ x ∈ l[j]?, A.strength x (decide (j + 1 = l.length)) ≠ ⊥

/-- Nucleus `j` is a licensor: it is not governed and can license. -/
def IsLicensor (j : ℕ) : Prop :=
  ¬ Governed A l j ∧ ∃ x ∈ l[j]?, A.licenses x (decide (j + 1 = l.length)) = true

instance : DecidablePred (Enclosed A l) := fun _ ↦ inferInstanceAs (Decidable (EnclosedHead A _))

instance : DecidablePred (Governed A l) := fun _ ↦ inferInstanceAs (Decidable (GovernedHead A _))

instance : Decidable (Governs A l j i) := inferInstanceAs (Decidable (_ ∧ _))

instance : DecidablePred (IsGovernor A l) := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

instance : DecidablePred (IsLicensor A l) := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

variable {A l}

/-- The first nucleus of a stretch is governed exactly as `GovernedHead` unfolds. -/
theorem governedHead_cons {x : Nucleus} {r : List Nucleus} : GovernedHead A (x :: r) ↔
    x.expressed = false ∧ ¬ EnclosedHead A (x :: r) ∧ ¬ GovernedHead A r ∧
      ∃ y ∈ r.head?, (x.melody : WithBot Melody) ≤ A.strength y (decide (r.tail = [])) :=
  Iff.rfl

theorem governed_iff : Governed A l i ↔ ¬ Enclosed A l i ∧ ¬ Governed A l (i + 1) ∧
    ∃ x ∈ l[i]?, x.expressed = false ∧ ∃ y ∈ l[i + 1]?,
      (x.melody : WithBot Melody) ≤ A.strength y (decide (i + 2 = l.length)) := by
  rcases Nat.lt_or_ge i l.length with h | h
  · have key (y : Nucleus) (hy : l[i + 1]? = some y) :
        decide ((l.drop (i + 1)).tail = []) = decide (i + 2 = l.length) := by
      have := (List.getElem?_eq_some_iff.1 hy).1
      exact decide_eq_decide.2 (by rw [List.tail_drop, List.drop_eq_nil_iff]; omega)
    rw [Governed, Enclosed, List.drop_eq_getElem_cons h, governedHead_cons, List.head?_drop]
    simp only [List.getElem?_eq_getElem h, Option.mem_def, Option.some.injEq, exists_eq_left']
    exact ⟨fun ⟨h1, h2, h3, y, hy, hle⟩ ↦ ⟨h2, h3, h1, y, hy, by rwa [← key y hy]⟩,
      fun ⟨h2, h3, h1, y, hy, hle⟩ ↦ ⟨h1, h2, h3, y, hy, by rwa [key y hy]⟩⟩
  · refine iff_of_false (by simp [Governed, List.drop_eq_nil_of_le h, GovernedHead]) ?_
    rintro ⟨-, -, x, hx, -⟩
    simp [List.getElem?_eq_none h] at hx

/-- The lateral relations of a stretch are those it has at the end of any longer domain. -/
theorem governed_append (l₁ l₂ : List Nucleus) :
    Governed A (l₁ ++ l₂) (i + l₁.length) ↔ Governed A l₂ i := by
  rw [Governed, Governed, Nat.add_comm, ← List.drop_drop, List.drop_left]

namespace Governs

/-- Government is local: the governed nucleus is the one before the governor. -/
theorem covBy (h : Governs A l j i) : i ⋖ j :=
  Nat.covBy_iff_add_one_eq.2 h.1

/-- A governor governs one nucleus. -/
theorem eq_left (h : Governs A l j i) (h' : Governs A l j k) : i = k :=
  Nat.add_right_cancel (h.1.trans h'.1.symm)

/-- A nucleus is governed by one governor. -/
theorem eq_right (h : Governs A l j i) (h' : Governs A l k i) : j = k :=
  h.1.symm.trans h'.1

/-- A governed nucleus governs nothing. -/
theorem not_governs (h : Governs A l j i) : ¬ Governs A l i k := by
  rintro ⟨rfl, hk⟩
  exact (governed_iff.1 hk).2.1 h.2

/-- The governed nucleus is unexpressed. -/
theorem not_expressed (h : Governs A l j i) : ∃ x ∈ l[i]?, x.expressed = false :=
  let ⟨_, _, x, hx, hxe, _⟩ := governed_iff.1 h.2
  ⟨x, hx, hxe⟩

protected theorem isGovernor (h : Governs A l j i) : IsGovernor A l j := by
  obtain ⟨rfl, hg⟩ := h
  obtain ⟨-, hn, x, -, -, y, hy, hle⟩ := governed_iff.1 hg
  refine ⟨hn, y, hy, fun h0 ↦ ?_⟩
  rw [show A.strength y (decide (i + 2 = l.length)) = ⊥ from h0] at hle
  exact WithBot.coe_ne_bot (le_bot_iff.1 hle)

end Governs

end GovernmentPhonology
