/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.List.Infix

/-!
# Roots

Bloomfield calls a form that can be spoken alone a free form and defines a word as a minimum free
form, one that does not consist of two or more lesser free forms. A word is primary when it
contains no free form other than itself, and Qin's base definition of a root is a morph that
occurs in a primary word, a morphological core. The definition is formal: the meaningless *-fer*
of *refer* is a core. A primary word is either a single free morph or made of bound morphs only,
so [a morph is a core](##Morphology.isCore_iff) exactly when it is free or combines with bound
morphs alone into a primary word, and [every primary word is a
word](##Morphology.IsPrimaryWord.isMinimalFreeForm).

## Implementation notes

Morphs are of an arbitrary type `M` and a language's free forms are a list of lists of them.
The free forms are assumed not to include the empty form where a lemma needs it.

## References

* [bloomfield-1933]
* [qin-2025]
-/

@[expose] public section

namespace Morphology

variable {M : Type*} {F : List (List M)} {w : List M} {m : M}

/-- A word is **primary** ([bloomfield-1933]) when it is a free form containing no free form other
than itself. *man* and *re-ceive* are primary; *boy-ish* and *door-knob* are secondary. -/
def IsPrimaryWord (F : List (List M)) (w : List M) : Prop :=
  w ∈ F ∧ ∀ f ∈ F, f <:+: w → f = w

instance [DecidableEq M] (F : List (List M)) (w : List M) : Decidable (IsPrimaryWord F w) :=
  inferInstanceAs (Decidable (_ ∧ ∀ f ∈ F, _))

/-- A morph is a **morphological core**, a root under [qin-2025]'s base definition, when it occurs
in a primary word. -/
def IsCore (F : List (List M)) (m : M) : Prop := ∃ w, IsPrimaryWord F w ∧ m ∈ w

instance [DecidableEq M] (F : List (List M)) (m : M) : Decidable (IsCore F m) :=
  decidable_of_iff (∃ w ∈ F, IsPrimaryWord F w ∧ m ∈ w)
    ⟨fun ⟨w, _, h⟩ ↦ ⟨w, h⟩, fun ⟨w, h⟩ ↦ ⟨w, h.1.1, h⟩⟩

/-- A **minimum free form** ([bloomfield-1933]) is a free form that cannot be analyzed into two
or more parts each of which is a free form. -/
def IsMinimalFreeForm (F : List (List M)) (w : List M) : Prop :=
  w ∈ F ∧ ∀ ps : List (List M), ps.flatten = w → [] ∉ ps → (∀ p ∈ ps, p ∈ F) → ps.length ≤ 1

theorem isPrimaryWord_singleton (h : [] ∉ F) (hm : [m] ∈ F) : IsPrimaryWord F [m] :=
  ⟨hm, fun _ hf hfm ↦ hfm.eq_of_length_le (List.length_pos_iff.2 fun e ↦ h (e ▸ hf))⟩

theorem isCore_of_singleton_mem (h : [] ∉ F) (hm : [m] ∈ F) : IsCore F m :=
  ⟨[m], isPrimaryWord_singleton h hm, List.mem_singleton_self m⟩

/-- A primary word of more than one morph is made of bound forms ([bloomfield-1933]'s derived
primary words, *re-ceive*). -/
theorem IsPrimaryWord.singleton_not_mem (hw : IsPrimaryWord F w) (hlen : 1 < w.length)
    {x : M} (hx : x ∈ w) : [x] ∉ F := fun hxF ↦
  hlen.ne (congrArg List.length (hw.2 _ hxF ((List.singleton_infix_iff _ _).2 hx)))

/-- A morph is a core exactly when it is a free form or occurs in a primary word whose morphs are
all bound, so that a bound morph is a core only together with another bound morph
([qin-2025]). -/
theorem isCore_iff (h : [] ∉ F) :
    IsCore F m ↔ [m] ∈ F ∨ ∃ w, IsPrimaryWord F w ∧ m ∈ w ∧ ∀ x ∈ w, [x] ∉ F := by
  refine ⟨fun ⟨w, hw, hm⟩ ↦ ?_, ?_⟩
  · rcases Nat.lt_or_ge 1 w.length with hlen | hlen
    · exact .inr ⟨w, hw, hm, fun x hx ↦ hw.singleton_not_mem hlen hx⟩
    · obtain ⟨y, rfl⟩ := List.length_eq_one_iff.1 (le_antisymm hlen (List.length_pos_of_mem hm))
      exact .inl (List.mem_singleton.1 hm ▸ hw.1)
  · rintro (hm | ⟨w, hw, hm, -⟩)
    exacts [isCore_of_singleton_mem h hm, ⟨w, hw, hm⟩]

theorem isMinimalFreeForm_of_take (hw : w ∈ F) (h : ∀ i < w.length, 0 < i → w.take i ∉ F) :
    IsMinimalFreeForm F w := by
  refine ⟨hw, fun ps hps hne hfree ↦ ?_⟩
  match ps, hps, hne, hfree with
  | [], _, _, _ => simp
  | [_], _, _, _ => simp
  | p :: q :: rest, hps, hne, hfree =>
    exfalso
    have hp : p ≠ [] := fun e ↦ hne (e ▸ List.mem_cons_self)
    have hq : q ≠ [] := fun e ↦ hne (e ▸ List.mem_cons_of_mem _ List.mem_cons_self)
    subst hps
    refine h p.length ?_ (List.length_pos_iff.2 hp) ?_
    · have := List.length_pos_iff.2 hq; simp; omega
    · simpa using hfree p List.mem_cons_self

/-- A primary word is a word, a minimum free form. -/
theorem IsPrimaryWord.isMinimalFreeForm (hw : IsPrimaryWord F w) : IsMinimalFreeForm F w :=
  isMinimalFreeForm_of_take hw.1 fun i hi _ hiF ↦ by
    have := congrArg List.length (hw.2 _ hiF (w.take_prefix i).isInfix)
    simp only [List.length_take] at this
    omega

end Morphology
