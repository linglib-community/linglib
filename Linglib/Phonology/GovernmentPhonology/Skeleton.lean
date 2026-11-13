/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Autosegmental.Candidate
public import Linglib.Phonology.Autosegmental.Skeleton
public import Mathlib.Order.Hom.Basic

/-!
# Strict CV skeletons

In Strict CV the skeleton is a sequence of CV units, a consonantal slot followed by a vocalic
one, so strict skeletons are [closed under concatenation](##Autosegmental.Skeleton.IsStrict.append)
and a word built from strict morphs is strict. Unit `j` of a form has its onset at slot `2j` and
its nucleus at slot `2j + 1`, which in a strict form
[are consonantal](##Autosegmental.Skeleton.IsStrict.value_onset) and
[vocalic](##Autosegmental.Skeleton.IsStrict.value_nucleus). The clusters of a candidate are the
units whose onset may be governed by the next onset, as two consonants that contract
infrasegmental government.

## Implementation notes

Only the following onset is tried as the governor of an onset. A governing first consonant
would have to be licensed by the empty nucleus that the domain encloses, which Government
Licensing excludes, so that infrasegmental government is head-final ([scheer-2004] (52)).

## References

* [lowenstamm-1996]
* [scheer-2004]
-/

@[expose] public section

namespace Autosegmental

namespace Skeleton

variable {s t : Skeleton}

/-- A skeleton is strict when it is a sequence of CV units ([lowenstamm-1996]). -/
def IsStrict (t : Skeleton) : Prop := ∃ n, t = (List.replicate n [Slot.C, .V]).flatten

private theorem length_units (n : ℕ) : (List.replicate n [Slot.C, .V]).flatten.length = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, List.flatten_cons, List.length_append, ih]; simp; omega

theorem isStrict_iff : IsStrict t ↔ t = (List.replicate (t.length / 2) [Slot.C, .V]).flatten := by
  refine ⟨fun ⟨n, h⟩ ↦ ?_, fun h ↦ ⟨_, h⟩⟩
  have : t.length / 2 = n := by rw [h, length_units]; omega
  rw [this, ← h]

instance : DecidablePred IsStrict := fun _ ↦ decidable_of_iff' _ isStrict_iff

@[simp] theorem isStrict_nil : IsStrict [] := ⟨0, rfl⟩

/-- A CV unit is a strict skeleton. -/
theorem isStrict_unit : IsStrict [.C, .V] := ⟨1, rfl⟩

/-- Strict skeletons are closed under concatenation. -/
theorem IsStrict.append : IsStrict s → IsStrict t → IsStrict (s ++ t) := by
  rintro ⟨m, rfl⟩ ⟨n, rfl⟩
  exact ⟨m + n, by rw [List.replicate_add, List.flatten_append]⟩

theorem IsStrict.two_mul_length_div_two (h : IsStrict t) : 2 * (t.length / 2) = t.length := by
  obtain ⟨n, rfl⟩ := h
  rw [length_units]
  omega

theorem IsStrict.getElem_two_mul (h : IsStrict t) (j : ℕ) (hj : 2 * j < t.length) :
    t[2 * j] = .C := by
  obtain ⟨n, rfl⟩ := h
  induction n generalizing j with
  | zero => simp at hj
  | succ n ih =>
    cases j with
    | zero => rfl
    | succ j =>
      simp only [List.replicate_succ, List.flatten_cons, List.cons_append, List.nil_append,
        Nat.mul_add, Nat.mul_one, List.getElem_cons_succ]
      exact ih j _

theorem IsStrict.getElem_two_mul_add_one (h : IsStrict t) (j : ℕ) (hj : 2 * j + 1 < t.length) :
    t[2 * j + 1] = .V := by
  obtain ⟨n, rfl⟩ := h
  induction n generalizing j with
  | zero => simp at hj
  | succ n ih =>
    cases j with
    | zero => rfl
    | succ j =>
      simp only [List.replicate_succ, List.flatten_cons, List.cons_append, List.nil_append,
        Nat.mul_add, Nat.mul_one, List.getElem_cons_succ]
      exact ih j _

end Skeleton

variable {T M : Type}

/-- The skeleton of a form is the sequence of its slots. -/
def AR.skeleton (u : AR (TwoTier (Sponsored T M) (Sponsored Slot M))) : Skeleton :=
  (u.word .lower).map (·.value)

namespace AR

variable (u v : AR (TwoTier (Sponsored T M) (Sponsored Slot M)))

@[simp] theorem length_skeleton : u.skeleton.length = (u.word .lower).length := List.length_map _

@[simp] theorem skeleton_one :
    (1 : AR (TwoTier (Sponsored T M) (Sponsored Slot M))).skeleton = [] := rfl

/-- The skeleton of a word is the concatenation of the skeletons of its morphs. -/
@[simp] theorem skeleton_mul : (u * v).skeleton = u.skeleton ++ v.skeleton := List.map_append

@[simp] theorem skeleton_morph (m : M) (us : List T) (ls : List Slot) (lines : Finset (ℕ × ℕ)) :
    (morph m us ls lines).skeleton = ls := by
  simp [skeleton, Function.comp_def]

@[simp] theorem getElem_skeleton (i : ℕ) (h : i < u.skeleton.length) :
    u.skeleton[i] = ((u.word .lower)[i]'(by simpa using h)).value := List.getElem_map _

end AR

end Autosegmental

namespace StrictCV

open Autosegmental

variable {T M : Type} (u : AR (TwoTier (Sponsored T M) (Sponsored Slot M)))

/-! ### CV units -/

/-- The number of CV units. -/
def units : ℕ := (u.word .lower).length / 2

/-- The onset of CV unit `j`. -/
def onset (j : Fin (units u)) : Fin (u.word .lower).length :=
  ⟨2 * j, by have := j.isLt; unfold units at this; omega⟩

/-- The nucleus of CV unit `j`. -/
def nucleus (j : Fin (units u)) : Fin (u.word .lower).length :=
  ⟨2 * j + 1, by have := j.isLt; unfold units at this; omega⟩

@[simp] theorem val_onset (j : Fin (units u)) : (onset u j).val = 2 * j := rfl

@[simp] theorem val_nucleus (j : Fin (units u)) : (nucleus u j).val = 2 * j + 1 := rfl

theorem strictMono_onset : StrictMono (onset u) :=
  fun _ _ h ↦ Fin.lt_def.2 (Nat.mul_lt_mul_of_pos_left (Fin.lt_def.1 h) Nat.two_pos)

theorem strictMono_nucleus : StrictMono (nucleus u) :=
  fun _ _ h ↦ Fin.lt_def.2 <| Nat.succ_lt_succ <|
    Nat.mul_lt_mul_of_pos_left (Fin.lt_def.1 h) Nat.two_pos

/-- `onset` as an order embedding of the units into the slots. -/
def onsetOrderEmb : Fin (units u) ↪o Fin (u.word .lower).length :=
  .ofStrictMono (onset u) (strictMono_onset u)

/-- `nucleus` as an order embedding of the units into the slots. -/
def nucleusOrderEmb : Fin (units u) ↪o Fin (u.word .lower).length :=
  .ofStrictMono (nucleus u) (strictMono_nucleus u)

@[simp] theorem coe_onsetOrderEmb : ⇑(onsetOrderEmb u) = onset u := rfl

@[simp] theorem coe_nucleusOrderEmb : ⇑(nucleusOrderEmb u) = nucleus u := rfl

theorem onset_injective : Function.Injective (onset u) := (strictMono_onset u).injective

theorem nucleus_injective : Function.Injective (nucleus u) := (strictMono_nucleus u).injective

/-- No slot is both an onset and a nucleus. -/
theorem onset_ne_nucleus (j k : Fin (units u)) : onset u j ≠ nucleus u k :=
  fun h ↦ by have := congrArg Fin.val h; simp only [val_onset, val_nucleus] at this; omega

theorem onset_lt_nucleus (j : Fin (units u)) : onset u j < nucleus u j :=
  Fin.lt_def.2 (Nat.lt_succ_self _)

variable {u} {v : AR (TwoTier (Sponsored T M) (Sponsored Slot M))}

/-- The units of a word after a strict form are the units of both. -/
theorem units_mul (h : u.skeleton.IsStrict) : units (u * v) = units u + units v := by
  have := h.two_mul_length_div_two
  simp only [AR.length_skeleton] at this
  simp only [units, AR.word_mul, List.length_append]
  omega

/-- The onset of a CV unit of a strict form is a consonantal slot. -/
theorem _root_.Autosegmental.Skeleton.IsStrict.value_onset (h : u.skeleton.IsStrict)
    (j : Fin (units u)) : (u.word .lower)[onset u j].value = .C :=
  (AR.getElem_skeleton u _ (by simpa using (onset u j).isLt)).symm.trans (h.getElem_two_mul j _)

/-- The nucleus of a CV unit of a strict form is a vocalic slot. -/
theorem _root_.Autosegmental.Skeleton.IsStrict.value_nucleus (h : u.skeleton.IsStrict)
    (j : Fin (units u)) : (u.word .lower)[nucleus u j].value = .V :=
  (AR.getElem_skeleton u _ (by simpa using (nucleus u j).isLt)).symm.trans
    (h.getElem_two_mul_add_one j _)

/-! ### The nuclei of a candidate -/

variable (c : Candidate u)

/-- The units whose onset may be governed by the next onset, given which melodies `MayGovern`
allows to contract infrasegmental government ([scheer-2004] (49a)). -/
def clusters (MayGovern : List T → List T → Prop) [∀ a b, Decidable (MayGovern a b)] :
    Finset (Fin (units u)) :=
  Finset.univ.filter fun j ↦ ∃ k : Fin (units u), k.val = j.val + 1 ∧
    MayGovern (c.tierValues (onset u k)) (c.tierValues (onset u j))

end StrictCV
