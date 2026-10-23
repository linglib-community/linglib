/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Morphology.Morph
public import Mathlib.Data.List.Infix

/-!
# Roots

The formal definition of roothood over `Morph`, relative to a fragment's word
and free-form inventories ([bloomfield-1933], the base definition of
[qin-2025]): a morph is a root iff it occurs in a *primary word* — one with no
free form as a proper part. The definition is deliberately inclusive
(meaning-free cores like *-fer* qualify; so do free function words);
`Studies/Qin2025.lean` grades instances by canonicity, and
[haspelmath-2025b]'s contentfulness-gated alternative is
`Studies/Haspelmath2025b.lean`. Consonantal skeletons are
`ConsonantalRoot`; DM's acategorial root is `DistributedMorphology.Root`
(`Morphology/DistributedMorphology/Basic.lean`).

## Main declarations

* `IsPrimaryWord` — no proper contiguous part is a free form.
* `Morph.IsCoreIn` — the root property: occurrence in a primary word.
* `Morph.IsTypicalAffixIn` — occurrence in secondary words only.
* `IsMinimalFreeForm` — Bloomfield's word, a free form not analyzable into
  free forms.
-/

@[expose] public section

namespace Morphology

/-- A word is **primary** ([bloomfield-1933]): no proper contiguous part of
it is a free form. *cat* and *refer* are primary; *cats* and *blackbirds* are
secondary. -/
def IsPrimaryWord (freeForms : List (List Morph)) (w : List Morph) : Prop :=
  ∀ f ∈ freeForms, f.length < w.length → ¬ f <:+: w

instance (freeForms : List (List Morph)) (w : List Morph) :
    Decidable (IsPrimaryWord freeForms w) :=
  inferInstanceAs (Decidable (∀ f ∈ freeForms, _ → _))

/-- A **morphological core**, [qin-2025]'s base definition of a root, is a
morph occurring in some primary word. -/
def Morph.IsCoreIn (m : Morph) (words freeForms : List (List Morph)) : Prop :=
  ∃ w ∈ words, IsPrimaryWord freeForms w ∧ m ∈ w

instance (m : Morph) (words freeForms : List (List Morph)) :
    Decidable (m.IsCoreIn words freeForms) :=
  inferInstanceAs (Decidable (∃ w ∈ words, _))

/-- A **typical affix** occurs only in secondary words ([bloomfield-1933]):
*-s* and *-ness* attach to free forms. -/
def Morph.IsTypicalAffixIn (m : Morph)
    (words freeForms : List (List Morph)) : Prop :=
  ∀ w ∈ words, m ∈ w → ¬ IsPrimaryWord freeForms w

theorem isPrimaryWord_singleton {freeForms : List (List Morph)}
    (h : [] ∉ freeForms) (m : Morph) : IsPrimaryWord freeForms [m] := by
  intro f hf hlen _
  exact h (List.length_eq_zero_iff.mp (Nat.lt_one_iff.mp hlen) ▸ hf)

theorem Morph.isCoreIn_of_free_word {words freeForms : List (List Morph)}
    {m : Morph} (hw : [m] ∈ words) (h : [] ∉ freeForms) :
    m.IsCoreIn words freeForms :=
  ⟨[m], hw, isPrimaryWord_singleton h m, List.mem_singleton_self m⟩

/-- A **minimum free form** ([bloomfield-1933]) is a free form that cannot be analyzed into two
or more parts each of which is a free form. -/
def IsMinimalFreeForm (freeForms : List (List Morph)) (w : List Morph) : Prop :=
  w ∈ freeForms ∧ ∀ ps : List (List Morph), ps.flatten = w → [] ∉ ps →
    (∀ p ∈ ps, p ∈ freeForms) → ps.length ≤ 1

theorem isMinimalFreeForm_of_take {freeForms : List (List Morph)} {w : List Morph}
    (hw : w ∈ freeForms) (h : ∀ i < w.length, 0 < i → w.take i ∉ freeForms) :
    IsMinimalFreeForm freeForms w := by
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

end Morphology
