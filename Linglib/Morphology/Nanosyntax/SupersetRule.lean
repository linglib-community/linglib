/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Morphology.Exponence.SupersetRule
public import Linglib.Morphology.Nanosyntax.Lexicon

/-!
# Lexical entries as superset rules

A rule over a containment hierarchy is read as a lexical entry that stores the spine up to the
rule's span. On spines, the spellout of such entries is the spellout of the rules, and the
lexicalization algorithm gives each grade the one exponent the rules spell out there.

## Main definitions

* `Morphology.Nanosyntax.spineUpTo`: the spine of the first features of a sequence.
* `Morphology.Nanosyntax.LexicalEntry.ofSupersetRule`: a rule read as a lexical entry.

## Main results

* `Morphology.Nanosyntax.spellout_ofSupersetRule`: on spines, spellout is the spellout of the
  rules.
* `Morphology.Nanosyntax.exponents_ofSupersetRule`: the algorithm gives each grade the exponent
  the rules spell out there.

## TODO

* `Morphology/Exponence/SupersetRule.lean` relates its rules to span rules directly; each should
  instead prove what it generates in the shared form, contiguity of the paradigm.

## References

* [starke-2009]
* [caha-2009]
-/

@[expose] public section

namespace Morphology.Nanosyntax

open Morphology Minimalist SyntacticObject

variable {F : Type} {α : Type*}

/-! ### Spellout over containment hierarchies -/

/-- The spine of the first `k + 1` features of a sequence. -/
def spineUpTo (feat : ℕ → F) (k : ℕ) : SyntacticObject (Option F) :=
  spine (feat 0) ((List.range k).map (feat ∘ Nat.succ))

theorem spineUpTo_containsOrEq_iff (feat : ℕ → F) (r k : ℕ) :
    (spineUpTo feat k).ContainsOrEq (spineUpTo feat r) ↔ r ≤ k := by
  rw [spineUpTo, spineUpTo, spine_containsOrEq_spine_iff]
  refine ⟨fun h ↦ by simpa using h.length_le, fun h ↦ List.IsPrefix.map _ ?_⟩
  rw [show List.range r = (List.range k).take r by simp [List.take_range, h]]
  exact List.take_prefix _ _

theorem card_leaves_spineUpTo_strictMono (feat : ℕ → F) :
    StrictMono fun k ↦ (spineUpTo feat k).leaves.card := fun r k h ↦
  Contains.card_leaves_lt (contains_iff_containsOrEq_and_ne.2
    ⟨(spineUpTo_containsOrEq_iff feat r k).2 h.le, fun heq ↦
      h.not_ge ((spineUpTo_containsOrEq_iff feat k r).1 (heq ▸ Relation.ReflTransGen.refl))⟩)

/-- An entry of the containment engine read as an entry storing the spine up to its span. -/
def LexicalEntry.ofSupersetRule {n : ℕ} (feat : ℕ → F) (e : SupersetRule n α) :
    LexicalEntry F α :=
  ⟨spineUpTo feat e.spans, e.exponent⟩

/-- On spines, spellout is the spellout of the containment engine, since containment of spines
is comparison of their lengths. -/
theorem spellout_ofSupersetRule [DecidableEq F] {n : ℕ} (feat : ℕ → F)
    (v : RuleSet (SupersetRule n α)) (g : Fin n) :
    spellout (v.map (LexicalEntry.ofSupersetRule feat)) (spineUpTo feat g) =
      SupersetRule.spellout v g := by
  rw [spellout, RuleSet.realize, RuleSet.selectBy_map (c := g)
    (f := fun e : SupersetRule n α ↦ OrderDual.toDual e.spans)
    (fun _ _ ↦ (spineUpTo_containsOrEq_iff feat _ _).trans Fin.val_fin_le)
    fun r _ s _ ↦ by
      simp only [LexicalEntry.ofSupersetRule, OrderDual.toDual_le_toDual]
      exact ((card_leaves_spineUpTo_strictMono feat).le_iff_le).trans Fin.val_fin_le,
    Option.map_map]
  rfl

/-- On a lexicon of containment entries the algorithm gives each grade the single exponent the
containment engine spells out there. -/
theorem exponents_ofSupersetRule [DecidableEq F] {n : ℕ} {feat : ℕ → F}
    (hf : ∀ k, feat (k + 1) ≠ feat 0)
    (v : RuleSet (SupersetRule n α)) (g : Fin n) :
    exponents (spellout (v.map (LexicalEntry.ofSupersetRule feat)))
        ((List.range ((g : ℕ) + 1)).map feat) =
      (SupersetRule.spellout v g).map fun x ↦ [x] := by
  rw [List.range_succ_eq_map, List.map_cons, List.map_map,
    exponents_cons_of_forall_bare (isLowerSpellout_spellout _)]
  · rw [show spine (feat 0) ((List.range g).map (feat ∘ Nat.succ)) = spineUpTo feat g from rfl,
      spellout_ofSupersetRule]
  · intro f hf'
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hf'
    refine spellout_eq_none_iff.2 fun e he hm ↦ ?_
    obtain ⟨r, -, rfl⟩ := List.mem_map.1 he
    exact hf k (eq_of_spine_containsOrEq_spine (gs := []) hm)

end Morphology.Nanosyntax
