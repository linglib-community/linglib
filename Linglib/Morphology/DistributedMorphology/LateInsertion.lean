/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Morphology.DistributedMorphology.Spellout
public import Linglib.Syntax.Minimalist.Linearization.Spellout

/-!
# Late insertion

The syntax hands PF a spell-out domain: the pronounced terminals of a linearized syntactic
object, left to right, each read as a feature bundle (`SpelloutDomain.ofLinearized`). The
postsyntactic pipeline then runs on it and Vocabulary Insertion realizes each surviving position
in its neighborhood: late insertion, on which no phonological content travels through the syntax.
Early insertion is the degenerate case: over the vocabulary whose items each spell out one
terminal's own token as its lexically listed form, the empty-module pipeline returns exactly the
carrier's `pfPhon`, so terminals carrying their forms compute what one context-free item per
token computes, and contextual allomorphy is precisely what such a vocabulary cannot state.

## Main definitions

* `DistributedMorphology.SpelloutDomain.ofLinearized`: the handover.
* `DistributedMorphology.earlyItems`, `DistributedMorphology.earlySpellout`: one context-free
  item per token, spelling out its lexically listed form, and the pipeline it drives.

## Main results

* `DistributedMorphology.pf_earlySpellout`: the early pipeline realizes each token's listed form.
* `DistributedMorphology.pfPhon_eq_earlyInsertion`: `pfPhon` is the early-insertion pipeline.

## References

* [halle-marantz-1993]
* [embick-noyer-2001]
-/

@[expose] public section

namespace DistributedMorphology

open Morphology.Exponence Minimalist

variable {Bundle : Type*}

/-- The spell-out domain of a linearized syntactic object: its pronounced terminals, left to
right, each read as a feature bundle. -/
def SpelloutDomain.ofLinearized (feats : LexicalItem.Token → Bundle)
    (t : LinearizedSyntacticObject) : SpelloutDomain Bundle :=
  (pfYield t).map feats

/-! ### Early insertion -/

/-- The early-insertion vocabulary over the tokens `toks`: each token its own atomic feature,
spelled out as its lexically listed form. -/
def earlyItems (toks : List LexicalItem.Token) :
    RuleSet (VocabularyItem LexicalItem.Token String) :=
  toks.map fun tok ↦ {tok} ⟷ tok.item.phonForm

/-- Early insertion: no postsyntactic modules, each position realizing the Subset Principle's
exponent for the early vocabulary. -/
def earlySpellout (toks : List LexicalItem.Token) :
    Spellout (Finset LexicalItem.Token) String :=
  ⟨[], fun n ↦ (subsetPrinciple (earlyItems toks) n).toList⟩

theorem applicable_earlyItems {toks : List LexicalItem.Token} (hnd : toks.Nodup)
    {tok : LexicalItem.Token} (h : tok ∈ toks) {n : Neighborhood (Finset LexicalItem.Token)}
    (hfoc : n.focus = {tok}) :
    (earlyItems toks).applicable n = [{tok} ⟷ tok.item.phonForm] := by
  rw [RuleSet.applicable, earlyItems, List.filter_map]
  have hf : (toks.filter fun tok' ↦
        decide (Applies ({tok'} ⟷ tok'.item.phonForm) n)) = toks.filter (· == tok) := by
    refine List.filter_congr fun tok' _ ↦ ?_
    exact decide_eq_decide.2 (by
      simp [VocabularyItem.applies_ofFeatures, hfoc])
  rw [show (fun r ↦ decide (Applies r n)) ∘ (fun tok' ↦ {tok'} ⟷ tok'.item.phonForm)
      = fun tok' ↦ decide (Applies ({tok'} ⟷ tok'.item.phonForm) n) from rfl, hf,
    List.filter_beq, List.count_eq_one_of_mem hnd h, List.replicate_one, List.map_singleton]

theorem pf_earlySpellout {toks : List LexicalItem.Token} (hnd : toks.Nodup) :
    (earlySpellout toks).pf (toks.map ({·})) = toks.map fun tok ↦ [tok.item.phonForm] := by
  refine List.ext_getElem
    (by simp [Spellout.pf, Neighborhood.along, earlySpellout, Spellout.run]) ?_
  intro i h1 h2
  have hi : i < toks.length := by simpa using h2
  simp only [Spellout.pf, Spellout.run, earlySpellout, runModules_nil, Neighborhood.along,
    List.getElem_map, List.getElem_mapIdx]
  rw [subsetPrinciple, RuleSet.realize, RuleSet.selectBy,
    applicable_earlyItems hnd (tok := toks[i]) (List.getElem_mem _)
      (by simp [Neighborhood.around]),
    List.argmax_singleton, Option.map_some, Option.toList_some]
  rfl

theorem pfPhon_eq_earlyInsertion (t : LinearizedSyntacticObject) :
    pfPhon t = ((earlySpellout (pfYield t)).pf
      (SpelloutDomain.ofLinearized ({·}) t)).flatten.filter (· ≠ "") := by
  rw [SpelloutDomain.ofLinearized, pf_earlySpellout (nodup_pfYield t), pfPhon]
  induction pfYield t with
  | nil => rfl
  | cons tok l ih =>
    rw [List.filterMap_cons, List.map_cons, List.flatten_cons, List.singleton_append,
      List.filter_cons, LexicalItem.phonForm?]
    by_cases hf : tok.item.phonForm.isEmpty
    · rw [ite_eq_left hf, ih, ite_eq_right (by simpa [String.isEmpty_iff] using hf)]
    · rw [ite_eq_right hf, ih, ite_eq_left (by simpa [String.isEmpty_iff] using hf)]

end DistributedMorphology
