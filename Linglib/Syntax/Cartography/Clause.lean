/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Order.OrdConnected
public import Linglib.Syntax.Spine.Label
public import Mathlib.Order.Interval.Set.LinearOrder
public import Mathlib.Tactic.DeriveFintype

/-!
# The hierarchy of clausal functional heads

This file defines the clausal functional heads of Cinque's universal hierarchy and their order.
Cinque matches the order of adverb classes against the order of the functional heads that
morphology and scope reveal, and pairs each adverb class with one head, as its specifier. The heads
are listed from the lower completive aspect at the bottom to the speech-act mood at the top, each
with its adverb class. A head is below another if it is merged lower.

The hierarchy is the spine that contains every head. The heads below a head on that spine are the
heads lower in the order, so the clause truncated at a head contains exactly those. The kinds of
head that the labels name, mood, modality, tense, aspect and Voice, are not intervals of the
hierarchy: the anterior tense and the volitional modality lie among the aspects.

## Main definitions

* `Cartography.Head`: the heads of the hierarchy, with their linear order.
* `Cartography.Family`, `Cartography.Head.family`: the kind of a head.
* `Cartography.Head.hierarchy`: the spine of all the heads.

## Main results

* `Cartography.Head.mem_below_hierarchy_iff`: the heads below a head on the hierarchy are the heads
  lower in the order.
* `Cartography.Head.not_isContiguous_family`: the kinds of head are not intervals of the hierarchy.

## Implementation notes

* The order is Cinque's second approximation of the hierarchy. His first approximation has a root
  modal head among the lowest aspects. The second keeps the volitional modal as its only root
  head, below habitual and the higher repetitive and frequentative aspects, and orders volition
  above obligation and ability or permission without placing those two among the heads; they are
  not heads here.
* Cinque marks the pairing of *characteristically* with generic or progressive aspect, and the
  head of *always*, as uncertain.

## References

* [cinque-1999]
-/

@[expose] public section

namespace Cartography

/-- A head of the universal hierarchy of clausal functional projections, bottom-up, each with the
adverb class in its specifier. -/
inductive Head
  /-- *completely*, the lower singular completive aspect. -/
  | aspSgCompletiveII
  /-- *often*, the lower frequentative aspect. -/
  | aspFrequentativeII
  /-- *again*, the lower repetitive aspect. -/
  | aspRepetitiveII
  /-- *fast*, *early*, the lower celerative aspect. -/
  | aspCelerativeII
  /-- *well*, Voice. -/
  | voice
  /-- *tutto*, plural completive aspect. -/
  | aspPlCompletive
  /-- *completely*, the higher singular completive aspect. -/
  | aspSgCompletiveI
  /-- *almost*, prospective aspect. -/
  | aspProspective
  /-- *characteristically*, generic or progressive aspect. -/
  | aspGenericProgressive
  /-- *briefly*, durative aspect. -/
  | aspDurative
  /-- *soon*, proximative aspect. -/
  | aspProximative
  /-- *just*, retrospective aspect. -/
  | aspRetrospective
  /-- *always*, perfect aspect. -/
  | aspPerfect
  /-- *still*, continuative aspect. -/
  | aspContinuative
  /-- *no longer*, terminative aspect. -/
  | aspTerminative
  /-- *already*, anterior tense. -/
  | tAnterior
  /-- *quickly*, the higher celerative aspect. -/
  | aspCelerativeI
  /-- *intentionally*, volitional modality. -/
  | modVolitional
  /-- *often*, the higher frequentative aspect. -/
  | aspFrequentativeI
  /-- *again*, the higher repetitive aspect. -/
  | aspRepetitiveI
  /-- *usually*, habitual aspect. -/
  | aspHabitual
  /-- *possibly*, alethic possibility. -/
  | modPossibility
  /-- *necessarily*, alethic necessity. -/
  | modNecessity
  /-- *perhaps*, irrealis mood. -/
  | moodIrrealis
  /-- *then*, future tense. -/
  | tFuture
  /-- *once*, past tense. -/
  | tPast
  /-- *probably*, epistemic modality. -/
  | modEpistemic
  /-- *allegedly*, evidential mood. -/
  | moodEvidential
  /-- *fortunately*, evaluative mood. -/
  | moodEvaluative
  /-- *frankly*, speech-act mood. -/
  | moodSpeechAct
  deriving DecidableEq, Fintype, Repr

/-- The kinds of clausal functional head that Cinque's labels name. -/
inductive Family
  | mood
  | modality
  | tense
  | aspect
  | voice
  deriving DecidableEq, Fintype, Repr

namespace Head

/-- A head is below another when it is merged lower. -/
instance : LinearOrder Head := LinearOrder.lift' Head.ctorIdx (by decide)

/-- The kind of head. -/
def family : Head → Family
  | voice => .voice
  | tAnterior | tFuture | tPast => .tense
  | modVolitional | modPossibility | modNecessity | modEpistemic => .modality
  | moodIrrealis | moodEvidential | moodEvaluative | moodSpeechAct => .mood
  | _ => .aspect

/-- The **hierarchy** is the spine of all the heads, from the lowest to the highest. -/
def hierarchy : Spine Head := ⟨(List.range 30).map Head.ofNat⟩

theorem mem_hierarchy (h : Head) : h ∈ hierarchy := by cases h <;> decide

theorem pairwise_hierarchy : hierarchy.heads.Pairwise (· < ·) := by decide

/-- The heads below a head on the hierarchy are the heads lower in the order. -/
theorem mem_below_hierarchy_iff {c h : Head} : c ∈ hierarchy.below h ↔ c < h :=
  ⟨Spine.rel_of_mem_below pairwise_hierarchy (mem_hierarchy h), fun hc ↦
    (Spine.mem_below_or_rel (r := (· ≤ ·)) (pairwise_hierarchy.imp le_of_lt) (mem_hierarchy h)
      (mem_hierarchy c)).resolve_right hc.not_ge⟩

/-- No order on the kinds of head is coarsened by the hierarchy
(`isContiguous_iff_exists_monotone`): the anterior tense and the volitional modality sit among the
aspects. -/
theorem not_isContiguous_family : ¬ IsContiguous family := by
  unfold IsContiguous
  decide

end Head

end Cartography
