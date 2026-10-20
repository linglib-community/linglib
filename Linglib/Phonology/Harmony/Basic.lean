/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.List.Chain
public import Linglib.Phonology.Subregular.ForbiddenPairs

/-!
# Vowel harmony: pattern-level vocabulary

The theory-neutral vocabulary of vowel harmony, anchored on
[ritter-vanderhulst-2024-themes]: the typological enums and `Pattern`, the
descriptive object mechanisms derive. At a finite alphabet a pattern presents
a TSL₂ grammar (`Pattern.harmonic_iff_mem_tsl`). Segment-level participation
cannot express parasitic harmony ((8b)) or configuration-dependent blocking, as
in Yakut, whose rounding is no pattern beside its fronting harmony
(`AksenovaEtAl2024.yakut_rounding_not_pattern`); those need the general
forbidden-pairs machinery.

## Main definitions

* `Participation`, `Direction`, `ControlType`, `Domain`, `HarmonyType`: the
  typological enums.
* `Pattern`: valuation, participation, descriptors; `Pattern.Harmonic` is the
  surface semantics — tier-adjacent compatibility with blocker imposition and
  icy absorption.
* `Pattern.project`: the tier value of a segment, nothing off the tier.

## Main results

* `Pattern.harmonic_insert_transparent`: transparency interrupts harmlessly.
* `Pattern.harmonic_iff_agreeOn`: with all segments participating, the chain
  and pairwise formulations coincide.
* `Pattern.harmonic_iff_mem_tsl`: surface harmonicity is membership in a TSL₂
  language.
* `Pattern.harmonic_iff_map_project_mem`: when every tier segment participates, a word is
  harmonic exactly when its tier projection is in the agreement language.

## References

* [ritter-vanderhulst-2024-themes]
* [aksenova-rawski-graf-heinz-2024]
* [jurgec-2011]
-/

@[expose] public section

namespace Phonology.Harmony

universe u v

variable {α : Type u} {V : Type v}

/-- How a segment participates in harmony ([ritter-vanderhulst-2024-themes] §1.3). -/
inductive Participation where
  /-- Alternates and propagates. -/
  | participating
  /-- Skipped harmlessly (neutral). -/
  | transparent
  /-- Does not undergo; imposes its value on what follows ((8c)). -/
  | opaque
  /-- Undergoes without passing on ([jurgec-2011]'s absorbing vowels). -/
  | icyTarget
  deriving DecidableEq, Repr

/-- Direction of the agreement relation ([ritter-vanderhulst-2024-themes] §1.2.3). -/
inductive Direction where
  | rightward
  | leftward
  /-- The prototype, outward from the root with no stipulated direction. -/
  | bidirectional
  deriving DecidableEq, Repr

/-- Who determines the harmonic value ([ritter-vanderhulst-2024-themes] §1.2.4). -/
inductive ControlType (V : Type u) where
  /-- Roots do not alternate; affixes harmonize to them (morphologically determined). -/
  | rootControlled
  /-- A designated value wins regardless of position (phonologically determined). -/
  | dominantRecessive (dominant : V)
  /-- Metaphony and umlaut, where stress attracts the harmonic value, which the chapter
      poses as an open question. -/
  | affixControlled
  deriving DecidableEq, Repr

/-- The domain delimiting harmony ([ritter-vanderhulst-2024-themes] §1.2.2). -/
inductive Domain where
  | root
  | stem
  /-- Bounded bisyllabic agreement, of the stem-final vowel and first suffix vowel only. -/
  | stemAndFirstAffix
  | word
  /-- As in metaphony and umlaut. -/
  | foot
  /-- Post-lexical harmony. -/
  | phrase
  deriving DecidableEq, Repr

/-- The feature types of [ritter-vanderhulst-2024-themes] §1.5; tonal harmony
    is unattested. -/
inductive HarmonyType where
  | palatal
  | labial
  | height
  /-- [ATR] (`Phonology.Feature.atr`); the [ATR]/[RTR] alternative is privative. -/
  | tongueRoot
  | tenseLax
  | nasal
  /-- Post-velar harmony. -/
  | emphasis
  | retroflex
  /-- Echo or copy harmony, in all features. -/
  | total
  deriving DecidableEq, Repr

/-! ### Patterns and their surface semantics

The descriptive object every mechanism must derive: harmony creates likeness
among the participating vowels of a domain ((2) of
[ritter-vanderhulst-2024-themes]). The undergoer/blocker/transparent
decomposition follows [aksenova-rawski-graf-heinz-2024]: transparent segments
are skipped; opaque blockers do not undergo but impose their transmitted value
on what follows ((8c)); icy targets undergo without passing on
([jurgec-2011]). -/

/-- A harmony pattern over segment type `α` with harmonic values in `V`. -/
structure Pattern (α : Type u) (V : Type v) where
  /-- The valuation, with `none` for a segment without a harmonic counterpart. For opaque
      and icy segments it is the value transmitted, not necessarily the phonetic one. -/
  value         : α → Option V
  /-- Participation is stored independently of the valuation, since neutral vowels'
      transparent-vs-opaque behavior is not predictable (§1.3.2). A segment without a value
      does not participate, so `value s = none → participation s ≠ .participating`. -/
  participation : α → Participation
  direction     : Direction := .bidirectional
  domain        : Domain := .word
  control       : ControlType V := .rootControlled

/-- Pairwise agreement in harmonic value. -/
def Pattern.AgreeOn (p : Pattern α V) (w : List α) : Prop :=
  w.Pairwise fun a b => p.value a = p.value b

/-- A segment is on the tier unless it is transparent. -/
def Pattern.OnTier (p : Pattern α V) (s : α) : Prop :=
  p.participation s ≠ .transparent

instance (p : Pattern α V) : DecidablePred p.OnTier := fun s => by
  unfold Pattern.OnTier; infer_instance

/-- The harmonic tier of a string. -/
def Pattern.tier (p : Pattern α V) (w : List α) : List α :=
  w.filter fun s => decide (p.OnTier s)

@[simp] theorem Pattern.tier_nil (p : Pattern α V) : p.tier [] = [] := rfl

theorem Pattern.tier_cons_of_onTier (p : Pattern α V) {x : α} (h : p.OnTier x) (w : List α) :
    p.tier (x :: w) = x :: p.tier w :=
  List.filter_cons_of_pos (decide_eq_true h)

theorem Pattern.tier_cons_of_not_onTier (p : Pattern α V) {x : α} (h : ¬ p.OnTier x)
    (w : List α) : p.tier (x :: w) = p.tier w :=
  List.filter_cons_of_neg (decide_eq_true_iff.not.mpr h)

/-- Adjacent compatibility, read left to right. An opaque right member is exempt, since
    blockers do not undergo, and so is an icy left member, which does not pass its value on;
    otherwise the values agree. The relation is deliberately asymmetric. -/
def Pattern.Compatible (p : Pattern α V) (a b : α) : Prop :=
  p.participation a = .icyTarget ∨ p.participation b = .opaque ∨
    p.value a = p.value b

instance [DecidableEq V] (p : Pattern α V) : DecidableRel p.Compatible :=
  fun a b => by unfold Pattern.Compatible; infer_instance

/-- A word is surface-harmonic when its tier is a chain of compatible segments. -/
def Pattern.Harmonic (p : Pattern α V) (w : List α) : Prop :=
  (p.tier w).IsChain p.Compatible

instance [DecidableEq V] (p : Pattern α V) (w : List α) :
    Decidable (p.Harmonic w) := by
  unfold Pattern.Harmonic; infer_instance

/-- Transparency interrupts harmlessly ([ritter-vanderhulst-2024-themes] §1.3.2). -/
theorem Pattern.harmonic_insert_transparent {p : Pattern α V} {t : α}
    (w₁ w₂ : List α) (ht : p.participation t = .transparent) :
    p.Harmonic (w₁ ++ t :: w₂) ↔ p.Harmonic (w₁ ++ w₂) := by
  unfold Pattern.Harmonic Pattern.tier
  simp [List.filter_append, Pattern.OnTier, ht]

/-- With all segments participating, the chain and pairwise formulations
    coincide (value-agreement is transitive). -/
theorem Pattern.harmonic_iff_agreeOn {p : Pattern α V} {w : List α}
    (h : ∀ s ∈ w, p.participation s = .participating) :
    p.Harmonic w ↔ p.AgreeOn (p.tier w) := by
  have hmem : ∀ s ∈ p.tier w, p.participation s = .participating :=
    fun s hs => h s (List.mem_of_mem_filter hs)
  have : Trans (fun a b => p.value a = p.value b)
      (fun a b => p.value a = p.value b) (fun a b => p.value a = p.value b) :=
    ⟨fun h₁ h₂ => h₁.trans h₂⟩
  unfold Pattern.Harmonic Pattern.AgreeOn
  rw [← List.isChain_iff_pairwise]
  suffices key : ∀ l : List α, (∀ s ∈ l, p.participation s = .participating) →
      (l.IsChain p.Compatible ↔ l.IsChain fun a b => p.value a = p.value b) from
    key _ hmem
  intro l hl
  induction l with
  | nil => exact iff_of_true .nil .nil
  | cons a l ih =>
    cases l with
    | nil => exact iff_of_true (.singleton _) (.singleton _)
    | cons b l =>
      have ha := hl a (by simp)
      have hb := hl b (by simp)
      simp only [List.isChain_cons_cons, Pattern.Compatible, ha, hb,
        reduceCtorEq, false_or,
        ih fun s hs => hl s (List.mem_cons_of_mem a hs)]

open Subregular TierStrictlyLocalGrammar in
/-- Harmony is TSL₂ by construction, since the tier supplies both the unbounded distance
strictly local grammars lack and the blocking strictly piecewise grammars lack
([aksenova-rawski-graf-heinz-2024]; for the latter,
`McMullin2016.blockingLang_not_isStrictlyPiecewise`). -/
theorem Pattern.harmonic_iff_mem_tsl (p : Pattern α V) (w : List α) :
    p.Harmonic w ↔ w ∈ (ofForbiddenPairs (¬ p.Compatible · ·) p.OnTier).language := by
  simp only [mem_ofForbiddenPairs_language_iff, Pattern.Harmonic, Pattern.tier,
    not_not]

/-- The tier value of a segment is its harmonic value on the tier and nothing off it. -/
def Pattern.project (p : Pattern α V) (s : α) : Option V :=
  if p.OnTier s then p.value s else none

open Subregular TierStrictlyLocalGrammar in
/-- When every segment on the tier participates with a value, the harmonic words are the inverse
image, under the tier projection, of agreement among the values. -/
theorem Pattern.harmonic_iff_map_project_mem [DecidableEq V] (p : Pattern α V)
    (hp : ∀ s, p.OnTier s → p.participation s = .participating ∧ (p.value s).isSome)
    (w : List α) :
    p.Harmonic w ↔ w.map p.project ∈ (ofForbiddenPairs (· ≠ ·) (·.isSome)).language := by
  have hproj : ∀ s, p.OnTier s → p.project s = p.value s := fun s hs ↦ ite_eq_left hs
  rw [harmonic_iff_mem_tsl, map_mem_ofForbiddenPairs_language_iff]
  refine Eq.to_iff (congrArg (w ∈ ·) (ofForbiddenPairs_language_congr (fun s ↦ ?_)
    fun s t hs ht ↦ ?_))
  · by_cases hs : p.OnTier s
    · simp [hproj s hs, (hp s hs).2, hs]
    · simp [Pattern.project, hs]
  · simp [Pattern.Compatible, (hp s hs).1, (hp t ht).1, hproj s hs, hproj t ht]

end Phonology.Harmony
