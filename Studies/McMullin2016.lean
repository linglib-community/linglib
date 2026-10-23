/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Studies.Hansson2010

/-!
# McMullin (2016): Tier-Based Locality in Long-Distance Phonotactics

This file formalizes McMullin's argument for the tier-based description of
long-distance phonotactics. A long-distance constraint can be stated over subsequences, a
forbidden pair of segments however far apart, the strictly piecewise description, or over
a tier projection, deleting transparent material and forbidding adjacent pairs, the
tier-based strictly local description; the thesis argues for the tier-based class, since
strictly piecewise grammars cannot see a blocker, an intervening segment that halts
harmony, deletion never turning a legal word illegal. Both halves are stated. Transparent
harmony, the Navajo sibilant harmony Hansson describes, is one stringset under either
description, as every agreement language is strictly piecewise of width two, agreement being
transitive; opaque harmony with a blocker is tier-based strictly local of width two but
strictly piecewise at no width, since deleting the blocker leaves an illegal word and
strictly piecewise languages are closed under subsequence.

## Implementation notes

The blocking alphabet is schematic, one blocker, one transparent segment, and the two
harmonizing series, and stands in for no particular language; the attested opaque
consonant-harmony systems surveyed by Hansson are not formalized.

## References

* [mcmullin-2016]
* [hansson-2010]
-/

@[expose] public section

namespace McMullin2016

open Subregular Hansson2010

/-! ### Transparent harmony: Navajo is SP_2 as well as TSL_2 -/

theorem navajoSibilantHarmony_lang_isSP2 :
    navajoSibilantHarmony.language.IsStrictlyPiecewise 2 := by
  rw [language_eq_preimage]
  exact (TierStrictlyLocalGrammar.agree_language_isStrictlyPiecewise _).preimage_map _

theorem navajoSibilantHarmony_language_eq_strictlyPiecewise : navajoSibilantHarmony.language =
    List.map sibilantClass ⁻¹' (StrictlyPiecewiseGrammar.agree (·.isSome)).language 2 := by
  rw [language_eq_preimage, TierStrictlyLocalGrammar.agree_language_eq_strictlyPiecewise]

theorem ur_ex6a_ii_violates_sp :
    ur Examples.ex6a_ii ∉
      List.map sibilantClass ⁻¹' (StrictlyPiecewiseGrammar.agree (·.isSome)).language 2 :=
  navajoSibilantHarmony_language_eq_strictlyPiecewise ▸ ur_ex6a_ii_violates

theorem sr_ex6a_ii_legal_sp :
    sr Examples.ex6a_ii ∈
      List.map sibilantClass ⁻¹' (StrictlyPiecewiseGrammar.agree (·.isSome)).language 2 :=
  navajoSibilantHarmony_language_eq_strictlyPiecewise ▸ sr_ex6a_ii_legal

/-! ### Opaque harmony: blocking is strictly piecewise at no width -/

/-- A schematic alphabet for an opaque long-distance pattern has the two harmonizing
series, a blocker, and transparent material. -/
inductive BSeg
  /-- Anterior member of the harmonizing series. -/
  | ant
  /-- Posterior member of the harmonizing series. -/
  | post
  /-- The blocker projects onto the tier, so it interrupts the harmony. -/
  | blocker
  /-- Transparent material is off the tier, hence invisible to the constraint. -/
  | transparent
  deriving DecidableEq

/-- Everything but the transparent segment projects. A blocker *is* a segment that the
tier keeps — that is the whole of its opacity. -/
def BSeg.onTier (s : BSeg) : Prop := s ≠ .transparent

instance : DecidablePred BSeg.onTier :=
  fun s ↦ inferInstanceAs (Decidable (s ≠ .transparent))

/-- The two series may not be tier-adjacent. -/
def BSeg.Mixed : BSeg → BSeg → Prop
  | .ant, .post => True
  | .post, .ant => True
  | _, _ => False

instance : DecidableRel BSeg.Mixed :=
  fun a b ↦ by cases a <;> cases b <;> simp only [BSeg.Mixed] <;> infer_instance

/-- The schematic blocking language has harmony across transparent material, halted by a
blocker. -/
def blockingLang : Language BSeg :=
  (TierStrictlyLocalGrammar.ofForbiddenPairs BSeg.Mixed BSeg.onTier).language

theorem blockingLang_isTSL2 : Language.IsTierStrictlyLocal 2 blockingLang :=
  ⟨_, rfl⟩

theorem transparent_not_mem : [BSeg.ant, .transparent, .post] ∉ blockingLang := by
  unfold blockingLang; decide

theorem blocked_mem : [BSeg.ant, .blocker, .post] ∈ blockingLang := by
  unfold blockingLang; decide

theorem unblocked_not_mem : [BSeg.ant, .post] ∉ blockingLang := by
  unfold blockingLang; decide

theorem blockingLang_not_isStrictlyPiecewise (k : ℕ) :
    ¬ blockingLang.IsStrictlyPiecewise k :=
  fun h ↦ unblocked_not_mem (h.isSublistClosed (by decide) blocked_mem)

theorem exists_isTierStrictlyLocal_not_isStrictlyPiecewise :
    ∃ L : Language BSeg,
      Language.IsTierStrictlyLocal 2 L ∧ ∀ k, ¬ L.IsStrictlyPiecewise k :=
  ⟨blockingLang, blockingLang_isTSL2, blockingLang_not_isStrictlyPiecewise⟩

end McMullin2016
