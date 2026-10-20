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

/-- **Navajo sibilant harmony is strictly 2-piecewise.** The subject is the very language
`Studies/Hansson2010.lean` builds as TSL_2, the inverse image of agreement among the sibilant
classes, and agreement is strictly 2-piecewise. -/
theorem navajoSibilantHarmony_lang_isSP2 :
    navajoSibilantHarmony.language.IsStrictlyPiecewise 2 := by
  rw [language_eq_preimage]
  exact (TierStrictlyLocalGrammar.agree_language_isStrictlyPiecewise _).preimage_map _

/-- The tier-based and subsequence-based grammars for Navajo generate the same language, read
through the sibilant classes. -/
theorem navajoSibilantHarmony_language_eq_strictlyPiecewise : navajoSibilantHarmony.language =
    List.map sibilantClass ⁻¹' (StrictlyPiecewiseGrammar.agree (·.isSome)).language 2 := by
  rw [language_eq_preimage, TierStrictlyLocalGrammar.agree_language_eq_strictlyPiecewise]

/-- Under the SP_2 description Hansson's minimal pair comes out as before, the pre-harmony
/si-dʒéːʔ/ rejected and the surface [ʃidʒéːʔ] accepted. Both transfer along the equality of
languages rather than being recomputed. -/
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

/-- Transparent material does not license a mixed pair, since the projection deletes it and
leaves the two series tier-adjacent. -/
theorem transparent_not_mem : [BSeg.ant, .transparent, .post] ∉ blockingLang := by
  unfold blockingLang; decide

/-- A blocker does license it, since the blocker projects and the two series are no longer
tier-adjacent. -/
theorem blocked_mem : [BSeg.ant, .blocker, .post] ∈ blockingLang := by
  unfold blockingLang; decide

/-- Deleting the blocker leaves an illegal word — the configuration no subsequence
grammar can distinguish. -/
theorem unblocked_not_mem : [BSeg.ant, .post] ∉ blockingLang := by
  unfold blockingLang; decide

/-- **Blocking is not strictly piecewise, at any width** ([mcmullin-2016]). SP
languages are subsequence-closed, so a legal word whose blocker-deletion is illegal
rules out every SP grammar at once. -/
theorem blockingLang_not_isStrictlyPiecewise (k : ℕ) :
    ¬ blockingLang.IsStrictlyPiecewise k :=
  fun h ↦ unblocked_not_mem (h.mem_of_sublist (by decide) blocked_mem)

/-- **The tier buys expressive power** ([mcmullin-2016]). Some TSL_2 language is
strictly piecewise at no width. With `navajoSibilantHarmony_lang_isSP2` — where the two
descriptions do coincide — this is the thesis's typological argument in miniature, that SP
suffices for transparency, and only for transparency. -/
theorem exists_isTierStrictlyLocal_not_isStrictlyPiecewise :
    ∃ L : Language BSeg,
      Language.IsTierStrictlyLocal 2 L ∧ ∀ k, ¬ L.IsStrictlyPiecewise k :=
  ⟨blockingLang, blockingLang_isTSL2, blockingLang_not_isStrictlyPiecewise⟩

end McMullin2016
