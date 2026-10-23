module

public import Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Order.BooleanAlgebra.Set

/-!
# Neo-Gricean pragmatics: secondary implicatures and the Standard Recipe

This file defines [sauerland-2004]'s derivation of secondary implicatures and the Standard
Recipe of [geurts-2010]. A speaker's epistemic state is a set of worlds `s : Set W` (the same
object as the `ContextSet` of `Discourse/CommonGround.lean`), and an *epistemic proposition* —
what an utterance implicates about the speaker — is a set of states `Set (Set W)`. Knowledge
`Kφ` is the principal down-set `Set.Iic φ` (the states `s ⊆ φ`), so the primary implicature
`¬Kψ` is `(Iic ψ)ᶜ`, the secondary implicature `K¬ψ` is `Iic ψᶜ`, competence `Kψ ∨ K¬ψ` is
`Iic ψ ∪ Iic ψᶜ`, and the empty state, a member of every `Iic`, is the inconsistent speaker.
Asserting `φ` against alternatives `alts` commits the speaker to `Kφ` and the primary
implicatures; `K¬ψ` is a secondary implicature iff it is consistent with that commitment.

## Main definitions

* `primaryImplicature`, `secondaryImplicature`, `competent`: the epistemic propositions
  `¬Kψ`, `K¬ψ`, `Kψ ∨ K¬ψ`.
* `commitment`: `Kφ` together with the primary implicatures of the alternatives.
* `Consistent`: an epistemic proposition holds of some nonempty state.
* `IsSecondaryImplicature`: [sauerland-2004]'s condition for `K¬ψ`.

## Main results

* `isSecondaryImplicature_iff`: `K¬ψ` is a secondary implicature iff the strengthened meaning
  `φ \ ψ` is consistent and entails no alternative — `φ \ ψ` itself is the canonical witness,
  so a blocked secondary implicature is always blocked by a single primary; the disjunction
  case (K¬(A∧B) arises, K¬A is blocked) is `Studies/Sauerland2004.lean`.
* `isSecondaryImplicature_of_ssubset`: a lone asymmetrically stronger alternative always yields
  its secondary implicature.
* `primaryImplicature_inter_competent`: the Standard Recipe as an identity — on consistent
  states, the weak implicature plus competence is the strong implicature.

## References

* [sauerland-2004] — primary vs secondary implicatures and the consistency condition
* [geurts-2010] — the Standard Recipe; textbook presentation
* [soames-1982], [horn-1989] — the epistemic modalization `¬Kψ`
* [vanrooij-schulz-2004], [spector-2006] — the competence step `Kψ ∨ K¬ψ`
-/

@[expose] public section

namespace NeoGricean

open Set

variable {W : Type*} {s φ ψ χ : Set W} {alts : Set (Set W)}

/-! ### Epistemic propositions -/

/-- The primary implicature `¬Kψ`: the states that do not know `ψ`. -/
def primaryImplicature (ψ : Set W) : Set (Set W) := (Iic ψ)ᶜ

/-- The secondary implicature `K¬ψ`: the states that know `¬ψ`. -/
def secondaryImplicature (ψ : Set W) : Set (Set W) := Iic ψᶜ

/-- Competence about `ψ`, `Kψ ∨ K¬ψ`: the states that know whether `ψ`. -/
def competent (ψ : Set W) : Set (Set W) := Iic ψ ∪ Iic ψᶜ

@[simp] theorem mem_primaryImplicature : s ∈ primaryImplicature ψ ↔ ¬ s ⊆ ψ := Iff.rfl

@[simp] theorem mem_secondaryImplicature : s ∈ secondaryImplicature ψ ↔ s ⊆ ψᶜ := Iff.rfl

@[simp] theorem mem_competent : s ∈ competent ψ ↔ s ⊆ ψ ∨ s ⊆ ψᶜ := Iff.rfl

/-- An epistemic proposition is consistent iff some nonempty state satisfies it. -/
def Consistent (E : Set (Set W)) : Prop := ∃ s ∈ E, s.Nonempty

/-! ### Primary and secondary implicatures

Asserting `φ` against scalar alternatives `alts` commits the speaker to `Kφ` plus the primary
implicature `¬Kψ` for each alternative ([sauerland-2004] (42), verified p. 383); `K¬ψ` is a
secondary implicature exactly when it is *consistent* with that commitment
([sauerland-2004] (43)). -/

/-- The speaker's commitment after asserting `φ` against `alts`: `Kφ` and the primary
implicature of each alternative. Per [sauerland-2004] the alternatives are the asymmetrically
stronger ones (`ψ ⊂ φ`); the definition does not enforce the filter. -/
def commitment (φ : Set W) (alts : Set (Set W)) : Set (Set W) :=
  Iic φ ∩ ⋂ χ ∈ alts, primaryImplicature χ

@[simp] theorem mem_commitment : s ∈ commitment φ alts ↔ s ⊆ φ ∧ ∀ χ ∈ alts, ¬ s ⊆ χ := by
  simp [commitment]

/-- `K¬ψ` is a secondary implicature of asserting `φ` against `alts` iff it is consistent with
the commitment. -/
def IsSecondaryImplicature (φ : Set W) (alts : Set (Set W)) (ψ : Set W) : Prop :=
  Consistent (commitment φ alts ∩ secondaryImplicature ψ)

/-- The strengthened meaning `φ \ ψ` is the canonical witness: `K¬ψ` is a secondary
implicature iff `φ \ ψ` is consistent and entails no alternative. A blocked secondary
implicature is thus always blocked by a single primary. -/
theorem isSecondaryImplicature_iff :
    IsSecondaryImplicature φ alts ψ ↔ (φ \ ψ).Nonempty ∧ ∀ χ ∈ alts, ¬ φ \ ψ ⊆ χ := by
  constructor
  · rintro ⟨s, ⟨hcom, hψ⟩, hs⟩
    obtain ⟨hφ, hprim⟩ := mem_commitment.1 hcom
    have hsub : s ⊆ φ \ ψ := fun w hw => ⟨hφ hw, hψ hw⟩
    exact ⟨hs.mono hsub, fun χ hχ h => hprim χ hχ (hsub.trans h)⟩
  · rintro ⟨hne, h⟩
    exact ⟨φ \ ψ, ⟨mem_commitment.2 ⟨sdiff_subset, h⟩, fun _ hw => hw.2⟩, hne⟩

theorem isSecondaryImplicature_singleton :
    IsSecondaryImplicature φ {χ} ψ ↔ (φ \ ψ).Nonempty ∧ ¬ φ \ ψ ⊆ χ := by
  simp [isSecondaryImplicature_iff]

theorem isSecondaryImplicature_singleton_self :
    IsSecondaryImplicature φ {ψ} ψ ↔ (φ \ ψ).Nonempty := by
  rw [isSecondaryImplicature_singleton]
  exact and_iff_left_of_imp fun ⟨_, hw⟩ h => hw.2 (h hw)

/-- A lone asymmetrically stronger alternative always yields its secondary implicature: the
*some ⇝ not all* case. -/
theorem isSecondaryImplicature_of_ssubset (h : ψ ⊂ φ) : IsSecondaryImplicature φ {ψ} ψ :=
  isSecondaryImplicature_singleton_self.2 (sdiff_nonempty.2 h.2)

/-! ### Competence and the Standard Recipe

Competence about `ψ` is [sauerland-2004]'s `Kψ ∨ K¬ψ` — the speaker *knows whether* `ψ`, which
is support of the polar question `Question.polar ψ` by `Question.mem_polar`. -/

theorem not_subset_compl_of_subset (hs : s.Nonempty) (h : s ⊆ ψ) : ¬ s ⊆ ψᶜ :=
  fun h' => hs.elim fun _ hw => h' hw (h hw)

theorem subset_compl_iff_not_subset (hs : s.Nonempty) (hc : s ⊆ ψ ∨ s ⊆ ψᶜ) :
    s ⊆ ψᶜ ↔ ¬ s ⊆ ψ :=
  ⟨fun h h' => not_subset_compl_of_subset hs h' h, hc.resolve_left⟩

/-- The Standard Recipe: on consistent states, the weak implicature plus competence is the
strong implicature. -/
theorem primaryImplicature_inter_competent (ψ : Set W) :
    primaryImplicature ψ ∩ competent ψ = secondaryImplicature ψ \ {∅} := by
  ext s
  simp only [mem_inter_iff, mem_primaryImplicature, mem_competent, mem_sdiff,
    mem_secondaryImplicature, mem_singleton_iff]
  constructor
  · rintro ⟨h, hc⟩
    exact ⟨hc.resolve_left h, fun he => h (he ▸ empty_subset ψ)⟩
  · rintro ⟨hψ, hs⟩
    exact ⟨fun h => not_subset_compl_of_subset (nonempty_iff_ne_empty.2 hs) h hψ, Or.inr hψ⟩

end NeoGricean
