module

public import Linglib.Semantics.Homogeneity.Defs
public import Linglib.Semantics.Questions.Partition.Basic

/-!
# Pragmatic usability of trivalent propositions

Križ evaluates a trivalent proposition `W → SignType` relative to an issue, a partition
`Setoid W` of the worlds. A proposition is `sufficientlyTrue` at a world when the world's cell
contains a world where it is true, `addressesIssue` when no cell contains both a true and a false
world, and `usable` at a world when it is not false there, is sufficiently true there, and
addresses the issue. Non-maximal readings are usability at gap-worlds (`gap_enables_nonmax`), gap
removal blocks them (`metaAssert_prevents_nonmax`), and tolerated exceptions cannot be mentioned
(`exception_unaddressable`). Strong relevance, after Križ and Spector, is the bivalent counterpart
of addressing, holding when the issue decides the proposition (`Setoid.Decides`).

## Main definitions

* `sufficientlyTrue`, `addressesIssue`, `usable`: Križ's weakened Quality.
* `communicatedContent`: worlds compatible with what is communicated.
* `isStronglyRelevantProp`: constancy on issue cells.
* `bivalentPred`: `Bool`-valued truth predicate of a bivalent proposition.

## References

* [kriz-2016]
* [kriz-spector-2021]
-/

@[expose] public section

namespace Homogeneity

variable {W : Type*}

/-- `p` is true enough at `w` relative to the issue `q` when some `q`-equivalent world makes
`p` literally true. This weakens the maxim of Quality, so that a speaker need only assert
something equivalent, for current purposes, to something true. -/
def sufficientlyTrue (q : Setoid W) (p : W → SignType) (w : W) : Prop :=
  ∃ w', q w w' ∧ p w' = 1

instance sufficientlyTrue.instDecidable [Fintype W] (q : Setoid W) [DecidableRel q]
    (p : W → SignType) (w : W) : Decidable (sufficientlyTrue q p w) :=
  inferInstanceAs (Decidable (∃ w', q w w' ∧ p w' = 1))

theorem literal_imp_sufficient (q : Setoid W) (p : W → SignType) (w : W)
    (h : p w = 1) : sufficientlyTrue q p w :=
  ⟨w, q.refl' w, h⟩

/-- `p` addresses issue `q` when no cell of `q` overlaps both the positive and the negative
extension. Gap-worlds do not count, since only cells straddling the true/false boundary
disqualify. -/
def addressesIssue (q : Setoid W) (p : W → SignType) : Prop :=
  ¬∃ w₁ w₂, q w₁ w₂ ∧ p w₁ = 1 ∧ p w₂ = -1

instance addressesIssue.instDecidable [Fintype W] (q : Setoid W) [DecidableRel q]
    (p : W → SignType) : Decidable (addressesIssue q p) :=
  inferInstanceAs (Decidable (¬∃ w₁ w₂, q w₁ w₂ ∧ p w₁ = 1 ∧ p w₂ = -1))

/-- `p` may be used at `w` when it is not false at `w`, sufficiently true at `w`, and addresses
the issue. -/
def usable (q : Setoid W) (p : W → SignType) (w : W) : Prop :=
  p w ≠ -1 ∧ sufficientlyTrue q p w ∧ addressesIssue q p

instance usable.instDecidable [Fintype W] (q : Setoid W) [DecidableRel q] (p : W → SignType)
    (w : W) : Decidable (usable q p w) :=
  inferInstanceAs
    (Decidable (p w ≠ -1 ∧ sufficientlyTrue q p w ∧ addressesIssue q p))

theorem usable_iff_of_isBivalent {p : W → SignType} (hbiv : Trivalent.IsBivalent p)
    (q : Setoid W) (w : W) :
    usable q p w ↔ p w = 1 ∧ addressesIssue q p := by
  constructor
  · intro ⟨hNotFalse, _, hAddr⟩
    exact ⟨(hbiv w).resolve_right (absurd · hNotFalse), hAddr⟩
  · intro ⟨hTrue, hAddr⟩
    exact ⟨by simp [hTrue], literal_imp_sufficient q p w hTrue, hAddr⟩

/-! ### Usability at gap-worlds -/

theorem gap_enables_nonmax (q : Setoid W) (p : W → SignType) (w w' : W)
    (hGap : p w = 0) (hEquiv : q w w') (hTrue : p w' = 1)
    (hAddr : addressesIssue q p) :
    usable q p w :=
  ⟨by simp [hGap], ⟨w', hEquiv, hTrue⟩, hAddr⟩

theorem metaAssert_prevents_nonmax (q : Setoid W) (p : W → SignType) (w : W)
    (h : usable q ((fun v ↦ SignType.ofProp (v = 1)) ∘ p) w) : SignType.ofProp (p w = 1) = 1 :=
  ((usable_iff_of_isBivalent (Trivalent.isBivalent_ofProp_eq_one p) q w).mp h).1

/-- When `p` is used at `w` under the issue `q`, a sentence mentioning an exception cannot address
`q` ([kriz-2016] §4.1). -/
theorem exception_unaddressable (q : Setoid W) (p e : W → SignType) (w : W)
    (hUse : usable q p w) (hEw : e w = 1)
    (hEfalse : ∀ w', p w' = 1 → e w' = -1) :
    ¬ addressesIssue q e := by
  obtain ⟨-, ⟨w', hEq, hTrue⟩, -⟩ := hUse
  exact fun hAddr ↦ hAddr ⟨w, w', hEq, hEw, hEfalse w' hTrue⟩

/-! ### Communicated content -/

/-- The worlds the hearer considers possible after hearing `p` under issue `q` are those
indistinguishable, for current purposes, from a world where `p` is literally true. -/
def communicatedContent (q : Setoid W) (p : W → SignType) : Set W :=
  {w | sufficientlyTrue q p w}

@[simp] theorem mem_communicatedContent {q : Setoid W} {p : W → SignType} {w : W} :
    w ∈ communicatedContent q p ↔ sufficientlyTrue q p w :=
  Iff.rfl

instance communicatedContent.instDecidableMem [Fintype W] (q : Setoid W) [DecidableRel q]
    (p : W → SignType) (w : W) : Decidable (w ∈ communicatedContent q p) :=
  inferInstanceAs (Decidable (sufficientlyTrue q p w))

theorem posExt_subset_communicated (q : Setoid W) (p : W → SignType) :
    Trivalent.posExt p ⊆ communicatedContent q p :=
  fun _ hw ↦ literal_imp_sufficient q p _ hw

theorem communicatedContent_eq_posExt {p : W → SignType} (hbiv : Trivalent.IsBivalent p)
    (q : Setoid W) (hAddr : addressesIssue q p) :
    communicatedContent q p = Trivalent.posExt p := by
  ext w
  constructor
  · intro ⟨w', hEq, hTrue⟩
    cases hbiv w with
    | inl h => exact h
    | inr hFalse =>
      exact absurd ⟨w', w, q.symm' hEq, hTrue, hFalse⟩ hAddr
  · exact literal_imp_sufficient q p w

theorem communicatedContent_antitone {q q' : Setoid W} (p : W → SignType) (hRef : q' ≤ q) :
    communicatedContent q' p ⊆ communicatedContent q p :=
  fun _ ⟨w', hEq, hTrue⟩ ↦ ⟨w', Setoid.le_def.1 hRef hEq, hTrue⟩

/-! ### Strong relevance

Bivalent counterpart of `addressesIssue`, from [kriz-spector-2021]: a `W → Prop` is *strongly
relevant* to an issue when it is constant on each cell, that is, when the issue decides it;
Addressing has it as its special case on bivalent propositions
(`KrizSpector2021.addressesIssue_iff_stronglyRelevant`). -/

/-- A proposition is strongly relevant to an issue iff the issue decides it. -/
abbrev isStronglyRelevantProp (q : Setoid W) (p : W → Prop) : Prop := q.Decides {w | p w}

/-- Filter a set of propositions to those strongly relevant to `q`. -/
def stronglyRelevantSet (q : Setoid W) (candidates : Set (W → Prop)) : Set (W → Prop) :=
  { p ∈ candidates | isStronglyRelevantProp q p }

theorem trivial_relevant_iff_constant (p : W → Prop) :
    isStronglyRelevantProp ⊤ p ↔ ∀ w₁ w₂ : W, p w₁ ↔ p w₂ :=
  Setoid.top_decides_iff

theorem exact_all_relevant (p : W → Prop) : isStronglyRelevantProp ⊥ p := Setoid.bot_decides

theorem exact_stronglyRelevantSet_eq (candidates : Set (W → Prop)) :
    stronglyRelevantSet ⊥ candidates = candidates :=
  Set.sep_eq_self_iff_mem_true.2 fun p _ ↦ exact_all_relevant p

/-- The `Bool` truth predicate of a proposition. Bridges the trivalent Addressing constraint
to bivalent strong-relevance filtering ([kriz-spector-2021]). -/
def bivalentPred (p : W → SignType) : W → Bool :=
  fun w ↦ p w == 1

end Homogeneity
