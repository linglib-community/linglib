module

public import Linglib.Discourse.Commitment.Basic
public import Linglib.Discourse.Role

/-!
# Rising and falling declaratives

[gunlogson-2001] represents a two-party context as the pair of the participants' commitment
sets, the worlds compatible with each one's public beliefs (60), and reads a declarative's
intonation as choosing whose commitment set its content updates: falling for the speaker's,
rising for the addressee's (77), (78). Which participant is committed to what defines the
statuses of a proposition — a commitment of a participant, a joint commitment, resolved,
controversial — and the bias of a context toward it (63)–(68). [gunlogson-2008] refines the
addressee's commitment under a rising declarative as attributed by the speaker rather than
self-generated, the `Commitment.Source` coordinate.

## Main definitions

* `Commitment.commitmentSet` — `cs_X` (60).
* `Commitment.falling`, `Commitment.rising` — (78), (77).
* `Commitment.IsCommitmentOf`, `IsJoint`, `IsResolved`, `IsControversial`, `IsBiased`,
  `IsNeutral` — (63)–(68).

## Main results

* `Commitment.commitmentSet_falling`, `Commitment.commitmentSet_rising` — each intonation
  narrows exactly one commitment set.
* `Commitment.isBiased_falling`, `Commitment.isBiased_rising` — a declarative in a neutral,
  unresolved context biases it toward its content.
* `Commitment.IsResolved.isNeutral` — a resolved context is neutral under (68), since (66) makes
  a resolved proposition controversial for no one.

## References

* [C. Gunlogson, *True to Form: Rising and Falling Declaratives as Questions in English*
  (2001)][gunlogson-2001]
* [C. Gunlogson, *A Question of Commitment* (2008)][gunlogson-2008]
-/

@[expose] public section

namespace Commitment


variable {W : Type*} (K : State Discourse.Role W) (x : Discourse.Role) (p : Set W)

/-- `cs_X` (60): the worlds compatible with `x`'s public commitments. -/
def commitmentSet : Set W := contextSet (ofCommitter K x)

/-- A falling declarative (78): the speaker commits to `p`. -/
def falling : State Discourse.Role W := insert (commit .speaker p) K

/-- A rising declarative (77): the addressee is committed to `p`, attributed by the speaker. -/
def rising : State Discourse.Role W :=
  insert (commit .addressee p .doxastic .otherGenerated) K

/-- (63): `p` is a commitment of `x`. -/
def IsCommitmentOf : Prop := (commitmentSet K x).Nonempty ∧ commitmentSet K x ⊆ p

/-- (64): `p` is a joint commitment. -/
def IsJoint : Prop := ∀ x, IsCommitmentOf K x p

/-- (65): `p` is resolved. -/
def IsResolved : Prop := IsJoint K p ∨ IsJoint K pᶜ

/-- (66): `p` is controversial — someone is committed against it, it is unresolved, and no
commitment set is empty. -/
def IsControversial : Prop :=
  (∃ x, IsCommitmentOf K x pᶜ) ∧ ¬ IsResolved K p ∧ ∀ x, (commitmentSet K x).Nonempty

/-- (67): the context is biased toward `p`. -/
def IsBiased : Prop := IsControversial K pᶜ ∧ ¬ IsControversial K p

/-- (68): the context is neutral with respect to `p`. -/
def IsNeutral : Prop := ¬ IsControversial K p ∧ ¬ IsControversial K pᶜ

@[simp] theorem commitmentSet_empty :
    commitmentSet (∅ : State Discourse.Role W) x = Set.univ := by
  simp [commitmentSet, ofCommitter]

/-- A falling declarative narrows the speaker's commitment set by its content and leaves the
addressee's alone. -/
theorem commitmentSet_falling :
    commitmentSet (falling K p) .speaker = p ∩ commitmentSet K .speaker ∧
      commitmentSet (falling K p) .addressee = commitmentSet K .addressee := by
  refine ⟨?_, ?_⟩
  · rw [commitmentSet, falling, ofCommitter_insert_of_eq K .speaker _ rfl,
      contextSet_insert_of_commit rfl]
    rfl
  · rw [commitmentSet, falling, ofCommitter_insert_of_ne K .addressee _ (by simp)]
    rfl

/-- A rising declarative narrows the addressee's commitment set by its content and leaves the
speaker's alone. -/
theorem commitmentSet_rising :
    commitmentSet (rising K p) .addressee = p ∩ commitmentSet K .addressee ∧
      commitmentSet (rising K p) .speaker = commitmentSet K .speaker := by
  refine ⟨?_, ?_⟩
  · rw [commitmentSet, rising, ofCommitter_insert_of_eq K .addressee _ rfl,
      contextSet_insert_of_commit rfl]
    rfl
  · rw [commitmentSet, rising, ofCommitter_insert_of_ne K .speaker _ (by simp)]
    rfl

/-! ### Statuses -/

variable {K p}

@[simp] theorem isResolved_compl : IsResolved K pᶜ ↔ IsResolved K p := by
  simp [IsResolved, or_comm]

/-- A resolved proposition is controversial for no one, so a resolved context is neutral. -/
theorem IsResolved.isNeutral (h : IsResolved K p) : IsNeutral K p :=
  ⟨λ hc => hc.2.1 h, λ hc => hc.2.1 (isResolved_compl.2 h)⟩

theorem IsNeutral.not_isBiased (h : IsNeutral K p) : ¬ IsBiased K p := λ hb => h.2 hb.1

theorem IsNeutral.not_subset (h : IsNeutral K p) (hu : ¬ IsResolved K p)
    (hne : ∀ x, (commitmentSet K x).Nonempty) (x : Discourse.Role) :
    ¬ commitmentSet K x ⊆ p ∧ ¬ commitmentSet K x ⊆ pᶜ :=
  ⟨λ hx => h.2 ⟨⟨x, hne x, by simpa using hx⟩, by simpa using hu, hne⟩,
    λ hx => h.1 ⟨⟨x, hne x, hx⟩, hu, hne⟩⟩

theorem isBiased_of_commitmentSet_eq {K' : State Discourse.Role W} {y : Discourse.Role}
    (h : IsNeutral K p) (hu : ¬ IsResolved K p) (hne : ∀ x, (commitmentSet K x).Nonempty)
    (hy : commitmentSet K' y = p ∩ commitmentSet K y)
    (hx : commitmentSet K' y.other = commitmentSet K y.other) : IsBiased K' p := by
  have hyp : (commitmentSet K' y).Nonempty := by
    obtain ⟨w, hw, hwp⟩ := Set.not_subset.1 (h.not_subset hu hne y).2
    exact ⟨w, by rw [hy]; exact ⟨by simpa using hwp, hw⟩⟩
  have hne' : ∀ x, (commitmentSet K' x).Nonempty :=
    (Discourse.Role.forall_role' y).2 ⟨hyp, hx ▸ hne _⟩
  have hsub : commitmentSet K' y ⊆ p := hy ▸ Set.inter_subset_left
  have hnot : ∀ x, ¬ commitmentSet K' x ⊆ pᶜ :=
    (Discourse.Role.forall_role' y).2 ⟨λ hxp => hyp.elim λ _ hw => hxp hw (hsub hw),
      λ hxp => (h.not_subset hu hne _).2 (hx ▸ hxp)⟩
  refine ⟨⟨⟨y, hyp, by simpa using hsub⟩, ?_, hne'⟩, λ hc => hc.1.elim λ x hx' => hnot x hx'.2⟩
  rw [isResolved_compl]
  rintro (hj | hj)
  · exact (h.not_subset hu hne y.other).1 (hx ▸ (hj y.other).2)
  · exact hnot y (hj y).2

/-- A falling declarative in a neutral, unresolved, nonempty context biases it toward its
content. -/
theorem isBiased_falling (h : IsNeutral K p) (hu : ¬ IsResolved K p)
    (hne : ∀ x, (commitmentSet K x).Nonempty) : IsBiased (falling K p) p :=
  isBiased_of_commitmentSet_eq h hu hne (commitmentSet_falling K p).1
    (commitmentSet_falling K p).2

/-- A rising declarative in a neutral, unresolved, nonempty context biases it toward its
content. -/
theorem isBiased_rising (h : IsNeutral K p) (hu : ¬ IsResolved K p)
    (hne : ∀ x, (commitmentSet K x).Nonempty) : IsBiased (rising K p) p :=
  isBiased_of_commitmentSet_eq h hu hne (commitmentSet_rising K p).1
    (commitmentSet_rising K p).2

end Commitment
