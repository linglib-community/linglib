module

public import Linglib.Data.Examples.Gunlogson2001
public import Linglib.Discourse.Commitment.Declarative

/-!
# Gunlogson (2001): True to Form: Rising and Falling Declaratives as Questions in English

This file formalizes chapters 3 and 4 of [gunlogson-2001], the context-update semantics of rising
and falling declaratives and the account of when a declarative can be a polar question. A context
is a pair of commitment sets, and a locution, a sentence type with its intonation (73), updates
one of them: a declarative narrows the targeted set to its content (74), an interrogative leaves
it alone (87), and the rise or fall selects the addressee's or the speaker's set (75), (76),
`Locution.update`. The statuses of a proposition in a context, commitment, joint commitment,
resolution, controversy, bias, and neutrality (63) to (68), are those of
`Discourse/Commitment/Declarative.lean`; this file adds the reduction-set characterization of
bias (69) to (71), `IsBiasedR`. Chapter 3 classifies locutions by their effect: the theorems that
no declarative is neutral and no interrogative biasing (91), (92),
`Locution.not_isNeutralIn_of_decl`, the expression of commitment (93), and entailment,
informativeness, and vacuousness (94) to (101), which separate a locution entailed by a context
from one uninformative in it. Chapter 4 defines a
polar question as a locution uninformative with respect to the addressee's commitment set (104),
(132), `Locution.IsPolarQuestion`, which for a declarative is the Contextual Bias Condition (105),
makes every rising declarative question reiterative (134) and without effect (133), and makes the
falling declarative the only resolving question (135). The dissertation's locution triples are the
rows of `Data.Examples.Gunlogson2001`.

## Implementation notes

Presuppositional admittance, (83) and (84), is not modelled, so consistency (86) is the
nonemptiness of the updated commitment sets, and the second clause of the final definition of
polar question (136), which is not a condition on commitment sets, is left out. Theorem (91) does
not hold as stated: a resolved proposition is controversial for no one under (66), so a resolved
context is neutral under (68), and a declarative whose content the addressee already holds makes
it a joint commitment and so is neutral, `Locution.isNeutralIn_fallingDecl`. The theorem holds
when the content stays unresolved, which is the form given here, and (93) correspondingly fails
for declaratives as literally defined. The reduction-set definition of bias (71), which the paper
says is equivalent to (67), agrees with it exactly on unresolved propositions,
`isBiasedR_iff_isBiased_of_not_isResolved` and `isBiasedR_of_isJoint`.

## References

* [gunlogson-2001]
-/

@[expose] public section

namespace Gunlogson2001

open Commitment Discourse

variable {W : Type*} {K : State Role W} {p : Set W}

/-! ### Contextual bias through the reduction set, section 3.1 -/

/-- (69): `K'` is reductively accessible from `K` when each commitment set shrinks to a nonempty
subset. -/
def Accessible (K K' : State Role W) : Prop :=
  (∀ x, commitmentSet K' x ⊆ commitmentSet K x) ∧ ∀ x, (commitmentSet K' x).Nonempty

/-- (71): `K` is biased toward `p` when some accessible context settles `p` and none settles
`pᶜ`. -/
def IsBiasedR (K : State Role W) (p : Set W) : Prop :=
  (∃ K', Accessible K K' ∧ ∀ x, commitmentSet K' x ⊆ p) ∧
    ¬ ∃ K', Accessible K K' ∧ ∀ x, commitmentSet K' x ⊆ pᶜ

theorem exists_accessible_iff (K : State Role W) (q : Set W) :
    (∃ K', Accessible K K' ∧ ∀ x, commitmentSet K' x ⊆ q) ↔
      ∀ x, (commitmentSet K x ∩ q).Nonempty := by
  constructor
  · rintro ⟨K', ⟨hsub, hne⟩, hq⟩ x
    obtain ⟨w, hw⟩ := hne x
    exact ⟨w, hsub x hw, hq x hw⟩
  · intro h
    have hc : ∀ x, commitmentSet (falling (rising K q) q) x = q ∩ commitmentSet K x := by
      rintro (_ | _)
      · rw [(commitmentSet_falling _ q).1, (commitmentSet_rising K q).2]
      · rw [(commitmentSet_falling _ q).2, (commitmentSet_rising K q).1]
    refine ⟨falling (rising K q) q, ⟨λ x => ?_, λ x => ?_⟩, λ x => ?_⟩ <;> rw [hc]
    · exact Set.inter_subset_right
    · rw [Set.inter_comm]; exact h x
    · exact Set.inter_subset_left

theorem isBiasedR_iff :
    IsBiasedR K p ↔ (∀ x, (commitmentSet K x ∩ p).Nonempty) ∧ ∃ x, commitmentSet K x ⊆ p := by
  simp only [IsBiasedR, exists_accessible_iff, not_forall, Set.inter_compl_nonempty_iff, not_not]

/-- (67) and (71) agree on unresolved propositions. -/
theorem isBiasedR_iff_isBiased_of_not_isResolved (hu : ¬ IsResolved K p) :
    IsBiasedR K p ↔ IsBiased K p := by
  rw [isBiasedR_iff]
  constructor
  · rintro ⟨hmeet, x, hx⟩
    have hne : ∀ x, (commitmentSet K x).Nonempty := λ x => (hmeet x).mono Set.inter_subset_left
    refine ⟨⟨⟨x, hne x, by simpa using hx⟩, by simpa using hu, hne⟩, ?_⟩
    rintro ⟨⟨y, -, hy⟩, -, -⟩
    obtain ⟨w, hw, hwp⟩ := hmeet y
    exact hy hw hwp
  · rintro ⟨⟨⟨x, -, hx⟩, -, hne⟩, hnc⟩
    refine ⟨λ y => ?_, x, by simpa using hx⟩
    by_contra hy
    exact hnc ⟨⟨y, hne y, λ w hw hwp => hy ⟨w, hw, hwp⟩⟩, hu, hne⟩

/-- (71) holds of a context in which `p` is a joint commitment, where (67) fails, since a resolved
context is neutral under (68): the two definitions of bias part at resolved propositions. -/
theorem isBiasedR_of_isJoint (h : IsJoint K p) : IsBiasedR K p :=
  isBiasedR_iff.2 ⟨λ x => (h x).1.mono (Set.subset_inter subset_rfl (h x).2), .speaker,
    (h .speaker).2⟩

theorem not_isBiased_of_isJoint (h : IsJoint K p) : ¬ IsBiased K p :=
  (IsResolved.isNeutral (Or.inl h)).not_isBiased

/-! ### Locutions and their context change potentials, sections 3.2 and 3.3 -/

/-- (73d): the sentence types. -/
inductive SentenceType
  | decl
  | interr
  deriving DecidableEq

/-- (74) and (87): a declarative with content `p` narrows a commitment set to `p`; an
interrogative leaves it alone. -/
def SentenceType.update (p : Set W) : SentenceType → Set W → Set W
  | .decl, cs => p ∩ cs
  | .interr, cs => cs

/-- (95): a commitment set entails a sentence when updating with it has no effect. -/
def SentenceType.Entails (S : SentenceType) (cs p : Set W) : Prop := S.update p cs = cs

theorem SentenceType.entails_decl_iff {cs : Set W} : SentenceType.decl.Entails cs p ↔ cs ⊆ p :=
  Set.inter_eq_right

theorem SentenceType.entails_interr {cs : Set W} : SentenceType.interr.Entails cs p := rfl

/-- (73e): the locutions, a sentence type with a rise or a fall. -/
inductive Locution
  | risingDecl
  | fallingDecl
  | risingInterr
  deriving DecidableEq

namespace Locution

/-- The sentence type of a locution. -/
def sentenceType : Locution → SentenceType
  | .risingInterr => .interr
  | _ => .decl

/-- (75) and (76): the commitment set the intonation targets, the addressee's under a rise and
the speaker's under a fall. -/
def target : Locution → Role
  | .fallingDecl => .speaker
  | _ => .addressee

/-- (77), (78), and (88): the context change potential of a locution with descriptive content
`p`. -/
def update (p : Set W) : Locution → State Role W → State Role W
  | .risingDecl, K => rising K p
  | .fallingDecl, K => falling K p
  | .risingInterr, K => K

variable (L : Locution)

/-- (81): the locution applies its sentence meaning to the targeted commitment set. -/
theorem commitmentSet_update_target :
    commitmentSet (L.update p K) L.target =
      L.sentenceType.update p (commitmentSet K L.target) := by
  cases L
  · exact (commitmentSet_rising K p).1
  · exact (commitmentSet_falling K p).1
  · rfl

/-- (81): the other commitment set is unchanged. -/
theorem commitmentSet_update_of_ne {x : Role} (h : x ≠ L.target) :
    commitmentSet (L.update p K) x = commitmentSet K x := by
  cases L <;> cases x <;>
    first
    | exact absurd rfl h
    | exact (commitmentSet_rising K p).2
    | exact (commitmentSet_falling K p).2
    | rfl

/-- (86): `L` with content `p` is consistent with `K` when every updated commitment set is
nonempty. -/
def Consistent (K : State Role W) (p : Set W) : Prop :=
  ∀ x, (commitmentSet (L.update p K) x).Nonempty

/-! ### Locutionary bias and neutrality, section 3.4 -/

/-- (89): `L` is neutral with respect to `K` when the updated context is neutral. -/
def IsNeutralIn (K : State Role W) (p : Set W) : Prop := IsNeutral (L.update p K) p

/-- (90): `L` is biasing with respect to `K` when it takes a neutral context to a biased one. -/
def IsBiasingIn (K : State Role W) (p : Set W) : Prop :=
  IsNeutral K p ∧ IsBiased (L.update p K) p

/-- (91): no declarative is neutral with respect to a context it is consistent with, provided its
content stays unresolved: the targeted participant is committed to the content afterwards, so its
negation is controversial. -/
theorem not_isNeutralIn_of_decl (hL : L.sentenceType = .decl) (hc : L.Consistent K p)
    (hu : ¬ IsResolved (L.update p K) p) : ¬ L.IsNeutralIn K p := λ hn =>
  hn.2 ⟨⟨L.target, hc _, by rw [commitmentSet_update_target, hL]; simp [SentenceType.update]⟩,
    by simpa using hu, hc⟩

/-- The proviso cannot be dropped: a falling declarative whose content the addressee already
holds makes it a joint commitment, and a resolved context is neutral under (68). -/
theorem isNeutralIn_fallingDecl (ha : IsCommitmentOf K .addressee p)
    (hs : (p ∩ commitmentSet K .speaker).Nonempty) : fallingDecl.IsNeutralIn K p := by
  show IsNeutral (falling K p) p
  refine IsResolved.isNeutral (Or.inl ?_)
  rintro (_ | _)
  · rw [IsCommitmentOf, (commitmentSet_falling K p).1]
    exact ⟨hs, Set.inter_subset_left⟩
  · rw [IsCommitmentOf, (commitmentSet_falling K p).2]
    exact ha

theorem isBiasingIn_of_decl (hL : L.sentenceType = .decl) (h : IsNeutral K p)
    (hu : ¬ IsResolved K p) (hne : ∀ x, (commitmentSet K x).Nonempty) : L.IsBiasingIn K p := by
  refine ⟨h, ?_⟩
  cases L
  · exact isBiased_rising h hu hne
  · exact isBiased_falling h hu hne
  · exact absurd hL (by decide)

/-- (92): no interrogative is biasing: it leaves the context as it is, and a neutral context is
not biased. -/
theorem not_isBiasingIn_risingInterr : ¬ risingInterr.IsBiasingIn K p :=
  λ h => h.1.not_isBiased h.2

/-- (93): `L` expresses commitment to `p` when no context consistent with it comes out
neutral. -/
def ExpressesCommitment (p : Set W) : Prop :=
  ∀ K : State Role W, L.Consistent K p → ¬ L.IsNeutralIn K p

theorem not_expressesCommitment_risingInterr (h₀ : p.Nonempty) (h₁ : pᶜ.Nonempty) :
    ¬ risingInterr.ExpressesCommitment p := by
  intro h
  obtain ⟨w₀, hw₀⟩ := h₀
  obtain ⟨w₁, hw₁⟩ := h₁
  refine h ∅ (λ x => ⟨w₀, by simp [update]⟩) ⟨λ hc => ?_, λ hc => ?_⟩
  · obtain ⟨x, -, hx⟩ := hc.1
    exact hx (by simp [update] : w₀ ∈ commitmentSet (risingInterr.update p ∅) x) hw₀
  · obtain ⟨x, -, hx⟩ := hc.1
    exact hx (by simp [update] : w₁ ∈ commitmentSet (risingInterr.update p ∅) x) hw₁

/-- Nor, as literally defined, does a falling declarative, (93) inheriting the gap in (91): a
context in which only the addressee holds `p` is consistent with it and comes out neutral. -/
theorem not_expressesCommitment_fallingDecl (h₀ : p.Nonempty) :
    ¬ fallingDecl.ExpressesCommitment p := by
  intro h
  have hs : commitmentSet (rising ∅ p) .speaker = Set.univ := by
    rw [(commitmentSet_rising ∅ p).2, commitmentSet_empty]
  have ha : commitmentSet (rising ∅ p) .addressee = p := by
    rw [(commitmentSet_rising ∅ p).1, commitmentSet_empty, Set.inter_univ]
  refine h (rising ∅ p) (λ x => ?_) (isNeutralIn_fallingDecl ⟨?_, ?_⟩ ?_)
  · rcases x with _ | _
    · show (commitmentSet (falling (rising ∅ p) p) .speaker).Nonempty
      rw [(commitmentSet_falling _ p).1, hs, Set.inter_univ]; exact h₀
    · show (commitmentSet (falling (rising ∅ p) p) .addressee).Nonempty
      rw [(commitmentSet_falling _ p).2, ha]; exact h₀
  · rw [ha]; exact h₀
  · simp [ha]
  · rw [hs, Set.inter_univ]; exact h₀

/-! ### Entailment, informativeness, and vacuousness, section 3.5 -/

/-- (94): a context entails a locution when the update leaves every commitment set as it was. -/
def Entails (K : State Role W) (p : Set W) : Prop :=
  ∀ x, commitmentSet (L.update p K) x = commitmentSet K x

theorem entails_iff : L.Entails K p ↔ L.sentenceType.Entails (commitmentSet K L.target) p := by
  constructor
  · intro h
    rw [SentenceType.Entails, ← commitmentSet_update_target]
    exact h _
  · intro h x
    by_cases hx : x = L.target
    · subst hx
      rw [commitmentSet_update_target]
      exact h
    · exact commitmentSet_update_of_ne L hx

/-- (97): `L` is uninformative with respect to `x`'s commitment set when the set entails its
sentence. -/
def Uninformative (K : State Role W) (x : Role) (p : Set W) : Prop :=
  L.sentenceType.Entails (commitmentSet K x) p

/-- (99): uninformative with respect to every commitment set. -/
def UninformativeIn (K : State Role W) (p : Set W) : Prop := ∀ x, L.Uninformative K x p

/-- (98): informative with respect to some commitment set. -/
def InformativeIn (K : State Role W) (p : Set W) : Prop := ∃ x, ¬ L.Uninformative K x p

theorem uninformative_risingInterr (x : Role) : risingInterr.Uninformative K x p := rfl

theorem uninformative_iff_of_decl (hL : L.sentenceType = .decl) {x : Role} :
    L.Uninformative K x p ↔ commitmentSet K x ⊆ p := by
  rw [Uninformative, hL]
  exact SentenceType.entails_decl_iff

/-- (100): a falling declarative reiterating the speaker's commitment is entailed by the context
yet informative with respect to the addressee. -/
theorem entails_and_informativeIn_fallingDecl (hs : commitmentSet K .speaker ⊆ p)
    (ha : ¬ commitmentSet K .addressee ⊆ p) :
    fallingDecl.Entails K p ∧ fallingDecl.InformativeIn K p :=
  ⟨(entails_iff _).2 (SentenceType.entails_decl_iff.2 hs), .addressee,
    λ h => ha ((uninformative_iff_of_decl _ rfl).1 h)⟩

theorem uninformative_of_isCommitmentOf {x : Role} (h : IsCommitmentOf K x p) :
    L.Uninformative K x p := by
  cases hL : L.sentenceType
  · exact (uninformative_iff_of_decl L hL).2 h.2
  · rw [Uninformative, hL]
    rfl

/-- (101): a locution whose content is a joint commitment is vacuous; it is then uninformative
with respect to the context and entailed by it. -/
theorem uninformativeIn_and_entails_of_isJoint (h : IsJoint K p) :
    L.UninformativeIn K p ∧ L.Entails K p :=
  ⟨λ x => L.uninformative_of_isCommitmentOf (h x),
    (entails_iff L).2 (L.uninformative_of_isCommitmentOf (h _))⟩

/-! ### Polar questions, chapter 4 -/

/-- (132), the Uninformativeness Condition (104) taken as necessary and sufficient: an utterance
of `L` is a polar question in `K` when `L` is uninformative with respect to the addressee's
commitment set. -/
def IsPolarQuestion (K : State Role W) (p : Set W) : Prop := L.Uninformative K .addressee p

/-- (131): every rising interrogative is a polar question. -/
theorem isPolarQuestion_risingInterr : risingInterr.IsPolarQuestion K p := rfl

/-- (105), the Contextual Bias Condition: a declarative is a polar question only where the
addressee is already committed to its content. -/
theorem isPolarQuestion_iff_of_decl (hL : L.sentenceType = .decl) :
    L.IsPolarQuestion K p ↔ commitmentSet K .addressee ⊆ p :=
  uninformative_iff_of_decl L hL

/-- (133): a rising declarative that is a polar question has the effect of the interrogative
with the same content, none. -/
theorem entails_of_isPolarQuestion_risingDecl (h : risingDecl.IsPolarQuestion K p) :
    risingDecl.Entails K p :=
  (entails_iff _).2 h

/-- (134): a reiterative question, a polar question whose content the addressee is committed
to. -/
def IsReiterativeQuestion (K : State Role W) (p : Set W) : Prop :=
  L.IsPolarQuestion K p ∧ IsCommitmentOf K .addressee p

theorem isReiterativeQuestion_risingDecl (hne : (commitmentSet K .addressee).Nonempty)
    (h : risingDecl.IsPolarQuestion K p) : risingDecl.IsReiterativeQuestion K p :=
  ⟨h, hne, (isPolarQuestion_iff_of_decl _ rfl).1 h⟩

/-- (135): a resolving question, a reiterative question that takes its unresolved content to a
joint commitment. -/
def IsResolvingQuestion (K : State Role W) (p : Set W) : Prop :=
  L.IsReiterativeQuestion K p ∧ ¬ IsResolved K p ∧ IsJoint (L.update p K) p

theorem eq_fallingDecl_of_isResolvingQuestion (h : L.IsResolvingQuestion K p) :
    L = .fallingDecl := by
  by_contra hL
  obtain ⟨⟨-, ha⟩, hu, hj⟩ := h
  refine hu (Or.inl ?_)
  rintro (_ | _)
  · have hs := hj .speaker
    rw [IsCommitmentOf, commitmentSet_update_of_ne L (by cases L <;> simp_all [target])] at hs
    exact hs
  · exact ha

theorem isJoint_of_entails_of_isPolarQuestion_fallingDecl
    (hne : ∀ x, (commitmentSet K x).Nonempty) (he : fallingDecl.Entails K p)
    (hq : fallingDecl.IsPolarQuestion K p) : IsJoint K p := by
  rintro (_ | _)
  · exact ⟨hne _, SentenceType.entails_decl_iff.1 ((entails_iff _).1 he)⟩
  · exact ⟨hne _, (isPolarQuestion_iff_of_decl _ rfl).1 hq⟩

end Locution

end Gunlogson2001
