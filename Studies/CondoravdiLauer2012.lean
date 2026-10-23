module

public import Linglib.Semantics.Attitudes.Preference.Structure
public import Linglib.Semantics.Modality.Necessity
public import Linglib.Discourse.Commitment.Sincerity
public import Linglib.Data.Examples.CondoravdiLauer2012

/-!
# Condoravdi and Lauer 2012: imperatives as preferential commitments

Condoravdi and Lauer give declaratives and imperatives one kind of conventional effect, a
public commitment of the speaker, differing in the attitude committed to: a declarative commits
the speaker to act as though believing its content, an imperative to act as though the content
were a maximal element of the speaker's effective preference structure, the consistent ranking
of propositions that guides action. The range of uses, from commands to wishes, permissions
and disinterested advice, comes from the context, while the constraints on every use come from
the commitment: successive imperatives are consistent because the maximal elements of a
consistent structure are jointly realizable, the speaker cannot be insincere because the
commitment is self-verifying, and a preference against the content survives a concession but
not disinterested advice, since the addressee's goal enters the adviser's structure at the
bottom by cooperation by default. The paper's formal points against ordering-source
affirmation and, in its discussion of To-Do Lists, against a secondary update of the ordering
source are checked as well.

## Implementation notes

The information state of a preference structure is its world type, so the paper's consistency
is `PreferenceStructure.Consistent Set.univ`; the theorems take an information state `B`, since
the paper's incompatibility is relative to what the speaker believes. A public effective
preference is a commitment keyed by the participant and `.preferential`; the doxastic reduction of a commitment to
one's own preferential commitment, which the paper takes over from the authors' earlier work, is
a hypothesis on the world-indexed commitment state. Disinterested advice identifies the content
with the adopted goal, which the paper reaches through a means-end inference, and quantifies
over the effective structure alone where cooperation by default ranges over all of the
adviser's structures.

## TODO

* Informal in the paper and not formalized: the two preconditions and the re-ranking of a
  permission, the second meaning component (36) that limits speaker involvement and excludes
  promises, the two conditions on wish uses behind (37), the conditional preferences of offers
  (41), and the practical reasoning step by which the preliminary semantics (32) is recovered
  from the final (34).

## References

* [C. Condoravdi and S. Lauer, *Imperatives: Meaning and illocutionary force*
  (2012)][condoravdi-lauer-2012]
* [C. Condoravdi and S. Lauer, *Performative verbs and performative acts*
  (2011)][condoravdi-lauer-2011]
* [S. Schmerling, *How imperatives are special, and how they aren't* (1982)][schmerling-1982]
* [M. Schwager, *Interpreting Imperatives* (2006)][schwager-2006]
* [S. Kaufmann and M. Schwager, *A unified analysis of conditional imperatives*
  (2009)][kaufmann-schwager-2009]
* [M. Kaufmann, *Interpreting Imperatives* (2012)][kaufmann-2012]
* [P. Portner, *Imperatives and modals* (2007)][portner-2007]
-/

@[expose] public section

namespace CondoravdiLauer2012

open Commitment Desire.Preferential Modality

variable {A W : Type*} {P : A → W → PreferenceStructure W} {a : A} {p q : Set W} {w : W}

/-! ### Effective preferences and public commitments

`Want P a p w` is the effective preference `EP_w(a, p)`: `p` is a maximal element of `a`'s
effective preference structure `P a w`, the distinguished consistent structure that determines
`a`'s action choices, (28) and (29). The public commitments of §3.2 are keyed by participant and
attitude. A commitment of `(a, .doxastic)` to `p` is `PB(a, p)`, to act as though believing `p`,
and one of `(a, .preferential)` is `PEP(a, p)`, to act as though `p` were a maximal effective
preference; a speaker commits to an effective preference only when holding it, condition (iii) of
§3.4, `Commitment.Sincere`. -/

/-! ### The conventions -/

/-- A declarative under the convention (30) narrows the speaker's doxastic commitment set by its
content and leaves the preferential one unchanged. -/
theorem declarative_commitmentSets (a : A) (p : Set W) (K : State (A × Force) W) :
    (insert ((a, .doxastic), p) K).commitmentSet (a, .doxastic) =
        p ∩ K.commitmentSet (a, .doxastic) ∧
      (insert ((a, .doxastic), p) K).commitmentSet (a, .preferential) =
        K.commitmentSet (a, .preferential) :=
  ⟨State.commitmentSet_insert_self, State.commitmentSet_insert_of_ne (by simp)⟩

/-- An imperative under the convention (47) narrows the speaker's preferential commitment set by
its content and leaves the doxastic one unchanged (10). -/
theorem imperative_commitmentSets (a : A) (p : Set W) (K : State (A × Force) W) :
    (insert ((a, .preferential), p) K).commitmentSet (a, .preferential) =
        p ∩ K.commitmentSet (a, .preferential) ∧
      (insert ((a, .preferential), p) K).commitmentSet (a, .doxastic) =
        K.commitmentSet (a, .doxastic) :=
  ⟨State.commitmentSet_insert_self, State.commitmentSet_insert_of_ne (by simp)⟩

/-! ### Self-verification -/

/-- The denotation (34) of `IMP(p)` over a world-indexed commitment state is the set of worlds at
which the speaker is publicly committed to an effective preference for `p`. -/
def imp (K : W → State (A × Force) W) (a : A) (p : Set W) : Set W :=
  {w | ((a, .preferential), p) ∈ K w}

/-- Doxastic reduction for preference commitment, after [condoravdi-lauer-2011], identifies a
doxastic commitment to one's own preferential commitment with that preferential commitment. -/
def DoxasticReduction (K : W → State (A × Force) W) : Prop :=
  ∀ w a p, ((a, .doxastic), {v | ((a, .preferential), p) ∈ K v}) ∈ K w →
    ((a, .preferential), p) ∈ K w

/-- The doxastic commitment to `IMP(p)` that (30) assigns an imperative holds at the world of
utterance, so it resists the challenges (23) to (25) (§3.3; cf. (47), §6). -/
theorem imp_self_verifying {K : W → State (A × Force) W} (hK : DoxasticReduction K)
    (h : ((a, .doxastic), imp K a p) ∈ K w) : w ∈ imp K a p :=
  hK w a p h

/-! ### Directive uses -/

/-- In a directive context, a sincere preferential commitment to `p` under (34) is an effective
preference satisfied only if the addressee effectively prefers `p` (§3.4; cf. (32)). -/
theorem directive_want_addressee {K : State (A × Force) W} {ad : A}
    (hs : Sincere (effectivePreference P) K w) (hp : ((a, .preferential), p) ∈ K)
    (hii : p ⊆ {v | Want P ad p v}) :
    WantNecessary P a {v | Want P ad p v} w :=
  (hs.want hp).wantNecessary.mono hii

/-! ### Consistency -/

/-- The preferential commitments of a sincere speaker with consistent effective preferences are
jointly realizable in the information state: successive imperatives are consistent, §2.1. -/
theorem imperatives_consistent {K : State (A × Force) W} {B : Set W} (hC : (P a w).Consistent B)
    (hs : Sincere (effectivePreference P) K w) :
    (B ∩ K.commitmentSet (a, .preferential)).Nonempty :=
  hC.inter_sInter_maxElts_nonempty.mono
    (Set.inter_subset_inter_right _ (Set.sInter_subset_sInter fun _ hp ↦ hs.want hp))

/-- Two imperatives with incompatible contents are not both sincere at one time, (11) and (15):
the second revises the speaker's effective preferences, (12) to (14). -/
theorem imperatives_revise {K : State (A × Force) W} {B : Set W} (hC : (P a w).Consistent B)
    (hp : ((a, .preferential), p) ∈ K) (hq : ((a, .preferential), q) ∈ K)
    (h : B ∩ (p ∩ q) = ∅) : ¬ Sincere (effectivePreference P) K w :=
  fun hs ↦ (hC.inter_inter_nonempty_of_mem_maxElts (hs.want hp) (hs.want hq)).ne_empty h

/-! ### Endorsement: advice, permission, concession -/

/-- In disinterested advice ((39), (40)), an effective goal adopted by cooperation is consistent
with every preference of the agent. -/
theorem advice_compatible {S : PreferenceStructure W} {B g : Set W} (hC : S.Consistent B)
    (hb : ∀ r ∈ S.prefs, ¬ S.prec r g) (hg : g ∈ S.maxElts) (hq : q ∈ S.prefs) :
    (B ∩ (g ∩ q)).Nonempty :=
  Set.nonempty_iff_ne_empty.2 fun h ↦ hb q hq (hC.prec_of_mem_maxElts hg hq h)

/-- In a concession ((21), (22)), a preference conflicting with an effective one is not itself
effective, so it survives only as a wish. -/
theorem concession_not_want {S : PreferenceStructure W} {B : Set W} (hC : S.Consistent B)
    (hp : p ∈ S.maxElts) (hq : q ∈ S.prefs) (h : B ∩ (p ∩ q) = ∅) : q ∉ S.maxElts :=
  fun hq' ↦ hq'.2 p hp.1 (hC.prec_of_mem_maxElts hp hq h)

/-- The utterances whose follow-ups the paper contrasts. -/
inductive Use
  | assertion | directive | advice | concession
  deriving DecidableEq

/-- An utterance requires of the speaker's effective preference structure an effective
preference for the content unless it is an assertion, which incurs no preferential commitment,
`declarative_commitmentSets`, and for advice also nothing ranked below the content, (39). -/
def Use.Holds (u : Use) (S : PreferenceStructure W) (p : Set W) : Prop :=
  (u ≠ .assertion → p ∈ S.maxElts) ∧ (u = .advice → ∀ r ∈ S.prefs, ¬ S.prec r p)

/-- A follow-up's present preference against the content is effective for *I don't want you
to*, mere for *I wish you would not*, and absent for a deontic statement or a past desire. -/
inductive Denial
  | want | wish | none
  deriving DecidableEq

/-- A denial carries a preference against the content unless it has none, and an effective one
for a want. -/
def Denial.Against (d : Denial) (S : PreferenceStructure W) (q : Set W) : Prop :=
  (d ≠ .none → q ∈ S.prefs) ∧ (d = .want → q ∈ S.maxElts)

variable (W) in
/-- A follow-up is coherent when some consistent effective preference structure meets the
utterance's requirement on the content and carries the denial's preference against it. -/
def Coherent (u : Use) (d : Denial) : Prop :=
  ∃ (S : PreferenceStructure W) (p q : Set W),
    S.Consistent Set.univ ∧ u.Holds S p ∧ p ∩ q = ∅ ∧ d.Against S q

/-- A follow-up is coherent unless it denies an effective preference the utterance incurred,
`concession_not_want`, or denies the content of disinterested advice at all,
`advice_compatible`. A directive followed by a wish against its content is thereby predicted
coherent, a case the paper does not discuss. -/
theorem coherent_iff [Nontrivial W] {u : Use} {d : Denial} :
    Coherent W u d ↔ d = .none ∨ u = .assertion ∨ d ≠ .want ∧ u ≠ .advice := by
  obtain ⟨x, y, hxy⟩ := exists_pair_ne W
  have hne : ({x} : Set W) ≠ {y} := fun h ↦ hxy (Set.singleton_eq_singleton_iff.1 h)
  have hxy' : ({x} : Set W) ∩ {y} = ∅ :=
    Set.singleton_inter_eq_empty.2 fun h ↦ hxy (Set.mem_singleton_iff.1 h)
  constructor
  · rintro ⟨S, p, q, hC, ⟨hp, hb⟩, hpq, hq, hqm⟩
    by_cases hd : d = .none
    · exact Or.inl hd
    by_cases ha : u = .assertion
    · exact Or.inr (Or.inl ha)
    have hpq' : Set.univ ∩ (p ∩ q) = ∅ := by rw [Set.univ_inter]; exact hpq
    exact Or.inr (Or.inr ⟨fun hw ↦ concession_not_want hC (hp ha) (hq hd) hpq' (hqm hw),
      fun hu ↦ (advice_compatible hC (hb hu) (hp ha) (hq hd)).ne_empty hpq'⟩)
  · rintro (rfl | rfl | ⟨hw, hu⟩)
    · exact ⟨PreferenceStructure.single {x}, {x}, {y},
        PreferenceStructure.consistent_single ⟨x, Set.mem_singleton x, Set.mem_univ x⟩,
        ⟨fun _ ↦ ⟨Set.mem_singleton _, fun _ _ h ↦ h⟩, fun _ _ _ h ↦ h⟩, hxy', fun h ↦ absurd rfl h,
        nofun⟩
    · exact ⟨PreferenceStructure.single {y}, {x}, {y},
        PreferenceStructure.consistent_single ⟨y, Set.mem_singleton y, Set.mem_univ y⟩,
        ⟨fun h ↦ absurd rfl h, nofun⟩, hxy', fun _ ↦ Set.mem_singleton _,
        fun _ ↦ ⟨Set.mem_singleton _, fun _ _ h ↦ h⟩⟩
    · exact ⟨.rankBelow {{x}, {y}} hne.symm, {x}, {y},
        PreferenceStructure.consistent_rankBelow hne.symm
          ⟨x, trivial, fun _ ⟨ht, hty⟩ ↦ (ht.resolve_right hty).symm ▸ rfl⟩
          ⟨y, trivial, fun _ ⟨ht, htx⟩ ↦ (ht.resolve_left htx).symm ▸ rfl⟩,
        ⟨fun _ ↦ ⟨Or.inl rfl, fun _ _ h ↦ hne h.1⟩, fun h ↦ absurd h hu⟩,
        hxy', fun _ ↦ Or.inr rfl, fun h ↦ absurd h hw⟩

/-! ### Ordering-source affirmation -/

/-- [schwager-2006]'s ordering-source affirmation, (19), read as a bouletic necessity of the
content, predicts the consistency requirement: two affirmed contents share a best world. -/
theorem affirmation_consistent {f g : Background W}
    (hne : (bestWorlds f g w).Nonempty) (hp : necessity f g (· ∈ p) w)
    (hq : necessity f g (· ∈ q) w) : (p ∩ q).Nonempty :=
  let ⟨u, hu⟩ := hne; ⟨u, hp u hu, hq u hu⟩

/-- The weaker affirmation (20) of [kaufmann-schwager-2009] affirms both a content and its negation
whenever the best worlds leave it open, admitting the imperatives of (15). -/
theorem weak_affirmation_compl {f g : Background W}
    (hp : ∃ u ∈ bestWorlds f g w, u ∈ p) (hq : ∃ u ∈ bestWorlds f g w, u ∉ p) :
    possibility f g (· ∈ p) w ∧ possibility f g (· ∈ pᶜ) w :=
  ⟨hp, hq⟩

/-! ### To-Do Lists -/

/-- Under [portner-2007]'s secondary update, the common ground need not entail *must p* when the
ordering source already holds a proposition incompatible with `p` (§5.2). -/
theorem todo_not_must {f g : Background W} {φ ψ : W → Prop} {u : W}
    (hψ : ψ ∈ g w) (hφψ : ∀ v, ψ v → ¬ φ v) (hu : u ∈ bestWorlds f g w) (huψ : ψ u) :
    ¬ necessity f (fun v ↦ insert φ (g v)) φ w :=
  not_necessity_insert hψ hφψ hu huψ (hφψ u huψ)

/-! ### The rows

The uses of (6) to (9), after [schmerling-1982]'s inventory, and the exclusions of (10) are
data; the sequences, follow-ups and challenges instantiate the theorems above. -/

/-- The second utterance of a sequence. -/
inductive Second
  | imperative | assertion
  deriving DecidableEq

/-- Whether the context lets the second utterance revise the first. -/
inductive Continuation
  | revising | conflicting
  deriving DecidableEq

/-- A sequence row of two utterances with incompatible contents. -/
structure Sequence where
  /-- The second utterance. -/
  second : Second
  /-- Whether the context lets it revise the first. -/
  continuation : Continuation

/-- The configuration a sequence row records. -/
def Sequence.ofRow (row : Datum) : Option Sequence := do
  guard (row.feature? "construction" = some "sequence")
  return ⟨← row.parse? "second" [("imperative", Second.imperative), ("assertion", .assertion)],
    ← row.parse? "continuation"
      [("revising", Continuation.revising), ("conflicting", .conflicting)]⟩

/-- In the sequences (11) to (16), a sequence is felicitous exactly when its second move is an
assertion or its continuation revises. -/
theorem sequence_rows : ∀ row ∈ Examples.all, row.feature? "construction" = some "sequence" →
    ∃ s ∈ Sequence.ofRow row,
      (row.JudgedFelicitous ↔ s.second = .assertion ∨ s.continuation = .revising) := by
  decide

/-- A follow-up row of an utterance and a denial. -/
structure FollowUp where
  /-- The utterance. -/
  use : Use
  /-- The denial that follows. -/
  denial : Denial

/-- The configuration a follow-up row records. -/
def FollowUp.ofRow (row : Datum) : Option FollowUp := do
  guard (row.feature? "construction" = some "followUp")
  return ⟨← row.parse? "use" [("assertion", Use.assertion), ("directive", .directive),
      ("advice", .advice), ("concession", .concession)],
    ← row.parse? "denial"
      [("want", Denial.want), ("wish", .wish), ("deontic", .none), ("pastWant", .none)]⟩

/-- The follow-ups of (17), (18), (21), (22) and (40) are acceptable exactly when coherent,
`coherent_iff`. -/
theorem followUp_rows : ∀ row ∈ Examples.all, row.feature? "construction" = some "followUp" →
    ∃ c ∈ FollowUp.ofRow row, (row.judgment = .acceptable ↔ Coherent Bool c.use c.denial) := by
  simp only [coherent_iff]
  decide

/-- The form of an utterance challenged as a lie or disbelieved. -/
inductive Form
  | imperative | performative | assertion
  deriving DecidableEq

/-- The form a challenge row records. -/
def Form.ofRow (row : Datum) : Option Form := do
  guard (row.feature? "construction" = some "challenge")
  return ← row.parse? "form"
    [("imperative", Form.imperative), ("performative", .performative), ("assertion", .assertion)]

/-- Of the challenges (23) to (25), exactly those to an assertion of desire are acceptable. -/
theorem challenge_rows : ∀ row ∈ Examples.all, row.feature? "construction" = some "challenge" →
    ∃ f ∈ Form.ofRow row, (row.judgment = .acceptable ↔ f = .assertion) := by
  decide

end CondoravdiLauer2012
