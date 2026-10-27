module

public import Linglib.Fragments.Mandarin.Adverbs
public import Linglib.Fragments.Mandarin.Verbs
public import Linglib.Semantics.Presupposition.Verb
public import Linglib.Semantics.Presupposition.Again
public import Linglib.Semantics.Aspect.Phasal
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Data.Fintype.Prod
public import Linglib.Pragmatics.Competition
public import Linglib.Semantics.Exhaustification.Finite

/-!
# Wang (2025): Presupposition, Competition, and Coherence

Wang's dissertation explains when a presupposition trigger of Mandarin is obligatory and when it
is dropped by a competition between the presuppositional sentence and its non-presuppositional
alternative, a sentence with the same assertion that is obtained by deleting or replacing the
trigger. Three constraints decide the competition, ranked in this order. Internal Coherence
requires the utterance to be consistent with the common ground, Felicity Presupposition requires
a presupposition to be entailed by it, and Maximize Presupposition, after Heim, bars a form
that has a presuppositionally stronger alternative. An utterance commits the speaker to a set of
information states and a context admits a set of them, so coherence is overlap, and the context
entails a proposition when every state it admits believes the proposition.

## Main statements

* `obligatory_of_entailed`, `omitted_of_not_entailed`: the trigger is obligatory where the
  context entails its presupposition and dropped where the context is silent about it.
* `obligatory_of_positive_evidence`, `omitted_of_denied`, `omitted_of_ignorance`: against the
  exhaustified alternative the trigger is obligatory under positive evidence for the
  presupposition, and dropped where the context denies it or the speaker is ignorant of it.
* `presup_beats_of_mp_over_fp`: were Maximize Presupposition ranked above Felicity
  Presupposition, every trigger with an alternative would be obligatory.
* `notNow_two_maxima`, `optional_of_two_readings`: the alternative of *buzai* 'no longer' has two
  exhaustified readings, and the trigger is optional because it loses on one and wins on the
  other.

## Implementation notes

* Information states are nonempty sets of worlds; the belief operator `K p` is the set of
  states included in `p`, and possibility and ignorance are the corresponding overlap
  conditions.
* Maximize Presupposition is blocking, `Competition.Blocked`. A sentence without a
  presupposition violates it in every context, as in the dissertation's tableaux, and its rank
  below Felicity Presupposition confines its effect to contexts that entail the presupposition.
* The aspectual triggers take their meanings from `Presupposition.again` and
  `Aspect.Phasal.denote`, with the earlier time, a free variable of the dissertation's entries,
  existentially closed.
* `Trigger` lists the lexical rows of Table 4.1 without its cleft row. The experiments of
  Chapters 3 and 5 and the de re and postsupposition analyses of Chapters 5 and 6 are not
  represented.

## References

* [wang-2025]
* [katzir-2007]
* [heim-1991]
-/

@[expose] public section

namespace Wang2025

variable {W : Type*}

/-! ### Information states, commitments and contexts -/

/-- `K p` is the set of nonempty information states included in `p`, those in which the speaker
believes `p`. -/
def K (p : Set W) : Set (Set W) := {s | s.Nonempty ∧ s ⊆ p}

/-- `Poss p` is the set of states meeting `p`, those in which the speaker holds `p` possible. -/
def Poss (p : Set W) : Set (Set W) := {s | (s ∩ p).Nonempty}

/-- `Ignorant p` is the set of states in which `p` and its negation are both possible. -/
def Ignorant (p : Set W) : Set (Set W) := Poss p ∩ Poss pᶜ

/-- A candidate is an utterance in the competition, given by the states its use commits the
speaker to and by its presupposition if it has one. -/
structure Candidate (W : Type*) where
  commitment : Set (Set W)
  presup : Option (Set W)

/-- The presuppositional sentence with presupposition `p` and assertion `a` commits the speaker
to both. -/
def presupSentence (p a : Set W) : Candidate W := ⟨K (p ∩ a), some p⟩

/-- The unexhaustified non-presuppositional alternative commits the speaker to `a`. -/
def plain (a : Set W) : Candidate W := ⟨K a, none⟩

/-- The alternative exhaustified against `q` below the belief operator commits the speaker to
`a` and to the negation of `q`. -/
def plainExhBelowK (a q : Set W) : Candidate W := ⟨K (a ∩ qᶜ), none⟩

/-- The alternative exhaustified against `q` above the belief operator commits the speaker to
`a` while the speaker does not believe `q`. -/
def plainExhAboveK (a q : Set W) : Candidate W := ⟨K a \ K q, none⟩

/-! ### The constraints and their ranking, (3) -/

/-- Internal Coherence is violated when the commitment excludes every admissible state. -/
def ViolIC (ctx : Set (Set W)) (c : Candidate W) : Prop := Disjoint ctx c.commitment

/-- Felicity Presupposition is violated by a presuppositional sentence whose presupposition
the context does not entail. -/
def ViolFP (ctx : Set (Set W)) (c : Candidate W) : Prop :=
  ∃ p, c.presup = some p ∧ ¬ ctx ⊆ K p

/-- A context admits a candidate when every admissible state believes its presupposition, if it
has one. -/
def Candidate.admits (c : Candidate W) : Set (Set (Set W)) :=
  {ctx | ∀ p, c.presup = some p → ctx ⊆ K p}

theorem Candidate.admits_of_presup_none {c : Candidate W} (h : c.presup = none) :
    c.admits = Set.univ := by
  ext ctx; simp [Candidate.admits, h]

theorem Candidate.admits_of_presup_some {c : Candidate W} {p : Set W} (h : c.presup = some p) :
    c.admits = {ctx | ctx ⊆ K p} := by
  ext ctx; simp [Candidate.admits, h]

theorem Candidate.admits_ssubset_univ {c : Candidate W} {p : Set W} (h : c.presup = some p) :
    c.admits ⊂ Set.univ := by
  rw [Candidate.admits_of_presup_some h]
  refine Set.ssubset_univ_iff.2 fun huniv ↦ ?_
  have hmem : ({∅} : Set (Set W)) ∈ {ctx | ctx ⊆ K p} := by rw [huniv]; trivial
  exact (hmem (Set.mem_singleton _)).1.ne_empty rfl

/-- Maximize Presupposition is violated by a candidate that its rival blocks, the rival being
presuppositionally stronger, admitted by strictly fewer contexts, (3c). -/
def ViolMP (rival c : Candidate W) : Prop :=
  Competition.Blocked (fun _ ↦ {rival}) Candidate.admits c

theorem violMP_iff {rival c : Candidate W} : ViolMP rival c ↔ rival.admits ⊂ c.admits :=
  ⟨fun ⟨_, h, hss⟩ ↦ h ▸ hss, fun h ↦ ⟨rival, rfl, h⟩⟩

theorem violMP_of_presup_none {rival c : Candidate W} {p : Set W} (hc : c.presup = none)
    (hr : rival.presup = some p) : ViolMP rival c :=
  violMP_iff.2 (Candidate.admits_of_presup_none hc ▸ Candidate.admits_ssubset_univ hr)

theorem not_violMP_self (c : Candidate W) : ¬ ViolMP c c :=
  fun h ↦ (violMP_iff.1 h).ne rfl

/-- `Beats cs a b` compares two candidates by strict domination along the list `cs` of violation
predicates, `a` beating `b` at the first constraint on which they differ. -/
def Beats : List (Candidate W → Prop) → Candidate W → Candidate W → Prop
  | [], _, _ => False
  | C :: cs, a, b => (¬ C a ∧ C b) ∨ ((C a ↔ C b) ∧ Beats cs a b)

/-- The ranking Internal Coherence ≫ Felicity Presupposition ≫ Maximize Presupposition,
evaluated for the competition between `sp` and its alternative. -/
def ranking (ctx : Set (Set W)) (sp : Candidate W) : List (Candidate W → Prop) :=
  [ViolIC ctx, ViolFP ctx, ViolMP sp]

@[simp] theorem violFP_presupSentence {ctx : Set (Set W)} {p a : Set W} :
    ViolFP ctx (presupSentence p a) ↔ ¬ ctx ⊆ K p :=
  ⟨fun ⟨_, hq, h⟩ ↦ Option.some.inj hq ▸ h, fun h ↦ ⟨p, rfl, h⟩⟩

/-! ### The three decisive facts -/

theorem presup_beats_of_incoherent {ctx : Set (Set W)} {p a : Set W} {c : Candidate W}
    (hsp : ¬ Disjoint ctx (K (p ∩ a))) (hc : Disjoint ctx c.commitment) :
    Beats (ranking ctx (presupSentence p a)) (presupSentence p a) c :=
  Or.inl ⟨hsp, hc⟩

theorem plain_beats_of_not_entailed {ctx : Set (Set W)} {p a : Set W} {c : Candidate W}
    (hc0 : c.presup = none) (hsp : ¬ Disjoint ctx (K (p ∩ a))) (hc : ¬ Disjoint ctx c.commitment)
    (hp : ¬ ctx ⊆ K p) :
    Beats (ranking ctx (presupSentence p a)) c (presupSentence p a) :=
  Or.inr ⟨⟨fun h ↦ absurd h hc, fun h ↦ absurd h hsp⟩,
    Or.inl ⟨fun ⟨q, hq, _⟩ ↦ by simp [hc0] at hq, ⟨p, rfl, hp⟩⟩⟩

theorem presup_beats_of_entailed {ctx : Set (Set W)} {p a : Set W} {c : Candidate W}
    (hc0 : c.presup = none) (hsp : ¬ Disjoint ctx (K (p ∩ a))) (hc : ¬ Disjoint ctx c.commitment)
    (hp : ctx ⊆ K p) :
    Beats (ranking ctx (presupSentence p a)) (presupSentence p a) c :=
  Or.inr ⟨⟨fun h ↦ absurd h hsp, fun h ↦ absurd h hc⟩,
    Or.inr ⟨⟨fun ⟨q, hq, hnq⟩ ↦ absurd hp (Option.some.inj hq ▸ hnq), fun ⟨q, hq, _⟩ ↦ by
      simp [hc0] at hq⟩,
      Or.inl ⟨not_violMP_self _, violMP_of_presup_none hc0 rfl⟩⟩⟩

/-! ### Felicity Presupposition above Maximize Presupposition -/

/-- Were Maximize Presupposition ranked above Felicity Presupposition, a coherent
presuppositional sentence would beat a coherent alternative whatever the context entails, so
every trigger with an alternative would be obligatory. -/
theorem presup_beats_of_mp_over_fp {ctx : Set (Set W)} {p a : Set W} {c : Candidate W}
    (hc0 : c.presup = none) (hsp : ¬ Disjoint ctx (K (p ∩ a))) (hc : ¬ Disjoint ctx c.commitment) :
    Beats [ViolIC ctx, ViolMP (presupSentence p a), ViolFP ctx] (presupSentence p a) c :=
  Or.inr ⟨⟨fun h ↦ absurd h hsp, fun h ↦ absurd h hc⟩,
    Or.inl ⟨not_violMP_self _, violMP_of_presup_none hc0 rfl⟩⟩

/-! ### The tableaux -/

/-- In Table 4.2 the context entails the presupposition, so the trigger is obligatory. -/
theorem obligatory_of_entailed {ctx : Set (Set W)} {p a : Set W} (hp : ctx ⊆ K p)
    (hwit : ∃ s ∈ ctx, s ⊆ a) :
    Beats (ranking ctx (presupSentence p a)) (presupSentence p a) (plain a) := by
  obtain ⟨s, hs, hsa⟩ := hwit
  have hsp := hp hs
  refine presup_beats_of_entailed rfl ?_ ?_ hp
  · exact Set.not_disjoint_iff.mpr ⟨s, hs, hsp.1, Set.subset_inter hsp.2 hsa⟩
  · exact Set.not_disjoint_iff.mpr ⟨s, hs, hsp.1, hsa⟩

/-- In Table 4.3 the context does not entail the presupposition, so the trigger is dropped. -/
theorem omitted_of_not_entailed {ctx : Set (Set W)} {p a : Set W} (hp : ¬ ctx ⊆ K p)
    (hwit : ∃ s ∈ ctx, s.Nonempty ∧ s ⊆ p ∩ a) :
    Beats (ranking ctx (presupSentence p a)) (plain a) (presupSentence p a) := by
  obtain ⟨s, hs, hne, hsa⟩ := hwit
  refine plain_beats_of_not_entailed rfl ?_ ?_ hp
  · exact Set.not_disjoint_iff.mpr ⟨s, hs, hne, hsa⟩
  · exact Set.not_disjoint_iff.mpr ⟨s, hs, hne, hsa.trans Set.inter_subset_right⟩

/-- With positive evidence for the presupposition and the alternative exhaustified below the belief
operator, the trigger is obligatory (Table 4.4). -/
theorem obligatory_of_positive_evidence {ctx : Set (Set W)} {p a : Set W}
    (hposs : ctx ⊆ Poss p) (hwit : ∃ s ∈ ctx, s.Nonempty ∧ s ⊆ p ∩ a) :
    Beats (ranking ctx (presupSentence p a)) (presupSentence p a) (plainExhBelowK a p) := by
  obtain ⟨s, hs, hne, hsa⟩ := hwit
  refine presup_beats_of_incoherent (Set.not_disjoint_iff.mpr ⟨s, hs, hne, hsa⟩) ?_
  rw [Set.disjoint_left]
  rintro t ht ⟨-, hta⟩
  obtain ⟨w, hw, hwp⟩ := hposs ht
  exact (hta hw).2 hwp

/-- In Table 4.5 the context denies the presupposition, so the presuppositional sentence is
incoherent and the alternative wins. -/
theorem omitted_of_denied {ctx : Set (Set W)} {p a : Set W} (hneg : ctx ⊆ K pᶜ)
    (hwit : ∃ s ∈ ctx, s ⊆ a) :
    Beats (ranking ctx (presupSentence p a)) (plainExhBelowK a p) (presupSentence p a) := by
  obtain ⟨s, hs, hsa⟩ := hwit
  have hsn := hneg hs
  refine Or.inl ⟨Set.not_disjoint_iff.mpr ⟨s, hs, hsn.1, Set.subset_inter hsa hsn.2⟩, ?_⟩
  show Disjoint ctx (K (p ∩ a))
  rw [Set.disjoint_left]
  rintro t ht ⟨⟨w, hw⟩, htp⟩
  exact (hneg ht).2 hw (htp hw).1

/-- In an ignorance context with the alternative exhaustified above the belief operator, the trigger
is dropped (Table 4.6). -/
theorem omitted_of_ignorance {ctx : Set (Set W)} {p a : Set W} (hign : ctx ⊆ Ignorant p)
    (hwit : ∃ s ∈ ctx, s ⊆ a) :
    Beats (ranking ctx (presupSentence p a)) (plainExhAboveK a p) (presupSentence p a) := by
  obtain ⟨s, hs, hsa⟩ := hwit
  obtain ⟨⟨w, hw, -⟩, ⟨v, hv, hvp⟩⟩ := hign hs
  refine Or.inl ⟨?_, ?_⟩
  · refine Set.not_disjoint_iff.mpr ⟨s, hs, ⟨⟨w, hw⟩, hsa⟩, fun hsp ↦ ?_⟩
    exact hvp (hsp.2 hv)
  · show Disjoint ctx (K (p ∩ a))
    rw [Set.disjoint_left]
    rintro t ht ⟨-, htp⟩
    obtain ⟨-, ⟨u, hu, hup⟩⟩ := hign ht
    exact hup (htp hu).1

/-- With positive but not entailing evidence for the presupposition, the alternative wins on one
exhaustified reading and loses on the other, so the trigger is optional (Tables 4.7 and 4.9). -/
theorem optional_of_two_readings {ctx : Set (Set W)} {p a : Set W} (hposs : ctx ⊆ Poss p)
    (hp : ¬ ctx ⊆ K p) (hwit : ∃ s ∈ ctx, s.Nonempty ∧ s ⊆ p ∩ a) :
    Beats (ranking ctx (presupSentence p a)) (plainExhBelowK a pᶜ) (presupSentence p a) ∧
      Beats (ranking ctx (presupSentence p a)) (presupSentence p a) (plainExhBelowK a p) := by
  refine ⟨?_, obligatory_of_positive_evidence hposs hwit⟩
  obtain ⟨s, hs, hne, hsa⟩ := hwit
  refine plain_beats_of_not_entailed rfl (Set.not_disjoint_iff.mpr ⟨s, hs, hne, hsa⟩) ?_ hp
  exact Set.not_disjoint_iff.mpr ⟨s, hs, hne, fun w hw ↦ ⟨(hsa hw).2, not_not_intro (hsa hw).1⟩⟩

/-- In Tables 4.8 and 4.10 the context entails the presupposition, and the trigger wins on both
readings of the alternative. -/
theorem obligatory_of_entailed_of_two_readings {ctx : Set (Set W)} {p a : Set W}
    (hp : ctx ⊆ K p) (hwit : ∃ s ∈ ctx, s ⊆ a) :
    Beats (ranking ctx (presupSentence p a)) (presupSentence p a) (plainExhBelowK a pᶜ) ∧
      Beats (ranking ctx (presupSentence p a)) (presupSentence p a) (plainExhBelowK a p) := by
  obtain ⟨s, hs, hsa⟩ := hwit
  obtain ⟨hne, hsp⟩ := hp hs
  have hspa : s ⊆ p ∩ a := Set.subset_inter hsp hsa
  refine ⟨presup_beats_of_entailed rfl (Set.not_disjoint_iff.mpr ⟨s, hs, hne, hspa⟩) ?_ hp,
    obligatory_of_positive_evidence (fun t ht ↦ ?_) ⟨s, hs, hne, hspa⟩⟩
  · exact Set.not_disjoint_iff.mpr ⟨s, hs, hne, fun w hw ↦ ⟨hsa hw, not_not_intro (hsp hw)⟩⟩
  · obtain ⟨⟨w, hw⟩, htp⟩ := hp ht
    exact ⟨w, hw, htp hw⟩

/-! ### The alternative structure of the triggers, Table 4.1 -/

/-- A trigger's non-presuppositional alternative is obtained by deleting the trigger, by
replacing it, or not at all. -/
inductive AltStructure
  | deletion
  | replacement
  | none
  deriving DecidableEq, Repr

/-- The lexical triggers of Table 4.1 are the adverbs *ye* 'also', *fan'er* 'instead', *reng*
'still', *you* and *zai* 'again', *buzai* 'no longer' and *jiu* 'only', and the verbs *kaishi*
'start', *zhidao* 'know' and *houhui* 'regret'. -/
inductive Trigger
  | ye
  | faner
  | reng
  | you
  | zai
  | kaishi
  | buzai
  | zhidao
  | jiu
  | houhui
  deriving DecidableEq, Repr

/-- The fragment entry of a trigger, an adverb or a verb. -/
def Trigger.entry : Trigger → Presupposition.TriggerItem ⊕ Verb
  | .ye => .inl Mandarin.Adverbs.ye
  | .faner => .inl Mandarin.Adverbs.faner
  | .reng => .inl Mandarin.Adverbs.reng
  | .you => .inl Mandarin.Adverbs.you
  | .zai => .inl Mandarin.Adverbs.zai
  | .buzai => .inl Mandarin.Adverbs.buzai
  | .jiu => .inl Mandarin.Adverbs.jiu
  | .kaishi => .inr Mandarin.kaishi
  | .zhidao => .inr Mandarin.zhidao
  | .houhui => .inr Mandarin.houhui

/-- Table 4.1. A trigger whose assertion is its prejacent deletes, as the additive, contrastive,
continuative, repetitive and inchoative ones do. The cessative and the factive replace, *buzai* by
negation and *zhidao* by *renwei* 'believe'. No sequence of deletions and replacements yields a
sentence with the assertion of *jiu* 'only' or of *houhui* 'regret', which have no alternative. -/
def Trigger.altStructure : Trigger → AltStructure
  | .ye | .faner | .reng | .you | .zai | .kaishi => .deletion
  | .buzai | .zhidao => .replacement
  | .jiu | .houhui => .none

theorem isTrigger_of_entry {t : Trigger} {v : Verb} (h : t.entry = .inr v) :
    v.IsTrigger := by
  cases t <;> simp only [Trigger.entry, Sum.inr.injEq, reduceCtorEq] at h <;> subst h <;> decide

/-- The replacement for *zhidao* is non-presuppositional, as (1) requires, since *renwei*
'believe' is not a trigger. -/
theorem not_isTrigger_renwei : ¬ Mandarin.renwei.IsTrigger := by decide

/-! ### The aspectual triggers

The repetitive *you* and *zai*, (12), the continuative *reng*, (24), the inchoative *kaishi*,
(38), and the cessative *buzai*, (19), relate their prejacent at the index of evaluation to the
prejacent at an earlier index, presupposing that it held or failed then and asserting that it
holds or fails now. -/

section Aspectual

open Presupposition ModalLogic Aspect

/-- The candidate for a sentence with the trivalent meaning `φ` commits the speaker to its
presupposition, where `φ` is defined, and to its assertion, where `φ` is true. -/
def Candidate.ofTrivalent (φ : W → SignType) : Candidate W :=
  presupSentence (Function.support φ) (posSupport φ)

variable {R S : SetRel W W} {P : W → Prop} {ctx : Set (Set W)} {t : Trigger} {φ : W → SignType}

theorem Candidate.ofTrivalent_eq_presupSentence {a : Set W}
    (h : ∀ w, φ w ≠ 0 → (φ w = 1 ↔ w ∈ a)) :
    Candidate.ofTrivalent φ = presupSentence (Function.support φ) a := by
  simp only [Candidate.ofTrivalent, presupSentence, Candidate.mk.injEq, and_true]
  congr 1
  ext w
  exact and_congr_right (h w)

/-- The meaning of an aspectual trigger with the prejacent `P`. `R` relates an index to the
earlier ones, the `<` of (12), and `S` relates an index to the earlier index of (19), (24) and
(38), a relation the dissertation writes `∞`. The meaning of *kaishi* is that of the phasal class
of its fragment entry, and the other triggers of Table 4.1 are not aspectual. -/
noncomputable def Trigger.aspectual (R S : SetRel W W) (P : W → Prop) :
    Trigger → Option (W → SignType)
  | .you | .zai => some (again R P)
  | .reng => some (Phasal.continuation.denote S P)
  | .buzai => some (Phasal.cessation.denote S P)
  | .kaishi => Mandarin.kaishi.phasal.map (·.denote S P)
  | _ => none

/-- An aspectual trigger whose alternative arises by deletion asserts its prejacent, as (1) requires
of the alternative. -/
theorem eq_one_iff_of_altStructure_deletion (h : t.aspectual R S P = some φ)
    (ht : t.altStructure = .deletion) {w : W} (hw : φ w ≠ 0) : φ w = 1 ↔ P w := by
  cases t <;>
    first | (cases ht; done) | (cases h; done) | (cases h; simp_all [Phasal.denote, again])

theorem eq_one_iff_buzai (h : Trigger.buzai.aspectual R S P = some φ) {w : W} (hw : φ w ≠ 0) :
    φ w = 1 ↔ ¬ P w := by
  cases h; simp_all [Phasal.denote]

/-- An aspectual trigger asserting its prejacent is obligatory when the context entails its
presupposition (Table 4.2). -/
theorem aspectual_obligatory_of_entailed (h : t.aspectual R S P = some φ)
    (ht : t.altStructure = .deletion) (hp : ctx ⊆ K (Function.support φ))
    (hwit : ∃ s ∈ ctx, s ⊆ {w | P w}) :
    Beats (ranking ctx (.ofTrivalent φ)) (.ofTrivalent φ) (plain {w | P w}) := by
  rw [Candidate.ofTrivalent_eq_presupSentence fun _ ↦ eq_one_iff_of_altStructure_deletion h ht]
  exact obligatory_of_entailed hp hwit

/-- An aspectual trigger asserting its prejacent loses to the sentence without it when the context
does not entail its presupposition (Table 4.3). -/
theorem aspectual_omitted_of_not_entailed (h : t.aspectual R S P = some φ)
    (ht : t.altStructure = .deletion) (hp : ¬ ctx ⊆ K (Function.support φ))
    (hwit : ∃ s ∈ ctx, s.Nonempty ∧ s ⊆ Function.support φ ∩ {w | P w}) :
    Beats (ranking ctx (.ofTrivalent φ)) (plain {w | P w}) (.ofTrivalent φ) := by
  rw [Candidate.ofTrivalent_eq_presupSentence fun _ ↦ eq_one_iff_of_altStructure_deletion h ht]
  exact omitted_of_not_entailed hp hwit

end Aspectual

/-! ### Exhaustification by maximal consistent subsets, (20) and (24) -/

section Exhaustification

variable [DecidableEq W]

/-- The reading of (24) for the maximal subset `M` is `φ` with every member of `M` negated. -/
def exhMx (φ : Finset W) (M : Finset (Finset W)) : Finset W :=
  φ.filter (fun w ↦ ∀ q ∈ M, w ∉ q)

open Exhaustification in
/-- When the maximal consistent subset is unique, innocent exclusion, the operator of (20), and
the operator of (24) agree, (25). -/
theorem exhIE_eq_exhMx_of_unique {φ : Finset W} {alts M₀ : Finset (Finset W)}
    (h₀ : IsMaximalExclusion alts φ M₀) (huniq : ∀ M, IsMaximalExclusion alts φ M → M = M₀) :
    exhIE alts.toSetFamily ↑φ = ↑(exhMx φ M₀) := by
  rw [exhIE_eq_sdiff_of_maximal_unique _ _ (isMaximalExclusion_iff.1 h₀) fun X hX ↦ ?_]
  · ext w
    simp [exhMx, Finset.mem_toSetFamily]
  · obtain ⟨M, -, rfl⟩ := Finset.exists_toSetFamily_eq_of_subset hX.prop.1
    rw [huniq M (isMaximalExclusion_iff.2 hX)]

/-- The worlds of the disjunction example (26) are the pairs of truth values of `p` and `q`. -/
abbrev PQ := Bool × Bool

/-- The alternative `p` of (26). -/
def pAlt : Finset PQ := Finset.univ.filter (·.1 = true)

/-- The alternative `q` of (26). -/
def qAlt : Finset PQ := Finset.univ.filter (·.2 = true)

/-- With alternatives `p`, `q` and `p ∧ q` (26), `p ∨ q` has two maximal consistent exclusions,
yielding `q ∧ ¬p` and `p ∧ ¬q`. -/
theorem disjunction_two_maxima :
    Exhaustification.IsMaximalExclusion {pAlt, qAlt, pAlt ∩ qAlt} (pAlt ∪ qAlt)
        {pAlt, pAlt ∩ qAlt} ∧
      Exhaustification.IsMaximalExclusion {pAlt, qAlt, pAlt ∩ qAlt} (pAlt ∪ qAlt)
        {qAlt, pAlt ∩ qAlt} ∧
      exhMx (pAlt ∪ qAlt) {pAlt, pAlt ∩ qAlt} = qAlt \ pAlt ∧
      exhMx (pAlt ∪ qAlt) {qAlt, pAlt ∩ qAlt} = pAlt \ qAlt := by
  decide

/-- The cell of (48) in which the state held in the past iff `past` and holds now iff `now`, a
world being the pair of the two truth values. -/
def cell (past now : Bool) : Finset PQ := {(past, now)}

/-- The alternatives of (48), the four cells. -/
def cells : Finset (Finset PQ) :=
  {cell false true, cell true false, cell true true, cell false false}

/-- The prejacent of (46), that the state does not hold now, the alternative of a sentence with
*buzai* 'no longer'. -/
def notNow : Finset PQ := Finset.univ.filter (·.2 = false)

/-- The alternative of *buzai* has two maximal consistent subsets (49), meaning that the state held
in the past or that it did not. -/
theorem notNow_two_maxima :
    Exhaustification.IsMaximalExclusion cells notNow
        {cell false true, cell true true, cell false false} ∧
      Exhaustification.IsMaximalExclusion cells notNow
        {cell false true, cell true false, cell true true} ∧
      exhMx notNow {cell false true, cell true true, cell false false} = cell true false ∧
      exhMx notNow {cell false true, cell true false, cell true true} = cell false false := by
  decide

end Exhaustification

end Wang2025
