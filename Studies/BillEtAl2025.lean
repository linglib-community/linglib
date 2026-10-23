module

public import Studies.MitrovicSauerland2016
public import Linglib.Data.Experiments.BillEtAl2025
public import Linglib.Fragments.Georgian.Coordination
public import Linglib.Fragments.Georgian.FocusParticles
public import Linglib.Semantics.Exhaustification.InnocentExclusion
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Bill, Gonzalez, Driemel, Makharoblidze and Pintér (2025): Is DP conjunction always complex?

Bill and colleagues test Mitrović and Sauerland's decomposition of noun-phrase conjunction on how
children understand the three conjunctive expressions of Georgian and Hungarian, a J particle
alone, a μ particle on each conjunct, and both. With van Hout's Transparency Principle the
decomposition predicts the fully pronounced J-μ expressions to be the easiest, and the rival
structures of Szabolcsi and of Haslinger and colleagues predict the J expressions to be. Georgian
children instead replayed J-μ sentences most, and Hungarian children showed no difference.

## Main statements

* `pronounced_mem_attested`: each sentence type pronounces a set of heads that Mitrović and
  Sauerland's examples attest.
* `transparency_prediction`: the decomposition with the Transparency Principle predicts J-μ
  easiest, while `playedMore_child_iff` says Georgian children replayed J-μ more than either
  other sentence type, and those two did not differ.
* `desiderata_iff`: a measure meets the paper's conditions on a successful account exactly when
  the order it predicts is the observed one, which none of `Account.universal.covert`,
  `Account.bareJ.complexity` and `Account.bareJ.covert` does.
* `not_sentenceEffect_hungarian`: Hungarian shows no sentence-type effect on either measure.
* `basicTrue_iff_conjunction`, `accurate_iff`: the decomposition computes the basic truth
  conditions of the test sentences, and the accurate end state is the one with the mentioned
  objects and nothing else on the table.

## Implementation notes

* An account assigns each sentence type the heads of its underlying structure, and a measure of
  difficulty counts the heads it leaves unpronounced or all of them. A difference is the paper's
  star on a contrast or a fixed effect, its direction the sign of the printed estimate.
* The sentence types are the paper's three; it sets aside the expressions with one μ (fn. 1).
* The type-shifter of the decomposition is not counted as a head, since no language pronounces
  it and it would add the same constant to every count. The rival structures are the paper's
  simplification, since neither Szabolcsi's nor Haslinger and colleagues' analysis is formalized.
* Accuracy exhaustifies against the domain alternatives *o is on the table*. The three kinds of
  error are classified in the order the paper lists them, so an error with an unmentioned object
  on the table counts as such whatever else it lacks.

## References

* [bill-etal-2025]
* [mitrovic-sauerland-2014]
* [mitrovic-sauerland-2016]
* [van-hout-1998]
* [szabolcsi-2015]
* [haslinger-etal-2019]
* [clark-2017]
* [fox-2007]
-/

@[expose] public section

namespace BillEtAl2025

open Data.Experiments MitrovicSauerland2016 Exhaustification

/-! ### The test sentences -/

/-- A sentence type pronounces J, the μ head of each conjunct, or all three heads. -/
def Sentence.pronounced : Sentence → Finset Head
  | .j => {.j}
  | .mu => {.mu 0, .mu 1}
  | .jMu => Finset.univ

theorem pronounced_mem_attested (s : Sentence) : s.pronounced ∈ attested := by
  rw [mem_attested_iff]; cases s <;> decide

/-- The J particle of a test language, Georgian *da*, (2), and Hungarian *és*, (1). -/
def jParticle : Language → Coordinator
  | .georgian => Georgian.Coordination.da
  | .hungarian => Hungarian.Coordination.es

/-- The μ particle of a test language, Georgian *-c*, (2), and Hungarian *is*, (1). -/
def muParticle : Language → Coordinator
  | .georgian => Georgian.Coordination.c
  | .hungarian => Hungarian.Coordination.is_

/-- The additive particle of a test language, Georgian *-c* and Hungarian *is*. -/
def additiveParticle : Language → AdditiveParticle
  | .georgian => Georgian.FocusParticles.c
  | .hungarian => Hungarian.FocusParticles.is_

theorem muParticle_isAlsoAdditive (l : Language) :
    (muParticle l).IsAlsoAdditive (additiveParticle l) := by
  cases l <;> rfl

theorem not_jParticle_isAlsoAdditive (l : Language) :
    ¬ (jParticle l).IsAlsoAdditive (additiveParticle l) := by
  cases l <;> decide

/-! ### Accounts and their measures -/

/-- An account assigns each sentence type the heads of its underlying structure, among which are
the heads it pronounces. -/
structure Account where
  /-- The heads of the structure underlying a sentence type. -/
  underlying : Sentence → Finset Head
  /-- A sentence type pronounces only heads of its structure. -/
  pronounced_subset : ∀ s, s.pronounced ⊆ underlying s

namespace Account

/-- Mitrović and Sauerland give every sentence type the whole structure. -/
def universal : Account where
  underlying _ := Finset.univ
  pronounced_subset _ := Finset.subset_univ _

/-- The rival structures give J expressions J alone, and μ and J-μ expressions the whole
structure. -/
def bareJ : Account where
  underlying
    | .j => {.j}
    | .mu | .jMu => Finset.univ
  pronounced_subset := by decide

/-- The complexity of a sentence type is the number of heads in its structure. -/
def complexity (a : Account) (s : Sentence) : ℕ := (a.underlying s).card

/-- The covert pieces of a sentence type are the heads of its structure it leaves unpronounced,
the Transparency Principle's measure of difficulty. -/
def covert (a : Account) (s : Sentence) : ℕ := (a.underlying s \ s.pronounced).card

theorem card_pronounced_add_covert (a : Account) (s : Sentence) :
    s.pronounced.card + a.covert s = a.complexity s :=
  (add_comm _ _).trans (Finset.card_sdiff_add_card_eq_card (a.pronounced_subset s))

theorem universal_covert (s : Sentence) :
    universal.covert s = Fintype.card Head - s.pronounced.card := by
  simp [covert, universal, Finset.card_univ_sdiff]

end Account

/-! ### The predictions -/

theorem transparency_prediction (s : Sentence) (h : s ≠ .jMu) :
    Account.universal.covert .jMu < Account.universal.covert s := by
  revert s; decide

theorem bareJ_prediction : Account.bareJ.complexity .j < Account.bareJ.complexity .jMu := by
  decide

theorem bareJ_underlying_mu : Account.bareJ.underlying .mu = Account.bareJ.underlying .jMu := rfl

theorem bareJ_mu_opaque : Account.bareJ.covert .jMu < Account.bareJ.covert .mu := by
  decide

/-! ### The findings -/

/-- The two sentence types a follow-up contrast compares, in the paper's order. -/
def Contrast.sentences : Contrast → Sentence × Sentence
  | .jVsJMu => (.j, .jMu)
  | .jVsMu => (.j, .mu)
  | .jMuVsMu => (.jMu, .mu)

/-- A group replayed sentences of one type more than those of another when the paper stars
their contrast, in the direction of the estimate, which is negative when the first was played
less. Children replay the sentences they find difficult, so this is the order of difficulty
the Georgian data show. -/
def PlayedMore (g : Group) (s t : Sentence) : Prop :=
  ∃ c, (contrasts g c).mark = .starred ∧
    (c.sentences = (s, t) ∧ 0 < (contrasts g c).estimate.toRat ∨
      c.sentences = (t, s) ∧ (contrasts g c).estimate.toRat < 0)

instance (g : Group) : DecidableRel (PlayedMore g) := fun _ _ ↦
  inferInstanceAs (Decidable (∃ _, _ ∧ _))

theorem playedMore_child_iff (s t : Sentence) :
    PlayedMore .child s t ↔ s = .jMu ∧ t ≠ .jMu := by
  revert s t; decide

theorem not_playedMore_adult (s t : Sentence) : ¬ PlayedMore .adult s t := by
  revert s t; decide

theorem playedMore_child_contradicts_transparency {s t : Sentence}
    (h : PlayedMore .child s t) : Account.universal.covert s < Account.universal.covert t := by
  obtain ⟨rfl, ht⟩ := (playedMore_child_iff s t).1 h
  exact transparency_prediction t ht

/-- A language shows a sentence-type effect on a measure when the paper stars that fixed
effect. -/
def SentenceEffect (l : Language) (m : Measure) : Prop := (lrt l m .sentence).mark = .starred

instance (l : Language) (m : Measure) : Decidable (SentenceEffect l m) :=
  inferInstanceAs (Decidable (_ = _))

theorem not_sentenceEffect_hungarian (m : Measure) : ¬ SentenceEffect .hungarian m := by
  revert m; decide

theorem georgian_sentenceEffect_iff (m : Measure) : SentenceEffect .georgian m ↔ m = .playedN := by
  revert m; decide

/-- A measure meets the paper's conditions on a successful account when J-μ is more complex than
J and than μ, and J and μ are equally complex. -/
def Desiderata (c : Sentence → ℕ) : Prop :=
  c .j < c .jMu ∧ c .mu < c .jMu ∧ c .j = c .mu

instance (c : Sentence → ℕ) : Decidable (Desiderata c) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem desiderata_iff (c : Sentence → ℕ) :
    Desiderata c ↔ ∀ s t, c s < c t ↔ PlayedMore .child t s := by
  simp only [playedMore_child_iff]
  constructor
  · rintro ⟨h1, h2, h3⟩ s t
    cases s <;> cases t <;> simp <;> omega
  · intro h
    refine ⟨(h _ _).2 ⟨rfl, nofun⟩, (h _ _).2 ⟨rfl, nofun⟩, ?_⟩
    have := h .j .mu; have := h .mu .j
    simp at *
    omega

theorem not_desiderata_universal_covert : ¬ Desiderata Account.universal.covert := by decide

theorem not_desiderata_bareJ_complexity : ¬ Desiderata Account.bareJ.complexity := by decide

theorem not_desiderata_bareJ_covert : ¬ Desiderata Account.bareJ.covert := by decide

theorem mu_kind_differs :
    (muParticle .georgian).morph.kind = .bound .after .clitic ∧
      (muParticle .hungarian).morph.kind = .free :=
  ⟨rfl, rfl⟩

/-! ### The act-out task -/

/-- A trial shows three objects, of which the test sentence mentions two. -/
abbrev Object := Fin objectsPerTrial

instance : NeZero objectsPerTrial := ⟨by decide⟩

/-- An end state of a trial is the set of objects on the table. -/
abbrev EndState := Finset Object

/-- The test sentence mentions the first two objects. -/
def mentioned : Finset Object := {0, 1}

/-- The proposition that an object is on the table, the alternative to the test sentence that
names it alone. -/
def onTable (o : Object) : Set EndState := {st | o ∈ st}

instance (o : Object) : DecidablePred (· ∈ onTable o) := fun st ↦
  inferInstanceAs (Decidable (o ∈ st))

/-- An end state meets the basic truth conditions of the test sentence when each mentioned object
is on the table. -/
def BasicTrue (st : EndState) : Prop := mentioned ⊆ st

instance : DecidablePred BasicTrue := fun st ↦ inferInstanceAs (Decidable (_ ⊆ st))

theorem not_basicTrue_singleton : ¬ BasicTrue {0} := by decide

theorem basicTrue_iff_conjunction {j : Coordinator} (hj : j.role = .conjunctive)
    (st : EndState) : BasicTrue st ↔ j.denote {mu (shift (0 : Object)), mu (shift 1)} (· ∈ st) := by
  rw [conjunction_apply hj]; simp [BasicTrue, mentioned, Finset.insert_subset_iff]

/-- An end state is accurate when it matches the exhaustified sentence, the basic truth
conditions with every innocently excludable alternative naming one object denied. -/
def Accurate (st : EndState) : Prop := st ∈ exhIE (Set.range onTable) {st | BasicTrue st}

theorem accurate_iff (st : EndState) : Accurate st ↔ st = mentioned := by
  have h : (exh (Set.range onTable) {st | BasicTrue st}).Nonempty := ⟨mentioned, by decide⟩
  rw [Accurate, exhIE_eq_exh_of_nonempty _ _ h]
  revert st; decide

instance : DecidablePred Accurate := fun st ↦ decidable_of_iff' _ (accurate_iff st)

theorem Accurate.basicTrue {st : EndState} (h : Accurate st) : BasicTrue st :=
  exhIE_subset _ _ h

/-- The kind of an inaccurate end state, which has an unmentioned object on the table, or else
exactly one of the mentioned objects, or else neither. -/
def errorKind (st : EndState) : ErrorKind :=
  if ¬ st ⊆ mentioned then .unmentioned
  else if (st ∩ mentioned).card = 1 then .oneMentioned
  else .neitherMentioned

theorem errorKind_eq_neitherMentioned_iff {st : EndState} (h : ¬ Accurate st) :
    errorKind st = .neitherMentioned ↔ st = ∅ := by
  rw [accurate_iff] at h
  revert st; decide

theorem errorKind_surjOn : Set.SurjOn errorKind {st | ¬ Accurate st} Set.univ := by
  rintro (_ | _ | _) -
  · exact ⟨{2}, by decide, by decide⟩
  · exact ⟨{0}, by decide, by decide⟩
  · exact ⟨∅, by decide, by decide⟩

-- The error counts add up to the children's errors.
example : ∑ k, (childErrorKinds k).count = childErrors := by decide

-- The printed percentages round the counts.
example : ∀ k, (childErrorKinds k).percent.RoundsPercent (childErrorKinds k).count childErrors := by
  decide

end BillEtAl2025
