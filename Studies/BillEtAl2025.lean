module

public import Studies.MitrovicSauerland2016
public import Linglib.Data.Statistics.BillEtAl2025
public import Linglib.Fragments.Georgian.Coordination
public import Linglib.Fragments.Georgian.FocusParticles
public import Linglib.Semantics.Exhaustification.InnocentExclusion
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Multiset.Filter

/-!
# Bill, Gonzalez, Driemel, Makharoblidze and Pintér (2025): Is DP conjunction always complex?

Georgian and Hungarian conjoin two noun phrases with a J particle alone, with a μ particle on each
conjunct, or with both. A sentence type `s` pronounces the set `s.pronounced` of the heads of
Mitrović and Sauerland's structure, J and a μ for each conjunct, and we order the sentence types
by inclusion of these sets: the J-μ type lies above the J and the μ type, which are incomparable.

An account gives each sentence type the heads of its underlying structure, among which are the
heads it pronounces. We define two measures of difficulty on an account `a`, the number
`a.complexity s` of heads of the structure and the number `a.covert s` of them that the sentence
leaves unpronounced, the measure of the Transparency Principle. Among sentence types with one
structure `a.complexity` is constant and `a.covert` is strictly antitone,
`Account.covert_strictAntiOn`.

A group replayed sentences of type `s` more than those of type `t`, `PlayedMore g s t`, when the
follow-up contrast between the two is significant at .05 in that direction. Georgian children
replayed a sentence type more exactly when it pronounces more, `playedMore_child_iff`, and a
measure orders the sentence types as their replays do exactly when J-μ exceeds J and μ and these
two are equal, `desiderata_iff`. For an account that gives μ and J-μ sentences one structure
neither measure does, `not_desiderata_covert`.

In a trial three objects are shown and the sentence says of two of them that they are on the
table. An end state is the set of objects on the table. It is accurate when it satisfies the
sentence exhaustified against the alternatives *o is on the table*, which holds of the two
mentioned objects alone, `accurate_iff`.

## Implementation notes

* The type-shifter of a conjunct is not a `Head`. No sentence type pronounces it, so counting it
  would add the same number to both measures for all sentence types with one structure.
* `Account.bareJ` is the pair of simplified structures the paper draws for the accounts of
  Szabolcsi and of Haslinger and colleagues, whose own analyses are not formalized. The sentence
  types are the paper's three, which leave out expressions with one μ.
* A difference is a printed p-value significant at .05, `PValue.Significant`, and its direction
  the sign of the printed estimate.
* An error is classified by the number of mentioned objects on the table, as the analysis script
  in the paper's supplementary materials classifies it. An end state with one mentioned object
  and the unmentioned one thus has only one of the mentioned objects.

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

open Data.Statistics MitrovicSauerland2016 Exhaustification

/-! ### The test sentences -/

namespace Sentence

/-- A sentence type pronounces J, the μ head of each conjunct, or all three heads. -/
def pronounced : Sentence → Finset Head
  | .j => {.j}
  | .mu => {.mu 0, .mu 1}
  | .jMu => Finset.univ

theorem pronounced_injective : Function.Injective pronounced := by decide

/-- One sentence type lies below another when the heads it pronounces are among the other's. -/
instance : PartialOrder Sentence := PartialOrder.lift pronounced pronounced_injective

instance : DecidableLE Sentence := fun s t ↦
  inferInstanceAs (Decidable (s.pronounced ⊆ t.pronounced))

instance : DecidableLT Sentence := decidableLTOfDecidableLE

/-- The heads a sentence type pronounces, as an order embedding. -/
def pronouncedEmbedding : Sentence ↪o Finset Head :=
  OrderEmbedding.ofMapLEIff pronounced fun _ _ ↦ Iff.rfl

@[simp] theorem coe_pronouncedEmbedding : ⇑pronouncedEmbedding = pronounced := rfl

theorem pronounced_strictMono : StrictMono pronounced := pronouncedEmbedding.strictMono

theorem lt_iff {s t : Sentence} : s < t ↔ s ≠ .jMu ∧ t = .jMu := by revert s t; decide

end Sentence

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

-- §4, (iii)
theorem muParticle_free_iff {l : Language} :
    (muParticle l).morph.kind = .free ↔ l = .hungarian := by
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

variable (a : Account) {s t : Sentence}

/-- Mitrović and Sauerland give every sentence type the whole structure, Fig. 2. -/
def universal : Account where
  underlying _ := Finset.univ
  pronounced_subset _ := Finset.subset_univ _

/-- The rival structures give J expressions J alone, and μ and J-μ expressions the whole
structure, Fig. 1. -/
def bareJ : Account where
  underlying
    | .j => {.j}
    | .mu | .jMu => Finset.univ
  pronounced_subset := by decide

/-- The complexity of a sentence type is the number of heads in its structure. -/
def complexity (s : Sentence) : ℕ := (a.underlying s).card

/-- The covert pieces of a sentence type are the heads of its structure it leaves unpronounced,
the Transparency Principle's measure of difficulty, (3). -/
def covert (s : Sentence) : ℕ := (a.underlying s \ s.pronounced).card

theorem card_pronounced_add_covert (s : Sentence) :
    s.pronounced.card + a.covert s = a.complexity s :=
  (add_comm _ _).trans (Finset.card_sdiff_add_card_eq_card (a.pronounced_subset s))

variable {a} in
theorem covert_lt_covert_of_lt (h : a.underlying s = a.underlying t) (hst : s < t) :
    a.covert t < a.covert s := by
  have hs := a.card_pronounced_add_covert s
  have ht := a.card_pronounced_add_covert t
  have := Finset.card_lt_card (Sentence.pronounced_strictMono hst)
  rw [complexity, h] at hs
  rw [complexity] at ht
  omega

/-- Among sentence types with one structure, one that pronounces more leaves fewer heads
covert. -/
theorem covert_strictAntiOn (U : Finset Head) : StrictAntiOn a.covert (a.underlying ⁻¹' {U}) :=
  fun _ hs _ ht ↦ covert_lt_covert_of_lt (hs.trans ht.symm)

end Account

/-! ### The predictions -/

-- (4)
theorem covert_universal_strictAnti : StrictAnti Account.universal.covert :=
  fun _ _ ↦ Account.covert_lt_covert_of_lt rfl

-- §4
theorem bareJ_prediction : Account.bareJ.complexity .j < Account.bareJ.complexity .jMu := by
  decide

-- §4
theorem bareJ_mu_opaque : Account.bareJ.covert .jMu < Account.bareJ.covert .mu :=
  Account.covert_lt_covert_of_lt rfl (by decide)

/-! ### The findings -/

-- Tables 1 and 2
theorem georgian_significant_iff (m : Measure) (e : Effect) :
    (lrt .georgian m e).p.Significant (1 / 20) ↔ m = .playedN ∨ e = .group := by
  revert m e; decide +kernel

-- Tables 4 and 5
theorem hungarian_significant_iff (m : Measure) (e : Effect) :
    (lrt .hungarian m e).p.Significant (1 / 20) ↔ m = .playedN ∧ e = .group := by
  revert m e; decide +kernel

/-- The two sentence types a follow-up contrast compares, in the paper's order. -/
def Contrast.sentences : Contrast → Sentence × Sentence
  | .jVsJMu => (.j, .jMu)
  | .jVsMu => (.j, .mu)
  | .jMuVsMu => (.jMu, .mu)

/-- A group replayed sentences of one type more than those of another when the contrast between
the two is significant at .05, in the direction of the estimate, which is negative when the first
was played less. Children replay the sentences they find difficult, so this is the order of
difficulty the data show. -/
def PlayedMore (g : Group) (s t : Sentence) : Prop :=
  ∃ c, (contrasts g c).p.Significant (1 / 20) ∧
    (c.sentences = (s, t) ∧ 0 < (contrasts g c).estimate.toRat ∨
      c.sentences = (t, s) ∧ (contrasts g c).estimate.toRat < 0)

instance (g : Group) : DecidableRel (PlayedMore g) := fun _ _ ↦
  inferInstanceAs (Decidable (∃ _, _ ∧ _))

/-- Georgian children replayed one sentence type more than another exactly when it pronounces
more: J-μ sentences more than J and than μ sentences, which did not differ. -/
theorem playedMore_child_iff (s t : Sentence) : PlayedMore .child s t ↔ t < s := by
  revert s t; decide +kernel

theorem not_playedMore_adult (s t : Sentence) : ¬ PlayedMore .adult s t := by
  revert s t; decide +kernel

-- §4
theorem covert_lt_covert_of_playedMore {a : Account} {s t : Sentence}
    (h : a.underlying s = a.underlying t) (hp : PlayedMore .child s t) :
    a.covert s < a.covert t :=
  Account.covert_lt_covert_of_lt h.symm ((playedMore_child_iff s t).1 hp)

/-! ### The conditions on a successful account -/

section Desiderata

variable {β : Type*}

/-- A measure of complexity meets the paper's conditions on a successful account when J-μ is more
complex than J and than μ, (i), and J and μ are equally complex, (ii). -/
structure Desiderata [Preorder β] (c : Sentence → β) : Prop where
  /-- (i): J-μ is more complex than J. -/
  j_lt_jMu : c .j < c .jMu
  /-- (i): J-μ is more complex than μ. -/
  mu_lt_jMu : c .mu < c .jMu
  /-- (ii): J and μ are equally complex. -/
  j_eq_mu : c .j = c .mu

theorem Desiderata.strictMono [Preorder β] {c : Sentence → β} (h : Desiderata c) :
    StrictMono c := fun s t hst ↦ by
  obtain ⟨hs, rfl⟩ := Sentence.lt_iff.1 hst
  cases s
  exacts [h.j_lt_jMu, h.mu_lt_jMu, absurd rfl hs]

/-- A measure meets the conditions exactly when it orders the sentence types as the Georgian
children's replays do. -/
theorem desiderata_iff [LinearOrder β] {c : Sentence → β} :
    Desiderata c ↔ ∀ s t, c s < c t ↔ PlayedMore .child t s := by
  simp only [playedMore_child_iff]
  refine ⟨fun h s t ↦ ⟨fun hst ↦ ?_, fun hst ↦ h.strictMono hst⟩, fun h ↦
    ⟨(h _ _).2 (by decide), (h _ _).2 (by decide),
      le_antisymm (not_lt.1 (mt (h _ _).1 (by decide))) (not_lt.1 (mt (h _ _).1 (by decide)))⟩⟩
  cases s <;> cases t <;>
    first
    | decide
    | exact (lt_irrefl _ hst).elim
    | exact (h.j_eq_mu.not_lt hst).elim
    | exact (h.j_eq_mu.not_gt hst).elim
    | exact (lt_asymm h.j_lt_jMu hst).elim
    | exact (lt_asymm h.mu_lt_jMu hst).elim

end Desiderata

-- §4
theorem not_desiderata_complexity (a : Account) (h : a.underlying .mu = a.underlying .jMu) :
    ¬ Desiderata a.complexity := fun hd ↦
  (congrArg Finset.card h).not_lt hd.mu_lt_jMu

/-- No account that gives μ and J-μ sentences one structure meets the conditions by the heads it
leaves covert: it makes μ sentences the harder of the two. -/
theorem not_desiderata_covert (a : Account) (h : a.underlying .mu = a.underlying .jMu) :
    ¬ Desiderata a.covert := fun hd ↦
  lt_asymm hd.mu_lt_jMu (Account.covert_lt_covert_of_lt h (by decide))

/-! ### The act-out task -/

section OnTable

variable {α : Type*}

/-- The proposition that an object is on the table, the alternative to the test sentence that
names it alone. -/
def onTable (o : α) : Set (Finset α) := {st | o ∈ st}

theorem exh_onTable (S : Finset α) : exh (Set.range onTable) {st | S ⊆ st} = {S} := by
  ext st
  rw [mem_exh_range_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨h, h'⟩
    exact Finset.Subset.antisymm (fun o ho ↦ h' o ho (Finset.Subset.refl S)) h
  · rintro rfl
    exact ⟨Finset.Subset.refl _, fun _ ho _ hst ↦ hst ho⟩

-- fn. 12
theorem exhIE_onTable (S : Finset α) : exhIE (Set.range onTable) {st | S ⊆ st} = {S} := by
  have h := exh_onTable S
  rw [exhIE_eq_exh_of_nonempty _ _ (h ▸ Set.singleton_nonempty S), h]

end OnTable

/-- A trial shows three objects, of which the test sentence mentions two. -/
abbrev Object := Fin objectsPerTrial

instance : NeZero objectsPerTrial := ⟨by decide⟩

/-- An end state of a trial is the set of objects on the table. -/
abbrev EndState := Finset Object

/-- The test sentence mentions the first two objects. -/
def mentioned : Finset Object := {0, 1}

/-- An end state meets the basic truth conditions of the test sentence when each mentioned object
is on the table. -/
def BasicTrue (st : EndState) : Prop := mentioned ⊆ st

instance : DecidablePred BasicTrue := fun st ↦ inferInstanceAs (Decidable (_ ⊆ st))

-- Fig. 2
theorem basicTrue_iff_conjunction {j : Coordinator} (hj : j.role = .conjunctive)
    (st : EndState) : BasicTrue st ↔
      j.denote {Quantifier.Det.every {(0 : Object)}, Quantifier.Det.every {1}}
        (st : Set Object) := by
  rw [conjunction_apply hj]; simp [BasicTrue, mentioned, Finset.insert_subset_iff]

/-- An end state is accurate when it matches the exhaustified sentence, the basic truth
conditions with every innocently excludable alternative naming one object denied. -/
def Accurate (st : EndState) : Prop := st ∈ exhIE (Set.range onTable) {st | BasicTrue st}

/-- The accurate end state has the mentioned objects and nothing else on the table. -/
theorem accurate_iff (st : EndState) : Accurate st ↔ st = mentioned := by
  simp only [Accurate, BasicTrue, exhIE_onTable, Set.mem_singleton_iff]

instance : DecidablePred Accurate := fun st ↦ decidable_of_iff' _ (accurate_iff st)

theorem Accurate.basicTrue {st : EndState} (h : Accurate st) : BasicTrue st :=
  exhIE_subset _ _ h

/-- The kind of an inaccurate end state by the number of mentioned objects on the table: neither,
only one, or both and so the unmentioned object with them. -/
def errorKind (st : EndState) : ErrorKind :=
  match (st ∩ mentioned).card with
  | 0 => .neitherMentioned
  | 1 => .oneMentioned
  | _ => .unmentioned

theorem errorKind_eq_unmentioned_iff {st : EndState} :
    errorKind st = .unmentioned ↔ BasicTrue st := by
  revert st; decide

-- fn. 12
theorem basicTrue_and_not_accurate_iff {st : EndState} :
    BasicTrue st ∧ ¬ Accurate st ↔ st = Finset.univ := by
  rw [accurate_iff]; revert st; decide

theorem errorKind_surjOn : Set.SurjOn errorKind {st | ¬ Accurate st} Set.univ := by
  rintro (_ | _ | _) -
  · exact ⟨Finset.univ, by decide, by decide⟩
  · exact ⟨{0}, by decide, by decide⟩
  · exact ⟨∅, by decide, by decide⟩

theorem countP_basicTrue (R : Multiset EndState) :
    R.countP BasicTrue =
      R.countP Accurate + R.countP fun st ↦ ¬ Accurate st ∧ errorKind st = .unmentioned := by
  rw [Multiset.countP_eq_countP_filter_add R BasicTrue Accurate, Multiset.countP_filter,
    Multiset.countP_filter]
  congr 1 <;> refine Multiset.countP_congr rfl fun st _ ↦ ?_
  · exact propext ⟨fun h ↦ h.2, fun h ↦ ⟨h.basicTrue, h⟩⟩
  · rw [errorKind_eq_unmentioned_iff, and_comm]

-- §3.1.2 and fn. 12: the responses that enter the replay analysis are the accurate ones and the
-- errors of the first kind.
theorem playedPoints_child :
    (playedPoints .child).count =
      (participants .georgian .child).count * (items - removedItems) - childErrors +
        (childErrorKinds .unmentioned).count := by
  decide

-- The error counts add up to the children's errors.
example : ∑ k, (childErrorKinds k).count = childErrors := by decide

-- The printed percentages round the counts.
example : ∀ k, (childErrorKinds k).percent.RoundsPercent (childErrorKinds k).count childErrors := by
  decide

end BillEtAl2025
