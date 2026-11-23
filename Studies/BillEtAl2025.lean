module

public import Studies.MitrovicSauerland2016
public import Linglib.Data.Statistics.BillEtAl2025
public import Linglib.Data.Examples.BillEtAl2025
public import Linglib.Data.Examples.Gloss
public import Linglib.Fragments.Georgian.Coordination
public import Linglib.Fragments.Georgian.FocusParticles
public import Linglib.Fragments.Hungarian.Coordination
public import Linglib.Fragments.Hungarian.FocusParticles
public import Linglib.Semantics.Exhaustification.InnocentExclusion
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Multiset.Filter

/-!
# Bill, Gonzalez, Driemel, Makharoblidze and Pintér (2025): Is DP conjunction always complex?

Georgian and Hungarian conjoin two noun phrases with a J particle alone, with a μ particle on each
conjunct, or with both. A sentence type `s` pronounces the set `s.pronounced` of the heads of
Mitrović and Sauerland's structure, J and a μ for each conjunct, and we order the sentence types
by inclusion of these sets: the J-μ type lies above the J and the μ type, which are incomparable.
The particle `exponent l h` pronounces the head `h` in the language `l`, and the paper's examples
of each language pronounce exactly these three sets of heads, each with the particles of the
Fragments written as their entries say, `toFinset_map_heads` and `printed`.

An account gives each sentence type the heads of its underlying structure, among which are the
heads it pronounces. We define two measures of difficulty on an account `a`, the number
`a.complexity s` of heads of the structure and the number `a.covert s` of them that the sentence
leaves unpronounced, the measure of the Transparency Principle. Where a sentence type that
pronounces more is no more complex, `a.covert` is strictly antitone,
`Account.covert_strictAntiOn`, and the J-μ type leaves no head covert on any account,
`Account.covert_jMu`.

A group replayed sentences of type `s` more than those of type `t`, `PlayedMore g s t`, when the
follow-up contrast between the two is significant at .05 in that direction. Georgian children
replayed a sentence type more exactly when it pronounces more, `playedMore_child_iff`, and a
measure orders the sentence types as their replays do exactly when J-μ exceeds J and μ and these
two are equal, `desiderata_iff`. Children replay the sentences they find difficult, so this is the
order of difficulty the data show. The measure `a.covert` meets the conditions for no account,
`not_desiderata_covert`, and `a.complexity` for none that gives μ and J-μ sentences one structure,
`not_desiderata_complexity`.

In a trial three objects are shown and the sentence says of two of them that they are on the
table. An end state is the set of objects on the table. It is accurate when it satisfies the
sentence exhaustified against the alternatives *o is on the table*, which holds of the two
mentioned objects alone, `accurate_iff`, and it satisfies the sentence unexhaustified without
being accurate when every object is on the table, `basicTrue_and_not_accurate_iff`.

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
* A row marks the words that pronounce a head, each with the head and the particle it is, and
  `exists_span_iff_glossed` checks the marks against the gloss line.

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

/-- The heads a sentence type pronounces: J, the μ head of each conjunct, or all three. -/
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

-- each sentence type pronounces heads in a way that Mitrović and Sauerland's examples attest
theorem pronounced_mem_attested (s : Sentence) : s.pronounced ∈ attested := by
  rw [mem_attested_iff]; cases s <;> decide

end Sentence

/-! ### The particles and the examples -/

/-- The particle of a test language that pronounces a head: J is Georgian *da* and Hungarian
*és*, μ is Georgian *-c* and Hungarian *is*. -/
def exponent : Language → Head → Coordinator
  | .georgian, .j => Georgian.Coordination.da
  | .georgian, .mu _ => Georgian.Coordination.c
  | .hungarian, .j => Hungarian.Coordination.es
  | .hungarian, .mu _ => Hungarian.Coordination.is_

/-- The additive particle of a test language, Georgian *-c* and Hungarian *is*. -/
def additiveParticle : Language → AdditiveParticle
  | .georgian => Georgian.FocusParticles.c
  | .hungarian => Hungarian.FocusParticles.is_

theorem exponent_isAlsoAdditive_iff (l : Language) (h : Head) :
    (exponent l h).IsAlsoAdditive (additiveParticle l) ↔ h ≠ .j := by
  revert l h; decide

-- §4, (iii)
theorem exponent_mu_free_iff (l : Language) (i : Fin 2) :
    (exponent l (.mu i)).morph.kind = .free ↔ l = .hungarian := by
  revert l i; decide

/-- The Glottocode of a test language. -/
def Language.glottocode : Language → Glottocode
  | .georgian => .georgian
  | .hungarian => .hungarian

/-- The coordinator of a fragment that a lexeme of the data is. -/
def Examples.Lexeme.coordinator : Examples.Lexeme → Coordinator
  | .da => Georgian.Coordination.da
  | .c => Georgian.Coordination.c
  | .es => Hungarian.Coordination.es
  | .is => Hungarian.Coordination.is_

/-- The head of the conjunction that a label of the data marks. -/
def Examples.SpanLabel.head : Examples.SpanLabel → Head
  | .j => .j
  | .muFirst => .mu 0
  | .muSecond => .mu 1

/-- The heads a row pronounces, those its marked words pronounce. -/
def heads (e : Datum) : Finset Head :=
  ((e.spans.filterMap Examples.label?).map (·.head)).toFinset

/-- A word is written as a coordinator when it is the coordinator's form, if that is a free word,
and when it ends in the form after other morphs, if it is bound. -/
def WrittenAs (w : GlossedWord) (c : Coordinator) : Prop :=
  if c.morph.kind = .free then w.wordform = c.morph.form.toList
  else 1 < w.morphs.length ∧ w.morphs.getLast? = some c.morph.form.toList

instance : DecidableRel WrittenAs := fun _ _ ↦ by unfold WrittenAs; infer_instance

-- (1), (2), (5), (6): each marked word names the particle of its language for the head it is
-- marked as, and is written as that particle
theorem printed (l : Language) :
    ∀ e ∈ Examples.all, e.language = l.glottocode → ∀ s ∈ e.spans,
      ∃ k ∈ Examples.label? s, ∃ x ∈ Examples.lexeme? s, x.coordinator = exponent l k.head ∧
        ∃ w ∈ (s.words e).head?, s.length = 1 ∧ WrittenAs w (exponent l k.head) := by
  revert l; decide

-- the marked words are those the gloss line glosses J or MU
theorem exists_span_iff_glossed :
    ∀ e ∈ Examples.all, ∀ i < e.glossedWords.length, ∀ w ∈ e.glossedWords[i]?,
      (∃ s ∈ e.spans, s.start = i) ↔ "J".toList ∈ w.glosses ∨ "MU".toList ∈ w.glosses := by
  decide

-- the examples of each language show the three sentence types
theorem toFinset_map_heads (l : Language) :
    ((Examples.all.filter (·.language = l.glottocode)).map heads).toFinset =
      Finset.univ.image Sentence.pronounced := by
  revert l; decide

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

/-- The account of Mitrović and Sauerland, on which every sentence type has the whole structure,
Fig. 2. -/
def universal : Account where
  underlying _ := Finset.univ
  pronounced_subset _ := Finset.subset_univ _

/-- The account of the rival structures, on which J expressions have J alone and μ and J-μ
expressions the whole structure, Fig. 1. -/
def bareJ : Account where
  underlying
    | .j => {.j}
    | .mu | .jMu => Finset.univ
  pronounced_subset := by decide

/-- The complexity of a sentence type is the number of heads in its structure. -/
def complexity (s : Sentence) : ℕ := (a.underlying s).card

/-- The number of heads of its structure that a sentence type leaves unpronounced, the
Transparency Principle's measure of difficulty, (3). -/
def covert (s : Sentence) : ℕ := (a.underlying s \ s.pronounced).card

theorem covert_add_card_pronounced (s : Sentence) :
    a.covert s + s.pronounced.card = a.complexity s :=
  Finset.card_sdiff_add_card_eq_card (a.pronounced_subset s)

theorem underlying_jMu : a.underlying .jMu = Finset.univ :=
  Finset.univ_subset_iff.mp (a.pronounced_subset .jMu)

@[simp] theorem covert_jMu : a.covert .jMu = 0 :=
  Finset.card_eq_zero.mpr (Finset.sdiff_eq_empty_iff_subset.mpr (Finset.subset_univ _))

variable {a} in
theorem covert_lt_covert_of_lt (h : a.complexity t ≤ a.complexity s) (hst : s < t) :
    a.covert t < a.covert s := by
  have hs := a.covert_add_card_pronounced s
  have ht := a.covert_add_card_pronounced t
  have := Finset.card_lt_card (Sentence.pronounced_strictMono hst)
  omega

/-- Where a sentence type that pronounces more is no more complex, it leaves fewer heads
covert. -/
theorem covert_strictAntiOn {S : Set Sentence} (h : AntitoneOn a.complexity S) :
    StrictAntiOn a.covert S :=
  fun _ hs _ ht hst ↦ covert_lt_covert_of_lt (h hs ht hst.le) hst

-- §4
theorem complexity_bareJ_j_lt_jMu : bareJ.complexity .j < bareJ.complexity .jMu := by decide

-- §4
theorem covert_bareJ_jMu_lt_mu : bareJ.covert .jMu < bareJ.covert .mu :=
  covert_lt_covert_of_lt le_rfl (by decide)

end Account

/-! ### The predictions -/

-- (4)
theorem covert_universal_strictAnti : StrictAnti Account.universal.covert :=
  fun _ _ ↦ Account.covert_lt_covert_of_lt le_rfl

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

/-- A group of the Georgian experiment replayed sentences of one type more than those of another
when the contrast between the two is significant at .05, in the direction of the estimate, which
is negative when the first was played less. -/
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
    (h : a.complexity s ≤ a.complexity t) (hp : PlayedMore .child s t) :
    a.covert s < a.covert t :=
  Account.covert_lt_covert_of_lt h ((playedMore_child_iff s t).mp hp)

/-! ### The conditions on a successful account -/

section Desiderata

variable {β : Type*} {c : Sentence → β}

/-- A measure of complexity meets the first two of the paper's conditions on a successful account
when J-μ is more complex than J and than μ, (i), and J and μ are equally complex, (ii). -/
structure Desiderata [Preorder β] (c : Sentence → β) : Prop where
  /-- (i): J-μ is more complex than J. -/
  j_lt_jMu : c .j < c .jMu
  /-- (i): J-μ is more complex than μ. -/
  mu_lt_jMu : c .mu < c .jMu
  /-- (ii): J and μ are equally complex. -/
  j_eq_mu : c .j = c .mu

theorem Desiderata.strictMono [Preorder β] (h : Desiderata c) : StrictMono c := fun s t hst ↦ by
  obtain ⟨hs, rfl⟩ := Sentence.lt_iff.mp hst
  cases s
  exacts [h.j_lt_jMu, h.mu_lt_jMu, absurd rfl hs]

theorem desiderata_iff_strictMono_and_eq [Preorder β] :
    Desiderata c ↔ StrictMono c ∧ c .j = c .mu :=
  ⟨fun h ↦ ⟨h.strictMono, h.j_eq_mu⟩, fun ⟨h, he⟩ ↦ ⟨h (by decide), h (by decide), he⟩⟩

theorem Desiderata.lt_iff_lt [Preorder β] (h : Desiderata c) {s t : Sentence} :
    c s < c t ↔ s < t := by
  refine ⟨fun hst ↦ ?_, fun hst ↦ h.strictMono hst⟩
  obtain ⟨hj, hm, he⟩ := h
  cases s <;> cases t <;>
    first
    | decide
    | exact (lt_irrefl _ hst).elim
    | exact (he.not_lt hst).elim
    | exact (he.not_gt hst).elim
    | exact (lt_asymm hj hst).elim
    | exact (lt_asymm hm hst).elim

theorem desiderata_iff_forall_lt_iff_lt [LinearOrder β] :
    Desiderata c ↔ ∀ s t, c s < c t ↔ s < t :=
  ⟨fun h _ _ ↦ h.lt_iff_lt, fun h ↦ ⟨(h _ _).mpr (by decide), (h _ _).mpr (by decide),
    le_antisymm (not_lt.mp (mt (h _ _).mp (by decide)))
      (not_lt.mp (mt (h _ _).mp (by decide)))⟩⟩

/-- A measure meets the conditions exactly when it orders the sentence types as the Georgian
children's replays do. -/
theorem desiderata_iff [LinearOrder β] :
    Desiderata c ↔ ∀ s t, c s < c t ↔ PlayedMore .child t s := by
  simp_rw [playedMore_child_iff, desiderata_iff_forall_lt_iff_lt]

end Desiderata

-- §4
theorem not_desiderata_complexity (a : Account) (h : a.underlying .mu = a.underlying .jMu) :
    ¬ Desiderata a.complexity := fun hd ↦ (congrArg Finset.card h).not_lt hd.mu_lt_jMu

/-- No account meets the conditions by the heads it leaves covert: the J-μ type, which should be
the most complex, leaves none. -/
theorem not_desiderata_covert (a : Account) : ¬ Desiderata a.covert := fun hd ↦ by
  simpa using hd.mu_lt_jMu

/-! ### The act-out task -/

section OnTable

variable {α : Type*}

/-- The proposition that an object is on the table, the alternative to the test sentence that
names it alone. -/
def onTable (o : α) : Set (Finset α) := {st | o ∈ st}

@[simp] theorem mem_onTable {o : α} {st : Finset α} : st ∈ onTable o ↔ o ∈ st := Iff.rfl

theorem exh_range_onTable (S : Finset α) : exh (Set.range onTable) {st | S ⊆ st} = {S} := by
  ext st
  rw [mem_exh_range_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨h, h'⟩
    exact Finset.Subset.antisymm (fun o ho ↦ h' o ho (Finset.Subset.refl S)) h
  · rintro rfl
    exact ⟨Finset.Subset.refl _, fun _ ho _ hst ↦ hst ho⟩

-- fn. 12
theorem exhIE_range_onTable (S : Finset α) : exhIE (Set.range onTable) {st | S ⊆ st} = {S} := by
  have h := exh_range_onTable S
  rw [exhIE_eq_exh_of_nonempty _ _ (h ▸ Set.singleton_nonempty S), h]

end OnTable

/-- An object of a trial, one of the three shown. -/
abbrev Object := Fin objectsPerTrial

instance : NeZero objectsPerTrial := ⟨by decide⟩

/-- An end state of a trial is the set of objects on the table. -/
abbrev EndState := Finset Object

/-- The objects the test sentence mentions, the first two. -/
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
def Accurate (st : EndState) : Prop := st ∈ exhIE (Set.range onTable) {st' | BasicTrue st'}

/-- The accurate end state has the mentioned objects and nothing else on the table. -/
theorem accurate_iff (st : EndState) : Accurate st ↔ st = mentioned := by
  simp only [Accurate, BasicTrue, exhIE_range_onTable, Set.mem_singleton_iff]

instance : DecidablePred Accurate := fun st ↦ decidable_of_iff' _ (accurate_iff st)

theorem Accurate.basicTrue {st : EndState} (h : Accurate st) : BasicTrue st :=
  exhIE_subset _ _ h

/-- The kind of an end state by the number of mentioned objects on the table: neither, only one,
or both, which an inaccurate end state has with the unmentioned object. -/
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
  intro k _
  match k with
  | .unmentioned => exact ⟨Finset.univ, by decide, by decide⟩
  | .oneMentioned => exact ⟨{0}, by decide, by decide⟩
  | .neitherMentioned => exact ⟨∅, by decide, by decide⟩

theorem countP_basicTrue (R : Multiset EndState) :
    R.countP BasicTrue =
      R.countP Accurate + R.countP fun st ↦ ¬ Accurate st ∧ errorKind st = .unmentioned := by
  rw [Multiset.countP_eq_countP_filter_add R BasicTrue Accurate, Multiset.countP_filter,
    Multiset.countP_filter]
  congr 1 <;> refine Multiset.countP_congr rfl fun st _ ↦ ?_
  · exact propext (and_iff_right_of_imp Accurate.basicTrue)
  · rw [errorKind_eq_unmentioned_iff, and_comm]

-- §3.1.2 and fn. 12: the responses that enter the replay analysis are the accurate ones and the
-- errors of the first kind.
theorem count_playedPoints_child :
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
