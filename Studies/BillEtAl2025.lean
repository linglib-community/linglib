module

public import Studies.MitrovicSauerland2016
public import Linglib.Data.Statistics.BillEtAl2025
public import Linglib.Data.Examples.BillEtAl2025
public import Linglib.Data.Examples.Gloss
public import Linglib.Languages.Georgian.Coordination
public import Linglib.Languages.Georgian.FocusParticles
public import Linglib.Languages.Hungarian.Coordination
public import Linglib.Languages.Hungarian.FocusParticles
public import Linglib.Semantics.Exhaustification.Disjunctive
public import Linglib.Morphology.Realization.Map
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Multiset.Filter

/-!
# Bill, Gonzalez, Driemel, Makharoblidze and Pintér (2025): Is DP conjunction always complex?

Georgian and Hungarian conjoin two noun phrases with a J particle alone, with a μ particle on each
conjunct, or with both. A sentence type `s` pronounces the set `s.pronounced` of the heads of
Mitrović and Sauerland's structure, J and a μ for each conjunct, and we order the sentence types
by inclusion of these sets: the J-μ type lies above the J and the μ type, which are incomparable.
The particle `exponent l h` pronounces the head `h` in the language `l`, and `exponence l` is the
realization in which a sentence type realizes each head it pronounces as that particle. Each of
the paper's examples realizes a sentence type of its language and each type has an example,
`exists_marked_eq_realize` and `exists_example_realizing`, with the particles written as their
language file entries say, `printed`. The J-μ type alone realizes every head,
`isDefective_transpose_exponence_iff`.

Each head's particle stands on a side of a conjunct, and the pattern of a sentence type is the
join of the patterns of the heads it pronounces. The J type is monosyndetic A co-B and the μ type
bisyndetic A-co B-co, two of the nine binary patterns with at most one coordinator on a
coordinand; the J-μ type is their join, `pattern_jMu`, with two coordinators on its second
conjunct, `card_pattern_le_one_iff`.

A structure for the conjunction is J over the two noun phrases or J over a μ phrase for each, and
an account gives each sentence type a structure, among whose heads are the heads it pronounces.
With a conjunctive J both structures denote *every* on the conjuncts,
`Structure.denote_eq_every`, and the accounts are two, differing in the structure of J
expressions, `Account.eq_universal_or_eq_bareJ`. We define two measures of difficulty on an
account `a`, the number `a.complexity s` of heads of the structure and the number `a.covert s` of
them that the sentence leaves unpronounced, the measure of the Transparency Principle. Where a
sentence type that pronounces more is no more complex, `a.covert` is strictly antitone,
`Account.covert_strictAntiOn`, and the J-μ type leaves no head covert on either account,
`Account.covert_jMu`.

A group replayed sentences of type `s` more than those of type `t`, `PlayedMore g s t`, when the
follow-up contrast between the two is significant at .05 in that direction. Georgian children
replayed a sentence type more exactly when it pronounces more, `playedMore_child_iff`, and a
measure orders the sentence types as their replays do exactly when J-μ exceeds J and μ and these
two are equal, `desiderata_iff`. Children replay the sentences they find difficult, so this is the
order of difficulty the data show. Neither measure meets the conditions on either account,
`not_desiderata_covert` and `not_desiderata_complexity`.

In a trial three objects are shown and the sentence says of two of them that they are on the
table. An end state is the set of objects on the table, so a noun phrase with quantifier `q` is
on the table at the end states `onTable q` of which `q` holds. The subject of the test sentence
denotes *every* on the mentioned objects on either account, `denote_mentioned`. An end state is
accurate when it satisfies the sentence
exhaustified against the alternatives *o is on the table*, which holds of the two mentioned
objects alone, `accurate_iff`, and it satisfies the sentence unexhaustified without being
accurate when every object is on the table, `subset_and_not_accurate_iff`.

## Implementation notes

* The type-shifter of a conjunct is not a `Head`. No sentence type pronounces it, so counting it
  would add the same number to both measures for all sentence types with one structure.
* The structures are the two simplified ones the paper draws, and `Account.bareJ` stands for the
  accounts of Szabolcsi and of Haslinger and colleagues, whose own analyses are not formalized.
  In the structure without μ phrases J coordinates the lifts of the noun phrases, since a
  coordinator denotes at the conjoinable types, and the collective reading of J is left out, as
  in the paper. The sentence types are the paper's three, which leave out expressions with one μ.
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

open Data.Statistics MitrovicSauerland2016 Exhaustification Quantifier

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

/-- The coordinator of a language file that a lexeme of the data is. -/
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

/-- The exponence of the heads in a test language: a sentence type realizes each head it
pronounces as the particle of that head, and the other heads as nothing. -/
def exponence (l : Language) : Morphology.Realization Head Sentence Coordinator :=
  .ofOption fun h s ↦ if h ∈ s.pronounced then some (exponent l h) else none

theorem isLicensed_exponence_iff {l : Language} {h : Head} {s : Sentence} :
    (exponence l).IsLicensed h s ↔ h ∈ s.pronounced := by
  revert l h s; decide

-- (4): the J-μ type alone realizes every head
theorem isDefective_transpose_exponence_iff {l : Language} {s : Sentence} :
    (exponence l).transpose.IsDefective s ↔ s ≠ .jMu := by
  revert l s; decide

/-- The particles a row marks as pronouncing a head. -/
def marked (e : Datum) (h : Head) : Finset Coordinator :=
  (e.spans.filterMap fun p ↦ (Examples.label? p).bind fun k ↦
    if k.head = h then (Examples.lexeme? p).map (·.coordinator) else none).toFinset

/-- A word is written as a coordinator when it is the coordinator's form, if that is a free word,
and when it ends in the form after other morphs, if it is bound. -/
def WrittenAs (w : GlossedWord) (c : Coordinator) : Prop :=
  if c.morph.kind = .free then w.wordform = c.morph.form.toList
  else 1 < w.morphs.length ∧ w.morphs.getLast? = some c.morph.form.toList

instance : DecidableRel WrittenAs := fun _ _ ↦ by unfold WrittenAs; infer_instance

-- (1), (2), (5), (6): each example realizes a sentence type of its language, marking for each
-- head the particle the type realizes it as
theorem exists_marked_eq_realize (l : Language) :
    ∀ e ∈ Examples.all, e.language = l.glottocode →
      ∃ s : Sentence, ∀ h, marked e h = (exponence l).realize h s := by
  revert l; decide

-- each sentence type of each language is realized by an example
theorem exists_example_realizing (l : Language) (s : Sentence) :
    ∃ e ∈ Examples.all, e.language = l.glottocode ∧
      ∀ h, marked e h = (exponence l).realize h s := by
  revert l s; decide

-- each marked word is written as the particle it names
theorem printed :
    ∀ e ∈ Examples.all, ∀ p ∈ e.spans, ∃ x ∈ Examples.lexeme? p,
      ∃ w ∈ (p.words e).head?, p.length = 1 ∧ WrittenAs w x.coordinator := by
  decide

-- the marked words are those the gloss line glosses J or MU
theorem exists_span_iff_glossed :
    ∀ e ∈ Examples.all, ∀ i < e.glossedWords.length, ∀ w ∈ e.glossedWords[i]?,
      (∃ s ∈ e.spans, s.start = i) ↔ "J".toList ∈ w.glosses ∨ "MU".toList ∈ w.glosses := by
  decide

/-! ### The patterns of the sentence types -/

/-- The coordinand and side at which the particle of a head stands in the test languages: J
before the second conjunct, the μ of a conjunct after it. -/
def headPattern : Head → Coordinator.Pattern
  | .j => ![∅, {.before}]
  | .mu i => fun k ↦ if k = i then {.after} else ∅

/-- The pattern of a sentence type, the join of the patterns of the heads it pronounces. -/
def Sentence.pattern (s : Sentence) : Coordinator.Pattern := s.pronounced.sup headPattern

theorem Sentence.pattern_mono : Monotone Sentence.pattern := fun _ _ h ↦ Finset.sup_mono h

-- (1a) and (2a): monosyndetic A co-B
theorem pattern_j : Sentence.j.pattern = ![∅, {.before}] := by decide

-- (1b) and (2b): bisyndetic A-co B-co
theorem pattern_mu : Sentence.mu.pattern = ![{.after}, {.after}] := by decide

-- (1c) and (2c)
theorem pattern_jMu : Sentence.jMu.pattern = Sentence.j.pattern ⊔ Sentence.mu.pattern := by
  decide

theorem syndesis_pattern (s : Sentence) : s.pattern.syndesis = s.pronounced.card := by
  cases s <;> decide

-- the J-μ type has two coordinators on its second conjunct
theorem card_pattern_le_one_iff {s : Sentence} : (∀ i, (s.pattern i).card ≤ 1) ↔ s ≠ .jMu := by
  revert s; decide

-- (2): the Georgian enclitic stands on the side `headPattern` gives μ
theorem side?_exponent_georgian_mu (i : Fin 2) :
    (exponent .georgian (.mu i)).morph.kind.side? = some .after := rfl

-- (1b) and (2b): the additive particle of each language stands on that side of its phrase
theorem headPattern_mu_self (l : Language) (i : Fin 2) :
    headPattern (.mu i) i = {(additiveParticle l).side} := by
  revert l i; decide

/-! ### Structures, accounts and their measures -/

/-- A structure for the conjunction of two noun phrases, Fig. 1. -/
inductive Structure where
  /-- J over the two noun phrases, Fig. 1a. -/
  | bare
  /-- J over a μ phrase for each noun phrase, Fig. 1b and Fig. 2. -/
  | mu
  deriving DecidableEq, Repr, Fintype

namespace Structure

variable {α : Type*}

/-- The heads of a structure. -/
def heads : Structure → Finset Head
  | .bare => {.j}
  | .mu => Finset.univ

/-- What a structure denotes on the conjuncts `a` and `b` with the junctor `j`, which coordinates
their lifts, or the μ phrases of their singletons. -/
def denote (j : Coordinator) (a b : α) : Structure → Quantifier α
  | .bare => j.denote {individual a, individual b}
  | .mu => j.denote {Det.every {a}, Det.every {b}}

/-- With a conjunctive junctor both structures denote *every* on the two conjuncts, so the
sentence types have the same truth conditions whichever structure an account gives them. -/
theorem denote_eq_every {j : Coordinator} (hj : j.role = .conjunctive) (a b : α)
    (t : Structure) : t.denote j a b = Det.every {a, b} := by
  cases t <;>
    simp only [denote, individual_eq_every, Coordinator.denote_of_conjunctive hj, sInf_pair,
      ← Det.every_union, Set.singleton_union]

end Structure

/-- An account assigns each sentence type its underlying structure, among whose heads are the
heads the sentence type pronounces. -/
@[ext] structure Account where
  /-- The structure underlying a sentence type. -/
  underlying : Sentence → Structure
  /-- A sentence type pronounces only heads of its structure. -/
  pronounced_subset : ∀ s, s.pronounced ⊆ (underlying s).heads

namespace Account

variable (a : Account) {s t : Sentence}

/-- The account of Mitrović and Sauerland, on which every sentence type has the structure with
μ phrases, Fig. 2. -/
def universal : Account where
  underlying _ := .mu
  pronounced_subset _ := Finset.subset_univ _

/-- The account of the rival structures, on which J expressions have the structure without μ
phrases and μ and J-μ expressions the one with them, Fig. 1. -/
def bareJ : Account where
  underlying
    | .j => .bare
    | .mu | .jMu => .mu
  pronounced_subset := by decide

theorem underlying_of_ne_j (hs : s ≠ .j) : a.underlying s = .mu := by
  have h := a.pronounced_subset s
  cases hu : a.underlying s
  · rw [hu] at h
    cases s <;> first | exact absurd rfl hs | exact absurd h (by decide)
  · rfl

-- Fig. 1: the accounts differ only in the structure of J expressions
theorem eq_universal_or_eq_bareJ : a = universal ∨ a = bareJ := by
  cases h : a.underlying .j
  · refine .inr (Account.ext (funext fun s ↦ ?_))
    cases s
    · exact h
    all_goals exact a.underlying_of_ne_j (by decide)
  · refine .inl (Account.ext (funext fun s ↦ ?_))
    cases s
    · exact h
    all_goals exact a.underlying_of_ne_j (by decide)

/-- The complexity of a sentence type is the number of heads in its structure. -/
def complexity (s : Sentence) : ℕ := (a.underlying s).heads.card

/-- The number of heads of its structure that a sentence type leaves unpronounced, the
Transparency Principle's measure of difficulty, (3). -/
def covert (s : Sentence) : ℕ := ((a.underlying s).heads \ s.pronounced).card

theorem covert_add_card_pronounced (s : Sentence) :
    a.covert s + s.pronounced.card = a.complexity s :=
  Finset.card_sdiff_add_card_eq_card (a.pronounced_subset s)

theorem complexity_mu : a.complexity .mu = a.complexity .jMu := by
  rw [complexity, complexity, a.underlying_of_ne_j (by decide), a.underlying_of_ne_j (by decide)]

@[simp] theorem covert_jMu : a.covert .jMu = 0 := by
  rw [covert, a.underlying_of_ne_j (by decide)]; decide

variable {a} in
theorem covert_lt_covert_of_lt (h : a.complexity t ≤ a.complexity s) (hst : s < t) :
    a.covert t < a.covert s := by
  have hs := a.covert_add_card_pronounced s
  have ht := a.covert_add_card_pronounced t
  have := Finset.card_lt_card (Sentence.pronounced_strictMono hst)
  omega

-- (3): where a sentence type that pronounces more is no more complex, it leaves fewer heads
-- covert
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
theorem not_desiderata_complexity (a : Account) : ¬ Desiderata a.complexity := fun hd ↦
  a.complexity_mu.not_lt hd.mu_lt_jMu

/-- No account meets the conditions by the heads it leaves covert: the J-μ type, which should be
the most complex, leaves none. -/
theorem not_desiderata_covert (a : Account) : ¬ Desiderata a.covert := fun hd ↦ by
  simpa using hd.mu_lt_jMu

/-! ### The act-out task -/

section OnTable

variable {α : Type*}

/-- The proposition that a noun phrase *is on the table*: the end states, sets of objects on the
table, of which its quantifier holds. -/
def onTable (q : Quantifier α) : Set (Finset α) := {st | q ↑st}

@[simp] theorem mem_onTable {q : Quantifier α} {st : Finset α} : st ∈ onTable q ↔ q ↑st := Iff.rfl

theorem mem_onTable_every {S st : Finset α} : st ∈ onTable (Det.every ↑S) ↔ S ⊆ st :=
  Finset.coe_subset

theorem onTable_every (S : Finset α) :
    onTable (Det.every ↑S) = ⋂ o ∈ S, onTable (individual o) := by
  ext st; simp [Det.every, individual, Set.subset_def]

variable [Fintype α]

theorem minterm_onTable (T : Finset α) :
    minterm Finset.univ (fun o ↦ onTable (individual o)) T = {T} := by
  ext st; simp [individual, Finset.ext_iff]

-- fn. 12
theorem exhIE_onTable_every (S : Finset α) :
    exhIE (Set.range fun o ↦ onTable (individual o)) (onTable (Det.every ↑S)) = {S} := by
  rw [← Set.image_univ, ← Finset.coe_univ, onTable_every,
    exhIE_image_biInter (Finset.subset_univ S) (by simp [minterm_onTable]), minterm_onTable]

end OnTable

/-- An object of a trial, one of the three shown. -/
abbrev Object := Fin objectsPerTrial

instance : NeZero objectsPerTrial := ⟨by decide⟩

/-- An end state of a trial is the set of objects on the table. -/
abbrev EndState := Finset Object

/-- The objects the test sentence mentions, the first two. -/
def mentioned : Finset Object := {0, 1}

-- Fig. 1 and Fig. 2
theorem denote_mentioned (a : Account) (l : Language) (s : Sentence) :
    (a.underlying s).denote (exponent l .j) (0 : Object) 1 = Det.every ↑mentioned := by
  rw [Structure.denote_eq_every (by cases l <;> rfl), mentioned, Finset.coe_pair]

/-- An end state is accurate when it matches the exhaustified sentence: the mentioned objects are
on the table, and every innocently excludable alternative naming one object is denied. -/
def Accurate (st : EndState) : Prop :=
  st ∈ exhIE (Set.range fun o ↦ onTable (individual o)) (onTable (Det.every ↑mentioned))

/-- The accurate end state has the mentioned objects and nothing else on the table. -/
theorem accurate_iff {st : EndState} : Accurate st ↔ st = mentioned := by
  rw [Accurate, exhIE_onTable_every, Set.mem_singleton_iff]

instance : DecidablePred Accurate := fun _ ↦ decidable_of_iff' _ accurate_iff

theorem Accurate.subset {st : EndState} (h : Accurate st) : mentioned ⊆ st :=
  mem_onTable_every.mp (exhIE_subset _ _ h)

/-- The kind of an end state by the number of mentioned objects on the table: neither, only one,
or both, which an inaccurate end state has with the unmentioned object. -/
def errorKind (st : EndState) : ErrorKind :=
  match (st ∩ mentioned).card with
  | 0 => .neitherMentioned
  | 1 => .oneMentioned
  | _ => .unmentioned

theorem errorKind_eq_unmentioned_iff {st : EndState} :
    errorKind st = .unmentioned ↔ mentioned ⊆ st := by
  revert st; decide

-- fn. 12
theorem subset_and_not_accurate_iff {st : EndState} :
    mentioned ⊆ st ∧ ¬ Accurate st ↔ st = Finset.univ := by
  rw [accurate_iff]; revert st; decide

theorem errorKind_surjOn : Set.SurjOn errorKind {st | ¬ Accurate st} Set.univ := by
  intro k _
  match k with
  | .unmentioned => exact ⟨Finset.univ, by decide, by decide⟩
  | .oneMentioned => exact ⟨{0}, by decide, by decide⟩
  | .neitherMentioned => exact ⟨∅, by decide, by decide⟩

theorem countP_subset (R : Multiset EndState) :
    R.countP (mentioned ⊆ ·) =
      R.countP Accurate + R.countP fun st ↦ ¬ Accurate st ∧ errorKind st = .unmentioned := by
  rw [Multiset.countP_eq_countP_filter_add R (mentioned ⊆ ·) Accurate, Multiset.countP_filter,
    Multiset.countP_filter]
  congr 1 <;> refine Multiset.countP_congr rfl fun st _ ↦ ?_
  · exact propext (and_iff_right_of_imp Accurate.subset)
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
