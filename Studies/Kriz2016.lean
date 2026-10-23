module

public import Linglib.Semantics.Homogeneity.Plural

/-!
# Križ (2016): Homogeneity, Non-Maximality, and All

Križ accounts for the non-maximal readings of definite plurals. *The professors smiled* is neither
true nor false when some but not all of them smiled, and the sentence is nonetheless usable there
whenever the current issue does not distinguish that situation from one in which all smiled; *all*
removes the gap and with it the non-maximal reading. A five-world model of three professors runs the
account end to end on the library's homogeneity substrate (`barePlural`, `allPlural`, both
originating with this paper): the non-maximal use under a coarse issue and its absence under a fine
one, the unusability of the *all*-sentence at any gap world, the unmentionability of exceptions
(`smith_exception_unaddressable`), and the paper's prediction that what an exception does instead
matters, since a visibly angry Smith falls into a different cell of the coarse issue than a neutral
one (`bare_usable_neutral_not_angry`). Conjunctions of names, modelled as plurals over their
conjuncts, are predicted to allow non-maximal readings they rarely have
(`conj_modeled_as_plural_predicts_nonmax`), which the paper answers with an accommodated finer
issue. For collective predicates §5.1 generalises the gap by overlap: a predicate is undefined of a
plurality that fails it but overlaps one that satisfies it, which on a distributive predicate is
supervaluation over the atoms (`generalisedTruthValue_distributive`).

## Implementation notes

* `Setoid W` is the substrate partition type, not Roberts's question stack: the
  paper's §4.5 argues that the current issue is an overarching property of the discourse that
  is not directly manipulable, so `coarseQ` and `fineQ` are constructions for the model.
* Following §4.4, the gap is trivalent but not presuppositional, contra Gajewski.
* The §4.5 puzzle of numerals (*the ten professors smiled* resists non-maximality) is left open,
  as in the paper, and so is the accommodation step of §6.2.

## References

* [kriz-2016]
* [kriz-2015] — the dissertation the account develops
* [lasersohn-1999], [kroch-1974] — pragmatic halos and the unmentionability of exceptions
* [szabolcsi-haddican-2004], [magri-2014] — the homogeneity of conjunctions
* [roberts-1996]
* [gajewski-2005]
-/

@[expose] public section

namespace Kriz2016

open Homogeneity

/-! ### Finite model

Three professors attend Sue's talk; the predicate is "smiled".

| World          | Smith | Jones | Lee | Bare plural | All   |
|----------------|-------|-------|-----|-------------|-------|
| allSmiled      | ✓     | ✓     | ✓   | TRUE        | true  |
| smithNeutral   | ✗     | ✓     | ✓   | GAP         | false |
| smithAngry     | ✗     | ✓     | ✓   | GAP         | false |
| onlyLeeSmiled  | ✗     | ✗     | ✓   | GAP         | false |
| noneSmiled     | ✗     | ✗     | ✗   | FALSE       | false |

`smithNeutral` and `smithAngry` agree on who smiled but differ in what Smith
does instead, which the coarse QUD ("Was the talk well-received?") is
sensitive to (§4.2); the fine QUD ("Did every professor smile?") separates
all worlds. -/

section FiniteModel

/-- Worlds of the five-world model. In both `smithNeutral` and `smithAngry`
    Smith fails to smile; the worlds differ in whether his demeanour is
    relevant to the coarse issue (§4.2). -/
inductive ProfWorld where
  | allSmiled
  | smithNeutral   -- Smith neutral expression (irrelevant exception)
  | smithAngry     -- Smith visibly angry (relevant exception per §4.2)
  | onlyLeeSmiled
  | noneSmiled
  deriving DecidableEq, Repr, Fintype

inductive Prof where
  | smith | jones | lee
  deriving DecidableEq, Repr, Fintype

/-- Which professor smiled in which world. -/
def smiled : Prof → ProfWorld → Prop
  | .smith, .allSmiled      => True
  | .smith, .smithNeutral   => False
  | .smith, .smithAngry     => False
  | .smith, .onlyLeeSmiled  => False
  | .smith, .noneSmiled     => False
  | .jones, .allSmiled      => True
  | .jones, .smithNeutral   => True
  | .jones, .smithAngry     => True
  | .jones, .onlyLeeSmiled  => False
  | .jones, .noneSmiled     => False
  | .lee,   .allSmiled      => True
  | .lee,   .smithNeutral   => True
  | .lee,   .smithAngry     => True
  | .lee,   .onlyLeeSmiled  => True
  | .lee,   .noneSmiled     => False

instance smiled.instDecidable : ∀ p w, Decidable (smiled p w) := by
  intro p w; cases p <;> cases w <;> unfold smiled <;> infer_instance

/-- All three professors. -/
def profs : Finset Prof := Finset.univ

/-- Reception grades for the coarse QUD — Smith's anger pulls reception down
    to `mixed`, his neutrality leaves it `positive` (§4.2). -/
inductive Reception where | positive | mixed | negative
  deriving DecidableEq

def receptionGrade : ProfWorld → Reception
  | .allSmiled => .positive
  | .smithNeutral => .positive
  | .smithAngry => .mixed       -- §4.2: Smith's anger is relevant
  | .onlyLeeSmiled => .mixed
  | .noneSmiled => .negative

/-- The coarse QUD asks "Was Sue's talk well-received?". -/
abbrev coarseQ : Setoid ProfWorld := Setoid.ker receptionGrade

/-- The fine QUD asks "Did every professor smile?". -/
abbrev fineQ : Setoid ProfWorld := ⊥

/-! #### Trivalent values at each world -/

theorem bare_allSmiled :
    barePlural smiled profs .allSmiled = 1 := by decide

theorem bare_smithNeutral :
    barePlural smiled profs .smithNeutral = 0 := by decide

theorem bare_onlyLeeSmiled :
    barePlural smiled profs .onlyLeeSmiled = 0 := by decide

theorem bare_noneSmiled :
    barePlural smiled profs .noneSmiled = -1 := by decide

/-! #### End-to-end predictions -/

theorem smithNeutral_usable_coarse :
    usable coarseQ (barePlural smiled profs) .smithNeutral := by decide

theorem smithNeutral_not_usable_fine :
    ¬usable fineQ (barePlural smiled profs) .smithNeutral := by decide

theorem all_not_usable_smithNeutral (q : Setoid ProfWorld)
    (h : usable q (allPlural smiled profs) .smithNeutral) : False :=
  absurd (allPlural_prevents_nonmax smiled profs q .smithNeutral h) (by decide)

theorem smith_exception_unmentionable (q : Setoid ProfWorld) (w : ProfWorld)
    (h : usable q (allPlural smiled profs) w) :
    smiled .smith w :=
  allPlural_exceptions_unmentionable smiled profs q w .smith (by decide) h

theorem coarse_communicates_gap :
    .smithNeutral ∈ communicatedContent coarseQ (barePlural smiled profs) :=
  ⟨.allSmiled, by decide, by decide⟩

theorem fine_does_not_communicate_gap :
    .smithNeutral ∉ communicatedContent fineQ (barePlural smiled profs) := by
  intro ⟨w', hEq, hTrue⟩
  revert hEq hTrue; cases w' <;> decide

/-! #### Unmentionability of exceptions (§4.1)

"#The professors smiled, but one of them didn't" is infelicitous even where
the non-maximal reading is licensed — the paper's (25a-b), with the
*although* diagnostic traced to [kroch-1974] via [lasersohn-1999]. The
derivation is pure Addressing (the substrate's `exception_unaddressable`):
non-maximal use requires a cell containing both a true-world and the
gap-world, and the exception-mentioning continuation straddles it. -/

/-- "Smith didn't smile", the exception-mentioning continuation. -/
def smithDidntSmile : (ProfWorld → SignType) :=
  fun w ↦ if smiled .smith w then -1 else 1

/-- Under the coarse issue licensing the non-maximal use at `smithNeutral`,
    "…but Smith didn't" cannot address the issue (§4.1). -/
theorem smith_exception_unaddressable :
    ¬ addressesIssue coarseQ smithDidntSmile :=
  exception_unaddressable coarseQ (barePlural smiled profs) smithDidntSmile
    .smithNeutral smithNeutral_usable_coarse (by decide) (by decide)

/-! #### What exceptions do (§4.2)

Whether an exception is tolerated depends on what it does instead: Smith
looking neutral is irrelevant to reception, Smith looking angry is not. The
model places `smithNeutral` and `smithAngry` in different `coarseQ` cells,
so the same sentence under the same QUD is usable at one gap-world and not
the other — a contrast unavailable to accounts without an issue parameter
(restricted reference, alternative geometry). -/

theorem bare_smithAngry :
    barePlural smiled profs .smithAngry = 0 := by decide

theorem bare_smithAngry_not_usable_coarse :
    ¬ usable coarseQ (barePlural smiled profs) .smithAngry := by decide

/-- The same sentence under the same QUD is usable at one gap-world and not at
    the other, the contrast of §4.2. -/
theorem bare_usable_neutral_not_angry :
    usable coarseQ (barePlural smiled profs) .smithNeutral ∧
    ¬ usable coarseQ (barePlural smiled profs) .smithAngry :=
  ⟨smithNeutral_usable_coarse, bare_smithAngry_not_usable_coarse⟩

end FiniteModel

/-! ### Conjunction overgeneration (§6.2)

Conjunctions of proper names are homogeneous ([szabolcsi-haddican-2004],
[magri-2014]) yet generally resist non-maximal readings. Modelled as a
plural over its conjunct atoms, the machinery predicts non-maximal use at a
gap-world (`conj_modeled_as_plural_predicts_nonmax`); the paper's informal
response is that mentioning an individual prompts accommodation of a finer
issue on which no non-maximal reading survives, an accommodation step not
formalized here or in the paper. -/

section ConjunctionOvergeneration

inductive ConjAtom where | bert | claire | dora
  deriving DecidableEq, Repr, Fintype

inductive ConjWorld where | allWent | dorasMissing | onlyBert | noneWent
  deriving DecidableEq, Repr, Fintype

def wentThere : ConjAtom → ConjWorld → Prop
  | .bert,   .allWent       => True
  | .bert,   .dorasMissing  => True
  | .bert,   .onlyBert      => True
  | .bert,   .noneWent      => False
  | .claire, .allWent       => True
  | .claire, .dorasMissing  => True
  | .claire, .onlyBert      => False
  | .claire, .noneWent      => False
  | .dora,   .allWent       => True
  | .dora,   .dorasMissing  => False
  | .dora,   .onlyBert      => False
  | .dora,   .noneWent      => False

instance wentThere.instDecidable : ∀ a w, Decidable (wentThere a w) := by
  intro a w; cases a <;> cases w <;> unfold wentThere <;> infer_instance

def threeCoworkers : Finset ConjAtom := Finset.univ

/-- Cells of the coarse "did anyone go?" issue. -/
inductive ConjPartition where | someWent | noneWent
  deriving DecidableEq

def someWentPartition : ConjWorld → ConjPartition
  | .allWent => .someWent
  | .dorasMissing => .someWent
  | .onlyBert => .someWent
  | .noneWent => .noneWent

abbrev coarseConjQ : Setoid ConjWorld := Setoid.ker someWentPartition

theorem conj_dorasMissing_gap :
    barePlural wentThere threeCoworkers .dorasMissing = 0 := by decide

theorem conj_modeled_as_plural_predicts_nonmax :
    usable coarseConjQ (barePlural wentThere threeCoworkers) .dorasMissing := by
  decide

end ConjunctionOvergeneration

/-! ### Generalised homogeneity (§5.1) -/

section Generalised

variable {Atom : Type*} [DecidableEq Atom]

/-- The generalised truth value of §5.1 is true where `P` holds of `a`, undefined where `a`
fails `P` but overlaps a plurality of `domain` that satisfies it, and false otherwise. -/
def generalisedTruthValue (P : Finset Atom → Prop) [DecidablePred P]
    (domain : Finset (Finset Atom)) (a : Finset Atom) : SignType :=
  if P a then 1 else if ∃ b ∈ domain, ¬ Disjoint a b ∧ P b then 0 else -1

theorem generalisedTruthValue_distributive (pred : Atom → Prop) [DecidablePred pred]
    {a : Finset Atom} (hne : a.Nonempty) {domain : Finset (Finset Atom)}
    (hdomain : ∀ x ∈ a, {x} ∈ domain) :
    generalisedTruthValue (fun s ↦ ∀ x ∈ s, pred x) domain a =
      SignType.supervaluation a pred := by
  obtain h | h | h := (SignType.supervaluation a pred).trichotomy <;> rw [h]
  · have hnone := ((SignType.supervaluation_eq_neg_one_iff ..).1 h).2
    obtain ⟨x, hx⟩ := hne
    rw [generalisedTruthValue, ite_eq_right fun hall ↦ hnone x hx (hall x hx), ite_eq_right]
    rintro ⟨b, -, hov, hPb⟩
    obtain ⟨y, hya, hyb⟩ := Finset.not_disjoint_iff.1 hov
    exact hnone y hya (hPb y hyb)
  · obtain ⟨⟨x, hxa, hpx⟩, y, hya, hpy⟩ := (SignType.supervaluation_eq_zero_iff ..).1 h
    rw [generalisedTruthValue, ite_eq_right fun hall ↦ hpy (hall y hya), ite_eq_left]
    exact ⟨{x}, hdomain x hxa, Finset.not_disjoint_iff.2 ⟨x, hxa, Finset.mem_singleton_self x⟩,
      fun z hz ↦ Finset.mem_singleton.1 hz ▸ hpx⟩
  · exact ite_eq_left ((SignType.supervaluation_eq_one_iff ..).1 h)

end Generalised

end Kriz2016
