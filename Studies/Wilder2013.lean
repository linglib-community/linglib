module

public import Linglib.Data.Examples.Wilder2013
public import Linglib.Semantics.Negation.Polarity
public import Linglib.Semantics.Focus.Control
public import Linglib.Semantics.Focus.Marking
public import Linglib.Discourse.QUD.Basic
public import Linglib.Data.Examples.Readers

/-!
# Wilder (2013): English emphatic *do*

Emphatic *do* is the *do*-support forced by the polarity head Σ holding the affirmative morpheme,
so [emphatic assertion has the syntax of negation](##doSupport_negative_iff_positive). The
emphasis is focus on Σ, whose alternatives are [the answers of a polar
question](##polarityFocus_alternatives_eq_alt_polar), and since $p \lor \lnot p$ is a tautology
[any antecedent makes the clause Given](##given_polarityFocus) in Schwarzschild's sense. A
sentence with a contrastive topic and emphatic *do* directly answers a polar question of the
strategy the topic indicates, so it [rejects a constituent
question](##not_admits_polarityFocus_of_constituentQuestion) and [embeds exactly where a
Yes-answer does](##ct_acceptable_iff_hostsYesAnswer).

## Implementation notes

* `Clause` keeps only the heads that decide Affix Hopping. An auxiliary in T stands for *have*,
  *be* or a modal, and Σ carries its polarity and whether it is F-marked.
* Givenness is Schwarzschild's at the propositional level, an antecedent entailing the existential
  F-closure, without the existential type shifting of other constituents.
* The contrastive-topic accent is recorded on an example row, not composed. The strategy it
  indicates is a `Discourse.Strategy`, a superquestion over its subquestions.
* The comparison of contrastive-topic sentences with Yes-answers runs over the environments where
  the paper judges a Yes-answer. It judges none in a *wh*-subject question or under object
  preposing, whose rejection of the contrastive topic it derives otherwise: Büring's restriction
  of contrastive topics to declaratives, and a clash between two indicated strategies.
* Wilder's star marks a sentence unacceptable with the intonation shown, and the rows record it
  as printed.

## TODO

* The Givenness of the unfocused subject and verb phrase, which with existential type shifting
  must find specific antecedents where the clause needs none, and the optionality of *do* in
  contrastive-topic sentences are not formalized.
* Büring's formation of the contrastive-topic value, from which the paper expects
  `DirectlyAnswersPolar` to follow, is not formalized; the strategies are given.

## References

* [wilder-2013]
* [laka-1990]
* [schwarzschild-1999]
* [buring-2003]
* [hohle-1992]
-/

@[expose] public section

namespace Wilder2013

open Focus

/-! ### The auxiliary system -/

/-- These heads of the clause structure (3) decide whether Tense reaches the verb, namely an
auxiliary raising to T (*have*, *be*) or a modal in T, the polarity head Σ of [laka-1990] with its
value and whether it is F-marked, subject–auxiliary inversion, and an empty verb (ellipsis or VP
fronting). -/
structure Clause where
  aux : Bool
  sigma : Option (Polarity × Mark)
  inversion : Bool
  emptyV : Bool
  deriving DecidableEq

/-- Affix Hopping attaches a stranded Tense affix to the adjacent overt verb when no Σ
intervenes, the subject has not intervened by inversion, and the verb is overt. -/
def AffixHopping (c : Clause) : Prop := c.sigma = none ∧ ¬c.inversion ∧ ¬c.emptyV

/-- *Do*-support arises when no auxiliary satisfies Tense and Affix Hopping is blocked. -/
def DoSupport (c : Clause) : Prop := ¬c.aux ∧ ¬AffixHopping c

/-- A clause has polarity focus when Σ is present and F-marked. -/
def PolarityFocus (c : Clause) : Prop := ∃ s, c.sigma = some (s, .focused)

/-- Emphatic *do* is *do*-support motivated by none of the contexts of (1), negation, inversion
or an empty verb. -/
def EmphaticDo (c : Clause) : Prop :=
  DoSupport c ∧ (∀ f, c.sigma ≠ some (.negative, f)) ∧ ¬c.inversion ∧ ¬c.emptyV

-- (4)
theorem doSupport_iff (c : Clause) :
    DoSupport c ↔ ¬c.aux ∧ (c.sigma ≠ none ∨ c.inversion ∨ c.emptyV) := by
  simp only [DoSupport, AffixHopping]
  tauto

-- (4a-ii)
theorem emphaticDo_iff (c : Clause) :
    EmphaticDo c ↔ ¬c.aux ∧ ¬c.inversion ∧ ¬c.emptyV ∧ ∃ f, c.sigma = some (.positive, f) := by
  obtain ⟨aux, sigma, inv, ev⟩ := c
  rcases sigma with _ | ⟨_ | _, f⟩ <;> simp [EmphaticDo, DoSupport, AffixHopping]

/-- With Σ present, *do*-support does not depend on its value, so emphatic assertion has the
syntax of negation (4a). -/
theorem doSupport_negative_iff_positive (c : Clause) (f f' : Mark) :
    DoSupport { c with sigma := some (.negative, f) } ↔
      DoSupport { c with sigma := some (.positive, f') } := by
  simp [doSupport_iff]

-- (5)
theorem not_doSupport_of_aux {c : Clause} (h : c.aux) : ¬DoSupport c :=
  fun hd ↦ hd.1 h

-- p. 144: a clause with Affix Hopping has no Σ to focus.
theorem not_polarityFocus_of_affixHopping {c : Clause} (h : AffixHopping c) :
    ¬PolarityFocus c :=
  fun ⟨_, hs⟩ ↦ Option.some_ne_none _ (hs.symm.trans h.1)

-- (2c), p. 145: the syntax generates *do* under an affirmative Σ that is not F-marked, so the
-- unacceptability of *He did leave* is not syntactic.
theorem emphaticDo_and_not_polarityFocus :
    EmphaticDo ⟨false, some (.positive, .unfeatured), false, false⟩ ∧
      ¬PolarityFocus ⟨false, some (.positive, .unfeatured), false, false⟩ :=
  ⟨(emphaticDo_iff _).2 ⟨Bool.false_ne_true, Bool.false_ne_true, Bool.false_ne_true, _, rfl⟩,
    fun ⟨_, h⟩ ↦ nomatch h⟩

/-! ### Polarity focus and Givenness -/

variable {W : Type*}

/-- Polarity focus is an affirmative Σ, F-marked, applied to the proposition of the clause, so
that each value of Σ, affirmation and negation, applies to it (73). -/
def polarityFocus (p : Set W) : WithAlternatives (Set W) :=
  WithAlternatives.map₂ (· • ·) ((WithAlternatives.unfeatured Polarity.positive).mark .focused)
    (WithAlternatives.unfeatured p)

@[simp] theorem polarityFocus_ordinary (p : Set W) : (polarityFocus p).ordinary = p := rfl

theorem polarityFocus_alternatives_eq_orbit (p : Set W) :
    (polarityFocus p).alternatives = MulAction.orbit Polarity p := by
  simp [polarityFocus, Set.image2_singleton_right, MulAction.orbit]

-- p. 153: the focus alternative set of an emphatic *do* sentence expressing `p` is `{p, ¬p}`.
theorem polarityFocus_alternatives (p : Set W) :
    (polarityFocus p).alternatives = {p, pᶜ} :=
  (polarityFocus_alternatives_eq_orbit p).trans (Polarity.orbit_eq_pair_compl p)

theorem polarityFocus_wellFormed (p : Set W) : (polarityFocus p).WellFormed :=
  ((WithAlternatives.WellFormed.unfeatured _).mark _).map₂
    (WithAlternatives.WellFormed.unfeatured _)

/-- The alternatives of an emphatic *do* sentence are the answers of the polar question it
answers (p. 154). -/
theorem polarityFocus_alternatives_eq_alt_polar {p : Set W} (hne : p ≠ ∅) (hnu : p ≠ Set.univ) :
    (polarityFocus p).alternatives = (Question.polar p).alt :=
  (polarityFocus_alternatives_eq_orbit p).trans (Question.alt_polar_eq_orbit hne hnu).symm

theorem admits_polarityFocus_iff {A : Set (Set W)} {p : Set W} :
    (Antecedent.question A).Admits (polarityFocus p).alternatives ↔ A ⊆ {p, pᶜ} := by
  rw [Antecedent.Admits, Antecedent.contrastSet_question, polarityFocus_alternatives]

-- (59), (60)
theorem question_admits_polarityFocus {p : Set W} (hne : p ≠ ∅) (hnu : p ≠ Set.univ) :
    (Antecedent.question (Question.polar p).alt).Admits (polarityFocus p).alternatives :=
  (polarityFocus_alternatives_eq_alt_polar hne hnu).superset

/-- A constituent question with an answer other than `p` and its negation does not admit the
polarity focus of an emphatic *do* answer, so a sentence directly answering one rejects *do*
((113), (114)). -/
theorem not_admits_polarityFocus_of_constituentQuestion {Q : Question W} {p a : Set W}
    (ha : a ∈ Q.alt) (hp : a ≠ p) (hc : a ≠ pᶜ) :
    ¬ (Antecedent.question Q.alt).Admits (polarityFocus p).alternatives :=
  fun h ↦ (admits_polarityFocus_iff.1 h ha).elim hp hc

-- (51)
theorem assertion_neg_resolves_polarityFocus {p : Set W} (hne : p ≠ ∅) :
    (Antecedent.assertion pᶜ).Resolves (polarityFocus p).ordinary
      (polarityFocus p).alternatives :=
  ⟨by simp [polarityFocus_alternatives], fun h ↦ hne (by simpa [h] using Set.inter_compl_self p)⟩

-- (57)
theorem not_assertion_self_resolves (p : Set W) :
    ¬ (Antecedent.assertion p).Resolves (polarityFocus p).ordinary
      (polarityFocus p).alternatives :=
  fun h ↦ h.2 rfl

/-- The existential F-closure (66) is the proposition that some alternative holds. -/
def existentialClosure (m : WithAlternatives (Set W)) : Set W := ⋃₀ m.alternatives

/-- Givenness (70) at the propositional level holds when a salient antecedent entails the
existential F-closure. -/
def Given (a : Set W) (m : WithAlternatives (Set W)) : Prop := a ⊆ existentialClosure m

-- (72): the F-closure of a clause with one narrow focus says that some alternative to the focus
-- satisfies the rest of the clause.
theorem existentialClosure_map₂_focused {α β : Type*} (f : α → β → Set W) (x : α) (y : β) :
    existentialClosure (WithAlternatives.map₂ f ((WithAlternatives.unfeatured x).mark .focused)
      (WithAlternatives.unfeatured y)) = ⋃ x', f x' y := by
  simp [existentialClosure, Set.image2_singleton_right, Set.sUnion_range]

-- (63): *John ate a green apple* makes *He ate a [red]F apple* Given, the antecedent being the
-- clause with an alternative in place of the focus.
theorem given_map₂_focused {α β : Type*} (f : α → β → Set W) (x x' : α) (y : β) :
    Given (f x' y) (WithAlternatives.map₂ f ((WithAlternatives.unfeatured x).mark .focused)
      (WithAlternatives.unfeatured y)) := by
  rw [Given, existentialClosure_map₂_focused]
  exact Set.subset_iUnion (f · y) x'

-- p. 157: a clause places no requirement on its antecedent exactly when its F-closure is a
-- tautology.
theorem forall_given_iff (m : WithAlternatives (Set W)) :
    (∀ a, Given a m) ↔ existentialClosure m = Set.univ :=
  ⟨fun h ↦ Set.univ_subset_iff.1 (h _), fun h a ↦ (Set.subset_univ a).trans h.ge⟩

-- (73)
theorem existentialClosure_polarityFocus (p : Set W) :
    existentialClosure (polarityFocus p) = Set.univ := by
  rw [existentialClosure, polarityFocus_alternatives]
  simp

/-- Any salient antecedent makes a clause with polarity focus Given, so the antecedent of an
emphatic *do* sentence need not be its negation (p. 157). -/
theorem given_polarityFocus (a p : Set W) : Given a (polarityFocus p) :=
  (forall_given_iff _).2 (existentialClosure_polarityFocus p) a

-- p. 156: without F on Σ, the negated antecedent (71a) does not make the clause (71b) Given.
theorem not_given_compl_of_unfeatured {p : Set W} (hp : p ≠ Set.univ) :
    ¬ Given pᶜ (WithAlternatives.map₂ (· • ·) (WithAlternatives.unfeatured Polarity.positive)
      (WithAlternatives.unfeatured p)) := by
  simpa [Given, existentialClosure] using hp

/-! ### Contrastive topic and strategies -/

/-- Under hypothesis (112), a sentence with a contrastive topic and emphatic *do* directly answers
a polar question of the strategy the contrastive topic indicates, one of the subquestions of the
superquestion the strategy addresses. -/
def DirectlyAnswersPolar (s : Discourse.Strategy W) (p : Set W) : Prop :=
  Question.polar p ∈ s.children.map RoseTree.value

/-- The strategy the contrastive-topic verb phrase of (106) and (107) indicates asks whether he is
a good doctor, divided into whether he has a lot of patients, diagnoses well and treats his
patients politely. -/
def doctorStrategy (good patients diagnose polite : Set W) : Discourse.Strategy W :=
  .node (Question.polar good)
    [.leaf (Question.polar patients), .leaf (Question.polar diagnose),
      .leaf (Question.polar polite)]

example (good patients diagnose polite : Set W) :
    DirectlyAnswersPolar (doctorStrategy good patients diagnose polite) patients := by
  simp [DirectlyAnswersPolar, doctorStrategy, RoseTree.leaf]

-- p. 162: the strategy is complete when the three subquestions decide the superquestion.
theorem doctorStrategy_isComplete {good patients diagnose polite : Set W}
    (h : good = patients ∩ diagnose ∩ polite) :
    (doctorStrategy good patients diagnose polite).IsComplete := by
  subst h
  refine .node (fun _ ↦ ?_) (by simp)
  simp only [RoseTree.leaf, RoseTree.value_node, List.map_cons, List.map_nil, Multiset.inf_coe,
    List.foldr, inf_top_eq]
  exact Question.le_polar_inter (Question.le_polar_inter inf_le_left
    (inf_le_right.trans inf_le_left)) (inf_le_right.trans inf_le_right)

-- (24), p. 148: the implicature that he does not diagnose well answers the superquestion 'No'.
theorem not_good_of_not_diagnose {good patients diagnose polite : Set W}
    (h : good = patients ∩ diagnose ∩ polite) {σ : Set W} (hσ : σ ⊆ diagnoseᶜ) : σ ⊆ goodᶜ :=
  hσ.trans (Set.compl_subset_compl.mpr (h ▸ Set.inter_subset_left.trans Set.inter_subset_right))

/-! ### The two sentence types across clause types -/

/-- The constituent bearing the contrastive-topic accent. -/
inductive Constituent
  | subject | vp | object
  deriving DecidableEq, Repr

/-- A row judges one kind of sentence, the Verum-focus pattern (46) named after [hohle-1992], the
contrastive-topic pattern (47) with its marked constituent, a contrastive-topic sentence directly
answering a constituent question (113), (114), or a Yes-answer to a polar question (126), (127),
(137). -/
inductive Kind
  | vf
  | ct (k : Constituent)
  | ctConstituentQuestion (k : Constituent)
  | yesAnswer
  deriving DecidableEq, Repr

/-- The contrastive-topic pattern (47). -/
def Kind.IsCT : Kind → Prop
  | .ct _ => True
  | _ => False

instance : DecidablePred Kind.IsCT := fun k ↦ by
  cases k <;> simp only [Kind.IsCT] <;> infer_instance

/-- A contrastive-topic sentence directly answering a constituent question. -/
def Kind.IsCTConstituentQuestion : Kind → Prop
  | .ctConstituentQuestion _ => True
  | _ => False

instance : DecidablePred Kind.IsCTConstituentQuestion := fun k ↦ by
  cases k <;> simp only [Kind.IsCTConstituentQuestion] <;> infer_instance

/-- The clause types of sections 3.5 and 3.6. -/
inductive Environment
  | root | believeComplement | interrogativeComplement | factiveComplement | itCleft
  | restrictiveRelative | adverbialClause | whSubjectQuestion | objectPreposing
  deriving DecidableEq, Repr

/-- A row's sentence kind, its environment, and the band of the paper's judgment of it. -/
structure Row where
  kind : Kind
  environment : Environment
  band : Judgment.Band
  deriving DecidableEq, Repr

def Row.ofDatum (ex : Datum) : Option Row := do
  let pattern ← ex.feature? "pattern"
  let kind ←
    if pattern = "VF" then some Kind.vf
    else if pattern = "yesAnswer" then some Kind.yesAnswer
    else do
      let k ← ex.parse? "ctConstituent"
        [("subject", Constituent.subject), ("vp", .vp), ("object", .object)]
      if pattern = "CT" then some (Kind.ct k)
      else if pattern = "CTwh" then some (Kind.ctConstituentQuestion k)
      else none
  let environment ← ex.parse? "environment" [("root", Environment.root),
    ("believeComplement", .believeComplement),
    ("interrogativeComplement", .interrogativeComplement),
    ("factiveComplement", .factiveComplement), ("itCleft", .itCleft),
    ("restrictiveRelative", .restrictiveRelative), ("adverbialClause", .adverbialClause),
    ("whSubjectQuestion", .whSubjectQuestion), ("objectPreposing", .objectPreposing)]
  pure ⟨kind, environment, ex.judgment.band⟩

def rows : List Row := Examples.all.filterMap Row.ofDatum

theorem rows_length : rows.length = Examples.all.length := by decide

/-- The paper judges a Yes-answer to a polar question in the environment. -/
def YesAnswerJudged (e : Environment) : Prop :=
  ∃ r ∈ rows, r.kind = .yesAnswer ∧ r.environment = e

instance : DecidablePred YesAnswerJudged := fun _ ↦ by
  unfold YesAnswerJudged; infer_instance

/-- An environment hosts a Yes-answer to a polar question when the paper judges one acceptable
in it, (126) and (137) against (127). -/
def HostsYesAnswer (e : Environment) : Prop :=
  ∃ r ∈ rows, r.kind = .yesAnswer ∧ r.environment = e ∧ r.band = .accepted

instance : DecidablePred HostsYesAnswer := fun _ ↦ by
  unfold HostsYesAnswer; infer_instance

-- (46c)
theorem vf_accepted : ∀ r ∈ rows, r.kind = .vf → r.band = .accepted := by decide

/-- Wherever the paper judges a Yes-answer, a contrastive-topic sentence with emphatic *do* is
acceptable exactly where the Yes-answer is: as a root declarative or under *believe* or
*appear*, and not in an interrogative or factive complement, a cleft, a relative or an adverbial
clause ((125)–(127)). -/
theorem ct_acceptable_iff_hostsYesAnswer :
    ∀ r ∈ rows, r.kind.IsCT → YesAnswerJudged r.environment →
      (r.band = .accepted ↔ HostsYesAnswer r.environment) := by
  decide

-- The comparison covers seven of the nine environments.
theorem yesAnswerJudged_iff (e : Environment) :
    YesAnswerJudged e ↔ e ≠ .whSubjectQuestion ∧ e ≠ .objectPreposing := by
  cases e <;> decide

-- Section 6.1
theorem ct_rejected_whSubjectQuestion :
    ∀ r ∈ rows, r.kind.IsCT → r.environment = .whSubjectQuestion → r.band = .rejected := by
  decide

-- Section 6.2
theorem ct_rejected_objectPreposing :
    ∀ r ∈ rows, r.kind.IsCT → r.environment = .objectPreposing → r.band = .rejected := by
  decide

-- (113), (114)
theorem ctConstituentQuestion_rejected :
    ∀ r ∈ rows, r.kind.IsCTConstituentQuestion → r.band = .rejected := by
  decide

end Wilder2013
