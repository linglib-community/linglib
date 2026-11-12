module

public import Linglib.Data.Examples.Wilder2013
public import Linglib.Semantics.Negation.Polarity
public import Linglib.Semantics.Focus.Control
public import Linglib.Semantics.Focus.Marking
public import Linglib.Discourse.QUD.Basic
public import Linglib.Data.Examples.Readers
public import Linglib.Syntax.Clause.Basic
public import Linglib.Fragments.English.Verbs.Attitude
public import Linglib.Fragments.English.Verbs.Levin
public import Linglib.Fragments.English.Complementizers
public import Linglib.Fragments.English.Pronouns
public import Linglib.Fragments.English.Particles

/-!
# Wilder (2013): English emphatic *do*

Emphatic *do* is the *do*-support forced by the polarity head Σ holding the affirmative morpheme,
so [emphatic assertion has the syntax of negation](##Clause.doSupport_negative_iff_positive). Its
emphasis is focus on Σ, which evokes [the polar question](##generate_polarityFocus), and a polar
question is not informative, so [any antecedent makes the clause Given](##given_polarityFocus) in
Schwarzschild's sense. A contrastive topic on such a sentence therefore indicates [a strategy of
polar questions](##ctValue_polarityFocus) in Büring's sense, and whatever its other foci the
sentence is [incongruent with a constituent question](##not_congruent_sigmaFocus). On these
grounds the account [fits every judgment](##checks_predicted) of the two sentence types.

## Implementation notes

* `Clause` keeps only the heads that decide Affix Hopping. An auxiliary in T stands for *have*,
  *be* or a modal, and Σ carries its polarity and whether it is F-marked.
* Givenness is Schwarzschild's at the propositional level, an antecedent entailing the existential
  F-closure, here the informative content of the question the focus alternatives generate. The
  existential type shifting of other constituents is not modelled.
* Congruence is Roberts's, equality of the focus alternatives with the answers. Rooth's
  containment admits a sentence whose further focus answers the constituent question, as the
  object focus of the paper's *Fred did eat the beans* does, so it cannot reject *do* there.
* Each row is linked to the fragment entries its sentence stands under: the embedding verb, the
  complementizer or interrogative word typing its clause, its context's interrogative word, and
  *yes*. Its clause type is derived from their fields, the sentence types a typer allows and the
  verb's factivity, and checked against [the paper's heading](##heading_derived); the linked
  forms are [checked against its words](##links_attested). Clefts, relatives, adverbial clauses
  and preposing are structural and name no entry.
* The account excludes a contrastive topic from interrogative clauses, with Büring, so it rejects
  an interrogative complement on two grounds, the paper citing only the Yes-answer one there.
* Wilder's star marks a sentence unacceptable with the intonation shown, and the rows record it
  as printed.

## TODO

* The Givenness of the unfocused subject and verb phrase, which with existential type shifting
  must find specific antecedents where the clause needs none, and the optionality of *do* in
  contrastive-topic sentences are not formalized.
* The example schema records no prosody, so the two patterns and the contrastive-topic
  constituent, which the paper defines by the printed contour, are still read off row labels.
* The contrast of *believe*-type with factive complements is Hooper and Thompson's assertive versus
  non-assertive embedding, read here off the fragment's factivity; the general clause API has no
  assertive embedding, its embedding contexts being those of interrogative embedding.

## References

* [wilder-2013]
* [laka-1990]
* [schwarzschild-1999]
* [buring-2003]
* [roberts-2012]
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

namespace Clause

/-- Affix Hopping attaches a stranded Tense affix to the adjacent overt verb when no Σ
intervenes, the subject has not intervened by inversion, and the verb is overt. -/
def AffixHopping (c : Clause) : Prop := c.sigma = none ∧ ¬c.inversion ∧ ¬c.emptyV

/-- *Do*-support arises when no auxiliary satisfies Tense and Affix Hopping is blocked. -/
def DoSupport (c : Clause) : Prop := ¬c.aux ∧ ¬c.AffixHopping

/-- A clause has polarity focus when Σ is present and F-marked. -/
def PolarityFocus (c : Clause) : Prop := ∃ s, c.sigma = some (s, .focused)

/-- Emphatic *do* is *do*-support motivated by none of the contexts of (1), negation, inversion
or an empty verb. -/
def EmphaticDo (c : Clause) : Prop :=
  c.DoSupport ∧ (∀ f, c.sigma ≠ some (.negative, f)) ∧ ¬c.inversion ∧ ¬c.emptyV

-- (4)
theorem doSupport_iff (c : Clause) :
    c.DoSupport ↔ ¬c.aux ∧ (c.sigma ≠ none ∨ c.inversion ∨ c.emptyV) := by
  simp only [DoSupport, AffixHopping]
  tauto

-- (4a-ii)
theorem emphaticDo_iff (c : Clause) :
    c.EmphaticDo ↔ ¬c.aux ∧ ¬c.inversion ∧ ¬c.emptyV ∧ ∃ f, c.sigma = some (.positive, f) := by
  obtain ⟨aux, sigma, inv, ev⟩ := c
  rcases sigma with _ | ⟨_ | _, f⟩ <;> simp [EmphaticDo, DoSupport, AffixHopping]

/-- With Σ present, *do*-support does not depend on its value, so emphatic assertion has the
syntax of negation (4a). -/
theorem doSupport_negative_iff_positive (c : Clause) (f f' : Mark) :
    DoSupport { c with sigma := some (.negative, f) } ↔
      DoSupport { c with sigma := some (.positive, f') } := by
  simp [doSupport_iff]

-- (5)
theorem not_doSupport_of_aux {c : Clause} (h : c.aux) : ¬c.DoSupport :=
  fun hd ↦ hd.1 h

-- p. 144: a clause with Affix Hopping has no Σ to focus.
theorem not_polarityFocus_of_affixHopping {c : Clause} (h : c.AffixHopping) :
    ¬c.PolarityFocus :=
  fun ⟨_, hs⟩ ↦ Option.some_ne_none _ (hs.symm.trans h.1)

-- (2c), p. 145: the syntax generates *do* under an affirmative Σ that is not F-marked, so the
-- unacceptability of *He did leave* is not syntactic.
theorem emphaticDo_and_not_polarityFocus :
    EmphaticDo ⟨false, some (.positive, .unfeatured), false, false⟩ ∧
      ¬PolarityFocus ⟨false, some (.positive, .unfeatured), false, false⟩ :=
  ⟨(emphaticDo_iff _).2 ⟨Bool.false_ne_true, Bool.false_ne_true, Bool.false_ne_true, _, rfl⟩,
    fun ⟨_, h⟩ ↦ nomatch h⟩

end Clause

/-! ### Focus on Σ -/

variable {W : Type*}

/-- An F-marked affirmative Σ over a clause meaning, whose alternatives are those of the clause
under each value of Σ (73). -/
def sigmaFocus (m : WithAlternatives (Set W)) : WithAlternatives (Set W) :=
  WithAlternatives.map₂ (· • ·) (.focused Polarity.positive) m

/-- Polarity focus, an F-marked Σ over a proposition with no other focus. -/
def polarityFocus (p : Set W) : WithAlternatives (Set W) := sigmaFocus (.unfeatured p)

@[simp] theorem polarityFocus_ordinary (p : Set W) : (polarityFocus p).ordinary = p := rfl

theorem polarityFocus_alternatives_eq_orbit (p : Set W) :
    (polarityFocus p).alternatives = MulAction.orbit Polarity p := by
  simp [polarityFocus, sigmaFocus, Set.image2_singleton_right, MulAction.orbit]

-- p. 153: the focus alternative set of an emphatic *do* sentence expressing `p` is `{p, ¬p}`.
theorem polarityFocus_alternatives (p : Set W) :
    (polarityFocus p).alternatives = {p, pᶜ} :=
  (polarityFocus_alternatives_eq_orbit p).trans (Polarity.orbit_eq_pair_compl p)

theorem polarityFocus_wellFormed (p : Set W) : (polarityFocus p).WellFormed :=
  (WithAlternatives.WellFormed.focused _).map₂ (WithAlternatives.WellFormed.unfeatured _)

-- p. 154: polarity focus evokes the polar question the sentence answers.
theorem generate_polarityFocus (p : Set W) :
    Question.generate (polarityFocus p).alternatives = Question.polar p := by
  rw [polarityFocus_alternatives_eq_orbit, Question.polar_eq_generate_orbit]

-- Focus on Σ adds the negation of each alternative of the clause.
theorem compl_mem_alternatives_sigmaFocus {m : WithAlternatives (Set W)} {a : Set W}
    (ha : a ∈ (sigmaFocus m).alternatives) : aᶜ ∈ (sigmaFocus m).alternatives := by
  obtain ⟨s, -, b, hb, rfl⟩ := ha
  exact ⟨Polarity.negative * s, trivial, b, hb,
    (mul_smul _ _ _).trans (Polarity.negative_smul_set _)⟩

theorem alternatives_subset_sigmaFocus (m : WithAlternatives (Set W)) :
    m.alternatives ⊆ (sigmaFocus m).alternatives :=
  fun a ha ↦ ⟨.positive, trivial, a, ha, Polarity.positive_smul a⟩

/-! ### Congruence -/

-- (59), (60)
theorem congruent_polarityFocus {p : Set W} (hne : p ≠ ∅) (hnu : p ≠ Set.univ) :
    Congruent (Question.polar p).alt (polarityFocus p).alternatives := by
  rw [Congruent, polarityFocus_alternatives_eq_orbit, Question.alt_polar_eq_orbit hne hnu]

/-- A sentence with emphatic *do* is incongruent with a constituent question one of whose answers
has a negation that is no answer, whatever its other foci: a contrastive-topic sentence directly
answering such a question rejects *do* ((113), (114)). -/
theorem not_congruent_sigmaFocus {Q : Question W} {a : Set W} (ha : a ∈ Q.alt)
    (hc : aᶜ ∉ Q.alt) (m : WithAlternatives (Set W)) :
    ¬ Congruent Q.alt (sigmaFocus m).alternatives := fun h ↦
  hc (h ▸ compl_mem_alternatives_sigmaFocus (h ▸ ha))

-- (113b), (114b): Rooth's containment admits emphatic *do* once another focus answers the
-- question, so it cannot reject *do* there.
theorem admits_sigmaFocus {q : Set (Set W)} {m : WithAlternatives (Set W)}
    (h : (Antecedent.question q).Admits m.alternatives) :
    (Antecedent.question q).Admits (sigmaFocus m).alternatives :=
  h.mono (alternatives_subset_sigmaFocus m)

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

/-! ### Givenness -/

/-- Givenness (70) at the propositional level holds when a salient antecedent entails the
existential F-closure (66), which is the informative content of the question the alternatives
generate. -/
def Given (a : Set W) (m : WithAlternatives (Set W)) : Prop :=
  a ⊆ (Question.generate m.alternatives).info

-- (72): the F-closure of a clause with one narrow focus says that some alternative to the focus
-- satisfies the rest of the clause.
theorem info_generate_map₂_focused {α β : Type*} (f : α → β → Set W) (x : α) (y : β) :
    (Question.generate (WithAlternatives.map₂ f (.focused x) (.unfeatured y)).alternatives).info =
      ⋃ x', f x' y := by
  simp [Question.info_generate, Set.image2_singleton_right, Set.sUnion_range]

-- (63): *John ate a green apple* makes *He ate a [red]F apple* Given, the antecedent being the
-- clause with an alternative in place of the focus.
theorem given_map₂_focused {α β : Type*} (f : α → β → Set W) (x x' : α) (y : β) :
    Given (f x' y) (WithAlternatives.map₂ f (.focused x) (.unfeatured y)) := by
  rw [Given, info_generate_map₂_focused]
  exact Set.subset_iUnion (f · y) x'

-- p. 157: a clause places no requirement on its antecedent exactly when the question its focus
-- evokes is not informative.
theorem forall_given_iff (m : WithAlternatives (Set W)) :
    (∀ a, Given a m) ↔ ¬ (Question.generate m.alternatives).IsInformative := by
  rw [Question.IsInformative, not_not]
  exact ⟨fun h ↦ Set.univ_subset_iff.1 (h _), fun h a ↦ (Set.subset_univ a).trans h.ge⟩

/-- Any salient antecedent makes a clause with polarity focus Given, so the antecedent of an
emphatic *do* sentence need not be its negation (p. 157). -/
theorem given_polarityFocus (a p : Set W) : Given a (polarityFocus p) :=
  (forall_given_iff _).2 (generate_polarityFocus p ▸ Question.not_isInformative_polar p) a

-- p. 156: without F on Σ, the negated antecedent (71a) does not make the clause (71b) Given.
theorem not_given_compl_of_unfeatured {p : Set W} (hp : p ≠ Set.univ) :
    ¬ Given pᶜ (WithAlternatives.map₂ (· • ·) (.unfeatured Polarity.positive) (.unfeatured p)) := by
  simpa [Given, Question.info_generate] using hp

/-! ### Contrastive topic and strategies -/

/-- [buring-2003]'s contrastive-topic value, as Wilder quotes its formation in footnote 28: for
each alternative `c` to the contrastive topic, the question generated by the focus alternatives of
the sentence with `c` in its place. -/
def ctValue {γ : Type*} (f : γ → WithAlternatives (Set W)) (cts : Set γ) : Set (Question W) :=
  (fun c ↦ Question.generate (f c).alternatives) '' cts

/-- A contrastive topic on a sentence whose only focus is on Σ indicates a strategy of polar
questions, so the question such a sentence directly answers in it is polar, Wilder's hypothesis
(112). -/
theorem ctValue_polarityFocus {γ : Type*} (P : γ → Set W) (cts : Set γ) :
    ctValue (fun c ↦ polarityFocus (P c)) cts = (fun c ↦ Question.polar (P c)) '' cts := by
  simp only [ctValue, generate_polarityFocus]

/-- The strategy the contrastive-topic verb phrase of (106) and (107) indicates asks whether he is
a good doctor, divided into whether he has a lot of patients, diagnoses well and treats his
patients politely. -/
def doctorStrategy (good patients diagnose polite : Set W) : Discourse.Strategy W :=
  .node (Question.polar good)
    [.leaf (Question.polar patients), .leaf (Question.polar diagnose),
      .leaf (Question.polar polite)]

-- (106), (107): the subquestions are the contrastive-topic value of the verb phrase.
theorem doctorStrategy_children (good patients diagnose polite : Set W) :
    {q | q ∈ (doctorStrategy good patients diagnose polite).children.map RoseTree.value} =
      ctValue polarityFocus {patients, diagnose, polite} := by
  ext q
  simp [doctorStrategy, RoseTree.leaf, ctValue, generate_polarityFocus]

-- p. 162: the strategy is complete when being a good doctor is determined by the three
-- subquestions, a Boolean combination of their propositions.
theorem doctorStrategy_isComplete {good patients diagnose polite : Set W}
    (h : good ∈ BooleanSubalgebra.closure {patients, diagnose, polite}) :
    (doctorStrategy good patients diagnose polite).IsComplete := by
  refine .node (fun _ ↦ ?_) (by simp)
  simp only [RoseTree.leaf, RoseTree.value_node, List.map_cons, List.map_nil, Multiset.inf_coe,
    List.foldr, inf_top_eq]
  refine Question.mem_determined.1 (BooleanSubalgebra.closure_le.2 (fun q hq ↦ ?_) h)
  rw [SetLike.mem_coe, Question.mem_determined]
  rcases hq with rfl | rfl | rfl
  exacts [inf_le_left, inf_le_right.trans inf_le_left, inf_le_right.trans inf_le_right]

example (patients diagnose polite : Set W) :
    (doctorStrategy (patients ∩ diagnose ∩ polite) patients diagnose polite).IsComplete :=
  doctorStrategy_isComplete <| BooleanSubalgebra.inf_mem
    (BooleanSubalgebra.inf_mem (BooleanSubalgebra.subset_closure (by simp))
      (BooleanSubalgebra.subset_closure (by simp)))
    (BooleanSubalgebra.subset_closure (by simp))

-- (24), p. 148: the implicature that he does not diagnose well answers the superquestion 'No'.
theorem not_good_of_not_diagnose {good patients diagnose polite : Set W}
    (h : good = patients ∩ diagnose ∩ polite) {σ : Set W} (hσ : σ ⊆ diagnoseᶜ) : σ ⊆ goodᶜ :=
  hσ.trans (Set.compl_subset_compl.mpr (h ▸ Set.inter_subset_left.trans Set.inter_subset_right))

/-! ### The two sentence types across clause types -/

/-- The constituent bearing the contrastive-topic accent. -/
inductive Constituent
  | subject | vp | object
  deriving DecidableEq, Repr

/-- The form of the question a contrastive-topic sentence directly answers. -/
inductive Answers
  | polar | constituent
  deriving DecidableEq, Repr

/-- The congruence emphatic *do* must meet in a sentence answering a question of the form: with
the polar question whether its proposition `p` holds, its only focus being Σ, or with a
constituent question `Q`, whatever the focus structure `m` under Σ. -/
def Answers.Congruent : Answers → Set W → WithAlternatives (Set W) → Question W → Prop
  | .polar, p, _, _ => Focus.Congruent (Question.polar p).alt (polarityFocus p).alternatives
  | .constituent, _, m, Q => Focus.Congruent Q.alt (sigmaFocus m).alternatives

-- Emphatic *do* is congruent with the question a sentence answers exactly when it is polar.
theorem Answers.congruent_iff (k : Answers) {p : Set W} (hne : p ≠ ∅) (hnu : p ≠ Set.univ)
    (m : WithAlternatives (Set W)) {Q : Question W} {a : Set W} (ha : a ∈ Q.alt)
    (hc : aᶜ ∉ Q.alt) : k.Congruent p m Q ↔ k = .polar := by
  cases k
  · simpa [Answers.Congruent] using congruent_polarityFocus hne hnu
  · simpa [Answers.Congruent] using not_congruent_sigmaFocus ha hc m

/-- An emphatic *do* sentence of a row: the Verum-focus pattern (46), named after [hohle-1992], or
the contrastive-topic pattern (47) with its marked constituent and the form of the question it
directly answers. -/
inductive Kind
  | vf
  | ct (k : Constituent) (a : Answers)
  deriving DecidableEq, Repr

/-! ### What a sentence stands in

Each row is linked to the fragment entries that embed or type its sentence: the verb whose
complement it is, the complementizer or interrogative word that types its clause, the interrogative
word of a constituent question its context asks, and the answer particle it opens with. The clause
types of sections 3.5 and 3.6 are derived from these, and the paper's heading for a row is a
target. -/

/-- What types a clause: a complementizer, or the interrogative word of a *wh*-clause. -/
inductive Typer
  | complementizer (c : Complementizer)
  | wh (w : InterrogativePronoun)

/-- The sentence types a typer allows: those its complementizer types, or the constituent
interrogative. -/
def Typer.types : Typer → Clause.Selection
  | .complementizer c => c.types
  | .wh _ => .only .constituent

/-- What a sentence stands in: a root clause with its interrogative word where it has one, a root
declarative with a preposed object, the complement of a verb with what types it, a cleft, a
restrictive relative, or an adverbial clause. -/
inductive Host
  | root (wh : Option InterrogativePronoun)
  | preposed
  | complement (v : English.Verbs.Verb) (t : Typer)
  | cleft | relative | adverbial

/-- The clause types of sections 3.5 and 3.6 as the account reads them: a root clause or an
interrogative complement with the sentence types of its clause, a declarative complement of a verb
that is not a full factive or of one that is, a cleft, a restrictive relative, an adverbial
clause, and a root declarative with a preposed object. -/
inductive Environment
  | root (s : Clause.Selection)
  | believeComplement | factiveComplement
  | interrogativeComplement (s : Clause.Selection)
  | itCleft | restrictiveRelative | adverbialClause | objectPreposing
  deriving DecidableEq

/-- The environment of a host: an interrogative word types a root clause as a constituent
question, a typer types a complement as interrogative or declarative, and a declarative
complement is factive when its verb is a full factive. -/
def Host.environment : Host → Environment
  | .root none => .root (.only .declarative)
  | .root (some _) => .root (.only .constituent)
  | .preposed => .objectPreposing
  | .complement v t =>
    if t.types.IsInterrogative then .interrogativeComplement t.types
    else if v.factivity = some .full then .factiveComplement else .believeComplement
  | .cleft => .itCleft
  | .relative => .restrictiveRelative
  | .adverbial => .adverbialClause

/-- The clause a sentence stands in is interrogative. -/
def Environment.IsInterrogative : Environment → Prop
  | .root s | .interrogativeComplement s => s.IsInterrogative
  | _ => False

instance : DecidablePred Environment.IsInterrogative := fun e ↦ by
  cases e <;> unfold Environment.IsInterrogative <;> infer_instance

/-- The clause type under which the paper gives a row: its headings for (27)–(33) and its
descriptions of the others. -/
inductive Heading
  | root | believeComplement | interrogativeComplement | factiveComplement | itCleft
  | restrictiveRelative | adverbialClause | whSubjectQuestion | objectPreposing
  deriving DecidableEq, Repr

/-- The paper's heading of an environment. -/
def Environment.heading : Environment → Heading
  | .root s => if s.IsInterrogative then .whSubjectQuestion else .root
  | .believeComplement => .believeComplement
  | .factiveComplement => .factiveComplement
  | .interrogativeComplement _ => .interrogativeComplement
  | .itCleft => .itCleft
  | .restrictiveRelative => .restrictiveRelative
  | .adverbialClause => .adverbialClause
  | .objectPreposing => .objectPreposing

/-- The heading a row records. -/
def heading? (ex : Datum) : Option Heading :=
  ex.parse? "environment" [("root", .root), ("believeComplement", .believeComplement),
    ("interrogativeComplement", .interrogativeComplement),
    ("factiveComplement", .factiveComplement), ("itCleft", .itCleft),
    ("restrictiveRelative", .restrictiveRelative), ("adverbialClause", .adverbialClause),
    ("whSubjectQuestion", .whSubjectQuestion), ("objectPreposing", .objectPreposing)]

/-- A row's link to the fragment: what its sentence stands in, the interrogative word of the
constituent question its context asks, and the answer particle it opens with. -/
structure Link where
  host : Host
  contextWh : Option InterrogativePronoun := none
  particle : Option Particle := none

namespace Host

open English

/-- The complement of a verb introduced by *that*. -/
def that (v : Verbs.Verb) : Host := .complement v (.complementizer Complementizers.that)

/-- The complement of a verb introduced by *if*. -/
def if_ (v : Verbs.Verb) : Host := .complement v (.complementizer Complementizers.if_)

/-- The complement of a verb typed by *which*. -/
def which (v : Verbs.Verb) : Host := .complement v (.wh Pronouns.which)

end Host

/-- A Yes-answer standing in the host. -/
def Link.yes (h : Host) : Link := { host := h, particle := some English.PolarityParticles.yes }

open English Examples in
/-- The rows with the items their sentences stand under. -/
def links : List (Datum × Link) :=
  [(ex10b, ⟨.root none, none, none⟩), (ex11b, ⟨.root none, none, none⟩),
    (ex12b, ⟨.root none, none, none⟩), (ex51, ⟨.root none, none, none⟩),
    (ex52, ⟨.root none, none, none⟩), (ex53, ⟨.root none, none, none⟩),
    (ex74b, ⟨.root none, none, none⟩),
    (ex27a, ⟨Host.that Verbs.believe, none, none⟩), (ex27b, ⟨Host.that Verbs.believe, none, none⟩),
    (ex27c, ⟨Host.that Verbs.believe, none, none⟩), (ex27d, ⟨Host.that Verbs.appear, none, none⟩),
    (ex27e, ⟨Host.that Verbs.appear, none, none⟩), (ex27f, ⟨Host.that Verbs.seem, none, none⟩),
    (ex28a, ⟨Host.if_ Verbs.wonder, none, none⟩), (ex28b, ⟨Host.if_ Verbs.wonder, none, none⟩),
    (ex28c, ⟨Host.if_ Verbs.know, none, none⟩), (ex28d, ⟨Host.which Verbs.ask, none, none⟩),
    (ex28e, ⟨Host.which Verbs.ask, none, none⟩),
    (ex29a, ⟨Host.that Verbs.resent, none, none⟩), (ex29b, ⟨Host.that Verbs.resent, none, none⟩),
    (ex29c, ⟨Host.that Verbs.resent, none, none⟩),
    (ex30a, ⟨.cleft, none, none⟩), (ex30b, ⟨.cleft, none, none⟩), (ex30c, ⟨.cleft, none, none⟩),
    (ex30d, ⟨.cleft, none, none⟩),
    (ex31a, ⟨.relative, none, none⟩), (ex31b, ⟨.relative, none, none⟩),
    (ex31c, ⟨.relative, none, none⟩), (ex31d, ⟨.relative, none, none⟩),
    (ex32a, ⟨.adverbial, none, none⟩), (ex32b, ⟨.adverbial, none, none⟩),
    (ex33a, ⟨.adverbial, none, none⟩), (ex33b, ⟨.adverbial, none, none⟩),
    (ex40b, ⟨.root (some Pronouns.which), none, none⟩),
    (ex41b, ⟨.root (some Pronouns.which), none, none⟩),
    (ex44b, ⟨.preposed, none, none⟩), (ex45b, ⟨.preposed, none, none⟩),
    (ex113b, ⟨.root none, some Pronouns.what, none⟩),
    (ex114b, ⟨.root none, some Pronouns.who, none⟩),
    (ex126a, Link.yes (Host.that Verbs.believe)), (ex126b, Link.yes (Host.that Verbs.appear)),
    (ex127a, Link.yes (Host.if_ Verbs.wonder)), (ex127b, Link.yes (Host.which Verbs.ask)),
    (ex127c, Link.yes (Host.that Verbs.resent)), (ex127d, Link.yes .cleft),
    (ex127e, Link.yes .relative),
    (ex127f, Link.yes .adverbial), (ex137c, Link.yes (.root none))]

/-- The link of a row. -/
def link? (ex : Datum) : Option Link := (links.find? (·.1.id = ex.id)).map (·.2)

-- Every row is linked, in the order of the data.
theorem links_ids : links.map (·.1.id) = Examples.all.map (·.id) := by decide

/-- The written forms of a typer: the morphs of a complementizer, or an interrogative word. -/
def Typer.forms : Typer → List String
  | .complementizer c => c.morphs.map (·.form)
  | .wh w => [w.form]

/-- The items a host names occur among the words: a morph of the verb begins a word and the forms
that type its complement are words, or the interrogative word of a root question is a word. -/
def Host.Attested : Host → List (List Char) → Prop
  | .root (some w), ws => w.form.toList ∈ ws
  | .complement v t, ws =>
    (∃ m ∈ v.morphs, ∃ x ∈ ws, m.form.toList <+: x) ∧ ∀ f ∈ t.forms, f.toList ∈ ws
  | _, _ => True

instance (h : Host) (ws : List (List Char)) : Decidable (h.Attested ws) := by
  rcases h with (_ | w) | _ | ⟨v, t⟩ | _ | _ | _ <;> unfold Host.Attested <;> infer_instance

/-- The items a link names occur in the row: those of its host and its answer particle in the
sentence, and the interrogative word of its context's question in the context. -/
def Link.Attested (l : Link) (ex : Datum) : Prop :=
  l.host.Attested (Datum.wordsOf ex.primaryText) ∧
    (∀ p ∈ l.particle, p.form.toList ∈ Datum.wordsOf ex.primaryText) ∧
    ∀ w ∈ l.contextWh, w.form.toList ∈ Datum.wordsOf ex.context

instance (l : Link) (ex : Datum) : Decidable (l.Attested ex) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

-- Each row's link is attested in its text, so a link to the wrong verb or typer fails.
theorem links_attested : ∀ p ∈ links, p.2.Attested p.1 := by decide +kernel

-- The clause type derived from a row's items is the paper's heading for it.
theorem heading_derived : ∀ p ∈ links, heading? p.1 = some p.2.host.environment.heading := by
  decide

/-- The sentence and environment of an emphatic *do* row: its pattern and contrastive-topic
constituent, the form of the question it answers by the interrogative word of its context, and
the environment its items derive. -/
def sentence? (ex : Datum) : Option (Kind × Environment) := do
  let l ← link? ex
  let a : Answers := if l.contextWh.isSome then .constituent else .polar
  let k := ex.parse? "ctConstituent" [("subject", .subject), ("vp", .vp), ("object", .object)]
  let kind ← match ex.feature? "pattern" with
    | some "VF" => some .vf
    | some "CT" => (Kind.ct · a) <$> k
    | _ => none
  return (kind, l.host.environment)

/-- The environment of a row that opens with *yes*, a Yes-answer to a polar question. -/
def yesAnswer? (ex : Datum) : Option Environment := do
  let l ← link? ex
  guard (l.particle = some English.PolarityParticles.yes)
  return l.host.environment

/-- The paper rejects a Yes-answer to a polar question in the environment, (127). -/
def RejectsYesAnswer (e : Environment) : Prop :=
  ∃ ex ∈ Examples.all, yesAnswer? ex = some e ∧ ex.judgment.band = .rejected

instance : DecidablePred RejectsYesAnswer := fun _ ↦
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- The account's judgment of a sentence in an environment. A Verum-focus sentence needs only a
salient antecedent (`given_polarityFocus`), so it is accepted everywhere (46c). A
contrastive-topic sentence must answer a polar question, emphatic *do* being incongruent with a
constituent question (`Answers.congruent_iff`); it must be declarative, a contrastive topic being
defined only there (section 6.1); it must not have a preposed object, whose contrastive topic
would indicate a second strategy (section 6.2); and it must stand where a Yes-answer can (125). -/
def predicted : Kind → Environment → Judgment.Band
  | .vf, _ => .accepted
  | .ct _ a, e =>
    .ofProp (a = .polar ∧ ¬e.IsInterrogative ∧ e ≠ .objectPreposing ∧ ¬RejectsYesAnswer e)

/-- The account fits every judgment of the two sentence types, the contrastive-topic sentences
accepted only as Yes-answers to a polar question may be, outside questions and object preposing
((27)–(45), (113), (114), (126), (127)). -/
theorem checks_predicted :
    Datum.Checks sentence? (fun s ↦ predicted s.1 s.2) Examples.all 39 := by
  decide

theorem readCount_yesAnswer : Datum.ReadCount yesAnswer? Examples.all 9 := by decide

end Wilder2013
