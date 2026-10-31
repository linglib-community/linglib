module

public import Linglib.Data.Examples.Wilder2013
public import Linglib.Semantics.Polarity.Basic
public import Linglib.Semantics.Focus.Control
public import Linglib.Semantics.Focus.Marking
public import Linglib.Discourse.QUD.Basic
public import Linglib.Data.Examples.Readers

/-!
# Wilder (2013): English emphatic *do*

On Wilder's analysis the auxiliary *do* appears wherever Affix Hopping cannot attach Tense to
the verb, and emphatic assertion is one such case: the
polarity head Σ of Laka holding the affirmative morpheme intervenes between Tense and the
verb just as negation does, so emphatic *do* has the syntax of *do*-support under negation. The
emphasis itself is focus on Σ, polarity focus, whose alternatives are the proposition and its
negation, the alternatives of the polar question the sentence answers. Under
Schwarzschild's Givenness the existential F-closure of a clause with F-marked Σ is a
tautology, so any salient antecedent makes the clause Given, and the requirement that the
antecedent be a negated or modalised version of the proposition falls on the unfocused subject
and verb phrase instead. Emphatic *do* sentences come in two types. A Verum-focus sentence has no
accent beyond focus accents and occurs in every finite clause type. A contrastive-topic sentence
has, on its subject, verb phrase or object, the fall-rise accent that Büring analyses as
indicating a strategy of questions, and it occurs only as a root declarative or a complement of
the *believe* type. Wilder derives the restriction from the hypothesis that a contrastive-topic
sentence with emphatic *do* directly answers a polar question of the strategy: such an answer can
be embedded under *believe* or *appear*, but not as an interrogative or factive complement, a
cleft, a relative or an adverbial clause, and a contrastive-topic sentence that answers a
constituent question rejects *do* altogether.

## Main definitions

* `Clause`, `AffixHopping`, `DoSupport`, `EmphaticDo`: the auxiliary system of section 2.
* `polarityFocus`: an F-marked Σ applied to the proposition, with its polarity alternatives.
* `existentialClosure`, `Given`: Schwarzschild's existential F-closure and Givenness.
* `DirectlyAnswersPolar`: the hypothesis (112) on the strategy a contrastive topic indicates.
* `Row`, `rows`: the paper's judgments on the two sentence types across clause types.

## Implementation notes

* `Clause` keeps only the heads of the clause structure (3) that decide Affix Hopping; an
  auxiliary in T stands for *have*, *be* or a modal, and Σ carries its polarity and whether it is
  F-marked. Wilder's claim that unfocused emphatic *do* is unacceptable rather than ungrammatical
  is not encoded.
* The contrastive-topic accent is recorded as a feature of an example row, not composed; the
  strategy it indicates is a `Discourse.Strategy`, and the hypothesis (112) is membership of the
  polar question among its nodes.
* The Yes-answer environments of (126) and (127) are rows like the emphatic *do* judgments, so
  `ct_acceptable_iff_hostsYesAnswer` compares two tables the paper gives independently. The
  wh-subject question and object preposing rows are outside that comparison: the paper explains
  them by the incompatibility of contrastive topic with questions and by a clash of strategies.

## TODO

* The optionality of *do* in contrastive-topic sentences (section 7) and the Givenness of the
  subject and verb phrase under composition (section 4.2) are not formalized; the latter is what
  the antecedents of section 4.1, an asserted, presupposed or modalised negation and the negation
  of a parallel predication, constrain.

## References

* [wilder-2013]
* [laka-1990]
* [schwarzschild-1999]
* [buring-2003]
* [hohle-1992]
* [roberts-2012]
-/

@[expose] public section

namespace Wilder2013

open Focus

/-! ### The auxiliary system -/

/-- These heads of the clause structure (3) decide whether Tense reaches the verb, namely an
auxiliary raising to T (*have*, *be*) or a modal in T, the polarity head Σ with its value and
whether it is F-marked, subject–auxiliary inversion, and an empty verb (ellipsis or VP fronting). -/
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

/-- Emphatic *do* is *do*-support forced by an affirmative Σ alone, as in (4a-ii). -/
theorem emphaticDo_iff (c : Clause) :
    EmphaticDo c ↔ ¬c.aux ∧ ¬c.inversion ∧ ¬c.emptyV ∧ ∃ f, c.sigma = some (.positive, f) := by
  obtain ⟨aux, sigma, inv, ev⟩ := c
  rcases sigma with _ | ⟨_ | _, f⟩ <;> simp [EmphaticDo, DoSupport, AffixHopping]

/-- The syntax of emphatic assertion is that of negation, since with Σ present *do*-support does
not depend on the value of Σ. -/
theorem doSupport_negative_iff_positive (c : Clause) (f f' : Mark) :
    DoSupport { c with sigma := some (.negative, f) } ↔
      DoSupport { c with sigma := some (.positive, f') } := by
  simp [doSupport_iff]

-- (5)
theorem not_doSupport_of_aux {c : Clause} (h : c.aux) : ¬DoSupport c :=
  fun hd ↦ hd.1 h

theorem not_polarityFocus_of_affixHopping {c : Clause} (h : AffixHopping c) :
    ¬PolarityFocus c := by
  rintro ⟨s, hs⟩
  rw [h.1] at hs
  cases hs

theorem emphaticDo_sigma {c : Clause} (h : EmphaticDo c) : ∃ f, c.sigma = some (.positive, f) :=
  ((emphaticDo_iff c).1 h).2.2.2

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

theorem polarityFocus_alternatives (p : Set W) :
    (polarityFocus p).alternatives = {p, pᶜ} :=
  (polarityFocus_alternatives_eq_orbit p).trans (Polarity.orbit_eq_pair_compl p)

theorem polarityFocus_wellFormed (p : Set W) : (polarityFocus p).WellFormed :=
  ((WithAlternatives.WellFormed.unfeatured _).mark _).map₂
    (WithAlternatives.WellFormed.unfeatured _)

/-- The alternative set of an emphatic *do* sentence is the meaning of the polar question it
answers (section 4.1). -/
theorem polarityFocus_alternatives_eq_alt_polar {p : Set W} (hne : p ≠ ∅) (hnu : p ≠ Set.univ) :
    (polarityFocus p).alternatives = (Question.polar p).alt :=
  (polarityFocus_alternatives_eq_orbit p).trans (Question.alt_polar_eq_orbit hne hnu).symm

-- (59), (60)
theorem question_admits_polarityFocus {p : Set W} (hne : p ≠ ∅) (hnu : p ≠ Set.univ) :
    (Antecedent.question (Question.polar p).alt).Admits (polarityFocus p).alternatives := by
  rw [polarityFocus_alternatives_eq_alt_polar hne hnu]
  exact subset_rfl

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

-- (73)
theorem existentialClosure_polarityFocus (p : Set W) :
    existentialClosure (polarityFocus p) = Set.univ := by
  rw [existentialClosure, polarityFocus_alternatives]
  simp

/-- Any salient antecedent makes a clause with polarity focus Given, so the requirement that the
antecedent be the negation falls on the unfocused subject and verb phrase, not on the clause. -/
theorem given_polarityFocus (a p : Set W) : Given a (polarityFocus p) := by
  rw [Given, existentialClosure_polarityFocus]
  exact Set.subset_univ a

-- (72)
theorem exists_not_given {m : WithAlternatives (Set W)} (h : existentialClosure m ≠ Set.univ) :
    ∃ a, ¬ Given a m :=
  ⟨Set.univ, fun h' ↦ h (Set.univ_subset_iff.mp h')⟩

/-! ### Contrastive topic and strategies -/

/-- Under hypothesis (112), a sentence with a contrastive topic and emphatic *do* directly answers
a polar question of the strategy the contrastive topic indicates, so the polar question is a node
of the strategy. -/
def DirectlyAnswersPolar (s : Discourse.Strategy W) (p : Set W) : Prop :=
  Question.polar p ∈ s.values

/-- The strategy the contrastive-topic verb phrase of (106) and (107) indicates asks whether he is
a good doctor, divided into whether he has a lot of patients, diagnoses well and treats his
patients politely. -/
def doctorStrategy (good patients diagnose polite : Set W) : Discourse.Strategy W :=
  .node (Question.polar good)
    [.leaf (Question.polar patients), .leaf (Question.polar diagnose),
      .leaf (Question.polar polite)]

theorem directlyAnswersPolar_doctorStrategy (good patients diagnose polite : Set W) :
    DirectlyAnswersPolar (doctorStrategy good patients diagnose polite) patients := by
  simp [DirectlyAnswersPolar, doctorStrategy, RoseTree.leaf]

/-- The strategy is complete when the three subquestions decide the superquestion, so that a
state that settles each of them settles whether he is a good doctor. -/
theorem doctorStrategy_isComplete {good patients diagnose polite : Set W}
    (h : good = patients ∩ diagnose ∩ polite) :
    (doctorStrategy good patients diagnose polite).IsComplete := by
  refine .node (fun _ ↦ ?_) (fun c hc ↦ ?_)
  · intro σ hσ
    simp only [List.map_cons, List.map_nil, RoseTree.value_node, RoseTree.leaf, Multiset.inf_coe,
      List.foldr, inf_top_eq, Question.mem_props, Question.mem_inf, Question.mem_polar] at hσ
    obtain ⟨ha, hb, hc⟩ := hσ
    rw [Question.mem_props, Question.mem_polar, h]
    rcases ha with ha | ha
    · rcases hb with hb | hb
      · rcases hc with hc | hc
        · exact Or.inl (Set.subset_inter (Set.subset_inter ha hb) hc)
        · exact Or.inr (hc.trans (Set.compl_subset_compl.mpr Set.inter_subset_right))
      · exact Or.inr (hb.trans (Set.compl_subset_compl.mpr
          (Set.inter_subset_left.trans Set.inter_subset_right)))
    · exact Or.inr (ha.trans (Set.compl_subset_compl.mpr
        (Set.inter_subset_left.trans Set.inter_subset_left)))
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with rfl | rfl | rfl <;> exact Discourse.Strategy.IsComplete.leaf _

-- (24)
theorem not_good_of_not_diagnose {good patients diagnose polite : Set W}
    (h : good = patients ∩ diagnose ∩ polite) {σ : Set W} (hσ : σ ⊆ diagnoseᶜ) : σ ⊆ goodᶜ :=
  hσ.trans (Set.compl_subset_compl.mpr (h ▸ Set.inter_subset_left.trans Set.inter_subset_right))

/-- By (113) and (114), a constituent question does not admit the polarity focus of an emphatic *do*
answer. -/
theorem not_admits_polarityFocus_of_constituentQuestion {Q : Question W} {p a : Set W}
    (ha : a ∈ Q.alt) (hp : a ≠ p) (hc : a ≠ pᶜ) :
    ¬ (Antecedent.question Q.alt).Admits (polarityFocus p).alternatives := by
  rw [Antecedent.Admits, Antecedent.contrastSet_question, polarityFocus_alternatives]
  intro h
  rcases h ha with rfl | rfl
  · exact hp rfl
  · exact hc rfl

/-! ### The two sentence types across clause types -/

/-- The constituent bearing the contrastive-topic accent. -/
inductive Constituent
  | subject | vp | object
  deriving DecidableEq, Repr

/-- A row judges one kind of sentence, the Verum-focus pattern (46), the contrastive-topic
pattern (47) with its marked constituent, a contrastive-topic sentence directly answering a
constituent question (113), (114), or a Yes-answer to a polar question (126), (127), (137). -/
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

structure Row where
  kind : Kind
  environment : Environment
  acceptable : Bool
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
  pure ⟨kind, environment, ex.judgment = .acceptable⟩

def rows : List Row := Examples.all.filterMap Row.ofDatum

theorem rows_length : rows.length = Examples.all.length := by decide

/-- The embedding environments of section 3.5, where the paper compares the two patterns. -/
def Environment.IsEmbedding : Environment → Prop
  | .whSubjectQuestion | .objectPreposing => False
  | _ => True

instance : DecidablePred Environment.IsEmbedding := fun e ↦ by
  cases e <;> simp only [Environment.IsEmbedding] <;> infer_instance

/-- An environment hosts a Yes-answer to a polar question when the paper judges one acceptable
in it, (126) and (137) against (127). -/
def HostsYesAnswer (e : Environment) : Prop :=
  ∃ r ∈ rows, r.kind = .yesAnswer ∧ r.environment = e ∧ r.acceptable

instance : DecidablePred HostsYesAnswer := fun _ ↦ by
  unfold HostsYesAnswer; infer_instance

-- (46c)
theorem vf_acceptable : ∀ r ∈ rows, r.kind = .vf → r.acceptable := by decide

/-- Across embedding environments, a contrastive-topic sentence with emphatic *do* is acceptable
exactly where a polar Yes-answer embeds, as (125) and (127) show. -/
theorem ct_acceptable_iff_hostsYesAnswer :
    ∀ r ∈ rows, r.kind.IsCT → r.environment.IsEmbedding →
      (r.acceptable ↔ HostsYesAnswer r.environment) := by
  decide

-- Section 6.1
theorem ct_not_whSubjectQuestion :
    ∀ r ∈ rows, r.kind.IsCT → r.environment = .whSubjectQuestion → ¬r.acceptable := by
  decide

-- Section 6.2
theorem ct_not_objectPreposing :
    ∀ r ∈ rows, r.kind.IsCT → r.environment = .objectPreposing → ¬r.acceptable := by
  decide

-- (113), (114)
theorem ctConstituentQuestion_unacceptable :
    ∀ r ∈ rows, r.kind.IsCTConstituentQuestion → ¬r.acceptable := by
  decide

end Wilder2013
