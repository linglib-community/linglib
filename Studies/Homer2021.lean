module

public import Linglib.Semantics.Polarity.Environment
public import Linglib.Data.Examples.Homer2021
public import Studies.Chierchia2004

/-!
# Homer (2021): Domains of polarity items

This file formalizes the localist, environment-based theory of polarity items: an item is
evaluated in its domains, the constituents containing it and the polarity head of their own
clause, and a negative polarity item is acceptable only if some domain is downward entailing with
respect to it, a positive one only if some domain is not. A second downward-entailing expression in
a domain undoes the first, so [*quoi que ce soit* is anti-licensed under *pas impossible* and
licensed again by a negation in its own clause](##Homer2021.flipFlop_npi), and [*some* is
anti-licensed under clausemate negation, rescued by a superordinate *impossible* and anti-licensed
again under *not impossible*](##Homer2021.flipFlop_ppi). [*Some* survives three
downward-entailing expressions](##Homer2021.localist_ppi) in a sentence downward entailing with
respect to it, since a smaller domain is not. A scalar implicature can [make a domain
non-monotone](##Homer2021.not_monotone_notConn_conj): [*any* is anti-licensed and *some* licensed
under *not … and*, but not under *not … or*](##Homer2021.disruption).

## Implementation notes

* The paper states its conditions as necessary ones. For sentences with one polarity item they are
  read here as biconditionals, as the paper does when it predicts which of them are acceptable.
* A world records a fact independent of the polarity item and which of two things the subject did.
  The environment of a domain is a function of the restrictor of the indefinite, a set of things,
  as in the paper's comparison of *things* with *simple things*, rather than of the item's full
  meaning.
* Each clause contributes its polarity phrase, whose head is the layer of the minimal domain, and
  its TP and, when embedded, CP, which are identity layers. A superordinate polarity phrase
  composes its polarity head with the predicate below it.
* The modals quantify over a fixed modal base in which the subject did the first thing. Over every
  world, *it is impossible that Jean didn't do something* would be false whatever the restrictor,
  and a constant environment is downward entailing. *Sure* and *claim* are both necessity, only
  their upward monotonicity mattering.
* A conditional is the material conditional with its consequent fixed, so the CP of the
  conditional clause denotes the whole conditional. This is downward entailing in the antecedent,
  which is all the sign needs, where a natural-language conditional is only Strawson downward
  entailing.
* The environments of *not … and* and *not … or* are Chierchia's strong values, negation being his
  *doubt*. The paper works the strengthened meaning through for *not every* only, so its
  application to the connectives is this file's. Tense adds no scalar alternatives, so the
  strengthened TP has the meaning of the strengthened polarity phrase.
* The *when*-clause of the sentence with clausemate negation is left out, as in its logical form.

## Errata

* The strengthened meaning conjoins the negation of the weakest alternative asymmetrically entailing
  the constituent, which is undefined when there is none: under *not … or* and in every
  constituent without a scalar term. Such a constituent is left as it is, as by Krifka's rule.
  The alternatives of a constituent without a scalar term are given as its meaning rather than
  the singleton of it.

## TODO

* Entanglement and cyclic marking of polarity items, and the test with *at most five people sold
  someone anything*, which needs a model separating downward entailment from anti-additivity.
* The disruption by *not every*, which needs a model of individuals, and the rescuing of *some* by
  a quantifier in the specifier of TP or by inferences that are not downward entailing.
* Strong negative polarity items such as *a single*.

## References

* [homer-2021]
* [chierchia-2004]
-/

@[expose] public section

namespace Homer2021

open Set NaturalLogic PolarityItem Chierchia2004 Chierchia2004.Meaning

/-- A world: a fact independent of the polarity item, and which of two things the subject did. -/
abbrev World := Bool × Finset (Fin 2)

/-- *The subject did something in `N`*, as a function of the restrictor `N` of the indefinite. -/
def didSome (N : Set (Fin 2)) : Set World := {w | ∃ x ∈ N, x ∈ w.2}

theorem monotone_didSome : Monotone didSome := fun _ _ h _ ⟨x, hx, hw⟩ ↦ ⟨x, h hx, hw⟩

theorem soundFor_mono_didSome : Signature.SoundFor .mono didSome :=
  soundFor_mono_iff.2 monotone_didSome

@[simp]
theorem didSome_eq_empty {N : Set (Fin 2)} : didSome N = ∅ ↔ N = ∅ := by
  refine ⟨fun h ↦ eq_empty_of_forall_notMem fun x hx ↦ ?_, fun h ↦ h ▸ by ext; simp [didSome]⟩
  exact (eq_empty_iff_forall_notMem.1 h) ((false, {x}) : World) ⟨x, hx, by simp⟩

@[simp]
theorem didSome_empty : didSome ∅ = ∅ :=
  didSome_eq_empty.2 rfl

@[simp]
theorem mem_didSome_univ {w : World} : w ∈ didSome univ ↔ w.2.Nonempty := by
  simp [didSome, Finset.Nonempty]

/-! ### Layers -/

/-- The modal base: the worlds in which the subject did the first thing. -/
def modalBase : Set World := {w | 0 ∈ w.2}

@[simp]
theorem disjoint_modalBase_didSome {N : Set (Fin 2)} : Disjoint modalBase (didSome N) ↔ N = ∅ := by
  refine ⟨fun h ↦ eq_empty_of_forall_notMem fun x hx ↦ ?_, fun h ↦ h ▸ by simp⟩
  exact disjoint_left.1 h (show ((false, {0, x}) : World) ∈ modalBase by simp [modalBase])
    ⟨x, hx, by simp⟩

@[simp]
theorem modalBase_subset_didSome {N : Set (Fin 2)} : modalBase ⊆ didSome N ↔ 0 ∈ N := by
  refine ⟨fun h ↦ ?_, fun h w hw ↦ ⟨0, h, hw⟩⟩
  obtain ⟨x, hx, hw⟩ := h (a := (false, {0})) (by simp [modalBase])
  exact Finset.mem_singleton.1 hw ▸ hx

@[simp]
theorem modalBase_ne_empty : modalBase ≠ ∅ :=
  Nonempty.ne_empty ⟨((false, {0}) : World), by simp [modalBase]⟩

/-- Clausemate negation, *pas* or *not*. -/
def negation : Signature.soundPairs (Set World) :=
  ⟨(compl, .antiAddMult), compl_soundFor_antiAddMult⟩

/-- *It is impossible that `p`*: no world of the modal base is a `p`-world. -/
def impossible : Signature.soundPairs (Set World) :=
  ⟨(fun p ↦ {_w | Disjoint modalBase p}, .anti),
    soundFor_anti_iff.2 fun _ _ h _ hd ↦ Disjoint.mono_right h hd⟩

/-- *I am sure that `p`*, *I claim that `p`*: every world of the modal base is a `p`-world. -/
def necessity : Signature.soundPairs (Set World) :=
  ⟨(fun p ↦ {_w | modalBase ⊆ p}, .mono),
    soundFor_mono_iff.2 fun _ _ h _ hp ↦ (hp : modalBase ⊆ _).trans h⟩

/-- *If `p`, `q`*, the material conditional with the consequent fixed. -/
def conditional (q : Set World) : Signature.soundPairs (Set World) :=
  ⟨(fun p ↦ pᶜ ∪ q, .anti),
    soundFor_anti_iff.2 fun _ _ h ↦ union_subset_union_left _ (compl_subset_compl.2 h)⟩

/-- The consequent of a conditional: *I will apologize to him*, *he has no notion of French at
all*. -/
def consequent : Set World := {w | w.1}

/-! ### Paths -/

/-- The path of the indefinite in a clause with polarity head `pol`, under the layers `t`,
outermost first. -/
def path (pol : Signature.soundPairs (Set World)) (t : List (Signature.soundPairs (Set World))) :
    Path (Set (Fin 2)) (Set World) where
  minimal := (pol : Function.End (Set World) × Signature).1 ∘ didSome
  signature := (pol : Function.End (Set World) × Signature).2 * Signature.mono
  sound := (Signature.mem_soundPairs.1 pol.2).comp soundFor_mono_didSome
  layers := t

/-- The path of the indefinite in a clause with polarity head `pol`, embedded under a polarity
phrase whose layer is `sup`: the domains are the embedded polarity phrase, TP and CP, and the
superordinate polarity phrase and TP. -/
def embedded (pol sup : Signature.soundPairs (Set World)) : Path (Set (Fin 2)) (Set World) :=
  path pol [1, sup, 1, 1]

-- (18), (31a)
/-- *Il n'est pas impossible que Jean ait fait quoi que ce soit*. -/
def notImpossible := embedded 1 (negation * impossible)

-- (19), (31b), (48a)
/-- *It is impossible that Jean didn't do something*. -/
def impossibleNot := embedded negation impossible

-- (32), (33), (48b), (49)
/-- *It is not impossible that Jean didn't do something*. -/
def notImpossibleNot := embedded negation (negation * impossible)

-- (24), (31c)
/-- *If it is impossible that Jean did something, I will apologize to him*: the matrix TP, the
CP, TP and polarity phrase of the conditional clause, and the CP and TP of the embedded clause. -/
def ifImpossible := path 1 [1, conditional consequent, 1, impossible, 1, 1]

-- (41a), (45a)
/-- *Jean-Paul doesn't understand something*. -/
def clausemateNot := path negation [1]

-- (42a), (45b)
/-- *I don't claim that Jean-Paul understands something*. -/
def notClaim := embedded 1 (negation * necessity)

-- (42b)
/-- *It is impossible that Jean-Paul understands something*. -/
def impossibleBare := embedded 1 impossible

-- (46a), (47)
/-- *I'm not sure that Jean-Paul doesn't understand something*. -/
def notSureNot := embedded negation (negation * necessity)

-- (46b)
/-- *If Jean-Paul doesn't understand something, he has no notion of French at all*: the matrix
TP, and the CP and TP of the conditional clause. -/
def ifNot := path negation [1, conditional consequent, 1]

-- (48c)
/-- *Not that it is impossible that John doesn't understand something*. -/
def notThatImpossibleNot := path negation [negation, 1, impossible, 1, 1]

/-! ### Flip-flop -/

section FlipFlop

attribute [local simp] path embedded negation impossible necessity Signature.sign_mul
  Function.End.one_def Function.End.mul_def

theorem not_licenses_negative_notImpossible : ¬notImpossible.Licenses .negative := by
  refine Path.not_licenses_negative _ fun t ht ↦ ?_
  simp [notImpossible] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl <;>
    refine ⟨?_, ∅, univ, empty_subset _, Ne.symm ?_⟩ <;> simp [notImpossible] <;> decide

theorem licenses_negative_impossibleNot : impossibleNot.Licenses .negative :=
  impossibleNot.licenses_negative (t := []) (by simp) (by simp [impossibleNot]; decide)

theorem licenses_negative_notImpossibleNot : notImpossibleNot.Licenses .negative :=
  notImpossibleNot.licenses_negative (t := []) (by simp) (by simp [notImpossibleNot]; decide)

theorem licenses_negative_ifImpossible : ifImpossible.Licenses .negative :=
  ifImpossible.licenses_negative (t := [impossible, 1, 1]) (by simp [ifImpossible])
    (by simp [ifImpossible]; decide)

theorem not_licenses_positive_clausemateNot : ¬clausemateNot.Licenses .positive :=
  clausemateNot.not_licenses_positive fun t ht ↦ by
    simp [clausemateNot] at ht
    rcases ht with rfl | rfl <;> simp [clausemateNot] <;> decide

theorem licenses_positive_notClaim : notClaim.Licenses .positive :=
  notClaim.licenses_positive (t := []) (by simp) (by simp [notClaim]; decide)
    (empty_subset univ) (Ne.symm <| by simp [notClaim])

theorem licenses_positive_impossibleBare : impossibleBare.Licenses .positive :=
  impossibleBare.licenses_positive (t := []) (by simp) (by simp [impossibleBare]; decide)
    (empty_subset univ) (Ne.symm <| by simp [impossibleBare])

theorem licenses_positive_notSureNot : notSureNot.Licenses .positive :=
  notSureNot.licenses_positive (t := [negation * necessity, 1, 1]) (by simp [notSureNot])
    (by simp [notSureNot]; decide) (empty_subset univ)
    (Ne.symm <| by simp [notSureNot, subset_compl_iff_disjoint_right])

theorem licenses_positive_impossibleNot : impossibleNot.Licenses .positive :=
  impossibleNot.licenses_positive (t := [impossible, 1, 1]) (by simp [impossibleNot])
    (by simp [impossibleNot]; decide) (empty_subset univ)
    (Ne.symm <| by simp [impossibleNot, disjoint_compl_right_iff_subset])

theorem not_licenses_positive_notImpossibleNot : ¬notImpossibleNot.Licenses .positive :=
  notImpossibleNot.not_licenses_positive fun t ht ↦ by
    simp [notImpossibleNot] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl <;> simp [notImpossibleNot] <;> decide

theorem licenses_positive_ifNot : ifNot.Licenses .positive :=
  ifNot.licenses_positive (t := [conditional consequent, 1]) (by simp [ifNot])
    (by simp [ifNot, conditional]; decide) (empty_subset univ) (Ne.symm <| by
      simpa [ifNot, conditional, subset_def, consequent] using ⟨{0}, by simp⟩)

theorem licenses_positive_notThatImpossibleNot : notThatImpossibleNot.Licenses .positive :=
  notThatImpossibleNot.licenses_positive (t := [impossible, 1, 1])
    (by simp [notThatImpossibleNot]) (by simp [notThatImpossibleNot]; decide) (empty_subset univ)
    (Ne.symm <| by simp [notThatImpossibleNot, disjoint_compl_right_iff_subset])

theorem antitone_notThatImpossibleNot :
    Antitone (notThatImpossibleNot.environment notThatImpossibleNot.layers) :=
  notThatImpossibleNot.antitone_environment (by simp [notThatImpossibleNot]; decide)

end FlipFlop

/-- *Quoi que ce soit* is anti-licensed under *pas impossible*, two clausemate downward-entailing
expressions, and licensed again when its own clause is negated. -/
theorem flipFlop_npi :
    ¬notImpossible.Licenses .negative ∧ notImpossibleNot.Licenses .negative :=
  ⟨not_licenses_negative_notImpossible, licenses_negative_notImpossibleNot⟩

/-- *Some* is anti-licensed under clausemate negation, rescued by a superordinate *impossible*,
and anti-licensed again under a superordinate *not impossible*. -/
theorem flipFlop_ppi :
    ¬clausemateNot.Licenses .positive ∧ impossibleNot.Licenses .positive ∧
      ¬notImpossibleNot.Licenses .positive :=
  ⟨not_licenses_positive_clausemateNot, licenses_positive_impossibleNot,
    not_licenses_positive_notImpossibleNot⟩

/-- Under *not that*, *impossible* and a clausemate negation, *some* is licensed although the
sentence is downward entailing with respect to it, since a smaller domain is not. -/
theorem localist_ppi :
    Antitone (notThatImpossibleNot.environment notThatImpossibleNot.layers) ∧
      notThatImpossibleNot.Licenses .positive :=
  ⟨antitone_notThatImpossibleNot, licenses_positive_notThatImpossibleNot⟩

/-! ### Disruption by scalar implicatures -/

/-- *John drank wine*. -/
def wine : Set World := {w | w.1}

theorem wine_nonempty : wine.Nonempty := ⟨(true, ∅), rfl⟩

theorem wine_ne_univ : wine ≠ univ :=
  (ne_univ_iff_exists_notMem _).2 ⟨(false, ∅), by simp [wine]⟩

/-- *John didn't drink wine `conn` something in `N`*: Chierchia's strong value of the polarity
phrase, *doubt* being complementation, as a function of the domain `N`. -/
noncomputable def notConn (conn : Set World → Meaning (Set World → Set World))
    (N : Set (Fin 2)) : Meaning (Set World) :=
  doubt.strongApply ((conn wine).strongApply (.lexical (didSome N) {didSome N}))

theorem notConn_conj_strong (N : Set (Fin 2)) :
    (notConn conj N).strong = (wine ∩ didSome N)ᶜ ∩ (wine ∪ didSome N) :=
  doubt_conj_strong wine_nonempty <| (ssubset_iff_of_subset
    (inter_subset_left.trans subset_union_left)).2 ⟨(true, ∅), Or.inl rfl, fun h ↦ by
      simpa [didSome] using h.2⟩

theorem notConn_disj_strong (N : Set (Fin 2)) : (notConn disj N).strong = (wine ∪ didSome N)ᶜ :=
  doubt_disj_strong wine_nonempty wine_ne_univ

theorem antitone_notConn_conj_ordinary : Antitone fun N ↦ (notConn conj N).ordinary := by
  intro _ _ h
  simp only [notConn, strongApply_ordinary, doubt, conj, lexical]
  exact compl_subset_compl.2 (inter_subset_inter_right _ (monotone_didSome h))

theorem not_antitone_notConn_conj : ¬Antitone fun N ↦ (notConn conj N).strong := fun h ↦ by
  have := h (empty_subset univ) (show ((false, {0}) : World) ∈ (notConn conj univ).strong by
    simp [notConn_conj_strong, wine])
  simp [notConn_conj_strong, wine] at this

theorem not_monotone_notConn_conj : ¬Monotone fun N ↦ (notConn conj N).strong := fun h ↦ by
  have := h (empty_subset univ) (show ((true, {0}) : World) ∈ (notConn conj ∅).strong by
    simp [notConn_conj_strong, wine])
  simp [notConn_conj_strong, wine] at this

theorem notConn_disj_strong_eq_ordinary (N : Set (Fin 2)) :
    (notConn disj N).strong = (notConn disj N).ordinary := by
  rw [notConn_disj_strong]
  simp [notConn, strongApply_ordinary, doubt, disj, lexical]

theorem antitone_notConn_disj : Antitone fun N ↦ (notConn disj N).strong := fun _ _ h ↦ by
  simp only [notConn_disj_strong]
  exact compl_subset_compl.2 (union_subset_union_right _ (monotone_didSome h))

-- (50e), (56d)
/-- *John didn't drink wine and something*: the strengthened polarity phrase and TP. -/
noncomputable def notAnd : Path (Set (Fin 2)) (Set World) :=
  ⟨fun N ↦ (notConn conj N).strong, .all, soundFor_all _, [1]⟩

-- (51b), (56e)
/-- *John didn't drink wine or something*: the strengthened polarity phrase and TP. -/
noncomputable def notOr : Path (Set (Fin 2)) (Set World) :=
  ⟨fun N ↦ (notConn disj N).strong, .anti, soundFor_anti_iff.2 antitone_notConn_disj, [1]⟩

theorem not_licenses_negative_notAnd : ¬notAnd.Licenses .negative := by
  simp [Path.Licenses, notAnd, Function.End.one_def, not_antitone_notConn_conj]

theorem licenses_positive_notAnd : notAnd.Licenses .positive :=
  ⟨[], by simp, not_antitone_notConn_conj⟩

theorem licenses_negative_notOr : notOr.Licenses .negative :=
  ⟨[], by simp, antitone_notConn_disj⟩

theorem not_licenses_positive_notOr : ¬notOr.Licenses .positive :=
  notOr.not_licenses_positive fun t ht ↦ by
    simp [notOr] at ht
    rcases ht with rfl | rfl <;> simp [notOr] <;> decide

/-- *John didn't drink wine and …* is downward entailing with respect to the indefinite, but not
once strengthened by its implicature that John drank one of them, so *any* is anti-licensed and
*some* licensed in it; *John didn't drink wine or …* is its own strengthened meaning, and the
reverse holds. -/
theorem disruption :
    (Antitone (fun N ↦ (notConn conj N).ordinary) ∧ ¬notAnd.Licenses .negative ∧
      notAnd.Licenses .positive) ∧
    ((∀ N, (notConn disj N).strong = (notConn disj N).ordinary) ∧ notOr.Licenses .negative ∧
      ¬notOr.Licenses .positive) :=
  ⟨⟨antitone_notConn_conj_ordinary, not_licenses_negative_notAnd, licenses_positive_notAnd⟩,
    notConn_disj_strong_eq_ordinary, licenses_negative_notOr, not_licenses_positive_notOr⟩

/-! ### The judgments -/

/-- The path of a row's item, read from the negation of its own clause, the expressions of the
superordinate clause and the connective. -/
noncomputable def path? (e : Datum) : Option (Path (Set (Fin 2)) (Set World)) :=
  match e.feature? "clause", e.feature? "superordinate", e.feature? "connective" with
  | some "none", some "not impossible", none => some notImpossible
  | some "negation", some "impossible", none => some impossibleNot
  | some "negation", some "not impossible", none => some notImpossibleNot
  | some "none", some "if impossible", none => some ifImpossible
  | some "negation", none, none => some clausemateNot
  | some "none", some "not claim", none => some notClaim
  | some "none", some "impossible", none => some impossibleBare
  | some "negation", some "not sure", none => some notSureNot
  | some "negation", some "if", none => some ifNot
  | some "negation", some "not that impossible", none => some notThatImpossibleNot
  | some "negation", none, some "and" => some notAnd
  | some "negation", none, some "or" => some notOr
  | _, _, _ => none

/-- The polarity of a row's item. -/
def polarity? (e : Datum) : Option Polarity :=
  match e.feature? "item" with
  | some "quoi que ce soit" | some "any" => some .negative
  | some "some" => some .positive
  | _ => none

/-- The licensing of a row's item in its path. -/
noncomputable def licensing? (e : Datum) : Option Prop :=
  (path? e).bind fun p ↦ (polarity? e).map p.Licenses

/-- The judgment on which a row's item is evaluated: the narrowest scope of *some*, the sentence
otherwise. -/
def judgment? (e : Datum) : Option Judgment :=
  if e.feature? "item" = some "some" then e.readings.lookup "narrowest scope of some"
  else some e.judgment

/-- An item is judged acceptable exactly when it meets the licensing condition in its path. -/
theorem rows_licensing : ∀ e ∈ Examples.all, ∀ p ∈ licensing? e, ∀ j ∈ judgment? e,
    (j = .acceptable ↔ p) := by
  simp only [Examples.all, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rintro p ⟨⟩ j ⟨⟩ <;>
    first
      | exact iff_of_false (by decide) not_licenses_negative_notImpossible
      | exact iff_of_true rfl licenses_negative_impossibleNot
      | exact iff_of_true rfl licenses_negative_ifImpossible
      | exact iff_of_true rfl licenses_negative_notImpossibleNot
      | exact iff_of_false (by decide) not_licenses_positive_clausemateNot
      | exact iff_of_true rfl licenses_positive_notClaim
      | exact iff_of_true rfl licenses_positive_impossibleBare
      | exact iff_of_true rfl licenses_positive_notSureNot
      | exact iff_of_true rfl licenses_positive_impossibleNot
      | exact iff_of_true rfl licenses_positive_ifNot
      | exact iff_of_true rfl licenses_positive_notThatImpossibleNot
      | exact iff_of_false (by decide) not_licenses_positive_notImpossibleNot
      | exact iff_of_false (by decide) not_licenses_negative_notAnd
      | exact iff_of_true rfl licenses_negative_notOr
      | exact iff_of_true rfl licenses_positive_notAnd
      | exact iff_of_false (by decide) not_licenses_positive_notOr

theorem readCount_licensing : Datum.ReadCount licensing? Examples.all 16 := by
  decide +kernel

end Homer2021
