module

public import Linglib.Semantics.Polarity.Environment
public import Linglib.Fragments.English.PolarityItems
public import Linglib.Data.Examples.Homer2021
public import Studies.Chierchia2004

/-!
# Homer (2021): Domains of polarity items

This file formalizes the localist, environment-based theory of polarity items: an item is
evaluated in its domains, the constituents containing it and the polarity head of their own
clause, and it is acceptable only if it is acceptable in some domain, one carrying the strength of
negation that licenses it and lacking the strength that blocks it. For *quoi que ce soit*, *any*
and, as the paper concludes, *some*, that strength is downward entailment. A second
downward-entailing expression in a domain undoes the first, so [*quoi que ce soit* and *some* are
anti-licensed and licensed again](##Homer2021.flipFlop) as such expressions stack up, and [*some*
survives three of them](##Homer2021.localist_ppi) in a sentence downward entailing with respect
to it, since a smaller domain is not. A scalar implicature can [make a domain
non-monotone](##Homer2021.not_monotone_notConn_conj): [*any* is anti-licensed and *some* licensed
under *not … and*, but not under *not … or*](##Homer2021.disruption).

Occurrences of *some* and *any* are entangled: an item is marked as licensed in a domain only if
every other item there counts as acceptable there, being acceptable or marked as licensed in a
smaller constituent, so licensing proceeds bottom-up. Below *impossible*, [*anyone … something*
is licensed and *someone … anything* is not](##Homer2021.cyclicity), *something* being marked as
licensed in its own clause first. Entanglement gives the paper's argument that [*some* is blocked
by downward entailment rather than anti-additivity](##Homer2021.downwardEntailment): below *not
sure*, downward entailing without being anti-additive, an anti-additive classification would
license *someone* together with *anything*. The same holds, without entanglement, below *not
impossible … not*, a derivation of this file.

## Implementation notes

* The paper states its conditions as necessary ones. For sentences with one polarity item they are
  read here as biconditionals, as the paper does when it predicts which of them are acceptable.
* A world records a fact independent of the polarity item and which of two things the subject did.
  The environment of a domain is a function of the meaning of the indefinite, a quantifier over
  things, evaluated at the things the subject did: the abstraction over the position of the item.
* Each clause contributes its polarity phrase, whose head is the layer of the minimal domain, and
  its TP and, when embedded, CP, which are identity layers. A superordinate polarity phrase
  composes its polarity head with the predicate below it.
* The modals quantify over a fixed modal base, the worlds in which the subject did something, so
  that it is possible that the subject did not do the first thing, and possible that the subject
  did not do the second, but not that the subject did neither: *not impossible … not* is not
  anti-additive, as it would be over a base of one world. *Sure* and *claim* are both necessity,
  only their upward monotonicity mattering.
* A conditional is the material conditional with its consequent fixed, so the CP of the
  conditional clause denotes the whole conditional. This is downward entailing in the antecedent,
  which is all the sign needs, where a natural-language conditional is only Strawson downward
  entailing.
* The environments of *not … and* and *not … or* are Chierchia's strong values, negation being his
  *doubt*. The paper works the strengthened meaning through for *not every* only, so its
  application to the connectives is this file's. Tense adds no scalar alternatives, so the
  strengthened TP has the meaning of the strengthened polarity phrase.
* *Quoi que ce soit* and *some* are this file's entries, licensed and blocked by downward
  entailment; *any* and *someone* are the Fragment's, *someone* blocked by anti-additivity.
* The *when*-clause of the sentence with clausemate negation is left out, as in its logical form.
* In the sentences with two indefinites, a world records which of two people did which of two
  things, every two items are entangled, and the constituents are numbered from the bottom of the
  clausal spine. A constituent below the position of the subject denotes a proposition for each
  value of its trace, and the modal base is the worlds in which someone did something.

## Errata

* The strengthened meaning conjoins the negation of the weakest alternative asymmetrically entailing
  the constituent, which is undefined when there is none: under *not … or* and in every
  constituent without a scalar term. Such a constituent is left as it is, as by Krifka's rule.
  The alternatives of a constituent without a scalar term are given as its meaning rather than
  the singleton of it.

## TODO

* The entanglement of *some* with itself and of *any* with itself, and *at most five people sold
  someone anything*, which needs a model of counting.
* The disruption by *not every*, which needs a model of individuals, and the rescuing of *some* by
  a quantifier in the specifier of TP or by inferences that are not downward entailing.
* Strong negative polarity items such as *a single*.

## References

* [homer-2021]
* [chierchia-2004]
* [szabolcsi-2004]
-/

@[expose] public section

namespace Homer2021

open Set NaturalLogic PolarityItem Chierchia2004 Chierchia2004.Meaning

/-- A world: a fact independent of the polarity item, and which of two things the subject did. -/
abbrev World := Bool × Finset (Fin 2)

/-- *The subject did `Q`*, the quantifier `Q` evaluated at the things the subject did, as a
function of the meaning of the indefinite. -/
def did (Q : Quantifier (Fin 2)) : Set World := {w | Q w.2}

theorem holdsFor_did : Signature.HoldsFor .addMult did := by
  intro r hr
  simp only [Signature.properties, Finset.mem_insert, Finset.mem_singleton] at hr
  rcases hr with rfl | rfl | rfl
  · exact fun _ _ h _ hw ↦ h _ hw
  · exact ⟨fun _ _ ↦ rfl, rfl⟩
  · exact ⟨fun _ _ ↦ rfl, rfl⟩

@[simp]
theorem did_bot : did ⊥ = ∅ :=
  rfl

@[simp]
theorem did_top : did ⊤ = univ :=
  rfl

/-! ### Layers -/

/-- The modal base: the worlds in which the subject did something. -/
def modalBase : Set World := {w | w.2.Nonempty}

@[simp]
theorem modalBase_ne_empty : modalBase ≠ ∅ :=
  Nonempty.ne_empty ⟨((false, {0}) : World), by simp [modalBase]⟩

/-- *It is impossible that `p`*: no world of the modal base is a `p`-world. -/
def impossible : Signature.classPairs (Set World) :=
  ⟨(fun p ↦ {_w | Disjoint modalBase p}, .antiAdd), Signature.holdsFor_antiAdd_iff.2
    ⟨fun _ _ ↦ by ext; simp, by simp⟩⟩

/-- *I am sure that `p`*, *I claim that `p`*: every world of the modal base is a `p`-world. -/
def necessity : Signature.classPairs (Set World) :=
  ⟨(fun p ↦ {_w | modalBase ⊆ p}, .mono),
    Signature.holdsFor_mono_iff.2 fun _ _ h _ hp ↦ (hp : modalBase ⊆ _).trans h⟩

/-- *If `p`, `q`*, the material conditional with the consequent fixed. -/
def conditional (q : Set World) : Signature.classPairs (Set World) :=
  ⟨(fun p ↦ pᶜ ∪ q, .anti),
    Signature.holdsFor_anti_iff.2 fun _ _ h ↦ union_subset_union_left _ (compl_subset_compl.2 h)⟩

/-- The consequent of a conditional: *I will apologize to him*, *he has no notion of French at
all*. -/
def consequent : Set World := {w | w.1}

/-! ### Paths -/

/-- The path of the indefinite in a clause with polarity head `pol`, under the layers `t`,
outermost first. -/
def path (pol : Signature.classPairs (Set World)) (t : List (Signature.classPairs (Set World))) :
    Path (Quantifier (Fin 2)) (Set World) where
  minimal := (pol : Function.End (Set World) × Signature).1 ∘ did
  signature := (pol : Function.End (Set World) × Signature).2 * Signature.addMult
  holdsFor := (Signature.mem_classPairs.1 pol.2).comp holdsFor_did
  layers := t

/-- The path of the indefinite in a clause with polarity head `pol`, embedded under a polarity
phrase whose layer is `sup`: the domains are the embedded polarity phrase, TP and CP, and the
superordinate polarity phrase and TP. -/
def embedded (pol sup : Signature.classPairs (Set World)) : Path (Quantifier (Fin 2)) (Set World) :=
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

/-! ### The items -/

/-- *Quoi que ce soit*, licensed by downward entailment. -/
def quoiQueCeSoit : PolarityItem :=
  { form := "quoi que ce soit", licensor := some .weak }

/-- *Some*, blocked by downward entailment, as the paper concludes. -/
def someItem : PolarityItem :=
  { form := "some", antiLicensor := some .weak }

/-! ### Flip-flop -/

section FlipFlop

attribute [local simp] path embedded negation impossible necessity Signature.sign_mul
  Function.End.one_def Function.End.mul_def

theorem not_licenses_notImpossible : ¬notImpossible.Licenses quoiQueCeSoit :=
  notImpossible.not_licenses_of_mem_licensor rfl fun t ht ↦ by
    simp [notImpossible] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl <;> simp [notImpossible] <;> decide

theorem licenses_impossibleNot : impossibleNot.Licenses quoiQueCeSoit :=
  ⟨[], by simp,
    acceptable_of_licensor rfl rfl <|
      impossibleNot.carries_weak_of_sign_eq_neg_one (by simp [impossibleNot]; decide)
        (by simp [impossibleNot])⟩

theorem licenses_notImpossibleNot : notImpossibleNot.Licenses quoiQueCeSoit :=
  ⟨[], by simp,
    acceptable_of_licensor rfl rfl <|
      notImpossibleNot.carries_weak_of_sign_eq_neg_one (by simp [notImpossibleNot]; decide)
        (by simp [notImpossibleNot])⟩

theorem licenses_ifImpossible : ifImpossible.Licenses quoiQueCeSoit :=
  ⟨[impossible, 1, 1], by simp [ifImpossible],
    acceptable_of_licensor rfl rfl <|
      ifImpossible.carries_weak_of_sign_eq_neg_one (by simp [ifImpossible]; decide)
        (by simp [ifImpossible])⟩

theorem not_licenses_clausemateNot : ¬clausemateNot.Licenses someItem :=
  clausemateNot.not_licenses_of_mem_antiLicensor rfl fun t ht ↦ by
    simp [clausemateNot] at ht
    rcases ht with rfl | rfl <;>
      exact clausemateNot.carries_weak_of_sign_eq_neg_one (by simp [clausemateNot]; decide)
        (by simp [clausemateNot])

theorem licenses_notClaim : notClaim.Licenses someItem :=
  ⟨[], by simp,
    acceptable_of_antiLicensor rfl rfl <|
      notClaim.not_carries_of_sign_eq_one (by simp [notClaim]; decide)⟩

theorem licenses_impossibleBare : impossibleBare.Licenses someItem :=
  ⟨[], by simp,
    acceptable_of_antiLicensor rfl rfl <|
      impossibleBare.not_carries_of_sign_eq_one (by simp [impossibleBare]; decide)⟩

theorem licenses_notSureNot : notSureNot.Licenses someItem :=
  ⟨[negation * necessity, 1, 1], by simp [notSureNot],
    acceptable_of_antiLicensor rfl rfl <|
      notSureNot.not_carries_of_sign_eq_one (by simp [notSureNot]; decide)⟩

theorem licenses_impossibleNot_some : impossibleNot.Licenses someItem :=
  ⟨[impossible, 1, 1], by simp [impossibleNot],
    acceptable_of_antiLicensor rfl rfl <|
      impossibleNot.not_carries_of_sign_eq_one (by simp [impossibleNot]; decide)⟩

theorem not_licenses_notImpossibleNot_some : ¬notImpossibleNot.Licenses someItem :=
  notImpossibleNot.not_licenses_of_mem_antiLicensor rfl fun t ht ↦ by
    simp [notImpossibleNot] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl <;>
      exact notImpossibleNot.carries_weak_of_sign_eq_neg_one (by simp [notImpossibleNot]; decide)
        (by simp [notImpossibleNot])

theorem licenses_ifNot : ifNot.Licenses someItem :=
  ⟨[conditional consequent, 1], by simp [ifNot],
    acceptable_of_antiLicensor rfl rfl <|
      ifNot.not_carries_of_sign_eq_one (by simp [ifNot, conditional]; decide)⟩

theorem licenses_notThatImpossibleNot : notThatImpossibleNot.Licenses someItem :=
  ⟨[impossible, 1, 1], by simp [notThatImpossibleNot],
    acceptable_of_antiLicensor rfl rfl <|
      notThatImpossibleNot.not_carries_of_sign_eq_one (by simp [notThatImpossibleNot]; decide)⟩

theorem antitone_notThatImpossibleNot :
    Antitone (notThatImpossibleNot.environment notThatImpossibleNot.layers) :=
  notThatImpossibleNot.antitone_environment (by simp [notThatImpossibleNot]; decide)

end FlipFlop

/-- *Quoi que ce soit* is anti-licensed under *pas impossible*, two clausemate downward-entailing
expressions, and licensed again when its own clause is negated; *some* is anti-licensed under
clausemate negation, rescued by a superordinate *impossible*, and anti-licensed again under a
superordinate *not impossible*. -/
theorem flipFlop :
    (¬notImpossible.Licenses quoiQueCeSoit ∧ notImpossibleNot.Licenses quoiQueCeSoit) ∧
      ¬clausemateNot.Licenses someItem ∧ impossibleNot.Licenses someItem ∧
        ¬notImpossibleNot.Licenses someItem :=
  ⟨⟨not_licenses_notImpossible, licenses_notImpossibleNot⟩, not_licenses_clausemateNot,
    licenses_impossibleNot_some, not_licenses_notImpossibleNot_some⟩

/-- Under *not that*, *impossible* and a clausemate negation, *some* is licensed although the
sentence is downward entailing with respect to it, since a smaller domain is not. -/
theorem localist_ppi :
    Antitone (notThatImpossibleNot.environment notThatImpossibleNot.layers) ∧
      notThatImpossibleNot.Licenses someItem :=
  ⟨antitone_notThatImpossibleNot, licenses_notThatImpossibleNot⟩

/-! ### Downward entailment or anti-additivity -/

-- the superordinate polarity phrase of (48b): somewhere in the modal base the subject did not do
-- `Q`, false for *something* but true for *the first thing* and for *the second thing*
theorem not_isAntiAdditive_notImpossibleNot :
    ¬IsAntiAdditive (notImpossibleNot.environment [negation * impossible, 1, 1]) := fun h ↦ by
  have := congrArg (((false, ∅) : World) ∈ ·)
    (h (Quantifier.Det.some {0}) (Quantifier.Det.some {1}))
  simp [notImpossibleNot, embedded, path, negation, impossible, Function.End.one_def,
    Function.End.mul_def, did, modalBase, Quantifier.Det.some] at this
  rw [disjoint_compl_right_iff_subset, disjoint_compl_right_iff_subset,
    disjoint_compl_right_iff_subset] at this
  refine this.2 ⟨fun h0 ↦ ?_, fun h1 ↦ ?_⟩ fun w ⟨x, hx⟩ ↦ ?_
  · simpa using h0 (a := ((false, {1}) : World)) (by simp)
  · simpa using h1 (a := ((false, {0}) : World)) (by simp)
  · fin_cases x
    exacts [Or.inl hx, Or.inr hx]

-- the superordinate polarity phrase of (48b) is downward entailing but not anti-additive
theorem notImpossibleNot_someone :
    notImpossibleNot.Licenses English.PolarityItems.someone ∧
      ¬notImpossibleNot.Licenses someItem := by
  refine ⟨⟨[negation * impossible, 1, 1], by simp [notImpossibleNot, embedded, path],
    acceptable_of_antiLicensor rfl rfl fun hc ↦ ?_⟩, not_licenses_notImpossibleNot_some⟩
  exact not_isAntiAdditive_notImpossibleNot
    (Signature.holdsFor_antiAdd_iff.1 (notImpossibleNot.carries_iff.1 hc).1).1

/-! ### Disruption by scalar implicatures -/

/-- *John drank wine*. -/
def wine : Set World := {w | w.1}

theorem wine_nonempty : wine.Nonempty := ⟨(true, ∅), rfl⟩

theorem wine_ne_univ : wine ≠ univ :=
  (ne_univ_iff_exists_notMem _).2 ⟨(false, ∅), by simp [wine]⟩

theorem wine_inter_did_ssubset (Q : Quantifier (Fin 2)) : wine ∩ did Q ⊂ wine ∪ did Q := by
  refine (ssubset_iff_of_subset (inter_subset_left.trans subset_union_left)).2 ?_
  by_cases hQ : Q ∅
  · exact ⟨(false, ∅), Or.inr (by simpa [did] using hQ), fun h ↦ by simpa [wine] using h.1⟩
  · exact ⟨(true, ∅), Or.inl rfl, fun h ↦ hQ (by simpa [did] using h.2)⟩

/-- *John didn't drink wine `conn` `Q`*: Chierchia's strong value of the polarity phrase, *doubt*
being complementation, as a function of the meaning `Q` of the indefinite. -/
noncomputable def notConn (conn : Set World → Meaning (Set World → Set World))
    (Q : Quantifier (Fin 2)) : Meaning (Set World) :=
  doubt.strongApply ((conn wine).strongApply (.lexical (did Q) {did Q}))

theorem notConn_conj_strong (Q : Quantifier (Fin 2)) :
    (notConn conj Q).strong = (wine ∩ did Q)ᶜ ∩ (wine ∪ did Q) :=
  doubt_conj_strong wine_nonempty (wine_inter_did_ssubset Q)

theorem notConn_disj_strong (Q : Quantifier (Fin 2)) :
    (notConn disj Q).strong = (wine ∪ did Q)ᶜ :=
  doubt_disj_strong wine_nonempty wine_ne_univ

theorem antitone_notConn_conj_ordinary : Antitone fun Q ↦ (notConn conj Q).ordinary := by
  intro _ _ h
  simp only [notConn, strongApply_ordinary, doubt, conj, lexical]
  exact compl_subset_compl.2 (inter_subset_inter_right _ (fun _ hw ↦ h _ hw))

theorem not_antitone_notConn_conj : ¬Antitone fun Q ↦ (notConn conj Q).strong := fun h ↦ by
  have := h (bot_le : ⊥ ≤ (⊤ : Quantifier (Fin 2)))
    (show ((false, ∅) : World) ∈ (notConn conj ⊤).strong by simp [notConn_conj_strong, wine])
  simp [notConn_conj_strong, wine] at this

theorem not_monotone_notConn_conj : ¬Monotone fun Q ↦ (notConn conj Q).strong := fun h ↦ by
  have := h (bot_le : ⊥ ≤ (⊤ : Quantifier (Fin 2)))
    (show ((true, ∅) : World) ∈ (notConn conj ⊥).strong by simp [notConn_conj_strong, wine])
  simp [notConn_conj_strong, wine] at this

theorem notConn_disj_strong_eq_ordinary (Q : Quantifier (Fin 2)) :
    (notConn disj Q).strong = (notConn disj Q).ordinary := by
  rw [notConn_disj_strong]
  simp [notConn, strongApply_ordinary, doubt, disj, lexical]

theorem antitone_notConn_disj : Antitone fun Q ↦ (notConn disj Q).strong := fun _ _ h ↦ by
  simp only [notConn_disj_strong]
  exact compl_subset_compl.2 (union_subset_union_right _ (fun _ hw ↦ h _ hw))

-- (50e), (56d)
/-- *John didn't drink wine and something*: the strengthened polarity phrase and TP. -/
noncomputable def notAnd : Path (Quantifier (Fin 2)) (Set World) :=
  ⟨fun Q ↦ (notConn conj Q).strong, .all, fun _ h ↦ absurd h (by simp [Signature.properties]),
    [1]⟩

-- (51b), (56e)
/-- *John didn't drink wine or something*: the strengthened polarity phrase and TP. -/
noncomputable def notOr : Path (Quantifier (Fin 2)) (Set World) :=
  ⟨fun Q ↦ (notConn disj Q).strong, .anti, Signature.holdsFor_anti_iff.2 antitone_notConn_disj,
    [1]⟩

theorem not_carries_notAnd {t : List (Signature.classPairs (Set World))}
    (ht : t ∈ notAnd.layers.tails) {s : Negation.Strength} : ¬notAnd.Carries t s := fun hc ↦ by
  have ha := Signature.holdsFor_anti_iff.1
    ((notAnd.carries_iff.1 hc).1.of_le (by cases s <;> decide))
  simp [notAnd] at ht
  rcases ht with rfl | rfl <;> exact not_antitone_notConn_conj (by simpa [notAnd,
    Function.End.one_def] using ha)

theorem carries_notOr {t : List (Signature.classPairs (Set World))} (ht : t ∈ notOr.layers.tails) :
    notOr.Carries t .weak := by
  simp [notOr] at ht
  rcases ht with rfl | rfl <;>
    refine notOr.carries_weak_of_sign_eq_neg_one (by simp [notOr]; decide) ?_ <;>
    simp [notOr, Function.End.one_def, notConn_disj_strong, wine_ne_univ]

theorem not_licenses_notAnd : ¬notAnd.Licenses English.PolarityItems.any :=
  fun ⟨_, ht, ha⟩ ↦ not_carries_notAnd ht (ha.1 .weak rfl)

theorem licenses_notAnd : notAnd.Licenses someItem :=
  ⟨[], by simp, acceptable_of_antiLicensor rfl rfl (not_carries_notAnd (by simp))⟩

theorem licenses_notOr : notOr.Licenses English.PolarityItems.any :=
  ⟨[], by simp, acceptable_of_licensor rfl rfl (carries_notOr (by simp))⟩

theorem not_licenses_notOr : ¬notOr.Licenses someItem :=
  notOr.not_licenses_of_mem_antiLicensor rfl fun _ ht ↦ carries_notOr ht

/-- *John didn't drink wine and …* is downward entailing with respect to the indefinite, but not
once strengthened by its implicature that John drank one of them, so *any* is anti-licensed and
*some* licensed in it; *John didn't drink wine or …* is its own strengthened meaning, and the
reverse holds. -/
theorem disruption :
    (Antitone (fun Q ↦ (notConn conj Q).ordinary) ∧
      ¬notAnd.Licenses English.PolarityItems.any ∧ notAnd.Licenses someItem) ∧
    ((∀ Q, (notConn disj Q).strong = (notConn disj Q).ordinary) ∧
      notOr.Licenses English.PolarityItems.any ∧ ¬notOr.Licenses someItem) :=
  ⟨⟨antitone_notConn_conj_ordinary, not_licenses_notAnd, licenses_notAnd⟩,
    notConn_disj_strong_eq_ordinary, licenses_notOr, not_licenses_notOr⟩

/-! ### Entanglement -/

/-- A world of the sentences with two indefinites: which of two people did which of two things. -/
abbrev World₂ := Finset (Fin 2 × Fin 2)

/-- The meaning of a constituent: a proposition for each value of the trace of the subject. -/
abbrev Clause := Fin 2 → Set World₂

/-- *`x` did `Q`*. -/
def did₂ (x : Fin 2) (Q : Quantifier (Fin 2)) : Set World₂ := {w | Q {y | (x, y) ∈ w}}

/-- The subject `Q` binding its trace in `c`. -/
def subject (Q : Quantifier (Fin 2)) (c : Clause) : Clause := fun _ ↦ {w | Q {x | w ∈ c x}}

/-- The modal base: the worlds in which someone did something. -/
def modalBase₂ : Set World₂ := {w | w.Nonempty}

/-- *It is impossible that `c`*. -/
def impossible₂ (c : Clause) : Clause := fun x ↦ {_w | Disjoint modalBase₂ (c x)}

/-- *I'm not sure that `c`*. -/
def notSure (c : Clause) : Clause := fun x ↦ {_w | ¬modalBase₂ ⊆ c x}

/-- *Someone*, *something*, *anyone* and *anything*: some of the two people or things. -/
def someOne : Quantifier (Fin 2) := Quantifier.Det.some univ

/-- A logical form with polarity items indexed by `ι`, all entangled with one another, as
occurrences of *some* and *any* are: the item at each index, the constituents in which
acceptability is evaluated, numbered from the bottom, the lowest of them containing each item, and
the meaning of each constituent as a function of the meanings of the items. -/
structure LF (ι : Type) [DecidableEq ι] where
  item : ι → PolarityItem
  height : ℕ
  position : ι → ℕ
  meaning : ℕ → (ι → Quantifier (Fin 2)) → Clause

namespace LF

variable {ι : Type} [DecidableEq ι] (L : LF ι)

/-- The environment of the constituent `j` with respect to the item `i`: its meaning as a function
of the meaning of `i`, the other items meaning what they mean. -/
def env (i : ι) (j : ℕ) (Q : Quantifier (Fin 2)) : Clause :=
  L.meaning j (Function.update (fun _ ↦ someOne) i Q)

/-- The item `i` is acceptable in the constituent `j`. -/
def Acceptable (i : ι) (j : ℕ) : Prop := (L.item i).Acceptable (L.env i j)

mutual

/-- The item `i` is marked as licensed in the constituent `j`, a domain of it, when it is
acceptable there and every other item there counts as acceptable there. -/
inductive Marked : ι → ℕ → Prop
  | intro {i : ι} {j : ℕ} (hp : L.position i ≤ j) (hj : j < L.height) (ha : L.Acceptable i j)
      (h : ∀ i', i' ≠ i → L.position i' ≤ j → CountsAsAcceptable i' j) : Marked i j

/-- The item `i` counts as acceptable in the constituent `j` when it is acceptable there or has
been marked as licensed in a smaller constituent. -/
inductive CountsAsAcceptable : ι → ℕ → Prop
  | acceptable {i : ι} {j : ℕ} (h : L.Acceptable i j) : CountsAsAcceptable i j
  | marked {i : ι} {j k : ℕ} (hk : k < j) (h : Marked i k) : CountsAsAcceptable i j

end

/-- The logical form is licensed when every item is marked as licensed in one of its domains. -/
def Licensed : Prop := ∀ i, ∃ j, L.Marked i j

/-- Without cyclic evaluation: every item is acceptable in one of its domains together with every
other item there. -/
def LicensedSimultaneously : Prop :=
  ∀ i, ∃ j, L.position i ≤ j ∧ j < L.height ∧ L.Acceptable i j ∧
    ∀ i', i' ≠ i → L.position i' ≤ j → L.Acceptable i' j

-- no item is marked as licensed when, in each domain, an item acceptable there finds another
-- item that is not
theorem not_marked
    (h : ∀ j i, L.position i ≤ j → L.Acceptable i j →
      ∃ i', i' ≠ i ∧ L.position i' ≤ j ∧ ¬L.Acceptable i' j) (i : ι) (j : ℕ) :
    ¬L.Marked i j := by
  induction j using Nat.strong_induction_on generalizing i with
  | _ j ih =>
    rintro ⟨hp, -, ha, h'⟩
    obtain ⟨i', hne, hp', hna⟩ := h j i hp ha
    rcases h' i' hne hp' with ha' | ⟨hk, hm⟩
    exacts [hna ha', ih _ hk i' hm]

end LF

section Acceptability

variable {f : Quantifier (Fin 2) → Clause}

theorem acceptable_any_iff :
    English.PolarityItems.any.Acceptable f ↔ Antitone f ∧ ¬Monotone f := by
  refine ⟨fun h ↦ ?_, fun h ↦ acceptable_of_licensor rfl rfl ?_⟩
  · obtain ⟨ha, hm⟩ := Licenser.carries_ofOperator_iff.1 (h.1 .weak rfl)
    exact ⟨Signature.holdsFor_anti_iff.1 ha, hm⟩
  · exact Licenser.carries_ofOperator_iff.2 ⟨Signature.holdsFor_anti_iff.2 h.1, h.2⟩

theorem acceptable_someItem_iff : someItem.Acceptable f ↔ ¬(Antitone f ∧ ¬Monotone f) := by
  refine ⟨fun h hc ↦ h.2 .weak rfl (Licenser.carries_ofOperator_iff.2
    ⟨Signature.holdsFor_anti_iff.2 hc.1, hc.2⟩), fun h ↦ acceptable_of_antiLicensor rfl rfl ?_⟩
  exact fun hc ↦ h (by
    obtain ⟨ha, hm⟩ := Licenser.carries_ofOperator_iff.1 hc
    exact ⟨Signature.holdsFor_anti_iff.1 ha, hm⟩)

theorem not_antitone_and_not_monotone (h : Monotone f) : ¬(Antitone f ∧ ¬Monotone f) :=
  fun hc ↦ hc.2 h

theorem not_monotone_of_antitone (h : Antitone f) (hne : f ⊥ ≠ f ⊤) : ¬Monotone f := fun hm ↦
  hne (le_antisymm (hm bot_le) (h bot_le))

end Acceptability

/-! #### Monotonicity of the constituents -/

theorem monotone_did₂ (x : Fin 2) : Monotone (did₂ x) := fun _ _ h _ hw ↦ h _ hw

theorem monotone_subject_left (c : Clause) : Monotone fun Q ↦ subject Q c :=
  fun _ _ h _ _ hw ↦ h _ hw

theorem monotone_subject_right : Monotone (subject someOne) :=
  fun _ _ h _ _ hw ↦ Quantifier.Det.monotone_some univ (fun x hx ↦ h x hx) hw

theorem antitone_impossible₂ : Antitone impossible₂ := fun _ _ h x _ hd ↦
  Disjoint.mono_right (h x) hd

theorem antitone_notSure : Antitone notSure := fun _ _ h x _ hn hs ↦ hn (hs.trans (h x))

@[simp]
theorem modalBase₂_ne_empty : modalBase₂ ≠ ∅ :=
  Nonempty.ne_empty ⟨({(0, 0)} : World₂), by simp [modalBase₂]⟩

theorem not_modalBase₂_subset_empty : ¬modalBase₂ ⊆ ∅ := fun h ↦
  modalBase₂_ne_empty (subset_empty_iff.1 h)

/-! #### The logical forms -/

-- the object is item `0`, the subject item `1`

/-- *It is impossible that `subj` stole `obj`*, the subject above its clause: the polarity phrase,
TP and CP of the embedded clause, and the polarity phrase and TP of the matrix. -/
def impossibleSubjObj (obj subj : PolarityItem) : LF (Fin 2) where
  item := ![obj, subj]
  height := 5
  position := ![0, 1]
  meaning
    | 0, Q => fun x ↦ did₂ x (Q 0)
    | 1, Q | 2, Q => subject (Q 1) fun x ↦ did₂ x (Q 0)
    | _, Q => impossible₂ (subject (Q 1) fun x ↦ did₂ x (Q 0))

-- (92b), (93)
/-- *It is impossible that someone stole anything*, with *someone* below *impossible*. -/
def impossibleSomeoneAnything := impossibleSubjObj English.PolarityItems.any someItem

-- (103b), (105a)
/-- *It is impossible that anyone stole something*, with *something* below *impossible*. -/
def impossibleAnyoneSomething := impossibleSubjObj someItem English.PolarityItems.any

-- (98), (102a)
/-- *It's impossible that someone isn't eating anything*, with *someone* below the negation. -/
def impossibleNotSomeoneAnything : LF (Fin 2) where
  item := ![English.PolarityItems.any, someItem]
  height := 5
  position := ![0, 0]
  meaning
    | 0, Q | 1, Q | 2, Q => (subject (Q 1) fun x ↦ did₂ x (Q 0))ᶜ
    | _, Q => impossible₂ (subject (Q 1) fun x ↦ did₂ x (Q 0))ᶜ

-- (98), (102b)
/-- *It's impossible that someone isn't eating anything*, with *someone* above the negation. -/
def impossibleSomeoneNotAnything : LF (Fin 2) where
  item := ![English.PolarityItems.any, someItem]
  height := 5
  position := ![0, 1]
  meaning
    | 0, Q => fun x ↦ (did₂ x (Q 0))ᶜ
    | 1, Q | 2, Q => subject (Q 1) fun x ↦ (did₂ x (Q 0))ᶜ
    | _, Q => impossible₂ (subject (Q 1) fun x ↦ (did₂ x (Q 0))ᶜ)

/-- *I'm not sure that `subj` understood `obj`*, both items in the embedded polarity phrase. -/
def notSureSubjObj (obj subj : PolarityItem) : LF (Fin 2) where
  item := ![obj, subj]
  height := 5
  position := ![0, 0]
  meaning
    | 0, Q | 1, Q | 2, Q => subject (Q 1) fun x ↦ did₂ x (Q 0)
    | _, Q => notSure (subject (Q 1) fun x ↦ did₂ x (Q 0))

-- (122b), (122c)
/-- *I'm not sure that someone understood anything*. -/
def notSureSomeoneAnything := notSureSubjObj English.PolarityItems.any someItem

/-! #### Acceptability in the logical forms -/

theorem monotone_did₂_fun : Monotone fun Q (x : Fin 2) ↦ did₂ x Q := fun _ _ h x ↦ monotone_did₂ x h

theorem impossible₂_bot_ne_top {f : Quantifier (Fin 2) → Clause} (h0 : f ⊥ = ⊥) (h1 : f ⊤ = ⊤) :
    impossible₂ (f ⊥) ≠ impossible₂ (f ⊤) := fun h ↦ by
  have := congrArg (fun c ↦ (∅ : World₂) ∈ c 0) h
  simp [impossible₂, h0, h1] at this

theorem compl_bot_ne_top {f : Quantifier (Fin 2) → Clause} (h0 : f ⊥ = ⊥) (h1 : f ⊤ = ⊤) :
    (f ⊥)ᶜ ≠ (f ⊤)ᶜ := by
  simp [h0, h1]

theorem notSure_bot_ne_top {f : Quantifier (Fin 2) → Clause} (h0 : f ⊥ = ⊥) (h1 : f ⊤ = ⊤) :
    notSure (f ⊥) ≠ notSure (f ⊤) := fun h ↦ by
  have := congrArg (fun c ↦ (∅ : World₂) ∈ c 0) h
  simp [notSure, h0, h1] at this

theorem did₂_fun_bot : (fun x ↦ did₂ x ⊥) = ⊥ :=
  rfl

theorem did₂_fun_top : (fun x ↦ did₂ x ⊤) = ⊤ :=
  rfl

@[simp]
theorem subject_bot (c : Clause) : subject ⊥ c = ⊥ :=
  rfl

@[simp]
theorem subject_top (c : Clause) : subject ⊤ c = ⊤ :=
  rfl

@[simp]
theorem subject_someOne_bot : subject someOne ⊥ = ⊥ := by
  ext; simp [subject, someOne, Quantifier.Det.some]

@[simp]
theorem subject_someOne_top : subject someOne ⊤ = ⊤ := by
  ext; simp [subject, someOne, Quantifier.Det.some]

-- the environments, the other item meaning what it means: in the embedded clause the item is in an
-- upward-entailing environment, below *impossible* or *not sure* in a downward-entailing one

section ImpossibleSubjObj

variable {obj subj : PolarityItem}

theorem monotone_impossibleSubjObj_env {i : Fin 2} {j : ℕ} (hj : j ≤ 2) :
    Monotone ((impossibleSubjObj obj subj).env i j) := by
  interval_cases j <;> fin_cases i
  · exact monotone_did₂_fun
  · exact fun _ _ _ ↦ le_rfl
  all_goals first
    | exact monotone_subject_right.comp monotone_did₂_fun
    | exact monotone_subject_left _

theorem antitone_impossibleSubjObj_env_zero (k : ℕ) :
    Antitone ((impossibleSubjObj obj subj).env 0 (k + 3)) ∧
      ¬Monotone ((impossibleSubjObj obj subj).env 0 (k + 3)) := by
  have ha : Antitone fun Q ↦ impossible₂ (subject someOne fun x ↦ did₂ x Q) :=
    antitone_impossible₂.comp_monotone (monotone_subject_right.comp monotone_did₂_fun)
  refine ⟨ha, not_monotone_of_antitone ha (impossible₂_bot_ne_top
    (f := fun Q ↦ subject someOne fun x ↦ did₂ x Q) ?_ ?_)⟩
  · show subject someOne (fun x ↦ did₂ x ⊥) = ⊥
    rw [did₂_fun_bot, subject_someOne_bot]
  · show subject someOne (fun x ↦ did₂ x ⊤) = ⊤
    rw [did₂_fun_top, subject_someOne_top]

theorem antitone_impossibleSubjObj_env_one (k : ℕ) :
    Antitone ((impossibleSubjObj obj subj).env 1 (k + 3)) ∧
      ¬Monotone ((impossibleSubjObj obj subj).env 1 (k + 3)) := by
  have ha : Antitone fun Q ↦ impossible₂ (subject Q fun x ↦ did₂ x someOne) :=
    antitone_impossible₂.comp_monotone (monotone_subject_left _)
  exact ⟨ha, not_monotone_of_antitone ha (impossible₂_bot_ne_top
    (f := fun Q ↦ subject Q fun x ↦ did₂ x someOne) (subject_bot _) (subject_top _))⟩

end ImpossibleSubjObj

section Acceptability

variable {f : Quantifier (Fin 2) → Clause}

theorem not_acceptable_any_of_monotone (h : Monotone f) :
    ¬English.PolarityItems.any.Acceptable f := fun ha ↦ (acceptable_any_iff.1 ha).2 h

theorem not_acceptable_someItem (h : Antitone f ∧ ¬Monotone f) : ¬someItem.Acceptable f :=
  fun ha ↦ acceptable_someItem_iff.1 ha h

theorem acceptable_someItem_of_monotone (h : Monotone f) : someItem.Acceptable f :=
  acceptable_someItem_iff.2 (not_antitone_and_not_monotone h)

end Acceptability

-- (92b)
theorem not_licensed_impossibleSomeoneAnything : ¬impossibleSomeoneAnything.Licensed := fun h ↦ by
  obtain ⟨j, hj⟩ := h 0
  refine LF.not_marked _ (fun j i _ ha ↦ ?_) 0 j hj
  rcases le_or_gt j 2 with hj2 | hj2
  · have h0 : ¬impossibleSomeoneAnything.Acceptable 0 j :=
      not_acceptable_any_of_monotone (monotone_impossibleSubjObj_env hj2)
    fin_cases i
    · exact absurd ha h0
    · exact ⟨0, by decide, Nat.zero_le _, h0⟩
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hj2
    have h1 : ¬impossibleSomeoneAnything.Acceptable 1 (k + 3) :=
      not_acceptable_someItem (antitone_impossibleSubjObj_env_one k)
    fin_cases i
    · exact ⟨1, by decide, by simp [impossibleSomeoneAnything, impossibleSubjObj], h1⟩
    · exact absurd ha h1

theorem marked_impossibleAnyoneSomething : impossibleAnyoneSomething.Marked 0 0 :=
  .intro le_rfl (by decide) (acceptable_someItem_of_monotone
    (monotone_impossibleSubjObj_env (by decide))) fun i' hi' hp ↦ by
    fin_cases i'
    · exact absurd rfl hi'
    · exact absurd hp (by decide)

-- (103b)
theorem licensed_impossibleAnyoneSomething : impossibleAnyoneSomething.Licensed := fun i ↦ by
  fin_cases i
  · exact ⟨0, marked_impossibleAnyoneSomething⟩
  · refine ⟨3, .intro (by decide) (by decide)
      (acceptable_any_iff.2 (antitone_impossibleSubjObj_env_one 0)) fun i' hi' _ ↦ ?_⟩
    fin_cases i'
    · exact .marked (by decide) marked_impossibleAnyoneSomething
    · exact absurd rfl hi'

theorem not_licensedSimultaneously_impossibleAnyoneSomething :
    ¬impossibleAnyoneSomething.LicensedSimultaneously := fun h ↦ by
  obtain ⟨j, hp, -, ha, h'⟩ := h 1
  rcases le_or_gt j 2 with hj2 | hj2
  · exact not_acceptable_any_of_monotone (monotone_impossibleSubjObj_env hj2) ha
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hj2
    exact not_acceptable_someItem (antitone_impossibleSubjObj_env_zero k)
      (h' 0 (by decide) (Nat.zero_le _))

/-- With *some* and *any* entangled, *it is impossible that someone stole anything* is
anti-licensed and *it is impossible that anyone stole something* licensed, *something* being
marked as licensed in its own clause before *anyone* is evaluated; evaluated together rather than
cyclically, the second would be anti-licensed as well. -/
theorem cyclicity :
    ¬impossibleSomeoneAnything.Licensed ∧ impossibleAnyoneSomething.Licensed ∧
      ¬impossibleAnyoneSomething.LicensedSimultaneously :=
  ⟨not_licensed_impossibleSomeoneAnything, licensed_impossibleAnyoneSomething,
    not_licensedSimultaneously_impossibleAnyoneSomething⟩

-- (98), (102a): below the negation the environments are downward entailing, below *impossible*
-- upward entailing again
theorem not_licensed_impossibleNotSomeoneAnything :
    ¬impossibleNotSomeoneAnything.Licensed := fun h ↦ by
  obtain ⟨j, hj⟩ := h 0
  refine LF.not_marked _ (fun j i _ ha ↦ ?_) 0 j hj
  rcases le_or_gt j 2 with hj2 | hj2
  · have h1 : ¬impossibleNotSomeoneAnything.Acceptable 1 j := by
      have ha' : Antitone fun Q ↦ (subject Q fun x ↦ did₂ x someOne)ᶜ :=
        compl_anti.comp_monotone (monotone_subject_left _)
      have hc : Antitone (impossibleNotSomeoneAnything.env 1 j) ∧
          ¬Monotone (impossibleNotSomeoneAnything.env 1 j) := by
        interval_cases j <;> exact ⟨ha', not_monotone_of_antitone ha'
          (compl_bot_ne_top (f := fun Q ↦ subject Q fun x ↦ did₂ x someOne) (subject_bot _)
            (subject_top _))⟩
      exact not_acceptable_someItem hc
    fin_cases i
    · exact ⟨1, by decide, Nat.zero_le _, h1⟩
    · exact absurd ha h1
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hj2
    have h0 : ¬impossibleNotSomeoneAnything.Acceptable 0 (k + 3) :=
      not_acceptable_any_of_monotone (f := fun Q ↦ impossible₂
        (subject someOne fun x ↦ did₂ x Q)ᶜ) (antitone_impossible₂.comp
          (compl_anti.comp_monotone (monotone_subject_right.comp monotone_did₂_fun)))
    fin_cases i
    · exact absurd ha h0
    · exact ⟨0, by decide, Nat.zero_le _, h0⟩

theorem marked_impossibleSomeoneNotAnything : impossibleSomeoneNotAnything.Marked 0 0 := by
  have ha : Antitone fun Q (x : Fin 2) ↦ (did₂ x Q)ᶜ := fun _ _ h x ↦ compl_le_compl
    (monotone_did₂ x h)
  refine .intro le_rfl (by decide) (acceptable_any_iff.2 ⟨ha, not_monotone_of_antitone ha ?_⟩)
    fun i' hi' hp ↦ ?_
  · exact compl_bot_ne_top (f := fun Q x ↦ did₂ x Q) did₂_fun_bot did₂_fun_top
  · fin_cases i'
    · exact absurd rfl hi'
    · exact absurd hp (by decide)

-- (98), (102b): *someone* above the negation is marked as licensed in the embedded TP once
-- *anything* is in the polarity phrase below it
theorem licensed_impossibleSomeoneNotAnything : impossibleSomeoneNotAnything.Licensed :=
  fun i ↦ by
  fin_cases i
  · exact ⟨0, marked_impossibleSomeoneNotAnything⟩
  · refine ⟨1, .intro le_rfl (by decide) (acceptable_someItem_of_monotone
      (f := fun Q ↦ subject Q fun x ↦ (did₂ x someOne)ᶜ) (monotone_subject_left _))
      fun i' hi' _ ↦ ?_⟩
    fin_cases i'
    · exact .marked (by decide) marked_impossibleSomeoneNotAnything
    · exact absurd rfl hi'

section NotSureSubjObj

variable {obj subj : PolarityItem}

theorem monotone_notSureSubjObj_env {i : Fin 2} {j : ℕ} (hj : j ≤ 2) :
    Monotone ((notSureSubjObj obj subj).env i j) := by
  interval_cases j <;> fin_cases i
  all_goals first
    | exact monotone_subject_right.comp monotone_did₂_fun
    | exact monotone_subject_left _

theorem antitone_notSureSubjObj_env_zero (k : ℕ) :
    Antitone ((notSureSubjObj obj subj).env 0 (k + 3)) ∧
      ¬Monotone ((notSureSubjObj obj subj).env 0 (k + 3)) := by
  have ha : Antitone fun Q ↦ notSure (subject someOne fun x ↦ did₂ x Q) :=
    antitone_notSure.comp_monotone (monotone_subject_right.comp monotone_did₂_fun)
  refine ⟨ha, not_monotone_of_antitone ha (notSure_bot_ne_top
    (f := fun Q ↦ subject someOne fun x ↦ did₂ x Q) ?_ ?_)⟩
  · show subject someOne (fun x ↦ did₂ x ⊥) = ⊥
    rw [did₂_fun_bot, subject_someOne_bot]
  · show subject someOne (fun x ↦ did₂ x ⊤) = ⊤
    rw [did₂_fun_top, subject_someOne_top]

theorem antitone_notSureSubjObj_env_one (k : ℕ) :
    Antitone ((notSureSubjObj obj subj).env 1 (k + 3)) ∧
      ¬Monotone ((notSureSubjObj obj subj).env 1 (k + 3)) := by
  have ha : Antitone fun Q ↦ notSure (subject Q fun x ↦ did₂ x someOne) :=
    antitone_notSure.comp_monotone (monotone_subject_left _)
  exact ⟨ha, not_monotone_of_antitone ha (notSure_bot_ne_top
    (f := fun Q ↦ subject Q fun x ↦ did₂ x someOne) (subject_bot _) (subject_top _))⟩

-- below *not sure* the environment of the subject is not anti-additive: in every world of the
-- modal base the first person or the second did something, but in some the first did nothing and
-- in some the second did nothing
theorem not_isAntiAdditive_notSureSubjObj_env :
    ¬IsAntiAdditive ((notSureSubjObj obj subj).env 1 3) := fun h ↦ by
  have := congrArg (fun c ↦ (∅ : World₂) ∈ c 0)
    (h (Quantifier.Det.some {0}) (Quantifier.Det.some {1}))
  simp [LF.env, notSureSubjObj, notSure, subject, did₂, modalBase₂, someOne,
    Quantifier.Det.some] at this
  refine absurd (this.2 ⟨⟨{(1, 0)}, by simp, by simp⟩, ⟨{(0, 0)}, by simp, by simp⟩⟩) ?_
  rintro ⟨w, ⟨⟨x, y⟩, hxy⟩, h0, h1⟩
  fin_cases x
  exacts [h0 ⟨y, hxy⟩, h1 ⟨y, hxy⟩]

end NotSureSubjObj

-- (122b), (122c)
theorem not_licensed_notSureSomeoneAnything : ¬notSureSomeoneAnything.Licensed := fun h ↦ by
  obtain ⟨j, hj⟩ := h 0
  refine LF.not_marked _ (fun j i _ ha ↦ ?_) 0 j hj
  rcases le_or_gt j 2 with hj2 | hj2
  · have h0 : ¬notSureSomeoneAnything.Acceptable 0 j :=
      not_acceptable_any_of_monotone (monotone_notSureSubjObj_env hj2)
    fin_cases i
    · exact absurd ha h0
    · exact ⟨0, by decide, Nat.zero_le _, h0⟩
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hj2
    have h1 : ¬notSureSomeoneAnything.Acceptable 1 (k + 3) :=
      not_acceptable_someItem (antitone_notSureSubjObj_env_one k)
    fin_cases i
    · exact ⟨1, by decide, Nat.zero_le _, h1⟩
    · exact absurd ha h1

-- with the anti-additive classification, *someone* and *anything* are both acceptable below
-- *not sure*
theorem licensed_notSureSubjObj_someone :
    (notSureSubjObj English.PolarityItems.any English.PolarityItems.someone).Licensed := by
  have h0 : (notSureSubjObj English.PolarityItems.any English.PolarityItems.someone).Acceptable
      0 3 := acceptable_any_iff.2 (antitone_notSureSubjObj_env_zero 0)
  have h1 : (notSureSubjObj English.PolarityItems.any English.PolarityItems.someone).Acceptable
      1 3 := acceptable_of_antiLicensor rfl rfl fun hc ↦ not_isAntiAdditive_notSureSubjObj_env
    (Signature.holdsFor_antiAdd_iff.1 (Licenser.carries_ofOperator_iff.1 hc).1).1
  intro i
  refine ⟨3, .intro (by fin_cases i <;> decide) (by decide) (by fin_cases i <;> assumption)
    fun i' hi' _ ↦ .acceptable ?_⟩
  fin_cases i <;> fin_cases i' <;> first | exact absurd rfl hi' | assumption

/-- Below *not impossible … not* and below *not sure*, environments are downward entailing without
being anti-additive. Blocked by downward entailment, *some* is anti-licensed in both, with
narrowest scope in the first and entangled with *anything* in the second, as judged; blocked only
by anti-additivity, as the Fragment classifies *someone*, it would be licensed in both. -/
theorem downwardEntailment :
    (¬notImpossibleNot.Licenses someItem ∧
        notImpossibleNot.Licenses English.PolarityItems.someone) ∧
      ¬notSureSomeoneAnything.Licensed ∧
        (notSureSubjObj English.PolarityItems.any English.PolarityItems.someone).Licensed :=
  ⟨⟨notImpossibleNot_someone.2, notImpossibleNot_someone.1⟩, not_licensed_notSureSomeoneAnything,
    licensed_notSureSubjObj_someone⟩


/-! ### The judgments -/

/-- The path of a row's item, read from the negation of its own clause, the expressions of the
superordinate clause and the connective. -/
noncomputable def path? (e : Datum) : Option (Path (Quantifier (Fin 2)) (Set World)) :=
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

/-- The entry of a row's item. -/
def item? (e : Datum) : Option PolarityItem :=
  match e.feature? "item" with
  | some "quoi que ce soit" => some quoiQueCeSoit
  | some "any" => some English.PolarityItems.any
  | some "some" => some someItem
  | _ => none

/-- The licensing of a row's item in its path. -/
noncomputable def licensing? (e : Datum) : Option Prop :=
  (path? e).bind fun p ↦ (item? e).map p.Licenses

/-- The judgment on which a row's item is evaluated: the narrowest scope of *some*, the sentence
otherwise. -/
def judgment? (e : Datum) : Option Judgment :=
  if e.feature? "item" = some "some" then e.readings.lookup "narrowest scope of some"
  else some e.judgment

-- an item is judged acceptable exactly when it meets the licensing condition in its path
theorem rows_licensing : ∀ e ∈ Examples.all, ∀ p ∈ licensing? e, ∀ j ∈ judgment? e,
    (j = .acceptable ↔ p) := by
  simp only [Examples.all, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rintro p ⟨⟩ j ⟨⟩ <;>
    first
      | exact iff_of_false (by decide) not_licenses_notImpossible
      | exact iff_of_true rfl licenses_impossibleNot
      | exact iff_of_true rfl licenses_ifImpossible
      | exact iff_of_true rfl licenses_notImpossibleNot
      | exact iff_of_false (by decide) not_licenses_clausemateNot
      | exact iff_of_true rfl licenses_notClaim
      | exact iff_of_true rfl licenses_impossibleBare
      | exact iff_of_true rfl licenses_notSureNot
      | exact iff_of_true rfl licenses_impossibleNot_some
      | exact iff_of_true rfl licenses_ifNot
      | exact iff_of_true rfl licenses_notThatImpossibleNot
      | exact iff_of_false (by decide) not_licenses_notImpossibleNot_some
      | exact iff_of_false (by decide) not_licenses_notAnd
      | exact iff_of_true rfl licenses_notOr
      | exact iff_of_true rfl licenses_notAnd
      | exact iff_of_false (by decide) not_licenses_notOr

theorem readCount_licensing : Datum.ReadCount licensing? Examples.all 16 := by
  decide +kernel

/-- The logical form of a reading of a row with two items, read from its subject, object,
superordinate expression and clausemate negation, and from the scopes the reading names. -/
def lf? (e : Datum) (reading : String) : Option (LF (Fin 2)) :=
  match e.feature? "subject", e.feature? "object", e.feature? "superordinate",
    e.feature? "clause", reading with
  | some "someone", some "anything", some "impossible", some "none", "IMPOS.≫SOME" =>
      some impossibleSomeoneAnything
  | some "anyone", some "something", some "impossible", some "none", "IMPOS.≫SOME" =>
      some impossibleAnyoneSomething
  | some "someone", some "anything", some "impossible", some "negation",
      "IMPOS.≫NEG≫SOME≫ANY" => some impossibleNotSomeoneAnything
  | some "someone", some "anything", some "impossible", some "negation",
      "IMPOS.≫SOME≫NEG≫ANY" => some impossibleSomeoneNotAnything
  | some "someone", some "anything", some "not sure", some "none", "NEG≫SOME" =>
      some notSureSomeoneAnything
  | _, _, _, _, _ => none

/-- The licensing of the logical form of a reading of a row. -/
def entanglement? (e : Datum) (reading : String) : Option Prop :=
  (lf? e reading).map LF.Licensed

-- a reading is judged acceptable exactly when its logical form is licensed
theorem rows_entanglement : ∀ e ∈ Examples.all, ∀ r ∈ e.readings, ∀ p ∈ entanglement? e r.1,
    (r.2 = .acceptable ↔ p) := by
  simp only [Examples.all, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    intro r hr <;>
    simp only [Examples.ex18, Examples.ex19, Examples.ex24, Examples.ex32, Examples.ex41a,
      Examples.ex42a, Examples.ex42b, Examples.ex46a, Examples.ex46b, Examples.ex48a,
      Examples.ex48b, Examples.ex48c, Examples.ex50e, Examples.ex51b, Examples.ex56d,
      Examples.ex56e, Examples.ex92b, Examples.ex98, Examples.ex103b, Examples.ex122b,
      List.mem_cons, List.not_mem_nil, or_false] at hr <;>
    first
      | (subst hr; rintro p ⟨⟩)
      | (rcases hr with rfl | rfl <;> rintro p ⟨⟩)
  exacts [iff_of_false (by decide) not_licensed_impossibleSomeoneAnything,
    iff_of_false (by decide) not_licensed_impossibleNotSomeoneAnything,
    iff_of_true rfl licensed_impossibleSomeoneNotAnything,
    iff_of_true rfl licensed_impossibleAnyoneSomething,
    iff_of_false (by decide) not_licensed_notSureSomeoneAnything]

/-- The scope readings of a row that have a logical form. -/
def readings? (e : Datum) : Option (List String) :=
  match e.readings.filterMap fun r ↦ (lf? e r.1).map fun _ ↦ r.1 with
  | [] => none
  | l => some l

theorem readCount_entanglement : Datum.ReadCount readings? Examples.all 4 := by
  decide +kernel

end Homer2021
