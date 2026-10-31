module

public import Linglib.Semantics.Polarity.Environment
public import Linglib.Fragments.English.PolarityItems
public import Linglib.Data.Examples.Homer2021
public import Studies.Chierchia2004

/-!
# Homer (2021): Domains of polarity items

This file formalizes the localist, environment-based theory of polarity items: an item is
evaluated in its domains, the constituents containing it and the polarity head of their own
clause, and it is acceptable only if some domain carries the strength of negation that licenses
it, or some domain lacks the strength that blocks it. For *quoi que ce soit*, *any* and, as the
paper concludes, *some*, that strength is downward entailment. A second downward-entailing
expression in a domain undoes the first, so [*quoi que ce soit* is anti-licensed under *pas
impossible* and licensed again by a negation in its own clause](##Homer2021.flipFlop_npi), and
[*some* is anti-licensed under clausemate negation, rescued by a superordinate *impossible* and
anti-licensed again under *not impossible*](##Homer2021.flipFlop_ppi). [*Some* survives three
downward-entailing expressions](##Homer2021.localist_ppi) in a sentence downward entailing with
respect to it, since a smaller domain is not. A scalar implicature can [make a domain
non-monotone](##Homer2021.not_monotone_notConn_conj): [*any* is anti-licensed and *some* licensed
under *not … and*, but not under *not … or*](##Homer2021.disruption). A superordinate *not
impossible* is downward entailing without being anti-additive, so [an item blocked only by
anti-additive domains would survive below it](##Homer2021.notImpossibleNot_someone), against the
judgment on narrowest-scope *some*; the paper argues for downward entailment from entanglement
instead.

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

## Errata

* The strengthened meaning conjoins the negation of the weakest alternative asymmetrically entailing
  the constituent, which is undefined when there is none: under *not … or* and in every
  constituent without a scalar term. Such a constituent is left as it is, as by Krifka's rule.
  The alternatives of a constituent without a scalar term are given as its meaning rather than
  the singleton of it.

## TODO

* Entanglement and cyclic marking of polarity items, and the paper's own argument that *some* is
  blocked by downward entailment, from *at most five people sold someone anything* and *I'm not
  sure that someone understood anything*.
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
  ⟨fun _ hs ↦ Option.mem_some_iff.1 hs ▸ ⟨[], by simp,
    impossibleNot.carries_weak_of_sign_eq_neg_one (by simp [impossibleNot]; decide)
      (by simp [impossibleNot])⟩,
    fun _ hs ↦ absurd hs (by simp [quoiQueCeSoit])⟩

theorem licenses_notImpossibleNot : notImpossibleNot.Licenses quoiQueCeSoit :=
  ⟨fun _ hs ↦ Option.mem_some_iff.1 hs ▸ ⟨[], by simp,
    notImpossibleNot.carries_weak_of_sign_eq_neg_one (by simp [notImpossibleNot]; decide)
      (by simp [notImpossibleNot])⟩,
    fun _ hs ↦ absurd hs (by simp [quoiQueCeSoit])⟩

theorem licenses_ifImpossible : ifImpossible.Licenses quoiQueCeSoit :=
  ⟨fun _ hs ↦ Option.mem_some_iff.1 hs ▸ ⟨[impossible, 1, 1], by simp [ifImpossible],
    ifImpossible.carries_weak_of_sign_eq_neg_one (by simp [ifImpossible]; decide)
      (by simp [ifImpossible])⟩,
    fun _ hs ↦ absurd hs (by simp [quoiQueCeSoit])⟩

theorem not_licenses_clausemateNot : ¬clausemateNot.Licenses someItem :=
  clausemateNot.not_licenses_of_mem_antiLicensor rfl fun t ht ↦ by
    simp [clausemateNot] at ht
    rcases ht with rfl | rfl <;>
      exact clausemateNot.carries_weak_of_sign_eq_neg_one (by simp [clausemateNot]; decide)
        (by simp [clausemateNot])

theorem licenses_notClaim : notClaim.Licenses someItem :=
  ⟨fun _ hs ↦ absurd hs (by simp [someItem]), fun _ hs ↦ Option.mem_some_iff.1 hs ▸
    ⟨[], by simp, notClaim.not_carries_of_sign_eq_one (by simp [notClaim]; decide)⟩⟩

theorem licenses_impossibleBare : impossibleBare.Licenses someItem :=
  ⟨fun _ hs ↦ absurd hs (by simp [someItem]), fun _ hs ↦ Option.mem_some_iff.1 hs ▸
    ⟨[], by simp, impossibleBare.not_carries_of_sign_eq_one (by simp [impossibleBare]; decide)⟩⟩

theorem licenses_notSureNot : notSureNot.Licenses someItem :=
  ⟨fun _ hs ↦ absurd hs (by simp [someItem]), fun _ hs ↦ Option.mem_some_iff.1 hs ▸
    ⟨[negation * necessity, 1, 1], by simp [notSureNot],
      notSureNot.not_carries_of_sign_eq_one (by simp [notSureNot]; decide)⟩⟩

theorem licenses_impossibleNot_some : impossibleNot.Licenses someItem :=
  ⟨fun _ hs ↦ absurd hs (by simp [someItem]), fun _ hs ↦ Option.mem_some_iff.1 hs ▸
    ⟨[impossible, 1, 1], by simp [impossibleNot],
      impossibleNot.not_carries_of_sign_eq_one (by simp [impossibleNot]; decide)⟩⟩

theorem not_licenses_notImpossibleNot_some : ¬notImpossibleNot.Licenses someItem :=
  notImpossibleNot.not_licenses_of_mem_antiLicensor rfl fun t ht ↦ by
    simp [notImpossibleNot] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl <;>
      exact notImpossibleNot.carries_weak_of_sign_eq_neg_one (by simp [notImpossibleNot]; decide)
        (by simp [notImpossibleNot])

theorem licenses_ifNot : ifNot.Licenses someItem :=
  ⟨fun _ hs ↦ absurd hs (by simp [someItem]), fun _ hs ↦ Option.mem_some_iff.1 hs ▸
    ⟨[conditional consequent, 1], by simp [ifNot],
      ifNot.not_carries_of_sign_eq_one (by simp [ifNot, conditional]; decide)⟩⟩

theorem licenses_notThatImpossibleNot : notThatImpossibleNot.Licenses someItem :=
  ⟨fun _ hs ↦ absurd hs (by simp [someItem]), fun _ hs ↦ Option.mem_some_iff.1 hs ▸
    ⟨[impossible, 1, 1], by simp [notThatImpossibleNot],
      notThatImpossibleNot.not_carries_of_sign_eq_one (by simp [notThatImpossibleNot]; decide)⟩⟩

theorem antitone_notThatImpossibleNot :
    Antitone (notThatImpossibleNot.environment notThatImpossibleNot.layers) :=
  notThatImpossibleNot.antitone_environment (by simp [notThatImpossibleNot]; decide)

end FlipFlop

/-- *Quoi que ce soit* is anti-licensed under *pas impossible*, two clausemate downward-entailing
expressions, and licensed again when its own clause is negated. -/
theorem flipFlop_npi :
    ¬notImpossible.Licenses quoiQueCeSoit ∧ notImpossibleNot.Licenses quoiQueCeSoit :=
  ⟨not_licenses_notImpossible, licenses_notImpossibleNot⟩

/-- *Some* is anti-licensed under clausemate negation, rescued by a superordinate *impossible*,
and anti-licensed again under a superordinate *not impossible*. -/
theorem flipFlop_ppi :
    ¬clausemateNot.Licenses someItem ∧ impossibleNot.Licenses someItem ∧
      ¬notImpossibleNot.Licenses someItem :=
  ⟨not_licenses_clausemateNot, licenses_impossibleNot_some, not_licenses_notImpossibleNot_some⟩

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

/-- Below *not impossible … not*, the superordinate polarity phrase is downward entailing but not
anti-additive with respect to the indefinite, so an item blocked only by anti-additive domains,
as the Fragment classifies *someone*, is licensed there, while *some*, blocked by downward
entailment, is not, as the judgment on its narrowest scope requires. -/
theorem notImpossibleNot_someone :
    notImpossibleNot.Licenses English.PolarityItems.someone ∧
      ¬notImpossibleNot.Licenses someItem := by
  refine ⟨⟨fun _ hs ↦ absurd hs (by simp [English.PolarityItems.someone]), fun _ hs ↦ ?_⟩,
    not_licenses_notImpossibleNot_some⟩
  obtain rfl := Option.mem_some_iff.1 hs
  refine ⟨[negation * impossible, 1, 1], by simp [notImpossibleNot, embedded, path], fun hc ↦ ?_⟩
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

theorem not_licenses_notAnd : ¬notAnd.Licenses English.PolarityItems.any := fun h ↦
  let ⟨_, ht, hc⟩ := h.1 .weak rfl
  not_carries_notAnd ht hc

theorem licenses_notAnd : notAnd.Licenses someItem :=
  ⟨fun _ hs ↦ absurd hs (by simp [someItem]), fun _ _ ↦ ⟨[], by simp, not_carries_notAnd (by simp)⟩⟩

theorem licenses_notOr : notOr.Licenses English.PolarityItems.any :=
  ⟨fun _ hs ↦ Option.mem_some_iff.1 hs ▸ ⟨[], by simp, carries_notOr (by simp)⟩,
    fun _ hs ↦ absurd hs (by simp [English.PolarityItems.any])⟩

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
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
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

end Homer2021
