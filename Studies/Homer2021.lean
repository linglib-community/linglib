module

public import Linglib.Semantics.PolarityItem.Environment
public import Linglib.Data.Examples.Homer2021
public import Studies.Chierchia2004
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.FinCases

/-!
# Domains of polarity items

A polarity item is evaluated in its *domains*, the constituents that contain it and the polarity
head of their own clause. The *environment* of the item in a domain is the meaning of the domain
as a function of the meaning of the item, and the item is *acceptable* in the domain when the
environment has the monotonicity that the item requires: *quoi que ce soit* and *any* require a
downward-entailing environment, and *some* requires an environment that is not downward entailing.
An item is licensed only if it is acceptable in one of its domains.

A second downward-entailing expression in a domain undoes the first. *Quoi que ce soit* is
anti-licensed under *pas impossible*, two expressions that share every domain, and licensed again
when its own clause is negated; *some* is anti-licensed under a clausemate negation, licensed
under a further *impossible*, and anti-licensed again under *not impossible*. A scalar implicature
makes a domain non-monotone: under *not … and*, *any* is anti-licensed and *some* licensed, and
under *not … or* the reverse holds.

Occurrences of *some* and *any* are *entangled*: an item is marked as licensed in a domain only if
it is acceptable there and every other item of the domain counts as acceptable there, being
acceptable or marked as licensed in a smaller constituent. Below *impossible*, *anyone …
something* is licensed, *something* being marked as licensed in its own clause first, and
*someone … anything* is not. Below *not sure*, which is downward entailing without being
anti-additive, *someone … anything* is anti-licensed, where a *some* blocked only by
anti-additivity would be licensed. *Some* and *any* are never acceptable in the same constituent,
and where the environment is not constant exactly one of them is.

## Implementation notes

* Licensing of a single item is the existence of a domain that admits it, a biconditional where
  the condition is stated in the source as a necessary one.
* A negative polarity item is acceptable in an environment that is downward entailing and not
  upward entailing, so a constant environment admits neither *any* nor *some*.
* An item enters through its class, the strength of negation that licenses or blocks it. The
  entries of the language files do not classify items, and the rows are not linked to them.
* A world records a fact independent of the polarity item and which of two things the subject did.
  The environment of a domain is a function of the meaning of the indefinite, a quantifier over
  things, evaluated at the things the subject did: the abstraction over the position of the item.
* Each clause contributes its polarity phrase, whose head is the layer of the minimal domain, and
  its TP and, when embedded, CP, which are identity layers. A superordinate polarity phrase
  composes its polarity head with the predicate below it.
* The modals quantify over a fixed modal base, the worlds in which something was done. *Sure* and
  *claim* are both necessity, only their upward monotonicity mattering. Over the base of the
  sentences with two indefinites, *not sure* is not anti-additive: in every world of the base the
  first person or the second did something, in some the first did nothing, and in some the second
  did nothing.
* A conditional is the material conditional with its consequent fixed, so the CP of the
  conditional clause denotes the whole conditional. This is downward entailing in the antecedent,
  which is all the sign needs, where a natural-language conditional is only Strawson downward
  entailing.
* The environments of *not … and* and *not … or* are the strong values of [chierchia-2004],
  negation being its *doubt*. The source works the strengthened meaning through for *not every*;
  the connectives are treated here in the same way. Tense adds no scalar alternatives, so the
  strengthened TP has the meaning of the strengthened polarity phrase.
* The *when*-clause of the sentence with clausemate negation is left out, as in its logical form.
* In the sentences with two indefinites, a world records which of two people did which of two
  things, every two items are entangled, and the constituents are numbered from the bottom of the
  clausal spine. A constituent below the position of the subject denotes a proposition for each
  value of its trace.

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

theorem holdsFor_did : ProjectivitySignature.HoldsFor .addMult did :=
  ProjectivitySignature.holdsFor_addMult_iff.2 ⟨⟨fun _ _ ↦ rfl, rfl⟩, fun _ _ ↦ rfl, rfl⟩

@[simp]
theorem did_bot : did ⊥ = ∅ :=
  rfl

@[simp]
theorem did_top : did ⊤ = univ :=
  rfl

/-! ### Layers -/

/-- A layer of meaning between two domains. -/
abbrev Layer := Environment (Set World) (Set World)

/-- The modal base: the worlds in which the subject did something. -/
def modalBase : Set World := {w | w.2.Nonempty}

@[simp]
theorem modalBase_ne_empty : modalBase ≠ ∅ :=
  Nonempty.ne_empty ⟨((false, {0}) : World), by simp [modalBase]⟩

/-- *It is impossible that `p`*: no world of the modal base is a `p`-world. -/
def impossible : Layer :=
  ⟨fun p ↦ {_w | Disjoint modalBase p}, .antiAdd, ProjectivitySignature.holdsFor_antiAdd_iff.2
    ⟨fun _ _ ↦ by ext; simp, by simp⟩⟩

/-- *I am sure that `p`*, *I claim that `p`*: every world of the modal base is a `p`-world. -/
def necessity : Layer :=
  ⟨fun p ↦ {_w | modalBase ⊆ p}, .mono,
    ProjectivitySignature.holdsFor_mono_iff.2 fun _ _ h _ hp ↦ (hp : modalBase ⊆ _).trans h⟩

/-- *If `p`, `q`*, the material conditional with the consequent fixed. -/
def conditional (q : Set World) : Layer :=
  ⟨fun p ↦ pᶜ ∪ q, .anti,
    ProjectivitySignature.holdsFor_anti_iff.2 fun _ _ h ↦ union_subset_union_left _
      (compl_subset_compl.2 h)⟩

/-- The consequent of a conditional: *I will apologize to him*, *he has no notion of French at
all*. -/
def consequent : Set World := {w | w.1}

/-! ### Paths -/

/-- The path of the indefinite in a clause with polarity head `pol`, under the layers `t`,
outermost first. -/
def path (pol : Layer) (t : List Layer) : Path (Quantifier (Fin 2)) (Set World) :=
  ⟨pol • ⟨did, .addMult, holdsFor_did⟩, t⟩

/-- The layer of the polarity head of a clause. -/
def polarity : Examples.ClausePolarity → Layer
  | .positive => 1
  | .negative => Environment.compl

/-- The layers above the minimal domain of an item whose clause is below the expressions `s`,
outermost first. An unembedded clause adds its TP. A clause embedded under a polarity phrase adds
its TP and CP, and that polarity phrase and its TP. A conditional clause adds its TP, its CP and
the matrix TP. -/
def above : Option Examples.Superordinate → List Layer
  | none => [1]
  | some .impossible => [1, impossible, 1, 1]
  | some .notImpossible => [1, Environment.compl * impossible, 1, 1]
  | some .notClaim | some .notSure => [1, Environment.compl * necessity, 1, 1]
  | some .conditional => [1, conditional consequent, 1]
  | some .ifImpossible => [1, conditional consequent, 1, impossible, 1, 1]
  | some .notThatImpossible => [Environment.compl, 1, impossible, 1, 1]

/-- The path of the indefinite in a clause of polarity `c` below the expressions `s`. -/
def sentence (c : Examples.ClausePolarity) (s : Option Examples.Superordinate) :
    Path (Quantifier (Fin 2)) (Set World) :=
  path (polarity c) (above s)

-- (18), (31a)
/-- *Il n'est pas impossible que Jean ait fait quoi que ce soit*. -/
def notImpossible := sentence .positive (some .notImpossible)

-- (19), (31b), (48a)
/-- *It is impossible that Jean didn't do something*. -/
def impossibleNot := sentence .negative (some .impossible)

-- (32), (33), (48b), (49)
/-- *It is not impossible that Jean didn't do something*. -/
def notImpossibleNot := sentence .negative (some .notImpossible)

-- (24), (31c)
/-- *If it is impossible that Jean did something, I will apologize to him*. -/
def ifImpossible := sentence .positive (some .ifImpossible)

-- (41a), (45a)
/-- *Jean-Paul doesn't understand something*. -/
def clausemateNot := sentence .negative none

-- (42a), (45b)
/-- *I don't claim that Jean-Paul understands something*. -/
def notClaim := sentence .positive (some .notClaim)

-- (42b)
/-- *It is impossible that Jean-Paul understands something*. -/
def impossibleBare := sentence .positive (some .impossible)

-- (46a), (47)
/-- *I'm not sure that Jean-Paul doesn't understand something*. -/
def notSureNot := sentence .negative (some .notSure)

-- (46b)
/-- *If Jean-Paul doesn't understand something, he has no notion of French at all*. -/
def ifNot := sentence .negative (some .conditional)

-- (48c)
/-- *Not that it is impossible that John doesn't understand something*. -/
def notThatImpossibleNot := sentence .negative (some .notThatImpossible)

/-! ### The items -/

/-- The class of *quoi que ce soit*, licensed by downward entailment. -/
abbrev quoiQueCeSoit : PolarityItem.Class := .npi .weak

/-- The class of *some*, blocked by downward entailment. -/
abbrev someItem : PolarityItem.Class := .ppi .weak

/-- The class of *any*, licensed by downward entailment. -/
abbrev anyItem : PolarityItem.Class := .npi .weak

/-- The class of *some* on which only anti-additivity blocks it, as in [szabolcsi-2004]. -/
abbrev someoneItem : PolarityItem.Class := .ppi .antiAdditive

/-! ### Flip-flop -/

section FlipFlop

attribute [local simp] path sentence polarity above impossible necessity
  ProjectivitySignature.sign_mul

theorem not_licenses_notImpossible : ¬notImpossible.Licenses quoiQueCeSoit :=
  notImpossible.not_licenses_npi fun t ht ↦ by
    simp [notImpossible] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl <;> simp [notImpossible] <;> decide

theorem licenses_impossibleNot : impossibleNot.Licenses quoiQueCeSoit :=
  ⟨[], by simp,
    Licenser.admits_npi_iff.2 <|
      Environment.carries_weak_of_sign_eq_neg_one _ (by simp [impossibleNot]; decide)
        (by simp [impossibleNot])⟩

theorem licenses_notImpossibleNot : notImpossibleNot.Licenses quoiQueCeSoit :=
  ⟨[], by simp,
    Licenser.admits_npi_iff.2 <|
      Environment.carries_weak_of_sign_eq_neg_one _ (by simp [notImpossibleNot]; decide)
        (by simp [notImpossibleNot])⟩

theorem licenses_ifImpossible : ifImpossible.Licenses quoiQueCeSoit :=
  ⟨[impossible, 1, 1], by simp [ifImpossible],
    Licenser.admits_npi_iff.2 <|
      Environment.carries_weak_of_sign_eq_neg_one _ (by simp [ifImpossible]; decide)
        (by simp [ifImpossible])⟩

theorem not_licenses_clausemateNot : ¬clausemateNot.Licenses someItem :=
  clausemateNot.not_licenses_ppi fun t ht ↦ by
    simp [clausemateNot] at ht
    rcases ht with rfl | rfl <;>
      exact Environment.holds_weak_of_sign_eq_neg_one _ (by simp [clausemateNot]; decide)

theorem licenses_notClaim : notClaim.Licenses someItem :=
  ⟨[], by simp,
    Licenser.admits_ppi_iff.2 <|
      Environment.not_holds_of_sign_eq_one _ (by simp [notClaim]; decide)
        (by simp [notClaim]; exact Set.empty_ne_univ)⟩

theorem licenses_impossibleBare : impossibleBare.Licenses someItem :=
  ⟨[], by simp,
    Licenser.admits_ppi_iff.2 <|
      Environment.not_holds_of_sign_eq_one _ (by simp [impossibleBare]; decide)
        (by simp [impossibleBare]; exact Set.empty_ne_univ)⟩

theorem licenses_notSureNot : notSureNot.Licenses someItem :=
  ⟨[Environment.compl * necessity, 1, 1], by simp [notSureNot],
    Licenser.admits_ppi_iff.2 <|
      Environment.not_holds_of_sign_eq_one _ (by simp [notSureNot]; decide)
        (by simp [notSureNot]; exact Set.empty_ne_univ)⟩

theorem licenses_impossibleNot_some : impossibleNot.Licenses someItem :=
  ⟨[impossible, 1, 1], by simp [impossibleNot],
    Licenser.admits_ppi_iff.2 <|
      Environment.not_holds_of_sign_eq_one _ (by simp [impossibleNot]; decide)
        (by simp [impossibleNot]; exact Set.empty_ne_univ)⟩

theorem not_licenses_notImpossibleNot_some : ¬notImpossibleNot.Licenses someItem :=
  notImpossibleNot.not_licenses_ppi fun t ht ↦ by
    simp [notImpossibleNot] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl <;>
      exact Environment.holds_weak_of_sign_eq_neg_one _ (by simp [notImpossibleNot]; decide)

theorem licenses_ifNot : ifNot.Licenses someItem :=
  ⟨[conditional consequent, 1], by simp [ifNot],
    Licenser.admits_ppi_iff.2 <|
      Environment.not_holds_of_sign_eq_one _ (by simp [ifNot, conditional]; decide)
        (by simp [ifNot, conditional, consequent, Set.eq_univ_iff_forall])⟩

theorem licenses_notThatImpossibleNot : notThatImpossibleNot.Licenses someItem :=
  ⟨[impossible, 1, 1], by simp [notThatImpossibleNot],
    Licenser.admits_ppi_iff.2 <|
      Environment.not_holds_of_sign_eq_one _ (by simp [notThatImpossibleNot]; decide)
        (by simp [notThatImpossibleNot]; exact Set.empty_ne_univ)⟩

theorem antitone_notThatImpossibleNot :
    Antitone (notThatImpossibleNot.environment notThatImpossibleNot.layers) :=
  Environment.antitone_of_sign_eq_neg_one _ (by simp [notThatImpossibleNot]; decide)

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

-- under *not that*, *impossible* and a clausemate negation, *some* is licensed although the
-- sentence is downward entailing with respect to it, since a smaller domain is not
theorem localist_ppi :
    Antitone (notThatImpossibleNot.environment notThatImpossibleNot.layers) ∧
      notThatImpossibleNot.Licenses someItem :=
  ⟨antitone_notThatImpossibleNot, licenses_notThatImpossibleNot⟩

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
  ⟨⟨fun Q ↦ (notConn conj Q).strong, .all, ProjectivitySignature.holdsFor_all _⟩, [1]⟩

-- (51b), (56e)
/-- *John didn't drink wine or something*: the strengthened polarity phrase and TP. -/
noncomputable def notOr : Path (Quantifier (Fin 2)) (Set World) :=
  ⟨⟨fun Q ↦ (notConn disj Q).strong, .anti,
    ProjectivitySignature.holdsFor_anti_iff.2 antitone_notConn_disj⟩,
    [1]⟩

theorem not_holds_notAnd {t : List Layer}
    (ht : t ∈ notAnd.layers.tails) {s : Negation.Strength} :
    ¬(Licenser.ofOperator (notAnd.environment t)).Holds s := fun hh ↦ by
  have ha : Antitone _ := Negation.HasStrength.of_le (s := .weak) (hh ⟨⟩) bot_le
  simp [notAnd] at ht
  rcases ht with rfl | rfl <;> exact not_antitone_notConn_conj (by simpa [notAnd,
    Function.End.one_def] using ha)

theorem carries_notOr {t : List Layer}
    (ht : t ∈ notOr.layers.tails) :
    (Licenser.ofOperator (notOr.environment t)).Carries .weak := by
  simp [notOr] at ht
  rcases ht with rfl | rfl <;>
    refine Environment.carries_weak_of_sign_eq_neg_one _ (by simp [notOr]; decide) ?_ <;>
    simp [notOr, notConn_disj_strong, wine_ne_univ]

theorem not_licenses_notAnd : ¬notAnd.Licenses anyItem := by
  rintro ⟨_, ht, ha⟩
  exact not_holds_notAnd ht (Licenser.carries_classical_iff.1 (Licenser.admits_npi_iff.1 ha)).1

theorem licenses_notAnd : notAnd.Licenses someItem :=
  ⟨[], by simp, Licenser.admits_ppi_iff.2 (not_holds_notAnd (by simp))⟩

theorem licenses_notOr : notOr.Licenses anyItem :=
  ⟨[], by simp, Licenser.admits_npi_iff.2 (carries_notOr (by simp))⟩

theorem not_licenses_notOr : ¬notOr.Licenses someItem :=
  notOr.not_licenses_ppi fun _ ht ↦
    (Licenser.carries_classical_iff.1 (carries_notOr ht)).1

/-- *John didn't drink wine and …* is downward entailing with respect to the indefinite, but not
once strengthened by its implicature that John drank one of them, so *any* is anti-licensed and
*some* licensed in it; *John didn't drink wine or …* is its own strengthened meaning, and the
reverse holds. -/
theorem disruption :
    (Antitone (fun Q ↦ (notConn conj Q).ordinary) ∧
      ¬notAnd.Licenses anyItem ∧ notAnd.Licenses someItem) ∧
    ((∀ Q, (notConn disj Q).strong = (notConn disj Q).ordinary) ∧
      notOr.Licenses anyItem ∧ ¬notOr.Licenses someItem) :=
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
  item : ι → PolarityItem.Class
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
def Acceptable (i : ι) (j : ℕ) : Prop := (Licenser.ofOperator (L.env i j)).Admits (L.item i)

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

-- cyclic evaluation licenses every logical form that simultaneous evaluation does
theorem LicensedSimultaneously.licensed (h : L.LicensedSimultaneously) : L.Licensed := fun i ↦
  let ⟨j, hp, hj, ha, h'⟩ := h i
  ⟨j, .intro hp hj ha fun i' hi' hp' ↦ .acceptable (h' i' hi' hp')⟩

-- with a single item, the item is licensed exactly when it is acceptable in one of its domains
theorem licensed_iff_of_subsingleton [Subsingleton ι] :
    L.Licensed ↔ ∀ i, ∃ j, L.position i ≤ j ∧ j < L.height ∧ L.Acceptable i j :=
  forall_congr' fun i ↦ exists_congr fun j ↦ by
    refine ⟨?_, fun ⟨hp, hj, ha⟩ ↦ .intro hp hj ha fun i' hi' ↦ absurd (Subsingleton.elim i' i) hi'⟩
    rintro ⟨hp, hj, ha, -⟩
    exact ⟨hp, hj, ha⟩

end LF

section Acceptability

variable {σ P : Type} [BooleanAlgebra σ] [BooleanAlgebra P] {f : σ → P}

theorem acceptable_any_iff :
    (Licenser.ofOperator f).Admits anyItem ↔ Antitone f ∧ ¬Monotone f :=
  Licenser.admits_npi_iff.trans Licenser.carries_ofOperator_iff

-- (43): *some* is acceptable in a constituent exactly when the constituent is not downward
-- entailing with respect to it
theorem acceptable_someItem_iff : (Licenser.ofOperator f).Admits someItem ↔ ¬Antitone f :=
  Licenser.admits_ppi_iff.trans <| not_congr ⟨fun h ↦ h ⟨⟩, fun h _ ↦ h⟩

theorem not_antitone_of_monotone (h : Monotone f) (hne : f ⊥ ≠ f ⊤) : ¬Antitone f :=
  fun ha ↦ hne (le_antisymm (h bot_le) (ha bot_le))

theorem not_monotone_of_antitone (h : Antitone f) (hne : f ⊥ ≠ f ⊤) : ¬Monotone f := fun hm ↦
  hne (le_antisymm (hm bot_le) (h bot_le))

theorem not_acceptable_any_of_monotone (h : Monotone f) :
    ¬(Licenser.ofOperator f).Admits anyItem :=
  fun ha ↦ (acceptable_any_iff.1 ha).2 h

theorem not_acceptable_someItem (h : Antitone f) : ¬(Licenser.ofOperator f).Admits someItem :=
  fun ha ↦ acceptable_someItem_iff.1 ha h

theorem acceptable_someItem_of_monotone (h : Monotone f) (hne : f ⊥ ≠ f ⊤) :
    (Licenser.ofOperator f).Admits someItem :=
  acceptable_someItem_iff.2 (not_antitone_of_monotone h hne)

/-- *Some* and *any* are never acceptable in the same constituent, and where the environment is
not constant, *any* is acceptable exactly where *some* is not. -/
theorem complementary :
    ¬((Licenser.ofOperator f).Admits anyItem ∧ (Licenser.ofOperator f).Admits someItem) ∧
      (f ⊥ ≠ f ⊤ →
        ((Licenser.ofOperator f).Admits anyItem ↔ ¬(Licenser.ofOperator f).Admits someItem)) := by
  simp only [acceptable_any_iff, acceptable_someItem_iff, not_not]
  exact ⟨fun h ↦ h.2 h.1.1, fun hne ↦ ⟨And.left, fun h ↦ ⟨h, not_monotone_of_antitone h hne⟩⟩⟩

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
def impossibleSubjObj (obj subj : PolarityItem.Class) : LF (Fin 2) where
  item := ![obj, subj]
  height := 5
  position := ![0, 1]
  meaning
    | 0, Q => fun x ↦ did₂ x (Q 0)
    | 1, Q | 2, Q => subject (Q 1) fun x ↦ did₂ x (Q 0)
    | _, Q => impossible₂ (subject (Q 1) fun x ↦ did₂ x (Q 0))

-- (92b), (93)
/-- *It is impossible that someone stole anything*, with *someone* below *impossible*. -/
def impossibleSomeoneAnything := impossibleSubjObj anyItem someItem

-- (103b), (105a)
/-- *It is impossible that anyone stole something*, with *something* below *impossible*. -/
def impossibleAnyoneSomething := impossibleSubjObj someItem anyItem

-- (98), (102a)
/-- *It's impossible that someone isn't eating anything*, with *someone* below the negation. -/
def impossibleNotSomeoneAnything : LF (Fin 2) where
  item := ![anyItem, someItem]
  height := 5
  position := ![0, 0]
  meaning
    | 0, Q | 1, Q | 2, Q => (subject (Q 1) fun x ↦ did₂ x (Q 0))ᶜ
    | _, Q => impossible₂ (subject (Q 1) fun x ↦ did₂ x (Q 0))ᶜ

-- (98), (102b)
/-- *It's impossible that someone isn't eating anything*, with *someone* above the negation. -/
def impossibleSomeoneNotAnything : LF (Fin 2) where
  item := ![anyItem, someItem]
  height := 5
  position := ![0, 1]
  meaning
    | 0, Q => fun x ↦ (did₂ x (Q 0))ᶜ
    | 1, Q | 2, Q => subject (Q 1) fun x ↦ (did₂ x (Q 0))ᶜ
    | _, Q => impossible₂ (subject (Q 1) fun x ↦ (did₂ x (Q 0))ᶜ)

/-- *I'm not sure that `subj` understood `obj`*, both items in the embedded polarity phrase. -/
def notSureSubjObj (obj subj : PolarityItem.Class) : LF (Fin 2) where
  item := ![obj, subj]
  height := 5
  position := ![0, 0]
  meaning
    | 0, Q | 1, Q | 2, Q => subject (Q 1) fun x ↦ did₂ x (Q 0)
    | _, Q => notSure (subject (Q 1) fun x ↦ did₂ x (Q 0))

-- (122b), (122c)
/-- *I'm not sure that someone understood anything*. -/
def notSureSomeoneAnything := notSureSubjObj anyItem someItem

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

variable {obj subj : PolarityItem.Class}

theorem monotone_impossibleSubjObj_env {i : Fin 2} {j : ℕ} (hj : j ≤ 2) :
    Monotone ((impossibleSubjObj obj subj).env i j) := by
  interval_cases j <;> fin_cases i
  · exact monotone_did₂_fun
  · exact fun _ _ _ ↦ le_rfl
  all_goals first
    | exact monotone_subject_right.comp monotone_did₂_fun
    | exact monotone_subject_left fun x ↦ did₂ x someOne

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
      not_acceptable_someItem (antitone_impossibleSubjObj_env_one k).1
    fin_cases i
    · exact ⟨1, by decide, by simp [impossibleSomeoneAnything, impossibleSubjObj], h1⟩
    · exact absurd ha h1

theorem marked_impossibleAnyoneSomething : impossibleAnyoneSomething.Marked 0 0 :=
  .intro le_rfl (by decide) (acceptable_someItem_of_monotone
    (monotone_impossibleSubjObj_env (by decide)) (show (fun x ↦ did₂ x ⊥) ≠ fun x ↦ did₂ x ⊤ by
      rw [did₂_fun_bot, did₂_fun_top]; exact bot_ne_top)) fun i' hi' hp ↦ by
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
    exact not_acceptable_someItem (antitone_impossibleSubjObj_env_zero k).1
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
      exact not_acceptable_someItem hc.1
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
      (f := fun Q ↦ subject Q fun x ↦ (did₂ x someOne)ᶜ) (monotone_subject_left _) (by simp))
      fun i' hi' _ ↦ ?_⟩
    fin_cases i'
    · exact .marked (by decide) marked_impossibleSomeoneNotAnything
    · exact absurd rfl hi'

section NotSureSubjObj

variable {obj subj : PolarityItem.Class}

theorem monotone_notSureSubjObj_env {i : Fin 2} {j : ℕ} (hj : j ≤ 2) :
    Monotone ((notSureSubjObj obj subj).env i j) := by
  interval_cases j <;> fin_cases i
  all_goals first
    | exact monotone_subject_right.comp monotone_did₂_fun
    | exact monotone_subject_left fun x ↦ did₂ x someOne

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
      not_acceptable_someItem (antitone_notSureSubjObj_env_one k).1
    fin_cases i
    · exact ⟨1, by decide, Nat.zero_le _, h1⟩
    · exact absurd ha h1

-- with the anti-additive classification, *someone* and *anything* are both acceptable below
-- *not sure*
theorem licensed_notSureSubjObj_someone :
    (notSureSubjObj anyItem someoneItem).Licensed := by
  have h0 : (notSureSubjObj anyItem someoneItem).Acceptable
      0 3 := acceptable_any_iff.2 (antitone_notSureSubjObj_env_zero 0)
  have h1 : (notSureSubjObj anyItem someoneItem).Acceptable
      1 3 := Licenser.admits_ppi_iff.2 fun h ↦
    not_isAntiAdditive_notSureSubjObj_env (obj := anyItem)
      (subj := someoneItem)
      (h ⟨⟩)
  intro i
  refine ⟨3, .intro (by fin_cases i <;> decide) (by decide) (by fin_cases i <;> assumption)
    fun i' hi' _ ↦ .acceptable ?_⟩
  fin_cases i <;> fin_cases i' <;> first | exact absurd rfl hi' | assumption

/-- Below *not sure*, downward entailing without being anti-additive, *someone … anything* is
anti-licensed when downward entailment blocks *some*, and would be licensed if only
anti-additivity blocked it. -/
theorem downwardEntailment :
    ¬notSureSomeoneAnything.Licensed ∧ (notSureSubjObj anyItem someoneItem).Licensed :=
  ⟨not_licensed_notSureSomeoneAnything, licensed_notSureSubjObj_someone⟩

/-! ### The judgments -/

/-- The class of the item of a row. -/
def itemClass : Examples.Item → PolarityItem.Class
  | .quoiQueCeSoit => quoiQueCeSoit
  | .any => anyItem
  | .some => someItem

/-- The path of a row's item: the strengthened polarity phrase of a row with a connective, and
otherwise the path given by the polarity of its clause and the expressions above it. -/
noncomputable def path? (e : Datum) : Option (Path (Quantifier (Fin 2)) (Set World)) :=
  match Examples.connective e with
  | some .and => some notAnd
  | some .or => some notOr
  | none => (Examples.clause e).map (sentence · (Examples.superordinate e))

/-- The licensing of a row's item in its path. -/
noncomputable def licensing? (e : Datum) : Option Prop :=
  (path? e).bind fun p ↦ (Examples.item e).map fun i ↦ p.Licenses (itemClass i)

/-- The judgment on which a row's item is evaluated: the narrowest scope of *some*, the sentence
otherwise. -/
def judgment? (e : Datum) : Option Judgment :=
  match Examples.item e with
  | some .some => Examples.reading e .narrowestScope
  | _ => some e.judgment

-- an item is judged acceptable exactly when it meets the licensing condition in its path
theorem rows_licensing : ∀ e ∈ Examples.all, ∀ p ∈ licensing? e, ∀ j ∈ judgment? e,
    (j = .acceptable ↔ p) := by
  simp only [Examples.all, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rintro p ⟨⟩ j ⟨⟩
  exacts [iff_of_false (by decide) not_licenses_notImpossible,
    iff_of_true rfl licenses_impossibleNot,
    iff_of_true rfl licenses_ifImpossible,
    iff_of_true rfl licenses_notImpossibleNot,
    iff_of_false (by decide) not_licenses_clausemateNot,
    iff_of_true rfl licenses_notClaim,
    iff_of_true rfl licenses_impossibleBare,
    iff_of_true rfl licenses_notSureNot,
    iff_of_true rfl licenses_ifNot,
    iff_of_true rfl licenses_impossibleNot_some,
    iff_of_false (by decide) not_licenses_notImpossibleNot_some,
    iff_of_true rfl licenses_notThatImpossibleNot,
    iff_of_false (by decide) not_licenses_notAnd,
    iff_of_true rfl licenses_notOr,
    iff_of_true rfl licenses_notAnd,
    iff_of_false (by decide) not_licenses_notOr]

theorem readCount_licensing : Datum.ReadCount licensing? Examples.all 16 := by
  decide +kernel

/-- The class of a subject. -/
def subjectClass : Examples.Subject → PolarityItem.Class
  | .someone => someItem
  | .anyone => anyItem

/-- The class of an object. -/
def objectClass : Examples.Object → PolarityItem.Class
  | .anything => anyItem
  | .something => someItem

/-- The logical form of a reading of a row with two items, read from its subject, object,
superordinate expression and clausemate negation, and from the scopes the reading names. -/
def lf? (e : Datum) (r : Examples.Reading) : Option (LF (Fin 2)) :=
  match Examples.subject e, Examples.object e, Examples.superordinate e, Examples.clause e, r with
  | some s, some o, some .impossible, some .positive, .imposSome =>
      some (impossibleSubjObj (objectClass o) (subjectClass s))
  | some .someone, some .anything, some .impossible, some .negative, .imposNegSomeAny =>
      some impossibleNotSomeoneAnything
  | some .someone, some .anything, some .impossible, some .negative, .imposSomeNegAny =>
      some impossibleSomeoneNotAnything
  | some s, some o, some .notSure, some .positive, .negSome =>
      some (notSureSubjObj (objectClass o) (subjectClass s))
  | _, _, _, _, _ => none

-- a reading is judged acceptable exactly when its logical form is licensed
theorem rows_entanglement : ∀ e ∈ Examples.all, ∀ r, ∀ j ∈ Examples.reading e r,
    ∀ L ∈ lf? e r, (j = .acceptable ↔ L.Licensed) := by
  simp only [Examples.all, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rintro (_ | _ | _ | _ | _) j ⟨⟩ L ⟨⟩
  exacts [iff_of_false (by decide) not_licensed_impossibleSomeoneAnything,
    iff_of_false (by decide) not_licensed_impossibleNotSomeoneAnything,
    iff_of_true rfl licensed_impossibleSomeoneNotAnything,
    iff_of_true rfl licensed_impossibleAnyoneSomething,
    iff_of_false (by decide) not_licensed_notSureSomeoneAnything]

-- the readings that the rows judge and that have a logical form
theorem readCount_entanglement :
    (Examples.all.map fun e ↦ (Finset.univ.filter fun r ↦
      (Examples.reading e r).isSome ∧ (lf? e r).isSome).card).sum = 5 := by
  decide +kernel

end Homer2021
