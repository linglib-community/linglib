module

public import Linglib.Discourse.Centering.Discourse
public import Linglib.Discourse.Centering.Pronominalization
public import Linglib.Discourse.Centering.GrammaticalRole
public import Linglib.Discourse.Accessibility
public import Linglib.Data.Examples.PoesioEtAl2004
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.List.MinMax
public import Mathlib.Data.List.Dedup
public import Mathlib.Order.Prod.Lex.Basic

/-!
# Poesio, Stevenson, Di Eugenio and Hitzeman (2004): Centering as a parametric theory

This file formalizes the parametric reading of centering theory by Poesio, Stevenson, Di Eugenio,
and Hitzeman. The claims of Grosz, Joshi, and Weinstein, Constraint 1 on the uniqueness of the
backward-looking center, Rule 1 on its pronominalization, and Rule 2 on the preference among
transitions, can only be evaluated once the notions they quantify over are fixed, and the
literature has fixed them in several ways: what an utterance is, which utterance counts as the
previous one, when an entity is realized, which noun phrases introduce forward-looking centers,
how the centers are ranked, and which pronouns Rule 1 governs. Each setting is an instantiation
of the theory, and the paper's corpus study finds that different instantiations make different
claims true.

The instantiations are the substrate's parameters: the realization relation is the set of
entities of which `cb` is taken, the ranking is the `LinearOrder` on roles, the CF filter is
`cfFilter`, the utterance unit is `merge`, and the previous utterance is the argument of `cb`.
The paper's illustrations of each parameter are worked as such: the associative reference of (5)
is a `bridged` realization (`ex5`), the second-person pronoun of (7) a filtered forward-looking
center (`ex7`),
the egg vases of (9) recovered either by sentence units or by indirect realization (`ex9`), the
tie of (10) two backward-looking centers under grammatical-function ranking and one under its
linear disambiguation (`ex10`), and the adjunct clauses of (14) and (16) the two definitions of
the previous utterance pulling in opposite directions (`ex14`, `ex16`). Constraint 1 is
unpacked into CB uniqueness and entity continuity (`strong_iff`), uniqueness holds under any
ranking that separates the previous utterance's realizations (`cbUniqueness_of_role_injective`),
in particular under linear disambiguation (`cbUniqueness_indexed`),
the three forms of Rule 1 are ordered (`CbPronominalized.rule1Original`), counting
demonstratives among the R1-pronouns Rule 1 takes as an argument helps the unconditional form and
can hurt Rule 1 itself (`pronominalizationConstraint_narrowR1_not_broadR1`), and the four-way
transition classification of Brennan, Friedman, and Pollard refines the three-way one
(`bfp_toTransition`).

## Implementation notes

The corpus statistics of Tables 1 to 15, the statistical tests, and the trade-off they reveal
between Rule 1 on the one hand and Constraint 1 and Rule 2 on the other are not formalized; the
examples carry the mechanisms the statistics measure. Utterance identification, segmentation,
and the Walker heuristics are corpus-operational choices and are represented only by the way
the examples are cut into utterances.

Realizations record the head of their noun phrase (`AccessibilityLevel.Head`), which does not
separate the second-person pronoun from the others, so the setting of the R1-pronouns that adds
*you* (p. 326) is represented by filtering *you* from the forward-looking centers, as for (7).
Where the examples' text is not printed in the file, names are assigned to proper nouns and
descriptions to common nouns, keeping the pronoun or non-pronoun status of each realization.

## References

* [poesio-stevenson-eugenio-hitzeman-2004]
* [grosz-joshi-weinstein-1995]
* [brennan-friedman-pollard-1987]
* [strube-hahn-1999]
-/

@[expose] public section

namespace PoesioEtAl2004

open Discourse.Centering
open Discourse.AccessibilityLevel (Head)

variable {E R F : Type*}

/-! ### Constraint 1 unpacked (§5.3.2, §5.3.4) -/

section Constraint1

variable [DecidableEq E] [LinearOrder R]

/-- CB uniqueness: at most one backward-looking center, the weak form of Constraint 1. -/
def CBUniqueness (prev : Utterance E R F) (s : Finset E) : Prop := (backwardCenters prev s).card ≤ 1

/-- Entity continuity: the utterance realizes some forward-looking center of the previous one. -/
def EntityContinuity (prev : Utterance E R F) (s : Finset E) : Prop :=
  (backwardCenters prev s).Nonempty

/-- The strong form of Constraint 1: exactly one backward-looking center. -/
def Constraint1Strong (prev : Utterance E R F) (s : Finset E) : Prop :=
  (backwardCenters prev s).card = 1

instance (prev : Utterance E R F) (s : Finset E) : Decidable (CBUniqueness prev s) :=
  inferInstanceAs (Decidable (_ ≤ _))

instance (prev : Utterance E R F) (s : Finset E) : Decidable (EntityContinuity prev s) :=
  inferInstanceAs (Decidable (Finset.Nonempty _))

instance (prev : Utterance E R F) (s : Finset E) : Decidable (Constraint1Strong prev s) :=
  inferInstanceAs (Decidable (_ = _))

/-- Strong Constraint 1 is CB uniqueness together with entity continuity. -/
theorem strong_iff (prev : Utterance E R F) (s : Finset E) :
    Constraint1Strong prev s ↔ CBUniqueness prev s ∧ EntityContinuity prev s := by
  unfold Constraint1Strong CBUniqueness EntityContinuity
  rw [← Finset.card_pos]
  omega

/-- CB uniqueness holds under any ranking that separates the realizations of the previous
utterance. -/
theorem cbUniqueness_of_role_injective (prev : Utterance E R F) (s : Finset E)
    (h : ∀ r₁ ∈ prev.realizations, ∀ r₂ ∈ prev.realizations,
      r₁.role = r₂.role → r₁.entity = r₂.entity) :
    CBUniqueness prev s :=
  card_backwardCenters_le_one s h

/-- CB uniqueness holds once ties in the ranking are broken by linear order, as
[strube-hahn-1999] break ties of information status by text position. -/
theorem cbUniqueness_indexed (prev : Utterance E R F) (s : Finset E) :
    CBUniqueness prev.indexed s := by
  rw [CBUniqueness, backwardCenters_indexed]
  cases cb prev s <;> simp

end Constraint1

/-! ### Rule 1 in its three forms (§2.3.2) -/

section Rule1

variable [DecidableEq E] [LinearOrder R]

/-- Rule 1 in its original form: a backward-looking center kept from the previous utterance is
pronominalized. The form of [grosz-joshi-weinstein-1995] is `PronominalizationConstraint`, and
the unconditional form is `CbPronominalized`. -/
def Rule1Original (P : Set F) [DecidablePred (· ∈ P)] (prev cur : Utterance E R F)
    (prevCb : Option E) : Prop :=
  (∃ c, cb prev cur.cf = some c ∧ prevCb = some c) → CbPronominalized P prev cur

theorem CbPronominalized.rule1Original {P : Set F} [DecidablePred (· ∈ P)]
    {prev cur : Utterance E R F}
    (prevCb : Option E) (h : CbPronominalized P prev cur) : Rule1Original P prev cur prevCb :=
  fun _ ↦ h

end Rule1

/-! ### Transitions (§2.2.3, §2.3.3) -/

section Transitions

variable [DecidableEq E] [LinearOrder R]

/-- The four-way classification of [brennan-friedman-pollard-1987] of an utterance after an
utterance with center `prevCb`, `none` for an utterance with no center. -/
def bfp (prev cur : Utterance E R F) (prevCb : Option E) : Option ExtendedTransition :=
  (cb prev cur.cf).map fun c ↦ .ofCenters prevCb c cur.cp

theorem bfp_eq_none_iff (prev cur : Utterance E R F) (prevCb : Option E) :
    bfp prev cur prevCb = none ↔ cb prev cur.cf = none := by
  simp [bfp]

/-- The four-way classification refines the three-way one. -/
theorem bfp_toTransition {prev cur : Utterance E R F} {prevCb : Option E}
    {t : ExtendedTransition} (h : bfp prev cur prevCb = some t) :
    t.toTransition = transition prevCb prev cur := by
  obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp h
  simp [transition, hc, Transition.ofCenters]

end Transitions

/-! ### The parameters (§2.4, §3.4) -/

/-- The CF filter: only the entities satisfying `p` introduce forward-looking centers, as when
first- and second-person pronouns or predicative noun phrases are excluded. -/
def cfFilter (p : E → Bool) (u : Utterance E R F) : Utterance E R F :=
  ⟨u.realizations.filter fun r ↦ p r.entity⟩

/-- The utterance unit: clauses merged into one sentence-sized utterance. -/
def merge (us : List (Utterance E R F)) : Utterance E R F := ⟨(us.map (·.realizations)).flatten⟩

/-- Indirect realization: the entities an utterance realizes when each mention also realizes the
entities it is anchored to, `anchors` pairing a mention with an entity it is associated with. -/
def bridged [DecidableEq E] (u : Utterance E R F) (anchors : List (E × E)) : Finset E :=
  u.cf ∪ ((anchors.filter (·.1 ∈ u.cf)).map (·.2)).toFinset

/-- The three tiers of information status of [strube-hahn-1999], the ranking of §4.4.3. -/
inductive InfoStatus where
  | hearerOld
  | mediated
  | hearerNew
  deriving DecidableEq, Repr, Fintype

/-- Hearer-old entities outrank mediated ones, which outrank hearer-new ones. -/
def InfoStatus.rank : InfoStatus → ℕ
  | .hearerOld => 2
  | .mediated => 1
  | .hearerNew => 0

instance : LinearOrder InfoStatus := LinearOrder.lift' InfoStatus.rank (by decide)

/-! ### The illustrations -/

section Examples

/-- The entities of (5). -/
inductive Ent5 where
  | john
  | house
  | door
  deriving DecidableEq, Repr

/-- In *John walked toward the house. The door was open.* (5), the second utterance has a
backward-looking center only with the door anchored to the house. -/
theorem ex5 :
    let u1 : Utterance Ent5 GrammaticalRole Head :=
      ⟨[⟨.john, .subject, .name⟩, ⟨.house, .other, .description⟩]⟩
    let u2 : Utterance Ent5 GrammaticalRole Head := ⟨[⟨.door, .subject, .description⟩]⟩
    cb u1 u2.cf = none ∧
      cb u1 (bridged u2 [(.door, .house)]) = some .house := by
  decide

/-- The entities of (7). -/
inductive Ent7 where
  | you
  | productZ
  deriving DecidableEq, Repr

/-- In (7) every utterance has a forward-looking center when the second-person pronoun introduces
one, and otherwise the if-clause has none. -/
theorem ex7 :
    let u1 : Utterance Ent7 GrammaticalRole Head :=
      ⟨[⟨.you, .subject, .pronoun⟩, ⟨.productZ, .object, .name⟩]⟩
    let u2 : Utterance Ent7 GrammaticalRole Head := ⟨[⟨.you, .subject, .pronoun⟩]⟩
    let u3 : Utterance Ent7 GrammaticalRole Head :=
      ⟨[⟨.you, .subject, .pronoun⟩, ⟨.productZ, .object, .name⟩]⟩
    let f := cfFilter (· != Ent7.you)
    (cb u1 u2.cf = some .you ∧ cb u2 u3.cf = some .you) ∧
      cb (f u1) (f u2).cf = none ∧ cb (f u2) (f u3).cf = none ∧
      cb (f u1) (f u3).cf = some .productZ := by
  decide

/-- The entities of (9). -/
inductive Ent9 where
  | vases
  | bases
  | bodies
  | straw
  | handles
  | eggs
  | nests
  | finial
  | lid
  deriving DecidableEq, Repr

/-- In (9) no clause after the first has a backward-looking center when finite clauses are
utterances, but the second sentence does when sentences are. -/
theorem ex9 :
    let u1 : Utterance Ent9 GrammaticalRole Head := ⟨[⟨.vases, .subject, .description⟩]⟩
    let u2 : Utterance Ent9 GrammaticalRole Head :=
      ⟨[⟨.bases, .subject, .description⟩, ⟨.bodies, .object, .description⟩]⟩
    let u3 : Utterance Ent9 GrammaticalRole Head :=
      ⟨[⟨.straw, .subject, .description⟩, ⟨.handles, .object, .description⟩]⟩
    let u4 : Utterance Ent9 GrammaticalRole Head :=
      ⟨[⟨.eggs, .subject, .description⟩, ⟨.nests, .other, .description⟩,
        ⟨.finial, .other, .description⟩, ⟨.lid, .other, .description⟩]⟩
    let u5 : Utterance Ent9 GrammaticalRole Head := ⟨[⟨.vases, .subject, .description⟩]⟩
    (cb u1 u2.cf = none ∧ cb u2 u3.cf = none ∧ cb u3 u4.cf = none ∧ cb u4 u5.cf = none) ∧
      cb (merge [u1, u2, u3, u4]) u5.cf = some .vases ∧
      cb u1 (bridged u2 [(.bases, .vases), (.bodies, .vases)]) = some .vases := by
  decide

/-- The entities of (10). -/
inductive Ent10 where
  | drawing
  | cupboard
  | branicki
  | dubois
  | dealer
  deriving DecidableEq, Repr

/-- In (10) the corner cupboard and Branicki tie as backward-looking centers under
grammatical-function ranking, and linear order picks the cupboard, the `cb`. -/
theorem ex10 :
    let u227 : Utterance Ent10 GrammaticalRole Head :=
      ⟨[⟨.drawing, .subject, .description⟩, ⟨.cupboard, .other, .description⟩,
        ⟨.branicki, .other, .name⟩]⟩
    let u229 : Utterance Ent10 GrammaticalRole Head :=
      ⟨[⟨.dubois, .subject, .name⟩, ⟨.dealer, .other, .description⟩,
        ⟨.cupboard, .object, .description⟩,
        ⟨.branicki, .other, .name⟩]⟩
    (backwardCenters u227 u229.cf).card = 2 ∧ ¬ CBUniqueness u227 u229.cf ∧
      EntityContinuity u227 u229.cf ∧ cb u227 u229.cf = some .cupboard ∧
      backwardCenters u227.indexed u229.cf = {.cupboard} := by
  decide

/-- The entities of (14) and (16). -/
inductive Ent14 where
  | john
  | bill
  | door
  | appointment
  | scissors
  | you
  | patch
  deriving DecidableEq, Repr

-- (14), (16)
theorem ex14_ex16 :
    let u1 : Utterance Ent14 GrammaticalRole Head := ⟨[⟨.john, .subject, .name⟩]⟩
    let u2 : Utterance Ent14 GrammaticalRole Head :=
      ⟨[⟨.bill, .subject, .name⟩, ⟨.door, .object, .description⟩]⟩
    let u3 : Utterance Ent14 GrammaticalRole Head :=
      ⟨[⟨.john, .subject, .pronoun⟩, ⟨.appointment, .object, .description⟩]⟩
    let v1 : Utterance Ent14 GrammaticalRole Head := ⟨[⟨.scissors, .object, .description⟩]⟩
    let v2 : Utterance Ent14 GrammaticalRole Head :=
      ⟨[⟨.you, .subject, .pronoun⟩, ⟨.patch, .object, .description⟩]⟩
    let v3 : Utterance Ent14 GrammaticalRole Head := ⟨[⟨.patch, .object, .description⟩]⟩
    (cb u2 u3.cf = none ∧ cb u1 u3.cf = some .john) ∧
      (cb v2 v3.cf = some .patch ∧ cb v1 v3.cf = none) := by
  decide

/-- The entities of (23). -/
inductive Ent23 where
  | leaflet
  | summary
  | info
  | productA
  | questions
  | treatment
  | doctor
  | pharmacist
  deriving DecidableEq, Repr

-- (23)
theorem ex23 :
    let u1 : Utterance Ent23 GrammaticalRole Head :=
      ⟨[⟨.leaflet, .subject, .description⟩, ⟨.summary, .other, .description⟩,
        ⟨.info, .other, .description⟩,
        ⟨.productA, .other, .name⟩]⟩
    let u2 : Utterance Ent23 GrammaticalRole Head :=
      ⟨[⟨.questions, .object, .description⟩, ⟨.treatment, .other, .description⟩]⟩
    let u3 : Utterance Ent23 GrammaticalRole Head :=
      ⟨[⟨.doctor, .object, .description⟩, ⟨.pharmacist, .other, .description⟩]⟩
    cb u1 u2.cf = none ∧ cb u2 u3.cf = none := by
  decide

/-! ### The R1-pronouns (§2.4.4, §4.1.3) -/

/-- The narrow R1-pronouns of the paper's results, the personal pronouns. -/
def narrowR1 : Set Head := {h | h = .pronoun}

/-- The broader R1-pronouns of p. 334, counting demonstrative pronouns too. -/
def broadR1 : Set Head := {h | h = .pronoun ∨ h = .demonstrative}

instance : DecidablePred (· ∈ narrowR1) := fun h ↦ inferInstanceAs (Decidable (h = .pronoun))

instance : DecidablePred (· ∈ broadR1) := fun h ↦
  inferInstanceAs (Decidable (h = .pronoun ∨ h = .demonstrative))

theorem narrowR1_subset_broadR1 : narrowR1 ⊆ broadR1 := fun _ ↦ Or.inl

/-- Counting demonstrative pronouns as R1-pronouns can only remove violations of the unconditional
rule (`CbPronominalized.mono`), but it can add violations of Rule 1: when the backward-looking
center is a full NP and another forward-looking center a demonstrative pronoun, the case p. 320
raises, Rule 1 holds of the narrow R1-pronouns and fails of the broad ones. The corpus counts of
p. 334 move the same ways, 152 to 148 violations of the unconditional rule and 9 to 11 of Rule 1. -/
theorem pronominalizationConstraint_narrowR1_not_broadR1 :
    let u1 : Utterance Ent5 GrammaticalRole Head :=
      ⟨[⟨.john, .subject, .name⟩, ⟨.house, .other, .description⟩]⟩
    let u2 : Utterance Ent5 GrammaticalRole Head :=
      ⟨[⟨.john, .subject, .name⟩, ⟨.house, .object, .demonstrative⟩]⟩
    PronominalizationConstraint narrowR1 u1 u2 ∧ ¬ PronominalizationConstraint broadR1 u1 u2 := by
  decide

end Examples

end PoesioEtAl2004
