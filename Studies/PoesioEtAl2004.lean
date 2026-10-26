module

public import Linglib.Discourse.Centering.Transition
public import Linglib.Discourse.Centering.GrammaticalRole
public import Linglib.Discourse.Accessibility
public import Linglib.Data.Examples.PoesioEtAl2004
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.List.MinMax
public import Mathlib.Data.List.Dedup
public import Mathlib.Order.Prod.Lex.Basic
import all Mathlib.Data.List.Sort  -- for unfolding `List.insertionSort`

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

The instantiations are the substrate's parameters: the realization relation is the `Membership`
instance, the ranking is the `LinearOrder` on roles, the CF filter is `cfFilter`, the utterance
unit is `merge`, and the previous utterance is the argument of `cb`. The paper's illustrations
of each parameter are worked as such: the associative reference of (5) is a `Bridged`
realization (`ex5`), the second-person pronoun of (7) a filtered forward-looking center (`ex7`),
the egg vases of (9) recovered either by sentence units or by indirect realization (`ex9`), the
tie of (10) two backward-looking centers under grammatical-function ranking and one under its
linear disambiguation (`ex10`), and the adjunct clauses of (14) and (16) the two definitions of
the previous utterance pulling in opposite directions (`ex14`, `ex16`). Constraint 1 is
unpacked into CB uniqueness and entity continuity (`strong_iff`), uniqueness holds under any
ranking that separates the previous utterance's realizations (`cbUniqueness_of_role_injective`),
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

variable [DecidableEq E] [LinearOrder R] {U : Type*} [Membership E U]
  [∀ (u : U) (e : E), Decidable (e ∈ u)]

/-- CB uniqueness: at most one backward-looking center, the weak form of Constraint 1. -/
def CBUniqueness (prev : Utterance E R F) (cur : U) : Prop := (backwardCenters prev cur).card ≤ 1

/-- Entity continuity: the utterance realizes some forward-looking center of the previous one. -/
def EntityContinuity (prev : Utterance E R F) (cur : U) : Prop :=
  (backwardCenters prev cur).Nonempty

/-- The strong form of Constraint 1: exactly one backward-looking center. -/
def Constraint1Strong (prev : Utterance E R F) (cur : U) : Prop :=
  (backwardCenters prev cur).card = 1

instance (prev : Utterance E R F) (cur : U) : Decidable (CBUniqueness prev cur) :=
  inferInstanceAs (Decidable (_ ≤ _))

instance (prev : Utterance E R F) (cur : U) : Decidable (EntityContinuity prev cur) :=
  inferInstanceAs (Decidable (Finset.Nonempty _))

instance (prev : Utterance E R F) (cur : U) : Decidable (Constraint1Strong prev cur) :=
  inferInstanceAs (Decidable (_ = _))

/-- Strong Constraint 1 is CB uniqueness together with entity continuity. -/
theorem strong_iff (prev : Utterance E R F) (cur : U) :
    Constraint1Strong prev cur ↔ CBUniqueness prev cur ∧ EntityContinuity prev cur := by
  unfold Constraint1Strong CBUniqueness EntityContinuity
  rw [← Finset.card_pos]
  omega

/-- CB uniqueness holds under any ranking that separates the realizations of the previous
utterance. -/
theorem cbUniqueness_of_role_injective (prev : Utterance E R F) (cur : U)
    (h : ∀ r₁ ∈ prev.realizations, ∀ r₂ ∈ prev.realizations,
      r₁.role = r₂.role → r₁.entity = r₂.entity) :
    CBUniqueness prev cur := by
  refine Finset.card_le_one.2 fun a ha b hb ↦ ?_
  obtain ⟨hpa, hca, hma⟩ := mem_backwardCenters.1 ha
  obtain ⟨hpb, hcb, hmb⟩ := mem_backwardCenters.1 hb
  have hab := le_antisymm (hmb a hpa hca) (hma b hpb hcb)
  obtain ⟨ra, hra, rfl, hea⟩ := prev.exists_rank_eq hpa
  obtain ⟨rb, hrb, rfl, heb⟩ := prev.exists_rank_eq hpb
  exact h ra hra rb hrb (WithBot.coe_injective (hea.symm.trans (hab.trans heb)))

end Constraint1

/-! ### Rule 1 in its three forms (§2.3.2) -/

section Rule1

variable [DecidableEq E] [LinearOrder R]

/-- Rule 1 in its original form: a backward-looking center kept from the previous utterance is
pronominalized. The form of [grosz-joshi-weinstein-1995] is `PronominalizationConstraint`, and
the unconditional form is `CbPronominalized`. -/
def Rule1Original (P : Set F) (prev cur : Utterance E R F) (prevCb : Option E) : Prop :=
  (∃ c, cb prev cur = some c ∧ prevCb = some c) → CbPronominalized P prev cur

theorem CbPronominalized.rule1Original {P : Set F} {prev cur : Utterance E R F}
    (prevCb : Option E) (h : CbPronominalized P prev cur) : Rule1Original P prev cur prevCb :=
  fun _ ↦ h

end Rule1

/-! ### Transitions (§2.2.3, §2.3.3) -/

section Transitions

variable [DecidableEq E] [LinearOrder R]

/-- The four-way classification of [brennan-friedman-pollard-1987] of an utterance after an
utterance with center `prevCb`, `none` for an utterance with no center. -/
def bfp (prev cur : Utterance E R F) (prevCb : Option E) : Option ExtendedTransition :=
  (cb prev cur).map fun c ↦ .ofCenters prevCb c cur.cp

theorem bfp_eq_none_iff (prev cur : Utterance E R F) (prevCb : Option E) :
    bfp prev cur prevCb = none ↔ cb prev cur = none := by
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

/-- An utterance with the anchors of its associative references, each mention paired with the
entity it indirectly realizes. -/
structure Bridged (E R F : Type*) where
  utt : Utterance E R F
  anchors : List (E × E)

/-- Indirect realization: an entity is realized when mentioned or when anchored by a mention. -/
instance : Membership E (Bridged E R F) :=
  ⟨fun b e ↦ e ∈ b.utt ∨ ∃ a ∈ b.anchors, a.2 = e ∧ a.1 ∈ b.utt⟩

instance [DecidableEq E] (b : Bridged E R F) (e : E) : Decidable (e ∈ b) :=
  inferInstanceAs (Decidable (e ∈ b.utt ∨ ∃ a ∈ b.anchors, a.2 = e ∧ a.1 ∈ b.utt))

/-- Grammatical function with linear-order disambiguation: the role together with the surface
position, an earlier mention outranking a later one of the same function. -/
abbrev GFLin (n : ℕ) := Lex (GrammaticalRole × (Fin n)ᵒᵈ)

/-- A realization by a name in role `r` at surface position `i`. -/
def GFLin.name {E : Type*} {n : ℕ} (e : E) (r : GrammaticalRole) (i : Fin n) :
    Realization E (GFLin n) Head :=
  ⟨e, toLex (r, OrderDual.toDual i), .name⟩

/-- A realization by a description in role `r` at surface position `i`. -/
def GFLin.desc {E : Type*} {n : ℕ} (e : E) (r : GrammaticalRole) (i : Fin n) :
    Realization E (GFLin n) Head :=
  ⟨e, toLex (r, OrderDual.toDual i), .description⟩

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
    cb u1 u2 = none ∧
      cb u1 (⟨u2, [(.door, .house)]⟩ : Bridged Ent5 GrammaticalRole Head) = some .house := by
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
    (cb u1 u2 = some .you ∧ cb u2 u3 = some .you) ∧
      cb (f u1) (f u2) = none ∧ cb (f u2) (f u3) = none ∧ cb (f u1) (f u3) = some .productZ := by
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
    (cb u1 u2 = none ∧ cb u2 u3 = none ∧ cb u3 u4 = none ∧ cb u4 u5 = none) ∧
      cb (merge [u1, u2, u3, u4]) u5 = some .vases ∧
      cb u1 (⟨u2, [(.bases, .vases), (.bodies, .vases)]⟩ : Bridged Ent9 GrammaticalRole Head)
        = some .vases := by
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
grammatical-function ranking, and linear order picks the cupboard, as `cb` does by surface
order. -/
theorem ex10 :
    let u227 : Utterance Ent10 GrammaticalRole Head :=
      ⟨[⟨.drawing, .subject, .description⟩, ⟨.cupboard, .other, .description⟩,
        ⟨.branicki, .other, .name⟩]⟩
    let u229 : Utterance Ent10 GrammaticalRole Head :=
      ⟨[⟨.dubois, .subject, .name⟩, ⟨.dealer, .other, .description⟩,
        ⟨.cupboard, .object, .description⟩,
        ⟨.branicki, .other, .name⟩]⟩
    let v227 : Utterance Ent10 (GFLin 4) Head :=
      ⟨[GFLin.desc .drawing .subject 0, GFLin.desc .cupboard .other 1,
        GFLin.name .branicki .other 2]⟩
    let v229 : Utterance Ent10 (GFLin 4) Head :=
      ⟨[GFLin.name .dubois .subject 0, GFLin.desc .dealer .other 1,
        GFLin.desc .cupboard .object 2, GFLin.name .branicki .other 3]⟩
    (backwardCenters u227 u229).card = 2 ∧ ¬ CBUniqueness u227 u229 ∧
      EntityContinuity u227 u229 ∧ cb u227 u229 = some .cupboard ∧
      backwardCenters v227 v229 = {.cupboard} := by
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

/-- The two definitions of the previous utterance after an adjunct clause pull in opposite
directions in (14) and (16). -/
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
    (cb u2 u3 = none ∧ cb u1 u3 = some .john) ∧ (cb v2 v3 = some .patch ∧ cb v1 v3 = none) := by
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

/-- (23): with the second-person pronoun excluded, no utterance realizes a forward-looking
center of the previous one, so entity coherence is absent throughout a coherent text. -/
theorem ex23 :
    let u1 : Utterance Ent23 GrammaticalRole Head :=
      ⟨[⟨.leaflet, .subject, .description⟩, ⟨.summary, .other, .description⟩,
        ⟨.info, .other, .description⟩,
        ⟨.productA, .other, .name⟩]⟩
    let u2 : Utterance Ent23 GrammaticalRole Head :=
      ⟨[⟨.questions, .object, .description⟩, ⟨.treatment, .other, .description⟩]⟩
    let u3 : Utterance Ent23 GrammaticalRole Head :=
      ⟨[⟨.doctor, .object, .description⟩, ⟨.pharmacist, .other, .description⟩]⟩
    cb u1 u2 = none ∧ cb u2 u3 = none := by
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
