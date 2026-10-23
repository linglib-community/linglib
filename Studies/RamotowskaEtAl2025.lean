module

public import Linglib.Semantics.Conditionals.Counterfactual
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Ramotowska, Marty, Romoli, and Santorio (2025): Counterfactuals and Quantificational Force

Ramotowska, Marty, Romoli, and Santorio compare three theories of counterfactuals on quantified
sentences in mixed scenarios, where some but not all of the players would have won. The universal
theory of Lewis and Kratzer quantifies over the closest antecedent worlds (2); Stalnaker's
selectional theory evaluates the whole sentence at a selected world and supervaluates over the
candidate selections after composition (5); the homogeneity theory of von Fintel and Križ gives
each counterfactual a third status during composition (6). Unembedded, the last two agree that a
single player's counterfactual has a third status and the first calls it false (Table 1,
`unembedded`). Embedded under a quantifier they part ways: the universal theory makes the
sentence turn on its polarity (`universal_polarity`), the selectional theory on its
quantificational force, the universal sentences false and the existential ones true whatever the
question under discussion (`selectional_force`), and the homogeneity theory leaves every
quantified sentence undefined under either projection algorithm (`homogeneity_undefined`), so
that only there is a gap for a question under discussion to resolve, as it does for the plural
definite of the same scenario (`dissociation`). Bassi and Bar-Lev's implicature variant (§8)
mispredicts *some* and *not all* (`implicature_some`, `implicature_notAll`). The paper's two
experiments find the force effect and no effect of the question under discussion on
counterfactuals, alongside a question effect on plural definites, the pattern of the selectional
theory.

## Implementation notes

A scenario is a similarity ordering, an antecedent, and one consequent per player. Mixedness is
stated as the paper's setting has it: every closest antecedent world has a winner and a loser,
and every player wins in one closest world and loses in another. The homogeneity theory's
projection through a quantifier is the Kleene aggregation of the players' trivalent values,
conjunctive or disjunctive over the values or their negations; the paper notes that the choice
makes no difference when every instance is undefined, and its Table 3 row for that theory,
which rests on a pragmatic resolution of undefinedness by the question under discussion, is
not derived. Force is the paper's binary, universal against existential, which differs from the
weak/strong labels Barwise and Cooper give *no*. The mean ratings and mixed-effects models
of §5 and §6 are not restated.

## References

* [ramotowska-marty-romoli-santorio-2025]
* [lewis-1973]
* [kratzer-2012]
* [stalnaker-1968]
* [von-fintel-1997]
* [kriz-2015]
* [bassi-bar-lev-2018]
* [barwise-cooper-1981]
-/

@[expose] public section


open Conditional

namespace RamotowskaEtAl2025

/-! ### Quantified counterfactuals -/

/-- The four quantifiers of the test sentences (15) are *all*, *none*, *some*, and *not all* of
the players would have won. -/
inductive Quant
  | all | none | some | notAll
  deriving DecidableEq, Repr, Fintype

/-- Quantificational force is the paper's binary, on which *all* and *none* are universal and
*some* and *not all* existential. -/
inductive Force
  | universal | existential
  deriving DecidableEq, Repr

/-- The force of a quantifier. -/
def Quant.force : Quant → Force
  | .all | .none => .universal
  | .some | .notAll => .existential

/-- A quantifier is positive when it is *all* or *some*, and negative when it is *none* or *not
all*. -/
def Quant.IsPositive : Quant → Prop
  | .all | .some => True
  | .none | .notAll => False

/-- The selectional theory's verdict in a mixed scenario is fixed by force alone. -/
def Force.verdict : Force → SignType
  | .universal => (-1)
  | .existential => 1

/-- The quantifier applied to a domain and a predicate. -/
def Quant.eval {ι : Type*} (q : Quant) (D : Finset ι) (P : ι → Prop) : Prop :=
  match q with
  | .all => ∀ d ∈ D, P d
  | .none => ∀ d ∈ D, ¬ P d
  | .some => ∃ d ∈ D, P d
  | .notAll => ∃ d ∈ D, ¬ P d

instance {ι : Type*} (q : Quant) (D : Finset ι) (P : ι → Prop) [DecidablePred P] :
    Decidable (q.eval D P) := by
  cases q <;> dsimp only [Quant.eval] <;> infer_instance

/-- The quantifier projects through the players' trivalent values by the Kleene meet for the
universal quantifiers and the Kleene join for the existential ones, over the values or their
negations. -/
def Quant.aggregate {ι : Type*} (q : Quant) (D : Finset ι) (v : ι → SignType) : SignType :=
  match q with
  | .all => D.inf v
  | .none => D.inf fun d ↦ -v d
  | .some => D.sup v
  | .notAll => D.sup fun d ↦ -v d

variable {W ι : Type*} (ord : W → Preorder W) (A : Set W) (w : W) (D : Finset ι) (B : ι → Set W)

/-! ### Mixed scenarios -/

/-- A scenario is mixed, win some and lose some, when there are players, every closest
antecedent world has a winner and a loser among them, and every player wins in some closest
world and loses in another. -/
structure Mixed : Prop where
  nonempty : D.Nonempty
  worlds : ∀ w' ∈ (ord w).minimals A, (∃ d ∈ D, w' ∈ B d) ∧ ∃ d ∈ D, w' ∉ B d
  players : ∀ d ∈ D,
    (∃ w' ∈ (ord w).minimals A, w' ∈ B d) ∧ ∃ w' ∈ (ord w).minimals A, w' ∉ B d

theorem Mixed.closest_nonempty (h : Mixed ord A w D B) : ((ord w).minimals A).Nonempty :=
  let ⟨d, hd⟩ := h.nonempty
  let ⟨⟨w₁, hw₁, _⟩, _⟩ := h.players d hd
  ⟨w₁, hw₁⟩

/-! ### The theories on a quantified sentence -/

section

variable [Fintype W] [∀ w, DecidableRel (ord w).le] [DecidablePred (· ∈ A)]
  [∀ d, DecidablePred (· ∈ B d)]

/-- The universal theory (2) applies the quantifier to the players' universal counterfactuals. -/
def universal (q : Quant) : Prop := q.eval D fun d ↦ w ∈ closestImp ord A (B d)

instance (q : Quant) : DecidablePred (· ∈ {v : W | q.eval D fun d ↦ v ∈ B d}) :=
  fun _ ↦ inferInstanceAs (Decidable (q.eval D _))

/-- The selectional theory (5) takes the selectional counterfactual of the quantified sentence,
the sentence evaluated at the selected world and supervaluated over the candidate selections. -/
def selectional (q : Quant) : SignType :=
  selectionalCounterfactual ord A {v | q.eval D fun d ↦ v ∈ B d} w

/-- On the homogeneity theory (6) each player's counterfactual carries its third status into
composition, and the quantifier projects it. -/
noncomputable def homogeneity (q : Quant) : SignType :=
  q.aggregate D fun d ↦ homogeneityCounterfactual ord A (B d) w

/-- The implicature theory (§8) pairs the basic existential meaning (23) with its exhaustified
universal strengthening (24), the latter computed in the upward-entailing scope of *some* and
the former in the downward-entailing scope of *not all*. -/
def implicature (q : Quant) : Prop :=
  match q with
  | .all => ∀ d ∈ D, w ∈ closestImp ord A (B d)
  | .none => ∀ d ∈ D, w ∉ might (closestImp ord) A (B d)
  | .some => ∃ d ∈ D, w ∈ closestImp ord A (B d)
  | .notAll => ∃ d ∈ D, w ∉ might (closestImp ord) A (B d)

variable {ord A w D B}

/-! ### Predictions in mixed scenarios -/

/-- In the unembedded case of Table 1, the counterfactual is false, indeterminate and undefined on
the universal, selectional and homogeneity theories respectively. -/
theorem unembedded (h : Mixed ord A w D B) {d : ι} (hd : d ∈ D) :
    w ∉ closestImp ord A (B d) ∧
      selectionalCounterfactual ord A (B d) w = 0 ∧
      homogeneityCounterfactual ord A (B d) w = 0 := by
  obtain ⟨⟨w₁, hw₁, hB₁⟩, ⟨w₂, hw₂, hB₂⟩⟩ := h.players d hd
  have hnot : w ∉ closestImp ord A (B d) := fun hall ↦ hB₂ (hall hw₂)
  have hnot' : w ∉ closestImp ord A (B d)ᶜ := fun hnone ↦ hnone hw₁ hB₁
  exact ⟨hnot, selectionalCounterfactual_eq_zero_iff.2 ⟨hnot, hnot'⟩,
    homogeneityCounterfactual_eq_zero_iff.2 ⟨hnot, hnot'⟩⟩

theorem universal_polarity (h : Mixed ord A w D B) (q : Quant) :
    universal ord A w D B q ↔ ¬ q.IsPositive := by
  have hfalse : ∀ d ∈ D, w ∉ closestImp ord A (B d) :=
    fun d hd ↦ (unembedded h hd).1
  cases q
  · simp only [universal, Quant.eval, Quant.IsPositive, not_true_eq_false, iff_false]
    exact fun hall ↦ let ⟨d, hd⟩ := h.nonempty; hfalse d hd (hall d hd)
  · simp only [universal, Quant.eval, Quant.IsPositive, not_false_eq_true, iff_true]
    exact hfalse
  · simp only [universal, Quant.eval, Quant.IsPositive, not_true_eq_false, iff_false]
    exact fun ⟨d, hd, hc⟩ ↦ hfalse d hd hc
  · simp only [universal, Quant.eval, Quant.IsPositive, not_false_eq_true, iff_true]
    exact let ⟨d, hd⟩ := h.nonempty; ⟨d, hd, hfalse d hd⟩

/-- On the selectional theory the quantified sentence is false for universal and true for
existential quantifiers, whatever the polarity (Table 3). -/
theorem selectional_force (h : Mixed ord A w D B) (q : Quant) :
    selectional ord A w D B q = q.force.verdict := by
  obtain ⟨v, hv⟩ := h.closest_nonempty
  cases q
  · exact selectionalCounterfactual_eq_neg_one_iff.2 ⟨fun hall ↦
      let ⟨d, hd, hB⟩ := (h.worlds v hv).2; hB (hall hv d hd),
      fun w' hw' (hall : ∀ d ∈ D, w' ∈ B d) ↦
        let ⟨d, hd, hB⟩ := (h.worlds w' hw').2; hB (hall d hd)⟩
  · exact selectionalCounterfactual_eq_neg_one_iff.2 ⟨fun hnone ↦
      let ⟨d, hd, hB⟩ := (h.worlds v hv).1; hnone hv d hd hB,
      fun w' hw' (hnone : ∀ d ∈ D, w' ∉ B d) ↦
        let ⟨d, hd, hB⟩ := (h.worlds w' hw').1; hnone d hd hB⟩
  · exact selectionalCounterfactual_eq_one_iff.2 fun w' hw' ↦ (h.worlds w' hw').1
  · exact selectionalCounterfactual_eq_one_iff.2 fun w' hw' ↦ (h.worlds w' hw').2

theorem selectional_determinate (h : Mixed ord A w D B) (q : Quant) :
    selectional ord A w D B q ≠ 0 := by
  rw [selectional_force h]
  cases q <;> simp [Quant.force, Force.verdict]

theorem homogeneity_undefined (h : Mixed ord A w D B) (q : Quant) :
    homogeneity ord A w D B q = 0 := by
  have hv : ∀ d ∈ D, homogeneityCounterfactual ord A (B d) w = 0 := fun d hd ↦
    (unembedded h hd).2.2
  have hn : ∀ d ∈ D, -homogeneityCounterfactual ord A (B d) w = 0 :=
    fun d hd ↦ by rw [hv d hd, SignType.neg_zero]
  cases q
  · exact (Finset.inf_congr rfl hv).trans (Finset.inf_const h.nonempty _)
  · exact (Finset.inf_congr rfl hn).trans (Finset.inf_const h.nonempty _)
  · exact (Finset.sup_congr rfl hv).trans (Finset.sup_const h.nonempty _)
  · exact (Finset.sup_congr rfl hn).trans (Finset.sup_const h.nonempty _)

/-- With the implicature computed in its scope, *some* says that some player was guaranteed to
win (25), which is false in the scenario. -/
theorem implicature_some (h : Mixed ord A w D B) : ¬ implicature ord A w D B .some :=
  fun ⟨_, hd, hc⟩ ↦ (unembedded h hd).1 hc

end

variable {ord A w D B}

/-- With the basic existential meaning in its scope, *not all* says that some player could not
have won (26), which is false in the scenario. -/
theorem implicature_notAll (h : Mixed ord A w D B) : ¬ implicature ord A w D B .notAll :=
  fun ⟨d, hd, hc⟩ ↦ hc fun hall ↦
    let ⟨_, hw₁, hB₁⟩ := (h.players d hd).1
    hall hw₁ hB₁

variable [Fintype W] [∀ w, DecidableRel (ord w).le] [DecidablePred (· ∈ A)]
  [∀ d, DecidablePred (· ∈ B d)]

theorem dissociation (h : Mixed ord A w D B) {v : W}
    (hv : (∃ d ∈ D, v ∈ B d) ∧ ∃ d ∈ D, v ∉ B d) (q : Quant) :
    SignType.supervaluation D (v ∈ B ·) = 0 ∧ selectional ord A w D B q ≠ 0 :=
  ⟨(SignType.supervaluation_eq_zero_iff D (v ∈ B ·)).2 hv, selectional_determinate h q⟩

end RamotowskaEtAl2025
