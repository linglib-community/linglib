module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Semantics.Conditionals.Counterfactual.Alternatives
public import Studies.McKayVanInwagen1977
public import Linglib.Data.Examples.AlonsoOvalle2009

/-!
# Alonso-Ovalle (2009): counterfactuals, correlatives, and disjunction

A *would*-counterfactual with a disjunctive antecedent is read as checking the consequent in
the closest worlds of each disjunct, which a minimal-change semantics with Boolean *or*
cannot do: on the bumper-crop scenario (1) it hands the modal the union and predicts the
counterfactual true (`bumperCrop_boolean`). The paper keeps minimal change and instead lets
*or* introduce its disjuncts as Hamblin alternatives (10) and treats conditionals as
correlatives: the *if*-clause universally quantifies over the alternatives (25) and the
consequent, abstracted over the propositional anaphor *then*, supplies the modal (24). The
composition is `distributiveImp` for *would* and `DistributiveMight` for *might*; it validates
Simplification (27), makes (1) false (`bumperCrop_alternatives`), and leaves the negated (29)
true when one simplification holds, where a sum with the homogeneity presupposition (33)
gives a gap (`hitler_negation`, `homogeneity_ne_false`).

Rival derivations fail. A strict conditional makes Simplification a monotonicity inference
(`strict_simplification`) but not for the dual *might* (`strictMight_not_simplifying`), and
Stalnaker's ◇(*would*) recovers it (`stalnaker_might_simplification`) only for epistemic
modals. On von Fintel's modal horizon (44)–(45), Simplification is Strawson-valid like
Strengthening the Antecedent (`horizonWould_anti`) but not dynamically valid
(`horizon_sunCold_undefined`). The manner implicature (75)–(76) does not deliver both
simplifications (`manner_insufficient`). Nute's (80) is a contradiction unless a disjunct is
impossible (`distributive_pair_disjoint_iff`) and needs Existential Closure (82) (`budget`).
The paper's verdicts are checked in `rows_agree`.

## References

* [alonso-ovalle-2009]
* [lewis-1973b]
* [mckay-vaninwagen-1977]
* [nute-1975]
* [hamblin-1973b]
* [dayal-1996]
* [von-fintel-2000]
* [von-fintel-1999]
* [stalnaker-1984]
* [bennett-2003]
* [lewis-1977]
-/

@[expose] public section

namespace AlonsoOvalle2009

open Conditional McKayVanInwagen1977

variable {W : Type*} (ord : W → Preorder W) (S : Finset (Finset W)) (C : Set W) (w : W)

section

variable [DecidableEq W]

/-! ### Conditionals as correlatives (§2) -/

section

variable [Fintype W] [∀ w, DecidableRel (ord w).le] [DecidablePred (· ∈ C)]

/-- *Might* in the consequent (70)–(71) under the universal *if*-clause (25) holds when the
closest worlds of every alternative are compatible with the consequent. -/
def DistributiveMight : Prop := ∀ A ∈ S, w ∈ might (closestImp ord) ↑A C

instance : Decidable (DistributiveMight ord S C w) :=
  inferInstanceAs (Decidable (∀ A ∈ S, w ∈ might (closestImp ord) ↑A C))

end

/-- Simplification (27) says that the disjunctive counterfactual entails each disjunct's. -/
theorem simplification {A B : Finset W} (h : w ∈ distributiveImp ord {A, B} C) :
    w ∈ closestImp ord ↑A C ∧ w ∈ closestImp ord ↑B C :=
  mem_distributiveImp_pair.1 h

/-- Simplification for *might* (54), the extension of §3.3. -/
theorem simplification_might {A B : Finset W} (h : DistributiveMight ord {A, B} C w) :
    w ∈ might (closestImp ord) ↑A C ∧ w ∈ might (closestImp ord) ↑B C :=
  ⟨h A (by simp), h B (by simp)⟩

/-- The good-weather and cold-sun worlds of the bumper-crop model. -/
abbrev goodWeatherW : Finset CropWorld := Finset.univ.filter (· ∈ goodWeather)
abbrev sunColdW : Finset CropWorld := Finset.univ.filter (· ∈ sunCold)

/-- Boolean *or* (6) hands the modal the union, and (1) comes out true (Fig. 1). -/
theorem bumperCrop_boolean :
    .actual ∈ disjunctiveImp cropSim {goodWeatherW, sunColdW} bumperCrop := by
  decide

/-- With the disjuncts as alternatives (13) under universal force (26), (1) is false, since the
closest cold-sun worlds have no crop. -/
theorem bumperCrop_alternatives :
    .actual ∉ distributiveImp cropSim {goodWeatherW, sunColdW} bumperCrop := by decide

/-! ### Universal quantifier or sum (§2.2.3) -/

theorem homogeneity_ne_false [Fintype W] [∀ w, DecidableRel (ord w).le] [DecidablePred (· ∈ C)]
    {A : Finset W} (hA : A ∈ S)
    (h : w ∈ closestImp ord ↑A C) : homogeneousImp ord S C w ≠ -1 :=
  fun hf ↦ (homogeneousImp_eq_neg_one_iff.1 hf).2 A hA h

/-- In (29)–(31) Spain joining Germany is closer than Spain joining the U.S., and Hitler is
pleased only in the former. -/
inductive HitlerWorld | actual | germany | us
  deriving DecidableEq, Fintype

def HitlerWorld.rank : HitlerWorld → ℕ
  | .actual => 0 | .germany => 1 | .us => 2

abbrev hitlerSim (_ : HitlerWorld) : Preorder HitlerWorld := Preorder.lift HitlerWorld.rank

abbrev joinedGermany : Finset HitlerWorld := {.germany}
abbrev joinedUS : Finset HitlerWorld := {.us}

abbrev pleased : Set HitlerWorld := {.germany}

/-- Sentence (29) is true under the universal quantifier, as (30a) holds and (30b) fails per (31),
and a gap under a homogeneous sum (33). -/
theorem hitler_negation :
    .actual ∉ distributiveImp hitlerSim {joinedGermany, joinedUS} pleased ∧
      .actual ∈ closestImp hitlerSim ↑joinedGermany pleased ∧
      .actual ∉ closestImp hitlerSim ↑joinedUS pleased ∧
      homogeneousImp hitlerSim {joinedGermany, joinedUS} pleased .actual = 0 := by decide

end

/-! ### Downward entailingness (§3) -/

section Strict

variable {I : Type*} (access : I → Set W) (φ ψ χ : Set W)

/-- A strict conditional is antitone in its antecedent, so Simplification is a monotonicity
inference, (37)–(38). -/
theorem strict_simplification {i : I} (h : i ∈ strictImp access (φ ∪ ψ) χ) :
    i ∈ strictImp access φ χ ∧ i ∈ strictImp access ψ χ :=
  ⟨strictImp_anti_left Set.subset_union_left h, strictImp_anti_left Set.subset_union_right h⟩

/-- Stalnaker's *might* counterfactual, epistemic possibility over `E` of the strict *would*,
inherits Simplification, (60)–(64). -/
theorem stalnaker_might_simplification (E : I → Set I) {i : I}
    (h : ∃ i' ∈ E i, i' ∈ strictImp access (φ ∪ ψ) χ) :
    (∃ i' ∈ E i, i' ∈ strictImp access φ χ) ∧ ∃ i' ∈ E i, i' ∈ strictImp access ψ χ :=
  let ⟨i', hi, hs⟩ := h
  ⟨⟨i', hi, (strict_simplification access φ ψ χ hs).1⟩,
    ⟨i', hi, (strict_simplification access φ ψ χ hs).2⟩⟩

end Strict

section

variable [DecidableEq W]

section

variable [Fintype W] [∀ w, DecidableRel (ord w).le]

/-- Accommodation (44) grows the modal horizon `f` by every world at least as close as the
closest antecedent worlds. -/
def expand (f : W → Finset W) (φ : Finset W) (w : W) : Finset W :=
  f w ∪ Finset.univ.filter fun w' => ∀ w'' ∈ φ, (ord w).le w' w''

end

/-- The counterfactual on a horizon (45) holds when every antecedent world in the horizon is a
consequent world. -/
def horizonWould (f : W → Finset W) (φ ψ : Finset W) (w : W) : Prop :=
  ∀ w' ∈ f w ∩ φ, w' ∈ ψ

/-- The presupposition of (45) is that the horizon reaches the antecedent. -/
def HorizonReaches (f : W → Finset W) (φ : Finset W) (w : W) : Prop := (f w ∩ φ).Nonempty

instance (f : W → Finset W) (φ : Finset W) : Decidable (HorizonReaches f φ w) :=
  inferInstanceAs (Decidable (f w ∩ φ).Nonempty)

/-- Strengthening the Antecedent and Simplification alike are Strawson valid (50), since on a
horizon that already reaches the stronger antecedent, (45) is antitone in it. -/
theorem horizonWould_anti {f : W → Finset W} {φ φ' ψ : Finset W} (h : φ' ⊆ φ)
    (hw : horizonWould f φ ψ w) : horizonWould f φ' ψ w :=
  fun w' hw' =>
    hw w' (Finset.mem_inter.2 ⟨(Finset.mem_inter.1 hw').1, h (Finset.mem_inter.1 hw').2⟩)

/-- Simplification is dynamically invalid (47), since accommodating (48)'s antecedent from the
initial horizon reaches the good-weather world only, so (49b) is undefined. -/
theorem horizon_sunCold_undefined :
    ¬ HorizonReaches (expand cropSim (fun w => {w}) (goodWeatherW ∪ sunColdW)) sunColdW
      .actual := by decide

/-! ### Might counterfactuals (§3.2) -/

/-- In (51) having a magic book is closer than being a newborn baby, and the fork is bent in
one of the closest magic-book worlds and in no newborn world (Fig. 2). -/
inductive ForkWorld | actual | book | bookBent | baby
  deriving DecidableEq, Fintype

def ForkWorld.rank : ForkWorld → ℕ
  | .actual => 0 | .book | .bookBent => 1 | .baby => 2

abbrev forkSim (_ : ForkWorld) : Preorder ForkWorld := Preorder.lift ForkWorld.rank

abbrev hasBook : Finset ForkWorld := {.book, .bookBent}
abbrev newborn : Finset ForkWorld := {.baby}

abbrev bent : Set ForkWorld := {.bookBent}

/-- Under (52)–(53), (51) is true because the closest union-worlds are magic-book worlds, but false
on the correlative analysis, with (58a) true and (58b) not. -/
theorem fork :
    .actual ∈ might (closestImp forkSim) ↑(hasBook ∪ newborn) bent ∧
      ¬ DistributiveMight forkSim {hasBook, newborn} bent .actual ∧
      .actual ∈ might (closestImp forkSim) ↑hasBook bent ∧
      .actual ∉ might (closestImp forkSim) ↑newborn bent := by decide

/-- The strict dual *might*, with every world accessible, is true of the disjunction but not of
the newborn disjunct, (57)–(58). -/
theorem strictMight_not_simplifying :
    (∃ w, w ∈ hasBook ∪ newborn ∧ w ∈ bent) ∧ ¬ ∃ w, w ∈ newborn ∧ w ∈ bent := by decide

/-! ### An implicature? (§4) -/

/-- Figures 3–4 have two worlds compatible with the speaker's beliefs; magic-book and newborn
worlds are equally close to each, and the fork is bent in a closest magic-book world of the
first and in a closest newborn world of the second. -/
inductive BeliefWorld | w₃ | book₃ | baby₃ | w₄ | book₄ | baby₄
  deriving DecidableEq, Fintype

def BeliefWorld.rank : BeliefWorld → BeliefWorld → ℕ
  | .w₃, .w₃ | .w₄, .w₄ => 0
  | .w₃, .book₃ | .w₃, .baby₃ | .w₄, .book₄ | .w₄, .baby₄ => 1
  | _, _ => 2

abbrev beliefSim (w₀ : BeliefWorld) : Preorder BeliefWorld := Preorder.lift (BeliefWorld.rank w₀)

abbrev belief : Finset BeliefWorld := {.w₃, .w₄}
abbrev bookB : Finset BeliefWorld := {.book₃, .book₄}
abbrev babyB : Finset BeliefWorld := {.baby₃, .baby₄}

abbrev bentB : Set BeliefWorld := {.book₃, .baby₄}

/-- Manner (75)–(76) holds, with (73) true throughout the belief state and neither (74a) nor (74b),
yet (77) is not predicted deviant. -/
theorem manner_insufficient :
    (∀ w ∈ belief, w ∈ might (closestImp beliefSim) ↑(bookB ∪ babyB) bentB) ∧
      (∃ w ∈ belief, w ∉ might (closestImp beliefSim) ↑bookB bentB) ∧
      (∃ w ∈ belief, w ∉ might (closestImp beliefSim) ↑babyB bentB) ∧
      ∀ w ∈ belief, ¬ DistributiveMight beliefSim {bookB, babyB} bentB w := by decide

/-! ### The visibility of the disjuncts (§5.2) -/

/-- On Nute's recipe (80), a counterfactual with one of two incompatible disjuncts as consequent is
true only if the other is impossible. -/
theorem distributive_pair_disjoint_iff {A B : Finset W} (h : Disjoint A B) :
    w ∈ distributiveImp ord {A, B} ↑A ↔ B = ∅ := by
  rw [mem_distributiveImp_pair]
  refine ⟨fun hd ↦ ?_, fun hB ↦ ⟨Preorder.minimals_subset _ _, by simp [hB]⟩⟩
  by_contra hne
  obtain ⟨b, hb⟩ := (ord w).minimals_nonempty_of_finite B.finite_toSet
    (Finset.coe_nonempty.2 (Finset.nonempty_iff_ne_empty.2 hne))
  exact Finset.disjoint_left.1 h (hd.2 hb) (Preorder.minimals_subset _ _ hb)

/-- In (80) more defense spending is closer than more education spending. -/
inductive BudgetWorld | actual | defense | education
  deriving DecidableEq, Fintype

def BudgetWorld.rank : BudgetWorld → ℕ
  | .actual => 0 | .defense => 1 | .education => 2

abbrev budgetSim (_ : BudgetWorld) : Preorder BudgetWorld := Preorder.lift BudgetWorld.rank

abbrev defense : Finset BudgetWorld := {.defense}
abbrev education : Finset BudgetWorld := {.education}

/-- (80) is a contradiction under the analysis and true once Existential Closure (82)
returns the Boolean antecedent. -/
theorem budget :
    (∀ w, w ∉ distributiveImp budgetSim {defense, education} ↑defense) ∧
      .actual ∈ disjunctiveImp budgetSim {defense, education} ↑defense :=
  ⟨fun w h ↦ by simpa using (distributive_pair_disjoint_iff budgetSim w (by decide)).1 h,
    by decide⟩

/-! ### The paper's verdicts -/

/-- The alternatives a row's `antecedent` feature names in each model. -/
def cropAlts : String → Option (Finset (Finset CropWorld))
  | "good weather" => some {goodWeatherW}
  | "sun cold" => some {sunColdW}
  | "good weather or sun cold" => some {goodWeatherW, sunColdW}
  | _ => none

def hitlerAlts : String → Option (Finset (Finset HitlerWorld))
  | "joined Germany" => some {joinedGermany}
  | "joined the U.S." => some {joinedUS}
  | "joined Germany or the U.S." => some {joinedGermany, joinedUS}
  | _ => none

def forkAlts : String → Option (Finset (Finset ForkWorld))
  | "magic book" => some {hasBook}
  | "newborn baby" => some {newborn}
  | "magic book or newborn baby" => some {hasBook, newborn}
  | _ => none

variable [Fintype W] [∀ w, DecidableRel (ord w).le] [DecidablePred (· ∈ C)]

/-- The verdict of the analysis for a *would* or *might* consequent, possibly negated. -/
def verdict : String → Bool → Option Bool
  | "would", neg => some (decide (w ∈ distributiveImp ord S C) != neg)
  | "might", neg => some (decide (DistributiveMight ord S C w) != neg)
  | _, _ => none

/-- A row's predicted verdict from its `scenario`, `antecedent`, `modal`, and `polarity`
features; (80) takes the Existential Closure reading (82). -/
def predicted (row : Datum) : Option Bool :=
  let neg := decide (row.feature? "polarity" = some "negated")
  match row.feature? "scenario", row.feature? "antecedent", row.feature? "modal" with
  | some "bumperCrop", some a, some m =>
    cropAlts a >>= fun S => verdict cropSim S bumperCrop .actual m neg
  | some "hitler", some a, some m =>
    hitlerAlts a >>= fun S => verdict hitlerSim S pleased .actual m neg
  | some "fork", some a, some m => forkAlts a >>= fun S => verdict forkSim S bent .actual m neg
  | some "budget", some "defense or education", some "would" =>
    some (decide (.actual ∈ disjunctiveImp budgetSim {defense, education} ↑defense))
  | _, _, _ => none

theorem rows_agree : Datum.ChecksVerdict predicted id Examples.all 10 := by
  decide +kernel

end

end AlonsoOvalle2009
