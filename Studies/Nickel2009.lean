module

public import Linglib.Semantics.Quantification.Counting
public import Studies.Cohen1999

/-!
# Nickel (2009): Generics and the Ways of Normality

This file formalizes the argument of [nickel-2009] from conjunctive generics against
majority-based accounts of the generic operator. *Elephants live in Africa and Asia* is
sentential conjunction, *elephants live in Africa and elephants live in Asia*, and is true
although no majority of elephants lives in either place, so the probabilistic operator of
[cohen-1999a] predicts it false (`cohen_fails_elephant_asia`). Normality comes in ways: a
characterizing sentence is true when there is a way of being normal in the respect the
predicate determines such that every individual normal in that way satisfies the predicate
(`nickelGEN`), so each conjunct of a conjunctive generic may draw on its own way
(`nickelConjunctiveGEN`, `nickel_handles_elephant_conjunction`,
`bears_nickel_succeeds`), and the ways are incompatible without the conjunction entailing
that anything lives in both places (`ways_incompatible`).

## Implementation notes

The ways are indices selecting the individuals that count as normal, the actual-extension
proxy for the paper's respects of normality and its inductive targets; the counterfactual
element the paper notes it needs when no individual is normal in a way is not represented,
so the operator holds vacuously in that case. Each toy model is a finite type of entities,
over which GEN is the type-level `every`. The comparison with Cohen's operator runs over one
shared toy model, with the habitats as the alternative set.

## References

* [nickel-2009]
* [cohen-1999a]
-/

@[expose] public section

namespace Nickel2009

open Quantifier.GQ (every)

/-! ### Ways of Being Normal -/

/-- A way of being normal, an index selecting which entities count as normal for a given
generalization. Different generic claims can appeal to different normality ways. -/
structure NormalcyWay where
  id : ℕ
  deriving DecidableEq, Repr

/-! ### Nickel's GEN

GEN is the restricted universal `every` under an existential over normality ways, so the only
apparatus specific to Nickel is the existential over ways. -/

section GEN

variable {α : Type*} (normalIn : α → NormalcyWay → Prop) (ways : Finset NormalcyWay)
  (restrictor scope scope' : α → Prop)

/-- Nickel's GEN with way-indexed normality holds when there is a way of being normal such
that every entity normal in that way and satisfying the restrictor satisfies the scope. The
existential over ways lets different conjuncts of a conjunctive generic use different ways. -/
def nickelGEN : Prop :=
  ∃ w ∈ ways, every (fun e ↦ restrictor e ∧ normalIn e w) scope

/-- A conjunctive generic holds when both `GEN[A][F₁]` and `GEN[A][F₂]` hold, possibly through
different normality ways. -/
def nickelConjunctiveGEN : Prop :=
  nickelGEN normalIn ways restrictor scope ∧ nickelGEN normalIn ways restrictor scope'

/-- Normality ways are pairwise incompatible when no entity is normal in two distinct ways.
The paper (p. 643) states this holds "usually (perhaps always)"; here it is a property of the
toy model, not a commitment of the account. -/
def WaysIncompatible : Prop :=
  ∀ e, ∀ w₁ ∈ ways, ∀ w₂ ∈ ways, w₁ ≠ w₂ → ¬ (normalIn e w₁ ∧ normalIn e w₂)

variable [Fintype α] [DecidablePred restrictor] [DecidablePred scope] [DecidablePred scope']
  [∀ w, DecidablePred (normalIn · w)]

instance : Decidable (nickelGEN normalIn ways restrictor scope) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

instance : Decidable (nickelConjunctiveGEN normalIn ways restrictor scope scope') :=
  inferInstanceAs (Decidable (_ ∧ _))

instance : Decidable (WaysIncompatible normalIn ways) :=
  inferInstanceAs (Decidable (∀ _, _))

end GEN

/-! ### The Elephant Example (2b/11) -/

section Elephants

/-- Ten elephants, six African (`0`–`5`) and four Asian (`6`–`9`). -/
abbrev Elephant := Fin 10

abbrev isElephant : Elephant → Prop := fun _ ↦ True
abbrev livesInAfrica : Elephant → Prop := (· < 6)
abbrev livesInAsia : Elephant → Prop := (6 ≤ ·)

def africanWay : NormalcyWay := ⟨1⟩
def asianWay : NormalcyWay := ⟨2⟩
def ways : Finset NormalcyWay := {africanWay, asianWay}

/-- Normal in the African way are the African elephants, in the Asian way the Asian ones. -/
abbrev elephantNormalIn : Elephant → NormalcyWay → Prop := fun e w ↦
  (w.id = 1 ∧ e < 6) ∨ (w.id = 2 ∧ 6 ≤ e)

end Elephants

/-! ### The Bears Example (2a) -/

section Bears

/-- Twenty bears across four continents, five each, with NA `0`–`4`, SA `5`–`9`, EU `10`–`14`
and AS `15`–`19`, so that each habitat is a quarter of the bears. -/
abbrev Bear := Fin 20

abbrev isBear : Bear → Prop := fun _ ↦ True
abbrev bearNA : Bear → Prop := (· < 5)
abbrev bearSA : Bear → Prop := fun e ↦ 5 ≤ e ∧ e < 10
abbrev bearEU : Bear → Prop := fun e ↦ 10 ≤ e ∧ e < 15
abbrev bearAS : Bear → Prop := (15 ≤ ·)

/-- The disjunction of the habitat alternatives, which every bear satisfies. -/
abbrev bearHabitat : Bear → Prop := fun e ↦ bearNA e ∨ bearSA e ∨ bearEU e ∨ bearAS e

def bearWays : Finset NormalcyWay := {⟨1⟩, ⟨2⟩, ⟨3⟩, ⟨4⟩}

abbrev bearNormalIn : Bear → NormalcyWay → Prop := fun e w ↦
  (w.id = 1 ∧ e < 5) ∨ (w.id = 2 ∧ 5 ≤ e ∧ e < 10) ∨
  (w.id = 3 ∧ 10 ≤ e ∧ e < 15) ∨ (w.id = 4 ∧ 15 ≤ e)

end Bears

/-! ### Key Theorems -/

theorem nickel_handles_elephant_conjunction :
    nickelConjunctiveGEN elephantNormalIn ways isElephant livesInAfrica livesInAsia := by
  decide

/-- In the bears example (2a) Nickel's view succeeds for all four habitat conjuncts. -/
theorem bears_nickel_succeeds :
    nickelGEN bearNormalIn bearWays isBear bearNA ∧
    nickelGEN bearNormalIn bearWays isBear bearSA ∧
    nickelGEN bearNormalIn bearWays isBear bearEU ∧
    nickelGEN bearNormalIn bearWays isBear bearAS := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

theorem ways_incompatible :
    WaysIncompatible elephantNormalIn ways ∧ WaysIncompatible bearNormalIn bearWays := by
  decide

/-! ### The majority view fails where Nickel's succeeds

The headline contrast is a theorem over a shared model citing the `gen` of [cohen-1999a]
directly, with the habitats as the alternative set. The majority view fails on the conjunction
because the Asia conjunct has prevalence 4/10 < 1/2, while Nickel's view succeeds. -/

theorem cohen_fails_elephant_asia :
    ¬ Cohen1999.gen .univ isElephant (fun e ↦ livesInAfrica e ∨ livesInAsia e) livesInAsia := by
  decide

theorem cohen_fails_nickel_succeeds_on_conjunction :
    ¬ Cohen1999.gen .univ isElephant (fun e ↦ livesInAfrica e ∨ livesInAsia e) livesInAsia ∧
    nickelConjunctiveGEN elephantNormalIn ways isElephant livesInAfrica livesInAsia :=
  ⟨cohen_fails_elephant_asia, nickel_handles_elephant_conjunction⟩

/-- The bears conjunction (2a) fails for the majority view on every conjunct, since each of the
four habitats is a minority. -/
theorem cohen_fails_all_bear_habitats :
    ¬ Cohen1999.gen .univ isBear bearHabitat bearNA ∧
    ¬ Cohen1999.gen .univ isBear bearHabitat bearSA ∧
    ¬ Cohen1999.gen .univ isBear bearHabitat bearEU ∧
    ¬ Cohen1999.gen .univ isBear bearHabitat bearAS := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-! ### Connection to Traditional GEN -/

theorem nickelGEN_singleton_iff {α : Type*} (normalIn : α → NormalcyWay → Prop)
    (w : NormalcyWay) (restrictor scope : α → Prop) :
    nickelGEN normalIn {w} restrictor scope ↔
      every (fun e ↦ restrictor e ∧ normalIn e w) scope := by
  simp [nickelGEN]

end Nickel2009
