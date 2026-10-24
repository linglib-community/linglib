module

public import Mathlib.Order.Basic
public import Mathlib.Order.Monotone.Defs
public import Mathlib.Tactic.DeriveFintype

/-!
# Morphological causation: compactness and directness

Causative constructions vary along two scales: **morphological complexity**, from compact
(lexical) to analytic (periphrastic), and **directness of mediation**, from a causer that brings
about the result itself to one that acts through a causee. [comrie-1989]'s generalization is that
within a language the more compact construction expresses the more direct causation
(`CausativeConstruction.ComrieMonotone`). The causee of a causativized verb takes the highest
grammatical relation its base verb leaves free (`causeeDemotion`), so the causee sinks as the
base valency rises (`causeeDemotion_antitoneOn`).

## References

* [comrie-1989]
-/

@[expose] public section

namespace Causation.Morphological

/-! ### Mediation -/

/-- Directness of causal mediation between causer and result.

[comrie-1989]: direct causation involves no intermediary, the causer bringing about the result
without an intervening causee decision or action; indirect causation involves a mediating causee
who retains some autonomy over the caused event. -/
inductive Mediation where
  /-- The causer brings about the result itself. -/
  | direct
  /-- The causer acts through an intermediary causee. -/
  | indirect
  deriving DecidableEq, Repr, Fintype

/-- Numeric rank: direct (0) < indirect (1). -/
def Mediation.rank : Mediation → ℕ
  | .direct => 0
  | .indirect => 1

/-- Direct < indirect: the directness scale. -/
instance : LinearOrder Mediation :=
  LinearOrder.lift' Mediation.rank fun a b _ ↦ by cases a <;> cases b <;> simp_all [Mediation.rank]

/-! ### Causative complexity -/

/-- Morphological complexity of a causative construction, [comrie-1989]'s compact-to-analytic
continuum:
- **lexical**: suppletive or idiosyncratic (*kill* ~ *die*, *fell* ~ *fall*)
- **morphological**: a productive affix (Japanese *-(s)ase*)
- **periphrastic**: an analytic multi-word construction (English *make X do Y*) -/
inductive CausativeComplexity where
  | lexical
  | morphological
  | periphrastic
  deriving DecidableEq, Repr

/-- Numeric encoding: lexical (0) < morphological (1) < periphrastic (2). -/
def CausativeComplexity.toNat : CausativeComplexity → ℕ
  | .lexical => 0
  | .morphological => 1
  | .periphrastic => 2

instance : LinearOrder CausativeComplexity :=
  LinearOrder.lift' CausativeComplexity.toNat fun a b _ ↦ by
    cases a <;> cases b <;> simp_all [CausativeComplexity.toNat]

/-! ### Causative constructions and Comrie's generalization -/

/-- A causative construction, located on the two scales. -/
structure CausativeConstruction where
  /-- Morphological complexity (compact → analytic). -/
  complexity : CausativeComplexity
  /-- Direct vs. indirect mediation. -/
  mediation : Mediation
  deriving DecidableEq, Repr

/-- **Comrie's monotonicity** ([comrie-1989]): if construction `c₁` is morphologically more
compact than `c₂`, then `c₁` encodes at least as direct causation as `c₂`. -/
def CausativeConstruction.ComrieMonotone (c₁ c₂ : CausativeConstruction) : Prop :=
  c₁.complexity < c₂.complexity → c₁.mediation ≤ c₂.mediation

instance (c₁ c₂ : CausativeConstruction) : Decidable (c₁.ComrieMonotone c₂) :=
  inferInstanceAs (Decidable (_ → _))

/-! ### The causee-marking hierarchy -/

/-- Grammatical relations available to the causee, ordered from highest to lowest.

[comrie-1989]: when a verb is causativized, its original subject is demoted to the highest
relation on the hierarchy that the base verb's arguments leave free, so an intransitive base
yields a direct-object causee, a transitive one an indirect-object causee, and a ditransitive
one an oblique causee. -/
inductive CauseeSlot where
  | directObject
  | indirectObject
  | oblique
  deriving DecidableEq, Repr, Fintype

/-- Rank on the hierarchy: DO (2) > IO (1) > OBL (0). -/
def CauseeSlot.rank : CauseeSlot → ℕ
  | .directObject => 2
  | .indirectObject => 1
  | .oblique => 0

/-- Oblique < indirect object < direct object: the grammatical-relations hierarchy. -/
instance : LinearOrder CauseeSlot := LinearOrder.lift' CauseeSlot.rank (by decide)

/-- The causee's slot given the base verb's valency: the highest slot the base verb's own
arguments leave free. -/
def causeeDemotion : ℕ → CauseeSlot
  | 1 => .directObject
  | 2 => .indirectObject
  | _ => .oblique

theorem causeeDemotion_antitoneOn : AntitoneOn causeeDemotion (Set.Ici 1) := by
  rintro (_ | _ | _ | a) ha (_ | _ | _ | b) hb hab <;> simp_all [causeeDemotion] <;> decide

end Causation.Morphological
