module

public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic.DeriveFintype

/-!
# Morphological causation: compactness and directness

Causative constructions vary along two scales: **morphological complexity**, from compact
(lexical) to analytic (periphrastic), and **directness of mediation**, from a causer that brings
about the result itself to one that acts through a causee. [comrie-1989]'s generalization is that
within a language the more compact construction expresses the more direct causation
(`CausativeConstruction.ComrieMonotone`). The causee of a causativized verb takes the highest
grammatical relation not already filled by the causer and the base verb's other arguments
(`causeeDemotion`), so the causee sinks as the base valency rises (`causeeDemotion_antitone`).

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

/-- Direct < indirect: the directness scale. -/
instance : LinearOrder Mediation := LinearOrder.lift' (·.ctorIdx) (by decide)

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
  deriving DecidableEq, Repr, Fintype

/-- Lexical < morphological < periphrastic: the compactness scale, compact first. -/
instance : LinearOrder CausativeComplexity := LinearOrder.lift' (·.ctorIdx) (by decide)

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

/-! ### The causee hierarchy -/

/-- The grammatical relations of [comrie-1989]'s causative hierarchy, subject > direct object >
indirect object > oblique. The causee of a causativized verb takes the highest of them that is not
already filled, so an intransitive base yields a direct-object causee, a transitive one an
indirect-object causee, and a ditransitive one an oblique causee. -/
inductive CauseeSlot where
  | oblique
  | indirectObject
  | directObject
  | subject
  deriving DecidableEq, Repr, Fintype

/-- Oblique < indirect object < direct object < subject. -/
instance : LinearOrder CauseeSlot := LinearOrder.lift' (·.ctorIdx) (by decide)

/-- The subject tops the hierarchy and the oblique is its bottom. -/
instance : BoundedOrder CauseeSlot where
  top := .subject
  le_top := by decide
  bot := .oblique
  bot_le := by decide

instance : LocallyFiniteOrder CauseeSlot := Fintype.toLocallyFiniteOrder

/-- The slots filled before the causee is placed, in the causative of a base verb with `n`
arguments: the subject by the causer, and the slots below it by the base verb's other arguments,
which keep their relations, down to the `n`th slot from the top. No oblique is ever filled, a
clause admitting any number of them. -/
def CauseeSlot.filled (n : ℕ) : Finset CauseeSlot := {s | s ≠ .oblique ∧ (Finset.Ioi s).card < n}

theorem CauseeSlot.oblique_notMem_filled (n : ℕ) : oblique ∉ filled n := by simp [filled]

theorem CauseeSlot.filled_mono : Monotone filled := fun _ _ h _ ↦ by
  simp only [filled, Finset.mem_filter, Finset.mem_univ, true_and]
  exact fun ⟨hs, hn⟩ ↦ ⟨hs, hn.trans_le h⟩

/-- The causee of a base verb with `n` arguments takes the highest slot not already filled. -/
def causeeDemotion (n : ℕ) : CauseeSlot :=
  (CauseeSlot.filled n)ᶜ.max' ⟨.oblique, Finset.mem_compl.2 (CauseeSlot.oblique_notMem_filled n)⟩

theorem isGreatest_causeeDemotion (n : ℕ) :
    IsGreatest ↑(CauseeSlot.filled n)ᶜ (causeeDemotion n) :=
  Finset.isGreatest_max' _ _

theorem causeeDemotion_antitone : Antitone causeeDemotion := fun _ _ h ↦
  Finset.max'_subset _ (Finset.compl_subset_compl.2 (CauseeSlot.filled_mono h))

end Causation.Morphological
