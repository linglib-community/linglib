module

public import Linglib.Morphology.DistributedMorphology.Neighborhood
public import Mathlib.Data.Multiset.AddSub

/-!
# Impoverishment

Impoverishment deletes features from a terminal before Vocabulary Insertion, the Distributed
Morphology mechanism for syncretism: a context that loses a distinguishing feature falls together
with its neighbor, and insertion retreats to the more general exponent (`winner?_retreat`). A rule
is evaluated at a `Neighborhood`, the focus terminal with the terminals beside it, so whether a
rule is paradigmatic, its condition reading the focus alone, is a theorem about the rule. A rule
whose deletion shrinks bundles only deletes; on a bundle of features it erases its target.

## Main definitions

* `ImpoverishmentRule`: a decidable condition on a neighborhood and the target it deletes;
  `ImpoverishmentRule.apply` takes the deletion as a parameter.
* `ImpoverishmentRule.ofFocus`: the rule whose condition reads the focus alone.
* `ImpoverishmentRule.Paradigmatic`, `ImpoverishmentRule.Syntagmatic`: the condition factors
  through the focus, or reads the context.
* `runChain`: a rule sequence threaded through the focus.

## Main results

* `ImpoverishmentRule.paradigmatic_ofFocus`: a focus-only rule is paradigmatic.
* `ImpoverishmentRule.apply_le`, `ImpoverishmentRule.apply_erase_subset`: a rule whose deletion
  shrinks bundles leaves a bundle below the focus, so impoverishment only deletes.

## Implementation notes

The deletion is a parameter of `apply`, not of the rule, since a rule system shares it;
`Studies/Middleton2026.lean` deletes from the slots of the Taos agreement prefix. On the tree
carrier, impoverishment derives from fission and the coproduct
(`Studies/SenturiaMarcolli2025.lean`).

## References

* [K. Arregi and A. Nevins, *Morphotactics*][arregi-nevins-2012]
-/

@[expose] public section

namespace DistributedMorphology

variable {Bundle Target : Type*}

/-- An Impoverishment rule deletes `target` from the focus of a neighborhood satisfying its
decidable `condition`. -/
structure ImpoverishmentRule (Bundle Target : Type*) where
  /-- The neighborhoods at which the rule fires. -/
  condition : Neighborhood Bundle → Prop
  [decCond : DecidablePred condition]
  /-- The feature the rule deletes from the focus. -/
  target : Target

namespace ImpoverishmentRule

instance (rule : ImpoverishmentRule Bundle Target) : DecidablePred rule.condition := rule.decCond

/-- With the deletion `delete`, a rule removes its target from the focus where its condition
holds, and otherwise leaves the focus as it is. -/
def apply (delete : Bundle → Target → Bundle) (rule : ImpoverishmentRule Bundle Target)
    (n : Neighborhood Bundle) : Bundle :=
  if rule.condition n then delete n.focus rule.target else n.focus

/-- `ofFocus p target` deletes `target` wherever the focus satisfies `p`. -/
def ofFocus (p : Bundle → Prop) [DecidablePred p] (target : Target) :
    ImpoverishmentRule Bundle Target :=
  ⟨fun n ↦ p n.focus, target⟩

/-! ### Paradigmatic and syntagmatic rules

The structural counterpart of [arregi-nevins-2012]'s distinction between rules conditioned by a
single node and rules conditioned by its surroundings. -/

/-- A rule is **paradigmatic** iff its condition factors through the focus, two neighborhoods
with the same focus agreeing on it. -/
def Paradigmatic (r : ImpoverishmentRule Bundle Target) : Prop :=
  ∀ n₁ n₂ : Neighborhood Bundle, n₁.focus = n₂.focus → (r.condition n₁ ↔ r.condition n₂)

/-- A rule is **syntagmatic** iff it is not paradigmatic, so that its condition reads the
context. -/
def Syntagmatic (r : ImpoverishmentRule Bundle Target) : Prop := ¬ r.Paradigmatic

theorem paradigmatic_ofFocus (p : Bundle → Prop) [DecidablePred p] (target : Target) :
    (ofFocus p target).Paradigmatic := fun _ _ h ↦ by simp [ofFocus, h]

/-! ### Impoverishment only deletes -/

/-- A rule whose deletion shrinks bundles leaves a bundle below the focus. -/
theorem apply_le [Preorder Bundle] {delete : Bundle → Target → Bundle}
    (h : ∀ b t, delete b t ≤ b) (rule : ImpoverishmentRule Bundle Target)
    (n : Neighborhood Bundle) : rule.apply delete n ≤ n.focus := by
  unfold apply
  split
  · exact h _ _
  · exact le_rfl

/-- On bundles of features, a rule erases its target from the focus where its condition holds. -/
theorem apply_erase_subset {α : Type*} [DecidableEq α] (rule : ImpoverishmentRule (Finset α) α)
    (n : Neighborhood (Finset α)) : rule.apply Finset.erase n ⊆ n.focus :=
  apply_le (fun _ _ ↦ Finset.erase_subset _ _) rule n

end ImpoverishmentRule

/-! ### Rule chains -/

/-- A chain applies a list of rules to a neighborhood, threading the focus through each step while
holding the context fixed. -/
def runChain {R : Type*} (apply : R → Neighborhood Bundle → Bundle)
    (rules : List R) (n : Neighborhood Bundle) : Bundle :=
  rules.foldl (init := n.focus) fun focus rule ↦ apply rule { n with focus }

theorem runChain_append {R : Type*} (apply : R → Neighborhood Bundle → Bundle)
    (rs₁ rs₂ : List R) (n : Neighborhood Bundle) :
    runChain apply (rs₁ ++ rs₂) n =
      runChain apply rs₂ { n with focus := runChain apply rs₁ n } := by
  simp only [runChain, List.foldl_append]

@[simp] theorem runChain_nil {R : Type*} (apply : R → Neighborhood Bundle → Bundle)
    (n : Neighborhood Bundle) : runChain apply [] n = n.focus := rfl

end DistributedMorphology
