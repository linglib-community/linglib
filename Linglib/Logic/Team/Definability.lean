module

public import Linglib.Logic.Team.Closure

/-!
# Definability and expressive completeness for team-semantic logics

A **team property** over a point type `α` is a class of teams, `Set (Finset α)`. A formula
defines the team property consisting of all teams that support it, and a logic defines the class
`⟦L⟧` of the properties its formulas define ([anttila-2025]). The organizing theorem for the
team-semantic family is **expressive completeness**: `⟦L⟧` equals a class fixed by closure
conditions (downward closure `IsLowerSet`, union closure `SupClosed`, convexity
`Set.OrdConnected`, the empty-team property `∅ ∈ P`, flatness `Team.IsFlat`), plus invariance
under bounded bisimulation in the modal case.

The definable class is stated over an abstract support relation `s : Form → Finset α → Prop`,
so every logic instantiates it with its own `support M`, and a fragment of a language is the
subtype of its formulas. Soundness is `definableClass s ⊆ C` and completeness
`definableClass s = C`; each logic proves the soundness half from its closure theorems through
`definableClass_subset`, and the converse half, through normal forms, is per-logic work.

## Main definitions

* `Team.definableClass s`: the properties definable under `s`, written `⟦L⟧` in [anttila-2025].

## Main results

* `Team.definableClass_subset`: closure of every formula's support set is soundness.

## References

* [anttila-2025] Anttila, Not Nothing: Nonemptiness in Team Semantics
-/

@[expose] public section

namespace Team

variable {α : Type*} {Form : Type*}

/-- The class `⟦L⟧` of team properties **definable** under the support relation `s`: the support
sets of the formulas. -/
def definableClass (s : Form → Finset α → Prop) : Set (TeamProperty α) :=
  Set.range fun φ ↦ {t | s φ t}

@[simp] theorem mem_definableClass {s : Form → Finset α → Prop} {P : TeamProperty α} :
    P ∈ definableClass s ↔ ∃ φ, {t | s φ t} = P :=
  Set.mem_range

/-- **Soundness from closure.** If every formula's support set has the closure property `C`,
every definable property does. -/
theorem definableClass_subset {s : Form → Finset α → Prop} {C : TeamProperty α → Prop}
    (h : ∀ φ, C {t | s φ t}) : definableClass s ⊆ {P | C P} :=
  Set.range_subset_iff.2 h

end Team
