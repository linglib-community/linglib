module

public import Linglib.Logic.Team.Closure

/-!
# Definability for team-semantic logics

A formula of a team logic expresses the property of the points that support it, and
`Team.definableClass s` is the class of properties expressed under a support relation `s`. The
expressive power of a logic is this class: taking the points to be pointed team models over the
atoms $\mathsf{X}$ gives what Anttila writes $\|L\|_{\mathsf{X}}$, and a logic is expressively
complete for a class of properties when the two are equal. [Closure of every expressed
property](##Team.definableClass_subset) gives one inclusion, and the converse goes through normal
forms in each logic.

## Implementation notes

The points are arbitrary, since the class only reads the support relation. The source's
propositional properties are classes of teams of valuations, and its modal ones classes of pointed
team models. Over the teams of a single Kripke model, closure properties and non-definability
transfer to the logic, but completeness there concerns that model only: the class over
`ModalLogic.PointedTeam` is the one the source calls $\|L\|_{\mathsf{X}}$.

## References

* [anttila-2025]
-/

@[expose] public section

namespace Team

variable {Form Pt : Type*} {s : Form → Pt → Prop}

/-- The class of properties expressed under the support relation `s`: the support sets of the
formulas. -/
abbrev definableClass (s : Form → Pt → Prop) : Set (Set Pt) :=
  Set.range fun φ ↦ {t | s φ t}

/-- If every formula's support set satisfies `C`, so does every expressed property. -/
theorem definableClass_subset {C : Set Pt → Prop} (h : ∀ φ, C {t | s φ t}) :
    definableClass s ⊆ {P | C P} :=
  Set.range_subset_iff.2 h

end Team
