module

public import Linglib.Logic.Team.Closure

/-!
# Definability for team-semantic logics

A formula of a team logic expresses the property of the points that support it, and
`Team.definableClass s` is the class of properties expressed under a support relation `s`. The
expressive power of a logic is this class: taking the points to be pointed team models gives what
Anttila writes $\|L\|$, and a logic is expressively complete for a class of properties when its
$\|L\|$ equals that class. [Closure of every expressed property](##Team.definableClass_subset) gives
one inclusion, the converse goes through normal forms in each logic, and [a translation between
logics compares their classes](##Team.definableClass_subset_of_translation).

## Implementation notes

The points are arbitrary, since the class only reads the support relation. Anttila's propositional
properties are classes of teams of valuations, and her modal ones classes of pointed team models.
Taking the points to be the teams of a single Kripke model gives a statement about that model, not
about the logic: the class of `ModalLogic.PointedTeam` is the one the source calls $\|L\|$.

## References

* [anttila-2025]
-/

@[expose] public section

namespace Team

variable {Form Form' Pt : Type*} {s : Form → Pt → Prop}

/-- The class of properties expressed under the support relation `s`: the support sets of the
formulas. -/
def definableClass (s : Form → Pt → Prop) : Set (Set Pt) :=
  Set.range fun φ ↦ {t | s φ t}

@[simp] theorem mem_definableClass {P : Set Pt} :
    P ∈ definableClass s ↔ ∃ φ, {t | s φ t} = P :=
  Set.mem_range

/-- If every formula's support set satisfies `C`, so does every expressed property. -/
theorem definableClass_subset {C : Set Pt → Prop} (h : ∀ φ, C {t | s φ t}) :
    definableClass s ⊆ {P | C P} :=
  Set.range_subset_iff.2 h

/-- A translation preserving support shows one logic expresses whatever another does. -/
theorem definableClass_subset_of_translation {s' : Form' → Pt → Prop} (f : Form → Form')
    (h : ∀ φ t, s φ t ↔ s' (f φ) t) : definableClass s ⊆ definableClass s' :=
  Set.range_subset_iff.2 fun φ ↦ ⟨f φ, Set.ext fun t ↦ (h φ t).symm⟩

end Team
