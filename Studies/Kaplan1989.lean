module

public import Linglib.Semantics.Reference.Kaplan

/-!
# Kaplan (1989): Demonstratives

Kaplan separates the character of an expression, its meaning, from its content at a context, what
it says there. A sentence is valid in the logic of demonstratives when it is true at every proper
context, one whose agent exists at its world and is at its position at its time there, and
necessary when its content at every context is true at every world. The two come apart: *I exist*
and *I am here now* are valid (`isAPriori_existsAgent`, `isAPriori_locatedAgent`), but what *I
exist* says at a context is contingent (`not_isNecessary_existsAgent`, `existsAgent_model`). The
pure indexicals of English read the speech-act context however deeply they are embedded, so English
has no monsters.

## Implementation notes

Validity quantifies over the proper contexts alone (`ProperContext`): over every tuple, *I exist*
would be true at every context only if every agent existed at every world, and so would be
necessary.

## References

* [kaplan-1989]
-/

@[expose] public section

namespace Kaplan1989

open Kaplan ContextTower

/-! ### Validity and necessity -/

section Character

variable {C W : Type*}

/-- A character is a priori, valid, when it holds at every context. -/
def IsAPriori (world : C → W) (χ : Character C W Prop) : Prop := ∀ c, χ.HoldsAt world c

/-- A character is necessary when its content at every context is true at every world. -/
def IsNecessary (χ : Character C W Prop) : Prop := ∀ (c : C) (w : W), χ c w

theorem IsNecessary.isAPriori {χ : Character C W Prop} (h : IsNecessary χ) (world : C → W) :
    IsAPriori world χ :=
  fun c ↦ h c _

end Character

/-! ### Proper contexts -/

variable {W E P T : Type*} (exists_ : E → W → Prop) (located : E → P → T → W → Prop)

/-- A context is proper when its agent exists at its world and is at its position at its time
there. -/
def Proper (c : Context W E P T) : Prop :=
  exists_ c.agent c.world ∧ located c.agent c.position c.time c.world

/-- The proper contexts. -/
abbrev ProperContext := {c : Context W E P T // Proper exists_ located c}

/-- The character of *I exist*: the agent of the context exists at the world of evaluation. -/
def existsAgent : Character (ProperContext exists_ located) W Prop := fun c w ↦ exists_ c.1.agent w

/-- The character of *I am here now*: the agent of the context is at its position at its time in
the world of evaluation. -/
def locatedAgent : Character (ProperContext exists_ located) W Prop :=
  fun c w ↦ located c.1.agent c.1.position c.1.time w

/-- *I exist* is valid. -/
theorem isAPriori_existsAgent : IsAPriori (·.1.world) (existsAgent exists_ located) :=
  fun c ↦ c.2.1

/-- *I am here now* is valid. -/
theorem isAPriori_locatedAgent : IsAPriori (·.1.world) (locatedAgent exists_ located) :=
  fun c ↦ c.2.2

/-- *I exist* is not necessary once the agent of some proper context fails to exist at some
world. -/
theorem not_isNecessary_existsAgent {c : ProperContext exists_ located} {w : W}
    (h : ¬ exists_ c.1.agent w) : ¬ IsNecessary (existsAgent exists_ located) :=
  fun hn ↦ h (hn c w)

/-- The English *I* reads the speech-act context under every embedding. -/
example : (Kaplan.I : AccessPattern (Context W E P T) E).Stable := AccessPattern.stable_origin _

/-! ### A one-agent, two-world model -/

/-- The actual world and one alternative. -/
inductive World where
  | w0
  | w1
  deriving DecidableEq, Repr

/-- The only agent exists at the actual world alone. -/
def existsAt (_ : Unit) (w : World) : Prop := w = .w0

/-- The agent is wherever it exists. -/
def locatedAt (_ : Unit) (_ : Unit) (_ : Unit) (w : World) : Prop := w = .w0

/-- *I exist* is valid but not necessary: the actual world is the world of the only proper
contexts, and at them *I exist* says something false at the alternative. -/
theorem existsAgent_model :
    IsAPriori (·.1.world) (existsAgent existsAt locatedAt) ∧
      ¬ IsNecessary (existsAgent existsAt locatedAt) :=
  ⟨isAPriori_existsAgent _ _,
    not_isNecessary_existsAgent _ _ (c := ⟨⟨(), (), .w0, (), ()⟩, rfl, rfl⟩) (w := .w1) nofun⟩

end Kaplan1989
