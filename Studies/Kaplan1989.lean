module

public import Linglib.Semantics.Reference.Kaplan

/-!
# Kaplan (1989): Demonstratives

Kaplan separates the character of an expression, its meaning, from its content at a context, what
it says there. A sentence is valid in the logic of demonstratives when it is true at every context,
and necessary when its content at every context is true at every world. Every necessary sentence
is valid, but the converse, the rule of necessitation, fails as soon as there are two worlds
([necessitation](##forall_isAPriori_imp_isNecessary_iff)). The identity of a term with its
rigidification, *α = dthat[α]*, is valid for every term and necessary exactly when the term is
directly referential ([dthat](##isNecessary_eq_dthat_iff)). Even for sentences whose content does
not vary with the context, necessitation holds only if every world is the world of some context
([stable characters](##forall_isAPriori_imp_isNecessary_of_stable_iff)), and a proper context, one
whose agent exists at its world and is at its position at its time there, has a world with an
agent. So *I exist* and *I am here now* are valid over the proper contexts
([I am here now](##isAPriori_locatedAgent)), and in a model with a world where no one exists both
say something contingent ([the model](##model_isAPriori_not_isNecessary)). The pure indexicals of
English read the speech-act context however deeply they are embedded, so English has no monsters.

## Implementation notes

* Validity of *I exist* and *I am here now* quantifies over the proper contexts alone
  (`ProperContext`): over every tuple, *I exist* would be true at every context only if every agent
  existed at every world, and so would be necessary.
* An index is a world; Kaplan's circumstances also fix a time, which the necessity of these
  sentences does not need.

## References

* [kaplan-1989]
-/

@[expose] public section

namespace Kaplan1989

open Kaplan ContextTower
open Kaplan.Character (IsAPriori IsNecessary)

/-! ### The failure of necessitation -/

section Necessitation

variable {C W E : Type*}

/-- Validity implies necessity for every sentence exactly when there is at most one world. -/
theorem forall_isAPriori_imp_isNecessary_iff [Nonempty C] (ι : C → W) :
    (∀ χ : Character C W Prop, χ.IsAPriori ι → χ.IsNecessary) ↔ Subsingleton W := by
  refine ⟨fun h ↦ ⟨fun w₁ w₂ ↦ ?_⟩, fun _ χ hχ c w ↦ ?_⟩
  · obtain ⟨c⟩ := ‹Nonempty C›
    have h' := h (fun c w ↦ w = ι c) fun _ ↦ rfl
    exact (h' c w₁).trans (h' c w₂).symm
  · rw [← Subsingleton.elim (ι c) w]
    exact hχ c

-- Remark 3: the identity of a term with its rigidification is valid
theorem isAPriori_eq_dthat (ι : C → W) (α : Character C W E) :
    IsAPriori ι fun c w ↦ α c w = Character.dthat (α.diag ι) c w :=
  fun _ ↦ rfl

/-- The identity of a term with its rigidification is necessary exactly when the term is directly
referential. -/
theorem isNecessary_eq_dthat_iff (ι : C → W) (α : Character C W E) :
    IsNecessary (fun c w ↦ α c w = Character.dthat (α.diag ι) c w) ↔
      α.IsDirectlyReferential :=
  ⟨fun h c w₁ w₂ ↦ (h c w₁).trans (h c w₂).symm, fun h c w ↦ h c w (ι c)⟩

/-- For sentences whose content is the same at every context, validity implies necessity exactly
when every world is the world of some context. -/
theorem forall_isAPriori_imp_isNecessary_of_stable_iff [Nonempty C] (ι : C → W) :
    (∀ χ : Character C W Prop, (∀ c c', χ c = χ c') → χ.IsAPriori ι → χ.IsNecessary) ↔
      Function.Surjective ι := by
  refine ⟨fun h w ↦ ?_, fun hι χ hχ hv c w ↦ ?_⟩
  · obtain ⟨c⟩ := ‹Nonempty C›
    exact h (fun _ w ↦ ∃ c, ι c = w) (fun _ _ ↦ rfl) (fun c ↦ ⟨c, rfl⟩) c w
  · obtain ⟨c', rfl⟩ := hι w
    rw [hχ c c']
    exact hv c'

end Necessitation

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

theorem isAPriori_existsAgent : IsAPriori (·.1.world) (existsAgent exists_ located) :=
  fun c ↦ c.2.1

/-- *I am here now* is valid. -/
theorem isAPriori_locatedAgent : IsAPriori (·.1.world) (locatedAgent exists_ located) :=
  fun c ↦ c.2.2

theorem not_isNecessary_existsAgent {c : ProperContext exists_ located} {w : W}
    (h : ¬ exists_ c.1.agent w) : ¬ IsNecessary (existsAgent exists_ located) :=
  fun hn ↦ h (hn c w)

theorem not_isNecessary_locatedAgent {c : ProperContext exists_ located} {w : W}
    (h : ¬ located c.1.agent c.1.position c.1.time w) :
    ¬ IsNecessary (locatedAgent exists_ located) :=
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

/-- The only proper context of the model. -/
def actualContext : ProperContext existsAt locatedAt := ⟨⟨(), (), .w0, (), ()⟩, rfl, rfl⟩

/-- *I exist* and *I am here now* are valid but not necessary: the actual world is the world of
the only proper context, and what both say there is false at the alternative, where no one
exists. -/
theorem model_isAPriori_not_isNecessary :
    (IsAPriori (·.1.world) (existsAgent existsAt locatedAt) ∧
        ¬ IsNecessary (existsAgent existsAt locatedAt)) ∧
      IsAPriori (·.1.world) (locatedAgent existsAt locatedAt) ∧
        ¬ IsNecessary (locatedAgent existsAt locatedAt) :=
  ⟨⟨isAPriori_existsAgent _ _,
      not_isNecessary_existsAgent _ _ (c := actualContext) (w := .w1) nofun⟩,
    isAPriori_locatedAgent _ _,
    not_isNecessary_locatedAgent _ _ (c := actualContext) (w := .w1) nofun⟩

end Kaplan1989
