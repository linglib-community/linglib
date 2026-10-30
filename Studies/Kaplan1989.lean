module

public import Linglib.Semantics.Reference.Kaplan

/-!
# Kaplan (1989): Demonstratives

A sentence is valid in Kaplan's logic of demonstratives when it is true at every context, and
necessary when what it says at every context is true at every world. Necessity implies validity
(`Kaplan.Character.IsNecessary.isAPriori`), but necessitation fails
[as soon as there are two worlds](##forall_isAPriori_imp_isNecessary_iff_subsingleton), and for
sentences whose content does not vary with the context it holds [only if every world is the world
of a context](##forall_isAPriori_const_imp_isNecessary_iff_surjective). *α = dthat[α]*
[is valid](##isAPriori_eq_dthat), and [necessary exactly when α is directly
referential](##isNecessary_eq_dthat_iff); *I exist* and *I am here now* are
[valid but contingent](##model_isAPriori_not_isNecessary).

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
theorem forall_isAPriori_imp_isNecessary_iff_subsingleton [Nonempty C] (ι : C → W) :
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

/-- For sentences whose content is the same at every context, Kaplan's stable characters, validity
implies necessity exactly when every world is the world of some context. -/
theorem forall_isAPriori_const_imp_isNecessary_iff_surjective [Nonempty C] (ι : C → W) :
    (∀ p : W → Prop, IsAPriori ι (fun (_ : C) ↦ p) → IsNecessary fun (_ : C) ↦ p) ↔
      Function.Surjective ι := by
  refine ⟨fun h w ↦ ?_, fun hι p hp c w ↦ ?_⟩
  · obtain ⟨c⟩ := ‹Nonempty C›
    exact h (fun w ↦ ∃ c, ι c = w) (fun c ↦ ⟨c, rfl⟩) c w
  · obtain ⟨c', rfl⟩ := hι w
    exact hp c'

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
  ⟨⟨isAPriori_existsAgent _ _, fun hn ↦ absurd (hn actualContext .w1) nofun⟩,
    isAPriori_locatedAgent _ _, fun hn ↦ absurd (hn actualContext .w1) nofun⟩

/-- The description *the world of evaluation*, which is not directly referential. -/
def worldOfEvaluation : Character Unit World World := fun _ w ↦ w

-- *the world of evaluation = dthat[the world of evaluation]* is valid but not necessary, while the
-- same identity for a name of the actual world is necessary
example :
    IsAPriori (fun _ ↦ World.w0) (fun c w ↦ worldOfEvaluation c w =
        Character.dthat (worldOfEvaluation.diag fun _ ↦ .w0) c w) ∧
      ¬ IsNecessary (fun c w ↦ worldOfEvaluation c w =
        Character.dthat (worldOfEvaluation.diag fun _ ↦ .w0) c w) ∧
      IsNecessary (fun c w ↦ (Character.const .w0 : Character Unit World World) c w =
        Character.dthat ((Character.const .w0 : Character Unit World World).diag
          fun _ ↦ .w0) c w) :=
  ⟨isAPriori_eq_dthat _ worldOfEvaluation,
    (isNecessary_eq_dthat_iff _ _).not.2 fun h ↦ absurd (h () .w0 .w1) nofun,
    (isNecessary_eq_dthat_iff _ _).2 fun _ _ _ ↦ rfl⟩

-- the model refutes necessitation, even for the stable characters, since its one proper context
-- does not reach the alternative world
example :
    (¬ ∀ χ : Character (ProperContext existsAt locatedAt) World Prop,
        χ.IsAPriori (·.1.world) → χ.IsNecessary) ∧
      ¬ ∀ p : World → Prop, IsAPriori (·.1.world) (fun (_ : ProperContext existsAt locatedAt) ↦ p) →
        IsNecessary fun (_ : ProperContext existsAt locatedAt) ↦ p := by
  have : Nonempty (ProperContext existsAt locatedAt) := ⟨actualContext⟩
  rw [forall_isAPriori_imp_isNecessary_iff_subsingleton,
    forall_isAPriori_const_imp_isNecessary_iff_surjective]
  refine ⟨fun h ↦ absurd (h.allEq .w0 .w1) nofun, fun h ↦ ?_⟩
  obtain ⟨c, hc⟩ := h .w1
  exact absurd (hc.symm.trans c.2.1) nofun

end Kaplan1989
