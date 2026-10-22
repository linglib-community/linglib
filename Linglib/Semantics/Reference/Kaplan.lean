/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.Reference.Character
public import Linglib.Semantics.Reference.Context.Tower

/-!
# Kaplan's theory of indexicality

Kaplan's tenets as Schlenker states them, over any context type with its coordinates given as
projections: a sentence is a priori when it holds at every context and necessary when it is true
at every world, and the two come apart because contexts are finer than worlds. An operator on
characters that evaluates its argument at another context is a *monster*; Kaplan's thesis for
English is that its indexicals read the speech-act context under every embedding shift.

## Main definitions

* `Character.HoldsAt`, `Character.IsAPriori`, `Character.IsNecessary`
* `IsMonster`: an operator on characters that does not operate on contents.
* `shiftBy τ`: evaluation at the context `τ c v` computed from the context and the index, as the
  shifty operators of `Context/Overwrite.lean` do; `shift σ` is its index-independent case.
* `Kaplan.I`, `Kaplan.you`, `Kaplan.now`, `Kaplan.here`, `Kaplan.actually`: the pure indexicals,
  origin access patterns on the context tower.
* `AccessPattern.toCharacter`, `AccessPattern.IsKaplanCompliant`

## Main results

* `isAPriori_existsAgent`, `not_isNecessary_existsAgent`, `isAPriori_locatedAgent`: *I exist* and
  *I am here now* are a priori, the first without being necessary.
* `isMonster_shiftBy_iff`, `isMonster_shift_iff`: an operator evaluating at a computed or shifted
  context is a monster iff it moves some context.
* `not_isMonster_shift_one`, `AccessPattern.stable_one`: the identity shift of English attitude
  verbs is no monster and leaves every access pattern stable.

## References

* [kaplan-1989]
* [schlenker-2011]
* [schlenker-2003]
* [anand-nevins-2004]
-/

@[expose] public section

namespace Kaplan

open ContextTower

variable {C R W E P T : Type*}

/-! ### A priori and necessary truth -/

namespace Character

variable (world : C → W)

/-- A character holds at a context when its content is true at the world of that context:
the evaluation of a root sentence. -/
def HoldsAt (χ : Character C W Prop) (c : C) : Prop := χ c (world c)

/-- A character is a priori when it holds at every context. -/
def IsAPriori (χ : Character C W Prop) : Prop := ∀ c, χ.HoldsAt world c

/-- A character is necessary when its content is true at every world of every context. -/
def IsNecessary (χ : Character C W Prop) : Prop := ∀ (c : C) (w : W), χ c w

theorem IsNecessary.isAPriori {χ : Character C W Prop} (h : χ.IsNecessary) :
    χ.IsAPriori world :=
  fun c ↦ h c _

end Character

section Tenets

variable (agent : C → E) (world : C → W) (position : C → P) (time : C → T)
  (exists_ : E → W → Prop) (located : E → P → T → W → Prop)

/-- The character of *I exist* says that the agent of the context exists at the world of
evaluation. -/
def existsAgent : Character C W Prop := fun c w ↦ exists_ (agent c) w

/-- The character of *I am here now* says that the agent of the context is at its position at its
time in the world of evaluation. -/
def locatedAgent : Character C W Prop := fun c w ↦ located (agent c) (position c) (time c) w

/-- *I exist* is a priori when every context is proper, its agent existing at its world:
Kaplan's coherence constraint on contexts. -/
theorem isAPriori_existsAgent (h : ∀ c, exists_ (agent c) (world c)) :
    (existsAgent agent exists_).IsAPriori world :=
  h

/-- *I exist* is not necessary once some agent fails to exist at some world. -/
theorem not_isNecessary_existsAgent {c : C} {w : W} (h : ¬ exists_ (agent c) w) :
    ¬ (existsAgent agent exists_).IsNecessary :=
  fun hn ↦ h (hn c w)

/-- *I am here now* is a priori when every context is located. -/
theorem isAPriori_locatedAgent (h : ∀ c, located (agent c) (position c) (time c) (world c)) :
    (locatedAgent agent position time located).IsAPriori world :=
  h

/-- On the canonical tuple, properness of every context is `Context.Proper`. -/
theorem isAPriori_existsAgent_of_proper (h : ∀ c : Context W E P T, c.Proper exists_) :
    (existsAgent (C := Context W E P T) Context.agent exists_).IsAPriori Context.world :=
  h

end Tenets

/-! ### Monsters -/

section Monster

variable {V α β : Type*}

/-- An operator on characters is a monster when it does not operate on contents, so that what it
yields at a context is not determined by the content of its argument there ([kaplan-1989]). -/
def IsMonster (O : Character C V α → Character C V β) : Prop :=
  ¬ ∃ o : C → Content V α → Content V β, ∀ χ c, O χ c = o c (χ c)

/-- The operator that evaluates a character, at a context and an index, at the context `τ c v`
and the same index. -/
def shiftBy (τ : C → V → C) (χ : Character C V α) : Character C V α := fun c v ↦ χ (τ c v) v

@[simp] theorem shiftBy_apply (τ : C → V → C) (χ : Character C V α) (c : C) (v : V) :
    shiftBy τ χ c v = χ (τ c v) v := rfl

/-- Over values that can differ, an operator evaluating at a computed context is a monster iff the
computation moves some context at some index. -/
theorem isMonster_shiftBy_iff [Nontrivial α] (τ : C → V → C) :
    IsMonster (shiftBy τ : Character C V α → Character C V α) ↔ ∃ c v, τ c v ≠ c := by
  classical
  refine ⟨fun h ↦ ?_, fun ⟨c, v, hc⟩ ⟨o, ho⟩ ↦ ?_⟩
  · by_contra! hτ
    exact h ⟨fun _ f ↦ f, fun χ c ↦ funext fun v ↦ by simp [hτ]⟩
  obtain ⟨a, b, hab⟩ := exists_pair_ne α
  have h₁ := congrFun (ho (fun _ _ ↦ a) c) v
  have h₂ := congrFun (ho (Function.update (fun _ _ ↦ a) (τ c v) fun _ ↦ b) c) v
  simp only [shiftBy_apply, Function.update_self, Function.update_of_ne hc.symm] at h₁ h₂
  exact hab (h₁.trans h₂.symm)

/-- The operator that evaluates a character at the shifted context. -/
def shift (σ : Function.End C) : Character C V α → Character C V α := shiftBy fun c _ ↦ σ • c

@[simp] theorem shift_apply (σ : Function.End C) (χ : Character C V α) (c : C) :
    shift σ χ c = χ (σ • c) := rfl

/-- A shift moves some context iff it is not the identity. -/
theorem ne_one_iff_exists_smul_ne (σ : Function.End C) : σ ≠ 1 ↔ ∃ c : C, σ • c ≠ c :=
  show (σ : C → C) ≠ id ↔ _ from Function.ne_iff

/-- Over contents that can differ, a shift operator is a monster iff the shift moves some
context. -/
theorem isMonster_shift_iff [Nontrivial (Content V α)] (σ : Function.End C) :
    IsMonster (shift σ : Character C V α → Character C V α) ↔ σ ≠ 1 := by
  have := Function.nontrivial_of_nontrivial V α
  obtain ⟨f, g, h⟩ := exists_pair_ne (Content V α)
  have : Nonempty V := (Function.ne_iff.1 h).nonempty
  simp [shift, isMonster_shiftBy_iff, ne_one_iff_exists_smul_ne]

/-- The identity shift, Kaplan's thesis for English attitude verbs, is no monster. -/
theorem not_isMonster_shift_one : ¬ IsMonster (shift 1 : Character C V α → Character C V α) :=
  fun h ↦ h ⟨fun _ f ↦ f, fun _ _ ↦ rfl⟩

end Monster

end Kaplan

namespace ContextTower.AccessPattern

open Kaplan

variable {C R W E P T : Type*}

/-- The identity shift leaves every access pattern stable. -/
theorem stable_one (ap : AccessPattern C R) : ap.Stable 1 := by
  intro t
  obtain ⟨d, f⟩ := ap
  simp only [resolve]
  congr 1
  cases d with
  | origin => simp
  | «local» =>
    rw [DepthSpec.local_resolve, DepthSpec.local_resolve, ContextTower.push_depth,
      ContextTower.push_contextAt_succ_depth, one_smul, ContextTower.contextAt_depth]
  | relative k =>
    rcases le_or_gt k t.depth with hk | hk
    · rw [DepthSpec.relative_resolve, DepthSpec.relative_resolve,
        ContextTower.push_contextAt_of_le _ _ hk]
    · rw [DepthSpec.relative_resolve, DepthSpec.relative_resolve,
        ContextTower.push_contextAt_of_lt _ _ hk, one_smul,
        ContextTower.contextAt_saturates _ hk.le]

/-- An access pattern is a character over towers, the rigid content at its value at each tower. -/
def toCharacter (ap : AccessPattern C R) : Character (ContextTower C) W R :=
  Character.dthat ap.resolve

@[simp] theorem toCharacter_apply (ap : AccessPattern C R) (t : ContextTower C) (w : W) :
    (ap.toCharacter : Character (ContextTower C) W R) t w = ap.resolve t :=
  rfl

theorem toCharacter_isDirectlyReferential (ap : AccessPattern C R) :
    (ap.toCharacter : Character (ContextTower C) W R).IsDirectlyReferential :=
  Character.dthat_isDirectlyReferential _

/-- At a root tower an origin pattern is Kaplan's rigidifier of its coordinate. -/
theorem origin_toCharacter_root (f : C → R) (c : C) :
    ((origin f).toCharacter : Character (ContextTower C) W R) (ContextTower.root c) =
      Character.dthat f c :=
  rfl

/-- An access pattern is Kaplan-compliant when it is stable under every shift. -/
def IsKaplanCompliant (ap : AccessPattern C R) : Prop := ∀ σ, ap.Stable σ

theorem isKaplanCompliant_origin (f : C → R) : (origin f).IsKaplanCompliant :=
  fun σ ↦ stable_origin f σ

end ContextTower.AccessPattern

namespace Kaplan

open ContextTower

variable {C W E P T : Type*}

/-- A shift moves some context iff the innermost context is unstable under it. -/
theorem ne_one_iff_not_stable_innermost_id (σ : Function.End C) :
    σ ≠ 1 ↔ ¬ (AccessPattern.innermost id).Stable σ := by
  simp only [ne_one_iff_exists_smul_ne, AccessPattern.Stable, AccessPattern.innermost_resolve,
    ContextTower.push_innermost, id_eq, not_forall]
  exact ⟨fun ⟨c, hc⟩ ↦ ⟨ContextTower.root c, by simpa using hc⟩, fun ⟨t, ht⟩ ↦ ⟨t.innermost, ht⟩⟩

/-! ### The English pure indexicals -/

/-- *I* is the agent of the speech-act context. -/
def I : AccessPattern (Context W E P T) E := .origin Context.agent

/-- *You* is the addressee of the speech-act context. -/
def you : AccessPattern (Context W E P T) E := .origin Context.addressee

/-- *Now* is the time of the speech-act context. -/
def now : AccessPattern (Context W E P T) T := .origin Context.time

/-- *Here* is the position of the speech-act context. -/
def here : AccessPattern (Context W E P T) P := .origin Context.position

/-- *Actually* is the world of the speech-act context. -/
def actually : AccessPattern (Context W E P T) W := .origin Context.world

end Kaplan
