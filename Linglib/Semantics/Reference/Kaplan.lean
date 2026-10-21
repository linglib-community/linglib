/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.Reference.Character
public import Linglib.Semantics.Reference.Context.Shifts

/-!
# Kaplan's theory of indexicality

Kaplan's three tenets as Schlenker states them, over any context type with its coordinates given as
projections. A sentence's character holds at a context when its content is true at that context's
world (`Character.HoldsAt`); it is *a priori* when it holds at every context
(`Character.IsAPriori`) and *necessary* when its content is true at every world
(`Character.IsNecessary`). The two come apart because contexts are finer than worlds: when every
context is proper, *I exist* is a priori (`Kaplan.isAPriori_existsAgent`) without being necessary
(`Kaplan.not_isNecessary_existsAgent`), and when every context is located *I am here now* is a
priori (`Kaplan.isAPriori_locatedAgent`).

The English pure indexicals read a coordinate of the speech-act context: as access patterns on the
context tower they are `AccessPattern.origin` of a coordinate (`Kaplan.I`, `Kaplan.you`,
`Kaplan.now`, `Kaplan.here`, `Kaplan.actually`), invariant under every embedding shift
(`AccessPattern.stable_origin`), which is Kaplan's thesis for English. An access pattern is a
character over towers with rigid content (`AccessPattern.toCharacter`), Kaplan's `dthat` of its
coordinate at a root tower (`AccessPattern.origin_toCharacter_root`), and one stable under every
shift is *Kaplan-compliant* (`AccessPattern.IsKaplanCompliant`). An operator on characters is
a *monster* when it does not operate on contents (`IsMonster`); the operator evaluating a character
at a shifted context is one exactly when the shift moves some context (`isMonster_shift_iff`), as
the attitude shift of Schlenker and of Anand and Nevins does whenever the holder is not the speaker
(`attitudeShift_ne_one`), and the identity shift of English attitude verbs does not
(`not_isMonster_shift_one`, `AccessPattern.stable_one`).

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

/-- The operator that evaluates a character at the shifted context. -/
def shift (σ : Function.End C) (χ : Character C V α) : Character C V α := fun c ↦ χ (σ • c)

@[simp] theorem shift_apply (σ : Function.End C) (χ : Character C V α) (c : C) :
    shift σ χ c = χ (σ • c) := rfl

/-- A shift moves some context iff it is not the identity. -/
theorem ne_one_iff_exists_smul_ne (σ : Function.End C) : σ ≠ 1 ↔ ∃ c : C, σ • c ≠ c :=
  show (σ : C → C) ≠ id ↔ _ from Function.ne_iff

/-- Over contents that can differ, a shift operator is a monster iff the shift moves some
context. -/
theorem isMonster_shift_iff [Nontrivial (Content V α)] (σ : Function.End C) :
    IsMonster (shift σ : Character C V α → Character C V α) ↔ σ ≠ 1 := by
  classical
  refine ⟨fun h h1 ↦ h ⟨fun _ f ↦ f, fun χ c ↦ by simp [h1]⟩, fun h ⟨o, ho⟩ ↦ ?_⟩
  obtain ⟨c, hc⟩ := (ne_one_iff_exists_smul_ne σ).1 h
  obtain ⟨f, f', hf⟩ := exists_pair_ne (Content V α)
  have h₁ := ho (fun _ ↦ f) c
  have h₂ := ho (Function.update (fun _ ↦ f) (σ • c) f') c
  simp only [shift_apply, Function.update_self, Function.update_of_ne hc.symm] at h₁ h₂
  exact hf (h₁.trans h₂.symm)

/-- The identity shift, Kaplan's thesis for English attitude verbs, is no monster. -/
theorem not_isMonster_shift_one : ¬ IsMonster (shift 1 : Character C V α → Character C V α) :=
  fun h ↦ h ⟨fun _ f ↦ f, fun _ _ ↦ rfl⟩

/-- An attitude shift to a holder other than some context's agent moves that context. -/
theorem attitudeShift_ne_one (holder : E) (w' : W) (c : Context W E P T)
    (h : c.agent ≠ holder) : attitudeShift (P := P) (T := T) holder w' ≠ 1 :=
  (ne_one_iff_exists_smul_ne _).2 ⟨c, fun e ↦ h (by simpa using (congrArg Context.agent e).symm)⟩

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
