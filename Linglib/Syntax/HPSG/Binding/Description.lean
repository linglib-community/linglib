/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.HPSG.Binding.Basic
public import Linglib.Syntax.HPSG.RSRL.Subinterpretation

/-!
# The binding principles as RSRL descriptions

This file states Principles A and B as descriptions of RSRL and shows that an entity satisfies
them exactly when the principles hold among its components.

The argument structure is a list, built from the attributes `FIRST` and `REST`, so "earlier on
the list" is said with paths from the `ARG-ST` of some word. At a root of which every entity is a
component, the descriptions say what the principles say
(`HPSG.Binding.satisfies_grammar_iff`). At any entity they say it of the components of that
entity, with local o-command taken within it (`HPSG.Binding.satisfies_grammar_iff_within`).

## References

* [pollard-sag-1994]
* [richter-2000]
-/

@[expose] public section

namespace HPSG.Binding

open HPSG.RSRL

/-! ### The descriptions -/

/-- The term for the member at position `m` of the argument structure of the entity at the
variable `w`: its `ARG-ST`, then `REST` `m` times, then `FIRST`. -/
def arg (w m : ℕ) : Term sig := .feat ((·.feat .REST)^[m] (.feat (.var w) .ARGST)) .FIRST

/-- The entities at the variables `x` and `y` are coindexed when they share their index. -/
def coindexed (x y : ℕ) : Formula sig :=
  .pathEq (.feat (.var x) .IDX) (.feat (.var y) .IDX)

/-- The entity at `y` locally o-commands the entity at `x` when it precedes it on the argument
structure of some word, here among the first three members. The variable `2` is bound, so `y`
and `x` are other variables. -/
def locallyOCommands (y x : ℕ) : Formula sig :=
  .ex 2 (.or (.and (.pathEq (arg 2 0) (.var y)) (.pathEq (arg 2 1) (.var x)))
    (.or (.and (.pathEq (arg 2 0) (.var y)) (.pathEq (arg 2 2) (.var x)))
      (.and (.pathEq (arg 2 1) (.var y)) (.pathEq (arg 2 2) (.var x)))))

/-- The entity at `y` locally o-binds the entity at `x` when it locally o-commands it and is
coindexed with it. -/
def locallyOBinds (y x : ℕ) : Formula sig :=
  .and (locallyOCommands y x) (coindexed y x)

/-- Principle A says that a locally o-commanded anaphor is locally o-bound. -/
def principleA : Formula sig :=
  .all 0 (.imp (.and (.sortAssign (.var 0) .ana) (.ex 1 (locallyOCommands 1 0)))
    (.ex 1 (locallyOBinds 1 0)))

/-- Principle B says that a personal pronoun is locally o-free. -/
def principleB : Formula sig :=
  .all 0 (.imp (.sortAssign (.var 0) .ppro) (.neg (.ex 1 (locallyOBinds 1 0))))

/-- The grammar of the binding fragment. -/
abbrev grammar : Grammar sig := .ofList [⟨principleA, by decide⟩, ⟨principleB, by decide⟩]

example : (locallyOBinds 1 0).freeVars = {0, 1} := by decide

variable {U : Type*} {I : Interpretation sig U} {r : U}

/-! ### Satisfaction at a root -/

theorem termDenot_arg (g : ℕ → U) (u : U) (w m : ℕ) :
    I.termDenot g (arg w m) u = argAt I (g w) m := by
  have key : ∀ m, I.termDenot g ((·.feat .REST)^[m] (.feat (.var w) .ARGST)) u =
      (·.bind (I.A .REST))^[m] (I.A .ARGST (g w)) := fun m ↦ by
    induction m with
    | zero => rfl
    | succ m ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        Interpretation.termDenot_feat, ih]
  rw [arg, Interpretation.termDenot_feat, key, argAt]
theorem satisfies_locallyOCommands_iff (hr : I.IsRootedAt r) (g : ℕ → U) {y x : ℕ}
    (hy : y ≠ 2) (hx : x ≠ 2) :
    I.Satisfies g r (locallyOCommands y x) ↔ LocallyOCommands I (g y) (g x) := by
  simp [locallyOCommands, termDenot_arg, locallyOCommands_iff, hr _, Function.update_of_ne hy,
    Function.update_of_ne hx, eq_comm]

theorem satisfies_principleA_iff (hr : I.IsRootedAt r) (g : ℕ → U) :
    I.Satisfies g r principleA ↔ PrincipleA I := by
  simp [PrincipleA, principleA, locallyOBinds, locallyOCommands, coindexed, termDenot_arg,
    locallyOCommands_iff, hr _, Srt.le_ana_iff, Coindexed, eq_comm]

theorem satisfies_principleB_iff (hr : I.IsRootedAt r) (g : ℕ → U) :
    I.Satisfies g r principleB ↔ PrincipleB I := by
  simp [PrincipleB, principleB, locallyOBinds, locallyOCommands, coindexed, termDenot_arg,
    locallyOCommands_iff, hr _, Srt.le_ppro_iff, Coindexed, eq_comm]

/-- At a root of which every entity is a component, the descriptions hold exactly when the
principles do. -/
theorem satisfies_grammar_iff (hr : I.IsRootedAt r) :
    (∀ d ∈ grammar, I.Satisfies (fun _ ↦ r) r d) ↔ PrincipleA I ∧ PrincipleB I := by
  simp only [grammar, Grammar.mem_ofList, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, satisfies_principleA_iff hr, satisfies_principleB_iff hr]

theorem satisfies_of_models (hI : I.Models grammar) (hr : I.IsRootedAt r)
    (hirr : ∀ x, ¬ LocallyOCommands I x x) :
    (configuration I).Satisfies (Coindexed I) (configuration I).exempt
      fun x ↦ (I.S x).bindingClass :=
  (principleA_and_principleB_iff hirr).1 ((satisfies_grammar_iff hr).1 fun d hd ↦ hI d hd _ r)

/-! ### Satisfaction at any entity -/

theorem Coindexed.of_generated {r : U} {x y : {v // I.IsComponentOf r v}}
    (h : Coindexed (I.generated r) x y) : Coindexed I x y := by
  obtain ⟨v, hx, hy⟩ := h
  refine ⟨v, ?_, ?_⟩
  · rw [← Interpretation.map_val_generated_A, Option.mem_def.1 hx]; rfl
  · rw [← Interpretation.map_val_generated_A, Option.mem_def.1 hy]; rfl

theorem map_val_argAt_generated (w : {v // I.IsComponentOf r v}) (m : ℕ) :
    (argAt (I.generated r) w m).map Subtype.val = argAt I w m := by
  have key : ∀ m, ((·.bind ((I.generated r).A .REST))^[m] ((I.generated r).A .ARGST w)).map
      Subtype.val = (·.bind (I.A .REST))^[m] (I.A .ARGST w) := fun m ↦ by
    induction m with
    | zero => exact Interpretation.map_val_generated_A _
    | succ m ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih, Option.map_bind,
        Option.bind_map]
      exact congrArg _ (funext fun v ↦ Interpretation.map_val_generated_A _)
  rw [argAt, argAt, ← key, Option.map_bind, Option.bind_map]
  exact congrArg _ (funext fun v ↦ Interpretation.map_val_generated_A _)

theorem LocallyOCommands.of_generated {y x : {v // I.IsComponentOf r v}}
    (h : LocallyOCommands (I.generated r) y x) : LocallyOCommands I y x := by
  obtain ⟨w, m, n, hmn, hy, hx⟩ := h
  exact ⟨w, m, n, hmn, by rw [← map_val_argAt_generated, hy]; rfl,
    by rw [← map_val_argAt_generated, hx]; rfl⟩

/-- The entity `y` locally o-commands `x` within `r` when it precedes it among the first three
members of the argument structure of a word that is a component of `r`. -/
def LocallyOCommandsWithin (I : Interpretation sig U) (r y x : U) : Prop :=
  ∃ w, I.IsComponentOf r w ∧ ∃ m n : Fin 3, m < n ∧ argAt I w m = some y ∧ argAt I w n = some x

theorem LocallyOCommandsWithin.locallyOCommands {y x : U} (h : LocallyOCommandsWithin I r y x) :
    LocallyOCommands I y x :=
  let ⟨w, _, h⟩ := h; ⟨w, h⟩

theorem isComponentOf_of_argAt {w y : U} {m : ℕ} (hw : I.IsComponentOf r w)
    (h : argAt I w m = some y) : I.IsComponentOf r y := by
  have key : ∀ (m : ℕ) (l : U), (·.bind (I.A .REST))^[m] (I.A .ARGST w) = some l →
      I.IsComponentOf r l := fun m ↦ by
    induction m with
    | zero => exact fun l hl ↦ hw.tail ⟨.ARGST, hl⟩
    | succ m ih =>
      intro l hl
      rw [Function.iterate_succ_apply'] at hl
      obtain ⟨l', hl', hl⟩ := Option.bind_eq_some_iff.1 hl
      exact (ih l' hl').tail ⟨.REST, hl⟩
  obtain ⟨l, hl, hy⟩ := Option.bind_eq_some_iff.1 h
  exact (key m l hl).tail ⟨.FIRST, hy⟩

theorem locallyOCommands_generated_iff {y x : {v // I.IsComponentOf r v}} :
    LocallyOCommands (I.generated r) y x ↔ LocallyOCommandsWithin I r y x := by
  refine ⟨fun ⟨w, m, n, hmn, hy, hx⟩ ↦ ⟨w, w.2, m, n, hmn,
      by rw [← map_val_argAt_generated, hy]; rfl, by rw [← map_val_argAt_generated, hx]; rfl⟩,
    fun ⟨w, hw, m, n, hmn, hy, hx⟩ ↦ ⟨⟨w, hw⟩, m, n, hmn, ?_, ?_⟩⟩
  · obtain ⟨y', hy', e⟩ := Option.map_eq_some_iff.1
      ((map_val_argAt_generated ⟨w, hw⟩ m).trans hy)
    rw [hy', Subtype.ext e]
  · obtain ⟨x', hx', e⟩ := Option.map_eq_some_iff.1
      ((map_val_argAt_generated ⟨w, hw⟩ n).trans hx)
    rw [hx', Subtype.ext e]

theorem coindexed_generated_iff {x y : {v // I.IsComponentOf r v}} :
    Coindexed (I.generated r) x y ↔ Coindexed I x y := by
  refine ⟨Coindexed.of_generated, fun ⟨v, hx, hy⟩ ↦ ?_⟩
  obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.1
    ((Interpretation.map_val_generated_A (I := I) (r := r) (v := x) .IDX).trans hx)
  obtain ⟨b, hb, e⟩ := Option.map_eq_some_iff.1
    ((Interpretation.map_val_generated_A (I := I) (r := r) (v := y) .IDX).trans hy)
  exact ⟨a, ha, by rw [Option.mem_def, hb, Subtype.ext e]⟩

/-- An entity satisfies the binding principles, the quantifiers ranging over its components,
exactly when every anaphor among them that something locally o-commands is locally o-bound and
every personal pronoun among them is locally o-free, local o-command being within the entity. -/
theorem satisfies_grammar_iff_within (r : U) :
    (∀ d ∈ grammar, I.Satisfies (fun _ ↦ r) r d) ↔
      (∀ x, I.IsComponentOf r x → I.S x = .ana → ∀ y, LocallyOCommandsWithin I r y x →
        ∃ z, LocallyOCommandsWithin I r z x ∧ Coindexed I z x) ∧
      ∀ x, I.IsComponentOf r x → I.S x = .ppro → ∀ y, LocallyOCommandsWithin I r y x →
        ¬ Coindexed I y x := by
  have hg (d : Formula sig) : I.Satisfies (fun _ ↦ r) r d ↔
      (I.generated r).Satisfies (fun _ ↦ ⟨r, .refl⟩) ⟨r, .refl⟩ d :=
    (Interpretation.satisfies_generated (v := ⟨r, .refl⟩)
      (g := fun _ ↦ (⟨r, .refl⟩ : {v // I.IsComponentOf r v})) (d := d)).symm
  have hc {y x : U} (h : LocallyOCommandsWithin I r y x) : I.IsComponentOf r y :=
    let ⟨_, hw, _, _, _, hy, _⟩ := h; isComponentOf_of_argAt hw hy
  simp only [grammar, Grammar.mem_ofList, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, hg,
    satisfies_principleA_iff Interpretation.isRootedAt_generated,
    satisfies_principleB_iff Interpretation.isRootedAt_generated, PrincipleA, PrincipleB]
  refine and_congr ⟨fun h x hx hana y hy ↦ ?_, fun h x hana y hy ↦ ?_⟩
    ⟨fun h x hx hp y hy hco ↦ ?_, fun h x hp y hy hco ↦ ?_⟩
  · obtain ⟨z, hz, hco⟩ := h ⟨x, hx⟩ hana ⟨y, hc hy⟩ (locallyOCommands_generated_iff.2 hy)
    exact ⟨z, locallyOCommands_generated_iff.1 hz, coindexed_generated_iff.1 hco⟩
  · obtain ⟨z, hz, hco⟩ := h x x.2 hana y (locallyOCommands_generated_iff.1 hy)
    exact ⟨⟨z, hc hz⟩, locallyOCommands_generated_iff.2 hz, coindexed_generated_iff.2 hco⟩
  · exact h ⟨x, hx⟩ hp ⟨y, hc hy⟩ (locallyOCommands_generated_iff.2 hy)
      (coindexed_generated_iff.2 hco)
  · exact h x x.2 hp y (locallyOCommands_generated_iff.1 hy) (coindexed_generated_iff.1 hco)

/-- In a model of the grammar, an anaphor that follows something on the argument structure of a
word is coindexed with something that locally o-commands it, when the word and the anaphor are
components of one entity. -/
theorem exists_coindexed_of_models (hI : I.Models grammar) {w x y : U} {m n : Fin 3}
    (hw : I.IsComponentOf r w) (hmn : m < n) (hy : argAt I w m = some y)
    (hx : argAt I w n = some x) (hana : I.S x = .ana) :
    ∃ z, LocallyOCommands I z x ∧ Coindexed I z x := by
  have hA := (satisfies_principleA_iff (I := I.generated r) Interpretation.isRootedAt_generated
    fun _ ↦ ⟨r, .refl⟩).1 ((hI.generated r) ⟨principleA, by decide⟩
      (by simp [grammar, Grammar.mem_ofList]) _ _)
  obtain ⟨y', hy', rfl⟩ := Option.map_eq_some_iff.1
    ((map_val_argAt_generated ⟨w, hw⟩ m).trans hy)
  obtain ⟨x', hx', rfl⟩ := Option.map_eq_some_iff.1
    ((map_val_argAt_generated ⟨w, hw⟩ n).trans hx)
  obtain ⟨z, hz, hc⟩ := hA x' hana y' ⟨⟨w, hw⟩, m, n, hmn, hy', hx'⟩
  exact ⟨z, hz.of_generated, hc.of_generated⟩

end HPSG.Binding
