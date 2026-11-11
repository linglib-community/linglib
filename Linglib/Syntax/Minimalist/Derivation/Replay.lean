/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Derivation.Basic
public import Linglib.Core.Data.List.Monadic

/-!
# Replaying a derivation

`Derivation.replay?` runs the steps of a derivation by Merge on linearized objects, each new
daughter on the side its step records, and [a successful replay forgets to the derivation's own
configuration](##Minimalist.Derivation.replay?_faithful). A step applies to a configuration when
what it moves is there to move, and a derivation is valid, `Derivation.IsValid`, when it starts
from a leaf, each step applies to the configuration it meets, and no token is merged twice. [The
replay succeeds exactly when the steps apply](##Minimalist.Derivation.isSome_replay?_iff), and
[a valid derivation pronounces each merged token once](##Minimalist.Derivation.yield_replay?).
`Derivation.CCommandsAt` is c-command at a stage of the derivation.

## Implementation notes

* The replay is partial, `none` when the initial object is not a leaf, when a mover is absent, or
  when nothing is left to merge back, where `Derivation.run` is total. An externally merged item
  replays in the order it was built in.
* `CCommandsAt` and validity are decided on the replay, which is cheaper to evaluate than the
  unordered stage.

## References

* [marcolli-chomsky-berwick-2025], §1.13 (Lemma 1.13.1)
* [collins-stabler-2016]
-/

@[expose] public section

namespace Minimalist

open RoseTree UnorderedTree SyntacticObject

/-! ### The replay -/

open Derivation (Cfg)

/-- A step on a linearized configuration, `Step.run` with each new daughter on its side. Internal
    Merge raises the leftmost occurrence of the mover, leaving the trace of its head under `τ`,
    and an extraction stacks it; `none` when the mover is absent or the stack is empty. -/
def Step.replay? (step : Step) (c : Cfg LinearizedSyntacticObject)
    (τ : SyntacticObject → Option LexicalItem.Token := selHead) :
    Option (Cfg LinearizedSyntacticObject) :=
  match step, c with
  | .em side item, ⟨p, st⟩ => some ⟨p.attach side item, st⟩
  | .im mover side, ⟨p, st⟩ =>
      (p.find? mover).map fun s ↦ ⟨(p.replace mover (mover.traceLinearized τ)).attach side s, st⟩
  | .extract mover, ⟨p, st⟩ =>
      (p.find? mover).map fun s ↦ ⟨p.replace mover (mover.traceLinearized τ), s :: st⟩
  | .remerge side, ⟨p, m :: st⟩ => some ⟨p.attach side m, st⟩
  | .remerge _, ⟨_, []⟩ => none

namespace Derivation

/-- The derivation's linearized configuration under the trace encoder `τ`, or `none` if the initial
    object is not a leaf, a mover is absent, or `remerge` finds the stack empty. -/
def replay? (d : Derivation) (τ : SyntacticObject → Option LexicalItem.Token := selHead) :
    Option (Cfg LinearizedSyntacticObject) :=
  d.initial.toLinearizedLeaf?.bind fun p ↦ d.steps.foldlM (fun c step ↦ step.replay? c τ) ⟨p, []⟩

/-- The derivation's linearized object under the trace encoder `τ`; copies still on the stack are
    not part of it. -/
def externalize? (d : Derivation) (τ : SyntacticObject → Option LexicalItem.Token := selHead) :
    Option LinearizedSyntacticObject :=
  (d.replay? τ).map (·.current)

end Derivation

/-! ### Faithfulness -/

variable {τ : SyntacticObject → Option LexicalItem.Token}

namespace Derivation

theorem replay?_append_singleton (d : Derivation) (step : Step) :
    (d.append [step]).replay? = d.replay?.bind (step.replay? ·) := by
  simp only [replay?, append, List.foldlM_append, List.foldlM_cons, List.foldlM_nil,
    Option.bind_assoc]
  congr 1
  funext p
  congr 1
  funext c
  cases step.replay? c <;> rfl

theorem stack_eq_nil_of_replay? {d : Derivation} {c : Cfg LinearizedSyntacticObject}
    (hm : ∀ step ∈ d.steps, step.IsMerge) (h : d.replay? τ = some c) : c.stack = [] := by
  obtain ⟨p, -, h⟩ := Option.bind_eq_some_iff.1 h
  have key : ∀ (steps : List Step) (c₀ c : Cfg LinearizedSyntacticObject),
      (∀ step ∈ steps, step.IsMerge) → c₀.stack = [] →
        steps.foldlM (fun c step ↦ step.replay? c τ) c₀ = some c → c.stack = [] := by
    intro steps
    induction steps with
    | nil => intro c₀ c _ h₀ h; obtain rfl := Option.some.inj h; exact h₀
    | cons step steps ih =>
      intro c₀ c hm h₀ h
      obtain ⟨c₁, h₁, h⟩ := Option.bind_eq_some_iff.1 h
      refine ih c₁ c (fun s hs ↦ hm s (List.mem_cons_of_mem _ hs)) ?_ h
      obtain ⟨p₀, st₀⟩ := c₀
      cases h₀
      have := hm step List.mem_cons_self
      cases step with
      | em side item => obtain rfl := Option.some.inj h₁; rfl
      | im mover side => obtain ⟨s, -, rfl⟩ := Option.map_eq_some_iff.1 h₁; rfl
      | extract mover => exact this.elim
      | remerge side => exact this.elim
  exact key _ _ _ hm rfl h

end Derivation

/-! ### Relabelling -/

section Map

variable {f : LexicalItem.Token → LexicalItem.Token}
  {τ' : SyntacticObject → Option LexicalItem.Token}

theorem Step.replay?_map (hf : Function.Injective f) (hτ : ∀ s, τ' (s.map f) = (τ s).map f)
    (step : Step) (c : Cfg LinearizedSyntacticObject) :
    (step.map f).replay? (c.map (LinearizedSyntacticObject.map f)) τ' =
      (step.replay? c τ).map (Cfg.map (LinearizedSyntacticObject.map f)) := by
  rcases c with ⟨p, _ | ⟨m, st⟩⟩ <;> cases step <;>
    simp [Step.map, Step.replay?, Cfg.map, LinearizedSyntacticObject.find?_map hf,
      LinearizedSyntacticObject.replace_map hf, SyntacticObject.traceLinearized_map hτ,
      Function.comp_def]

namespace Derivation

theorem replay?_map (hf : Function.Injective f) (hτ : ∀ s, τ' (s.map f) = (τ s).map f)
    (d : Derivation) :
    (d.map f).replay? τ' = (d.replay? τ).map (Cfg.map (LinearizedSyntacticObject.map f)) := by
  simp only [replay?, map, SyntacticObject.toLinearizedLeaf?_map]
  cases d.initial.toLinearizedLeaf? with
  | none => rfl
  | some p =>
    simp only [Option.map_some, Option.bind_some, List.foldlM_map]
    exact (List.map_foldlM (f := fun c step ↦ step.replay? c τ)
      (g := fun c step ↦ (step.map f).replay? c τ')
      (fun c step ↦ (Step.replay?_map hf hτ step c).symm) d.steps ⟨p, []⟩).symm

theorem externalize?_map (hf : Function.Injective f) (hτ : ∀ s, τ' (s.map f) = (τ s).map f)
    (d : Derivation) :
    (d.map f).externalize? τ' = (d.externalize? τ).map (LinearizedSyntacticObject.map f) := by
  rw [externalize?, externalize?, replay?_map hf hτ, Option.map_map, Option.map_map]
  rfl

end Derivation

end Map

private theorem Step.map_of_replay? {c c' : Cfg LinearizedSyntacticObject} {step : Step}
    (h : step.replay? c τ = some c') :
    c'.map LinearizedSyntacticObject.toSyntacticObject
      = step.run (c.map LinearizedSyntacticObject.toSyntacticObject) τ := by
  obtain ⟨p, st⟩ := c
  cases step with
  | em side item =>
    obtain rfl := Option.some.inj h
    simp [Cfg.map, Step.run, Step.apply_em]
  | im mover side =>
    obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.1 h
    simp [Cfg.map, Step.run, Step.apply_im, deleteAccessible,
      LinearizedSyntacticObject.toSyntacticObject_find? hs, SyntacticObject.merge_comm]
  | extract mover =>
    obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.1 h
    simp [Cfg.map, Step.run, Step.apply, deleteAccessible,
      LinearizedSyntacticObject.toSyntacticObject_find? hs]
  | remerge side =>
    rcases st with _ | ⟨m, st⟩
    · cases h
    · obtain rfl := Option.some.inj h
      simp [Cfg.map, Step.run]

/-- A successful replay forgets to the configuration of the derivation
([marcolli-chomsky-berwick-2025] Lemma 1.13.1). -/
theorem Derivation.replay?_faithful (d : Derivation) {c : Cfg LinearizedSyntacticObject}
    (h : d.replay? τ = some c) :
    c.map LinearizedSyntacticObject.toSyntacticObject = d.run τ := by
  obtain ⟨p, hp, h⟩ := Option.bind_eq_some_iff.1 h
  rw [List.foldl_eq_of_foldlM_eq_some (f := fun c (step : Step) ↦ step.replay? c τ)
    (g := fun c (step : Step) ↦ step.run c τ)
    (π := Cfg.map LinearizedSyntacticObject.toSyntacticObject)
    (fun _ _ _ ↦ Step.map_of_replay?) h, Derivation.run, Cfg.map, List.map_nil,
    toSyntacticObject_of_toLinearizedLeaf? hp]

/-- A successful externalization forgets to the derived object, so the surface readouts are the
    word order of `final` itself. -/
theorem Derivation.externalize?_faithful (d : Derivation) {p : LinearizedSyntacticObject}
    (h : d.externalize? τ = some p) : p.toSyntacticObject = d.final τ := by
  obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.1 h
  rw [Derivation.final, ← d.replay?_faithful hc, Cfg.map_current]

theorem Derivation.externalize?_take_faithful (d : Derivation) (n : Nat)
    {p : LinearizedSyntacticObject} (h : (d.take n).externalize? τ = some p) :
    p.toSyntacticObject = d.stageAt n τ :=
  externalize?_faithful (d.take n) h

/-! ### Validity

A step applies to a configuration when what it moves is there to move. A derivation is valid when
it starts from a lexical item, each step applies to the configuration it meets, and no token is
merged twice; the replay succeeds exactly on the derivations whose steps apply. -/

/-- The step applies to the configuration: an Internal Merge or an extraction moves a term of the
object, and `remerge` finds a copy on the stack. -/
def Step.AppliesTo (c : Cfg SyntacticObject) : Step → Prop
  | .em _ _ => True
  | .im mover _ | .extract mover => mover ∈ c.current.terms
  | .remerge _ => c.stack ≠ []

/-- Each step of the list applies to the configuration the earlier ones reach. -/
def Step.ApplyFrom (τ : SyntacticObject → Option LexicalItem.Token) :
    List Step → Cfg SyntacticObject → Prop
  | [], _ => True
  | step :: steps, c => step.AppliesTo c ∧ Step.ApplyFrom τ steps (step.run c τ)

/-- A step replays exactly when it applies to the configuration replayed so far. -/
theorem Step.isSome_replay?_iff (step : Step) (c : Cfg LinearizedSyntacticObject) :
    (step.replay? c τ).isSome ↔
      step.AppliesTo (c.map LinearizedSyntacticObject.toSyntacticObject) := by
  obtain ⟨p, st⟩ := c
  cases step with
  | em side item => simp [Step.replay?, Step.AppliesTo]
  | im mover side =>
    simp [Step.replay?, Step.AppliesTo, LinearizedSyntacticObject.isSome_find?_iff]
  | extract mover =>
    simp [Step.replay?, Step.AppliesTo, LinearizedSyntacticObject.isSome_find?_iff]
  | remerge side => cases st <;> simp [Step.replay?, Step.AppliesTo]

theorem Step.isSome_foldlM_replay?_iff :
    ∀ (steps : List Step) (c : Cfg LinearizedSyntacticObject),
      (steps.foldlM (fun c (step : Step) ↦ step.replay? c τ) c).isSome ↔
        Step.ApplyFrom τ steps (c.map LinearizedSyntacticObject.toSyntacticObject)
  | [], _ => by simp [Step.ApplyFrom]
  | step :: steps, c => by
    rw [List.foldlM_cons, Step.ApplyFrom, ← Step.isSome_replay?_iff (τ := τ)]
    cases h : step.replay? c τ with
    | none => simp
    | some c₁ =>
      have ih := Step.isSome_foldlM_replay?_iff steps c₁
      rw [Step.map_of_replay? h] at ih
      simpa using ih

namespace Derivation

/-- A derivation is valid when it starts from a lexical item or a trace, each step applies to the
configuration it meets, and no token is merged twice. -/
structure IsValid (d : Derivation) (τ : SyntacticObject → Option LexicalItem.Token := selHead) :
    Prop where
  /-- The initial object is a leaf. -/
  initial : d.initial.toLinearizedLeaf?.isSome
  /-- Each step applies to the configuration it meets. -/
  steps : Step.ApplyFrom τ d.steps ⟨d.initial, []⟩
  /-- No token is merged twice. -/
  nodup : d.lexTokens.Nodup

/-- The replay succeeds exactly when the derivation starts from a leaf and each step applies. -/
theorem isSome_replay?_iff {d : Derivation} :
    (d.replay? τ).isSome ↔
      d.initial.toLinearizedLeaf?.isSome ∧ Step.ApplyFrom τ d.steps ⟨d.initial, []⟩ := by
  rw [replay?]
  cases h : d.initial.toLinearizedLeaf? with
  | none => simp
  | some p =>
    rw [Option.bind_some, Step.isSome_foldlM_replay?_iff]
    simp [Cfg.map, SyntacticObject.toSyntacticObject_of_toLinearizedLeaf? h]


theorem IsValid.isSome_replay? {d : Derivation} (h : d.IsValid τ) : (d.replay? τ).isSome :=
  isSome_replay?_iff.2 ⟨h.initial, h.steps⟩

/-- Validity is decided on the replay. -/
instance (d : Derivation) : Decidable (d.IsValid τ) :=
  decidable_of_iff
    (d.initial.toLinearizedLeaf?.isSome ∧ (d.replay? τ).isSome ∧ d.lexTokens.Nodup)
    ⟨fun ⟨hi, hr, hn⟩ ↦ ⟨hi, (isSome_replay?_iff.1 hr).2, hn⟩,
      fun h ↦ ⟨h.initial, h.isSome_replay?, h.nodup⟩⟩

theorem _root_.Minimalist.Step.ApplyFrom.take :
    ∀ {steps : List Step} {c : Cfg SyntacticObject} (n : Nat),
      Step.ApplyFrom τ steps c → Step.ApplyFrom τ (steps.take n) c
  | _, _, 0, _ => by simp [Step.ApplyFrom]
  | [], _, _ + 1, _ => by simp [Step.ApplyFrom]
  | _ :: _, _, n + 1, ⟨h, hs⟩ => ⟨h, Step.ApplyFrom.take n hs⟩

/-- The replay of an initial segment succeeds when the replay of the whole does. -/
theorem isSome_replay?_take {d : Derivation} (h : (d.replay? τ).isSome) (n : Nat) :
    ((d.take n).replay? τ).isSome :=
  let ⟨hi, hs⟩ := isSome_replay?_iff.1 h
  isSome_replay?_iff.2 ⟨hi, hs.take n⟩

/-- An initial segment of a valid derivation is valid. -/
theorem IsValid.take {d : Derivation} (h : d.IsValid τ) (n : Nat) : (d.take n).IsValid τ :=
  ⟨h.initial, h.steps.take n, Multiset.nodup_of_le (d.lexTokens_take_le n) h.nodup⟩

end Derivation

/-! ### Pronounced tokens -/

section Yield

open LinearizedSyntacticObject (toSyntacticObject)

private theorem Step.yield_map_replay? {step : Step} {c c' : Cfg LinearizedSyntacticObject}
    (hc : ((c.map toSyntacticObject).yield + (step.items.map SyntacticObject.yield).sum).Nodup)
    (h : step.replay? c τ = some c') :
    (c'.map toSyntacticObject).yield =
      (c.map toSyntacticObject).yield + (step.items.map SyntacticObject.yield).sum := by
  obtain ⟨p, st⟩ := c
  have hp : p.toSyntacticObject.yield.Nodup :=
    Multiset.nodup_of_le ((Multiset.le_add_right _ _).trans (Multiset.le_add_right _ _)) hc
  cases step with
  | em side item =>
    obtain rfl := Option.some.inj h
    simp only [Cfg.yield_map, Step.items, Multiset.map_singleton, Multiset.sum_singleton,
      LinearizedSyntacticObject.yield_attach]
    abel
  | im mover side =>
    obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.1 h
    simp only [Cfg.yield_map, Step.items, Multiset.map_zero, Multiset.sum_zero, add_zero,
      LinearizedSyntacticObject.yield_attach]
    rw [add_comm s.toSyntacticObject.yield,
      LinearizedSyntacticObject.yield_replace_add_yield τ hp hs]
  | extract mover =>
    obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.1 h
    simp only [Cfg.yield_map, Step.items, Multiset.map_zero, Multiset.sum_zero, add_zero,
      List.map_cons, List.sum_cons]
    rw [← add_assoc, LinearizedSyntacticObject.yield_replace_add_yield τ hp hs]
  | remerge side =>
    rcases st with _ | ⟨m, st⟩
    · cases h
    · obtain rfl := Option.some.inj h
      simp only [Cfg.yield_map, Step.items, Multiset.map_zero, Multiset.sum_zero, add_zero,
        List.map_cons, List.sum_cons, LinearizedSyntacticObject.yield_attach]
      abel

private theorem yield_map_foldlM_replay? :
    ∀ {steps : List Step} {c c' : Cfg LinearizedSyntacticObject},
      steps.foldlM (fun c step ↦ step.replay? c τ) c = some c' →
      ((c.map toSyntacticObject).yield +
        ((Step.itemsList steps).map SyntacticObject.yield).sum).Nodup →
      (c'.map toSyntacticObject).yield =
        (c.map toSyntacticObject).yield + ((Step.itemsList steps).map SyntacticObject.yield).sum
  | [], _, _, h, _ => by obtain rfl := Option.some.inj h; simp
  | step :: steps, c, _, h, hn => by
    obtain ⟨c₁, h₁, h⟩ := Option.bind_eq_some_iff.1 h
    rw [Step.itemsList_cons, Multiset.map_add, Multiset.sum_add, ← add_assoc] at hn ⊢
    have e₁ := Step.yield_map_replay? (Multiset.nodup_of_le (Multiset.le_add_right _ _) hn) h₁
    rw [← e₁] at hn ⊢
    exact yield_map_foldlM_replay? h hn

/-- When no token is merged twice, a derivation pronounces each token it merges once, in its
object or in a copy left on the stack, however many copies its movements leave. -/
theorem Derivation.yield_replay? {d : Derivation} {c : Cfg LinearizedSyntacticObject}
    (hd : d.lexTokens.Nodup) (h : d.replay? τ = some c) :
    (c.map toSyntacticObject).yield = d.lexTokens := by
  obtain ⟨p, hp, h⟩ := Option.bind_eq_some_iff.1 h
  have h0 : (Cfg.map toSyntacticObject ⟨p, []⟩).yield = d.initial.yield := by
    simp [Cfg.yield_map, SyntacticObject.toSyntacticObject_of_toLinearizedLeaf? hp]
  have := yield_map_foldlM_replay? h (by rwa [h0])
  rwa [h0] at this

end Yield

/-- No configuration a valid derivation reaches pronounces a token twice. -/
theorem Derivation.IsValid.nodup_yield_run_take {d : Derivation} (h : d.IsValid τ) (n : Nat) :
    ((d.take n).run τ).yield.Nodup := by
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 (h.take n).isSome_replay?
  rw [← replay?_faithful _ hc, yield_replay? (h.take n).nodup hc]
  exact (h.take n).nodup

/-! ### C-command at a stage -/

namespace Derivation

variable {d : Derivation} {steps : List Step} {n : Nat} {x y : SyntacticObject}

/-- `x` c-commands `y` at stage `n` of `d`. -/
def CCommandsAt (d : Derivation) (n : Nat) (x y : SyntacticObject) : Prop :=
  CCommands (d.stageAt n) x y

/-- Decided on the replayed object when the replay succeeds, which is cheaper to evaluate than the
stage itself. -/
instance (d : Derivation) (n : Nat) (x y : SyntacticObject) :
    Decidable (d.CCommandsAt n x y) :=
  match h : (d.take n).externalize? with
  | some p => decidable_of_iff (CCommands (↑p) x y) (by
      rw [CCommandsAt, ← d.externalize?_take_faithful n h])
  | none => inferInstanceAs (Decidable (CCommands (d.stageAt n) x y))

theorem CCommandsAt.cCommands_stageAt (h : d.CCommandsAt n x y) :
    CCommands (d.stageAt n) x y := h

theorem cCommandsAt_append_of_le (h : n ≤ d.length) :
    (d.append steps).CCommandsAt n x y ↔ d.CCommandsAt n x y := by
  rw [CCommandsAt, CCommandsAt, stageAt_append_of_le h]

theorem cCommandsAt_map_iff {f : LexicalItem.Token → LexicalItem.Token} (hf : Function.Injective f)
    (hsel : LexicalItem.Token.PreservesSelection f) :
    (d.map f).CCommandsAt n (x.map f) (y.map f) ↔ d.CCommandsAt n x y := by
  rw [CCommandsAt, CCommandsAt, stageAt_map d hf (fun s ↦ s.selHead_map hsel),
    cCommands_map_iff hf]

end Derivation

end Minimalist
