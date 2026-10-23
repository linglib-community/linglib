/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Derivation.Basic
public import Linglib.Core.Data.List.Monadic
public import Linglib.Syntax.Minimalist.Linearization.Externalization

/-!
# Replaying a derivation on linearized objects

Free symmetric Merge builds unordered objects, so the surface order is not recoverable from
`Derivation.final`, but each step records the side its new daughter takes. `Derivation.replay?`
replays the steps by Merge on linearized objects, and a successful replay forgets to the
derivation's own configuration, so the readouts `surfaceTokens`, `surfaceCats` and `surfacePhon` are
the word order of the derived object. The order is a datum of the derivation rather than of its
object, and a derivation whose daughters take the head side exactly when they project records the
harmonic linearization of its object.

## Main definitions

* `Minimalist.Step.replay?`, `Minimalist.Derivation.replay?`, `externalize?`: the replay.
* `Minimalist.Step.Harmonic`, `Step.HarmonicList`: steps that place the projecting daughter on
  the head side.
* `Minimalist.Derivation.surfaceTokens`, `surfaceCats`, `surfacePhon`.

## Main results

* `Minimalist.Derivation.replay?_faithful`, `externalize?_faithful`: a successful replay forgets
  to `run` and `final`.
* `Minimalist.Derivation.not_factorsThrough_final`: the linearized object does not factor through
  the derived object.
* `Minimalist.Derivation.externalize?_eq_linearize?`: a harmonic derivation records the harmonic
  linearization of its object.

## Implementation notes

* The replay is partial, `none` when the initial object is not a leaf, when a mover is absent, or
  when nothing is left to merge back. An externally merged item replays in the order it was built
  in. Traces are unpronounced.
* Sibling accounts of linearization are the selection-induced harmonic order
  (`Linearization/Externalization.lean`) and cyclic linearization (`Linearization/Cyclic.lean`).

## References

* [marcolli-chomsky-berwick-2025], §1.12 and §1.13 (Lemmas 1.13.1 and 1.13.5)
-/

@[expose] public section

namespace Minimalist

open RoseTree UnorderedTree SyntacticObject

variable {side : Edge}

theorem linearize?_of_toLinearizedLeaf? {s : SyntacticObject} {p : LinearizedSyntacticObject}
    (h : s.toLinearizedLeaf? = some p) : s.linearize? side = some p := by
  rcases s.exists_form with ⟨tok, rfl⟩ | rfl | ⟨tok, rfl⟩ | ⟨l, r, rfl⟩ <;>
    simp [toLinearizedLeaf?, merge_val] at h <;> subst h <;> rfl

theorem linearize?_headTrace (s : SyntacticObject)
    (τ : SyntacticObject → Option LexicalItem.Token) :
    (s.headTrace τ).linearize? side = some (s.traceLinearized τ) := by
  unfold headTrace traceLinearized; cases τ s <;> rfl


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

/-- The pronounced tokens, left to right; empty if the replay fails. -/
def surfaceTokens (d : Derivation) : List LexicalItem.Token :=
  (d.externalize?.map (·.yield)).getD []

/-- The surface category sequence, the readout of word-order studies. -/
def surfaceCats (d : Derivation) : List Cat := d.surfaceTokens.map (·.item.cat)

/-- The surface string lists the pronounced forms left to right, dropping empty forms. -/
def surfacePhon (d : Derivation) : List String :=
  d.surfaceTokens.filterMap (·.item.phonForm?)

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

/-- A successful replay forgets to the derivation's configuration, the object and every copy on
    the stack, forgetting the order being a morphism of magmas
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

/-! ### Harmonic derivations

A derivation is harmonic for a head side when each daughter it merges projects exactly if it takes
the head side, and each mover leaves a trace with its selection state. Its recorded order is then
the harmonic linearization of its object (`Derivation.externalize?_eq_linearize?`). -/

namespace SyntacticObject

private theorem linearizationState_replace_self {cur t : SyntacticObject} {σ}
    {pc pt : LinearizedSyntacticObject} (hc : cur.linearizationState side = ⟨some (σ, pc)⟩)
    (ht : t.linearize? side = some pt) (hsel : t.selCheck = cur.selCheck) :
    (cur.replace cur t).linearizationState side = ⟨some (σ, pc.replace cur pt)⟩ := by
  have hpc : cur.linearize? side = some pc := by
    simp [linearize?, hc, LinearizationState.linearized?]
  rw [replace_self,
    LinearizedSyntacticObject.replace_of_toSyntacticObject_eq (toSyntacticObject_of_linearize? hpc)]
  obtain ⟨σt, hσt, hst⟩ := linearizationState_eq_of_linearize? ht
  have : cur.selCheck = ⟨some σ⟩ := by rw [← sel_linearizationState side cur, hc]; rfl
  rw [hσt, this] at hsel
  cases hsel
  exact hst

private theorem linearizationState_replace_leaf {cur m t : SyntacticObject} {a : Vertex} {σ}
    {pc pt : LinearizedSyntacticObject} (hs : cur.val = UnorderedTree.leaf a)
    (hpv : pc.val = .node a []) (hc : cur.linearizationState side = ⟨some (σ, pc)⟩)
    (ht : t.linearize? side = some pt) (hsel : t.selCheck = m.selCheck) :
    (cur.replace m t).linearizationState side = ⟨some (σ, pc.replace m pt)⟩ := by
  by_cases heq : cur = m
  · subst heq; exact linearizationState_replace_self hc ht hsel
  · have hpc : cur.linearize? side = some pc := by
      simp [linearize?, hc, LinearizationState.linearized?]
    rw [replace_of_val_eq_leaf hs heq, LinearizedSyntacticObject.replace_of_val_eq_leaf hpv
      (by rwa [toSyntacticObject_of_linearize? hpc]), hc]

theorem linearizationState_replace {cur m t : SyntacticObject} {σ}
    {pc pt : LinearizedSyntacticObject} (hc : cur.linearizationState side = ⟨some (σ, pc)⟩)
    (ht : t.linearize? side = some pt) (hsel : t.selCheck = m.selCheck) :
    (cur.replace m t).linearizationState side = ⟨some (σ, pc.replace m pt)⟩ := by
  induction cur using ind generalizing σ pc with
  | leaf tok | trace | traceOf tok =>
    have hc' := hc
    simp only [linearizationState_leaf, linearizationState_trace, linearizationState_traceOf,
      LinearizationState.of, LinearizationState.mk.injEq, Option.some.injEq,
      Prod.mk.injEq] at hc'
    obtain ⟨rfl, rfl⟩ := hc'
    exact linearizationState_replace_leaf rfl rfl hc ht hsel
  | merge l r ihl ihr =>
    by_cases heq : merge l r = m
    · subst heq; exact linearizationState_replace_self hc ht hsel
    · rw [linearizationState_node] at hc
      rcases hl : l.linearizationState side with ⟨_ | ⟨σl, pl⟩⟩ <;>
        rcases hr : r.linearizationState side with ⟨_ | ⟨σr, pr⟩⟩ <;>
        rw [hl, hr] at hc <;> try cases hc
      rw [LinearizationState.some_mul_some] at hc
      obtain ⟨⟨b, σ'⟩, hcomb, he⟩ := Option.map_eq_some_iff.1 (LinearizationState.mk.inj hc)
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      have hpl : l.linearize? side = some pl := by
        simp [linearize?, hl, LinearizationState.linearized?]
      have hpr : r.linearize? side = some pr := by
        simp [linearize?, hr, LinearizationState.linearized?]
      rw [replace_merge_of_ne heq, linearizationState_node, ihl hl, ihr hr,
        LinearizationState.some_mul_some, hcomb]
      have hl' := toSyntacticObject_of_linearize? hpl
      have hr' := toSyntacticObject_of_linearize? hpr
      cases b <;> dsimp only [cond]
      · rw [LinearizedSyntacticObject.replace_attach
          (by rw [hl', hr']; exact fun h ↦ heq ((merge_comm l r).trans h))]
        rfl
      · rw [LinearizedSyntacticObject.replace_attach (by rw [hl', hr']; exact heq)]
        rfl

theorem linearize?_of_find? {cur m : SyntacticObject} {pc s : LinearizedSyntacticObject}
    (hc : cur.linearize? side = some pc) (hf : pc.find? m = some s) :
    m.linearize? side = some s := by
  rw [← LinearizedSyntacticObject.toSyntacticObject_find? hf]
  exact linearize?_of_mem_subtrees hc (LinearizedSyntacticObject.mem_subtrees_of_find? hf) s.2

end SyntacticObject

/-- A step is harmonic for the head side `side` at a configuration when each daughter it merges
    projects exactly if it takes the head side, an externally merged item is built in its harmonic
    order, and a mover is a term of the object whose trace keeps its selection state. -/
def Step.Harmonic (side : Edge) (τ : SyntacticObject → Option LexicalItem.Token)
    (c : Cfg SyntacticObject) : Step → Prop
  | .em e item => (item : SyntacticObject).linearize? side = some item ∧
      selSide (item : SyntacticObject).selCheck c.current.selCheck = some (decide (e = side))
  | .im mover e => mover ∈ c.current.terms ∧ (mover.headTrace τ).selCheck = mover.selCheck ∧
      selSide mover.selCheck (deleteAccessible mover c.current τ).selCheck =
        some (decide (e = side))
  | .extract mover => mover ∈ c.current.terms ∧ (mover.headTrace τ).selCheck = mover.selCheck
  | .remerge e => ∃ m ∈ c.stack.head?,
      selSide m.selCheck c.current.selCheck = some (decide (e = side))

/-- Each step of a list is harmonic at the configuration it applies to. -/
def Step.HarmonicList (side : Edge) (τ : SyntacticObject → Option LexicalItem.Token) :
    List Step → Cfg SyntacticObject → Prop
  | [], _ => True
  | step :: steps, c => step.Harmonic side τ c ∧ HarmonicList side τ steps (step.run c τ)

private theorem linearize?_deleteAccessible {cur mover : SyntacticObject}
    {pc : LinearizedSyntacticObject} (hc : cur.linearize? side = some pc)
    (hsel : (mover.headTrace τ).selCheck = mover.selCheck) :
    (deleteAccessible mover cur τ).linearize? side =
      some (pc.replace mover (mover.traceLinearized τ)) := by
  obtain ⟨σ, -, hs⟩ := linearizationState_eq_of_linearize? hc
  simp [linearize?, deleteAccessible,
    linearizationState_replace hs (linearize?_headTrace mover τ) hsel,
    LinearizationState.linearized?]

theorem Step.replay?_of_harmonic {step : Step} {c : Cfg SyntacticObject}
    {q : Cfg LinearizedSyntacticObject} (h : step.Harmonic side τ c)
    (hq : c.map (·.linearize? side) = q.map some) :
    ∃ q', step.replay? q τ = some q' ∧ (step.run c τ).map (·.linearize? side) = q'.map some := by
  obtain ⟨cur, st⟩ := c
  obtain ⟨qc, qst⟩ := q
  simp only [Cfg.map, Cfg.mk.injEq] at hq
  obtain ⟨hc, hst⟩ := hq
  have hqc := toSyntacticObject_of_linearize? hc
  cases step with
  | em e item =>
    obtain ⟨hi, hside⟩ := h
    refine ⟨⟨qc.attach e item, qst⟩, rfl, ?_⟩
    simp only [Cfg.map, Step.run, Step.apply_em, Cfg.mk.injEq, hst, and_true]
    exact linearize?_merge hi hc hside
  | im mover e =>
    obtain ⟨hm, hsel, hside⟩ := h
    obtain ⟨s, hs⟩ := Option.isSome_iff_exists.1
      (LinearizedSyntacticObject.isSome_find?_iff.2 (hqc ▸ hm))
    refine ⟨⟨(qc.replace mover (mover.traceLinearized τ)).attach e s, qst⟩,
      by simp [Step.replay?, hs], ?_⟩
    simp only [Cfg.map, Step.run, Step.apply_im, Cfg.mk.injEq, hst, and_true]
    rw [merge_comm]
    exact linearize?_merge (linearize?_of_find? hc hs) (linearize?_deleteAccessible hc hsel) hside
  | extract mover =>
    obtain ⟨hm, hsel⟩ := h
    obtain ⟨s, hs⟩ := Option.isSome_iff_exists.1
      (LinearizedSyntacticObject.isSome_find?_iff.2 (hqc ▸ hm))
    refine ⟨⟨qc.replace mover (mover.traceLinearized τ), s :: qst⟩, by simp [Step.replay?, hs], ?_⟩
    simp only [Cfg.map, Step.run, Step.apply, List.map_cons, hst,
      linearize?_deleteAccessible hc hsel, linearize?_of_find? hc hs]
  | remerge e =>
    obtain ⟨m, hm, hside⟩ := h
    obtain ⟨st, rfl⟩ : ∃ st', st = m :: st' := by
      cases st with
      | nil => cases hm
      | cons m' st' => exact ⟨st', by cases hm; rfl⟩
    obtain ⟨qm, qst', rfl, hqm, hst'⟩ : ∃ qm qst', qst = qm :: qst' ∧
        m.linearize? side = some qm ∧ st.map (·.linearize? side) = qst'.map some := by
      cases qst with
      | nil => cases hst
      | cons qm qst' =>
        simp only [List.map_cons, List.cons.injEq] at hst
        exact ⟨qm, qst', rfl, hst⟩
    refine ⟨⟨qc.attach e qm, qst'⟩, rfl, ?_⟩
    simp only [Cfg.map, Step.run, Cfg.mk.injEq, hst', and_true]
    exact linearize?_merge hqm hc hside

theorem foldlM_replay?_of_harmonicList : ∀ {steps : List Step} {c : Cfg SyntacticObject}
    {q : Cfg LinearizedSyntacticObject}, Step.HarmonicList side τ steps c →
      c.map (·.linearize? side) = q.map some →
      ∃ q', steps.foldlM (fun q (step : Step) ↦ step.replay? q τ) q = some q' ∧
        (steps.foldl (fun c (step : Step) ↦ step.run c τ) c).map (·.linearize? side) =
          q'.map some
  | [], _, q, _, hq => ⟨q, rfl, hq⟩
  | _ :: _, _, _, ⟨h, hs⟩, hq => by
    obtain ⟨q₁, h₁, hq₁⟩ := Step.replay?_of_harmonic h hq
    obtain ⟨q', h', hq'⟩ := foldlM_replay?_of_harmonicList hs hq₁
    exact ⟨q', by simp [List.foldlM_cons, h₁, h'], hq'⟩

/-- A derivation from a leaf whose every step is harmonic externalizes to the harmonic
    linearization of its object: the order the derivation records is the one the head function
    determines. -/
theorem Derivation.externalize?_eq_linearize? {d : Derivation}
    (hi : d.initial.toLinearizedLeaf?.isSome)
    (hd : Step.HarmonicList side τ d.steps ⟨d.initial, []⟩) :
    d.externalize? τ = (d.final τ).linearize? side := by
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 hi
  obtain ⟨q', h', hq'⟩ := foldlM_replay?_of_harmonicList (q := ⟨p, []⟩) hd
    (by simp [Cfg.map, linearize?_of_toLinearizedLeaf? hp])
  simp only [Cfg.map, Cfg.mk.injEq] at hq'
  rw [Derivation.externalize?, Derivation.replay?, hp, Option.bind_some, h', Option.map_some,
    Derivation.final, Derivation.run, hq'.1]

/-- The linearized object is a datum of the derivation, not of the object it derives: merging a
    second leaf on the left and on the right derives one object in two orders. -/
theorem Derivation.not_factorsThrough_final :
    ¬ Function.FactorsThrough (externalize? · selHead) (final · selHead) := fun h ↦ by
  have := @h ⟨.leaf ⟨.of .N [], 0⟩, [.em .left (.leaf ⟨.of .N [], 1⟩)]⟩
    ⟨.leaf ⟨.of .N [], 0⟩, [.em .right (.leaf ⟨.of .N [], 1⟩)]⟩ rfl
  revert this
  decide

end Minimalist
