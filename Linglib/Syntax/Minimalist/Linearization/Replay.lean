/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Derivation.Replay
public import Linglib.Syntax.Minimalist.Linearization.Externalization

/-!
# The word order of a derivation

Free symmetric Merge builds unordered objects, so the surface order is not recoverable from
`Derivation.final`, but each step records the side its new daughter takes and the replay of
`Derivation/Replay.lean` keeps it. The readouts `surfaceTokens`, `surfaceCats` and `surfacePhon`
are the word order of the replayed object. The order is a datum of the derivation and not of its
object: [the linearized object does not factor through the derived
one](##Minimalist.Derivation.not_factorsThrough_final), and a derivation whose daughters take the
head side exactly when they project [records the harmonic linearization of its
object](##Minimalist.Derivation.externalize?_eq_linearize?).

## Implementation notes

* Traces are unpronounced.
* Sibling accounts of linearization are the selection-induced harmonic order
  (`Linearization/Externalization.lean`) and cyclic linearization (`Linearization/Cyclic.lean`).

## References

* [marcolli-chomsky-berwick-2025], §1.12 and §1.13 (Lemma 1.13.5)
-/

@[expose] public section

namespace Minimalist

open RoseTree UnorderedTree SyntacticObject

variable {side : Edge}

theorem linearize?_of_toPlanarLeaf? {s : SyntacticObject} {p : PlanarSyntacticObject}
    (h : s.toPlanarLeaf? = some p) : s.linearize? side = some p := by
  rcases s.exists_form with ⟨tok, rfl⟩ | rfl | ⟨tok, rfl⟩ | ⟨l, r, rfl⟩ <;>
    simp [toPlanarLeaf?, toUnorderedTree_merge] at h <;> subst h <;> rfl

theorem linearize?_headTrace (s : SyntacticObject)
    (τ : SyntacticObject → Option LexicalItem.Token) :
    (s.headTrace τ).linearize? side = some (s.tracePlanar τ) := by
  unfold headTrace tracePlanar; cases τ s <;> rfl


/-! ### Surface readouts -/

open Derivation (Cfg)

variable {τ : SyntacticObject → Option LexicalItem.Token}

namespace Derivation

/-- The pronounced tokens, left to right; empty if the replay fails. -/
def surfaceTokens (d : Derivation) : List LexicalItem.Token :=
  (d.externalize?.map (·.yield)).getD []

/-- The surface category sequence, the readout of word-order studies. -/
def surfaceCats (d : Derivation) : List Cat := d.surfaceTokens.map (·.item.cat)

/-- The surface string lists the pronounced forms left to right, dropping empty forms. -/
def surfacePhon (d : Derivation) : List String :=
  d.surfaceTokens.filterMap (·.item.phonForm?)

end Derivation

/-! ### Harmonic derivations

A derivation is harmonic for a head side when each daughter it merges projects exactly if it takes
the head side, and each mover leaves a trace with its selection state. Its recorded order is then
the harmonic linearization of its object (`Derivation.externalize?_eq_linearize?`). -/

namespace SyntacticObject

private theorem linearizationState_replace_self {cur t : SyntacticObject} {σ}
    {pc pt : PlanarSyntacticObject} (hc : cur.linearizationState side = ⟨some (σ, pc)⟩)
    (ht : t.linearize? side = some pt) (hsel : t.selCheck = cur.selCheck) :
    (cur.replace cur t).linearizationState side = ⟨some (σ, pc.replace cur pt)⟩ := by
  have hpc : cur.linearize? side = some pc := by
    simp [linearize?, hc, LinearizationState.linearized?]
  rw [replace_self,
    PlanarSyntacticObject.replace_of_toSyntacticObject_eq (toSyntacticObject_of_linearize? hpc)]
  obtain ⟨σt, hσt, hst⟩ := linearizationState_eq_of_linearize? ht
  have : cur.selCheck = ⟨some σ⟩ := by rw [← sel_linearizationState side cur, hc]; rfl
  rw [hσt, this] at hsel
  cases hsel
  exact hst

private theorem linearizationState_replace_leaf {cur m t : SyntacticObject} {a : Vertex} {σ}
    {pc pt : PlanarSyntacticObject} (hs : cur.toUnorderedTree = UnorderedTree.leaf a)
    (hpv : pc.toRoseTree = .node a []) (hc : cur.linearizationState side = ⟨some (σ, pc)⟩)
    (ht : t.linearize? side = some pt) (hsel : t.selCheck = m.selCheck) :
    (cur.replace m t).linearizationState side = ⟨some (σ, pc.replace m pt)⟩ := by
  by_cases heq : cur = m
  · subst heq; exact linearizationState_replace_self hc ht hsel
  · have hpc : cur.linearize? side = some pc := by
      simp [linearize?, hc, LinearizationState.linearized?]
    rw [replace_of_toUnorderedTree_eq_leaf hs heq,
        PlanarSyntacticObject.replace_of_toRoseTree_eq_leaf hpv
      (by rwa [toSyntacticObject_of_linearize? hpc]), hc]

theorem linearizationState_replace {cur m t : SyntacticObject} {σ}
    {pc pt : PlanarSyntacticObject} (hc : cur.linearizationState side = ⟨some (σ, pc)⟩)
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
      · rw [PlanarSyntacticObject.replace_attach
          (by rw [hl', hr']; exact fun h ↦ heq ((merge_comm l r).trans h))]
        rfl
      · rw [PlanarSyntacticObject.replace_attach (by rw [hl', hr']; exact heq)]
        rfl

theorem linearize?_of_find? {cur m : SyntacticObject} {pc s : PlanarSyntacticObject}
    (hc : cur.linearize? side = some pc) (hf : pc.find? m = some s) :
    m.linearize? side = some s := by
  rw [← PlanarSyntacticObject.toSyntacticObject_find? hf]
  have h := linearize?_of_mem_subtrees hc (PlanarSyntacticObject.mem_subtrees_of_find? hf)
    s.isSyntacticObject_toRoseTree
  rwa [← PlanarSyntacticObject.toSyntacticObject_ofRoseTree,
    PlanarSyntacticObject.ofRoseTree_toRoseTree] at h

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
    {pc : PlanarSyntacticObject} (hc : cur.linearize? side = some pc)
    (hsel : (mover.headTrace τ).selCheck = mover.selCheck) :
    (deleteAccessible mover cur τ).linearize? side =
      some (pc.replace mover (mover.tracePlanar τ)) := by
  obtain ⟨σ, -, hs⟩ := linearizationState_eq_of_linearize? hc
  simp [linearize?, deleteAccessible,
    linearizationState_replace hs (linearize?_headTrace mover τ) hsel,
    LinearizationState.linearized?]

theorem Step.replay?_of_harmonic {step : Step} {c : Cfg SyntacticObject}
    {q : Cfg PlanarSyntacticObject} (h : step.Harmonic side τ c)
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
      (PlanarSyntacticObject.isSome_find?_iff.2 (hqc ▸ hm))
    refine ⟨⟨(qc.replace mover (mover.tracePlanar τ)).attach e s, qst⟩,
      by simp [Step.replay?, hs], ?_⟩
    simp only [Cfg.map, Step.run, Step.apply_im, Cfg.mk.injEq, hst, and_true]
    rw [merge_comm]
    exact linearize?_merge (linearize?_of_find? hc hs) (linearize?_deleteAccessible hc hsel) hside
  | extract mover =>
    obtain ⟨hm, hsel⟩ := h
    obtain ⟨s, hs⟩ := Option.isSome_iff_exists.1
      (PlanarSyntacticObject.isSome_find?_iff.2 (hqc ▸ hm))
    refine ⟨⟨qc.replace mover (mover.tracePlanar τ), s :: qst⟩, by simp [Step.replay?, hs], ?_⟩
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
    {q : Cfg PlanarSyntacticObject}, Step.HarmonicList side τ steps c →
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
    (hi : d.initial.toPlanarLeaf?.isSome)
    (hd : Step.HarmonicList side τ d.steps ⟨d.initial, []⟩) :
    d.externalize? τ = (d.final τ).linearize? side := by
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 hi
  obtain ⟨q', h', hq'⟩ := foldlM_replay?_of_harmonicList (q := ⟨p, []⟩) hd
    (by simp [Cfg.map, linearize?_of_toPlanarLeaf? hp])
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
