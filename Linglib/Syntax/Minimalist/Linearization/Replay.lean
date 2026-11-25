/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Derivation.Replay
public import Linglib.Syntax.Minimalist.Derivation.Licensing
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
object](##Minimalist.Derivation.externalize?_eq_linearized?).

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

A derivation is harmonic for a linearization when each daughter it merges projects exactly if it
takes the head side, and each mover leaves a trace with its selection state. Its recorded order is
then the linearization of its object (`Derivation.externalize?_eq_linearized?`). -/

section Harmonic

open LinearizationState

variable {ι : Type} [DecidableEq ι] [TraceLabel LexicalItem.Token ι]
  {φ : SyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι) →ₙ* LinearizationState side ι}
  {τ : SyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι) → Option ι}

namespace LinearizationState.Linearizes

variable (hφ : Linearizes φ)
include hφ

omit [TraceLabel LexicalItem.Token ι] in
private theorem map_replace_self
    {cur t : SyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι)} {σ}
    {pc pt : PlanarSyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι)}
        (hc : φ cur = ⟨some (σ, pc)⟩)
    (ht : (φ t).linearized? = some pt) (hsel : sel (φ t) = sel (φ cur)) :
    φ (cur.replace cur t) = ⟨some (σ, pc.replace cur pt)⟩ := by
  have hpc : (φ cur).linearized? = some pc := by rw [hc]; rfl
  rw [SyntacticObject.replace_self,
    PlanarSyntacticObject.replace_of_toSyntacticObject_eq (hφ.toSyntacticObject_eq hpc)]
  obtain ⟨σt, hσt, hst⟩ := eq_of_linearized? ht
  rw [hσt, hc] at hsel
  cases hsel
  exact hst

omit [TraceLabel LexicalItem.Token ι] in
private theorem map_replace_leaf
    {cur m t : SyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι)}
    {a : Vertex LexicalItem.Token ι} {σ}
        {pc pt : PlanarSyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι)}
    (hs : cur.toUnorderedTree = UnorderedTree.leaf a) (hpv : pc.toRoseTree = .node a [])
    (hc : φ cur = ⟨some (σ, pc)⟩) (ht : (φ t).linearized? = some pt)
    (hsel : sel (φ t) = sel (φ m)) :
    φ (cur.replace m t) = ⟨some (σ, pc.replace m pt)⟩ := by
  by_cases heq : cur = m
  · subst heq; exact hφ.map_replace_self hc ht hsel
  · have hpc : (φ cur).linearized? = some pc := by rw [hc]; rfl
    rw [replace_of_toUnorderedTree_eq_leaf hs heq,
        PlanarSyntacticObject.replace_of_toRoseTree_eq_leaf hpv
      (by rwa [hφ.toSyntacticObject_eq hpc]), hc]

omit [TraceLabel LexicalItem.Token ι] in
private theorem map_replace_of {ℓ : Leaf LexicalItem.Token ι}
    {m t : SyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι)} {σ}
    {pc pt : PlanarSyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι)}
        (hc : φ (FreeCommMagma.of ℓ) = ⟨some (σ, pc)⟩)
    (ht : (φ t).linearized? = some pt) (hsel : sel (φ t) = sel (φ m)) :
    φ (SyntacticObject.replace (FreeCommMagma.of ℓ) m t) = ⟨some (σ, pc.replace m pt)⟩ := by
  obtain rfl := hφ ℓ pc (by rw [hc]; rfl)
  cases ℓ <;> exact hφ.map_replace_leaf rfl rfl hc ht hsel

omit [TraceLabel LexicalItem.Token ι] in
/-- A linearization commutes with replacing a term by an object in the same selection state. -/
theorem map_replace {cur m t : SyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι)} {σ}
    {pc pt : PlanarSyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι)}
        (hc : φ cur = ⟨some (σ, pc)⟩)
    (ht : (φ t).linearized? = some pt) (hsel : sel (φ t) = sel (φ m)) :
    φ (cur.replace m t) = ⟨some (σ, pc.replace m pt)⟩ := by
  induction cur using ind generalizing σ pc with
  | leaf tok => exact hφ.map_replace_of (ℓ := .lex tok) hc ht hsel
  | trace => exact hφ.map_replace_of (ℓ := .trace) hc ht hsel
  | traceOf i => exact hφ.map_replace_of (ℓ := .traceOf i) hc ht hsel
  | merge l r ihl ihr =>
    by_cases heq : merge l r = m
    · subst heq; exact hφ.map_replace_self hc ht hsel
    · rw [show merge l r = l * r from rfl, map_mul] at hc
      rcases hl : φ l with ⟨_ | ⟨σl, pl⟩⟩ <;> rcases hr : φ r with ⟨_ | ⟨σr, pr⟩⟩ <;>
        rw [hl, hr] at hc <;> try cases hc
      rw [some_mul_some] at hc
      have hpl : (φ l).linearized? = some pl := by rw [hl]; rfl
      have hpr : (φ r).linearized? = some pr := by rw [hr]; rfl
      have hl' := hφ.toSyntacticObject_eq hpl
      have hr' := hφ.toSyntacticObject_eq hpr
      rw [replace_merge_of_ne heq, show merge (l.replace m t) (r.replace m t) =
        l.replace m t * r.replace m t from rfl, map_mul, ihl hl, ihr hr, some_mul_some]
      split_ifs at hc ⊢
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (LinearizationState.mk.inj hc))
        rw [PlanarSyntacticObject.replace_attach (by rw [hl', hr']; exact heq)]
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (LinearizationState.mk.inj hc))
        rw [PlanarSyntacticObject.replace_attach
          (by rw [hl', hr']; exact fun h ↦ heq ((merge_comm l r).trans h))]
      · cases hc

omit [TraceLabel LexicalItem.Token ι] in
theorem linearized?_of_find? {cur m : SyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι)}
    {pc s : PlanarSyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι)}
        (hc : (φ cur).linearized? = some pc)
    (hf : pc.find? m = some s) : (φ m).linearized? = some s := by
  rw [← PlanarSyntacticObject.toSyntacticObject_find? hf]
  have h := hφ.linearized?_of_mem_subtrees hc (PlanarSyntacticObject.mem_subtrees_of_find? hf)
    s.isSyntacticObject_toRoseTree
  rwa [← PlanarSyntacticObject.toSyntacticObject_ofRoseTree,
    PlanarSyntacticObject.ofRoseTree_toRoseTree] at h

omit [DecidableEq ι] [TraceLabel LexicalItem.Token ι] in
/-- A leaf in the domain of a linearization linearizes to itself. -/
theorem linearized?_of {ℓ : Leaf LexicalItem.Token ι} (h : sel (φ (FreeCommMagma.of ℓ)) ≠ 0) :
    (φ (FreeCommMagma.of ℓ)).linearized? = some (FreeMagma.of ℓ) := by
  rcases hx : φ (FreeCommMagma.of ℓ) with ⟨_ | ⟨σ, q⟩⟩
  · exact absurd (by rw [hx]; rfl) h
  · obtain rfl := hφ ℓ q (by rw [hx]; rfl)
    rfl

omit [DecidableEq ι] in
/-- The trace of a mover linearizes to its planar trace where the linearization is defined. -/
theorem linearized?_headTrace {m : SyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι)}
    (h : sel (φ (m.headTrace τ)) ≠ 0) :
    (φ (m.headTrace τ)).linearized? = some (m.tracePlanar τ) := by
  unfold headTrace tracePlanar at *
  revert h
  cases τ m <;> exact fun h ↦ hφ.linearized?_of h

private theorem linearized?_deleteAccessible
    {cur mover : SyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι)}
    {pc s : PlanarSyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι)}
        (hc : (φ cur).linearized? = some pc)
    (hs : pc.find? mover = some s) (hsel : sel (φ (mover.headTrace τ)) = sel (φ mover)) :
    (φ (deleteAccessible mover cur τ)).linearized? =
      some (pc.replace mover (mover.tracePlanar τ)) := by
  obtain ⟨σ, -, hσ⟩ := eq_of_linearized? hc
  obtain ⟨σm, hσm, -⟩ := eq_of_linearized? (hφ.linearized?_of_find? hc hs)
  have h0 : sel (φ (mover.headTrace τ)) ≠ 0 := by rw [hsel, hσm]; exact fun h ↦ by cases h
  rw [deleteAccessible, hφ.map_replace hσ (hφ.linearized?_headTrace h0) hsel]
  rfl

end LinearizationState.Linearizes

/-- A step is harmonic for a linearization at a configuration when each daughter it merges
    projects exactly if it takes the head side, an externally merged item is built in its harmonic
    order, and a mover is a term of the object whose trace keeps its selection state. -/
def Step.Harmonic
    (φ : SyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι) →ₙ* LinearizationState side ι)
    (τ : SyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι) → Option ι)
        (c : Cfg (SyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι))) :
    Step ι → Prop
  | .em e item => (φ item.toSyntacticObject).linearized? = some item ∧
      SelectionRule.State.side (sel (φ item.toSyntacticObject)) (sel (φ c.current)) =
        some (decide (e = side))
  | .im mover e => mover ∈ c.current.terms ∧ sel (φ (mover.headTrace τ)) = sel (φ mover) ∧
      SelectionRule.State.side (sel (φ mover)) (sel (φ (deleteAccessible mover c.current τ))) =
        some (decide (e = side))
  | .extract mover => mover ∈ c.current.terms ∧ sel (φ (mover.headTrace τ)) = sel (φ mover)
  | .remerge e => ∃ m ∈ c.stack.head?,
      SelectionRule.State.side (sel (φ m)) (sel (φ c.current)) = some (decide (e = side))

/-- Each step of a list is harmonic at the configuration it applies to. -/
def Step.HarmonicList
    (φ : SyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι) →ₙ* LinearizationState side ι)
    (τ : SyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι) → Option ι) :
    List (Step ι) → Cfg (SyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι)) → Prop
  | [], _ => True
  | step :: steps, c => step.Harmonic φ τ c ∧ HarmonicList φ τ steps (step.run c τ)

instance (c : Cfg (SyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι))) : DecidablePred
    (Step.Harmonic φ τ c) :=
  fun step ↦ by cases step <;> unfold Step.Harmonic <;> infer_instance

instance : ∀ (steps : List (Step ι))
    (c : Cfg (SyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι))),
    Decidable (Step.HarmonicList φ τ steps c)
  | [], _ => isTrue trivial
  | step :: steps, c =>
    haveI := instDecidableHarmonicList steps (step.run c τ)
    inferInstanceAs (Decidable (_ ∧ _))

theorem Step.replay?_of_harmonic (hφ : Linearizes φ) {step : Step ι}
    {c : Cfg (SyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι))}
        {q : Cfg (PlanarSyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι))}
    (h : step.Harmonic φ τ c) (hq : c.map (fun x ↦ (φ x).linearized?) = q.map some) :
    ∃ q', step.replay? q τ = some q' ∧
      (step.run c τ).map (fun x ↦ (φ x).linearized?) = q'.map some := by
  obtain ⟨cur, st⟩ := c
  obtain ⟨qc, qst⟩ := q
  simp only [Cfg.map, Cfg.mk.injEq] at hq
  obtain ⟨hc, hst⟩ := hq
  have hqc := hφ.toSyntacticObject_eq hc
  cases step with
  | em e item =>
    obtain ⟨hi, hside⟩ := h
    refine ⟨⟨qc.attach e item, qst⟩, rfl, ?_⟩
    simp only [Cfg.map, Step.run, Step.apply_em, Cfg.mk.injEq, hst, and_true]
    exact Linearizes.linearized?_merge hi hc hside
  | im mover e =>
    obtain ⟨hm, hsel, hside⟩ := h
    obtain ⟨s, hs⟩ := Option.isSome_iff_exists.1
      (PlanarSyntacticObject.isSome_find?_iff.2 (hqc ▸ hm))
    refine ⟨⟨(qc.replace mover (mover.tracePlanar τ)).attach e s, qst⟩,
      by simp [Step.replay?, hs], ?_⟩
    simp only [Cfg.map, Step.run, Step.apply_im, Cfg.mk.injEq, hst, and_true]
    rw [merge_comm]
    exact Linearizes.linearized?_merge (hφ.linearized?_of_find? hc hs)
      (hφ.linearized?_deleteAccessible hc hs hsel) hside
  | extract mover =>
    obtain ⟨hm, hsel⟩ := h
    obtain ⟨s, hs⟩ := Option.isSome_iff_exists.1
      (PlanarSyntacticObject.isSome_find?_iff.2 (hqc ▸ hm))
    refine ⟨⟨qc.replace mover (mover.tracePlanar τ), s :: qst⟩, by simp [Step.replay?, hs], ?_⟩
    simp only [Cfg.map, Step.run, Step.apply, List.map_cons, hst,
      hφ.linearized?_deleteAccessible hc hs hsel, hφ.linearized?_of_find? hc hs]
  | remerge e =>
    obtain ⟨m, hm, hside⟩ := h
    obtain ⟨st, rfl⟩ : ∃ st', st = m :: st' := by
      cases st with
      | nil => cases hm
      | cons m' st' => exact ⟨st', by cases hm; rfl⟩
    obtain ⟨qm, qst', rfl, hqm, hst'⟩ : ∃ qm qst', qst = qm :: qst' ∧
        (φ m).linearized? = some qm ∧
          st.map (fun x ↦ (φ x).linearized?) = qst'.map some := by
      cases qst with
      | nil => cases hst
      | cons qm qst' =>
        simp only [List.map_cons, List.cons.injEq] at hst
        exact ⟨qm, qst', rfl, hst⟩
    refine ⟨⟨qc.attach e qm, qst'⟩, rfl, ?_⟩
    simp only [Cfg.map, Step.run, Cfg.mk.injEq, hst', and_true]
    exact Linearizes.linearized?_merge hqm hc hside

theorem foldlM_replay?_of_harmonicList (hφ : Linearizes φ) :
    ∀ {steps : List (Step ι)} {c : Cfg (SyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι))}
      {q : Cfg (PlanarSyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι))},
          Step.HarmonicList φ τ steps c →
      c.map (fun x ↦ (φ x).linearized?) = q.map some →
      ∃ q', steps.foldlM (fun q (step : Step ι) ↦ step.replay? q τ) q = some q' ∧
        (steps.foldl (fun c (step : Step ι) ↦ step.run c τ) c).map
          (fun x ↦ (φ x).linearized?) = q'.map some
  | [], _, q, _, hq => ⟨q, rfl, hq⟩
  | _ :: _, _, _, ⟨h, hs⟩, hq => by
    obtain ⟨q₁, h₁, hq₁⟩ := Step.replay?_of_harmonic hφ h hq
    obtain ⟨q', h', hq'⟩ := foldlM_replay?_of_harmonicList hφ hs hq₁
    exact ⟨q', by simp [List.foldlM_cons, h₁, h'], hq'⟩

/-- A derivation from a leaf whose every step is harmonic for a linearization externalizes to the
    linearization of its object: the order the derivation records is the one the head function
    determines. -/
theorem Derivation.externalize?_eq_linearized? (hφ : Linearizes φ) {d : Derivation ι}
    {p : PlanarSyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι)}
        (hi : d.initial.toPlanarLeaf? = some p)
    (h0 : (φ d.initial).linearized? = some p)
    (hd : Step.HarmonicList φ τ d.steps ⟨d.initial, []⟩) :
    d.externalize? τ = (φ (d.final τ)).linearized? := by
  obtain ⟨q', h', hq'⟩ := foldlM_replay?_of_harmonicList (q := ⟨p, []⟩) hφ hd
    (by simp [Cfg.map, h0])
  simp only [Cfg.map, Cfg.mk.injEq] at hq'
  rw [Derivation.externalize?, Derivation.replay?, hi, Option.bind_some, h', Option.map_some,
    Derivation.final, Derivation.run, hq'.1]

end Harmonic

/-! ### Numbered traces

Over a derivation whose traces are numbered by its movers, harmonic linearization is a licensing:
an item is itself, and the trace of a mover is silent, saturated, and headed as the mover is. -/

/-- Harmonic linearization as a licensing: an item with its selectors, in its own order, and a
trace the saturated head of the object moved, linearized as the trace itself. -/
def LinearizationState.licensing (side : Edge) : Licensing (LinearizationState side ℕ) where
  lex tok := .of tok tok.item.sel (.leaf tok)
  trace i x := ⟨x.toOption.map fun s ↦ (⟨s.1.head, []⟩, .labelledTrace i)⟩

/-- The selection component of linearization is triggered Merge, over any derivation. -/
theorem LinearizationState.sel_comp_hom (d : Derivation ℕ) :
    (LinearizationState.sel (side := side)).comp ((LinearizationState.licensing side).hom d) =
      SelectionRule.State.licensing.hom d :=
  Licensing.comp_hom rfl (fun _ ↦ rfl) (fun _ x ↦ by rcases x with ⟨_ | ⟨⟨a, ra⟩, p⟩⟩ <;> rfl) d

/-- Harmonic linearization over a derivation linearizes. -/
theorem LinearizationState.linearizes_hom (d : Derivation ℕ) :
    LinearizationState.Linearizes ((LinearizationState.licensing side).hom d) := fun ℓ p h ↦ by
  rcases ℓ with tok | _ | i
  · exact (Option.some.inj h).symm
  · cases h
  · change ((((LinearizationState.licensing side).traceStates d.movedItems)[i]?).getD 0).linearized?
      = some p at h
    rcases hx : ((LinearizationState.licensing side).traceStates d.movedItems)[i]? with _ | x
    · rw [hx] at h; cases h
    · obtain ⟨y, rfl⟩ := Licensing.exists_eq_trace_of_getElem? _ hx
      rw [hx] at h
      rcases y with ⟨_ | s⟩
      · cases h
      · exact (Option.some.inj h).symm

/-- The linearized object is a datum of the derivation, not of the object it derives: merging a
    second leaf on the left and on the right derives one object in two orders. -/
theorem Derivation.not_factorsThrough_final :
    ¬ Function.FactorsThrough (externalize? · selectionHead) (final · selectionHead) := fun h ↦ by
  have := @h ⟨.leaf ⟨.of .N [], 0⟩, [.em .left (.leaf ⟨.of .N [], 1⟩)]⟩
    ⟨.leaf ⟨.of .N [], 0⟩, [.em .right (.leaf ⟨.of .N [], 1⟩)]⟩ rfl
  revert this
  decide

end Minimalist
