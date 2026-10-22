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
# Replaying a derivation on planar objects

Free symmetric Merge builds unordered objects, so the surface order is not recoverable from
`Derivation.final`, but each step of a derivation records the side its new daughter takes.
`Derivation.replay?` replays the steps with Merge on planar trees, each daughter on its side, on
a configuration of a `PlanarSyntacticObject` and the planar copies extracted from it, so that
surface orders `decide`; `Derivation.externalize?` is its object. This is Merge in the
noncommutative magma of planar trees ([marcolli-chomsky-berwick-2025] §1.13.1), and forgetting the
order is a morphism of magmas (their Lemma 1.13.1), so a successful replay forgets to the
derivation's own configuration (`Derivation.replay?_faithful`): the readouts `surfaceTokens`,
`surfaceCats` and `surfacePhon` are the word order of the derived object. The order is a datum
of the derivation, not of the object it derives, since one object has derivations in two orders
(`Derivation.not_factorsThrough_final`). When every daughter a derivation merges takes the head
side exactly if it projects, the order is the harmonic planarization of its object, the harmonic
candidate for MCB's externalization section (`Derivation.externalize?_eq_planarize?`). The
replay is partial, `none` when an
externally merged item is not a leaf, an unordered complex item having no order to replay, when
a mover is absent, or when nothing is left to merge back. Traces are unpronounced. Sibling
accounts of linearization: the selection-induced harmonic order
(`Linearization/Externalization.lean`) and cyclic linearization (`Linearization/Cyclic.lean`).

## Main definitions

* `Minimalist.PlanarSyntacticObject.find?`, `replace`: an occurrence and its replacement.
* `Minimalist.Step.replay?`, `Minimalist.Derivation.replay?`, `externalize?`: the replay.
* `Minimalist.Step.Harmonic`, `Step.HarmonicList`: steps that place the projecting daughter on
  the head side.
* `Minimalist.Derivation.surfaceTokens`, `surfaceCats`, `surfacePhon`.

## Main results

* `Minimalist.Derivation.replay?_faithful`, `externalize?_faithful`: a successful replay forgets
  to `run` and `final`.
* `Minimalist.Derivation.not_factorsThrough_final`: the planar object does not factor through
  the derived object.
* `Minimalist.Derivation.externalize?_eq_planarize?`: a harmonic derivation records the harmonic
  planarization of its object.

## References

* [marcolli-chomsky-berwick-2025], §1.12 and §1.13 (Lemmas 1.13.1 and 1.13.5)
-/

@[expose] public section

namespace Minimalist

open RoseTree UnorderedTree SyntacticObject

/-! ### Planar leaves -/

/-- The planar form of a leaf object, which has only one; `none` on a merged object. -/
def SyntacticObject.toPlanarLeaf? (s : SyntacticObject) : Option PlanarSyntacticObject :=
  match s.val.value with
  | .inl (some tok) => some (.leaf tok)
  | .inl none => none
  | .inr none => some .trace
  | .inr (some tok) => some (.traceOf tok)

/-- A planar leaf forgets to the object it came from. -/
theorem SyntacticObject.toSyntacticObject_of_toPlanarLeaf? {s : SyntacticObject}
    {p : PlanarSyntacticObject} (h : s.toPlanarLeaf? = some p) : p.toSyntacticObject = s := by
  rcases s.exists_form with ⟨tok, rfl⟩ | rfl | ⟨tok, rfl⟩ | ⟨l, r, rfl⟩ <;>
    simp [toPlanarLeaf?, merge_val] at h <;> subst h <;> rfl

/-! ### Occurrences in planar objects -/

namespace PlanarSyntacticObject

/-- The leftmost, outermost subtree of `p` projecting to `target`. -/
def find? (p : PlanarSyntacticObject) (target : SyntacticObject) : Option PlanarSyntacticObject :=
  (p.val.subtrees.find? (mk · = target.val)).pmap (p := (mk · = target.val))
    (fun s hs ↦ ⟨s, hs.symm ▸ target.2⟩) fun _ h ↦ by simpa using List.find?_some h

theorem toSyntacticObject_find? {p s : PlanarSyntacticObject} {target : SyntacticObject}
    (h : p.find? target = some s) : s.toSyntacticObject = target := by
  obtain ⟨t, ht, -, rfl⟩ := Option.pmap_eq_some_iff.1 (by rwa [find?] at h)
  exact Subtype.ext ht

/-- Every subtree of `p` projecting to `target` replaced by `rep`. -/
def replace (p : PlanarSyntacticObject) (target : SyntacticObject)
    (rep : PlanarSyntacticObject) : PlanarSyntacticObject :=
  ⟨replaceIf (mk · = target.val) rep.val p.val, by
    rw [mk_replaceIf]
    exact isSyntacticObject_replace target rep.toSyntacticObject p.toSyntacticObject⟩

/-- Replacement forgets to substitution in the syntactic object. -/
@[simp] theorem toSyntacticObject_replace (p : PlanarSyntacticObject) (target : SyntacticObject)
    (rep : PlanarSyntacticObject) :
    (p.replace target rep).toSyntacticObject
      = p.toSyntacticObject.replace target rep.toSyntacticObject :=
  Subtype.ext (mk_replaceIf _ _ _)

/-- The terms of a planar object's object are the projections of its planar subtrees. -/
theorem mem_terms_toSyntacticObject {p : PlanarSyntacticObject} {m : SyntacticObject} :
    m ∈ p.toSyntacticObject.terms ↔ ∃ q ∈ p.val.subtrees, mk q = m.val := by
  rw [← val_mem_subtrees, toSyntacticObject_val, subtrees_mk, unorderedSubtrees_eq_map,
    Multiset.mem_coe, List.mem_map]

/-- An occurrence is found exactly when the target is a term. -/
theorem isSome_find?_iff {p : PlanarSyntacticObject} {m : SyntacticObject} :
    (p.find? m).isSome ↔ m ∈ p.toSyntacticObject.terms := by
  rw [mem_terms_toSyntacticObject, find?, Option.isSome_pmap, List.find?_isSome]
  simp

/-- The occurrence found is a planar subtree. -/
theorem mem_subtrees_of_find? {p s : PlanarSyntacticObject} {m : SyntacticObject}
    (h : p.find? m = some s) : s.val ∈ p.val.subtrees := by
  obtain ⟨t, -, ht, rfl⟩ := Option.pmap_eq_some_iff.1 (by rwa [find?] at h)
  exact List.mem_of_find?_eq_some ht

/-- Replacing at the root yields the replacement. -/
theorem replace_of_toSyntacticObject_eq {p r : PlanarSyntacticObject} {target : SyntacticObject}
    (h : p.toSyntacticObject = target) : p.replace target r = r := by
  obtain ⟨⟨a, cs⟩, hp⟩ := p
  apply Subtype.ext
  simp only [replace, replaceIf_node]
  split_ifs with hc
  · rfl
  · exact absurd (congrArg Subtype.val h) hc

/-- Away from the root, replacement recurses into the daughters. -/
theorem replace_attach {p d r : PlanarSyntacticObject} {target : SyntacticObject} {e : Edge}
    (h : SyntacticObject.merge d.toSyntacticObject p.toSyntacticObject ≠ target) :
    (p.attach e d).replace target r = (p.replace target r).attach e (d.replace target r) := by
  have h' : (p.attach e d).toSyntacticObject ≠ target := by rwa [toSyntacticObject_attach]
  apply Subtype.ext
  cases e <;> simp only [replace, attach, merge_val, replaceIf_node, List.map_cons,
    List.map_nil] <;> split_ifs with hc <;> first | rfl | exact (h' (Subtype.ext hc)).elim

/-- A leaf other than the target is kept. -/
theorem replace_of_val_eq_leaf {p r : PlanarSyntacticObject} {target : SyntacticObject}
    {a : Vertex} (hp : p.val = RoseTree.leaf a) (h : p.toSyntacticObject ≠ target) :
    p.replace target r = p := by
  apply Subtype.ext
  simp only [replace, hp, replaceIf_node, List.map_nil]
  split_ifs with hc
  · exact (h (Subtype.ext (by rw [toSyntacticObject_val, hp]; exact hc))).elim
  · rfl

end PlanarSyntacticObject

/-- The planar trace a moved object leaves, `SyntacticObject.headTrace` with its order. -/
def SyntacticObject.tracePlanar (s : SyntacticObject)
    (τ : SyntacticObject → Option LexicalItem.Token := selHead) : PlanarSyntacticObject :=
  (τ s).elim PlanarSyntacticObject.trace PlanarSyntacticObject.traceOf

/-- The planar trace of `s` is the trace leaf of its label. -/
theorem SyntacticObject.tracePlanar_val (s : SyntacticObject)
    (τ : SyntacticObject → Option LexicalItem.Token) :
    (s.tracePlanar τ).val = .node (.inr (τ s)) [] := by
  unfold tracePlanar; cases τ s <;> rfl

@[simp] theorem SyntacticObject.toSyntacticObject_tracePlanar (s : SyntacticObject)
    (τ : SyntacticObject → Option LexicalItem.Token) :
    (s.tracePlanar τ).toSyntacticObject = s.headTrace τ := by
  unfold tracePlanar headTrace; cases τ s <;> rfl

variable {side : Edge}

/-- A leaf's planar form is its harmonic planarization. -/
theorem planarize?_of_toPlanarLeaf? {s : SyntacticObject} {p : PlanarSyntacticObject}
    (h : s.toPlanarLeaf? = some p) : s.planarize? side = some p := by
  rcases s.exists_form with ⟨tok, rfl⟩ | rfl | ⟨tok, rfl⟩ | ⟨l, r, rfl⟩ <;>
    simp [toPlanarLeaf?, merge_val] at h <;> subst h <;> rfl

/-- The trace a mover leaves is planarized as its planar trace. -/
theorem planarize?_headTrace (s : SyntacticObject)
    (τ : SyntacticObject → Option LexicalItem.Token) :
    (s.headTrace τ).planarize? side = some (s.tracePlanar τ) := by
  unfold headTrace tracePlanar; cases τ s <;> rfl


/-! ### The replay -/

open Derivation (Cfg)

/-- A step on a planar configuration, `Step.run` with each new daughter on its side. Internal
    Merge raises the leftmost occurrence of the mover, leaving the trace of its head under `τ`,
    and an extraction stacks it; `none` when an externally merged item is not a leaf, the mover is
    absent, or the stack is empty. -/
def Step.replay? (step : Step) (c : Cfg PlanarSyntacticObject)
    (τ : SyntacticObject → Option LexicalItem.Token := selHead) :
    Option (Cfg PlanarSyntacticObject) :=
  match step, c with
  | .em side item, ⟨p, st⟩ => item.toPlanarLeaf?.map fun i ↦ ⟨p.attach side i, st⟩
  | .im mover side, ⟨p, st⟩ =>
      (p.find? mover).map fun s ↦ ⟨(p.replace mover (mover.tracePlanar τ)).attach side s, st⟩
  | .extract mover, ⟨p, st⟩ =>
      (p.find? mover).map fun s ↦ ⟨p.replace mover (mover.tracePlanar τ), s :: st⟩
  | .remerge side, ⟨p, m :: st⟩ => some ⟨p.attach side m, st⟩
  | .remerge _, ⟨_, []⟩ => none

namespace Derivation

/-- The derivation's planar configuration under the trace encoder `τ`, or `none` if a merged item
    is not a leaf, a mover is absent, or `remerge` finds the stack empty. -/
def replay? (d : Derivation) (τ : SyntacticObject → Option LexicalItem.Token := selHead) :
    Option (Cfg PlanarSyntacticObject) :=
  d.initial.toPlanarLeaf?.bind fun p ↦ d.steps.foldlM (fun c step ↦ step.replay? c τ) ⟨p, []⟩

/-- The derivation's planar object under the trace encoder `τ`; copies still on the stack are not
    part of it. -/
def externalize? (d : Derivation) (τ : SyntacticObject → Option LexicalItem.Token := selHead) :
    Option PlanarSyntacticObject :=
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

/-- A successful replay step forgets to `Step.run`. -/
private theorem Step.map_of_replay? {c c' : Cfg PlanarSyntacticObject} {step : Step}
    (h : step.replay? c τ = some c') :
    c'.map PlanarSyntacticObject.toSyntacticObject
      = step.run (c.map PlanarSyntacticObject.toSyntacticObject) τ := by
  obtain ⟨p, st⟩ := c
  cases step with
  | em side item =>
    obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.1 h
    simp [Cfg.map, Step.run, Step.apply_em, toSyntacticObject_of_toPlanarLeaf? hi]
  | im mover side =>
    obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.1 h
    simp [Cfg.map, Step.run, Step.apply_im, deleteAccessible,
      PlanarSyntacticObject.toSyntacticObject_find? hs, SyntacticObject.merge_comm]
  | extract mover =>
    obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.1 h
    simp [Cfg.map, Step.run, Step.apply, deleteAccessible,
      PlanarSyntacticObject.toSyntacticObject_find? hs]
  | remerge side =>
    rcases st with _ | ⟨m, st⟩
    · cases h
    · obtain rfl := Option.some.inj h
      simp [Cfg.map, Step.run, Step.apply_em]

/-- A successful replay forgets to the derivation's configuration, the object and every copy on
    the stack, forgetting the order being a morphism of magmas
    ([marcolli-chomsky-berwick-2025] Lemma 1.13.1). -/
theorem Derivation.replay?_faithful (d : Derivation) {c : Cfg PlanarSyntacticObject}
    (h : d.replay? τ = some c) :
    c.map PlanarSyntacticObject.toSyntacticObject = d.run τ := by
  obtain ⟨p, hp, h⟩ := Option.bind_eq_some_iff.1 h
  rw [List.foldl_eq_of_foldlM_eq_some (f := fun c (step : Step) ↦ step.replay? c τ)
    (g := fun c (step : Step) ↦ step.run c τ) (π := Cfg.map PlanarSyntacticObject.toSyntacticObject)
    (fun _ _ _ ↦ Step.map_of_replay?) h, Derivation.run, Cfg.map, List.map_nil,
    toSyntacticObject_of_toPlanarLeaf? hp]

/-- A successful externalization forgets to the derived object, so the surface readouts are the
    word order of `final` itself. -/
theorem Derivation.externalize?_faithful (d : Derivation) {p : PlanarSyntacticObject}
    (h : d.externalize? τ = some p) : p.toSyntacticObject = d.final τ := by
  obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.1 h
  rw [Derivation.final, ← d.replay?_faithful hc, Cfg.map_current]

/-- Faithfulness holds for prefixes, since a successful replay of the first `n` steps forgets to
    stage `n`. -/
theorem Derivation.externalize?_take_faithful (d : Derivation) (n : Nat)
    {p : PlanarSyntacticObject} (h : (d.take n).externalize? τ = some p) :
    p.toSyntacticObject = d.stageAt n τ :=
  externalize?_faithful (d.take n) h

/-! ### Harmonic derivations

A derivation is harmonic for a head side when each daughter it merges projects exactly if it takes
the head side, and each mover leaves a trace with its selection state. Its recorded order is then
the harmonic planarization of its object (`Derivation.externalize?_eq_planarize?`). -/

namespace SyntacticObject

/-- Replacing an object by one with its selection state, at the root. -/
private theorem linearizationState_replace_self {cur t : SyntacticObject} {σ}
    {pc pt : PlanarSyntacticObject} (hc : cur.linearizationState side = ⟨some (σ, pc)⟩)
    (ht : t.planarize? side = some pt) (hsel : t.selCheck = cur.selCheck) :
    (cur.replace cur t).linearizationState side = ⟨some (σ, pc.replace cur pt)⟩ := by
  have hpc : cur.planarize? side = some pc := by simp [planarize?, hc, LinearizationState.planar?]
  rw [replace_self,
    PlanarSyntacticObject.replace_of_toSyntacticObject_eq (toSyntacticObject_of_planarize? hpc)]
  obtain ⟨σt, hσt, hst⟩ := linearizationState_eq_of_planarize? ht
  have : cur.selCheck = ⟨some σ⟩ := by rw [← sel_linearizationState side cur, hc]; rfl
  rw [hσt, this] at hsel
  cases hsel
  exact hst

/-- Replacing in a leaf, which is the target or is kept. -/
private theorem linearizationState_replace_leaf {cur m t : SyntacticObject} {a : Vertex} {σ}
    {pc pt : PlanarSyntacticObject} (hs : cur.val = UnorderedTree.leaf a)
    (hpv : pc.val = .node a []) (hc : cur.linearizationState side = ⟨some (σ, pc)⟩)
    (ht : t.planarize? side = some pt) (hsel : t.selCheck = m.selCheck) :
    (cur.replace m t).linearizationState side = ⟨some (σ, pc.replace m pt)⟩ := by
  by_cases heq : cur = m
  · subst heq; exact linearizationState_replace_self hc ht hsel
  · have hpc : cur.planarize? side = some pc := by
      simp [planarize?, hc, LinearizationState.planar?]
    rw [replace_of_val_eq_leaf hs heq, PlanarSyntacticObject.replace_of_val_eq_leaf hpv
      (by rwa [toSyntacticObject_of_planarize? hpc]), hc]

/-- Replacing a term by an object with its selection state keeps the selection state, and the
    planarization changes by the same replacement. -/
theorem linearizationState_replace {cur m t : SyntacticObject} {σ}
    {pc pt : PlanarSyntacticObject} (hc : cur.linearizationState side = ⟨some (σ, pc)⟩)
    (ht : t.planarize? side = some pt) (hsel : t.selCheck = m.selCheck) :
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
      have hpl : l.planarize? side = some pl := by
        simp [planarize?, hl, LinearizationState.planar?]
      have hpr : r.planarize? side = some pr := by
        simp [planarize?, hr, LinearizationState.planar?]
      rw [replace_merge_of_ne heq, linearizationState_node, ihl hl, ihr hr,
        LinearizationState.some_mul_some, hcomb]
      have hl' := toSyntacticObject_of_planarize? hpl
      have hr' := toSyntacticObject_of_planarize? hpr
      cases b <;> dsimp only [cond]
      · rw [PlanarSyntacticObject.replace_attach
          (by rw [hl', hr']; exact fun h ↦ heq ((merge_comm l r).trans h))]
        rfl
      · rw [PlanarSyntacticObject.replace_attach (by rw [hl', hr']; exact heq)]
        rfl

/-- The occurrence the replay finds in a harmonic planarization is the mover's own. -/
theorem planarize?_of_find? {cur m : SyntacticObject} {pc s : PlanarSyntacticObject}
    (hc : cur.planarize? side = some pc) (hf : pc.find? m = some s) :
    m.planarize? side = some s := by
  rw [← PlanarSyntacticObject.toSyntacticObject_find? hf]
  exact planarize?_of_mem_subtrees hc (PlanarSyntacticObject.mem_subtrees_of_find? hf) s.2

end SyntacticObject

/-- A step is harmonic for the head side `side` at a configuration when each daughter it merges
    projects exactly if it takes the head side, an externally merged item is a leaf, and a mover
    is a term of the object whose trace keeps its selection state. -/
def Step.Harmonic (side : Edge) (τ : SyntacticObject → Option LexicalItem.Token)
    (c : Cfg SyntacticObject) : Step → Prop
  | .em e item => item.toPlanarLeaf?.isSome ∧
      selSide item.selCheck c.current.selCheck = some (decide (e = side))
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

/-- The remainder of a harmonic movement is the replaced planarization. -/
private theorem planarize?_deleteAccessible {cur mover : SyntacticObject}
    {pc : PlanarSyntacticObject} (hc : cur.planarize? side = some pc)
    (hsel : (mover.headTrace τ).selCheck = mover.selCheck) :
    (deleteAccessible mover cur τ).planarize? side =
      some (pc.replace mover (mover.tracePlanar τ)) := by
  obtain ⟨σ, -, hs⟩ := linearizationState_eq_of_planarize? hc
  simp [planarize?, deleteAccessible,
    linearizationState_replace hs (planarize?_headTrace mover τ) hsel, LinearizationState.planar?]

/-- A harmonic step replays to the harmonic planarization of the configuration it reaches. -/
theorem Step.replay?_of_harmonic {step : Step} {c : Cfg SyntacticObject}
    {q : Cfg PlanarSyntacticObject} (h : step.Harmonic side τ c)
    (hq : c.map (·.planarize? side) = q.map some) :
    ∃ q', step.replay? q τ = some q' ∧ (step.run c τ).map (·.planarize? side) = q'.map some := by
  obtain ⟨cur, st⟩ := c
  obtain ⟨qc, qst⟩ := q
  simp only [Cfg.map, Cfg.mk.injEq] at hq
  obtain ⟨hc, hst⟩ := hq
  have hqc := toSyntacticObject_of_planarize? hc
  cases step with
  | em e item =>
    obtain ⟨hi, hside⟩ := h
    obtain ⟨i, hi⟩ := Option.isSome_iff_exists.1 hi
    refine ⟨⟨qc.attach e i, qst⟩, by simp [Step.replay?, hi], ?_⟩
    simp only [Cfg.map, Step.run, Step.apply_em, Cfg.mk.injEq, hst, and_true]
    exact planarize?_merge (planarize?_of_toPlanarLeaf? hi) hc hside
  | im mover e =>
    obtain ⟨hm, hsel, hside⟩ := h
    obtain ⟨s, hs⟩ := Option.isSome_iff_exists.1
      (PlanarSyntacticObject.isSome_find?_iff.2 (hqc ▸ hm))
    refine ⟨⟨(qc.replace mover (mover.tracePlanar τ)).attach e s, qst⟩,
      by simp [Step.replay?, hs], ?_⟩
    simp only [Cfg.map, Step.run, Step.apply_im, Cfg.mk.injEq, hst, and_true]
    rw [merge_comm]
    exact planarize?_merge (planarize?_of_find? hc hs) (planarize?_deleteAccessible hc hsel) hside
  | extract mover =>
    obtain ⟨hm, hsel⟩ := h
    obtain ⟨s, hs⟩ := Option.isSome_iff_exists.1
      (PlanarSyntacticObject.isSome_find?_iff.2 (hqc ▸ hm))
    refine ⟨⟨qc.replace mover (mover.tracePlanar τ), s :: qst⟩, by simp [Step.replay?, hs], ?_⟩
    simp only [Cfg.map, Step.run, Step.apply, List.map_cons, hst,
      planarize?_deleteAccessible hc hsel, planarize?_of_find? hc hs]
  | remerge e =>
    obtain ⟨m, hm, hside⟩ := h
    obtain ⟨st, rfl⟩ : ∃ st', st = m :: st' := by
      cases st with
      | nil => cases hm
      | cons m' st' => exact ⟨st', by cases hm; rfl⟩
    obtain ⟨qm, qst', rfl, hqm, hst'⟩ : ∃ qm qst', qst = qm :: qst' ∧
        m.planarize? side = some qm ∧ st.map (·.planarize? side) = qst'.map some := by
      cases qst with
      | nil => cases hst
      | cons qm qst' =>
        simp only [List.map_cons, List.cons.injEq] at hst
        exact ⟨qm, qst', rfl, hst⟩
    refine ⟨⟨qc.attach e qm, qst'⟩, rfl, ?_⟩
    simp only [Cfg.map, Step.run, Step.apply_em, Cfg.mk.injEq, hst', and_true]
    exact planarize?_merge hqm hc hside

/-- A harmonic list of steps replays to the harmonic planarization of the configuration it
    reaches. -/
theorem foldlM_replay?_of_harmonicList : ∀ {steps : List Step} {c : Cfg SyntacticObject}
    {q : Cfg PlanarSyntacticObject}, Step.HarmonicList side τ steps c →
      c.map (·.planarize? side) = q.map some →
      ∃ q', steps.foldlM (fun q (step : Step) ↦ step.replay? q τ) q = some q' ∧
        (steps.foldl (fun c (step : Step) ↦ step.run c τ) c).map (·.planarize? side) =
          q'.map some
  | [], _, q, _, hq => ⟨q, rfl, hq⟩
  | _ :: _, _, _, ⟨h, hs⟩, hq => by
    obtain ⟨q₁, h₁, hq₁⟩ := Step.replay?_of_harmonic h hq
    obtain ⟨q', h', hq'⟩ := foldlM_replay?_of_harmonicList hs hq₁
    exact ⟨q', by simp [List.foldlM_cons, h₁, h'], hq'⟩

/-- A derivation from a leaf whose every step is harmonic externalizes to the harmonic
    planarization of its object: the order the derivation records is the one the head function
    determines. -/
theorem Derivation.externalize?_eq_planarize? {d : Derivation}
    (hi : d.initial.toPlanarLeaf?.isSome) (hd : Step.HarmonicList side τ d.steps ⟨d.initial, []⟩) :
    d.externalize? τ = (d.final τ).planarize? side := by
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 hi
  obtain ⟨q', h', hq'⟩ := foldlM_replay?_of_harmonicList (q := ⟨p, []⟩) hd
    (by simp [Cfg.map, planarize?_of_toPlanarLeaf? hp])
  simp only [Cfg.map, Cfg.mk.injEq] at hq'
  rw [Derivation.externalize?, Derivation.replay?, hp, Option.bind_some, h', Option.map_some,
    Derivation.final, Derivation.run, hq'.1]

/-- The planar object is a datum of the derivation, not of the object it derives: merging a
    second leaf on the left and on the right derives one object in two orders. -/
theorem Derivation.not_factorsThrough_final :
    ¬ Function.FactorsThrough (externalize? · selHead) (final · selHead) := fun h ↦ by
  have := @h ⟨.leaf ⟨.of .N [], 0⟩, [.em .left (.leaf ⟨.of .N [], 1⟩)]⟩
    ⟨.leaf ⟨.of .N [], 0⟩, [.em .right (.leaf ⟨.of .N [], 1⟩)]⟩ (merge_comm _ _)
  revert this
  decide

end Minimalist
