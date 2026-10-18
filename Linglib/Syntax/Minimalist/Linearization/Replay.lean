/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Derivation.Basic

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
(`Derivation.not_exists_externalize?_eq_comp_final`). The replay is partial, `none` when an
externally merged item is not a leaf, an unordered complex item having no order to replay, when
a mover is absent, or when nothing is left to merge back. Traces are unpronounced. Sibling
accounts of linearization: the selection-induced harmonic order
(`Linearization/Externalization.lean`) and cyclic linearization (`Linearization/Cyclic.lean`).

## Main definitions

* `Minimalist.PlanarSyntacticObject.find?`, `replace`, `move`: Internal Merge on planar objects.
* `Minimalist.Step.replay?`, `Minimalist.Derivation.replay?`, `externalize?`: the replay.
* `Minimalist.Derivation.surfaceTokens`, `surfaceCats`, `surfacePhon`.

## Main results

* `Minimalist.Derivation.replay?_faithful`, `externalize?_faithful`: a successful replay forgets
  to `run` and `final`.
* `Minimalist.Derivation.not_exists_externalize?_eq_comp_final`: the planar object does not
  factor through the derived object.

## References

* [marcolli-chomsky-berwick-2025], §1.12 and §1.13.1 (Lemma 1.13.1)
-/

@[expose] public section

namespace Minimalist

open RoseTree UnorderedTree SyntacticObject

/-! ### Planar leaves and yields -/

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

/-- The pronounced tokens of a planar object, left to right; traces are unpronounced. -/
def PlanarSyntacticObject.yield (p : PlanarSyntacticObject) : List LexicalItem.Token :=
  p.val.leafList.filterMap (Sum.elim id fun _ ↦ none)

/-! ### Internal Merge on planar objects -/

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

end PlanarSyntacticObject

/-- The planar trace a moved object leaves, `SyntacticObject.headTrace` with its order. -/
def SyntacticObject.tracePlanar (s : SyntacticObject)
    (τ : SyntacticObject → Option LexicalItem.Token := selHead) : PlanarSyntacticObject :=
  (τ s).elim PlanarSyntacticObject.trace PlanarSyntacticObject.traceOf

@[simp] theorem SyntacticObject.toSyntacticObject_tracePlanar (s : SyntacticObject)
    (τ : SyntacticObject → Option LexicalItem.Token) :
    (s.tracePlanar τ).toSyntacticObject = s.headTrace τ := by
  unfold tracePlanar headTrace; cases τ s <;> rfl

namespace PlanarSyntacticObject

/-- Internal Merge on a planar object raises the leftmost subtree projecting to `mover` to the
    edge on `side`, leaving the trace of its head under `τ`; `none` if it is absent. -/
def move (side : Edge) (p : PlanarSyntacticObject) (mover : SyntacticObject)
    (τ : SyntacticObject → Option LexicalItem.Token := selHead) : Option PlanarSyntacticObject :=
  (p.find? mover).map fun s ↦ match side with
    | .left => merge s (p.replace mover (mover.tracePlanar τ))
    | .right => merge (p.replace mover (mover.tracePlanar τ)) s

/-- Internal Merge on a planar object forgets to Internal Merge on the syntactic object. -/
theorem toSyntacticObject_move {side : Edge} {p p' : PlanarSyntacticObject}
    {mover : SyntacticObject} {τ : SyntacticObject → Option LexicalItem.Token}
    (h : p.move side mover τ = some p') :
    p'.toSyntacticObject = SyntacticObject.merge
      (deleteAccessible mover p.toSyntacticObject τ) mover := by
  obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.1 h
  cases side
  · rw [toSyntacticObject_merge, toSyntacticObject_find? hs, toSyntacticObject_replace,
      toSyntacticObject_tracePlanar, SyntacticObject.merge_comm]
    rfl
  · rw [toSyntacticObject_merge, toSyntacticObject_find? hs, toSyntacticObject_replace,
      toSyntacticObject_tracePlanar]
    rfl

end PlanarSyntacticObject

/-! ### The replay -/

open Derivation (Cfg)

/-- A step on a planar configuration, `Step.run` with each new daughter on its side, an extraction
    stacking the planar copy it finds; `none` when an externally merged item is not a leaf, the
    mover is absent, or the stack is empty. -/
def Step.replay? (step : Step) (c : Cfg PlanarSyntacticObject)
    (τ : SyntacticObject → Option LexicalItem.Token := selHead) :
    Option (Cfg PlanarSyntacticObject) :=
  match step, c with
  | .em .left item, ⟨p, st⟩ => item.toPlanarLeaf?.map fun i ↦ ⟨i.merge p, st⟩
  | .em .right item, ⟨p, st⟩ => item.toPlanarLeaf?.map fun i ↦ ⟨p.merge i, st⟩
  | .im mover side, ⟨p, st⟩ => (p.move side mover τ).map fun p' ↦ ⟨p', st⟩
  | .extract mover, ⟨p, st⟩ =>
      (p.find? mover).map fun s ↦ ⟨p.replace mover (mover.tracePlanar τ), s :: st⟩
  | .remerge .left, ⟨p, m :: st⟩ => some ⟨m.merge p, st⟩
  | .remerge .right, ⟨p, m :: st⟩ => some ⟨p.merge m, st⟩
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
    rcases hi : item.toPlanarLeaf? with _ | i
    · cases side <;> simp [Step.replay?, hi] at h
    · have hi' := toSyntacticObject_of_toPlanarLeaf? hi
      cases side <;> simp only [Step.replay?, hi, Option.map_some, Option.some.injEq] at h <;>
        subst h <;>
        simp [Cfg.map, Step.run, Step.apply, PlanarSyntacticObject.toSyntacticObject_merge, hi']
  | im mover side =>
    rcases hm : p.move side mover τ with _ | p'
    · simp [Step.replay?, hm] at h
    · simp only [Step.replay?, hm, Option.map_some, Option.some.injEq] at h
      subst h
      simp [Cfg.map, Step.run, Step.apply, PlanarSyntacticObject.toSyntacticObject_move hm]
  | extract mover =>
    rcases hf : p.find? mover with _ | f
    · simp [Step.replay?, hf] at h
    · simp only [Step.replay?, hf, Option.map_some, Option.some.injEq] at h
      subst h
      simp [Cfg.map, Step.run, Step.apply, deleteAccessible,
        PlanarSyntacticObject.toSyntacticObject_find? hf]
  | remerge side =>
    rcases st with _ | ⟨m, st⟩
    · cases side <;> simp [Step.replay?] at h
    · cases side <;> simp only [Step.replay?, Option.some.injEq] at h <;>
        subst h <;>
        simp [Cfg.map, Step.run, Step.apply, PlanarSyntacticObject.toSyntacticObject_merge]

/-- A successful replay of a list of steps forgets to the fold of `Step.run`. -/
private theorem map_of_foldlM_replay? :
    ∀ (steps : List Step) {c p : Cfg PlanarSyntacticObject},
      steps.foldlM (fun c step ↦ step.replay? c τ) c = some p →
      p.map PlanarSyntacticObject.toSyntacticObject
        = steps.foldl (fun c step ↦ step.run c τ) (c.map PlanarSyntacticObject.toSyntacticObject)
  | [], _, _, h => by obtain rfl := Option.some.inj h; rfl
  | step :: steps, _, _, h => by
    obtain ⟨c', hc', h⟩ := Option.bind_eq_some_iff.1 h
    rw [List.foldl_cons, ← Step.map_of_replay? hc', map_of_foldlM_replay? steps h]

/-- A successful replay forgets to the derivation's configuration, the object and every copy on
    the stack, forgetting the order being a morphism of magmas
    ([marcolli-chomsky-berwick-2025] Lemma 1.13.1). -/
theorem Derivation.replay?_faithful (d : Derivation) {c : Cfg PlanarSyntacticObject}
    (h : d.replay? τ = some c) :
    c.map PlanarSyntacticObject.toSyntacticObject = d.run τ := by
  obtain ⟨p, hp, h⟩ := Option.bind_eq_some_iff.1 h
  rw [map_of_foldlM_replay? d.steps h, Derivation.run, Cfg.map, List.map_nil,
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

/-- The planar object is a datum of the derivation, not of the object it derives: merging a
    second leaf on the left and on the right derives one object in two orders. -/
theorem Derivation.not_exists_externalize?_eq_comp_final :
    ¬ ∃ σ : SyntacticObject → Option PlanarSyntacticObject,
      ∀ d : Derivation, d.externalize? = σ d.final := by
  rintro ⟨σ, hσ⟩
  have hfinal : (⟨.leaf ⟨.of .N [], 0⟩, [.em .left (.leaf ⟨.of .N [], 1⟩)]⟩ : Derivation).final =
      (⟨.leaf ⟨.of .N [], 0⟩, [.em .right (.leaf ⟨.of .N [], 1⟩)]⟩ : Derivation).final :=
    merge_comm _ _
  have h := (hσ _).trans ((congrArg σ hfinal).trans (hσ _).symm)
  revert h
  decide

end Minimalist
