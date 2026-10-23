/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Data.List.Monadic
public import Linglib.Syntax.Minimalist.Copy.FormCopy
public import Linglib.Syntax.Minimalist.Copy.Marked
public import Linglib.Syntax.Minimalist.Linearization.Replay

/-!
# Derivations with copies

Under the copy theory Internal Merge merges a copy of the mover and leaves the mover in place. The
replay of a derivation with copies builds its linearized copy object with the lower copies marked,
and contracting them gives the replay with traces. The copy object is a syntactic object, on which
Internal Merge is Merge with one of the object's own terms, the terms of each stage are terms of
every later one, and only the tokens the derivation merges are pronounced.

## Main definitions

* `Minimalist.Step.replayWithCopies?`, `Minimalist.Derivation.replayWithCopies?`: the replay with
  copies.
* `Minimalist.Derivation.copyObject?`: the copy object.

## Main results

* `Minimalist.Derivation.map_contract_replayWithCopies?`: contracting the lower copies gives the
  replay with traces.
* `Minimalist.Step.replayWithCopies?_im_eq_merge`: Internal Merge with copies is MERGE leaving
  copies on the copy object and MERGE leaving traces on its contraction.
* `Minimalist.Step.count_terms_replayWithCopies?_im`: it adds a position to the chain it moves.
* `Minimalist.Step.unmark_replayWithCopies?_im`: Extension and No Tampering.
* `Minimalist.Derivation.copyObject?_append_em`, `copyObject?_append_im`: External Merge merges the
  copy object with an item from outside, Internal Merge with one of its own terms.
* `Minimalist.Derivation.copyRel_copyObject?_append_im`: Internal Merge leaves a copy in the sense
  of Form Copy.
* `Minimalist.Derivation.terms_subset_copyObject?_append`: preservation of terms.
* `Minimalist.Derivation.mem_lexTokens_of_mem_yield_copyObject?`: Inclusiveness.

## TODO

* Steps name their movers in the replay with traces, so a remnant mover carries traces and the copy
  object depends on the trace encoder `τ`; and each lower copy is marked, so deleted, at the step
  that moves it, which leaves no room for externalizations that pronounce several copies. Name
  movers independently of traces and decide deletion at externalization.
* The lower copies as an admissible cut of the copy object, the one its contraction contracts.

## References

* [marcolli-chomsky-berwick-2025], Definitions 1.2.4–1.2.6 and §1.8
-/

@[expose] public section

namespace Minimalist

open RoseTree SyntacticObject

/-! ### The replay with copies -/

open Derivation (Cfg)
open LinearizedSyntacticObject (Marked)

/-- A step on a marked configuration, `Step.replay?` keeping the copies. Internal Merge merges a
copy of the leftmost outermost occurrence of the mover and marks the occurrences it leaves as
lower copies, each with the trace of the mover's head under `τ`; an extraction stacks the copy. -/
def Step.replayWithCopies? (step : Step) (c : Cfg Marked)
    (τ : SyntacticObject → Option LexicalItem.Token := selHead) : Option (Cfg Marked) :=
  match step, c with
  | .em side item, ⟨p, st⟩ => some ⟨p.attach side (.ofLinearized item), st⟩
  | .im mover side, ⟨p, st⟩ =>
      (p.find? mover).map fun s ↦ ⟨(p.mark mover (τ mover)).attach side s, st⟩
  | .extract mover, ⟨p, st⟩ => (p.find? mover).map fun s ↦ ⟨p.mark mover (τ mover), s :: st⟩
  | .remerge side, ⟨p, m :: st⟩ => some ⟨p.attach side m, st⟩
  | .remerge _, ⟨_, []⟩ => none

/-- The derivation's marked configuration under the trace encoder `τ`, `none` exactly when
`Derivation.replay?` is. -/
def Derivation.replayWithCopies? (d : Derivation)
    (τ : SyntacticObject → Option LexicalItem.Token := selHead) : Option (Cfg Marked) :=
  d.initial.toLinearizedLeaf?.bind fun p ↦
    d.steps.foldlM (fun c step ↦ step.replayWithCopies? c τ) ⟨.ofLinearized p, []⟩

variable {τ : SyntacticObject → Option LexicalItem.Token}

/-- Contracting the copies of a step with copies gives the step with traces. -/
theorem Step.map_contract_replayWithCopies? (step : Step) (c : Cfg Marked) :
    (step.replayWithCopies? c τ).map (Cfg.map Marked.contract) =
      step.replay? (c.map Marked.contract) τ := by
  obtain ⟨p, st⟩ := c
  cases step with
  | em side item => simp [Step.replayWithCopies?, Step.replay?, Cfg.map]
  | im mover side =>
    simp only [Step.replayWithCopies?, Step.replay?, Cfg.map]
    rw [← Marked.map_contract_find?, Option.map_map, Option.map_map]
    congr 1
    funext s
    simp [Cfg.map, Marked.contract_mark]
  | extract mover =>
    simp only [Step.replayWithCopies?, Step.replay?, Cfg.map]
    rw [← Marked.map_contract_find?, Option.map_map, Option.map_map]
    congr 1
    funext s
    simp [Cfg.map, Marked.contract_mark]
  | remerge side =>
    rcases st with _ | ⟨m, st⟩ <;> simp [Step.replayWithCopies?, Step.replay?, Cfg.map]

/-- Contracting the copies of the replay with copies gives the replay with traces. -/
theorem Derivation.map_contract_replayWithCopies? (d : Derivation) :
    (d.replayWithCopies? τ).map (Cfg.map Marked.contract) = d.replay? τ := by
  rw [replayWithCopies?, replay?, Option.map_bind]
  congr 1
  funext p
  rw [Function.comp_apply, List.map_foldlM (g := fun c (step : Step) ↦ step.replay? c τ)
    (fun c step ↦ Step.map_contract_replayWithCopies? step c)]
  simp [Cfg.map]

theorem Derivation.externalize?_eq_map_replayWithCopies? (d : Derivation) :
    d.externalize? τ = (d.replayWithCopies? τ).map (·.current.contract) := by
  rw [externalize?, ← d.map_contract_replayWithCopies?, Option.map_map]
  rfl

theorem Derivation.isSome_replayWithCopies? (d : Derivation) :
    (d.replayWithCopies? τ).isSome = (d.replay? τ).isSome := by
  rw [← d.map_contract_replayWithCopies?, Option.isSome_map]

/-- Internal Merge with copies merges a copy of a subtree of the copy object onto the object
unchanged: Extension and No Tampering. -/
theorem Step.unmark_replayWithCopies?_im {mover : SyntacticObject} {side : Edge}
    {c c' : Cfg Marked} (h : (Step.im mover side).replayWithCopies? c τ = some c') :
    ∃ s : Marked, IsSubtree s.unmark.val c.current.unmark.val ∧
      c'.current.unmark = c.current.unmark.attach side s.unmark := by
  obtain ⟨p, st⟩ := c
  obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.1 h
  refine ⟨s, ?_, by simp⟩
  obtain ⟨r, hr, -, rfl⟩ := Option.pmap_eq_some_iff.1 hs
  exact (isSubtree_of_mem_subtreesUntil hr).map _

/-- Internal Merge with copies is MERGE leaving copies of a copy of the mover on the copy object,
and MERGE leaving traces of the mover on the contraction. -/
theorem Step.replayWithCopies?_im_eq_merge {mover : SyntacticObject} {side : Edge}
    {c c' : Cfg Marked} (h : (Step.im mover side).replayWithCopies? c τ = some c')
    (hne : c.current.contract.toSyntacticObject ≠ mover) :
    ∃ s : Marked, s.contract.toSyntacticObject = mover ∧
      ({c'.current.unmark.toSyntacticObject} : Workspace) =
        ({c.current.unmark.toSyntacticObject} : Workspace).merge s.unmark.toSyntacticObject
          c.current.unmark.toSyntacticObject ∧
      ({c'.current.contract.toSyntacticObject} : Workspace) =
        ({c.current.contract.toSyntacticObject} : Workspace).mergeWith (·.headTrace τ) mover
          c.current.contract.toSyntacticObject := by
  obtain ⟨p, st⟩ := c
  obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.1 h
  have hfind : p.contract.find? mover = some s.contract := by
    rw [← Marked.map_contract_find?, hs]
    rfl
  have hsm := LinearizedSyntacticObject.toSyntacticObject_find? hfind
  have hmc := LinearizedSyntacticObject.isSome_find?_iff.1 (by rw [hfind]; rfl)
  have hW := Workspace.mergeWith_internal (leave := (·.headTrace τ)) (W := 0) hmc hne (by simp)
  rw [add_zero, zero_add] at hW
  refine ⟨s, hsm, ?_, ?_⟩
  · simp [Workspace.singleton_merge]
  · simp [hW, Marked.contract_mark, hsm]

/-! ### The copy object -/

/-- The derivation's copy object, the syntactic object with every copy in place and neither order
nor marks: the form the semantic interface receives. -/
def Derivation.copyObject? (d : Derivation)
    (τ : SyntacticObject → Option LexicalItem.Token := selHead) : Option SyntacticObject :=
  (d.replayWithCopies? τ).map (·.current.unmark.toSyntacticObject)

theorem Derivation.replayWithCopies?_append (d : Derivation) (steps : List Step) :
    (d.append steps).replayWithCopies? τ = (d.replayWithCopies? τ).bind fun c ↦
      steps.foldlM (fun c step ↦ step.replayWithCopies? c τ) c := by
  simp only [replayWithCopies?, append, List.foldlM_append, Option.bind_assoc]
  rfl

theorem Derivation.replayWithCopies?_append_singleton (d : Derivation) (step : Step) :
    (d.append [step]).replayWithCopies? = d.replayWithCopies?.bind (step.replayWithCopies? ·) := by
  rw [replayWithCopies?_append]
  congr 1
  funext c
  simp only [List.foldlM_cons, List.foldlM_nil]
  cases step.replayWithCopies? c <;> rfl

theorem Step.toSyntacticObject_replayWithCopies?_em {side : Edge}
    {item : LinearizedSyntacticObject} {c c' : Cfg Marked}
    (h : (Step.em side item).replayWithCopies? c τ = some c') :
    c'.current.unmark.toSyntacticObject = merge item c.current.unmark.toSyntacticObject := by
  obtain ⟨p, st⟩ := c
  obtain rfl := Option.some.inj h
  simp

theorem Step.toSyntacticObject_replayWithCopies?_im {mover : SyntacticObject} {side : Edge}
    {c c' : Cfg Marked} (h : (Step.im mover side).replayWithCopies? c τ = some c') :
    ∃ u ∈ c.current.unmark.toSyntacticObject.terms,
      c'.current.unmark.toSyntacticObject = merge u c.current.unmark.toSyntacticObject := by
  obtain ⟨s, hs, he⟩ := Step.unmark_replayWithCopies?_im h
  refine ⟨s.unmark.toSyntacticObject, ?_,
    by rw [he, LinearizedSyntacticObject.toSyntacticObject_attach]⟩
  exact LinearizedSyntacticObject.mem_terms_toSyntacticObject.2 ⟨_, mem_subtrees.2 hs, rfl⟩

/-- Internal Merge with copies adds a position to the chain of the copy it merges
(`LinearizedSyntacticObject.card_chainRel`). -/
theorem Step.count_terms_replayWithCopies?_im {mover : SyntacticObject} {side : Edge}
    {c c' : Cfg Marked} (h : (Step.im mover side).replayWithCopies? c τ = some c') :
    ∃ u ∈ c.current.unmark.toSyntacticObject.terms,
      c'.current.unmark.toSyntacticObject.terms.count u =
        c.current.unmark.toSyntacticObject.terms.count u + 1 := by
  obtain ⟨u, hu, he⟩ := Step.toSyntacticObject_replayWithCopies?_im h
  exact ⟨u, hu, by rw [he, count_terms_merge_left]⟩

theorem Step.mem_terms_replayWithCopies? {step : Step} {c c' : Cfg Marked}
    (h : step.replayWithCopies? c τ = some c') :
    c.current.unmark.toSyntacticObject ∈ c'.current.unmark.toSyntacticObject.terms := by
  obtain ⟨p, st⟩ := c
  cases step with
  | em side item =>
    rw [Step.toSyntacticObject_replayWithCopies?_em h]
    exact SyntacticObject.mem_terms_merge_right _ _
  | im mover side =>
    obtain ⟨u, -, hu⟩ := Step.toSyntacticObject_replayWithCopies?_im h
    rw [hu]
    exact SyntacticObject.mem_terms_merge_right _ _
  | extract mover =>
    obtain ⟨s, -, rfl⟩ := Option.map_eq_some_iff.1 h
    simp only [Marked.unmark_mark]
    exact self_mem_terms _
  | remerge side =>
    rcases st with _ | ⟨m, st⟩
    · cases h
    · obtain rfl := Option.some.inj h
      simp only [Marked.unmark_attach, LinearizedSyntacticObject.toSyntacticObject_attach]
      exact SyntacticObject.mem_terms_merge_right _ _

private theorem mem_terms_foldlM_replayWithCopies? :
    ∀ {steps : List Step} {c c' : Cfg Marked},
      steps.foldlM (fun c step ↦ step.replayWithCopies? c τ) c = some c' →
        c.current.unmark.toSyntacticObject ∈ c'.current.unmark.toSyntacticObject.terms
  | [], _, _, h => by obtain rfl := Option.some.inj h; exact self_mem_terms _
  | step :: steps, _, _, h => by
    obtain ⟨c₁, h₁, h⟩ := Option.bind_eq_some_iff.1 h
    exact terms_subset_terms (mem_terms.1 (mem_terms_foldlM_replayWithCopies? h))
      (Step.mem_terms_replayWithCopies? h₁)

/-- Preservation of terms: the terms of the copy object at a stage are terms of the copy object at
every later stage. -/
theorem Derivation.terms_subset_copyObject?_append {d : Derivation} {steps : List Step}
    {C' : SyntacticObject} (h : (d.append steps).copyObject? τ = some C') :
    ∃ C ∈ d.copyObject? τ, C.terms ⊆ C'.terms := by
  obtain ⟨c', hc', rfl⟩ := Option.map_eq_some_iff.1 h
  rw [replayWithCopies?_append] at hc'
  obtain ⟨c, hc, hc'⟩ := Option.bind_eq_some_iff.1 hc'
  exact ⟨_, Option.map_eq_some_iff.2 ⟨c, hc, rfl⟩,
    terms_subset_terms (mem_terms.1 (mem_terms_foldlM_replayWithCopies? hc'))⟩

/-- External Merge merges the copy object with the item, built outside. -/
theorem Derivation.copyObject?_append_em (d : Derivation) (side : Edge)
    (item : LinearizedSyntacticObject) :
    (d.append [.em side item]).copyObject? τ = (d.copyObject? τ).map (merge item) := by
  simp only [copyObject?, replayWithCopies?_append]
  cases d.replayWithCopies? τ <;> simp [Step.replayWithCopies?]

/-- Internal Merge merges the copy object with one of its own terms, so Internal and External
Merge are one operation, differing in where its object comes from. -/
theorem Derivation.copyObject?_append_im {d : Derivation} {mover : SyntacticObject} {side : Edge}
    {C' : SyntacticObject} (h : (d.append [.im mover side]).copyObject? τ = some C') :
    ∃ C ∈ d.copyObject? τ, ∃ u ∈ C.terms, C' = merge u C := by
  obtain ⟨c', hc', rfl⟩ := Option.map_eq_some_iff.1 h
  rw [replayWithCopies?_append] at hc'
  obtain ⟨c, hc, hc'⟩ := Option.bind_eq_some_iff.1 hc'
  exact ⟨_, Option.map_eq_some_iff.2 ⟨c, hc, rfl⟩,
    Step.toSyntacticObject_replayWithCopies?_im (by simpa using hc')⟩

/-- The occurrence Internal Merge leaves is a copy of the one it merges, in the sense of Form Copy,
unless the whole object moves. -/
theorem Derivation.copyRel_copyObject?_append_im {d : Derivation} {mover : SyntacticObject}
    {side : Edge} {C' : SyntacticObject} (h : (d.append [.im mover side]).copyObject? τ = some C') :
    ∃ C ∈ d.copyObject? τ, ∃ u ∈ C.terms, C' = merge u C ∧ ((u, u) ∈ C'.copyRel ↔ u ≠ C) := by
  obtain ⟨C, hC, u, hu, rfl⟩ := copyObject?_append_im h
  exact ⟨C, hC, u, hu, rfl, self_mem_copyRel_merge_iff hu⟩

/-! ### Inclusiveness -/

private theorem Step.mem_yield_map_replayWithCopies? {step : Step} {c c' : Cfg Marked}
    (h : step.replayWithCopies? c τ = some c') {tok : LexicalItem.Token}
    (ht : tok ∈ (c'.map (·.unmark.toSyntacticObject)).yield) :
    tok ∈ (c.map (·.unmark.toSyntacticObject)).yield ∨
      tok ∈ (step.items.map SyntacticObject.yield).sum := by
  obtain ⟨p, st⟩ := c
  cases step with
  | em side item =>
    obtain rfl := Option.some.inj h
    simp only [Cfg.yield_map, Marked.unmark_attach, Marked.unmark_ofLinearized,
      LinearizedSyntacticObject.yield_attach, Step.items, Multiset.map_singleton,
      Multiset.sum_singleton, Multiset.mem_add] at ht ⊢
    tauto
  | im mover side =>
    obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.1 h
    have hle := SyntacticObject.yield_le_of_mem_terms (Marked.mem_terms_of_find? hs)
    simp only [Cfg.yield_map, Marked.unmark_attach, Marked.unmark_mark,
      LinearizedSyntacticObject.yield_attach, Multiset.mem_add] at ht ⊢
    rcases ht with (ht | ht) | ht
    · exact .inl (.inl (Multiset.mem_of_le hle ht))
    · exact .inl (.inl ht)
    · exact .inl (.inr ht)
  | extract mover =>
    obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.1 h
    have hle := SyntacticObject.yield_le_of_mem_terms (Marked.mem_terms_of_find? hs)
    simp only [Cfg.yield_map, Marked.unmark_mark, List.map_cons, List.sum_cons,
      Multiset.mem_add] at ht ⊢
    rcases ht with ht | ht | ht
    · exact .inl (.inl ht)
    · exact .inl (.inl (Multiset.mem_of_le hle ht))
    · exact .inl (.inr ht)
  | remerge side =>
    rcases st with _ | ⟨m, st⟩
    · cases h
    · obtain rfl := Option.some.inj h
      simp only [Cfg.yield_map, Marked.unmark_attach, LinearizedSyntacticObject.yield_attach,
        List.map_cons, List.sum_cons, Multiset.mem_add] at ht ⊢
      tauto

private theorem mem_yield_map_foldlM_replayWithCopies? : ∀ {steps : List Step} {c c' : Cfg Marked},
    steps.foldlM (fun c step ↦ step.replayWithCopies? c τ) c = some c' →
    ∀ tok ∈ (c'.map (·.unmark.toSyntacticObject)).yield,
      tok ∈ (c.map (·.unmark.toSyntacticObject)).yield ∨
        tok ∈ ((Step.itemsList steps).map SyntacticObject.yield).sum
  | [], _, _, h, _, ht => by obtain rfl := Option.some.inj h; exact .inl ht
  | step :: steps, _, _, h, tok, ht => by
    obtain ⟨c₁, h₁, h⟩ := Option.bind_eq_some_iff.1 h
    rw [Step.itemsList_cons, Multiset.map_add, Multiset.sum_add, Multiset.mem_add]
    rcases mem_yield_map_foldlM_replayWithCopies? h tok ht with ht | ht
    · rcases Step.mem_yield_map_replayWithCopies? h₁ ht with ht | ht
      · exact .inl ht
      · exact .inr (.inl ht)
    · exact .inr (.inr ht)

/-- Inclusiveness: the copy object pronounces only tokens the derivation merges. -/
theorem Derivation.mem_lexTokens_of_mem_yield_copyObject? {d : Derivation} {C : SyntacticObject}
    {tok : LexicalItem.Token} (h : d.copyObject? τ = some C) (ht : tok ∈ C.yield) :
    tok ∈ d.lexTokens := by
  obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨p, hp, hc⟩ := Option.bind_eq_some_iff.1 hc
  rcases mem_yield_map_foldlM_replayWithCopies? hc tok (Multiset.mem_add.2 (.inl ht)) with ht | ht
  · simpa [Cfg.yield_map, lexTokens, SyntacticObject.toSyntacticObject_of_toLinearizedLeaf? hp]
      using Multiset.mem_add.2 (.inl ht)
  · exact Multiset.mem_add.2 (.inr ht)

end Minimalist
