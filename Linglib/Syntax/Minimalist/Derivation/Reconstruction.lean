/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Copy.Replay
public import Linglib.Syntax.Minimalist.Linearization.ChainReduction
public import Linglib.Syntax.Minimalist.Linearization.Replay
public import Linglib.Syntax.Minimalist.SyntacticObject.Term

/-!
# Binding at a stage of the derivation

Movement reorders c-command, and binding may be evaluated before or after it: reconstruction.
`CCommandsAt d n x y` says that `x` c-commands `y` in the object the replay of `d` reaches after
`n` steps, which by faithfulness is `d.stageAt n` itself; a stage whose replay fails c-commands
nothing. `BindsAtSurface` evaluates binding at the last stage and `BindsAtSomeStage` at any, the
derivational binding condition under which a sentence is well formed as soon as some stage
satisfies it. `BindsAtLF` evaluates binding at the copy object, where some copy of each must stand
in the relation, and in a derivation of Merge steps that merges no token twice the two coincide.

## Main definitions

* `Minimalist.Derivation.CCommandsAt`, `BindsAtSurface`, `BindsAtSomeStage`, `BindsAtLF`

## Main results

* `Minimalist.Derivation.CCommandsAt.cCommands_stageAt`: the predicate speaks
  of the derivation's own stage.
* `Minimalist.Derivation.cCommandsAt_append_of_le`, `BindsAtSomeStage.append`.
* `Minimalist.Derivation.BindsAtSomeStage.bindsAtLF`, `BindsAtLF.bindsAtSomeStage`: binding at
  some stage is binding at the copy object, and conversely in a derivation of Merge steps that
  merges no token twice and moves no trace.
* `Minimalist.Derivation.bindsAtSomeStage_iff_bindsAtLF`: derivational binding is binding at
  the copy object.

## References

* [cole-hermon-2008], fn. 28
* [chomsky-1995]
-/

@[expose] public section

namespace Minimalist.Derivation

open SyntacticObject
open PlanarSyntacticObject (Marked)

variable {d : Derivation} {steps : List Step} {n : Nat} {x y : SyntacticObject}

/-- `x` c-commands `y` at stage `n` of `d`: in the ordered object the replay reaches after `n`
steps. -/
def CCommandsAt (d : Derivation) (n : Nat) (x y : SyntacticObject) : Prop :=
  ∃ p ∈ (d.take n).externalize?, CCommands p x y

instance (d : Derivation) (n : Nat) (x y : SyntacticObject) :
    Decidable (d.CCommandsAt n x y) := by
  unfold CCommandsAt; infer_instance

/-- The stage the predicate looks at is the derivation's own. -/
theorem CCommandsAt.cCommands_stageAt (h : d.CCommandsAt n x y) :
    CCommands (d.stageAt n) x y :=
  let ⟨_, hp, hc⟩ := h
  d.externalize?_take_faithful n hp ▸ hc

/-- The early stages of an extended derivation are the original's. -/
theorem cCommandsAt_append_of_le (h : n ≤ d.length) :
    (d.append steps).CCommandsAt n x y ↔ d.CCommandsAt n x y := by
  rw [CCommandsAt, CCommandsAt, take_append_of_le h]

/-- Surface binding: c-command at the last stage. -/
abbrev BindsAtSurface (d : Derivation) (x y : SyntacticObject) : Prop :=
  d.CCommandsAt d.length x y

/-- Derivational binding: c-command at some stage. -/
def BindsAtSomeStage (d : Derivation) (x y : SyntacticObject) : Prop :=
  ∃ n ≤ d.length, d.CCommandsAt n x y

instance (d : Derivation) (x y : SyntacticObject) : Decidable (d.BindsAtSomeStage x y) := by
  unfold BindsAtSomeStage; infer_instance

/-- Binding at the surface is binding at some stage. -/
theorem BindsAtSurface.bindsAtSomeStage (h : d.BindsAtSurface x y) : d.BindsAtSomeStage x y :=
  ⟨d.length, le_rfl, h⟩

/-- Binding at some stage is monotone under extension. -/
theorem BindsAtSomeStage.append (h : d.BindsAtSomeStage x y) :
    (d.append steps).BindsAtSomeStage x y :=
  let ⟨n, hn, hc⟩ := h
  ⟨n, by rw [length_append]; exact hn.trans (Nat.le_add_right _ _),
    (cCommandsAt_append_of_le hn).2 hc⟩

/-! ### Binding at the copy object -/

/-- Binding at the copy object, binding at LF under the copy theory of movement
([chomsky-1995]): some copy of `x` c-commands some copy of `y` in the object with every copy in
place. -/
def BindsAtLF (d : Derivation) (x y : SyntacticObject) : Prop :=
  ∃ C ∈ d.copyObject?, CCommands C x y

instance (d : Derivation) (x y : SyntacticObject) : Decidable (d.BindsAtLF x y) := by
  unfold BindsAtLF; infer_instance

/-- Binding at some stage is binding at the copy object, where every stage survives. -/
theorem BindsAtSomeStage.bindsAtLF {x y : LexicalItem.Token} (hxy : x ≠ y)
    (hd : d.replay?.isSome) (h : d.BindsAtSomeStage ↑x ↑y) : d.BindsAtLF ↑x ↑y := by
  obtain ⟨n, -, p, hp, hc⟩ := h
  rw [Option.mem_def, externalize?_eq_map_replayWithCopies?] at hp
  obtain ⟨c, hc', rfl⟩ := Option.map_eq_some_iff.1 hp
  have h1 := Marked.cCommands_unmark_of_cCommands_contract hxy hc
  obtain ⟨C', hC'⟩ := Option.isSome_iff_exists.1 (show (d.copyObject?).isSome by
    rw [copyObject?, Option.isSome_map, isSome_replayWithCopies?]; exact hd)
  have hsplit : (d.take n).append (d.steps.drop n) = d := by
    show (⟨d.initial, d.steps.take n ++ d.steps.drop n⟩ : Derivation) = d
    rw [List.take_append_drop]
  obtain ⟨C, hC, hsub⟩ := terms_subset_copyObject?_append (by rw [hsplit]; exact hC')
  rw [Option.mem_def, copyObject?, hc', Option.map_some] at hC
  obtain rfl := Option.some.inj hC
  exact ⟨C', hC', h1.mono hsub⟩

/-- Binding at the copy object is binding at some stage, in a derivation of Merge steps that moves
no trace and merges no token twice: two copies stand in a c-command relation only if, at the step
that merged the higher one, its sister held the other pronounced. -/
theorem BindsAtLF.bindsAtSomeStage {x y : LexicalItem.Token} (hxy : x ≠ y)
    (hd : d.lexTokens.Nodup) (hm : ∀ step ∈ d.steps, step.IsMerge)
    (hmv : ∀ step ∈ d.steps, ∀ m ∈ step.mover?, m.val.value.isLeft)
    (h : d.BindsAtLF ↑x ↑y) : d.BindsAtSomeStage ↑x ↑y := by
  obtain ⟨init, steps⟩ := d
  induction steps using List.reverseRecOn with
  | nil =>
    exfalso
    obtain ⟨C, hC, z, -, hs, -⟩ := h
    simp only [Option.mem_def, copyObject?, replayWithCopies?, List.foldlM_nil,
      Option.map_bind] at hC
    obtain ⟨p, hp, hC⟩ := Option.bind_eq_some_iff.1 hC
    obtain rfl := Option.some.inj hC
    exact not_sisters_of_toPlanarLeaf? hp
      (by simpa [SyntacticObject.toSyntacticObject_of_toPlanarLeaf? hp] using hs)
  | append_singleton ss s ih =>
    set d : Derivation := ⟨init, ss⟩
    change (d.append [s]).lexTokens.Nodup at hd
    change (d.append [s]).BindsAtLF ↑x ↑y at h
    change (d.append [s]).BindsAtSomeStage ↑x ↑y
    have hm' : ∀ t ∈ d.steps, t.IsMerge := fun t ht ↦ hm t (List.mem_append_left _ ht)
    have hmv' : ∀ t ∈ d.steps, ∀ m ∈ t.mover?, m.val.value.isLeft :=
      fun t ht ↦ hmv t (List.mem_append_left _ ht)
    have hs : s.IsMerge := hm s (List.mem_append_right _ (List.mem_singleton_self _))
    have hd0 : d.lexTokens.Nodup :=
      Multiset.nodup_of_le (by rw [lexTokens_append]; exact Multiset.le_add_right _ _) hd
    have ih' := ih hd0 hm' hmv'
    obtain ⟨C', hC', hcc⟩ := h
    rw [Option.mem_def, copyObject?, replayWithCopies?_append_singleton] at hC'
    obtain ⟨c', hc', rfl⟩ := Option.map_eq_some_iff.1 hC'
    obtain ⟨c, hc, hstep⟩ := Option.bind_eq_some_iff.1 hc'
    have hdC : d.copyObject? = some c.current.unmark.toSyntacticObject := by
      rw [copyObject?, hc]; rfl
    have hcT : d.replay? = some (c.map Marked.contract) := by
      rw [← map_contract_replayWithCopies?, hc]; rfl
    have hT : c.current.contract.toSyntacticObject.yield = d.lexTokens := by
      have := d.yield_replay? hd0 hcT
      rwa [Derivation.Cfg.yield_map, stack_eq_nil_of_replay? hm' hcT, List.map_nil, List.sum_nil,
        add_zero] at this
    have hpron : ∀ t : LexicalItem.Token, leaf t ∈ c.current.unmark.toSyntacticObject.terms →
        t ∈ c.current.contract.toSyntacticObject.yield := fun t ht ↦
      hT ▸ mem_lexTokens_of_mem_yield_copyObject? hdC (mem_yield_iff.2 ht)
    have hfinal : ∀ cT', (d.append [s]).replay? = some cT' →
        CCommands cT'.current.toSyntacticObject ↑x ↑y → (d.append [s]).BindsAtSomeStage ↑x ↑y :=
      fun cT' h1 h2 ↦ ⟨(d.append [s]).length, le_rfl, cT'.current,
        by rw [take_length, externalize?, h1]; rfl, h2⟩
    have hne : ∀ T : SyntacticObject, leaf y ∈ T.terms → (↑x : SyntacticObject) ≠ T :=
      fun T hy he ↦ by
        rw [← he, terms_leaf, Multiset.mem_singleton, leaf_inj] at hy
        exact hxy hy.symm
    obtain ⟨z, -, hsis, hzy⟩ := hcc
    cases s with
    | extract mover => exact hs.elim
    | remerge side => exact hs.elim
    | em side item =>
      obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.1 hstep
      have hitem := SyntacticObject.toSyntacticObject_of_toPlanarLeaf? hi
      have hreplay : (d.append [.em side item]).replay? =
          some ⟨c.current.contract.attach side i, c.stack.map Marked.contract⟩ := by
        rw [replay?_append_singleton, hcT]
        simp [Step.replay?, Cfg.map, hi]
      simp only [Marked.unmark_attach,
        Marked.unmark_ofPlanar, PlanarSyntacticObject.toSyntacticObject_attach,
        hitem] at hsis
      rcases Sisters.of_merge hsis with hl | hr | ⟨hx, rfl⟩ | ⟨hx, rfl⟩
      · exact absurd hl (not_sisters_of_toPlanarLeaf? hi)
      · exact (ih' ⟨_, hdC, z, hr.mem_right, hr, hzy⟩).append
      · have hy := mem_yield_iff.1 (hpron y (mem_terms.2 hzy))
        refine hfinal _ hreplay ?_
        rw [PlanarSyntacticObject.toSyntacticObject_attach, hitem, ← hx]
        exact cCommands_merge_left (hne _ hy) hy
      · have hyi : z = leaf y := by
          have := mem_terms.2 hzy
          rcases z.exists_form with ⟨tok, rfl⟩ | rfl | ⟨tok, rfl⟩ | ⟨l, r, rfl⟩
          · rw [terms_leaf, Multiset.mem_singleton] at this; exact this.symm
          · simp at this
          · simp at this
          · simp [toPlanarLeaf?, merge_val] at hi
        have hTx := Marked.contract_eq_leaf_of_unmark_eq_leaf hx.symm
          (hpron x (hx ▸ self_mem_terms _))
        refine hfinal _ hreplay ?_
        rw [PlanarSyntacticObject.toSyntacticObject_attach, hitem, hTx, hyi, merge_comm]
        exact cCommands_merge_left (by simpa using hxy) (self_mem_terms _)
    | im mover side =>
      obtain ⟨sM, hsM, rfl⟩ := Option.map_eq_some_iff.1 hstep
      have hu := Marked.mem_terms_of_find? hsM
      have hsT : c.current.contract.find? mover = some sM.contract := by
        rw [← Marked.map_contract_find?, hsM]; rfl
      have hreplay : (d.append [.im mover side]).replay? =
          some ⟨(c.current.contract.replace mover (mover.tracePlanar selHead)).attach side
            sM.contract, c.stack.map Marked.contract⟩ := by
        rw [replay?_append_singleton, hcT]
        simp [Step.replay?, Cfg.map, hsT]
      simp only [Marked.unmark_attach,
        Marked.unmark_mark, PlanarSyntacticObject.toSyntacticObject_attach]
        at hsis
      rcases Sisters.of_merge hsis with hl | hr | ⟨hx, rfl⟩ | ⟨hx, rfl⟩
      · exact (ih' ⟨_, hdC, (show CCommands _ _ _ from ⟨z, hl.mem_right, hl, hzy⟩).mono
          (terms_subset_terms (mem_terms.1 hu))⟩).append
      · exact (ih' ⟨_, hdC, z, hr.mem_right, hr, hzy⟩).append
      · have hmover : mover = leaf x := Marked.eq_leaf_of_find? hsM
          (hmv _ (List.mem_append_right _ (List.mem_singleton_self _)) mover rfl) hx.symm
        subst hmover
        have hy := hpron y (mem_terms.2 hzy)
        have hrep := PlanarSyntacticObject.yield_replace_add_yield selHead (hT ▸ hd0) hsT
        rw [PlanarSyntacticObject.toSyntacticObject_find? hsT, yield_leaf] at hrep
        rw [← hrep, Multiset.mem_add, Multiset.mem_singleton] at hy
        have hy' := mem_yield_iff.1 (hy.resolve_right hxy.symm)
        refine hfinal _ hreplay ?_
        rw [PlanarSyntacticObject.toSyntacticObject_attach,
          PlanarSyntacticObject.toSyntacticObject_find? hsT]
        exact cCommands_merge_left (hne _ hy') hy'
      · rw [← hx, terms_leaf, Multiset.mem_singleton] at hu
        rw [hu] at hzy
        have := mem_terms.2 hzy
        rw [terms_leaf, Multiset.mem_singleton, leaf_inj] at this
        exact absurd this.symm hxy

/-- Derivational binding is binding at the copy object: in a derivation of Merge steps that moves
no trace and merges no token twice, `x` c-commands `y` at some stage exactly when some copy of `x`
c-commands some copy of `y` in the object with every copy in place. -/
theorem bindsAtSomeStage_iff_bindsAtLF {x y : LexicalItem.Token} (hxy : x ≠ y)
    (hd : d.lexTokens.Nodup) (hm : ∀ step ∈ d.steps, step.IsMerge)
    (hmv : ∀ step ∈ d.steps, ∀ m ∈ step.mover?, m.val.value.isLeft) (hr : d.replay?.isSome) :
    d.BindsAtSomeStage ↑x ↑y ↔ d.BindsAtLF ↑x ↑y :=
  ⟨fun h ↦ h.bindsAtLF hxy hr, fun h ↦ h.bindsAtSomeStage hxy hd hm hmv⟩

end Minimalist.Derivation
