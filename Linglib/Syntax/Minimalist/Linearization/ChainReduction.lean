/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Linearization.Replay

/-!
# Chain reduction

Externalization pronounces a moved constituent once and deletes its lower copies. The replay with
traces deletes every lower copy at the step that moves it, so a derivation that merges no token
twice and leaves no extracted copy on the stack pronounces each token it merges exactly once. That
one copy is pronounced is the replay's choice: chain reduction explains why lower copies go
unpronounced, and languages that spell out several copies of a wh-phrase show it is a choice of
the externalization, not a law of the copy theory.

## Main results

* `Minimalist.Derivation.yield_replay?`: the pronounced tokens of a configuration are the merged
  tokens.
* `Minimalist.Derivation.coe_surfaceTokens`: each merged token is pronounced exactly once.
* `Minimalist.Derivation.mem_yield_of_mem_lexTokens`: a derivation of Merge steps pronounces every
  token it merges.

## References

* [nunes-2004]
-/

@[expose] public section

namespace Minimalist

open RoseTree SyntacticObject
open Derivation (Cfg)

variable {τ : SyntacticObject → Option LexicalItem.Token}

/-- The pronounced tokens of a configuration, its object's and those of the copies on its stack. -/
private def cfgYield (c : Cfg PlanarSyntacticObject) : Multiset LexicalItem.Token :=
  c.current.toSyntacticObject.yield + (c.stack.map (·.toSyntacticObject.yield)).sum

private theorem Step.cfgYield_replay? {step : Step} {c c' : Cfg PlanarSyntacticObject}
    (hc : (cfgYield c + (step.items.map SyntacticObject.yield).sum).Nodup)
    (h : step.replay? c τ = some c') :
    cfgYield c' = cfgYield c + (step.items.map SyntacticObject.yield).sum := by
  obtain ⟨p, st⟩ := c
  have hp : p.toSyntacticObject.yield.Nodup :=
    Multiset.nodup_of_le ((Multiset.le_add_right _ _).trans (Multiset.le_add_right _ _)) hc
  cases step with
  | em side item =>
    obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.1 h
    rw [← SyntacticObject.toSyntacticObject_of_toPlanarLeaf? hi]
    simp only [cfgYield, Step.items, Multiset.map_singleton, Multiset.sum_singleton,
      PlanarSyntacticObject.yield_attach]
    abel
  | im mover side =>
    obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.1 h
    simp only [cfgYield, Step.items, Multiset.map_zero, Multiset.sum_zero, add_zero,
      PlanarSyntacticObject.yield_attach]
    rw [add_comm s.toSyntacticObject.yield, PlanarSyntacticObject.yield_replace_add_yield τ hp hs]
  | extract mover =>
    obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.1 h
    simp only [cfgYield, Step.items, Multiset.map_zero, Multiset.sum_zero, add_zero, List.map_cons,
      List.sum_cons]
    rw [← add_assoc, PlanarSyntacticObject.yield_replace_add_yield τ hp hs]
  | remerge side =>
    rcases st with _ | ⟨m, st⟩
    · cases h
    · obtain rfl := Option.some.inj h
      simp only [cfgYield, Step.items, Multiset.map_zero, Multiset.sum_zero, add_zero,
        List.map_cons, List.sum_cons, PlanarSyntacticObject.yield_attach]
      abel

private theorem cfgYield_foldlM_replay? : ∀ {steps : List Step} {c c' : Cfg PlanarSyntacticObject},
    steps.foldlM (fun c step ↦ step.replay? c τ) c = some c' →
    (cfgYield c + ((Step.itemsList steps).map SyntacticObject.yield).sum).Nodup →
    cfgYield c' = cfgYield c + ((Step.itemsList steps).map SyntacticObject.yield).sum
  | [], _, _, h, _ => by obtain rfl := Option.some.inj h; simp
  | step :: steps, c, _, h, hn => by
    obtain ⟨c₁, h₁, h⟩ := Option.bind_eq_some_iff.1 h
    rw [Step.itemsList_cons, Multiset.map_add, Multiset.sum_add, ← add_assoc] at hn ⊢
    have e₁ := Step.cfgYield_replay? (Multiset.nodup_of_le (Multiset.le_add_right _ _) hn) h₁
    rw [← e₁] at hn ⊢
    exact cfgYield_foldlM_replay? h hn

/-- When no token is merged twice, a derivation pronounces each token it merges once, in its
object or in a copy left on the stack, however many copies its movements leave. -/
theorem Derivation.yield_replay? {d : Derivation} {c : Cfg PlanarSyntacticObject}
    (hd : d.lexTokens.Nodup) (h : d.replay? τ = some c) :
    c.current.toSyntacticObject.yield + (c.stack.map (·.toSyntacticObject.yield)).sum =
      d.lexTokens := by
  obtain ⟨p, hp, h⟩ := Option.bind_eq_some_iff.1 h
  have h0 : cfgYield ⟨p, []⟩ = d.initial.yield := by
    simp [cfgYield, SyntacticObject.toSyntacticObject_of_toPlanarLeaf? hp]
  have := cfgYield_foldlM_replay? h (by rwa [h0])
  rwa [h0] at this

/-- When no token is merged twice and no extracted copy is left on the stack, the externalized
object pronounces every token the derivation merges exactly once, the outcome [nunes-2004]'s chain
reduction secures. -/
theorem Derivation.coe_surfaceTokens {d : Derivation} (hd : d.lexTokens.Nodup)
    (h : d.replay?.map (·.stack) = some []) : (d.surfaceTokens : Multiset _) = d.lexTokens := by
  obtain ⟨c, hc, hst⟩ := Option.map_eq_some_iff.1 h
  have := d.yield_replay? hd hc
  rw [hst, List.map_nil, List.sum_nil, add_zero] at this
  rw [surfaceTokens, externalize?, hc, Option.map_some, Option.map_some, Option.getD_some,
    PlanarSyntacticObject.coe_yield, this]

/-- In a derivation of Merge steps with no token merged twice, every token merged is pronounced in
its object. -/
theorem Derivation.mem_yield_of_mem_lexTokens {d : Derivation} {c : Cfg PlanarSyntacticObject}
    (hd : d.lexTokens.Nodup) (hm : ∀ step ∈ d.steps, step.IsMerge) (h : d.replay? τ = some c)
    {tok : LexicalItem.Token} (ht : tok ∈ d.lexTokens) :
    tok ∈ c.current.toSyntacticObject.yield := by
  have := d.yield_replay? hd h
  rw [stack_eq_nil_of_replay? hm h, List.map_nil, List.sum_nil, add_zero] at this
  rwa [this]

/-- Chain reduction needs the tokens fresh: raising a token merged twice replaces both occurrences
by its trace, so one of the two goes unpronounced. -/
example :
    let a : LexicalItem.Token := ⟨.of .D [], 0⟩
    let b : LexicalItem.Token := ⟨.of .V [.D], 1⟩
    let d : Derivation := ⟨a, [.em .left b, .em .left a, .im a]⟩
    (d.surfaceTokens : Multiset _) ≠ d.lexTokens := by
  decide

end Minimalist
