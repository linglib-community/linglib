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

* `Minimalist.Derivation.coe_surfaceTokens`: each merged token is pronounced exactly once.
* `Minimalist.Derivation.mem_yield_of_mem_lexTokens`: a derivation of Merge steps pronounces every
  token it merges.

## References

* [nunes-2004]
-/

public section

namespace Minimalist

open RoseTree SyntacticObject
open Derivation (Cfg)
open PlanarSyntacticObject (toSyntacticObject)

variable {τ : SyntacticObject → Option LexicalItem.Token}

/-- When no token is merged twice and no extracted copy is left on the stack, the externalized
object pronounces every token the derivation merges exactly once, the outcome [nunes-2004]'s chain
reduction secures. -/
theorem Derivation.coe_surfaceTokens {d : Derivation} (hd : d.lexTokens.Nodup)
    (h : d.replay?.map (·.stack) = some []) : (d.surfaceTokens : Multiset _) = d.lexTokens := by
  obtain ⟨c, hc, hst⟩ := Option.map_eq_some_iff.1 h
  have := d.yield_replay? hd hc
  rw [Cfg.yield_map, hst, List.map_nil, List.sum_nil, add_zero] at this
  rw [surfaceTokens, externalize?, hc, Option.map_some, Option.map_some, Option.getD_some,
    PlanarSyntacticObject.coe_yield, this]

/-- In a derivation of Merge steps with no token merged twice, every token merged is pronounced in
its object. -/
theorem Derivation.mem_yield_of_mem_lexTokens {d : Derivation} {c : Cfg PlanarSyntacticObject}
    (hd : d.lexTokens.Nodup) (hm : ∀ step ∈ d.steps, step.IsMerge) (h : d.replay? τ = some c)
    {tok : LexicalItem.Token} (ht : tok ∈ d.lexTokens) :
    tok ∈ c.current.toSyntacticObject.yield := by
  have := d.yield_replay? hd h
  rw [Cfg.yield_map, stack_eq_nil_of_replay? hm h, List.map_nil, List.sum_nil, add_zero] at this
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
