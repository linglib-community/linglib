/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Copy.Chain

/-!
# Spell-out of linearized syntactic objects

PF pronounces the pronounced copies of a linearized syntactic object (`Chain.lean`) and nothing
else, so a deleted copy, a trace, is silent wherever it stands. A shared token is one token,
pronounced once, at its last occurrence, as Wilder and de Vries linearize multidominance, so that
material two conjuncts share is pronounced in the second. An [E] feature on a head silences the
head's complement, after Merchant, and since a shared token is one token, eliding either of its
occurrences silences it everywhere. An [E] head applies once per distinct complement.

## Main definitions

* `pronouncedAt`, `elidedDomains`, `IsSilenced`: pronunciation under [E].
* `pfYield`, `pfPhon`: the pronounced tokens and forms, left to right.
* `SpellsOut`: recognition by checked witness, an object over a lexicon pronouncing a given word
  sequence.

## Main statements

* `nodup_pfYield`: a token is pronounced once at most, however many mothers dominate it.

## References

* [wilder-1999]
* [de-vries-2009]
* [merchant-2001]
-/

@[expose] public section

namespace Minimalist

open RoseTree SyntacticObject Core.Order

variable (t : LinearizedSyntacticObject)

/-- `tok` is pronounced at its last occurrence. -/
def pronouncedAt (tok : LexicalItem.Token) : Option TreePath := (occurrences t tok).getLast?

/-! ### Ellipsis -/

/-- The [E] heads. -/
def eHeads : List TreePath :=
  (tokenList t.val).filterMap fun x ↦ if x.2.item.ellipsis then some x.1 else none

/-- The elided domains are the distinct complements of the [E] heads, in the order of the heads,
so a shared head over one shared complement applies once and over two complements twice. -/
def elidedDomains : List TreePath :=
  ((eHeads t).map complement).foldl
    (fun acc p ↦ if acc.any (fun q ↦ subtreeAt t.val q.toList = subtreeAt t.val p.toList) then acc
      else acc ++ [p]) []

/-- `tok` is silenced when one of its occurrences lies in an elided domain. -/
def IsSilenced (tok : LexicalItem.Token) : Prop :=
  ∃ K ∈ elidedDomains t, ∃ p ∈ occurrences t tok, K ≤ p

instance (tok : LexicalItem.Token) : Decidable (IsSilenced t tok) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- The pronounced tokens, left to right, each at its last occurrence unless silenced. -/
def pfYield : List LexicalItem.Token :=
  (tokenList t.val).filterMap fun x ↦
    if pronouncedAt t x.2 = some x.1 ∧ ¬ IsSilenced t x.2 then some x.2 else none

/-- The pronounced forms, left to right. -/
def pfPhon : List String := (pfYield t).filterMap (·.item.phonForm?)

/-- `t` spells `ws` from `lex`: every pronounced token's item is drawn from `lex`, and the
pronounced forms are exactly `ws`. Recognition by checked witness: a study exhibits a linearized
object over its lexicon and proves that it pronounces a row's sentence. -/
def SpellsOut (lex : List LexicalItem) (ws : List String) : Prop :=
  (∀ tok ∈ pfYield t, tok.item ∈ lex) ∧ pfPhon t = ws

instance (lex : List LexicalItem) (ws : List String) : Decidable (SpellsOut t lex ws) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- A token is pronounced once at most, however many mothers dominate it. -/
theorem nodup_pfYield : (pfYield t).Nodup := by
  refine ((nodup_map_fst_positions _ t.val).of_map Prod.fst).filterMap fun x y tok hx hy ↦ ?_
  simp only [Option.mem_def, Option.ite_none_right_eq_some, Option.some.injEq] at hx hy
  obtain ⟨⟨hx, -⟩, rfl⟩ := hx
  obtain ⟨⟨hy, -⟩, hxy⟩ := hy
  exact Prod.ext (Option.some_injective _ (hx.symm.trans (hxy ▸ hy))) hxy.symm

end Minimalist
