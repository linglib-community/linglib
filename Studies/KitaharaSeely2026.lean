module

public import Studies.MarcolliChomskyBerwick2025
public import Linglib.Syntax.Minimalist.Workspace.Basic

/-!
# Kitahara and Seely (2026): Merge and the formal recognition of the workspace

Chomsky reconceives Merge as an operation on the workspace (10): it targets two accessible terms
`P` and `Q` and adds `{P, Q}`. What else the output holds follows from two third-factor
principles, Preservation of Terms (11) and Minimal Yield (12), under which accessibility, the
members of the workspace and their terms, grows by exactly one. Keeping the Merge-ees as members
would raise it by more (18), so they leave the workspace (20); External and Internal Merge then
satisfy Minimal Yield (21)–(22), and Parallel and Sideward Merge, Late Merge and Countercyclic
Merge do not (23)–(25).

Marcolli, Chomsky and Berwick state Minimal Yield over a count of accessible terms, and its
condition on size is this one at the count of distinct terms (`minimalYield_of_minimalist`). Their
Sideward Merge of type 2(b) satisfies their Minimal Yield, since the term it extracts leaves an
inaccessible trace; MERGE of the same targets on the same workspace leaves the term accessible
where it was and violates Minimal Yield (`sideward2b`).

## Implementation notes

* MERGE is `Workspace.merge`, and Preservation of Terms `Workspace.terms_subset_terms_merge`.
* The terms of an object are counted once each, so the lower copy of an internally merged term is
  not counted again, minimal search finding the higher copy first; copies in different members of
  the workspace are counted apart.
* The leaves `a` to `d` stand for the chapter's schematic lexical items.

## References

* [kitahara-seely-2026]
* [marcolli-chomsky-berwick-2025]
-/

@[expose] public section

namespace KitaharaSeely2026

open Minimalist (Workspace SyntacticObject)
open Minimalist.SyntacticObject (merge leaf deleteAccessible)
open MarcolliChomskyBerwick2025 (eaten theD theApple)

/-- The accessibility of a workspace: its members, and below each the terms it contains, each
counted once. -/
def accessibility (W : Workspace) : ℕ :=
  Multiset.card W + (W.map fun s ↦ s.accessibleTerms.toFinset.card).sum

/-- Minimal Yield (12): accessibility increases by only one. -/
def MinimalYield (W W' : Workspace) : Prop := accessibility W' = accessibility W + 1

instance (W W' : Workspace) : Decidable (MinimalYield W W') :=
  inferInstanceAs (Decidable (_ = _))

/-- Minimal Yield (12) is the condition on size of Marcolli, Chomsky and Berwick's Minimal Yield,
counting an object's distinct terms. -/
theorem minimalYield_of_minimalist {W W' : Workspace}
    (h : Minimalist.MinimalYield (fun s ↦ s.accessibleTerms.toFinset.card) W W') :
    MinimalYield W W' :=
  h.minimalYield

/-- A schematic lexical item. -/
def item (i : ℕ) : SyntacticObject := leaf ⟨.of .N [], i⟩

/-- The schematic items `a`, `b`, `c` and `d`. -/
def a : SyntacticObject := item 0
@[inherit_doc a] def b : SyntacticObject := item 1
@[inherit_doc a] def c : SyntacticObject := item 2
@[inherit_doc a] def d : SyntacticObject := item 3

/-- (17), (20), (21): External Merge of `a` and `b` in `[a, b, c]` gives `[{a, b}, c]`, raising
accessibility from three to four. -/
theorem ex21 : ({a, b, c} : Workspace).merge a b = {merge a b, c} ∧
    accessibility {a, b, c} = 3 ∧ MinimalYield {a, b, c} (({a, b, c} : Workspace).merge a b) := by
  decide +kernel

/-- (18): keeping `a` and `b` as members beside `{a, b}` makes each accessible twice. -/
theorem ex18 : ¬ MinimalYield {a, b, c} {a, b, merge a b, c} := by decide +kernel

/-- (22): Internal Merge of `c` with `{a, {b, c}}` raises accessibility from five to six, the lower
copy of `c` not counted. -/
theorem ex22 :
    ({merge a (merge b c)} : Workspace).merge c (merge a (merge b c)) =
      {merge c (merge a (merge b c))} ∧
    accessibility {merge a (merge b c)} = 5 ∧
    MinimalYield {merge a (merge b c)}
      (({merge a (merge b c)} : Workspace).merge c (merge a (merge b c))) := by
  decide +kernel

/-- (23): Parallel or Sideward Merge of `a` with the `c` of `{b, c}` leaves `c` accessible twice,
raising accessibility from four to six. -/
theorem ex23 : ({a, merge b c} : Workspace).merge a c = {merge a c, merge b c} ∧
    accessibility {a, merge b c} = 4 ∧ accessibility {merge a c, merge b c} = 6 ∧
    ¬ MinimalYield {a, merge b c} (({a, merge b c} : Workspace).merge a c) := by
  decide +kernel

/-- (24): Late Merge of `{c, d}` with the `b` of `{a, b}` raises accessibility from six to eight. -/
theorem ex24 :
    ({merge a b, merge c d} : Workspace).merge b (merge c d) =
      {merge a b, merge b (merge c d)} ∧
    accessibility {merge a b, merge c d} = 6 ∧
    accessibility {merge a b, merge b (merge c d)} = 8 := by
  decide +kernel

/-- (25): Countercyclic Merge of `c` with `{b, {c, d}}` inside `{a, {b, {c, d}}}` raises
accessibility from seven to thirteen. -/
theorem ex25 :
    ({merge a (merge b (merge c d))} : Workspace).merge c (merge b (merge c d)) =
      {merge c (merge b (merge c d)), merge a (merge b (merge c d))} ∧
    accessibility {merge a (merge b (merge c d))} = 7 ∧
    accessibility {merge c (merge b (merge c d)), merge a (merge b (merge c d))} = 13 := by
  decide +kernel

/-- Sideward Merge of type 2(b) on the workspace `{eaten, {the, apple}}` of Marcolli, Chomsky and
Berwick: their trace-cut term satisfies their Minimal Yield under the trace count, while MERGE of
*eaten* and *the* violates Minimal Yield (12), the copy of *the* staying accessible in *the
apple*. -/
theorem sideward2b :
    Minimalist.MinimalYield UnorderedTree.accessibleCount {eaten.val, theApple.val}
      {(merge eaten theD).val, (deleteAccessible theD theApple).val} ∧
    ¬ MinimalYield {eaten, theApple} (({eaten, theApple} : Workspace).merge eaten theD) :=
  ⟨MarcolliChomskyBerwick2025.sideward2b_minimalYield, by decide +kernel⟩

end KitaharaSeely2026
