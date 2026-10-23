/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.SyntacticObject.Build
public import Linglib.Syntax.Minimalist.SyntacticObject.Projection
public import Linglib.Syntax.Projection
public import Linglib.Core.Data.RoseTree.Get

/-!
# Chains on linearized syntactic objects

A linearized syntactic object is a copy-theoretic representation. A vertex `Vertex.lex tok` is a
pronounced copy of `tok` and a vertex `Vertex.traceOf tok` a deleted one, the trace Internal Merge
leaves, Marcolli, Chomsky and Berwick's cancellation `T/T_v` with the head of `T_v` remembered.
The chain of a token is the list of its copies, and a copy stands for the maximal projection of
its token, so a moved phrase sits where its head projects. A token moves when it has a deleted
copy. A token bound in situ by an operator, as for Pesetsky, has a single copy. A deleted copy
above the pronounced one is Huang's covert movement, and a pronounced copy between two deleted
ones is Sato and Ngui's partial movement, so where a phrase is pronounced and where it takes scope
come apart without a separate choice of the copy to spell out. A token with two pronounced copies
is shared, dominated by two mothers, Citko's Parallel Merge.

A copy is linked to the nearest copy above it, the one whose projection c-commands it with no
other copy's projection in between, c-command being Reinhart's (`RoseTree.CCommands`).
A token with one copy has no link (`links_eq_nil_of_length_le_one`). The locality conditions on
links are in `Locality/Chain.lean`.

## Main definitions

* `Minimalist.tokenList`, `Minimalist.traceList`: the pronounced and the deleted copies.
* `occurrences`, `traces`, `chain`, `Moves`, `IsShared`: the copies of a token.
* `occurrencesWith`: the pronounced copies of the tokens a predicate holds of.
* `HasAntecedent`, `orphanTraces`: whether a pronounced copy c-commands a deleted one, and the
  deleted copies without antecedents, seen from their own conjunct copies.
* `IsLink`, `links`, `chainTop`: the links of a chain and its scope position.

## Implementation notes

* Positions, not terms, individuate copies: two deleted copies of one token are the same term.
* A copy is located at the maximal projection of its token under a head function, which the
  analysis supplies (`HeadFunction`). Under `HeadFunction.raising` a phrase with a specifier
  merged in place has a maximal projection to locate a copy in; under `HeadFunction.label` a
  phrase merged beside another is unlabeled, and its head projects no further than its sister.
* A chain here is the copies an object contains; the replay of a derivation
  (`Derivation.externalize?`) builds overt chains, while covert movement and sharing are available
  to the representation only. Remnant movement carries a deleted copy away from its antecedent,
  so an externalized object can have orphan traces.

## TODO

* Chains on the copy object of `Derivation.replayWithCopies?` (`Copy/Replay.lean`), the
  positions holding one term, with the token chains here as their case without remnant movement.

## References

* [marcolli-chomsky-berwick-2025]
* [citko-2005]
* [pesetsky-1987]
* [huang-1982]
* [sato-ngui-2017]
* [barker-pullum-1990]
-/

@[expose] public section

namespace Minimalist

open RoseTree SyntacticObject Core.Order PhraseStructure

/-! ### Copies -/

/-- The positions of `t` whose label `f` accepts, with the values, in preorder. -/
def positions {β : Type*} (f : Vertex → Option β) (t : RoseTree Vertex) : List (TreePath × β) :=
  t.positionedSubtrees.filterMap fun x ↦ (f x.2.value).map (x.1, ·)

theorem mem_positions_iff {β : Type*} {f : Vertex → Option β} {t : RoseTree Vertex}
    {p : TreePath} {b : β} :
    (p, b) ∈ positions f t ↔ ∃ s, subtreeAt t p.toList = some s ∧ f s.value = some b := by
  simp only [positions, List.mem_filterMap, Option.map_eq_some_iff, Prod.mk.injEq, Prod.exists,
    mem_positionedSubtrees]
  exact ⟨fun ⟨_, s, hs, _, hb, rfl, rfl⟩ ↦ ⟨s, hs, hb⟩,
    fun ⟨s, hs, hb⟩ ↦ ⟨p, s, hs, b, hb, rfl, rfl⟩⟩

theorem nodup_map_fst_positions {β : Type*} (f : Vertex → Option β) (t : RoseTree Vertex) :
    ((positions f t).map Prod.fst).Nodup := by
  rw [positions, List.map_filterMap]
  refine (List.pairwise_map.1 t.nodup_map_fst_positionedSubtrees).filterMap _
    fun _ _ hne b hb b' hb' ↦ ?_
  simp only [Option.map_map, Function.comp_def, Option.map_eq_some_iff] at hb hb'
  obtain ⟨-, -, rfl⟩ := hb
  obtain ⟨-, -, rfl⟩ := hb'
  exact hne

/-- The pronounced copies, left to right. -/
def tokenList : RoseTree Vertex → List (TreePath × LexicalItem.Token) :=
  positions (Sum.elim id fun _ ↦ none)

/-- The deleted copies, left to right. -/
def traceList : RoseTree Vertex → List (TreePath × LexicalItem.Token) :=
  positions (Sum.elim (fun _ ↦ none) id)

variable (hd : HeadFunction) (t : LinearizedSyntacticObject) (tok : LexicalItem.Token)

/-- The positions of the pronounced copies of `tok`. -/
def occurrences : List TreePath :=
  (tokenList t.val).filterMap fun x ↦ if x.2 = tok then some x.1 else none

/-- The positions of the pronounced copies of the tokens `P` holds of. -/
def occurrencesWith (P : LexicalItem.Token → Prop) [DecidablePred P] : List TreePath :=
  (tokenList t.val).filterMap fun x ↦ if P x.2 then some x.1 else none

theorem occurrencesWith_eq : occurrencesWith t (· = tok) = occurrences t tok := rfl

/-- The positions of the deleted copies of `tok`. -/
def traces : List TreePath :=
  (traceList t.val).filterMap fun x ↦ if x.2 = tok then some x.1 else none

/-- The chain of `tok` lists the positions of its copies, pronounced or deleted, left to right. -/
def chain : List TreePath :=
  (positions (Sum.elim id id) t.val).filterMap fun x ↦ if x.2 = tok then some x.1 else none

/-- `tok` moves when it has a deleted copy. -/
def Moves : Prop := traces t tok ≠ []

instance : Decidable (Moves t tok) := inferInstanceAs (Decidable (_ ≠ _))

/-- `tok` is shared, dominated by two mothers, when it has two pronounced copies. -/
def IsShared : Prop := 2 ≤ (occurrences t tok).length

instance : Decidable (IsShared t tok) := inferInstanceAs (Decidable (_ ≤ _))

/-! ### Antecedents -/

/-- A deleted copy has an antecedent when the projection of a pronounced copy of its token
c-commands it. -/
def HasAntecedent (x : TreePath × LexicalItem.Token) : Prop :=
  ∃ p ∈ occurrences t x.2, CCommands t.val (projectionAt hd t p) x.1

instance (x : TreePath × LexicalItem.Token) : Decidable (HasAntecedent hd t x) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- The deleted copies without antecedents. -/
def orphanTraces : List (TreePath × LexicalItem.Token) :=
  (traceList t.val).filter (¬ HasAntecedent hd t ·)

/-! ### Links -/

/-- The copy at `p` is linked to the copy at `q` below it when its projection c-commands `q` and
the projection of no other copy of `tok` lies between them. -/
def IsLink (p q : TreePath) : Prop :=
  CCommands t.val (projectionAt hd t p) q ∧
    ∀ r ∈ chain t tok, CCommands t.val (projectionAt hd t p) (projectionAt hd t r) →
      ¬ CCommands t.val (projectionAt hd t r) q

instance (p q : TreePath) : Decidable (IsLink hd t tok p q) := inferInstanceAs (Decidable (_ ∧ _))

/-- The links of the chain of `tok` pair each copy with the projection of the copy linked to it. -/
def links : List (TreePath × TreePath) :=
  (chain t tok).flatMap fun q ↦
    ((chain t tok).filter fun p ↦ IsLink hd t tok p q).map fun p ↦ (projectionAt hd t p, q)

/-- The top of the chain of `tok` consists of the copies no copy's projection c-commands, where it
takes scope. -/
def chainTop : List TreePath :=
  (chain t tok).filter fun q ↦
    (chain t tok).all fun p ↦ ¬ CCommands t.val (projectionAt hd t p) q

theorem not_isLink_self (p : TreePath) : ¬ IsLink hd t tok p p :=
  fun h ↦ h.1.2.1 (projectionAt_le hd t p)

/-- A token with at most one copy has no link. -/
theorem links_eq_nil_of_length_le_one (h : (chain t tok).length ≤ 1) : links hd t tok = [] := by
  simp only [links, List.flatMap_eq_nil_iff, List.map_eq_nil_iff, List.filter_eq_nil_iff,
    decide_eq_true_eq]
  intro q hq p hp
  obtain rfl : p = q := by
    rcases hc : chain t tok with _ | ⟨a, _ | ⟨b, l⟩⟩
    · simp [hc] at hp
    · simp only [hc, List.mem_singleton] at hp hq
      rw [hp, hq]
    · simp [hc] at h
  exact not_isLink_self hd t tok p


end Minimalist
