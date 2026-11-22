/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.ConstructionGrammar.Licensing

/-!
# Construction-relative composition

Rules of semantic combination are construction-relative: a construction
"specifies how the semantics of the daughters are combined to produce the
semantics of the mother, and what additional semantics, if any, is
contributed by the construction itself" ([kay-michaelis-2019] §4). A
composition rule is partial — it demands daughter denotations of the
right shape — and mismatches are repaired by the override principle
([michaelis-2004], (20)): the lexical item conforms to the meaning of the
structure in which it is embedded.

## Main definitions

* `CompositionRule`: from the daughters' denotations to the mother's
* `CompositionRule.override`: readings under the override principle, one per daughter and
  reconciliation operator
* `interps`: all readings of a tree, through the forms its constituents instantiate

## Main results

* `Licenses.of_interps_ne_nil`: a tree with a reading is licensed

## References

* [kay-michaelis-2019]
* [michaelis-2004]
-/

@[expose] public section

namespace ConstructionGrammar

variable {D : Type*}

/-- A composition rule maps the daughters' denotations to the mother's, partially, because a
rule demands daughter denotations of the right shape ([kay-michaelis-2019] §4). -/
abbrev CompositionRule (D : Type*) := List D → Option D

/-- The readings follow the override principle ([michaelis-2004], (20)), "if a lexical item is
semantically incompatible with its morphosyntactic context, the meaning of the lexical item
conforms to the meaning of the structure in which it is embedded". They are the rule's own output
where the daughters already conform, and otherwise one reading for each daughter and
reconciliation operator that makes the daughters conform when applied to that daughter alone.
Distinct repairs produce genuine ambiguity. -/
def CompositionRule.override [DecidableEq D] (r : CompositionRule D)
    (shifts : List (D → D)) (ds : List D) : List D :=
  match r ds with
  | some d => [d]
  | none =>
    ((List.range ds.length).flatMap fun i ↦ shifts.filterMap fun s ↦ r (ds.modify i s)).dedup

/-- Conforming daughters are composed directly, since implicit type-shifting occurs only on
mismatch ([michaelis-2004], (20)). -/
theorem CompositionRule.override_eq_of_eq_some [DecidableEq D]
    {r : CompositionRule D} {ds : List D} {d : D} (shifts : List (D → D))
    (h : r ds = some d) : r.override shifts ds = [d] := by
  simp [CompositionRule.override, h]

@[simp]
theorem CompositionRule.override_nil [DecidableEq D]
    (r : CompositionRule D) (ds : List D) :
    r.override [] ds = (r ds).toList := by
  cases h : r ds <;> simp [CompositionRule.override, h]

open PhraseStructure (Tree)
open Morphology (Word)

mutual

/-- In the readings of a tree, each construction whose typed form the daughters instantiate
contributes the readings its meaning pole, a composition rule, produces from the daughters'
readings; words read their denotations `den`. -/
def interps (cxns : List (Construction (CompositionRule D))) (den : Word → Option D) :
    Tree Unit Word → List D
  | .terminal _ w => (den w).toList
  | .node _ ts =>
      cxns.flatMap fun c ↦
        if FormMatches c.form ts then (interpsList cxns den ts).filterMap c.meaning else []
  | _ => []

/-- All sequences of daughter readings. -/
def interpsList (cxns : List (Construction (CompositionRule D))) (den : Word → Option D) :
    List (Tree Unit Word) → List (List D)
  | [] => [[]]
  | t :: ts => (interps cxns den t).flatMap fun d ↦ (interpsList cxns den ts).map (d :: ·)

end

variable {cxns : List (Construction (CompositionRule D))} {den : Word → Option D}

theorem interps_node (c : Unit) (ts : List (Tree Unit Word)) :
    interps cxns den (.node c ts) = cxns.flatMap fun c ↦
      if FormMatches c.form ts then (interpsList cxns den ts).filterMap c.meaning else [] := by
  rw [interps]

theorem interps_ne_nil_of_interpsList_ne_nil {ts : List (Tree Unit Word)}
    (h : interpsList cxns den ts ≠ []) : ∀ t ∈ ts, interps cxns den t ≠ [] := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    rw [interpsList] at h
    obtain ⟨_, hmem⟩ := List.exists_mem_of_ne_nil _ h
    obtain ⟨d, hd, hds⟩ := List.mem_flatMap.1 hmem
    rw [List.forall_mem_cons]
    exact ⟨List.ne_nil_of_mem hd, ih (by rintro e; simp [e] at hds)⟩

/-- A tree with a reading is licensed: each of its constituents instantiates the form of the
construction that composes it. -/
theorem Licenses.of_interps_ne_nil {t : Tree Unit Word} (h : interps cxns den t ≠ []) :
    Licenses cxns t := by
  induction t using RoseTree.rec' with
  | node l ts ih =>
    intro s hs
    rw [RoseTree.subtrees_node, List.mem_cons, List.mem_flatMap] at hs
    rcases l with ⟨_, w⟩ | ⟨_, _ | _⟩ | _ | _
    · cases ts with
      | nil => obtain rfl | ⟨_, h', _⟩ := hs <;> [trivial; cases h']
      | cons => simp [interps] at h
    · simp only [interps, ne_eq, List.flatMap_eq_nil_iff, not_forall] at h
      obtain ⟨c, hc, hne⟩ := h
      split_ifs at hne with hm
      · have hts : ∀ u ∈ ts, interps cxns den u ≠ [] :=
          interps_ne_nil_of_interpsList_ne_nil fun e ↦ hne (by rw [e]; rfl)
        obtain rfl | ⟨u, hu, hsu⟩ := hs
        · exact ⟨c, hc, hm⟩
        · exact ih u hu (hts u hu) s hsu
      · exact absurd rfl hne
    all_goals simp [interps] at h

end ConstructionGrammar
