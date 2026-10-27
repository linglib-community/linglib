module

public import Linglib.Core.Computability.ContextFreeGrammar.Tree

/-!
# Bresnan, Kaplan, Peters and Zaenen 1982: cross-serial dependencies in Dutch

This file formalizes the argument of [bresnan-etal-1982] that Dutch is not *strongly*
context-free. In subordinate clauses like *dat Jan Piet Marie zag helpen zwemmen* the object NPs
and the verbs form two parallel right-branching structures — a VP spine holding the arguments and a
V′ cluster holding the verbs — whose depths must match: a verb with no argument at its level
violates Completeness, an argument with no verb violates Coherence. The string set of these clauses
is weakly context-free (the argument of [huybregts-1976] fails), but no context-free grammar
generates exactly the well-formed trees, under any relabelling of its nonterminals: a tall enough
derivation tree repeats a nonterminal along the verb cluster, and pumping the cluster yields a
licensed tree with more verbs than arguments. The lexical-functional grammar of
[kaplan-bresnan-1982] generates the trees through a context-free c-structure grammar filtered by the
well-formedness conditions on f-structures, and functional control derives the cross-serial
association itself.

## Main definitions

* `tree k m` — the c-structure with `k + 1` object NPs and `m + 1` verbs; `dutch n` the matched
  ones, `cStructure` the context-free c-structure grammar, `weakGrammar` the string grammar
* `Spine`, `Spine.Complete`, `Spine.Coherent` — the f-structure spine and LFG's two conditions

## Main results

* `tree_licensed_cStructure` — the c-structure grammar generates every `tree k m`
* `Spine.complete_and_coherent_iff` — Completeness and Coherence hold exactly when the objects
  match the non-final verbs
* `yield_dutch_mem_weakGrammar` — the matched strings are weakly context-free
* `not_strongly_contextFree` — no context-free grammar's derivation trees relabel onto the matched
  trees
* `subjOfVerb_eq` — the `i`-th NP is the subject of the `i`-th verb

## References

* [bresnan-etal-1982]
* [kaplan-bresnan-1982]
* [huybregts-1976]
* [evers-1975]
* [pullum-gazdar-1982]
-/

@[expose] public section

namespace BresnanEtAl1982

open RoseTree Symbol

/-- A leaf is a noun phrase or a verb. -/
inductive Word | np | v
  deriving DecidableEq, Repr

/-- The phrasal categories of the c-structure rules (25). -/
inductive Cat | S | VP | vBar
  deriving DecidableEq, Repr

/-! ### The trees -/

/-- The verb cluster of `m + 1` verbs is the right-branching V′ of (22), by V′ → V (V′). -/
def cluster : ℕ → RoseTree (Symbol Word Cat)
  | 0 => node (nonterminal .vBar) [leaf (terminal .v)]
  | m + 1 => node (nonterminal .vBar) [leaf (terminal .v), cluster m]

/-- The embedded VP spine of `k + 1` object NPs, by VP → (NP)(VP). -/
def spine : ℕ → RoseTree (Symbol Word Cat)
  | 0 => node (nonterminal .VP) [leaf (terminal .np)]
  | k + 1 => node (nonterminal .VP) [leaf (terminal .np), spine k]

/-- The VP of (22) has the first object, the spine of the remaining `k` objects, and the
cluster. -/
def topVP : ℕ → ℕ → RoseTree (Symbol Word Cat)
  | 0, m => node (nonterminal .VP) [leaf (terminal .np), cluster m]
  | k + 1, m => node (nonterminal .VP) [leaf (terminal .np), spine k, cluster m]

/-- The c-structure (22) of a clause with a subject, `k + 1` object NPs and `m + 1` verbs. -/
def tree (k m : ℕ) : RoseTree (Symbol Word Cat) :=
  node (nonterminal .S) [leaf (terminal .np), topVP k m]

/-- The well-formed trees have `n + 1` objects and `n + 2` verbs, each non-final verb with its
object.
(1) is `dutch 0`, (26) is `dutch 1`, (3) is `dutch 2`. -/
def dutch (n : ℕ) : RoseTree (Symbol Word Cat) := tree n (n + 1)

@[simp] theorem yield_cluster (m : ℕ) : (cluster m).yield = List.replicate (m + 1) .v := by
  induction m with
  | zero => rfl
  | succ m ih => simp [cluster, ih, List.replicate_succ]

@[simp] theorem yield_spine (k : ℕ) : (spine k).yield = List.replicate (k + 1) .np := by
  induction k with
  | zero => rfl
  | succ k ih => simp [spine, ih, List.replicate_succ]

@[simp] theorem yield_topVP (k m : ℕ) :
    (topVP k m).yield = List.replicate (k + 1) .np ++ List.replicate (m + 1) .v := by
  cases k <;> simp [topVP, List.replicate_succ]

@[simp] theorem yield_tree (k m : ℕ) :
    (tree k m).yield = List.replicate (k + 2) .np ++ List.replicate (m + 1) .v := by
  simp [tree, List.replicate_succ]

theorem yield_dutch (n : ℕ) :
    (dutch n).yield = List.replicate (n + 2) .np ++ List.replicate (n + 2) .v := by
  simp [dutch]

@[simp] theorem value_cluster (m : ℕ) : (cluster m).value = nonterminal .vBar := by
  cases m <;> rfl

@[simp] theorem value_spine (k : ℕ) : (spine k).value = nonterminal .VP := by
  cases k <;> rfl

@[simp] theorem value_topVP (k m : ℕ) : (topVP k m).value = nonterminal .VP := by
  cases k <;> rfl

theorem one_lt_height_cluster (m : ℕ) : 1 < (cluster m).height := by
  cases m <;> simp [cluster, leaf]

/-! ### The c-structure grammar -/

/-- The c-structure grammar (25) has S → NP VP, VP → (NP)(VP)(V′) and V′ → V (V′), with the
optional expansions the trees use. It generates every `tree k m`, matched or not; the f-structure
conditions below do the filtering. -/
def cStructure : ContextFreeGrammar Word where
  NT := Cat
  initial := .S
  rules := { ⟨.S, [terminal .np, nonterminal .VP]⟩,
             ⟨.VP, [terminal .np, nonterminal .VP, nonterminal .vBar]⟩,
             ⟨.VP, [terminal .np, nonterminal .vBar]⟩,
             ⟨.VP, [terminal .np, nonterminal .VP]⟩,
             ⟨.VP, [terminal .np]⟩,
             ⟨.vBar, [terminal .v, nonterminal .vBar]⟩,
             ⟨.vBar, [terminal .v]⟩ }

theorem cluster_licensed (m : ℕ) : (cluster m).Licensed cStructure.Licenses := by
  induction m with
  | zero =>
    refine .nonterminal _ _ (by simp [cStructure]) ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]; exact .terminal _
  | succ m ih =>
    refine .nonterminal _ _ (by simp [cStructure]) ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨.terminal _, ih⟩

theorem spine_licensed (k : ℕ) : (spine k).Licensed cStructure.Licenses := by
  induction k with
  | zero =>
    refine .nonterminal _ _ (by simp [cStructure]) ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]; exact .terminal _
  | succ k ih =>
    refine .nonterminal _ _ (by simp [cStructure]) ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨.terminal _, ih⟩

theorem topVP_licensed (k m : ℕ) : (topVP k m).Licensed cStructure.Licenses := by
  cases k with
  | zero =>
    refine .nonterminal _ _ (by simp [cStructure]) ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨.terminal _, cluster_licensed m⟩
  | succ k =>
    refine .nonterminal _ _ (by simp [cStructure]) ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨.terminal _, spine_licensed k, cluster_licensed m⟩

/-- The c-structure grammar generates every tree, whatever its counts of objects and verbs. -/
theorem tree_licensed_cStructure (k m : ℕ) : (tree k m).Licensed cStructure.Licenses := by
  refine .nonterminal _ _ (by simp [cStructure]) ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨.terminal _, topVP_licensed k m⟩

/-! ### The f-structure and its well-formedness -/

/-- In the f-structure spine a c-structure induces under (32) and (35)–(36), the VP branch supplies
an OBJ at each depth below `objects` and the V′ branch a PRED at each depth below `verbs`, every
non-final PRED subcategorizing SUBJ, OBJ and VCOMP and the final one SUBJ alone. -/
structure Spine where
  objects : ℕ
  verbs : ℕ

/-- The spine of a tree records its object NPs (all but the subject) and its verbs. -/
def Spine.ofTree (t : RoseTree (Symbol Word Cat)) : Spine :=
  ⟨t.yield.count .np - 1, t.yield.count .v⟩

@[simp] theorem Spine.ofTree_tree (k m : ℕ) : Spine.ofTree (tree k m) = ⟨k + 1, m + 1⟩ := by
  simp [ofTree, List.count_replicate]

/-- The OBJ at depth `i` has a value. -/
def Spine.HasObj (s : Spine) (i : ℕ) : Prop := i < s.objects

/-- The PRED at depth `i` subcategorizes an OBJ when it exists and is not the final verb. -/
def Spine.GovernsObj (s : Spine) (i : ℕ) : Prop := i + 1 < s.verbs

/-- Completeness requires every subcategorized OBJ to have a value. -/
def Spine.Complete (s : Spine) : Prop := ∀ i, s.GovernsObj i → s.HasObj i

/-- Coherence requires every OBJ present to be subcategorized by the PRED at its depth. -/
def Spine.Coherent (s : Spine) : Prop := ∀ i, s.HasObj i → s.GovernsObj i

/-- Completeness and Coherence hold together exactly when the objects match the non-final verbs. -/
theorem Spine.complete_and_coherent_iff (s : Spine) (hv : 1 ≤ s.verbs) :
    s.Complete ∧ s.Coherent ↔ s.objects + 1 = s.verbs := by
  simp only [Complete, Coherent, GovernsObj, HasObj]
  constructor
  · rintro ⟨hc, hh⟩
    have := hc s.objects
    have := hh (s.verbs - 1)
    omega
  · intro h
    exact ⟨fun i _ => by omega, fun i _ => by omega⟩

-- (26)
theorem dutch_wellFormed (n : ℕ) :
    (Spine.ofTree (dutch n)).Complete ∧ (Spine.ofTree (dutch n)).Coherent :=
  (Spine.complete_and_coherent_iff _ (by simp [dutch])).mpr (by simp [dutch])

-- (43)
theorem extra_verb_incomplete : ¬ (Spine.ofTree (tree 1 3)).Complete := fun h => by
  have := h 2
  simp [Spine.GovernsObj, Spine.HasObj] at this

-- (46)
theorem extra_np_incoherent : ¬ (Spine.ofTree (tree 2 2)).Coherent := fun h => by
  have := h 2
  simp [Spine.GovernsObj, Spine.HasObj] at this

/-- The OBJ at depth `i` is the `i + 1`-th NP, since the VP spine places one object per level
below the subject. -/
def npOfObj (i : ℕ) : ℕ := i + 1

/-- Under functional control (36), `(↑ VCOMP SUBJ) = (↑ OBJ)`, the subject of the verb at depth
`i + 1` is the OBJ at depth `i`, and the clause subject is the subject of the first verb. -/
def subjOfVerb : ℕ → ℕ
  | 0 => 0
  | i + 1 => npOfObj i

/-- In the cross-serial association of (1)–(3), the `i`-th NP is the subject of the `i`-th verb. -/
theorem subjOfVerb_eq (i : ℕ) : subjOfVerb i = i := by
  cases i <;> rfl

/-! ### Weak context-freeness -/

/-- This grammar for the strings of the matched trees, in the spirit of (8), has S → NP S V and
S → NP V. -/
def weakGrammar : ContextFreeGrammar Word where
  NT := Unit
  initial := ()
  rules := { ⟨(), [terminal .np, nonterminal (), terminal .v]⟩, ⟨(), [terminal .np, terminal .v]⟩ }

theorem weakGrammar_derives_center (k : ℕ) :
    weakGrammar.Derives [nonterminal ()]
      (List.replicate k (terminal .np) ++ [nonterminal ()] ++ List.replicate k (terminal .v)) := by
  induction k with
  | zero => exact .refl _
  | succ k ih =>
    refine ih.trans (ContextFreeGrammar.Produces.single
      ⟨⟨(), [terminal .np, nonterminal (), terminal .v]⟩, by simp [weakGrammar], ?_⟩)
    have h := ContextFreeRule.rewrites_of_exists_parts
      (⟨(), [terminal .np, nonterminal (), terminal .v]⟩ : ContextFreeRule Word Unit)
      (List.replicate k (terminal .np)) (List.replicate k (terminal .v))
    have e : List.replicate (k + 1) (terminal Word.np) ++ [nonterminal ()]
          ++ List.replicate (k + 1) (terminal Word.v)
        = List.replicate k (terminal .np) ++ [terminal .np, nonterminal (), terminal .v]
          ++ List.replicate k (terminal .v) := by
      rw [List.replicate_succ', List.replicate_succ]; simp
    rw [e]; exact h

/-- The matched strings are weakly context-free, since `dutch n` yields `np^(n+2) v^(n+2)`. -/
theorem yield_dutch_mem_weakGrammar (n : ℕ) : (dutch n).yield ∈ weakGrammar.language := by
  rw [ContextFreeGrammar.mem_language_iff, yield_dutch]
  simp only [List.map_append, List.map_replicate]
  refine (weakGrammar_derives_center (n + 1)).trans (ContextFreeGrammar.Produces.single
    ⟨⟨(), [terminal .np, terminal .v]⟩, by simp [weakGrammar], ?_⟩)
  have h := ContextFreeRule.rewrites_of_exists_parts
    (⟨(), [terminal .np, terminal .v]⟩ : ContextFreeRule Word Unit)
    (List.replicate (n + 1) (terminal .np)) (List.replicate (n + 1) (terminal .v))
  have e1 : List.replicate (n + 1 + 1) (terminal Word.np : Symbol Word Unit)
      = List.replicate (n + 1) (terminal .np) ++ [terminal .np] := by simp [List.replicate_succ']
  have e2 : List.replicate (n + 1 + 1) (terminal Word.v : Symbol Word Unit)
      = terminal .v :: List.replicate (n + 1) (terminal .v) := rfl
  rw [e1, e2]; simpa using h

/-! ### Strong non-context-freeness -/

/-- The derivation trees of `g` from its start symbol. -/
def trees (g : ContextFreeGrammar Word) : Set (RoseTree (Symbol Word g.NT)) :=
  {t | t.Licensed g.Licenses ∧ t.value = nonterminal g.initial}

/-- The path from the root down the verb cluster goes into the VP, into the V′, then `L` steps
along the cluster. -/
def path (L : ℕ) : List ℕ := 1 :: 2 :: List.replicate L 1

theorem cluster_subtreeAt_replicate (m r : ℕ) :
    subtreeAt (cluster (m + r)) (List.replicate r 1) = some (cluster m) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    show subtreeAt (cluster (m + r + 1)) (1 :: List.replicate r 1) = some (cluster m)
    simp [cluster, ih]

theorem dutch_subtreeAt_take (n L r : ℕ) (hr : r ≤ L) (hL : L ≤ n + 2) :
    subtreeAt (dutch (n + 1)) ((path L).take (r + 2)) = some (cluster (n + 2 - r)) := by
  have hp : (path L).take (r + 2) = [1, 2] ++ List.replicate r 1 := by
    simp [path, List.take_replicate, Nat.min_eq_left hr]
  rw [hp, subtreeAt_append]
  have h1 : subtreeAt (dutch (n + 1)) [1, 2] = some (cluster (n + 2)) := rfl
  rw [h1, Option.bind_some]
  have := cluster_subtreeAt_replicate (n + 2 - r) r
  rwa [Nat.sub_add_cancel (by omega)] at this

/-- The category at depth `k` along `path` is S, then VP, then V′ all the way down. -/
def catAt : ℕ → Cat
  | 0 => .S
  | 1 => .VP
  | _ + 2 => .vBar

/-- No context-free grammar generates exactly the well-formed trees, under any relabelling of its
nonterminals to the categories S, VP, V′ — so no finite feature decoration helps. A grammar with
`L` rules that generates `dutch (L + 1)` repeats a nonterminal along the verb cluster, and
replacing the lower repeat by the upper one gives a licensed tree of the same root with more verbs
than noun phrases, which no `dutch n` has. -/
theorem not_strongly_contextFree (g : ContextFreeGrammar Word) (ℓ : g.NT → Cat) :
    map (Symbol.mapNonterminal ℓ) '' trees g ≠ Set.range dutch := by
  intro hEq
  set L := g.rules.card with hL
  have hmem : dutch (L + 1) ∈ map (Symbol.mapNonterminal ℓ) '' trees g := by
    rw [hEq]; exact Set.mem_range_self _
  obtain ⟨t, ⟨ht, hroot⟩, htℓ⟩ := hmem
  -- the subtrees of `t` along the cluster path relabel to clusters
  have hsub : ∀ r ≤ L, ∃ s, subtreeAt t ((path L).take (r + 2)) = some s ∧
      map (Symbol.mapNonterminal ℓ) s = cluster (L + 2 - r) := by
    intro r hr
    have h := dutch_subtreeAt_take L L r hr (by omega)
    rw [← htℓ, subtreeAt_map] at h
    exact Option.map_eq_some_iff.mp h
  -- the category of the subtree of `t` at each depth along the path
  have hcat : ∀ k ≤ L + 2, ∀ nt cs,
      subtreeAt t ((path L).take k) = some (node (nonterminal nt) cs) → ℓ nt = catAt k := by
    intro k hk nt cs h
    have hm := congrArg (Option.map (map (Symbol.mapNonterminal ℓ))) h
    rw [← subtreeAt_map, htℓ] at hm
    have key : ∀ d : RoseTree (Symbol Word Cat),
        subtreeAt (dutch (L + 1)) ((path L).take k) = some d →
          d.value = nonterminal (catAt k) := by
      match k, hk with
      | 0, _ =>
        intro d hd
        simp only [List.take_zero, subtreeAt_nil, Option.some.injEq] at hd
        subst hd; rfl
      | 1, _ =>
        intro d hd
        have h1 : subtreeAt (dutch (L + 1)) ((path L).take 1) = some (topVP (L + 1) (L + 2)) :=
          rfl
        rw [h1, Option.some.injEq] at hd
        subst hd; exact value_topVP _ _
      | r + 2, hk =>
        intro d hd
        rw [dutch_subtreeAt_take L L r (by omega) (by omega), Option.some.injEq] at hd
        subst hd; exact value_cluster _
    simpa using key _ hm
  -- pigeonhole along the cluster path
  obtain ⟨sL, hsL, hsLℓ⟩ := hsub L le_rfl
  have hpath : (path L).take (L + 2) = path L := List.take_of_length_le (by simp [path])
  rw [hpath] at hsL
  have hsLh : 1 < sL.height := by
    rw [← height_map (Symbol.mapNonterminal ℓ), hsLℓ]; exact one_lt_height_cluster _
  obtain ⟨i, j, hij, hjle, A, cᵢ, cⱼ, hi, hj⟩ :=
    ht.exists_repeat hsL hsLh (by simp only [path, List.length_cons, List.length_replicate]; omega)
  simp only [path, List.length_cons, List.length_replicate] at hjle
  -- both repeats lie in the cluster
  have hcati := hcat i (by omega) A cᵢ hi
  have hcatj := hcat j (by omega) A cⱼ hj
  have hi2 : 2 ≤ i := by
    have hc : catAt i = catAt j := by rw [← hcati, ← hcatj]
    rcases i with _ | _ | i <;> rcases j with _ | _ | j <;> simp [catAt] at hc <;> omega
  -- the pumped tree
  set t' := t.replaceAt ((path L).take j) (node (nonterminal A) cᵢ) with ht'
  have hvalid : t'.Licensed g.Licenses := ht.replaceAt hj (ht.of_subtreeAt hi) rfl
  have hroot' : t'.value = nonterminal g.initial := by
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [ht', path, List.take_succ_cons, value_replaceAt_cons]; exact hroot
  have hmem' : map (Symbol.mapNonterminal ℓ) t' ∈ Set.range dutch := by
    rw [← hEq]; exact Set.mem_image_of_mem _ ⟨hvalid, hroot'⟩
  obtain ⟨m, hm⟩ := hmem'
  -- yields: the pumped tree has `j - i` more verbs than noun phrases
  obtain ⟨pre, post, hy, hy'⟩ := yield_replaceAt hj
  obtain ⟨sᵢ, hsᵢ, hsᵢℓ⟩ := hsub (i - 2) (by omega)
  obtain ⟨sⱼ, hsⱼ, hsⱼℓ⟩ := hsub (j - 2) (by omega)
  rw [show i - 2 + 2 = i by omega, hi, Option.some.injEq] at hsᵢ
  rw [show j - 2 + 2 = j by omega, hj, Option.some.injEq] at hsⱼ
  subst hsᵢ hsⱼ
  have hyi : (node (nonterminal A) cᵢ).yield = List.replicate (L + 2 - (i - 2) + 1) .v := by
    rw [← yield_map ℓ, hsᵢℓ, yield_cluster]
  have hyj : (node (nonterminal A) cⱼ).yield = List.replicate (L + 2 - (j - 2) + 1) .v := by
    rw [← yield_map ℓ, hsⱼℓ, yield_cluster]
  have hyt : t.yield = List.replicate (L + 3) .np ++ List.replicate (L + 3) .v := by
    rw [← yield_map ℓ, htℓ, yield_dutch]
  have hyt' : t'.yield = List.replicate (m + 2) .np ++ List.replicate (m + 2) .v := by
    rw [← yield_map ℓ, ← hm, yield_dutch]
  have hnp := congrArg (List.count Word.np) hy
  have hv := congrArg (List.count Word.v) hy
  have hnp' := congrArg (List.count Word.np) (hy' (node (nonterminal A) cᵢ))
  have hv' := congrArg (List.count Word.v) (hy' (node (nonterminal A) cᵢ))
  rw [hyt, hyj] at hnp hv
  rw [← ht', hyt', hyi] at hnp' hv'
  simp [List.count_replicate] at hnp hv hnp' hv'
  omega

end BresnanEtAl1982
