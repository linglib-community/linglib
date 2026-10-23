module

public import Linglib.Core.Data.RoseTree.Get
public import Linglib.Morphology.Exponence.Containment.Selection
public import Linglib.Morphology.Exponence.Select

/-!
# Nanosyntax: phrasal spellout over feature trees

In nanosyntax a lexical entry pairs an exponent with a stored tree of features, one feature per
node. Caha, after Starke, lets an entry spell out a syntactic tree when the stored tree has a
subtree identical to it, the Superset Principle, which is `RoseTree.IsSubtree`.
When several entries match, the Elsewhere Condition prefers the one that matches in fewer
environments, and since a matching stored tree exceeds the syntactic tree by exactly its
superfluous material, that is the matching entry with the smallest tree. The Foot Condition asks
the lowest feature of a stored tree to occur in what it spells out. Taraldsen's matching relation
instead pairs a node of the stored tree with the root of the syntactic tree and requires their
daughters to match each other both ways; it agrees with containment on right-branching chains,
where tree spellout is also the spellout of the containment engine.

## Main definitions

* `LexicalEntry`: a stored feature tree paired with an exponent.
* `LexicalEntry.Matches`, `treeSelect`, `treeSpellout`: the Superset Principle and the Elsewhere
  Condition.
* `foot`, `FootConditionMet`: the Foot Condition.
* `Matching`: Taraldsen's matching relation.
* `chainTree`, `phrase`, `LexicalEntry.ofSupersetRule`: right-branching chains, and the
  containment engine's entries read as chain entries.

## Main results

* `LexicalEntry.applySet_subset_iff`: specificity is reverse containment of the stored trees.
* `treeSelect_isElsewhereWinner`: smallest-tree selection picks an Elsewhere winner.
* `footConditionMet_of_matches_chainTree`: an entry storing a chain meets the Foot Condition
  wherever it matches, so the condition constrains only entries with branching trees.
* `matching_chainTree_iff`, `exists_matching_not_isSubtree`: Taraldsen's matching is containment
  on chains but ignores the order of daughters in general.
* `treeSpellout_ofSupersetRule`: on chains, tree spellout is the containment engine's
  spellout.

## Implementation notes

* Trees are over any type of labels. The lexicalization algorithm
  (`Nanosyntax/Lexicalization.lean`) takes labels in `Option F`: a node labelled by a feature is
  that feature's phrase over its complement, and an unlabelled node joins an evacuated
  constituent to the remnant it left. A bare head merged as a complement is not told apart from
  a phrase of one feature, so a stored tree does not record whether its foot is unary or binary,
  the difference Starke draws between suffixes and prefixes.
* Matching is the rigid Superset Principle of Caha's (6), identity of a subtree. The algorithm
  follows the later formulation in which evacuation leaves no trace, so it needs no matching
  that ignores traces.

## References

* [starke-2009]
* [caha-2009]
* [starke-2018]
* [taraldsen-2018]
* [taraldsen-et-al-2018]
-/

@[expose] public section

namespace Morphology.Nanosyntax

open Morphology.Exponence RoseTree

variable {F α : Type*}

/-! ### Lexical entries and matching -/

/-- A nanosyntactic lexical entry pairs a stored feature tree with its exponent. -/
structure LexicalEntry (F : Type*) (α : Type*) where
  /-- The stored feature tree. -/
  tree : RoseTree F
  /-- The exponent. -/
  exponent : α
  deriving Repr

/-- An entry matches a syntactic tree when its stored tree has a subtree identical to it, the
Superset Principle of [caha-2009] (6). -/
def LexicalEntry.Matches (e : LexicalEntry F α) (t : RoseTree F) : Prop :=
  IsSubtree t e.tree

instance [DecidableEq F] (e : LexicalEntry F α) (t : RoseTree F) : Decidable (e.Matches t) :=
  inferInstanceAs (Decidable (IsSubtree _ _))

/-- A lexical entry is a rule of the exponence core, applicable where it matches. -/
instance : Exponence.Rule (LexicalEntry F α) (RoseTree F) α :=
  ⟨LexicalEntry.exponent, fun e t ↦ e.Matches t⟩

theorem LexicalEntry.applySet_subset_iff {a b : LexicalEntry F α} :
    Exponence.applySet a ⊆ Exponence.applySet b ↔ IsSubtree a.tree b.tree :=
  ⟨fun h ↦ h (.refl a.tree), fun h _ hc ↦ hc.trans h⟩

/-! ### Spellout -/

private theorem numNodes_lt_of_applySet_ssubset {s r : LexicalEntry F α}
    (hlt : Exponence.applySet s ⊂ Exponence.applySet r) : s.tree.numNodes < r.tree.numNodes := by
  have hcon := LexicalEntry.applySet_subset_iff.mp hlt.le
  refine lt_of_le_of_ne hcon.numNodes_le fun heq ↦ ?_
  exact hlt.not_ge (LexicalEntry.applySet_subset_iff.mpr (hcon.eq_of_numNodes_le heq.ge ▸ .refl _))

section
variable [DecidableEq F]

instance : DecidableRel (Applies : LexicalEntry F α → RoseTree F → Prop) :=
  fun e t ↦ inferInstanceAs (Decidable (e.Matches t))

/-- `treeSelect entries t` is the matching entry with the smallest stored tree, the first listed
on ties. -/
def treeSelect (entries : RuleSet (LexicalEntry F α)) (t : RoseTree F) :
    Option (LexicalEntry F α) :=
  entries.selectBy (fun e ↦ OrderDual.toDual e.tree.numNodes) t

/-- `treeSpellout entries t` is the exponent of the entry `treeSelect` picks. -/
def treeSpellout (entries : RuleSet (LexicalEntry F α)) (t : RoseTree F) : Option α :=
  (treeSelect entries t).map (·.exponent)

theorem treeSelect_isElsewhereWinner {entries : RuleSet (LexicalEntry F α)} {t : RoseTree F}
    {e : LexicalEntry F α} (h : treeSelect entries t = some e) :
    entries.IsElsewhereWinner Exponence.applySet t e :=
  RuleSet.selectBy_isElsewhereWinner
    (f := fun e : LexicalEntry F α ↦ OrderDual.toDual e.tree.numNodes)
    (fun _ _ _ _ h ↦ OrderDual.toDual_lt_toDual.2 (numNodes_lt_of_applySet_ssubset h)) h

theorem treeSpellout_isElsewhereWinner {entries : RuleSet (LexicalEntry F α)} {t : RoseTree F}
    {x : α} (h : treeSpellout entries t = some x) :
    ∃ e ∈ entries, e.exponent = x ∧ entries.IsElsewhereWinner Exponence.applySet t e := by
  obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨e, RuleSet.selectBy_mem he, rfl, treeSelect_isElsewhereWinner he⟩

theorem treeSpellout_eq_none_iff {entries : RuleSet (LexicalEntry F α)} {t : RoseTree F} :
    treeSpellout entries t = none ↔ ∀ e ∈ entries, ¬ e.Matches t := by
  simp [treeSpellout, treeSelect, RuleSet.selectBy_eq_none_iff, RuleSet.applicable,
    List.filter_eq_nil_iff, Applies]

theorem treeSpellout_eq_none_of_isSubtree {entries : RuleSet (LexicalEntry F α)}
    {s t : RoseTree F} (hst : IsSubtree s t) (h : treeSpellout entries s = none) :
    treeSpellout entries t = none :=
  treeSpellout_eq_none_iff.2 fun e he ht ↦ treeSpellout_eq_none_iff.1 h e he (hst.trans ht)

end

/-! ### The Foot Condition -/

/-- The foot of a tree is its lowest feature on the complement line, its last leaf. -/
def foot (t : RoseTree F) : F := t.leafList.getLast t.leafList_ne_nil

/-- The Foot Condition ([taraldsen-et-al-2018] (39)) requires a syntactic tree an entry spells
out to contain the foot of the entry's stored tree. -/
def FootConditionMet (e : LexicalEntry F α) (t : RoseTree F) : Prop :=
  foot e.tree ∈ t.leafList

instance [DecidableEq F] (e : LexicalEntry F α) (t : RoseTree F) :
    Decidable (FootConditionMet e t) :=
  inferInstanceAs (Decidable (_ ∈ _))

theorem footConditionMet_of_foot_eq {e : LexicalEntry F α} {t : RoseTree F}
    (h : foot t = foot e.tree) : FootConditionMet e t := by
  rw [FootConditionMet, ← h]
  exact List.getLast_mem _

/-! ### Chains -/

/-- `chainTree feat n` is the right-branching chain `[feat n [… [feat 0]]]`. -/
def chainTree (feat : ℕ → F) : ℕ → RoseTree F
  | 0 => leaf (feat 0)
  | n + 1 => node (feat (n + 1)) [chainTree feat n]

theorem chainTree_numNodes (feat : ℕ → F) (n : ℕ) : (chainTree feat n).numNodes = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [chainTree, ih]

theorem leafList_chainTree (feat : ℕ → F) (n : ℕ) : (chainTree feat n).leafList = [feat 0] := by
  induction n with
  | zero => simp [chainTree]
  | succ n ih => simp [chainTree, ih]

theorem foot_chainTree (feat : ℕ → F) (n : ℕ) : foot (chainTree feat n) = feat 0 := by
  simp [foot, leafList_chainTree]

theorem chainTree_injective (feat : ℕ → F) : Function.Injective (chainTree feat) :=
  fun n m h ↦ by simpa [chainTree_numNodes] using congrArg numNodes h

theorem chainTree_isSubtree_iff (feat : ℕ → F) (r k : ℕ) :
    IsSubtree (chainTree feat r) (chainTree feat k) ↔ r ≤ k := by
  induction k generalizing r with
  | zero => cases r <;> simp [chainTree]
  | succ k ih =>
    rw [chainTree, isSubtree_node_iff, ← chainTree, (chainTree_injective feat).eq_iff]
    simp only [List.mem_singleton, exists_eq_left, ih]
    omega

theorem eq_chainTree_of_isSubtree {feat : ℕ → F} {k : ℕ} {t : RoseTree F}
    (h : IsSubtree t (chainTree feat k)) : ∃ r ≤ k, t = chainTree feat r := by
  induction k with
  | zero => exact ⟨0, le_rfl, by simpa [chainTree] using h⟩
  | succ k ih =>
    rcases isSubtree_node_iff.1 h with h | ⟨c, hc, hsub⟩
    · exact ⟨k + 1, le_rfl, h⟩
    · obtain ⟨r, hr, rfl⟩ := ih (List.mem_singleton.1 hc ▸ hsub)
      exact ⟨r, hr.trans k.le_succ, rfl⟩

/-- The right-branching phrase a feature sequence builds on its first feature, each feature
taking what is below it as its complement. -/
def phrase (f₀ : F) (fs : List F) : RoseTree F := fs.foldl (fun t f ↦ node f [t]) (leaf f₀)

@[simp] theorem phrase_nil (f₀ : F) : phrase f₀ [] = leaf f₀ := rfl

@[simp] theorem phrase_concat (f₀ : F) (fs : List F) (f : F) :
    phrase f₀ (fs ++ [f]) = node f [phrase f₀ fs] := by simp [phrase]

theorem chainTree_eq_phrase (feat : ℕ → F) (k : ℕ) :
    chainTree feat k = phrase (feat 0) ((List.range k).map (feat ∘ Nat.succ)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.map_singleton, phrase_concat, ← ih, chainTree]
    rfl

theorem footConditionMet_of_matches_chainTree {e : LexicalEntry F α} {feat : ℕ → F} {k : ℕ}
    (he : e.tree = chainTree feat k) {t : RoseTree F} (h : e.Matches t) :
    FootConditionMet e t := by
  obtain ⟨r, -, rfl⟩ := eq_chainTree_of_isSubtree (he ▸ h : IsSubtree t (chainTree feat k))
  exact footConditionMet_of_foot_eq (by rw [he, foot_chainTree, foot_chainTree])

/-! ### Taraldsen's matching relation -/

/-- `MatchesRoot s u` holds when the roots of `s` and `u` carry the same feature and every
daughter of each root-matches some daughter of the other, the two clauses of [taraldsen-2018]
(3) and [taraldsen-et-al-2018] (35). -/
def MatchesRoot : RoseTree F → RoseTree F → Prop
  | node f cs, node g ds =>
      f = g ∧ (∀ c ∈ cs, ∃ d ∈ ds, MatchesRoot c d) ∧ ∀ d ∈ ds, ∃ c, ∃ _ : c ∈ cs, MatchesRoot c d
termination_by s _ => sizeOf s
decreasing_by all_goals exact sizeOf_lt_of_mem (by assumption)

theorem matchesRoot_node_iff {f g : F} {cs ds : List (RoseTree F)} :
    MatchesRoot (node f cs) (node g ds) ↔
      f = g ∧ (∀ c ∈ cs, ∃ d ∈ ds, MatchesRoot c d) ∧ ∀ d ∈ ds, ∃ c ∈ cs, MatchesRoot c d := by
  rw [MatchesRoot]
  simp only [exists_prop]

theorem MatchesRoot.refl : ∀ t : RoseTree F, MatchesRoot t t
  | node _ cs => matchesRoot_node_iff.2 ⟨rfl, fun c hc ↦ ⟨c, hc, MatchesRoot.refl c⟩,
      fun d hd ↦ ⟨d, hd, MatchesRoot.refl d⟩⟩
termination_by t => sizeOf t
decreasing_by all_goals exact sizeOf_lt_of_mem (by assumption)

/-- A syntactic tree `s` matches a stored tree `t` when the root of `s` root-matches some node of
`t`. -/
def Matching (s t : RoseTree F) : Prop := ∃ u, IsSubtree u t ∧ MatchesRoot s u

/-- A subtree matches, so the Superset Principle follows from Taraldsen's matching
([taraldsen-et-al-2018] (36)). -/
theorem Matching.of_isSubtree {s t : RoseTree F} (h : IsSubtree s t) : Matching s t :=
  ⟨s, h, .refl s⟩

theorem matchesRoot_chainTree_iff (feat : ℕ → F) (r k : ℕ) :
    MatchesRoot (chainTree feat r) (chainTree feat k) ↔ r = k := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ .refl _⟩
  induction r generalizing k with
  | zero =>
    cases k with
    | zero => rfl
    | succ k =>
      obtain ⟨-, -, hb⟩ := matchesRoot_node_iff.1 h
      obtain ⟨c, hc, -⟩ := hb _ (List.mem_singleton_self _)
      cases hc
  | succ r ih =>
    cases k with
    | zero =>
      obtain ⟨-, ha, -⟩ := matchesRoot_node_iff.1 h
      obtain ⟨d, hd, -⟩ := ha _ (List.mem_singleton_self _)
      cases hd
    | succ k =>
      obtain ⟨-, ha, -⟩ := matchesRoot_node_iff.1 h
      obtain ⟨d, hd, hm⟩ := ha _ (List.mem_singleton_self _)
      rw [List.mem_singleton.1 hd] at hm
      rw [ih k hm]

theorem matching_chainTree_iff (feat : ℕ → F) (r k : ℕ) :
    Matching (chainTree feat r) (chainTree feat k) ↔
      IsSubtree (chainTree feat r) (chainTree feat k) := by
  refine ⟨fun ⟨u, hu, hm⟩ ↦ ?_, Matching.of_isSubtree⟩
  obtain ⟨j, hj, rfl⟩ := eq_chainTree_of_isSubtree hu
  rw [chainTree_isSubtree_iff, (matchesRoot_chainTree_iff feat r j).1 hm]
  exact hj

theorem exists_matching_not_isSubtree :
    ∃ s t : RoseTree Bool, Matching s t ∧ ¬ IsSubtree s t := by
  refine ⟨node true [leaf true, leaf false], node true [leaf false, leaf true], ⟨_, .refl _, ?_⟩,
    by decide⟩
  refine matchesRoot_node_iff.2 ⟨rfl, ?_, ?_⟩ <;> simp only [List.mem_cons, List.mem_nil_iff,
    or_false, forall_eq_or_imp, forall_eq, exists_eq_or_imp, exists_eq_left]
  · exact ⟨.inr (.refl _), .inl (.refl _)⟩
  · exact ⟨.inr (.refl _), .inl (.refl _)⟩

/-! ### Spellout over containment hierarchies -/

/-- An entry of the containment engine read as an entry storing the chain up to its span. -/
def LexicalEntry.ofSupersetRule {n : ℕ} (feat : ℕ → F) (e : Containment.SupersetRule n α) :
    LexicalEntry F α :=
  ⟨chainTree feat e.spans, e.exponent⟩

theorem treeSpellout_ofSupersetRule [DecidableEq F] {n : ℕ} (feat : ℕ → F)
    (v : RuleSet (Containment.SupersetRule n α)) (g : Fin n) :
    treeSpellout (v.map (LexicalEntry.ofSupersetRule feat)) (chainTree feat g) =
      Containment.spellout v g := by
  rw [treeSpellout, treeSelect, RuleSet.selectBy_map (c := g)
    (f := fun e : Containment.SupersetRule n α ↦ OrderDual.toDual e.spans)
    (fun _ _ ↦ (chainTree_isSubtree_iff feat _ _).trans Fin.val_fin_le)
    fun _ _ _ _ ↦ by simp [LexicalEntry.ofSupersetRule, chainTree_numNodes], Option.map_map]
  rfl

end Morphology.Nanosyntax
