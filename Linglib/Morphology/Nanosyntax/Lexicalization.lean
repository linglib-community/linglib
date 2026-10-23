module

public import Linglib.Morphology.Nanosyntax.TreeSpellout

/-!
# Nanosyntax: the lexicalization algorithm

In nanosyntax features merge one at a time, and the phrase a merger creates must be lexicalized
before the next feature merges. Starke's algorithm says what happens when no entry matches the
new phrase. Material evacuates from the complement of the new feature, first the constituent
holding the bottom of the sequence and then ever larger constituents around it, until the remnant
is lexicalized. If no evacuation helps, the derivation returns to the previous merger and takes
its next option. An evacuated constituent keeps its exponent and the remnant gets one of its own,
so evacuation is what makes a suffix. A lexicalized constituent is pronounced as a whole, so an
entry matching the new phrase, or the whole structure evacuation has built, overrides the
exponents inside it.

## Main definitions

* `spine`, `merge`, `adjoin`: syntactic objects, with labelled phrases and the unlabelled nodes
  evacuation creates.
* `mergeOptions`: the ways of lexicalizing a merger, in order of preference.
* `derivations`: the derivations of a feature sequence, in order of preference.
* `spell`: the exponents of a derivation, largest lexicalized constituents first.
* `lexicalize`, `exponents`: the first derivation and its exponents.

## Main results

* `derivations_append`: deriving a sequence is deriving its first part and then, from each
  result in turn, the rest, which is backtracking.
* `exists_matches_of_mem_lexicalize`, `exponents_eq_none_iff`: every constituent of the
  derivation is matched by an entry, so a derivation is always pronounced.
* `exponents_cons_of_forall_leaf`, `exponents_ofSupersetRule`: where no entry lexicalizes a
  feature above the bottom alone the algorithm never evacuates, so on a lexicon of containment
  entries its one exponent is the containment engine's spellout.

## Implementation notes

* A syntactic object is a tree with labels in `Option F`. A node labelled `some f` is the phrase
  of the feature `f`, with its complement as its one daughter, or none when the complement has
  evacuated. A node labelled `none` is unlabelled and has two daughters, an evacuated constituent
  and the remnant it left. Evacuation leaves no trace and projects no label.
* A derivation is the row of constituents along the left edge of its root. Its exponents are
  read off the finished structure, which is sound because a constituent once built is never
  changed, only merged over.
* `mergeOptions` follows the pied-piping formulation of the algorithm, which adds evacuations
  to Starke's original steps. On a lexicon whose trees have no unlabelled node only the original
  ones can be lexicalized (`length_le_of_mem_mergeOptions`).

## TODO

* The algorithm's last resort, a specifier built in a workspace of its own, which is where
  prefixes come from. The literature differs on what such a derivation starts from.

## References

* [starke-2018]
* [declercq-et-al-2025]
* [caha-2009]
-/

@[expose] public section

namespace Morphology.Nanosyntax

open Morphology.Exponence RoseTree

variable {F α : Type*}

/-! ### Syntactic objects -/

/-- The right-branching phrase a feature sequence builds without evacuation, its first feature
at the bottom. -/
def spine (f₀ : F) (fs : List F) : RoseTree (Option F) := phrase (some f₀) (fs.map some)

/-- The phrase a feature projects over a complement. -/
abbrev merge (f : F) (t : RoseTree (Option F)) : RoseTree (Option F) := node (some f) [t]

/-- The unlabelled node an evacuated constituent forms with the remnant it left. -/
abbrev adjoin (l r : RoseTree (Option F)) : RoseTree (Option F) := node none [l, r]

@[simp] theorem spine_nil (f₀ : F) : spine f₀ [] = leaf (some f₀) := rfl

@[simp] theorem spine_concat (f₀ : F) (fs : List F) (f : F) :
    spine f₀ (fs ++ [f]) = merge f (spine f₀ fs) := by simp [spine]

/-- A derivation in progress is the row of constituents along the left edge of its root, the
one holding the bottom of the feature sequence first and the remnants of evacuation after
it. -/
abbrev Derivation (F : Type*) := List (RoseTree (Option F))

/-- The object a row of constituents forms, each remnant adjoined to what evacuated from it. -/
def root : Derivation F → Option (RoseTree (Option F))
  | [] => none
  | t :: ts => some (ts.foldl adjoin t)

@[simp] theorem root_nil : root ([] : Derivation F) = none := rfl

@[simp] theorem root_singleton (t : RoseTree (Option F)) : root [t] = some t := rfl

theorem root_concat {d : Derivation F} (hd : d ≠ []) (t : RoseTree (Option F)) :
    root (d ++ [t]) = (root d).map (adjoin · t) := by
  obtain ⟨s, ts, rfl⟩ := List.exists_cons_of_ne_nil hd
  simp [root]

theorem value_eq_none_of_root {d : Derivation F} {t : RoseTree (Option F)} (h : root d = some t)
    (hd : 2 ≤ d.length) : t.value = none := by
  induction d using List.reverseRecOn with
  | nil => simp at hd
  | append_singleton d s _ =>
    have hne : d ≠ [] := by rintro rfl; simp at hd
    rw [root_concat hne] at h
    obtain ⟨l, -, rfl⟩ := Option.map_eq_some_iff.mp h
    rfl

variable [DecidableEq F] {L : RuleSet (LexicalEntry (Option F) α)} {f : F}

/-! ### One merger -/

/-- The ways of lexicalizing the merger of a feature with a derivation, in order of preference.
The new phrase is lexicalized whole, or the first `j` constituents of its complement evacuate
and the remnant is lexicalized, for `j` from one up to all of them. -/
def mergeOptions (L : RuleSet (LexicalEntry (Option F) α)) (d : Derivation F) (f : F) :
    List (Derivation F) :=
  (List.range (d.length + 1)).filterMap fun j ↦
    (treeSpellout L (node (some f) (root (d.drop j)).toList)).map fun _ ↦
      d.take j ++ [node (some f) (root (d.drop j)).toList]

theorem mem_mergeOptions {d d' : Derivation F} :
    d' ∈ mergeOptions L d f ↔ ∃ j ≤ d.length,
      (treeSpellout L (node (some f) (root (d.drop j)).toList)).isSome ∧
        d' = d.take j ++ [node (some f) (root (d.drop j)).toList] := by
  simp only [mergeOptions, List.mem_filterMap, List.mem_range, Nat.lt_succ_iff,
    Option.map_eq_some_iff, Option.isSome_iff_exists]
  exact ⟨fun ⟨j, hj, x, hx, h⟩ ↦ ⟨j, hj, ⟨x, hx⟩, h.symm⟩,
    fun ⟨j, hj, ⟨x, hx⟩, h⟩ ↦ ⟨j, hj, x, hx, h.symm⟩⟩

theorem mergeOptions_nil (L : RuleSet (LexicalEntry (Option F) α)) (f : F) :
    mergeOptions L [] f =
      ((treeSpellout L (leaf (some f))).map fun _ ↦ [leaf (some f)]).toList := by
  cases h : treeSpellout L (leaf (some f)) <;> simp [mergeOptions, h]

theorem mergeOptions_singleton (L : RuleSet (LexicalEntry (Option F) α))
    (t : RoseTree (Option F)) (f : F) :
    mergeOptions L [t] f =
      ((treeSpellout L (merge f t)).map fun _ ↦ [merge f t]).toList ++
        ((treeSpellout L (leaf (some f))).map fun _ ↦ [t, leaf (some f)]).toList := by
  cases h : treeSpellout L (merge f t) <;> cases h' : treeSpellout L (leaf (some f)) <;>
    simp [mergeOptions, List.range_succ, h, h']

theorem length_le_of_mem_mergeOptions
    (hL : ∀ e ∈ L, ∀ t, IsSubtree t e.tree → t.value ≠ none) {d d' : Derivation F}
    (h : d' ∈ mergeOptions L d f) : d.length ≤ d'.length := by
  obtain ⟨j, hj, hx, rfl⟩ := mem_mergeOptions.1 h
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hx
  obtain ⟨e, he, -, hw⟩ := treeSpellout_isElsewhereWinner hx
  have hlen : (d.drop j).length ≤ 1 := by
    by_contra hlt
    obtain ⟨t, ht⟩ : ∃ t, root (d.drop j) = some t := by
      rcases hdj : d.drop j with - | ⟨s, ts⟩
      · simp [hdj] at hlt
      · exact ⟨_, rfl⟩
    refine hL e he t (IsSubtree.trans (.of_mem_children ?_) hw.1.2)
      (value_eq_none_of_root ht (by omega))
    simp [ht]
  simp only [List.length_drop] at hlen
  simp only [List.length_append, List.length_take, List.length_singleton]
  omega

/-! ### Derivations -/

/-- The derivations of a feature sequence from a derivation, in order of preference. Each
merger takes its options in turn and the rest of the sequence is derived from each. -/
def derivations (L : RuleSet (LexicalEntry (Option F) α)) :
    Derivation F → List F → List (Derivation F)
  | d, [] => [d]
  | d, f :: fs => (mergeOptions L d f).flatMap (derivations L · fs)

@[simp] theorem derivations_nil (d : Derivation F) : derivations L d [] = [d] := rfl

@[simp] theorem derivations_cons (d : Derivation F) (f : F) (fs : List F) :
    derivations L d (f :: fs) = (mergeOptions L d f).flatMap (derivations L · fs) := rfl

theorem derivations_singleton (d : Derivation F) (f : F) :
    derivations L d [f] = mergeOptions L d f := by simp

theorem derivations_append (d : Derivation F) (fs gs : List F) :
    derivations L d (fs ++ gs) = (derivations L d fs).flatMap (derivations L · gs) := by
  induction fs generalizing d with
  | nil => simp
  | cons f fs ih => simp [ih, List.flatMap_assoc]

/-- The lexicalization algorithm returns the first derivation of a feature sequence, the bottom
of the sequence first. -/
def lexicalize (L : RuleSet (LexicalEntry (Option F) α)) (fs : List F) :
    Option (Derivation F) :=
  (derivations L [] fs).head?

/-! ### Exponents -/

/-- The exponents of a row given last constituent first. The whole row gets one exponent where
an entry matches the object it forms, and otherwise its last constituent gets its own after
the exponents of the rest. -/
def spellAux (L : RuleSet (LexicalEntry (Option F) α)) : Derivation F → Option (List α)
  | [] => some []
  | t :: rd =>
    (((root (rd.reverse ++ [t])).bind (treeSpellout L)).map fun x ↦ [x]) <|>
      (spellAux L rd).bind fun xs ↦ (treeSpellout L t).map fun x ↦ xs ++ [x]

/-- The exponents of a derivation, in linear order. A lexicalized constituent is pronounced as
a whole, so the longest initial part of the row forming a lexicalized object gets one exponent
and each constituent after it its own. -/
def spell (L : RuleSet (LexicalEntry (Option F) α)) (d : Derivation F) : Option (List α) :=
  spellAux L d.reverse

@[simp] theorem spell_nil : spell L ([] : Derivation F) = some [] := rfl

theorem spell_concat (d : Derivation F) (t : RoseTree (Option F)) :
    spell L (d ++ [t]) =
      ((((root (d ++ [t])).bind (treeSpellout L)).map fun x ↦ [x]) <|>
        (spell L d).bind fun xs ↦ (treeSpellout L t).map fun x ↦ xs ++ [x]) := by
  simp [spell, spellAux]

@[simp] theorem spell_singleton (t : RoseTree (Option F)) :
    spell L [t] = (treeSpellout L t).map fun x ↦ [x] := by
  cases h : treeSpellout L t <;> simp [spell, spellAux, h]

theorem spell_isSome {d : Derivation F} (h : ∀ t ∈ d, (treeSpellout L t).isSome) :
    (spell L d).isSome := by
  induction d using List.reverseRecOn with
  | nil => rfl
  | append_singleton d t ih =>
    obtain ⟨xs, hxs⟩ := Option.isSome_iff_exists.1 (ih fun s hs ↦ h s (by simp [hs]))
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 (h t (by simp))
    rw [spell_concat, hxs, hx]
    cases (root (d ++ [t])).bind (treeSpellout L) <;> rfl

/-- The exponents the algorithm gives a feature sequence, in linear order. -/
def exponents (L : RuleSet (LexicalEntry (Option F) α)) (fs : List F) : Option (List α) :=
  (lexicalize L fs).bind (spell L)

/-! ### Soundness -/

private theorem isSome_of_mem_derivations {d d' : Derivation F} {fs : List F}
    (hd : ∀ t ∈ d, (treeSpellout L t).isSome) (h : d' ∈ derivations L d fs) :
    ∀ t ∈ d', (treeSpellout L t).isSome := by
  induction fs generalizing d with
  | nil => exact List.mem_singleton.1 h ▸ hd
  | cons f fs ih =>
    obtain ⟨d₁, h₁, h⟩ := List.mem_flatMap.1 h
    obtain ⟨j, -, hx, rfl⟩ := mem_mergeOptions.1 h₁
    refine ih (fun t ht ↦ ?_) h
    rcases List.mem_append.1 ht with ht | ht
    · exact hd t (List.mem_of_mem_take ht)
    · exact List.mem_singleton.1 ht ▸ hx

theorem exists_matches_of_mem_lexicalize {d : Derivation F} {fs : List F}
    (h : lexicalize L fs = some d) {t : RoseTree (Option F)} (ht : t ∈ d) :
    ∃ e ∈ L, e.Matches t := by
  have := isSome_of_mem_derivations (L := L) (d := []) (fun _ h ↦ absurd h List.not_mem_nil)
    (List.mem_of_mem_head? h) t ht
  by_contra hne
  exact absurd (treeSpellout_eq_none_iff.2 fun e he hm ↦ hne ⟨e, he, hm⟩) (by
    rw [← Option.not_isSome_iff_eq_none]; exact not_not.2 this)

theorem exponents_eq_none_iff {fs : List F} : exponents L fs = none ↔ lexicalize L fs = none := by
  rcases h : lexicalize L fs with - | d
  · simp [exponents, h]
  · have := spell_isSome (isSome_of_mem_derivations (L := L) (d := [])
      (fun _ h ↦ absurd h List.not_mem_nil) (List.mem_of_mem_head? h))
    obtain ⟨xs, hxs⟩ := Option.isSome_iff_exists.1 this
    simp [exponents, h, hxs]

/-! ### Short sequences -/

theorem exponents_singleton (L : RuleSet (LexicalEntry (Option F) α)) (f : F) :
    exponents L [f] = (treeSpellout L (leaf (some f))).map fun x ↦ [x] := by
  simp only [exponents, lexicalize, derivations_singleton, mergeOptions_nil]
  cases h : treeSpellout L (leaf (some f)) <;> simp [h]

theorem exponents_pair (L : RuleSet (LexicalEntry (Option F) α)) (f₁ f₂ : F) :
    exponents L [f₁, f₂] = (treeSpellout L (leaf (some f₁))).bind fun x ↦
      ((treeSpellout L (merge f₂ (leaf (some f₁)))).map fun y ↦ [y]) <|>
        (treeSpellout L (leaf (some f₂))).bind fun y ↦
          ((treeSpellout L (adjoin (leaf (some f₁)) (leaf (some f₂)))).map fun z ↦ [z]) <|>
            some [x, y] := by
  simp only [exponents, lexicalize, derivations_cons, derivations_nil, mergeOptions_nil]
  rcases h₁ : treeSpellout L (leaf (some f₁)) with - | x
  · rfl
  · simp only [Option.map_some, Option.toList_some, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, mergeOptions_singleton]
    rcases hw : treeSpellout L (merge f₂ (leaf (some f₁))) with - | y <;>
      rcases hs : treeSpellout L (leaf (some f₂)) with - | z
    · rfl
    · rcases ha : treeSpellout L (adjoin (leaf (some f₁)) (leaf (some f₂))) with - | w <;>
        simp [spell, spellAux, root, h₁, hs, ha]
    · simp [hw]
    · simp [hw]

/-! ### Lexicons without suffixes -/

theorem mergeOptions_singleton_of_leaf (h : treeSpellout L (leaf (some f)) = none)
    (t : RoseTree (Option F)) :
    mergeOptions L [t] f = ((treeSpellout L (merge f t)).map fun _ ↦ [merge f t]).toList := by
  simp [mergeOptions_singleton, h]

theorem derivations_cons_of_forall_leaf (f₀ : F) {fs : List F}
    (h : ∀ f ∈ fs, treeSpellout L (leaf (some f)) = none) :
    derivations L [] (f₀ :: fs) =
      ((treeSpellout L (spine f₀ fs)).map fun _ ↦ [spine f₀ fs]).toList := by
  induction fs using List.reverseRecOn with
  | nil => simp [mergeOptions_nil]
  | append_singleton fs f ih =>
    rw [← List.cons_append, derivations_append, ih fun g hg ↦ h g (List.mem_append_left _ hg),
      spine_concat]
    rcases hx : treeSpellout L (spine f₀ fs) with - | x
    · simp [treeSpellout_eq_none_of_isSubtree
        (.of_mem_children (t := merge f (spine f₀ fs)) (List.mem_singleton_self _)) hx]
    · simp [mergeOptions_singleton_of_leaf (h f (by simp))]

theorem exponents_cons_of_forall_leaf (f₀ : F) {fs : List F}
    (h : ∀ f ∈ fs, treeSpellout L (leaf (some f)) = none) :
    exponents L (f₀ :: fs) = (treeSpellout L (spine f₀ fs)).map fun x ↦ [x] := by
  rw [exponents, lexicalize, derivations_cons_of_forall_leaf f₀ h]
  cases h : treeSpellout L (spine f₀ fs) <;> simp [h]

section Containment

variable {n : ℕ} {feat : ℕ → F}

theorem exponents_ofSupersetRule (hf : feat.Injective)
    (v : RuleSet (Containment.SupersetRule n α)) (g : Fin n) :
    exponents (v.map (LexicalEntry.ofSupersetRule (some ∘ feat)))
        ((List.range ((g : ℕ) + 1)).map feat) =
      (Containment.spellout v g).map fun x ↦ [x] := by
  have hs : (some ∘ feat).Injective := (Option.some_injective F).comp hf
  rw [List.range_succ_eq_map, List.map_cons, List.map_map, exponents_cons_of_forall_leaf]
  · rw [spine, List.map_map, show phrase (some (feat 0)) (List.map (some ∘ feat ∘ Nat.succ)
      (List.range g)) = chainTree (some ∘ feat) g from (chainTree_eq_phrase (some ∘ feat) g).symm,
      treeSpellout_ofSupersetRule]
  · intro f hf'
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hf'
    refine treeSpellout_eq_none_iff.2 fun e he hm ↦ ?_
    obtain ⟨r, -, rfl⟩ := List.mem_map.1 he
    obtain ⟨j, -, hj⟩ := eq_chainTree_of_isSubtree hm
    obtain rfl : j = 0 := by simpa [chainTree_numNodes] using (congrArg numNodes hj).symm
    exact absurd (hs (node.inj hj).1) (Nat.succ_ne_zero k)

end Containment

end Morphology.Nanosyntax
