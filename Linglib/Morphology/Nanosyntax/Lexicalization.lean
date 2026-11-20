module

public import Linglib.Morphology.Nanosyntax.TreeSpellout
public import Mathlib.Data.List.Monad

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

A syntactic object is built from `spine`, `merge` and `adjoin`, the last being the unlabelled
node an evacuated constituent forms with its remnant. `mergeOptions L d f` lists the ways of
lexicalizing the merger of the feature `f` with the derivation `d`, in order of preference, and
`derivations L d fs` folds it over the sequence `fs` in the list monad. Deriving `fs ++ gs` is
then deriving `fs` and, from each result in turn, `gs` (`derivations_append`), which is
backtracking. `lexicalize` returns the first derivation and `exponents` what `spell` pronounces
of it.

Every constituent of the derivation is matched by an entry (`exists_matches_of_mem_lexicalize`),
so a sequence the algorithm derives is pronounced (`exponents_eq_none_iff`). A sequence whose
spine an entry matches is lexicalized without movement (`lexicalize_cons_of_isSome`). Where no
entry lexicalizes a feature above the bottom alone the algorithm never evacuates
(`exponents_cons_of_forall_leaf`), so on a lexicon of containment entries its one exponent is the
containment engine's spellout (`exponents_ofSupersetRule`).

The subtrees of a spine are the spines of the initial parts of its sequence
(`isSubtree_spine_iff`), so an entry storing a spine shrinks to every smaller size. An entry
storing `adjoin (spine f₀ fs) r` matches the spines on `f₀` up to `fs` and no larger one
(`spine_isSubtree_adjoin_spine_iff`). Where no entry stores an unlabelled node, a sequence
pronounced with one exponent has every initial part pronounced with one exponent
(`exists_exponents_eq_singleton_of_prefix`).

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

open Morphology RoseTree

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

theorem value_spine_ne_none (f₀ : F) (fs : List F) : (spine f₀ fs).value ≠ none := by
  cases fs using List.reverseRecOn <;> simp

theorem spine_eq_spine_iff {f₀ g₀ : F} {fs gs : List F} :
    spine f₀ fs = spine g₀ gs ↔ f₀ = g₀ ∧ fs = gs := by
  simp [spine, phrase_eq_phrase_iff, (Option.some_injective F).list_map.eq_iff]

theorem spine_injective (f₀ : F) : Function.Injective (spine f₀) :=
  fun _ _ h ↦ (spine_eq_spine_iff.1 h).2

/-- The subtrees of a spine are the spines of the initial parts of its sequence. -/
theorem isSubtree_spine_iff {t : RoseTree (Option F)} {f₀ : F} {fs : List F} :
    IsSubtree t (spine f₀ fs) ↔ ∃ gs, gs <+: fs ∧ t = spine f₀ gs := by
  rw [spine, isSubtree_phrase_iff]
  constructor
  · rintro ⟨gs, h, rfl⟩
    refine ⟨fs.take gs.length, List.take_prefix _ _, ?_⟩
    rw [spine, List.map_take, ← List.prefix_iff_eq_take.1 h]
  · rintro ⟨gs, h, rfl⟩
    exact ⟨gs.map some, h.map some, rfl⟩

theorem spine_isSubtree_spine_iff {f₀ : F} {fs gs : List F} :
    IsSubtree (spine f₀ gs) (spine f₀ fs) ↔ gs <+: fs := by
  rw [isSubtree_spine_iff]
  exact ⟨fun ⟨_, h, he⟩ ↦ spine_injective f₀ he ▸ h, fun h ↦ ⟨gs, h, rfl⟩⟩

theorem isSubtree_adjoin_iff {t l r : RoseTree (Option F)} (ht : t.value ≠ none) :
    IsSubtree t (adjoin l r) ↔ IsSubtree t l ∨ IsSubtree t r := by
  rw [isSubtree_node_iff]
  simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left]
  exact or_iff_right fun h ↦ ht (h ▸ rfl)

/-- A spine standing beside a remnant with another foot contains the spines on its foot up to
its own size and no larger one. -/
theorem spine_isSubtree_adjoin_spine_iff {f₀ g₀ : F} (h : f₀ ≠ g₀) {fs gs hs : List F} :
    IsSubtree (spine f₀ gs) (adjoin (spine f₀ fs) (spine g₀ hs)) ↔ gs <+: fs := by
  rw [isSubtree_adjoin_iff (value_spine_ne_none _ _), spine_isSubtree_spine_iff, or_iff_left]
  rintro hr
  obtain ⟨ks, -, he⟩ := isSubtree_spine_iff.1 hr
  exact h (spine_eq_spine_iff.1 he).1

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
def derivations (L : RuleSet (LexicalEntry (Option F) α)) (d : Derivation F) (fs : List F) :
    List (Derivation F) :=
  fs.foldlM (mergeOptions L) d

@[simp] theorem derivations_nil (d : Derivation F) : derivations L d [] = [d] := rfl

@[simp] theorem derivations_cons (d : Derivation F) (f : F) (fs : List F) :
    derivations L d (f :: fs) = (mergeOptions L d f).flatMap (derivations L · fs) := rfl

theorem derivations_singleton (d : Derivation F) (f : F) :
    derivations L d [f] = mergeOptions L d f := by simp

/-- Deriving a sequence is deriving its first part and then the rest from each result in turn,
so a failure in the rest returns to the latest merger of the first part with an option left. -/
theorem derivations_append (d : Derivation F) (fs gs : List F) :
    derivations L d (fs ++ gs) = (derivations L d fs).flatMap (derivations L · gs) :=
  List.foldlM_append

theorem ne_nil_of_mem_mergeOptions {d d' : Derivation F} (h : d' ∈ mergeOptions L d f) :
    d' ≠ [] := by
  obtain ⟨j, -, -, rfl⟩ := mem_mergeOptions.1 h
  simp

theorem ne_nil_of_mem_derivations {d d' : Derivation F} {fs : List F} (hfs : fs ≠ [])
    (h : d' ∈ derivations L d fs) : d' ≠ [] := by
  induction fs generalizing d with
  | nil => exact absurd rfl hfs
  | cons f fs ih =>
    obtain ⟨d₁, h₁, h⟩ := List.mem_flatMap.1 h
    rcases fs with - | ⟨g, fs⟩
    · exact List.mem_singleton.1 h ▸ ne_nil_of_mem_mergeOptions h₁
    · exact ih (List.cons_ne_nil _ _) h

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

/-- Every constituent of the derivation the algorithm returns is matched by an entry. -/
theorem exists_matches_of_mem_lexicalize {d : Derivation F} {fs : List F}
    (h : lexicalize L fs = some d) {t : RoseTree (Option F)} (ht : t ∈ d) :
    ∃ e ∈ L, e.Matches t := by
  have := isSome_of_mem_derivations (L := L) (d := []) (fun _ h ↦ absurd h List.not_mem_nil)
    (List.mem_of_mem_head? h) t ht
  by_contra hne
  exact absurd (treeSpellout_eq_none_iff.2 fun e he hm ↦ hne ⟨e, he, hm⟩) (by
    rw [← Option.not_isSome_iff_eq_none]; exact not_not.2 this)

/-- A sequence the algorithm derives is pronounced. -/
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

/-! ### Lexicalization without movement -/

/-- A sequence whose spine an entry matches is lexicalized without movement, since each merger
tries the new phrase whole before any evacuation. -/
theorem lexicalize_cons_of_isSome (f₀ : F) {fs : List F}
    (h : (treeSpellout L (spine f₀ fs)).isSome) :
    lexicalize L (f₀ :: fs) = some [spine f₀ fs] := by
  rw [lexicalize]
  induction fs using List.reverseRecOn with
  | nil =>
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 h
    rw [spine_nil] at hx
    simp [mergeOptions_nil, hx]
  | append_singleton fs f ih =>
    rw [spine_concat] at h
    have hs : (treeSpellout L (spine f₀ fs)).isSome := by
      by_contra hn
      rw [treeSpellout_eq_none_of_isSubtree (.of_mem_children (t := merge f (spine f₀ fs))
        (List.mem_singleton_self _)) (by simpa using hn)] at h
      exact absurd h (by simp)
    obtain ⟨ds, hds⟩ := List.head?_eq_some_iff.1 (ih hs)
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 h
    rw [← List.cons_append, derivations_append, hds, spine_concat]
    simp [mergeOptions_singleton, hx]

theorem exponents_cons_of_eq_some (f₀ : F) {fs : List F} {x : α}
    (h : treeSpellout L (spine f₀ fs) = some x) : exponents L (f₀ :: fs) = some [x] := by
  rw [exponents, lexicalize_cons_of_isSome f₀ (by simp [h])]
  simp [h]

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

/-- Where no entry lexicalizes a feature above the bottom alone, the sequence gets a single
exponent, that of its one phrase, or none. -/
theorem exponents_cons_of_forall_leaf (f₀ : F) {fs : List F}
    (h : ∀ f ∈ fs, treeSpellout L (leaf (some f)) = none) :
    exponents L (f₀ :: fs) = (treeSpellout L (spine f₀ fs)).map fun x ↦ [x] := by
  rw [exponents, lexicalize, derivations_cons_of_forall_leaf f₀ h]
  cases h : treeSpellout L (spine f₀ fs) <;> simp [h]

/-! ### Lexicons without stored evacuation -/

section Labelled

variable (hL : ∀ e ∈ L, ∀ t, IsSubtree t e.tree → t.value ≠ none)
include hL

/-- Where no entry stores an unlabelled node, no entry matches an object of several
constituents, so each constituent of a derivation has an exponent of its own. -/
theorem length_of_spell_eq_some {d : Derivation F} {xs : List α} (h : spell L d = some xs) :
    xs.length = d.length := by
  induction d using List.reverseRecOn generalizing xs with
  | nil => simpa [eq_comm] using h
  | append_singleton d t ih =>
    rcases eq_or_ne d [] with rfl | hd
    · obtain ⟨x, -, rfl⟩ := Option.map_eq_some_iff.1 (by simpa using h)
      rfl
    · obtain ⟨u, hu⟩ : ∃ u, root d = some u := by
        obtain ⟨s, ts, rfl⟩ := List.exists_cons_of_ne_nil hd
        exact ⟨_, rfl⟩
      have hroot : root (d ++ [t]) = some (adjoin u t) := by rw [root_concat hd, hu]; rfl
      have hnone : treeSpellout L (adjoin u t) = none :=
        treeSpellout_eq_none_iff.2 fun e he hm ↦ hL e he _ hm rfl
      rcases hys : spell L d with - | ys <;> rcases hx : treeSpellout L t with - | x <;>
        simp [spell_concat, hroot, hnone, hys, hx] at h
      subst h
      simp [ih hys]

theorem eq_spine_of_mem_derivations {f₀ : F} {fs : List F} {d : Derivation F}
    (h : d ∈ derivations L [] (f₀ :: fs)) (hd : d.length = 1) : d = [spine f₀ fs] := by
  induction fs using List.reverseRecOn generalizing d with
  | nil =>
    rw [derivations_singleton, mergeOptions_nil] at h
    cases hx : treeSpellout L (leaf (some f₀)) <;> simp_all
  | append_singleton fs f ih =>
    rw [← List.cons_append, derivations_append] at h
    obtain ⟨d₁, h₁, h⟩ := List.mem_flatMap.1 h
    rw [derivations_singleton] at h
    have hle := length_le_of_mem_mergeOptions hL h
    have hpos := List.length_pos_iff.2 (ne_nil_of_mem_derivations (List.cons_ne_nil _ _) h₁)
    obtain rfl := ih h₁ (by omega)
    obtain ⟨j, hj, -, rfl⟩ := mem_mergeOptions.1 h
    obtain rfl : j = 0 := by
      simp only [List.length_append, List.length_take, List.length_singleton] at hd hj
      omega
    simp [root]

/-- Where no entry stores an unlabelled node, a sequence pronounced with one exponent has every
initial part pronounced with one exponent. A root that needs a suffix at one size and none at a
larger size therefore stores the structure evacuation builds. -/
theorem exists_exponents_eq_singleton_of_prefix {f₀ : F} {fs gs : List F} {x : α}
    (hgs : gs <+: fs) (h : exponents L (f₀ :: fs) = some [x]) :
    ∃ y, exponents L (f₀ :: gs) = some [y] := by
  obtain ⟨d, hd, hs⟩ := Option.bind_eq_some_iff.1 h
  obtain rfl := eq_spine_of_mem_derivations hL (List.mem_of_mem_head? hd)
    (length_of_spell_eq_some hL hs).symm
  have hx : treeSpellout L (spine f₀ fs) = some x := by simpa using hs
  rcases hy : treeSpellout L (spine f₀ gs) with - | y
  · rw [treeSpellout_eq_none_of_isSubtree (spine_isSubtree_spine_iff.2 hgs) hy] at hx
    exact absurd hx (by simp)
  · exact ⟨y, exponents_cons_of_eq_some f₀ hy⟩

end Labelled

section Containment

variable {n : ℕ} {feat : ℕ → F}

/-- On a lexicon of containment entries the algorithm never evacuates, and it gives each grade
the single exponent the containment engine spells out there. -/
theorem exponents_ofSupersetRule (hf : feat.Injective)
    (v : RuleSet (SupersetRule n α)) (g : Fin n) :
    exponents (v.map (LexicalEntry.ofSupersetRule (some ∘ feat)))
        ((List.range ((g : ℕ) + 1)).map feat) =
      (SupersetRule.spellout v g).map fun x ↦ [x] := by
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
