module

public import Linglib.Morphology.DistributedMorphology.Basic
public import Linglib.Morphology.DistributedMorphology.VocabularyInsertion.Basic

/-!
# Vocabulary Insertion from the inside out

Vocabulary Insertion targets the morphemes of a complex head, once each, from the inside out. At
each morpheme the context an item sees is the complex head as it then stands: the inner morphemes
realized, with their features and the morphophonological features of their exponents, and the
outer ones still bare. Which morphemes count as context is a locality regime, either the
concatenated neighbors after null exponents are pruned or every morpheme by hierarchical
distance. What insertion does to a morpheme's features is a second parameter: they persist, or
insertion rewrites the morpheme as its exponent and they are gone. The root is a morpheme whose
exponent is present from the start, and insertion targets the heads above it.

## Main definitions

* `DistributedMorphology.ComplexHead.order`, `DistributedMorphology.ComplexHead.exponents`: the
  positions of a complex head of morphemes in linear order, the surface of `ComplexHead.surface`,
  and its surface exponents.
* `DistributedMorphology.ComplexHead.Locality`, `DistributedMorphology.ComplexHead.Discharge`: the
  two regimes of context and the two fates of features.
* `DistributedMorphology.ComplexHead.contextAt`, `DistributedMorphology.ComplexHead.insertAt`,
  `DistributedMorphology.ComplexHead.insertAll`: the context a morpheme presents, insertion at one
  morpheme, and insertion from the inside out.

## Main results

* `insertAt_of_isRealized`, `exp_insertAll_of_eq_some`: Uniqueness — a
  realized morpheme is never realized again.
* `feats_insertAll_nondeletion`: under non-deletion, features survive
  insertion.
* `visible_insertUpTo_rewriting`: under rewriting, a realized morpheme keeps no
  features, so inward-looking conditioning sees exponents only.
* `exp_insertUpTo_of_le`, `visible_of_exp_none`: inside-out insertion leaves
  the outer morphemes bare, so outward-looking conditioning sees features
  only.
* `length_heads_insertAll`: insertion adds no morpheme.
* `nth_contextAt_hierarchical`, `nth_contextAt_hierarchical_root`: under
  hierarchy, head `j` stands at offset `j - i` from head `i` and the root at
  `-(i + 1)`.

## References

* [embick-2015]
* [embick-noyer-2007]
* [bobaljik-2000]
* [halle-1997]
-/

@[expose] public section

namespace DistributedMorphology

open Morphology (Morph)

namespace ComplexHead

variable {F E : Type*} (w : ComplexHead (Morpheme F E) (Morpheme F E))

/-! ### Linearization -/

/-- The positions of the complex head in linear order, the root at `none` and head `i` at
`some i`: the surface of the complex head of positions, each head on its morpheme's side. -/
def order : List (Option ℕ) :=
  (surface ⟨(), List.range w.heads.length⟩ fun i ↦ (w.heads[i]?.map (·.side)).getD .before).map
    (Sum.elim (fun _ ↦ none) some)

theorem order_eq : w.order =
    ((List.range w.heads.length).filter fun i ↦
      (w.heads[i]?.map (·.side)) = some .before).reverse.map some ++
    none :: ((List.range w.heads.length).filter fun i ↦
      (w.heads[i]?.map (·.side)) = some .after).map some := by
  have hb : ∀ i ∈ List.range w.heads.length,
      ((w.heads[i]?.map (·.side)).getD Morph.Side.before = .before) =
        ((w.heads[i]?.map (·.side)) = some .before) := fun i hi ↦ by
    rw [List.getElem?_eq_getElem (List.mem_range.1 hi)]
    simp
  have ha : ∀ i : ℕ, ((w.heads[i]?.map (·.side)).getD Morph.Side.before = .after) =
      ((w.heads[i]?.map (·.side)) = some Morph.Side.after) := fun i ↦ by
    cases w.heads[i]? <;> simp
  have hf : (List.range w.heads.length).filter (fun i ↦
        decide ((w.heads[i]?.map (·.side)).getD Morph.Side.before = .before)) =
      (List.range w.heads.length).filter (fun i ↦
        decide ((w.heads[i]?.map (·.side)) = some Morph.Side.before)) :=
    List.filter_congr fun i hi ↦ by simp only [hb i hi]
  simp only [order, surface_eq, List.map_append, List.map_cons, List.map_reverse, List.map_map,
    Function.comp_def, Sum.elim_inl, Sum.elim_inr, ha]
  rw [hf]

/-- The morpheme at a position. -/
def at? : Option ℕ → Option (Morpheme F E)
  | none => some w.root
  | some i => w.heads[i]?

/-- The surface exponents, in linear order. -/
def exponents : List E := w.order.filterMap fun p => (w.at? p).bind (·.exp)

/-! ### Context -/

/-- The context of a morpheme undergoing insertion is either its
concatenated neighbors, null exponents pruned, or every morpheme of the
complex head by hierarchical distance, inner and outer. -/
inductive Locality where
  /-- The concatenated neighbors, with null exponents pruned. -/
  | concatenation
  /-- Every morpheme, by hierarchical distance. -/
  | hierarchical
  deriving DecidableEq, Repr

/-- Insertion either leaves a morpheme's features in place or rewrites the
morpheme as its exponent, deleting them. -/
inductive Discharge where
  /-- Features survive insertion. -/
  | nondeletion
  /-- The morpheme's features are deleted on insertion. -/
  | rewriting
  deriving DecidableEq, Repr

variable [DecidableEq F]

/-- A morpheme presents as context its own features and, once realized, the
morphophonological features of its exponent. -/
def visible (expFeatures : E → Finset F) (s : Morpheme F E) : Finset F :=
  s.feats ∪ (s.exp.map expFeatures).getD ∅

@[simp] theorem visible_of_exp_none {expFeatures : E → Finset F} {s : Morpheme F E}
    (h : s.exp = none) : visible expFeatures s = s.feats := by
  simp [visible, h]

/-- A realized morpheme whose exponent is null is pruned from
concatenation. -/
def Pruned (isNull : E → Prop) (s : Morpheme F E) : Prop := ∃ e, s.exp = some e ∧ isNull e

instance (isNull : E → Prop) [DecidablePred isNull] (s : Morpheme F E) :
    Decidable (Pruned isNull s) :=
  match h : s.exp with
  | none => .isFalse (by simp [Pruned, h])
  | some e => decidable_of_iff (isNull e) (by simp [Pruned, h])

variable (isNull : E → Prop) [DecidablePred isNull]

/-- The linear order with pruned morphemes removed. -/
def concat : List (Option ℕ) :=
  w.order.filter fun p => ¬ ∃ s ∈ w.at? p, Pruned isNull s

/-- The concatenated neighbors of head `i` are the nearest unpruned
morphemes on its inner and outer sides, if any. -/
def neighbors (i : ℕ) : Option (Morpheme F E) × Option (Morpheme F E) :=
  let c := w.concat isNull
  match c.idxOf? (some i) with
  | none => (none, none)
  | some k =>
    let before := if k = 0 then none else (c[k - 1]?).bind w.at?
    let after := (c[k + 1]?).bind w.at?
    if (w.heads[i]?.map (·.side)) = some .before then (after, before) else (before, after)

/-- Head `i` presents its features in focus to Vocabulary Insertion, with
inner context on the left and outer on the right, nearest first. Under
concatenation the context is the unpruned neighbors, under hierarchy the
neighborhood of head `i` in the complex head read from the root outward. -/
def contextAt (loc : Locality) (expFeatures : E → Finset F) (i : ℕ) : Neighborhood (Finset F) :=
  match loc with
  | .concatenation =>
    let (inner, outer) := w.neighbors isNull i
    ⟨(w.heads[i]?.map (·.feats)).getD ∅, (inner.map fun s => [visible expFeatures s]).getD [],
      (outer.map fun s => [visible expFeatures s]).getD []⟩
  | .hierarchical =>
    .around ((w.root :: w.heads).map (visible expFeatures)) (i + 1)
      ((w.heads[i]?.map (·.feats)).getD ∅)

theorem nth_contextAt_hierarchical {expFeatures : E → Finset F} {i j : ℕ}
    (hi : i ≤ w.heads.length) (hj : j ≠ i) :
    (w.contextAt isNull .hierarchical expFeatures i).nth (j - i) =
      (w.heads.map (visible expFeatures)).getD j ∅ := by
  have := Neighborhood.nth_around ((w.root :: w.heads).map (visible expFeatures)) (i + 1)
    ((w.heads[i]?.map (·.feats)).getD ∅) (k := j + 1) (by simpa using hi) (by omega)
  simpa [contextAt, show ((j + 1 : ℕ) - (i + 1 : ℕ) : ℤ) = j - i by omega,
    show (default : Finset F) = ∅ from rfl] using this

theorem nth_contextAt_hierarchical_root {expFeatures : E → Finset F} {i : ℕ}
    (hi : i ≤ w.heads.length) :
    (w.contextAt isNull .hierarchical expFeatures i).nth (-(i + 1)) =
      visible expFeatures w.root := by
  have := Neighborhood.nth_around ((w.root :: w.heads).map (visible expFeatures)) (i + 1)
    ((w.heads[i]?.map (·.feats)).getD ∅) (k := 0) (by simpa using hi) (by omega)
  simpa [contextAt, show ((0 : ℕ) - (i + 1 : ℕ) : ℤ) = -(i + 1) by omega] using this

/-! ### Insertion -/

variable (vocab : List (VocabularyItem F E)) (loc : Locality)
  (expFeatures : E → Finset F) (dis : Discharge)

/-- Vocabulary Insertion at head `i` substitutes the Subset Principle's
winner for Q, once only; under rewriting it deletes the morpheme's
features. -/
def insertAt (i : ℕ) : ComplexHead (Morpheme F E) (Morpheme F E) :=
  match w.heads[i]? with
  | none => w
  | some s =>
    if s.IsRealized then w
    else
      match winner? vocab (w.contextAt isNull loc expFeatures i) with
      | none => w
      | some item =>
        let feats := match dis with
          | .nondeletion => s.feats
          | .rewriting => ∅
        let s' : Morpheme F E := { s with exp := some item.exponent, feats := feats }
        { w with heads := w.heads.set i s' }

/-- Insertion at the first `n` heads, from the inside out. -/
def insertUpTo (n : ℕ) : ComplexHead (Morpheme F E) (Morpheme F E) :=
  (List.range n).foldl (fun w i => w.insertAt isNull vocab loc expFeatures dis i) w

/-- Vocabulary Insertion from the inside out reaches every head in turn. -/
def insertAll : ComplexHead (Morpheme F E) (Morpheme F E) :=
  w.insertUpTo isNull vocab loc expFeatures dis w.heads.length

/-! ### Uniqueness and terminal insertion -/

variable {w vocab loc expFeatures dis}

@[simp] theorem insertUpTo_zero : w.insertUpTo isNull vocab loc expFeatures dis 0 = w := rfl

theorem insertUpTo_succ (n : ℕ) :
    w.insertUpTo isNull vocab loc expFeatures dis (n + 1) =
      (w.insertUpTo isNull vocab loc expFeatures dis n).insertAt isNull vocab loc expFeatures dis
        n := by
  simp [insertUpTo, List.range_succ]

@[simp] theorem root_insertAt (i : ℕ) :
    (w.insertAt isNull vocab loc expFeatures dis i).root = w.root := by
  unfold insertAt; split <;> (try split) <;> (try split) <;> rfl

@[simp] theorem length_heads_insertAt (i : ℕ) :
    (w.insertAt isNull vocab loc expFeatures dis i).heads.length = w.heads.length := by
  unfold insertAt; split <;> (try split) <;> (try split) <;> simp

theorem insertAt_of_isRealized {i : ℕ} {s : Morpheme F E} (hs : w.heads[i]? = some s)
    (h : s.IsRealized) : w.insertAt isNull vocab loc expFeatures dis i = w := by
  unfold insertAt; rw [hs]; simp [h]

theorem getElem?_heads_insertAt_of_ne {i j : ℕ} (h : i ≠ j) :
    (w.insertAt isNull vocab loc expFeatures dis i).heads[j]? = w.heads[j]? := by
  unfold insertAt; split <;> (try split) <;> (try split) <;> simp [List.getElem?_set_ne h]

theorem exp_insertAt_of_eq_some {i j : ℕ} {s : Morpheme F E} {e : E} (hs : w.heads[j]? = some s)
    (he : s.exp = some e) :
    ∃ s', (w.insertAt isNull vocab loc expFeatures dis i).heads[j]? = some s' ∧
      s'.exp = some e := by
  by_cases hij : i = j
  · subst hij
    rw [insertAt_of_isRealized isNull hs (by simp [Morpheme.IsRealized, he])]
    exact ⟨s, hs, he⟩
  · rw [getElem?_heads_insertAt_of_ne isNull hij]; exact ⟨s, hs, he⟩

theorem exp_insertUpTo_of_eq_some (n : ℕ) {j : ℕ} {s : Morpheme F E} {e : E}
    (hs : w.heads[j]? = some s) (he : s.exp = some e) :
    ∃ s', (w.insertUpTo isNull vocab loc expFeatures dis n).heads[j]? = some s' ∧
      s'.exp = some e := by
  induction n generalizing w with
  | zero => exact ⟨s, hs, he⟩
  | succ n ih =>
    rw [insertUpTo_succ]
    obtain ⟨s', hs', he'⟩ := ih hs
    exact exp_insertAt_of_eq_some isNull hs' he'

theorem exp_insertAll_of_eq_some {j : ℕ} {s : Morpheme F E} {e : E} (hs : w.heads[j]? = some s)
    (he : s.exp = some e) :
    ∃ s', (w.insertAll isNull vocab loc expFeatures dis).heads[j]? = some s' ∧
      s'.exp = some e :=
  exp_insertUpTo_of_eq_some isNull _ hs he

/-! ### Inside-out insertion -/

theorem exp_insertAt_of_lt {i j : ℕ} (hij : i < j) {s : Morpheme F E} (hs : w.heads[j]? = some s)
    (he : s.exp = none) :
    ∃ s', (w.insertAt isNull vocab loc expFeatures dis i).heads[j]? = some s' ∧
      s'.exp = none := by
  rw [getElem?_heads_insertAt_of_ne isNull hij.ne]; exact ⟨s, hs, he⟩

theorem exp_insertUpTo_of_le (n : ℕ) {j : ℕ} (hnj : n ≤ j) {s : Morpheme F E}
    (hs : w.heads[j]? = some s) (he : s.exp = none) :
    ∃ s', (w.insertUpTo isNull vocab loc expFeatures dis n).heads[j]? = some s' ∧
      s'.exp = none := by
  induction n generalizing w with
  | zero => exact ⟨s, hs, he⟩
  | succ n ih =>
    rw [insertUpTo_succ]
    obtain ⟨s', hs', he'⟩ := ih (Nat.le_of_succ_le hnj) hs
    exact exp_insertAt_of_lt isNull (Nat.lt_of_succ_le hnj) hs' he'

/-! ### Non-deletion -/

theorem feats_insertAt_nondeletion (i : ℕ) :
    (w.insertAt isNull vocab loc expFeatures .nondeletion i).heads.map (·.feats) =
      w.heads.map (·.feats) := by
  unfold insertAt
  cases hs : w.heads[i]? with
  | none => rfl
  | some s =>
    simp only
    split_ifs with hr
    · rfl
    cases winner? vocab (w.contextAt isNull loc expFeatures i) with
    | none => rfl
    | some item =>
      simp only [List.map_set]
      apply List.ext_getElem?
      intro k
      by_cases hk : i = k
      · subst hk
        rw [List.getElem?_set_self (by simpa using (List.getElem?_eq_some_iff.1 hs).1)]
        simp [hs]
      · rw [List.getElem?_set_ne hk]

theorem feats_insertUpTo_nondeletion (n : ℕ) :
    (w.insertUpTo isNull vocab loc expFeatures .nondeletion n).heads.map (·.feats) =
      w.heads.map (·.feats) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [insertUpTo_succ, feats_insertAt_nondeletion, ih]

theorem feats_insertAll_nondeletion :
    (w.insertAll isNull vocab loc expFeatures .nondeletion).heads.map (·.feats) =
      w.heads.map (·.feats) :=
  feats_insertUpTo_nondeletion isNull _

/-! ### Rewriting -/

theorem feats_insertAt_rewriting (h : ∀ s ∈ w.heads, s.IsRealized → s.feats = ∅) (i : ℕ) :
    ∀ s ∈ (w.insertAt isNull vocab loc expFeatures .rewriting i).heads,
      s.IsRealized → s.feats = ∅ := by
  unfold insertAt
  split
  · exact h
  split_ifs
  · exact h
  split
  · exact h
  intro s hs
  rcases List.mem_or_eq_of_mem_set hs with hs | rfl
  · exact h s hs
  · exact fun _ ↦ rfl

theorem feats_insertUpTo_rewriting (hw : ∀ s ∈ w.heads, s.exp = none) (n : ℕ) :
    ∀ s ∈ (w.insertUpTo isNull vocab loc expFeatures .rewriting n).heads,
      s.IsRealized → s.feats = ∅ := by
  induction n with
  | zero => intro s hs hr; simp [Morpheme.IsRealized, hw s hs] at hr
  | succ n ih => rw [insertUpTo_succ]; exact feats_insertAt_rewriting isNull ih n

theorem visible_insertUpTo_rewriting (hw : ∀ s ∈ w.heads, s.exp = none) (n : ℕ) {s : Morpheme F E}
    (hs : s ∈ (w.insertUpTo isNull vocab loc expFeatures .rewriting n).heads) {e : E}
    (he : s.exp = some e) : visible expFeatures s = expFeatures e := by
  simp [visible, he,
    feats_insertUpTo_rewriting isNull hw n s hs (by simp [Morpheme.IsRealized, he])]

theorem length_heads_insertUpTo (n : ℕ) :
    (w.insertUpTo isNull vocab loc expFeatures dis n).heads.length = w.heads.length := by
  induction n with
  | zero => rfl
  | succ n ih => rw [insertUpTo_succ, length_heads_insertAt, ih]

@[simp] theorem length_heads_insertAll :
    (w.insertAll isNull vocab loc expFeatures dis).heads.length = w.heads.length :=
  length_heads_insertUpTo isNull _

end ComplexHead

end DistributedMorphology
