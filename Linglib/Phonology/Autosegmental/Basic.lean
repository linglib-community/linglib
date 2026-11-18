/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.Algebra.Group.Embedding
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Fin.Embedding
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Pi
public import Linglib.Phonology.Autosegmental.NonCrossing

/-!
# Autosegmental representations

An autosegmental representation has a word on each tier and association lines joining positions
on distinct tiers. The lines between two tiers are a finite set of pairs of positions, so a
representation is finite data: its lines can be listed, counted and edited, and equality and the
No-Crossing Constraint are decidable. Association is also
[a simple graph on the positions](##Autosegmental.AR.assoc), the form in which the graph-theoretic
statements read it. Representations concatenate tier by tier, appending the words and keeping
[the lines of both factors](##Autosegmental.AR.link_mul), and form a monoid in which
representations on disjoint tiers [commute](##Autosegmental.AR.commute_of_disjoint_support).
Concatenation and monotone moves of the positions preserve
[the No-Crossing Constraint](##Autosegmental.AR.NoCrossing.mul).

## Implementation notes

The lines from tier `i` to tier `j` are stored as pairs of natural numbers with a proof that they
are in range, as a `Finset` stores a multiset with a proof that it has no duplicates, so
concatenation is a union and a shift, with no cast along the length of an appended word. Both
orientations of a pair of tiers are stored, tied by `AR.swap_mem_lines`, as `SimpleGraph` stores
a symmetric adjacency relation: the No-Crossing Constraint reads the lines of one ordered pair of
tiers, and no operation needs to decide equality of tiers. The alternative of a `SimpleGraph` on
the positions with a decidability instance cannot be enumerated, and its instance does not
survive `List.prod`.

## References

* [goldsmith-1976]
* [coleman-local-1991]
* [mccarthy-1989]
* [jardine-heinz-2015]
* [jardine-2019]
-/

@[expose] public section

namespace Autosegmental

variable {ι : Type*} {τ : ι → Type*}

/-- An autosegmental representation: a word on each tier, and for each pair of tiers the finite
set of association lines between their positions. -/
structure AR (τ : ι → Type*) where
  /-- The word on tier `i`. -/
  word : ∀ i, List (τ i)
  /-- The lines from tier `i` to tier `j`, each a position of `i` and a position of `j`. -/
  lines : ι → ι → Finset (ℕ × ℕ)
  /-- No line joins two positions of one tier. -/
  lines_self (i : ι) : lines i i = ∅
  /-- A line from `i` to `j` is a line from `j` to `i`. -/
  swap_mem_lines ⦃i j : ι⦄ ⦃p q : ℕ⦄ : (p, q) ∈ lines i j → (q, p) ∈ lines j i
  /-- Lines start at positions of the word. -/
  fst_lt_of_mem_lines ⦃i j : ι⦄ ⦃p q : ℕ⦄ : (p, q) ∈ lines i j → p < (word i).length

namespace AR

variable (X Y Z : AR τ)

/-- The positions of a representation: a tier and an index into its word. -/
abbrev Pos : Type _ := (i : ι) × Fin (X.word i).length

/-- The label at a position. -/
def label (v : X.Pos) : τ v.1 := (X.word v.1)[v.2]

/-! ### Lines -/

/-- Position `p` of tier `i` is associated with position `q` of tier `j`; positions beyond the
end of a word are associated with nothing. -/
def Link (i j : ι) (p q : ℕ) : Prop := (p, q) ∈ X.lines i j

instance (i j : ι) (p q : ℕ) : Decidable (X.Link i j p q) :=
  inferInstanceAs (Decidable (_ ∈ _))

variable {X Y Z}

theorem mem_lines {i j : ι} {p q : ℕ} : (p, q) ∈ X.lines i j ↔ X.Link i j p q := .rfl

theorem Link.lt_left {i j : ι} {p q : ℕ} (h : X.Link i j p q) : p < (X.word i).length :=
  X.fst_lt_of_mem_lines h

theorem Link.symm {i j : ι} {p q : ℕ} (h : X.Link i j p q) : X.Link j i q p :=
  X.swap_mem_lines h

theorem Link.lt_right {i j : ι} {p q : ℕ} (h : X.Link i j p q) : q < (X.word j).length :=
  h.symm.lt_left

theorem Link.ne {i j : ι} {p q : ℕ} (h : X.Link i j p q) : i ≠ j := by
  rintro rfl
  simp [Link, X.lines_self] at h

theorem link_comm {i j : ι} {p q : ℕ} : X.Link i j p q ↔ X.Link j i q p := ⟨.symm, .symm⟩

theorem lines_injective : Function.Injective fun X : AR τ ↦ (X.word, X.lines) := by
  rintro ⟨_, _, _, _, _⟩ ⟨_, _, _, _, _⟩ h
  cases h
  rfl

@[ext] theorem ext (hw : X.word = Y.word) (hl : ∀ i j p q, X.Link i j p q ↔ Y.Link i j p q) :
    X = Y :=
  lines_injective <| Prod.ext hw <| funext₂ fun i j ↦ Finset.ext fun ⟨p, q⟩ ↦ hl i j p q

instance [Fintype ι] [∀ i, DecidableEq (τ i)] : DecidableEq (AR τ) :=
  fun X Y ↦ decidable_of_iff (X.word = Y.word ∧ X.lines = Y.lines)
    ⟨fun h ↦ lines_injective (Prod.ext h.1 h.2), fun h ↦ h ▸ ⟨rfl, rfl⟩⟩

/-! ### The graph on the positions -/

variable (X) in
/-- Association as a simple graph on the positions. -/
def assoc : SimpleGraph X.Pos where
  Adj v w := X.Link v.1 w.1 v.2 w.2
  symm := ⟨fun _ _ h ↦ h.symm⟩
  loopless := ⟨fun _ h ↦ h.ne rfl⟩

instance : DecidableRel X.assoc.Adj :=
  fun v w ↦ inferInstanceAs (Decidable (X.Link v.1 w.1 v.2 w.2))

theorem link_iff_adj {v w : X.Pos} : X.Link v.1 w.1 v.2 w.2 ↔ X.assoc.Adj v w := .rfl

theorem Link.adj {i j : ι} {p q : ℕ} (h : X.Link i j p q) :
    X.assoc.Adj ⟨i, ⟨p, h.lt_left⟩⟩ ⟨j, ⟨q, h.lt_right⟩⟩ := h

theorem fst_ne_of_adj {v w : X.Pos} (h : X.assoc.Adj v w) : v.1 ≠ w.1 := Link.ne h

/-! ### Lines as pairs of positions -/

section Links

variable (X) (i j : ι)

/-- The lines from tier `i` to tier `j` as pairs of positions of the two words, the view that
candidates edit. -/
def links : Finset (Fin (X.word i).length × Fin (X.word j).length) :=
  Finset.univ.filter fun x ↦ (x.1.val, x.2.val) ∈ X.lines i j

variable {X i j}

@[simp] theorem mem_links {x : Fin (X.word i).length × Fin (X.word j).length} :
    x ∈ X.links i j ↔ (x.1.val, x.2.val) ∈ X.lines i j := by
  simp [links]

variable (X i j) in
theorem map_links :
    (X.links i j).map (Fin.valEmbedding.prodMap Fin.valEmbedding) = X.lines i j := by
  ext ⟨a, b⟩
  simp only [Finset.mem_map, mem_links, Function.Embedding.prodMap, Prod.exists,
    Function.Embedding.coeFn_mk, Prod.map, Fin.valEmbedding_apply, Prod.mk.injEq]
  constructor
  · rintro ⟨k, l, h, rfl, rfl⟩
    exact h
  · intro h
    exact ⟨⟨a, Link.lt_left h⟩, ⟨b, Link.lt_right h⟩, h, rfl, rfl⟩

theorem isNonCrossing_lines_iff_links :
    IsNonCrossing (X.lines i j : SetRel ℕ ℕ) ↔
      IsNonCrossing (X.links i j : SetRel (Fin (X.word i).length) (Fin (X.word j).length)) := by
  rw [← map_links, Finset.coe_map, isNonCrossing_image]
  rfl

end Links

/-! ### Representations from words and a graph -/

section OfAssoc

variable (w : ∀ i, List (τ i)) (G : SimpleGraph ((i : ι) × Fin (w i).length))
  [DecidableRel G.Adj] (hG : ∀ ⦃v v'⦄, G.Adj v v' → v.1 ≠ v'.1)

/-- The representation with words `w` whose association is a given graph on the positions that
joins only distinct tiers. -/
def ofAssoc : AR τ where
  word := w
  lines i j := (Finset.univ.filter fun x : Fin (w i).length × Fin (w j).length ↦
    G.Adj ⟨i, x.1⟩ ⟨j, x.2⟩).map (Fin.valEmbedding.prodMap Fin.valEmbedding)
  lines_self i := Finset.eq_empty_of_forall_notMem fun _ h ↦ by
    obtain ⟨x, hx, -⟩ := Finset.mem_map.1 h
    exact hG (Finset.mem_filter.1 hx).2 rfl
  swap_mem_lines i j p q h := by
    obtain ⟨x, hx, he⟩ := Finset.mem_map.1 h
    cases he
    exact Finset.mem_map.2 ⟨(x.2, x.1), Finset.mem_filter.2
      ⟨Finset.mem_univ _, (Finset.mem_filter.1 hx).2.symm⟩, rfl⟩
  fst_lt_of_mem_lines i j p q h := by
    obtain ⟨x, -, he⟩ := Finset.mem_map.1 h
    cases he
    exact x.1.2

@[simp] theorem word_ofAssoc : (ofAssoc w G hG).word = w := rfl

/-- The graph of `ofAssoc` is the given graph. -/
@[simp] theorem assoc_ofAssoc : (ofAssoc w G hG).assoc = G :=
  SimpleGraph.ext <| funext₂ fun v v' ↦ propext
    ⟨fun h ↦ by
      obtain ⟨x, hx, he⟩ := Finset.mem_map.1 h
      obtain ⟨h₁, h₂⟩ := Prod.ext_iff.1 he
      rw [← Sigma.eta v, ← Sigma.eta v', ← Fin.ext h₁, ← Fin.ext h₂]
      exact (Finset.mem_filter.1 hx).2,
    fun h ↦ Finset.mem_map.2 ⟨(v.2, v'.2), Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩, rfl⟩⟩

/-- A representation is determined by its words and its graph. -/
theorem ofAssoc_assoc (X : AR τ) : ofAssoc X.word X.assoc (fun _ _ ↦ fst_ne_of_adj) = X :=
  ext rfl fun i j p q ↦
    ⟨fun h ↦ by
      obtain ⟨x, hx, he⟩ := Finset.mem_map.1 h
      cases he
      exact (Finset.mem_filter.1 hx).2,
    fun h ↦ Finset.mem_map.2
      ⟨(⟨p, h.lt_left⟩, ⟨q, h.lt_right⟩), Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩, rfl⟩⟩

end OfAssoc

/-! ### Concatenation -/

section Monoid

/-- `shift a b` moves a line `a` positions along its first tier and `b` along its second. -/
def shift (a b : ℕ) : ℕ × ℕ ↪ ℕ × ℕ := (addLeftEmbedding a).prodMap (addLeftEmbedding b)

@[simp] theorem shift_apply (a b : ℕ) (p : ℕ × ℕ) : shift a b p = (a + p.1, b + p.2) := rfl

/-- Concatenation appends the words tier by tier and keeps the lines of both factors, those of
the right factor shifted past the words of the left one. -/
instance : Mul (AR τ) where
  mul X Y :=
    { word i := X.word i ++ Y.word i
      lines i j := X.lines i j ∪ (Y.lines i j).map (shift (X.word i).length (X.word j).length)
      lines_self i := by simp [X.lines_self, Y.lines_self]
      swap_mem_lines i j p q h := by
        simp only [Finset.mem_union, Finset.mem_map, shift_apply, Prod.mk.injEq,
          Prod.exists] at h ⊢
        rcases h with h | ⟨a, b, h, rfl, rfl⟩
        · exact .inl (X.swap_mem_lines h)
        · exact .inr ⟨b, a, Y.swap_mem_lines h, rfl, rfl⟩
      fst_lt_of_mem_lines i j p q h := by
        simp only [Finset.mem_union, Finset.mem_map, shift_apply, Prod.mk.injEq, Prod.exists] at h
        rcases h with h | ⟨a, b, h, rfl, rfl⟩
        · have := X.fst_lt_of_mem_lines h
          simp only [List.length_append]
          omega
        · have := Y.fst_lt_of_mem_lines h
          simp only [List.length_append]
          omega }

/-- The empty representation. -/
instance : One (AR τ) := ⟨⟨fun _ ↦ [], fun _ _ ↦ ∅, fun _ ↦ rfl, nofun, nofun⟩⟩

instance : Inhabited (AR τ) := ⟨1⟩

@[simp] theorem word_mul (i : ι) : (X * Y).word i = X.word i ++ Y.word i := rfl

@[simp] theorem lines_mul (i j : ι) : (X * Y).lines i j =
    X.lines i j ∪ (Y.lines i j).map (shift (X.word i).length (X.word j).length) := rfl

@[simp] theorem word_one (i : ι) : (1 : AR τ).word i = [] := rfl

@[simp] theorem lines_one (i j : ι) : (1 : AR τ).lines i j = ∅ := rfl

@[simp] theorem not_link_one (i j : ι) (p q : ℕ) : ¬ (1 : AR τ).Link i j p q :=
  Finset.notMem_empty _

@[simp] theorem assoc_one : (1 : AR τ).assoc = ⊥ :=
  SimpleGraph.ext <| funext₂ fun _ _ ↦ propext ⟨fun h ↦ (not_link_one _ _ _ _ h).elim, False.elim⟩

theorem link_mul (i j : ι) (p q : ℕ) :
    (X * Y).Link i j p q ↔ X.Link i j p q ∨
      (X.word i).length ≤ p ∧ (X.word j).length ≤ q ∧
        Y.Link i j (p - (X.word i).length) (q - (X.word j).length) := by
  simp only [Link, lines_mul, Finset.mem_union, Finset.mem_map, shift_apply, Prod.mk.injEq,
    Prod.exists]
  refine or_congr_right ⟨?_, fun ⟨hp, hq, h⟩ ↦ ⟨_, _, h, by omega, by omega⟩⟩
  rintro ⟨a, b, h, rfl, rfl⟩
  exact ⟨by omega, by omega, by simpa using h⟩

instance : Monoid (AR τ) where
  mul_assoc X Y Z := by
    refine ext (funext fun i ↦ List.append_assoc ..) fun i j p q ↦ ?_
    simp only [link_mul, word_mul, List.length_append, Nat.sub_sub]
    constructor
    · rintro ((h | ⟨hp, hq, h⟩) | ⟨hp, hq, h⟩)
      exacts [.inl h, .inr ⟨hp, hq, .inl h⟩,
        .inr ⟨by omega, by omega, .inr ⟨by omega, by omega, h⟩⟩]
    · rintro (h | ⟨hp, hq, h | ⟨hp', hq', h⟩⟩)
      exacts [.inl (.inl h), .inl (.inr ⟨hp, hq, h⟩), .inr ⟨by omega, by omega, h⟩]
  one_mul X := ext rfl fun i j p q ↦ by simp [link_mul]
  mul_one X := ext (funext fun i ↦ List.append_nil _) fun i j p q ↦ by
    simp only [link_mul, not_link_one, and_false, or_false]

variable (X) in
/-- The support of a representation, the tiers whose words are nonempty. -/
def support : Set ι := {i | X.word i ≠ []}

@[simp] theorem mem_support {i : ι} : i ∈ X.support ↔ X.word i ≠ [] := .rfl

@[simp] theorem support_mul : (X * Y).support = X.support ∪ Y.support := by
  ext i
  simp only [mem_support, word_mul, ne_eq, List.append_eq_nil_iff, not_and_or, Set.mem_union]

@[simp] theorem support_one : (1 : AR τ).support = ∅ := by
  ext i
  simp

theorem Link.mem_support_left {i j : ι} {p q : ℕ} (h : X.Link i j p q) : i ∈ X.support :=
  List.ne_nil_of_length_pos (Nat.zero_lt_of_lt h.lt_left)

theorem Link.mem_support_right {i j : ι} {p q : ℕ} (h : X.Link i j p q) : j ∈ X.support :=
  List.ne_nil_of_length_pos (Nat.zero_lt_of_lt h.lt_right)

/-- Representations with disjoint supports commute: concatenation orders material only within a
tier, so morphs on separate planes are unordered ([mccarthy-1989], p. 73). -/
theorem commute_of_disjoint_support (h : Disjoint X.support Y.support) : Commute X Y := by
  have hX {i j : ι} {p q : ℕ} (hl : X.Link i j p q) : Y.word i = [] ∧ Y.word j = [] :=
    ⟨not_not.1 (Set.disjoint_left.1 h hl.mem_support_left),
      not_not.1 (Set.disjoint_left.1 h hl.mem_support_right)⟩
  have hY {i j : ι} {p q : ℕ} (hl : Y.Link i j p q) : X.word i = [] ∧ X.word j = [] :=
    ⟨not_not.1 (Set.disjoint_right.1 h hl.mem_support_left),
      not_not.1 (Set.disjoint_right.1 h hl.mem_support_right)⟩
  refine ext (funext fun i ↦ ?_) fun i j p q ↦ ?_
  · by_cases hx : X.word i = []
    · simp [hx]
    · simp [not_not.1 (Set.disjoint_left.1 h hx)]
  · simp only [link_mul]
    constructor
    · rintro (hl | ⟨-, -, hl⟩)
      · obtain ⟨hi, hj⟩ := hX hl
        exact .inr ⟨by simp [hi], by simp [hj], by simpa [hi, hj] using hl⟩
      · obtain ⟨hi, hj⟩ := hY hl
        exact .inl (by simpa [hi, hj] using hl)
    · rintro (hl | ⟨-, -, hl⟩)
      · obtain ⟨hi, hj⟩ := hY hl
        exact .inr ⟨by simp [hi], by simp [hj], by simpa [hi, hj] using hl⟩
      · obtain ⟨hi, hj⟩ := hX hl
        exact .inl (by simpa [hi, hj] using hl)

/-- The word on tier `i`, as a monoid hom. -/
def wordHom (i : ι) : AR τ →* FreeMonoid (τ i) where
  toFun X := .ofList (X.word i)
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem wordHom_apply (i : ι) : wordHom i X = .ofList (X.word i) := rfl

theorem wordHom_comp_lift {S : Type*} (g₀ : S → AR τ) (i : ι) :
    (wordHom i).comp (FreeMonoid.lift g₀) = FreeMonoid.lift fun s ↦ wordHom i (g₀ s) :=
  FreeMonoid.hom_eq fun _ ↦ rfl

end Monoid

/-! ### The No-Crossing Constraint -/

variable (X) in
/-- The No-Crossing Constraint: between any two tiers, no two lines cross. -/
def NoCrossing : Prop := ∀ i j, IsNonCrossing (X.lines i j : SetRel ℕ ℕ)

instance [Fintype ι] : Decidable X.NoCrossing :=
  inferInstanceAs (Decidable (∀ i j, IsNonCrossing (X.lines i j : SetRel ℕ ℕ)))

@[simp] theorem NoCrossing.one : (1 : AR τ).NoCrossing := fun _ _ _ h ↦ by simp at h

theorem isNonCrossing_lines_iff {i j : ι} : IsNonCrossing (X.lines i j : SetRel ℕ ℕ) ↔
    ∀ ⦃p q p' q'⦄, X.Link i j p q → X.Link i j p' q' → p < p' → q ≤ q' :=
  ⟨fun h _ _ _ _ h₁ h₂ ↦ h h₁ h₂, fun h _ ha _ hb ↦ h ha hb⟩

theorem isNonCrossing_lines_self (i : ι) : IsNonCrossing (X.lines i i : SetRel ℕ ℕ) :=
  isNonCrossing_lines_iff.2 fun _ _ _ _ h ↦ absurd rfl h.ne

theorem isNonCrossing_lines_comm {i j : ι} :
    IsNonCrossing (X.lines i j : SetRel ℕ ℕ) ↔ IsNonCrossing (X.lines j i : SetRel ℕ ℕ) := by
  simp only [isNonCrossing_lines_iff]
  exact ⟨fun h _ _ _ _ h₁ h₂ hlt ↦ le_of_not_gt fun hgt ↦ (h h₂.symm h₁.symm hgt).not_gt hlt,
    fun h _ _ _ _ h₁ h₂ hlt ↦ le_of_not_gt fun hgt ↦ (h h₂.symm h₁.symm hgt).not_gt hlt⟩

/-- Concatenation keeps the lines between two tiers non-crossing. -/
theorem isNonCrossing_lines_mul {i j : ι} (hX : IsNonCrossing (X.lines i j : SetRel ℕ ℕ))
    (hY : IsNonCrossing (Y.lines i j : SetRel ℕ ℕ)) :
    IsNonCrossing ((X * Y).lines i j : SetRel ℕ ℕ) :=
  isNonCrossing_lines_iff.2 fun p q p' q' h₁ h₂ hlt ↦ by
    replace hX := isNonCrossing_lines_iff.1 hX
    replace hY := isNonCrossing_lines_iff.1 hY
    rcases (link_mul i j p q).1 h₁ with h₁ | ⟨hp, hq, h₁⟩ <;>
      rcases (link_mul i j p' q').1 h₂ with h₂ | ⟨hp', hq', h₂⟩
    · exact hX h₁ h₂ hlt
    · exact (h₁.lt_right.trans_le hq').le
    · exact absurd (h₂.lt_left.trans_le hp) (by omega)
    · have := hY h₁ h₂ (by omega)
      omega

/-- Concatenation preserves the No-Crossing Constraint. With `NoCrossing.repoint` under the
merge this gives the inductive step of [jardine-heinz-2015]'s Theorem 4 for their merging
concatenation, `MergeAR.noCrossing_toAR_mul`. -/
theorem NoCrossing.mul (hX : X.NoCrossing) (hY : Y.NoCrossing) : (X * Y).NoCrossing :=
  fun i j ↦ isNonCrossing_lines_mul (hX i j) (hY i j)

/-! ### Moving positions -/

section Map

variable (w : ∀ i, List (τ i)) (f g : ι → ℕ → ℕ)
  (hf : ∀ i, ∀ p < (X.word i).length, f i p < (w i).length)

variable (X) in
/-- The representation with words `w` whose lines are those of `X`, each position moved
along `f` on its tier; positions merged by `f` keep the lines of all of them. -/
def map : AR τ where
  word := w
  lines i j := (X.lines i j).image (Prod.map (f i) (f j))
  lines_self i := by simp [X.lines_self]
  swap_mem_lines i j p q h := by
    simp only [Finset.mem_image, Prod.map, Prod.mk.injEq, Prod.exists] at h ⊢
    obtain ⟨a, b, h, rfl, rfl⟩ := h
    exact ⟨b, a, X.swap_mem_lines h, rfl, rfl⟩
  fst_lt_of_mem_lines i j p q h := by
    simp only [Finset.mem_image, Prod.map, Prod.mk.injEq, Prod.exists] at h
    obtain ⟨a, b, h, rfl, rfl⟩ := h
    exact hf i a (X.fst_lt_of_mem_lines h)

@[simp] theorem word_map : (X.map w f hf).word = w := rfl

theorem lines_map (i j : ι) :
    (X.map w f hf).lines i j = (X.lines i j).image (Prod.map (f i) (f j)) := rfl

variable {w f hf} in
theorem link_map {i j : ι} {r s : ℕ} :
    (X.map w f hf).Link i j r s ↔ ∃ p q, X.Link i j p q ∧ f i p = r ∧ f j q = s := by
  simp [Link, map]

/-- A move depends only on where it sends the positions of the words. -/
theorem map_congr (hg : ∀ i, ∀ p < (X.word i).length, g i p < (w i).length)
    (h : ∀ i, ∀ p < (X.word i).length, f i p = g i p) : X.map w f hf = X.map w g hg :=
  ext rfl fun i j r s ↦ by
    simp only [link_map]
    constructor <;> rintro ⟨p, q, hl, rfl, rfl⟩
    · exact ⟨p, q, hl, (h i p hl.lt_left).symm, (h j q hl.lt_right).symm⟩
    · exact ⟨p, q, hl, h i p hl.lt_left, h j q hl.lt_right⟩

/-- Moving positions monotonically preserves the No-Crossing Constraint. -/
theorem NoCrossing.map (hmono : ∀ i, MonotoneOn (f i) (Set.Iio (X.word i).length))
    (h : X.NoCrossing) : (X.map w f hf).NoCrossing := fun i j ↦
  isNonCrossing_lines_iff.2 fun r s r' s' h₁ h₂ hlt ↦ by
    obtain ⟨p, q, hl, rfl, rfl⟩ := link_map.1 h₁
    obtain ⟨p', q', hl', rfl, rfl⟩ := link_map.1 h₂
    have hpp' : p < p' := lt_of_not_ge fun hge ↦
      (hmono i hl'.lt_left hl.lt_left hge).not_gt hlt
    exact hmono j hl.lt_right hl'.lt_right (isNonCrossing_lines_iff.1 (h i j) hl hl' hpp')

variable (X) in
@[simp] theorem map_id : X.map X.word (fun _ ↦ id) (fun _ _ h ↦ h) = X :=
  ext rfl fun i j p q ↦ by simp [link_map]

end Map

/-! ### Representations from words and a relation -/

section FromRel

variable [DecidableEq ι] (w : ∀ i, List (τ i)) (L : ι → ι → ℕ → ℕ → Prop)
  [∀ i j, DecidableRel (L i j)]

/-- The representation with words `w` and a line between positions on distinct tiers wherever
`L` holds in either direction. -/
def fromRel : AR τ where
  word := w
  lines i j := if i = j then ∅ else
    (Finset.range (w i).length ×ˢ Finset.range (w j).length).filter
      fun x ↦ L i j x.1 x.2 ∨ L j i x.2 x.1
  lines_self i := by simp
  swap_mem_lines i j p q h := by
    split_ifs at h ⊢ with hij hji hji
    · simp at h
    · exact absurd hij.symm hji
    · exact absurd hji.symm hij
    · simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at h ⊢
      tauto
  fst_lt_of_mem_lines i j p q h := by
    split_ifs at h
    · simp at h
    · simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at h
      exact h.1.1

@[simp] theorem word_fromRel : (fromRel w L).word = w := rfl

variable {w L} in
@[simp] theorem link_fromRel {i j : ι} {p q : ℕ} :
    (fromRel w L).Link i j p q ↔
      i ≠ j ∧ p < (w i).length ∧ q < (w j).length ∧ (L i j p q ∨ L j i q p) := by
  simp only [Link, fromRel]
  split_ifs with h
  · simp [h]
  · simp [h, and_assoc]

end FromRel

end AR

end Autosegmental
