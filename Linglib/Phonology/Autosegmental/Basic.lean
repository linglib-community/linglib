/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.Logic.Equiv.Fin.Basic
public import Linglib.Core.Combinatorics.SimpleGraph.Sum
public import Linglib.Phonology.Autosegmental.NonCrossing

/-!
# Autosegmental representations

An autosegmental representation has a word on each tier and association lines joining positions
on distinct tiers. Representations concatenate tier by tier, appending the words and keeping the
lines of both factors, and form a monoid.

## Main definitions

* `AR τ`: a representation with alphabet `τ i` on tier `i`.
* `AR.Link`: association of two positions given in `ℕ` coordinates.
* `AR.NoCrossing`: the No-Crossing Constraint.
* `AR.fromRel`: the representation with given words and the lines a relation specifies.
* `AR.map`: a representation with its positions moved along maps of each tier.
* `AR.wordHom`: the word on one tier, as a monoid hom.

## Main results

* `AR.link_mul`: the lines of a concatenation are those of its factors, the right factor's
  shifted past the left one.
* `AR.NoCrossing.mul`, `AR.NoCrossing.map`: concatenation and monotone moves preserve the
  No-Crossing Constraint.

## References

* [goldsmith-1976]
* [coleman-local-1991]
* [jardine-heinz-2015]
* [jardine-2019]
-/

@[expose] public section

namespace Autosegmental

variable {ι : Type*} {τ : ι → Type*}

/-- An autosegmental representation: a word on each tier, and association lines between
positions on distinct tiers. -/
structure AR (τ : ι → Type*) where
  /-- The word on tier `i`. -/
  word : ∀ i, List (τ i)
  /-- The association lines, a graph on the positions. -/
  assoc : SimpleGraph ((i : ι) × Fin (word i).length)
  /-- Lines join distinct tiers: association lies in the complete multipartite graph on the
  tiers. -/
  assoc_le : assoc ≤ SimpleGraph.completeMultipartiteGraph fun i ↦ Fin (word i).length
  /-- Association is decidable. -/
  decidableAdj : DecidableRel assoc.Adj := by infer_instance

attribute [instance] AR.decidableAdj

namespace AR

variable (X Y Z : AR τ)

/-- The positions of a representation: a tier and an index into its word. -/
abbrev Pos : Type _ := (i : ι) × Fin (X.word i).length

/-- The label at a position. -/
def label (v : X.Pos) : τ v.1 := (X.word v.1)[v.2]

instance : Inhabited (AR τ) := ⟨⟨fun _ ↦ [], ⊥, bot_le, inferInstance⟩⟩

variable {X} in
theorem fst_ne_of_adj {v w : X.Pos} (h : X.assoc.Adj v w) : v.1 ≠ w.1 := X.assoc_le h

/-! ### Lines in `ℕ` coordinates -/

/-- Position `p` of tier `i` is associated with position `q` of tier `j`; positions beyond the
end of a word are associated with nothing. -/
def Link (i j : ι) (p q : ℕ) : Prop :=
  ∃ (hp : p < (X.word i).length) (hq : q < (X.word j).length),
    X.assoc.Adj ⟨i, ⟨p, hp⟩⟩ ⟨j, ⟨q, hq⟩⟩

instance (i j : ι) (p q : ℕ) : Decidable (X.Link i j p q) :=
  inferInstanceAs (Decidable (∃ _ _, _))

variable {X Y Z}

theorem link_iff_adj {v w : X.Pos} : X.Link v.1 w.1 v.2 w.2 ↔ X.assoc.Adj v w :=
  ⟨fun ⟨_, _, h⟩ ↦ h, fun h ↦ ⟨v.2.2, w.2.2, h⟩⟩

theorem Link.lt_left {i j : ι} {p q : ℕ} (h : X.Link i j p q) : p < (X.word i).length := h.1

theorem Link.lt_right {i j : ι} {p q : ℕ} (h : X.Link i j p q) : q < (X.word j).length := h.2.1

theorem Link.symm {i j : ι} {p q : ℕ} (h : X.Link i j p q) : X.Link j i q p :=
  ⟨h.2.1, h.1, h.2.2.symm⟩

theorem Link.ne {i j : ι} {p q : ℕ} (h : X.Link i j p q) : i ≠ j := fst_ne_of_adj h.2.2

theorem link_comm {i j : ι} {p q : ℕ} : X.Link i j p q ↔ X.Link j i q p := ⟨.symm, .symm⟩

theorem mk_inj {w : ∀ i, List (τ i)} {G G' : SimpleGraph ((i : ι) × Fin (w i).length)}
    {hG hG'} {d : DecidableRel G.Adj} {d' : DecidableRel G'.Adj} :
    (⟨w, G, hG, d⟩ : AR τ) = ⟨w, G', hG', d'⟩ ↔ G = G' := by
  refine ⟨fun h ↦ eq_of_heq (AR.mk.inj h).2.1, ?_⟩
  rintro rfl
  congr
  exact Subsingleton.elim _ _

@[ext] theorem ext (hw : X.word = Y.word) (hl : ∀ i j p q, X.Link i j p q ↔ Y.Link i j p q) :
    X = Y := by
  cases X
  cases Y
  obtain rfl := hw
  exact mk_inj.2 <| SimpleGraph.ext <| funext₂ fun v v' ↦ propext <|
    link_iff_adj.symm.trans <| (hl v.1 v'.1 v.2 v'.2).trans link_iff_adj

theorem ext_iff_bounded : X = Y ↔ (∀ i, X.word i = Y.word i) ∧
    ∀ i j, ∀ p < (X.word i).length, ∀ q < (X.word j).length, X.Link i j p q ↔ Y.Link i j p q := by
  refine ⟨by rintro rfl; exact ⟨fun _ ↦ rfl, fun _ _ _ _ _ _ ↦ .rfl⟩, fun ⟨hw, hl⟩ ↦
    ext (funext hw) fun i j p q ↦ ⟨fun h ↦ (hl i j p h.lt_left q h.lt_right).1 h, fun h ↦ ?_⟩⟩
  have hp := h.lt_left
  have hq := h.lt_right
  rw [← hw] at hp hq
  exact (hl i j p hp q hq).2 h

instance [Fintype ι] [∀ i, DecidableEq (τ i)] : DecidableEq (AR τ) :=
  fun _ _ ↦ decidable_of_iff _ ext_iff_bounded.symm

/-! ### Concatenation -/

section Monoid

variable (X Y) in
/-- The positions of a concatenation split into the positions of its factors. -/
def posMulEquiv : ((i : ι) × Fin (X.word i ++ Y.word i).length) ≃ X.Pos ⊕ Y.Pos :=
  (Equiv.sigmaCongrRight fun _ ↦ (finCongr List.length_append).trans finSumFinEquiv.symm).trans
    (Equiv.sigmaSumDistrib _ _)

private theorem elim_fst_posMulEquiv (v : (i : ι) × Fin (X.word i ++ Y.word i).length) :
    Sum.elim Sigma.fst Sigma.fst (posMulEquiv X Y v) = v.1 := by
  obtain ⟨i, p⟩ := v
  simp only [posMulEquiv, Equiv.trans_apply, Equiv.sigmaCongrRight_apply,
    Equiv.sigmaSumDistrib_apply]
  cases finSumFinEquiv.symm (finCongr List.length_append p) <;> rfl

theorem posMulEquiv_of_lt {i : ι} {p : ℕ} (hp : p < (X.word i ++ Y.word i).length)
    (h : p < (X.word i).length) : posMulEquiv X Y ⟨i, ⟨p, hp⟩⟩ = .inl ⟨i, ⟨p, h⟩⟩ := by
  simp only [posMulEquiv, Equiv.trans_apply, Equiv.sigmaCongrRight_apply,
    Equiv.sigmaSumDistrib_apply]
  rw [show finCongr List.length_append ⟨p, hp⟩ = Fin.castAdd (Y.word i).length ⟨p, h⟩ from rfl,
    finSumFinEquiv_symm_apply_castAdd]
  rfl

theorem posMulEquiv_of_le {i : ι} {p : ℕ} (hp : p < (X.word i ++ Y.word i).length)
    (h : (X.word i).length ≤ p) :
    posMulEquiv X Y ⟨i, ⟨p, hp⟩⟩ =
      .inr ⟨i, ⟨p - (X.word i).length, by rw [List.length_append] at hp; omega⟩⟩ := by
  simp only [posMulEquiv, Equiv.trans_apply, Equiv.sigmaCongrRight_apply,
    Equiv.sigmaSumDistrib_apply]
  rw [show finCongr List.length_append ⟨p, hp⟩ = Fin.natAdd (X.word i).length
      ⟨p - (X.word i).length, by rw [List.length_append] at hp; omega⟩ from
        Fin.ext (by simp; omega), finSumFinEquiv_symm_apply_natAdd]
  rfl

/-- Concatenation appends the words tier by tier and keeps the lines of both factors. -/
instance : Mul (AR τ) where
  mul X Y :=
    { word i := X.word i ++ Y.word i
      assoc := (X.assoc ⊕g Y.assoc).comap (posMulEquiv X Y)
      assoc_le v w h := by
        change v.1 ≠ w.1
        rw [← elim_fst_posMulEquiv v, ← elim_fst_posMulEquiv w]
        revert h
        change (X.assoc ⊕g Y.assoc).Adj (posMulEquiv X Y v) (posMulEquiv X Y w) → _
        generalize posMulEquiv X Y v = a
        generalize posMulEquiv X Y w = b
        rcases a with a | a <;> rcases b with b | b <;> intro h
        exacts [fst_ne_of_adj h, (Bool.false_ne_true h).elim, (Bool.false_ne_true h).elim,
          fst_ne_of_adj h] }

/-- The empty representation. -/
instance : One (AR τ) := ⟨default⟩

@[simp] theorem word_mul (i : ι) : (X * Y).word i = X.word i ++ Y.word i := rfl

@[simp] theorem word_one (i : ι) : (1 : AR τ).word i = [] := rfl

@[simp] theorem not_link_one (i j : ι) (p q : ℕ) : ¬ (1 : AR τ).Link i j p q :=
  fun h ↦ Nat.not_lt_zero _ h.lt_left

@[simp] theorem assoc_one : (1 : AR τ).assoc = ⊥ := rfl

theorem link_mul (i j : ι) (p q : ℕ) :
    (X * Y).Link i j p q ↔ X.Link i j p q ∨
      (X.word i).length ≤ p ∧ (X.word j).length ≤ q ∧
        Y.Link i j (p - (X.word i).length) (q - (X.word j).length) := by
  constructor
  · rintro ⟨hp, hq, h⟩
    change (X.assoc ⊕g Y.assoc).Adj _ _ at h
    rcases lt_or_ge p (X.word i).length with hpi | hpi <;>
      rcases lt_or_ge q (X.word j).length with hqj | hqj
    · rw [posMulEquiv_of_lt hp hpi, posMulEquiv_of_lt hq hqj] at h
      exact .inl ⟨hpi, hqj, h⟩
    · rw [posMulEquiv_of_lt hp hpi, posMulEquiv_of_le hq hqj] at h
      simp at h
    · rw [posMulEquiv_of_le hp hpi, posMulEquiv_of_lt hq hqj] at h
      simp at h
    · rw [posMulEquiv_of_le hp hpi, posMulEquiv_of_le hq hqj] at h
      exact .inr ⟨hpi, hqj, _, _, h⟩
  · rintro (⟨hp, hq, h⟩ | ⟨hpi, hqj, hp, hq, h⟩)
    · have hp' : p < (X.word i ++ Y.word i).length := by simp; omega
      have hq' : q < (X.word j ++ Y.word j).length := by simp; omega
      refine ⟨hp', hq', ?_⟩
      change (X.assoc ⊕g Y.assoc).Adj _ _
      rwa [posMulEquiv_of_lt hp' hp, posMulEquiv_of_lt hq' hq]
    · have hp' : p < (X.word i ++ Y.word i).length := by simp; omega
      have hq' : q < (X.word j ++ Y.word j).length := by simp; omega
      refine ⟨hp', hq', ?_⟩
      change (X.assoc ⊕g Y.assoc).Adj _ _
      rwa [posMulEquiv_of_le hp' hpi, posMulEquiv_of_le hq' hqj]

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
/-- The lines between tiers `i` and `j`, a relation between their positions. -/
def lines (i j : ι) : SetRel (Fin (X.word i).length) (Fin (X.word j).length) :=
  {x | X.assoc.Adj ⟨i, x.1⟩ ⟨j, x.2⟩}

theorem mem_lines {i j : ι} {x : Fin (X.word i).length × Fin (X.word j).length} :
    x ∈ X.lines i j ↔ X.Link i j x.1 x.2 :=
  ⟨fun h ↦ ⟨_, _, h⟩, fun ⟨_, _, h⟩ ↦ h⟩

variable (X) in
/-- The No-Crossing Constraint: between any two tiers, no two lines cross. -/
def NoCrossing : Prop := ∀ i j, IsNonCrossing (X.lines i j)

instance (i j : ι) : DecidablePred (· ∈ X.lines i j) :=
  fun _ ↦ inferInstanceAs (Decidable (X.assoc.Adj _ _))

instance [Fintype ι] : Decidable X.NoCrossing :=
  decidable_of_iff (∀ i j, IsNonCrossing (X.lines i j)) Iff.rfl

@[simp] theorem NoCrossing.one : (1 : AR τ).NoCrossing := fun _ _ _ h ↦ h.elim

theorem isNonCrossing_lines_iff {i j : ι} : IsNonCrossing (X.lines i j) ↔
    ∀ ⦃p q p' q'⦄, X.Link i j p q → X.Link i j p' q' → p < p' → q ≤ q' :=
  ⟨fun h _ _ _ _ ⟨hp, hq, h₁⟩ ⟨hp', hq', h₂⟩ hlt ↦
      @h (⟨_, hp⟩, ⟨_, hq⟩) h₁ (⟨_, hp'⟩, ⟨_, hq'⟩) h₂ hlt,
    fun h a ha b hb hlt ↦ h ⟨a.1.2, a.2.2, ha⟩ ⟨b.1.2, b.2.2, hb⟩ hlt⟩

theorem isNonCrossing_lines_iff_link {i j : ι} :
    IsNonCrossing (X.lines i j) ↔ IsNonCrossing {x : ℕ × ℕ | X.Link i j x.1 x.2} :=
  isNonCrossing_lines_iff.trans
    ⟨fun h _ ha _ hb ↦ h ha hb, fun h _ _ _ _ h₁ h₂ ↦ @h (_, _) h₁ (_, _) h₂⟩

theorem isNonCrossing_lines_self (i : ι) : IsNonCrossing (X.lines i i) :=
  isNonCrossing_lines_iff.2 fun _ _ _ _ h ↦ absurd rfl h.ne

theorem isNonCrossing_lines_comm {i j : ι} :
    IsNonCrossing (X.lines i j) ↔ IsNonCrossing (X.lines j i) := by
  simp only [isNonCrossing_lines_iff]
  exact ⟨fun h _ _ _ _ h₁ h₂ hlt ↦ le_of_not_gt fun hgt ↦ (h h₂.symm h₁.symm hgt).not_gt hlt,
    fun h _ _ _ _ h₁ h₂ hlt ↦ le_of_not_gt fun hgt ↦ (h h₂.symm h₁.symm hgt).not_gt hlt⟩

/-- Concatenation preserves the No-Crossing Constraint, the inductive step of
[jardine-heinz-2015]'s Theorem 4 for their merging concatenation. -/
theorem NoCrossing.mul (hX : X.NoCrossing) (hY : Y.NoCrossing) : (X * Y).NoCrossing :=
    fun i j ↦ isNonCrossing_lines_iff.2 fun p q p' q' h₁ h₂ hlt ↦ by
  replace hX := isNonCrossing_lines_iff.1 (hX i j)
  replace hY := isNonCrossing_lines_iff.1 (hY i j)
  rcases (link_mul i j p q).1 h₁ with h₁ | ⟨hp, hq, h₁⟩ <;>
    rcases (link_mul i j p' q').1 h₂ with h₂ | ⟨hp', hq', h₂⟩
  · exact hX h₁ h₂ hlt
  · exact (h₁.lt_right.trans_le hq').le
  · exact absurd (h₂.lt_left.trans_le hp) (by omega)
  · have := hY h₁ h₂ (by omega)
    omega

/-! ### Moving positions -/

section Map

variable [Fintype ι] [DecidableEq ι] (w : ∀ i, List (τ i))
  (f : ∀ i, Fin (X.word i).length → Fin (w i).length)

variable (X) in
/-- The representation with words `w` whose lines are those of `X`, each position moved
along `f` on its tier; positions merged by `f` keep the lines of all of them. -/
def map : AR τ where
  word := w
  assoc := X.assoc.map (Sigma.map id f)
  assoc_le := by
    rintro _ _ ⟨-, v, v', h, rfl, rfl⟩
    exact X.assoc_le h

theorem lines_map (i j : ι) : (X.map w f).lines i j = Prod.map (f i) (f j) '' X.lines i j := by
  ext ⟨p, q⟩
  simp only [lines, map, Set.mem_ofPred_eq, SimpleGraph.map_adj', Set.mem_image, Prod.exists,
    Prod.map, Prod.mk.injEq]
  constructor
  · rintro ⟨-, ⟨i', p'⟩, ⟨j', q'⟩, h, he₁, he₂⟩
    simp only [Sigma.map, id, Sigma.mk.injEq] at he₁ he₂
    obtain ⟨rfl, he₁⟩ := he₁
    obtain ⟨rfl, he₂⟩ := he₂
    exact ⟨p', q', h, eq_of_heq he₁, eq_of_heq he₂⟩
  · rintro ⟨p', q', h, rfl, rfl⟩
    exact ⟨fun he ↦ fst_ne_of_adj h (Sigma.mk.inj_iff.1 he).1, ⟨i, p'⟩, ⟨j, q'⟩, h, rfl, rfl⟩

theorem link_map {i j : ι} {r s : ℕ} :
    (X.map w f).Link i j r s ↔ ∃ x ∈ X.lines i j, (f i x.1 : ℕ) = r ∧ (f j x.2 : ℕ) = s := by
  constructor
  · rintro ⟨hr, hs, h⟩
    have : ((⟨r, hr⟩, ⟨s, hs⟩) : Fin _ × Fin _) ∈ (X.map w f).lines i j := h
    rw [lines_map] at this
    obtain ⟨x, hx, he⟩ := this
    exact ⟨x, hx, congrArg (Fin.val ∘ Prod.fst) he, congrArg (Fin.val ∘ Prod.snd) he⟩
  · rintro ⟨x, hx, rfl, rfl⟩
    have : (f i x.1, f j x.2) ∈ (X.map w f).lines i j := by rw [lines_map]; exact ⟨x, hx, rfl⟩
    exact mem_lines.1 this

/-- Moving positions monotonically preserves the No-Crossing Constraint. -/
theorem NoCrossing.map (hf : ∀ i, Monotone (f i)) (h : X.NoCrossing) :
    (X.map w f).NoCrossing := fun i j ↦ by
  rw [lines_map, isNonCrossing_image]
  exact fun a ha b hb hab ↦ hf j (h i j ha hb ((hf i).reflect_lt hab))

variable (X) in
@[simp] theorem map_id : X.map X.word (fun _ ↦ id) = X :=
  mk_inj.2 <|
    (congrArg (SimpleGraph.map · X.assoc) (funext fun _ ↦ rfl)).trans (SimpleGraph.map_id _)

theorem map_map (w' : ∀ i, List (τ i)) (g : ∀ i, Fin (w i).length → Fin (w' i).length) :
    (X.map w f).map w' g = X.map w' fun i ↦ g i ∘ f i :=
  mk_inj.2 <| SimpleGraph.map_map _ _ _

end Map

/-! ### Representations from words and a relation -/

section FromRel

variable [DecidableEq ι] (w : ∀ i, List (τ i)) (L : ι → ι → ℕ → ℕ → Prop)
  [∀ i j, DecidableRel (L i j)]

/-- The representation with words `w` and a line between positions on distinct tiers wherever
`L` holds in either direction: the symmetric closure `SimpleGraph.fromRel`, restricted to the
complete multipartite graph on the tiers. -/
def fromRel : AR τ where
  word := w
  assoc := .fromRel (fun v v' ↦ L v.1 v'.1 v.2 v'.2) ⊓ .completeMultipartiteGraph _
  assoc_le := inf_le_right

@[simp] theorem word_fromRel : (fromRel w L).word = w := rfl

variable {w L} in
@[simp] theorem link_fromRel {i j : ι} {p q : ℕ} :
    (fromRel w L).Link i j p q ↔
      i ≠ j ∧ p < (w i).length ∧ q < (w j).length ∧ (L i j p q ∨ L j i q p) := by
  simp only [Link, fromRel, SimpleGraph.inf_adj, SimpleGraph.fromRel_adj,
    SimpleGraph.comap_adj, SimpleGraph.top_adj]
  constructor
  · rintro ⟨hp, hq, ⟨-, h⟩, hij⟩
    exact ⟨hij, hp, hq, h⟩
  · rintro ⟨hij, hp, hq, h⟩
    exact ⟨hp, hq, ⟨fun h' ↦ hij (Sigma.mk.inj_iff.1 h').1, h⟩, hij⟩

end FromRel

end AR

end Autosegmental
