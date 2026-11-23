/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Logic.Team.Kripke
public import Linglib.Phonology.Autosegmental.OCP
public import Linglib.Phonology.Autosegmental.TierTree

/-!
# The Kripke model of a representation along a tree of tiers

A representation along a tree of tiers is a Kripke model, `AR.toKripkeModel`: its worlds are
the positions on the tiers, a position sees its children, and the atom `⟨j, b⟩` is true at the
positions of tier `j` labelled `b`. A slot reads `b` on tier `j` when a position it reaches makes
that atom true (`reads_iff_exists_dom`). Representations whose models are related by a
bisimulation therefore read alike at related slots (`IsBisimulation.reads_iff`). Material that no
slot dominates, such as an autosegment left floating by delinking, plays no part.

A relation between positions of the same tier is a bisimulation when related positions carry
the same label and each child of one is related to a child of the other
(`isBisimulation_toKripkeModel`). In a realization by trees with at most one token on a tier,
spreading a tier from one symbol onto another by a change of lines, `AR.spreadTier`, is
bisimilar in this way to replacing the target symbol by one that has the source's tokens on
that tier and below it and the target's own elsewhere (`exists_isBisimulation_spreadTier`). The
two read alike (`reads_spreadTier_iff`): linking shares what copying duplicates.

The OCP-merging collapse of a tier that no tier hangs from is bisimilar to the representation,
each position related to its run index (`exists_isBisimulation_collapse`), so it changes what no
slot reads (`reads_collapse_iff`). On two tiers, collapsing the autosegments changes what no
slot surfaces with (`surfacesWith_collapse_upper_iff`).

## References

* [blackburn-derijke-venema-2001]
* [jardine-2019]
* [sagey-1986]
-/

@[expose] public section

open ModalLogic

namespace Autosegmental.AR

variable {ι : Type*} {τ : ι → Type*} [Fintype ι] [DecidableEq ι] {T : ParentTree ι}
  {X Y Z : AR τ}

/-- The Kripke model of a representation along a tree of tiers: a position sees its children,
and the atom `⟨j, b⟩` is true at the positions of tier `j` labelled `b`. -/
def toKripkeModel (T : ParentTree ι) (X : AR τ) : KripkeModel (ι × ℕ) (Σ j, τ j) where
  access := X.children T
  val a := fun (i, q) ↦ (X.word i)[q]?.map (Sigma.mk i) = some a

@[simp] theorem toKripkeModel_access (v : ι × ℕ) :
    (X.toKripkeModel T).access v = X.children T v := rfl

theorem toKripkeModel_val_self {j : ι} {q : ℕ} {b : τ j} :
    (X.toKripkeModel T).val ⟨j, b⟩ (j, q) ↔ (X.word j)[q]? = some b :=
  Option.map_eq_some_iff.trans
    ⟨fun ⟨_, ha, he⟩ ↦ by cases he; exact ha, fun h ↦ ⟨b, h, rfl⟩⟩

/-- A slot reads a label on a tier when a position it reaches makes the atom true. -/
theorem reads_iff_exists_dom {k : ℕ} {j : ι} {b : τ j} :
    X.Reads T k j b ↔ ∃ v, X.Dom T (T.root, k) v ∧ (X.toKripkeModel T).val ⟨j, b⟩ v := by
  constructor
  · rintro ⟨q, -, hq, hb⟩
    exact ⟨(j, q), dominates_iff_dom.mp hq, toKripkeModel_val_self.mpr hb⟩
  · rintro ⟨⟨i, q⟩, hv, hval⟩
    obtain ⟨a, ha, he⟩ := Option.map_eq_some_iff.mp hval
    cases he
    exact ⟨q, Finset.mem_range.mpr (List.getElem?_eq_some_iff.mp ha).1,
      dominates_iff_dom.mpr hv, ha⟩

/-- Representations whose Kripke models are related by a bisimulation read alike at related
slots. -/
theorem _root_.ModalLogic.KripkeModel.IsBisimulation.reads_iff {r : ι × ℕ → ι × ℕ → Prop}
    (h : (Y.toKripkeModel T).IsBisimulation (Z.toKripkeModel T) r) {k k' : ℕ}
    (hr : r (T.root, k) (T.root, k')) {j : ι} {b : τ j} :
    Y.Reads T k j b ↔ Z.Reads T k' j b := by
  simp only [reads_iff_exists_dom]
  constructor
  · rintro ⟨v, hv, hval⟩
    obtain ⟨v', hv', hrv⟩ := h.exists_reflTransGen hr hv
    exact ⟨v', hv', (h.val_iff hrv _).mp hval⟩
  · rintro ⟨v', hv', hval⟩
    obtain ⟨v, hv, hrv⟩ := h.symm.exists_reflTransGen hr hv'
    exact ⟨v, hv, (h.val_iff hrv _).mpr hval⟩

/-- A relation between positions of the same tier is a bisimulation when related positions
carry the same label and each child of one is related to a child of the other. -/
theorem isBisimulation_toKripkeModel {R : ι → ℕ → ℕ → Prop}
    (label : ∀ ⦃j q q'⦄, R j q q' → (Y.word j)[q]? = (Z.word j)[q']?)
    (forth : ∀ ⦃i p p' j q⦄, R i p p' → (j, q) ∈ Y.children T (i, p) →
      ∃ q', (j, q') ∈ Z.children T (i, p') ∧ R j q q')
    (back : ∀ ⦃i p p' j q'⦄, R i p p' → (j, q') ∈ Z.children T (i, p') →
      ∃ q, (j, q) ∈ Y.children T (i, p) ∧ R j q q') :
    (Y.toKripkeModel T).IsBisimulation (Z.toKripkeModel T)
      fun v v' ↦ ∃ j q q', v = (j, q) ∧ v' = (j, q') ∧ R j q q' where
  val_iff := by
    rintro _ _ ⟨j, q, q', rfl, rfl, hR⟩ a
    show (Y.word j)[q]?.map (Sigma.mk j) = some a ↔ (Z.word j)[q']?.map (Sigma.mk j) = some a
    rw [label hR]
  liftRel_access := by
    rintro _ _ ⟨i, p, p', rfl, rfl, hR⟩
    exact ⟨fun ⟨j, q⟩ hc ↦
        let ⟨q', hc', hR'⟩ := forth hR hc; ⟨(j, q'), hc', j, q, q', rfl, rfl, hR'⟩,
      fun ⟨j, q'⟩ hc ↦
        let ⟨q, hc', hR'⟩ := back hR hc; ⟨(j, q), hc', j, q, q', rfl, rfl, hR'⟩⟩

/-! ### Spreading -/

section Spread

variable {S : Type*} (g₀ : S → AR τ)

/-- The tokens of the `k`th symbol of a word on a tier. -/
private def tokens (v : List S) (k : ℕ) (t : ι) : List (τ t) :=
  if hk : k < v.length then (g₀ v[k]).word t else []

omit [Fintype ι] [DecidableEq ι] in
private theorem tokens_of_lt {v : List S} {k : ℕ} (hk : k < v.length) (t : ι) :
    tokens g₀ v k t = (g₀ v[k]).word t := by simp [tokens, hk]

omit [Fintype ι] [DecidableEq ι] in
private theorem tokens_ne_nil_iff {v : List S} {k : ℕ} {t : ι} :
    tokens g₀ v k t ≠ [] ↔ ∃ hk : k < v.length, (g₀ v[k]).word t ≠ [] := by
  unfold tokens
  constructor
  · intro h
    by_cases hk : k < v.length
    · exact ⟨hk, by simpa [hk] using h⟩
    · simp [hk] at h
  · rintro ⟨hk, h⟩
    simpa [hk] using h

omit [Fintype ι] [DecidableEq ι] in
private theorem tokens_set (w : List S) {n : ℕ} (hn : n < w.length) (s' : S) (k : ℕ) (t : ι) :
    tokens g₀ (w.set n s') k t = if k = n then (g₀ s').word t else tokens g₀ w k t := by
  unfold tokens
  by_cases hkn : k = n
  · subst hkn
    simp [hn]
  · simp [hkn, Ne.symm hkn]

omit [Fintype ι] [DecidableEq ι] in
private theorem getElem?_word_prod_map_tokens (v : List S) {k : ℕ} {t : ι}
    (h : tokens g₀ v k t ≠ []) :
    ((v.map g₀).prod.word t)[tierOffset g₀ t v k]? = (tokens g₀ v k t)[0]? := by
  obtain ⟨hk, h'⟩ := (tokens_ne_nil_iff g₀).1 h
  rw [tokens_of_lt g₀ hk]
  simpa using getElem?_word_prod_map g₀ t v hk (r := 0) (List.length_pos_iff.2 h')

omit [Fintype ι] [DecidableEq ι] in
private theorem eq_of_tierOffset_eq_tokens (v : List S) {k k' : ℕ} {t : ι}
    (h : tokens g₀ v k t ≠ []) (h' : tokens g₀ v k' t ≠ [])
    (he : tierOffset g₀ t v k = tierOffset g₀ t v k') : k = k' := by
  obtain ⟨hk, h⟩ := (tokens_ne_nil_iff g₀).1 h
  obtain ⟨hk', h'⟩ := (tokens_ne_nil_iff g₀).1 h'
  exact eq_of_tierOffset_eq g₀ t v hk hk' h h' he

section Tree

variable (h1 : ∀ s t, ((g₀ s).word t).length ≤ 1)
  (htree : ∀ s t, t ≠ T.root → ((g₀ s).Link (T.parent t) t 0 0 ↔ (g₀ s).word t ≠ []))
include h1 htree

private theorem mem_children_prod_map_tokens {v : List S} {i' t : ι} {p q : ℕ} :
    (t, q) ∈ (v.map g₀).prod.children T (i', p) ↔ T.parent t = i' ∧ t ≠ T.root ∧
      ∃ k, p = tierOffset g₀ i' v k ∧ q = tierOffset g₀ t v k ∧ tokens g₀ v k t ≠ [] := by
  rw [mem_children_prod_map T g₀ h1 htree]
  exact and_congr_right fun _ ↦ and_congr_right fun _ ↦ exists_congr fun k ↦
    ⟨fun ⟨hk, hp, hq, h⟩ ↦ ⟨hp, hq, (tokens_ne_nil_iff g₀).2 ⟨hk, h⟩⟩,
      fun ⟨hp, hq, h⟩ ↦ let ⟨hk, h⟩ := (tokens_ne_nil_iff g₀).1 h; ⟨hk, hp, hq, h⟩⟩

omit [Fintype ι] [DecidableEq ι] h1 in
private theorem tokens_parent_ne_nil {v : List S} {k : ℕ} {t : ι} (hr : t ≠ T.root)
    (h : tokens g₀ v k t ≠ []) : tokens g₀ v k (T.parent t) ≠ [] := by
  obtain ⟨hk, h⟩ := (tokens_ne_nil_iff g₀).1 h
  exact (tokens_ne_nil_iff g₀).2
    ⟨hk, List.ne_nil_of_length_pos ((htree _ t hr).2 h).lt_left⟩

omit [Fintype ι] [DecidableEq ι] in
private theorem link_prod_map_tokens {v : List S} {k : ℕ} {t : ι} (hr : t ≠ T.root)
    (h : tokens g₀ v k t ≠ []) :
    (v.map g₀).prod.Link (T.parent t) t (tierOffset g₀ (T.parent t) v k)
      (tierOffset g₀ t v k) := by
  obtain ⟨hk, h⟩ := (tokens_ne_nil_iff g₀).1 h
  exact (link_prod_map_of_length_le_one (fun s ↦ h1 s _) (fun s ↦ h1 s _)).2
    ⟨k, hk, rfl, rfl, (htree _ t hr).2 h⟩

end Tree

/-- Where the token of the `k`th symbol on tier `t` stands after tier `j` is spread from the
`m`th symbol onto the `n`th: with the tokens of the `m`th symbol when it belongs to the `n`th
and `t` is `j` or below it. -/
private noncomputable def spreadPos (T : ParentTree ι) (w : List S) (j : ι) (m n : ℕ) (t : ι)
    (k : ℕ) : ℕ :=
  open Classical in
  if k = n ∧ T.toPartialOrder.le j t then tierOffset g₀ t w m else tierOffset g₀ t w k

omit [Fintype ι] [DecidableEq ι] in
private theorem spreadPos_of_below {w : List S} {j t : ι} {m n : ℕ}
    (h : T.toPartialOrder.le j t) :
    spreadPos g₀ T w j m n t n = tierOffset g₀ t w m := by simp [spreadPos, h]

omit [Fintype ι] [DecidableEq ι] in
private theorem spreadPos_of_not_below {w : List S} {j t : ι} {m n : ℕ}
    (h : ¬ T.toPartialOrder.le j t) (k : ℕ) :
    spreadPos g₀ T w j m n t k = tierOffset g₀ t w k := by simp [spreadPos, h]

omit [Fintype ι] [DecidableEq ι] in
private theorem spreadPos_of_ne {w : List S} {j : ι} {m n k : ℕ} (h : k ≠ n) (t : ι) :
    spreadPos g₀ T w j m n t k = tierOffset g₀ t w k := by simp [spreadPos, h]

/-- Spreading a tier by a change of lines is bisimilar, slot by slot, to replacing the target
symbol by one that has the source's tokens on that tier and below it, and the target's own
tokens elsewhere. -/
theorem exists_isBisimulation_spreadTier {w : List S} {j : ι} {m n : ℕ} {s' : S} (hj : j ≠ T.root)
    (h1 : ∀ s t, ((g₀ s).word t).length ≤ 1) (hroot : ∀ s, ((g₀ s).word T.root).length = 1)
    (htree : ∀ s t, t ≠ T.root → ((g₀ s).Link (T.parent t) t 0 0 ↔ (g₀ s).word t ≠ []))
    (hm : m < w.length) (hn : n < w.length) (hmj : (g₀ w[m]).word j ≠ [])
    (hnp : (g₀ w[n]).word (T.parent j) ≠ [])
    (hbelow : ∀ t, T.toPartialOrder.le j t → (g₀ s').word t = (g₀ w[m]).word t)
    (hrest : ∀ t, ¬ T.toPartialOrder.le j t → (g₀ s').word t = (g₀ w[n]).word t) :
    ∃ r, (((w.set n s').map g₀).prod.toKripkeModel T).IsBisimulation
        ((spreadTier T g₀ w j m n).toKripkeModel T) r ∧
      ∀ k < w.length, r (T.root, k) (T.root, k) := by
  have tok_below : ∀ {t : ι}, T.toPartialOrder.le j t →
      tokens g₀ (w.set n s') n t = tokens g₀ w m t := fun {t} hb ↦ by
    rw [tokens_set g₀ w hn, ite_eq_left rfl, hbelow t hb, tokens_of_lt g₀ hm]
  have tok_not_below : ∀ {t : ι}, ¬ T.toPartialOrder.le j t → ∀ k,
      tokens g₀ (w.set n s') k t = tokens g₀ w k t := fun {t} hb k ↦ by
    rw [tokens_set g₀ w hn]
    by_cases hkn : k = n
    · rw [ite_eq_left hkn, hrest t hb, hkn, tokens_of_lt g₀ hn]
    · rw [ite_eq_right hkn]
  have tok_ne : ∀ {k : ℕ}, k ≠ n → ∀ t,
      tokens g₀ (w.set n s') k t = tokens g₀ w k t := fun {k} hkn t ↦ by
    rw [tokens_set g₀ w hn, ite_eq_right hkn]
  have hroot_nb : ¬ T.toPartialOrder.le j T.root := fun ⟨r, hr⟩ ↦
    hj (hr.symm.trans (T.iterate_root r))
  have hoff : ∀ (v : List S) k, k ≤ v.length → tierOffset g₀ T.root v k = k := fun v k hk ↦
    tierOffset_of_length_eq_one g₀ T.root v hroot hk
  have child := @mem_children_prod_map_tokens ι τ _ _ T S g₀ h1 htree
  refine ⟨_, isBisimulation_toKripkeModel (Y := ((w.set n s').map g₀).prod)
    (Z := spreadTier T g₀ w j m n) (R := fun t q q' ↦ ∃ k, tokens g₀ (w.set n s') k t ≠ [] ∧
      q = tierOffset g₀ t (w.set n s') k ∧ q' = spreadPos g₀ T w j m n t k) ?_ ?_ ?_,
    fun k hk ↦ ⟨T.root, k, k, rfl, rfl, k, ?_, ?_, ?_⟩⟩
  · rintro t q q' ⟨k, hk, rfl, rfl⟩
    rw [getElem?_word_prod_map_tokens g₀ _ hk]
    show _ = ((w.map g₀).prod.word t)[_]?
    by_cases hkn : k = n
    · subst hkn
      by_cases hb : T.toPartialOrder.le j t
      · rw [spreadPos_of_below g₀ hb, tok_below hb] at *
        rw [getElem?_word_prod_map_tokens g₀ _ hk]
      · rw [spreadPos_of_not_below g₀ hb, tok_not_below hb] at *
        rw [getElem?_word_prod_map_tokens g₀ _ hk]
    · rw [spreadPos_of_ne g₀ hkn, tok_ne hkn] at *
      rw [getElem?_word_prod_map_tokens g₀ _ hk]
  · rintro i' p p' t q ⟨k, hk, rfl, rfl⟩ hc
    obtain ⟨rfl, hr, k₂, he, rfl, hk₂⟩ := child.1 hc
    obtain rfl : k = k₂ := eq_of_tierOffset_eq_tokens g₀ _ hk
      (tokens_parent_ne_nil g₀ htree hr hk₂) he
    refine ⟨_, mem_children.2 ⟨rfl, hr, ?_⟩, _, hk₂, rfl, rfl⟩
    show (spreadTier T g₀ w j m n).Link (T.parent t) t _ _
    rw [link_spreadTier T g₀ hj hm hn hmj hnp]
    by_cases hkn : k = n
    · subst hkn
      by_cases hbt : T.toPartialOrder.le j t
      · by_cases htj : t = j
        · subst htj
          exact .inr (.inl ⟨rfl, rfl, spreadPos_of_not_below g₀ (T.not_le_parent hj) _,
            spreadPos_of_below g₀ hbt⟩)
        · have hbp : T.toPartialOrder.le j (T.parent t) :=
            (T.le_iff_eq_or_le_parent.1 hbt).resolve_left htj
          refine .inl ⟨?_, fun h ↦ htj h.2.1, fun h ↦ T.not_le_parent hj (h.2.1 ▸ hbt)⟩
          rw [spreadPos_of_below g₀ hbp, spreadPos_of_below g₀ hbt]
          exact link_prod_map_tokens g₀ h1 htree hr (by rw [← tok_below hbt]; exact hk₂)
      · have hbp : ¬ T.toPartialOrder.le j (T.parent t) := fun h ↦
          hbt (T.le_iff_eq_or_le_parent.2 (.inr h))
        refine .inl ⟨?_, fun h ↦ hbt (h.2.1 ▸ ⟨0, rfl⟩), fun h ↦ hbp (h.1 ▸ ⟨0, rfl⟩)⟩
        rw [spreadPos_of_not_below g₀ hbp, spreadPos_of_not_below g₀ hbt]
        exact link_prod_map_tokens g₀ h1 htree hr (by rw [← tok_not_below hbt]; exact hk₂)
    · refine .inl ⟨?_, ?_, fun h ↦ T.not_le_parent hj ⟨1, by rw [← h.2.1]; exact h.1⟩⟩
      · rw [spreadPos_of_ne g₀ hkn, spreadPos_of_ne g₀ hkn]
        exact link_prod_map_tokens g₀ h1 htree hr (by rw [← tok_ne hkn]; exact hk₂)
      · rintro ⟨-, rfl, h₃, -⟩
        rw [spreadPos_of_ne g₀ hkn] at h₃
        exact hkn (eq_of_tierOffset_eq_tokens g₀ w (by rw [← tok_ne hkn]; exact hk)
          ((tokens_ne_nil_iff g₀).2 ⟨hn, hnp⟩) h₃)
  · rintro i' p p' t q' ⟨k, hk, rfl, rfl⟩ hc
    obtain ⟨hp, hr, hl⟩ := mem_children.1 hc
    obtain rfl : T.parent t = i' := hp
    replace hl : (spreadTier T g₀ w j m n).Link (T.parent t) t
        (spreadPos g₀ T w j m n (T.parent t) k) q' := hl
    rw [link_spreadTier T g₀ hj hm hn hmj hnp] at hl
    rcases hl with ⟨hx, hne₁, -⟩ | ⟨-, htj, hp', hq'⟩ | ⟨h₁, h₂, -, -⟩
    · obtain ⟨k₂, hk₂, he, rfl, hl0⟩ :=
        (link_prod_map_of_length_le_one (fun s ↦ h1 s _) (fun s ↦ h1 s _)).1 hx
      have hk₂t : tokens g₀ w k₂ t ≠ [] :=
        (tokens_ne_nil_iff g₀).2 ⟨hk₂, (htree _ t hr).1 hl0⟩
      have hk₂p := tokens_parent_ne_nil g₀ htree hr hk₂t
      by_cases hkn : k = n
      · subst hkn
        by_cases hbp : T.toPartialOrder.le j (T.parent t)
        · rw [spreadPos_of_below g₀ hbp] at he
          obtain rfl : m = k₂ := eq_of_tierOffset_eq_tokens g₀ w
            (by rw [← tok_below hbp]; exact hk) hk₂p he
          have hbt : T.toPartialOrder.le j t := T.le_iff_eq_or_le_parent.2 (.inr hbp)
          have hk't : tokens g₀ (w.set k s') k t ≠ [] := by rw [tok_below hbt]; exact hk₂t
          exact ⟨_, child.2 ⟨rfl, hr, _, rfl, rfl, hk't⟩, _, hk't, rfl,
            (spreadPos_of_below g₀ hbt).symm⟩
        · rw [spreadPos_of_not_below g₀ hbp] at he
          obtain rfl : k = k₂ := eq_of_tierOffset_eq_tokens g₀ w
            (by rw [← tok_not_below hbp]; exact hk) hk₂p he
          have htj : t ≠ j := fun h ↦ hne₁
            ⟨by rw [h], h, by rw [spreadPos_of_not_below g₀ hbp, h], by rw [h]⟩
          have hbt : ¬ T.toPartialOrder.le j t := fun h ↦
            (T.le_iff_eq_or_le_parent.1 h).elim htj hbp
          have hk't : tokens g₀ (w.set k s') k t ≠ [] := by
            rw [tok_not_below hbt]; exact hk₂t
          exact ⟨_, child.2 ⟨rfl, hr, _, rfl, rfl, hk't⟩, _, hk't, rfl,
            (spreadPos_of_not_below g₀ hbt _).symm⟩
      · rw [spreadPos_of_ne g₀ hkn] at he
        obtain rfl : k = k₂ := eq_of_tierOffset_eq_tokens g₀ w
          (by rw [← tok_ne hkn]; exact hk) hk₂p he
        have hk't : tokens g₀ (w.set n s') k t ≠ [] := by rw [tok_ne hkn]; exact hk₂t
        exact ⟨_, child.2 ⟨rfl, hr, _, rfl, rfl, hk't⟩, _, hk't, rfl,
          (spreadPos_of_ne g₀ hkn t).symm⟩
    · subst htj
      have hnb := T.not_le_parent hj
      rw [spreadPos_of_not_below g₀ hnb] at hp'
      obtain rfl : k = n := eq_of_tierOffset_eq_tokens g₀ w
        (by rw [← tok_not_below hnb]; exact hk) ((tokens_ne_nil_iff g₀).2 ⟨hn, hnp⟩) hp'
      have hbj : T.toPartialOrder.le t t := ⟨0, rfl⟩
      have hk't : tokens g₀ (w.set k s') k t ≠ [] := by
        rw [tok_below hbj]; exact (tokens_ne_nil_iff g₀).2 ⟨hm, hmj⟩
      exact ⟨_, child.2 ⟨rfl, hr, _, rfl, rfl, hk't⟩, _, hk't, rfl,
        by rw [hq', spreadPos_of_below g₀ hbj]⟩
    · exact absurd ⟨1, by rw [← h₂]; exact h₁⟩ (T.not_le_parent hj)
  · exact (tokens_ne_nil_iff g₀).2 ⟨by simpa using hk,
      List.ne_nil_of_length_pos (by rw [hroot]; exact Nat.one_pos)⟩
  · exact (hoff _ k (by simpa using hk.le)).symm
  · rw [spreadPos_of_not_below g₀ hroot_nb, hoff w k hk.le]

/-- Spreading a tier by a change of lines reads as replacing the target symbol by one that has
the source's tokens on that tier and below it, and the target's own tokens elsewhere. -/
theorem reads_spreadTier_iff {w : List S} {j : ι} {m n : ℕ} {s' : S} (hj : j ≠ T.root)
    (h1 : ∀ s t, ((g₀ s).word t).length ≤ 1) (hroot : ∀ s, ((g₀ s).word T.root).length = 1)
    (htree : ∀ s t, t ≠ T.root → ((g₀ s).Link (T.parent t) t 0 0 ↔ (g₀ s).word t ≠ []))
    (hm : m < w.length) (hn : n < w.length) (hmj : (g₀ w[m]).word j ≠ [])
    (hnp : (g₀ w[n]).word (T.parent j) ≠ [])
    (hbelow : ∀ t, T.toPartialOrder.le j t → (g₀ s').word t = (g₀ w[m]).word t)
    (hrest : ∀ t, ¬ T.toPartialOrder.le j t → (g₀ s').word t = (g₀ w[n]).word t)
    {k : ℕ} {t : ι} {b : τ t} :
    (spreadTier T g₀ w j m n).Reads T k t b ↔ ((w.set n s').map g₀).prod.Reads T k t b := by
  obtain ⟨r, hB, hr⟩ :=
    exists_isBisimulation_spreadTier g₀ hj h1 hroot htree hm hn hmj hnp hbelow hrest
  by_cases hk : k < w.length
  · exact (hB.reads_iff (hr k hk)).symm
  · have hlen : ∀ v : List S, ((v.map g₀).prod.word T.root).length = v.length := fun v ↦
      length_word_prod_map_of_length_eq_one g₀ T.root v hroot
    exact iff_of_false
      (not_reads_of_length_le (X := spreadTier T g₀ w j m n) (by
        show ((w.map g₀).prod.word T.root).length ≤ k
        rw [hlen]; exact not_lt.1 hk))
      (not_reads_of_length_le (by rw [hlen]; simpa using not_lt.1 hk))

end Spread

/-! ### The OCP-merging collapse -/

section Collapse

open OCP

variable {m : ι} [DecidableEq (τ m)]

/-- Collapsing a tier that no tier hangs from is bisimilar to the representation, each
position to its run index. -/
theorem exists_isBisimulation_collapse (hm : ∀ t, t ≠ T.root → T.parent t ≠ m) :
    ∃ r, (X.toKripkeModel T).IsBisimulation ((X.collapse m).toKripkeModel T) r ∧
      ∀ k < (X.word T.root).length,
        r (T.root, k) (T.root, repointIdx m (runIdx (X.word m)) T.root k) := by
  refine ⟨_, isBisimulation_toKripkeModel (R := fun i p p' ↦ p < (X.word i).length ∧
    p' = repointIdx m (runIdx (X.word m)) i p) ?_ ?_ ?_,
    fun k hk ↦ ⟨T.root, k, _, rfl, rfl, hk, rfl⟩⟩
  · rintro j q _ ⟨hq, rfl⟩
    rcases eq_or_ne j m with rfl | hj
    · rw [repointIdx_self, word_collapse_self, getElem?_collapse_runIdx hq]
    · rw [repointIdx_of_ne hj, word_collapse_of_ne _ _ hj]
  · rintro i p _ j q ⟨hp, rfl⟩ hc
    obtain ⟨hpar, hr, hl⟩ := mem_children.1 hc
    exact ⟨_, mem_children.2 ⟨hpar, hr, link_collapse.2 ⟨p, q, hl, rfl, rfl⟩⟩, hl.lt_right, rfl⟩
  · rintro i p _ j q' ⟨hp, rfl⟩ hc
    obtain ⟨hpar, hr, hl⟩ := mem_children.1 hc
    obtain rfl : T.parent j = i := hpar
    replace hl : (X.collapse m).Link (T.parent j) j
      (repointIdx m (runIdx (X.word m)) (T.parent j) p) q' := hl
    obtain ⟨p₀, q₀, hl₀, hp₀, rfl⟩ := link_collapse.1 hl
    have hi := hm j hr
    rw [repointIdx_of_ne hi, repointIdx_of_ne hi] at hp₀
    subst hp₀
    exact ⟨q₀, mem_children.2 ⟨rfl, hr, hl₀⟩, hl₀.lt_right, rfl⟩

/-- Collapsing a tier that no tier hangs from changes what no slot reads. -/
theorem reads_collapse_iff (hm : ∀ t, t ≠ T.root → T.parent t ≠ m) (hroot : m ≠ T.root)
    {k : ℕ} {j : ι} {b : τ j} : (X.collapse m).Reads T k j b ↔ X.Reads T k j b := by
  obtain ⟨r, hB, hr⟩ := exists_isBisimulation_collapse (X := X) hm
  by_cases hk : k < (X.word T.root).length
  · have h := hr k hk
    rw [repointIdx_of_ne (Ne.symm hroot)] at h
    exact (hB.reads_iff h).symm
  · exact iff_of_false
      (not_reads_of_length_le (by rw [word_collapse_of_ne _ _ (Ne.symm hroot)]; exact not_lt.1 hk))
      (not_reads_of_length_le (not_lt.1 hk))

end Collapse

section TwoTier

open Tier

universe u

variable {α β : Type u} [DecidableEq α] {X : AR (TwoTier α β)} {a : α} {j : ℕ}

/-- Collapsing the autosegments changes what no slot surfaces with. -/
theorem surfacesWith_collapse_upper_iff :
    (X.collapse upper).SurfacesWith a j ↔ X.SurfacesWith a j := by
  rw [← reads_twoTier_upper_iff, ← reads_twoTier_upper_iff]
  exact reads_collapse_iff (fun _ _ ↦ (by decide : lower ≠ upper)) (by decide)

end TwoTier

end Autosegmental.AR
