module

public import Linglib.Phonology.Subregular.ModelTheory.Local
public import Linglib.Phonology.Subregular.ModelTheory.WordModel.Factor
public import Linglib.Phonology.Subregular.Stringset.Multitier
public import Linglib.Phonology.Subregular.Stringset.StrictlyPiecewise
public import Mathlib.Order.SuccPred.Nat
public import Linglib.Core.Computability.Edge

/-!
# The stringsets of word models

The strictly local and locally testable sets of word models under precedence are the strictly
piecewise and piecewise testable stringsets. Those of words between their edges under successor
are the strictly local and locally testable ones, and on the projection to a tier the tier-based
strictly local ones. Over a finite alphabet the piecewise testable stringsets are therefore the
Boolean combinations of the strictly piecewise ones, and for widths from two up the locally
testable stringsets those of the strictly local ones.

## Main definitions

* `Subregular.anchor`: a word between its two edges.

## Main results

* `Language.isStrictlyPiecewise_iff_wordModel`, `Language.isPiecewiseTestable_iff_wordModel`: the
  strictly piecewise and piecewise testable stringsets are the strictly local and locally testable
  sets of precedence models.
* `Language.isStrictlyLocal_iff_wordModel`, `Language.isLocallyTestable_iff_wordModel`: the
  strictly local stringsets, for widths from two up, and the locally testable ones are those of
  anchored words under successor.
* `Language.isTierStrictlyLocal_iff_wordModel`: the tier-based strictly local stringsets are those
  of the projections to a tier.
* `Language.isPiecewiseTestable_iff_mem_closure`, `Language.isLocallyTestable_iff_mem_closure`:
  over a finite alphabet the testable stringsets are the Boolean combinations of the strict ones.
* `Language.multitier_isLocallyTestable`, `Language.mem_multitierLocallyTestable_iff`: the
  multitier extension of the locally testable stringsets is that of the strictly local ones, and
  the test vectors of the tier projections of a word decide membership in it.
* `Subregular.WordModel.factors_eq_iff_subseqSet`: under precedence the factors of a word are
  determined by its subsequences of bounded length.

## Implementation notes

* As in Rogers and Lambert's word models, the edges carry their own labels and are not related to
  themselves. The strictly local stringsets pad a word with `k - 1` boundary symbols instead, and
  the two classes differ only at `k = 1`, where the word models also forbid every word; the
  locally testable classes agree at every `k`.
* Strict locality under successor rests on locality of concatenation,
  `Subregular.WordModel.factors_append_append_subset`: a `k`-factor of a word around `k - 1` or
  more symbols occurs on one side of them, which is suffix substitution closure read on models.

## TODO

* Successor relativized to a tier is modelled by the successor model of the word's projection.
  The relation on the word's own positions, relating a tier position to the next one, and the
  isomorphism of the substructure it induces on the tier positions with that model, are not
  stated.

## References

* [rogers-lambert-2019]
* [rogers-pullum-2011]
* [rogers-heinz-et-al-2010]
* [lambert-2023]
-/

@[expose] public section

universe u

open FirstOrder FirstOrder.Language List

namespace Subregular

variable {α : Type u}

/-! ### Factors under precedence and subsequences -/

namespace WordModel

variable {β : Type*} {w w' : List β}

theorem factors_subset_of_subseqSet_subset {k : ℕ} (h : subseqSet k w ⊆ subseqSet k w') :
    (wordLanguage β {.prec}).factors k (WordModel ({·}) w) ⊆
      (wordLanguage β {.prec}).factors k (WordModel ({·}) w') := fun _ hf ↦
  let ⟨_, hsw, hs, hfs⟩ := exists_sublist_of_occurs hf
  factors_subset_of_sublist (h ⟨hsw, hs⟩).1 hfs

theorem factors_eq_iff_subseqSet {k : ℕ} :
    (wordLanguage β {.prec}).factors k (WordModel ({·}) w) =
        (wordLanguage β {.prec}).factors k (WordModel ({·}) w') ↔
      subseqSet k w = subseqSet k w' := by
  refine ⟨fun h ↦ Set.ext fun s ↦ ⟨fun ⟨hsw, hs⟩ ↦ ⟨?_, hs⟩, fun ⟨hsw, hs⟩ ↦ ⟨?_, hs⟩⟩,
    fun h ↦ (factors_subset_of_subseqSet_subset h.subset).antisymm
      (factors_subset_of_subseqSet_subset h.symm.subset)⟩
  · exact (diagram_occurs_iff hs).1 (h.subset ((diagram_occurs_iff hs).2 hsw))
  · exact (diagram_occurs_iff hs).1 (h.symm.subset ((diagram_occurs_iff hs).2 hsw))

end WordModel

/-! ### Anchored words -/

/-- The word `w` between its edges, `⋊ w ⋉`. -/
def anchor (w : List α) : List (α ⊕ Edge) := .inr .left :: (w.map .inl ++ [.inr .right])

section Anchor

variable {s v : List α}

@[simp] theorem length_anchor (w : List α) : (anchor w).length = w.length + 2 := by
  simp [anchor]

private theorem prefix_of_infix_cons {β : Type*} {e : β} {c l : List β} (h : e :: c <:+: e :: l)
    (he : e ∉ l) : c <+: l := by
  rcases List.infix_cons_iff.1 h with h | h
  · exact (List.cons_prefix_cons.1 h).2
  · exact absurd (h.subset List.mem_cons_self) he

theorem infix_of_map_inl_infix_anchor (h : s.map .inl <:+: anchor v) : s <:+: v := by
  simpa [anchor, List.filterMap_map] using h.filterMap Sum.getLeft?

theorem prefix_of_infix_anchor (h : .inr .left :: s.map .inl <:+: anchor v) : s <+: v := by
  have := (prefix_of_infix_cons h (by simp)).filterMap Sum.getLeft?
  simpa [List.filterMap_map] using this

theorem suffix_of_infix_anchor (h : s.map .inl ++ [.inr .right] <:+: anchor v) : s <:+ v := by
  have h' : .inr .right :: (s.reverse.map .inl) <:+:
      .inr .right :: ((v.reverse.map .inl) ++ [(.inr .left : α ⊕ Edge)]) := by
    simpa [anchor, List.map_reverse] using h.reverse
  have := (prefix_of_infix_cons h' (by simp)).filterMap Sum.getLeft?
  simpa [List.filterMap_map, List.reverse_prefix] using this

theorem eq_of_anchor_infix_anchor {w : List α} (h : anchor w <:+: anchor v) : w = v := by
  have hp := prefix_of_infix_cons h (by simp)
  have hle : w.length ≤ v.length := by simpa using hp.length_le
  have hlen : w.length = v.length := by
    refine le_antisymm hle (not_lt.1 fun hlt ↦ ?_)
    have hmem : (Sum.inr Edge.right : α ⊕ Edge) ∈ w.map .inl ++ [.inr .right] := by simp
    rw [List.prefix_iff_eq_take.1 hp, List.take_append_of_le_length (by simpa using hlt)] at hmem
    simpa using List.mem_of_mem_take hmem
  have := List.append_cancel_right (hp.eq_of_length (by simpa using hlen))
  exact List.map_injective_iff.2 Sum.inl_injective this

theorem anchor_append_append (u x v : List α) :
    anchor (u ++ x ++ v) =
      (.inr .left :: u.map .inl) ++ x.map .inl ++ (v.map .inl ++ [.inr .right]) := by
  simp [anchor]

theorem map_inl_infix_anchor_iff : s.map .inl <:+: anchor v ↔ s <:+: v :=
  ⟨infix_of_map_inl_infix_anchor,
    fun h ↦ (h.map _).trans ⟨[.inr .left], [.inr .right], by simp [anchor]⟩⟩

theorem cons_infix_anchor_iff : .inr .left :: s.map .inl <:+: anchor v ↔ s <+: v :=
  ⟨prefix_of_infix_anchor, fun h ↦
    (List.cons_prefix_cons.2 ⟨rfl, (h.map _).trans (List.prefix_append _ _)⟩).isInfix⟩

theorem append_infix_anchor_iff : s.map .inl ++ [.inr .right] <:+: anchor v ↔ s <:+ v := by
  refine ⟨suffix_of_infix_anchor, fun h ↦ ?_⟩
  obtain ⟨t, ht⟩ := h.map (Sum.inl : α → α ⊕ Edge)
  exact List.IsSuffix.isInfix ⟨.inr .left :: t, by rw [anchor, ← ht]; simp⟩

private theorem eq_map_inl_filterMap {c : List (α ⊕ Edge)} (h : ∀ x ∈ c, x.isLeft) :
    c = (c.filterMap Sum.getLeft?).map .inl := by
  induction c with
  | nil => rfl
  | cons x c ih =>
    obtain ⟨a, rfl⟩ : ∃ a, x = .inl a := Sum.isLeft_iff.1 (h x (by simp))
    simp [← ih fun y hy ↦ h y (by simp [hy])]

theorem infix_anchor_cases {c : List (α ⊕ Edge)} (h : c <:+: anchor v) :
    ∃ s : List α, c = s.map .inl ∨ c = .inr .left :: s.map .inl ∨
      c = s.map .inl ++ [.inr .right] ∨ c = anchor s := by
  have hmap (d : List (α ⊕ Edge)) (hd : d <:+: v.map .inl) :
      d = (d.filterMap Sum.getLeft?).map .inl :=
    eq_map_inl_filterMap fun x hx ↦ by obtain ⟨a, -, rfl⟩ := List.mem_map.1 (hd.subset hx); rfl
  rw [anchor, List.infix_cons_iff] at h
  rcases h with h | h
  · rcases List.prefix_cons_iff.1 h with rfl | ⟨t, rfl, ht⟩
    · exact ⟨[], .inl rfl⟩
    · rcases List.prefix_concat_iff.1 ht with rfl | ht
      · exact ⟨v, .inr (.inr (.inr rfl))⟩
      · exact ⟨_, .inr (.inl (congrArg _ (hmap t ht.isInfix)))⟩
  · rcases List.infix_concat_iff.1 h with h | h
    · rcases List.suffix_concat_iff.1 h with rfl | ⟨t, rfl, ht⟩
      · exact ⟨[], .inl rfl⟩
      · exact ⟨_, .inr (.inr (.inl (congrArg (· ++ _) (hmap t ht.isInfix))))⟩
    · exact ⟨_, .inl (hmap c h)⟩

end Anchor

/-! ### Locally testable stringsets -/

section LocallyTestable

variable {w v : List α} {k : ℕ}

private theorem eq_of_kTestVector_eq (h : w.kTestVector k = v.kTestVector k) (hw : w.length < k) :
    w = v := by
  simp only [List.kTestVector, Prod.mk.injEq, Edge.takeAt_left, Edge.takeAt_right] at h
  obtain ⟨hP, hK, -⟩ := h
  have hv : v.length < k := by
    by_contra hv
    have := ((Set.ext_iff.1 hK (v.take k)).2
      ⟨(List.take_prefix _ _).isInfix, by simp; omega⟩).1.length_le
    simp at this
    omega
  rwa [List.take_of_length_le (by omega), List.take_of_length_le (by omega)] at hP

theorem kTestVector_eq_iff :
    w.kTestVector k = v.kTestVector k ↔
      {c | c <:+: anchor w ∧ c.length ≤ k} = {c | c <:+: anchor v ∧ c.length ≤ k} := by
  constructor
  · have sub (w v : List α) (h : w.kTestVector k = v.kTestVector k) :
        {c | c <:+: anchor w ∧ c.length ≤ k} ⊆ {c | c <:+: anchor v ∧ c.length ≤ k} := by
      rintro c ⟨hc, hck⟩
      refine ⟨?_, hck⟩
      by_cases hw : w.length < k
      · rwa [← eq_of_kTestVector_eq h hw]
      have h' := h
      simp only [List.kTestVector, Prod.mk.injEq, Edge.takeAt_left, Edge.takeAt_right] at h'
      obtain ⟨hP, hK, hQ⟩ := h'
      obtain ⟨s, rfl | rfl | rfl | rfl⟩ := infix_anchor_cases hc
      · rw [map_inl_infix_anchor_iff] at hc ⊢
        obtain ⟨f, hfw, hfk, hsf⟩ := exists_infix_length_eq hc (by simpa using hck) (by omega)
        exact hsf.trans ((Set.ext_iff.1 hK f).1 ⟨hfw, hfk⟩).1
      · rw [cons_infix_anchor_iff] at hc ⊢
        have : s <+: w.take (k - 1) := List.prefix_take_iff.2 ⟨hc, by simp at hck; omega⟩
        rw [hP] at this
        exact this.trans (List.take_prefix _ _)
      · rw [append_infix_anchor_iff] at hc ⊢
        have : s <:+ w.rtake (k - 1) := List.suffix_rtake_iff.2 ⟨hc, by simp at hck; omega⟩
        rw [hQ] at this
        exact this.trans (List.rtake_suffix _ _)
      · obtain rfl := eq_of_anchor_infix_anchor hc
        simp at hck
        omega
    exact fun h ↦ (sub w v h).antisymm (sub v w h.symm)
  · intro hA
    have mem (c : List (α ⊕ Edge)) (hc : c.length ≤ k) : c <:+: anchor w ↔ c <:+: anchor v := by
      simpa [hc] using Set.ext_iff.1 hA c
    simp only [List.kTestVector, Prod.mk.injEq, Edge.takeAt_left, Edge.takeAt_right]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · refine ⟨by simp, Set.ext fun f ↦ ?_, by simp⟩
      simp only [Set.mem_ofPred_eq, List.length_eq_zero_iff]
      constructor <;> rintro ⟨-, rfl⟩ <;> exact ⟨List.nil_infix, rfl⟩
    have pre (w v : List α) (mem : ∀ c : List (α ⊕ Edge), c.length ≤ k →
        c <:+: anchor w → c <:+: anchor v) : w.take (k - 1) <+: v.take (k - 1) :=
      List.prefix_take_iff.2 ⟨cons_infix_anchor_iff.1 (mem _ (by simp; omega)
        (cons_infix_anchor_iff.2 (List.take_prefix _ _))), by simp⟩
    have suf (w v : List α) (mem : ∀ c : List (α ⊕ Edge), c.length ≤ k →
        c <:+: anchor w → c <:+: anchor v) : w.rtake (k - 1) <:+ v.rtake (k - 1) :=
      List.suffix_rtake_iff.2 ⟨append_infix_anchor_iff.1 (mem _ (by simp; omega)
        (append_infix_anchor_iff.2 (List.rtake_suffix _ _))), by simp⟩
    refine ⟨(pre w v fun c hc ↦ (mem c hc).1).eq_of_length
        (le_antisymm (pre w v fun c hc ↦ (mem c hc).1).length_le
          (pre v w fun c hc ↦ (mem c hc).2).length_le), Set.ext fun f ↦ ?_,
      (suf w v fun c hc ↦ (mem c hc).1).eq_of_length
        (le_antisymm (suf w v fun c hc ↦ (mem c hc).1).length_le
          (suf v w fun c hc ↦ (mem c hc).2).length_le)⟩
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hf, rfl⟩
      exact ⟨map_inl_infix_anchor_iff.1 ((mem _ (by simp)).1 (map_inl_infix_anchor_iff.2 hf)), rfl⟩
    · rintro ⟨hf, rfl⟩
      exact ⟨map_inl_infix_anchor_iff.1 ((mem _ (by simp)).2 (map_inl_infix_anchor_iff.2 hf)), rfl⟩

end LocallyTestable

/-! ### Strictly local stringsets -/

section StrictlyLocal

variable {u₁ v₁ u₂ v₂ x : List α} {k : ℕ}

theorem factors_crossover_subset (hx : x.length = k - 1) :
    (wordLanguage (α ⊕ Edge) {.succ}).factors k (WordModel ({·}) (anchor (u₁ ++ x ++ v₂))) ⊆
      (wordLanguage (α ⊕ Edge) {.succ}).factors k (WordModel ({·}) (anchor (u₁ ++ x ++ v₁))) ∪
        (wordLanguage (α ⊕ Edge) {.succ}).factors k (WordModel ({·}) (anchor (u₂ ++ x ++ v₂))) := by
  rw [anchor_append_append, anchor_append_append, anchor_append_append]
  refine (WordModel.factors_append_append_subset (by simp; omega)).trans
    (Set.union_subset_union (WordModel.factors_subset_of_infix ?_)
      (WordModel.factors_subset_of_infix ?_))
  · exact (List.prefix_append _ _).isInfix
  · rw [List.append_assoc]
    exact (List.suffix_append _ _).isInfix

variable {L : _root_.Language α}

theorem mem_of_factors_subset_biUnion (hL : L.SuffixSubstitutionClosed k) (hk : 2 ≤ k)
    {w : List α} (hw : (wordLanguage (α ⊕ Edge) {.succ}).factors k (WordModel ({·}) (anchor w)) ⊆
      ⋃ v ∈ L, (wordLanguage (α ⊕ Edge) {.succ}).factors k (WordModel ({·}) (anchor v))) :
    w ∈ L := by
  have hinfix (c : List (α ⊕ Edge)) (hc : c <:+: anchor w) (hlen : c.length ≤ k) :
      ∃ v ∈ L, c <:+: anchor v := by
    obtain ⟨v, hv, hcv⟩ := Set.mem_iUnion₂.1
      (hw ((WordModel.succDiagram_occurs_iff hlen).2 hc))
    exact ⟨v, hv, (WordModel.succDiagram_occurs_iff hlen).1 hcv⟩
  by_cases hshort : w.length + 2 ≤ k
  · obtain ⟨v, hv, hwv⟩ := hinfix (anchor w) (List.infix_refl _) (by simpa using hshort)
    rwa [eq_of_anchor_infix_anchor hwv]
  refine hL.mem_of_exists_infix hk (by omega) ?_ (fun s hs hlen ↦ ?_) ?_
  · obtain ⟨v, hv, hcv⟩ := hinfix (.inr .left :: (w.take (k - 1)).map .inl)
      (cons_infix_anchor_iff.2 (List.take_prefix _ _)) (by simp; omega)
    exact ⟨v, hv, prefix_of_infix_anchor hcv⟩
  · obtain ⟨v, hv, hcv⟩ := hinfix (s.map .inl) (map_inl_infix_anchor_iff.2 hs) (by simp [hlen])
    exact ⟨v, hv, infix_of_map_inl_infix_anchor hcv⟩
  · obtain ⟨v, hv, hcv⟩ := hinfix ((w.rtake (k - 1)).map .inl ++ [.inr .right])
      (append_infix_anchor_iff.2 (List.rtake_suffix _ _)) (by simp; omega)
    exact ⟨v, hv, suffix_of_infix_anchor hcv⟩

end StrictlyLocal


end Subregular

open Subregular

namespace Language

variable {α : Type u} {L : Language α} {k : ℕ}

/-- A stringset is strictly `k`-piecewise exactly when it is a strictly `k`-local set of
precedence models. -/
theorem isStrictlyPiecewise_iff_wordModel :
    L.IsStrictlyPiecewise k ↔ (wordLanguage α {.prec}).IsStrictlyLocal (WordModel ({·}) ·) k L := by
  rw [isStrictlyLocal_iff]
  constructor
  · intro hL w hw
    rw [← hL.language_self]
    intro s hs hsw
    obtain ⟨v, hv, hsv⟩ := Set.mem_iUnion₂.1 (hw ((WordModel.diagram_occurs_iff hs).2 hsw))
    exact hL.isSublistClosed ((WordModel.diagram_occurs_iff hs).1 hsv) hv
  · intro hS
    refine ⟨L, le_antisymm (fun w hw ↦ hS w fun f hf ↦ ?_) fun w hw s _ hs ↦ ?_⟩
    · obtain ⟨s, hsw, hs, hfs⟩ := WordModel.exists_sublist_of_occurs hf
      exact Set.mem_iUnion₂.2 ⟨s, hw s hs hsw, hfs⟩
    · exact hS s fun f hf ↦ Set.mem_iUnion₂.2 ⟨w, hw, WordModel.factors_subset_of_sublist hs hf⟩

/-- A stringset is strictly `k`-local, for `2 ≤ k`, exactly when it is a strictly `k`-local set of
anchored words ordered by successor. -/
theorem isStrictlyLocal_iff_wordModel (hk : 2 ≤ k) :
    L.IsStrictlyLocal k ↔
      (wordLanguage (α ⊕ Edge) {.succ}).IsStrictlyLocal
        (fun w ↦ WordModel ({·}) (anchor w)) k L := by
  rw [isStrictlyLocal_iff_suffixSubstitutionClosed hk, FirstOrder.Language.isStrictlyLocal_iff]
  refine ⟨fun hL w hw ↦ mem_of_factors_subset_biUnion hL hk hw, fun hS u₁ v₁ u₂ v₂ x hx h₁ h₂ ↦ ?_⟩
  exact (FirstOrder.Language.isStrictlyLocal_iff.2 hS).mem_of_factors_subset_union h₁ h₂
    (factors_crossover_subset hx)

/-- A stringset is tier-based strictly `k`-local, for `2 ≤ k`, exactly when for some tier it is a
strictly `k`-local set of words under successor relativized to the tier. Restricting a word to
its tier positions and taking successor there gives the successor model of its projection, so
the relativized models are those of the projections. -/
theorem isTierStrictlyLocal_iff_wordModel (hk : 2 ≤ k) :
    L.IsTierStrictlyLocal k ↔ ∃ (T : α → Prop) (_ : DecidablePred T),
      (wordLanguage (α ⊕ Edge) {.succ}).IsStrictlyLocal
        (fun w ↦ WordModel ({·}) (anchor (w.filter (T ·)))) k L := by
  constructor
  · rintro ⟨G, rfl⟩
    exact ⟨G.tier, inferInstance,
      ((isStrictlyLocal_iff_wordModel hk).1 ⟨G.permitted, rfl⟩).preimage
        fun w : List α ↦ w.filter (G.tier ·)⟩
  · rintro ⟨T, _, G', rfl⟩
    obtain ⟨G₀, hG₀⟩ := (isStrictlyLocal_iff_wordModel hk).2 ⟨G', rfl⟩
    exact ⟨⟨T, G₀⟩, Set.ext fun w ↦ Set.ext_iff.1 hG₀ (w.filter (T ·))⟩

/-- A stringset is piecewise `k`-testable exactly when it is a locally `k`-testable set of words
under precedence. -/
theorem isPiecewiseTestable_iff_wordModel :
    L.IsPiecewiseTestable k ↔ (wordLanguage α {.prec}).IsLocallyTestable (WordModel ({·}) ·) k L :=
  ⟨fun h _ _ e ↦ h (WordModel.factors_eq_iff_subseqSet.1 e),
    fun h _ _ e ↦ h (WordModel.factors_eq_iff_subseqSet.2 e)⟩

/-- A stringset is locally `k`-testable exactly when it is a locally `k`-testable set of words
between their edges under successor. -/
theorem isLocallyTestable_iff_wordModel :
    L.IsLocallyTestable k ↔
      (wordLanguage (α ⊕ Edge) {.succ}).IsLocallyTestable
        (fun w ↦ WordModel ({·}) (anchor w)) k L := by
  have key (w v : List α) : w.kTestVector k = v.kTestVector k ↔
      (wordLanguage (α ⊕ Edge) {.succ}).factors k (WordModel ({·}) (anchor w)) =
        (wordLanguage (α ⊕ Edge) {.succ}).factors k (WordModel ({·}) (anchor v)) :=
    kTestVector_eq_iff.trans WordModel.factors_eq_iff_infix.symm
  exact ⟨fun h _ _ e ↦ h ((key _ _).2 e), fun h _ _ e ↦ h ((key _ _).1 e)⟩

/-- Over a finite alphabet, a stringset is piecewise `k`-testable exactly when it is a Boolean
combination of strictly `k`-piecewise stringsets. -/
theorem isPiecewiseTestable_iff_mem_closure [Finite α] :
    L.IsPiecewiseTestable k ↔
      L ∈ BooleanSubalgebra.closure {K : Language α | K.IsStrictlyPiecewise k} := by
  have h : {K : Language α | K.IsStrictlyPiecewise k} =
      {S | (wordLanguage α {.prec}).IsStrictlyLocal (WordModel ({·}) ·) k S} :=
    Set.ext fun _ ↦ isStrictlyPiecewise_iff_wordModel
  rw [isPiecewiseTestable_iff_wordModel, FirstOrder.Language.isLocallyTestable_iff_mem_closure, h]

/-- Over a finite alphabet, a stringset is locally `k`-testable, for `2 ≤ k`, exactly when it is a
Boolean combination of strictly `k`-local stringsets. -/
theorem isLocallyTestable_iff_mem_closure [Finite α] (hk : 2 ≤ k) :
    L.IsLocallyTestable k ↔
      L ∈ BooleanSubalgebra.closure {K : Language α | K.IsStrictlyLocal k} := by
  have h : {K : Language α | K.IsStrictlyLocal k} =
      {S | (wordLanguage (α ⊕ Edge) {.succ}).IsStrictlyLocal
        (fun w ↦ WordModel ({·}) (anchor w)) k S} :=
    Set.ext fun _ ↦ isStrictlyLocal_iff_wordModel hk
  rw [isLocallyTestable_iff_wordModel, FirstOrder.Language.isLocallyTestable_iff_mem_closure, h]

/-! ### Multitier locally testable stringsets -/

/-- Over a finite alphabet and for `2 ≤ k`, the multitier locally testable languages are the
multitier extension of the locally `k`-testable languages as well, since the strictly `k`-local
languages generate those. -/
theorem multitier_isLocallyTestable [Finite α] (hk : 2 ≤ k) :
    multitier {K : Language α | K.IsLocallyTestable k} = multitierLocallyTestable k := by
  have h : {K : Language α | K.IsLocallyTestable k} =
      (BooleanSubalgebra.closure {K : Language α | K.IsStrictlyLocal k} : Set (Language α)) :=
    Set.ext fun _ ↦ isLocallyTestable_iff_mem_closure hk
  rw [h, multitier_closure, multitierLocallyTestable]

/-- Over a finite alphabet and for `2 ≤ k`, a language is multitier locally testable with window
`k` exactly when the `k`-test vectors of the tier projections of a word decide its membership. -/
theorem mem_multitierLocallyTestable_iff [Finite α] (hk : 2 ≤ k) :
    L ∈ multitierLocallyTestable k ↔ ∀ w w' : List α,
      (∀ (T : α → Prop) [DecidablePred T],
        (w.filter T).kTestVector k = (w'.filter T).kTestVector k) → (w ∈ L ↔ w' ∈ L) := by
  rw [← multitier_isLocallyTestable hk]
  exact mem_multitier_factorsThrough_iff (List.finite_range_kTestVector k)

end Language
