/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Finset.Pairwise
public import Linglib.Syntax.Minimalist.Probe.SyntacticObject
public import Linglib.Syntax.Minimalist.SyntacticObject.Projection

/-!
# Labeling by minimal search

The labeling algorithm is minimal search from a syntactic object for the heads it contains: a head
merged with a phrase labels the result, and two phrases leave a head of each, which label only by a
feature they agree in. Search sees the terms every occurrence of which lies inside an occurrence of
the object, so the lower copy of a phrase that has moved on is invisible to it.

## Main definitions

* `Minimalist.LinearizedSyntacticObject.InDomain`: every occurrence of a term lies inside an
  occurrence of another.
* `Minimalist.LinearizedSyntacticObject.FindsHead`, `labelsAt`, `labels`: what minimal search finds.
* `Minimalist.LinearizedSyntacticObject.IsLabeledBy`, `IsLabeledByFeature`, `IsLabeled`.
* `Minimalist.LinearizedSyntacticObject.LabelDaughter`, `Minimalist.HeadFunction.label`: the head
  relation labels induce, and the head function it gives.

## Main results

* `Minimalist.LinearizedSyntacticObject.findsHead_iff`: search finds the visible heads that no
  visible head asymmetrically c-commands.
* `isLabeledBy_merge_head`, `labels_merge_heads`: a head merged with a non-head labels the result,
  and two heads are both found.
* `labelsAt_merge`, `labelsAt_merge_of_not_inDomain`: two non-heads leave the heads of both, and a
  daughter that has moved on is invisible.
* `Minimalist.HeadFunction.labelDaughter_of_headDaughterRel_label`: the head daughters of the label
  head function are label daughters.

## Implementation notes

* Search runs on the tree, not on the daughters' labels, so a phrase with a specifier contributes
  the specifier's heads too. Copies of one head count once, and tokens are fresh, as chain
  reduction takes them, so repetitions are never identified.
* Under remnant movement the landing site of the remnant loses the label of what moved out of it,
  and a head occurring only in a lower copy can be found.

## TODO

* `labelsAt` depends only on the term at a position; the isomorphism between the positions of two
  occurrences is missing.
* On a derivation, labels on the contraction agree with those on the copy object when each lower
  copy is c-commanded by a higher occurrence; stating it needs the contraction's positions embedded
  in the copy object's.

## References

* [chomsky-2013]
* [chomsky-2015]
-/

@[expose] public section

namespace Minimalist.LinearizedSyntacticObject

open RoseTree SyntacticObject Core.Order

variable (t : LinearizedSyntacticObject)

/-- `y` is in the domain of `x` in `t`: every occurrence of `y` is a term of an occurrence of `x`,
[chomsky-2013]'s condition under which the labeling algorithm searching `x` sees `y`. -/
def InDomain (y x : SyntacticObject) : Prop := ∀ q, t.termAt q = y → ∃ n ≤ q, t.termAt n = x

instance (y x : SyntacticObject) : Decidable (t.InDomain y x) :=
  inferInstanceAs (Decidable (∀ _, _))

/-- Minimal search from the occurrence at `n` finds the head at `q`: a head in the domain of the
term at `n` that no other is closer than. -/
def FindsHead (n q : t.val.Positions) : Prop :=
  (Probe.relativized fun p ↦ (t.termAt p).token?.isSome).Finds
    {p | n ≤ p ∧ t.InDomain (t.termAt p) (t.termAt n)} (t.above t.branching) q

instance (n : t.val.Positions) : DecidablePred (t.FindsHead n) := fun _ ↦
  inferInstanceAs (Decidable (Probe.Finds _ _ _ _))

/-- The heads minimal search from the occurrence at `n` finds. -/
def labelsAt (n : t.val.Positions) : Finset LexicalItem.Token :=
  (Finset.univ.filter (t.FindsHead n)).biUnion fun q ↦ (t.termAt q).token?.toFinset

/-- The labels of `x`: the heads minimal search from an occurrence of `x` finds. -/
def labels (x : SyntacticObject) : Finset LexicalItem.Token :=
  (Finset.univ.filter fun n ↦ t.termAt n = x).biUnion t.labelsAt

/-- `x` is labeled by the head `a`: minimal search finds `a` alone. -/
def IsLabeledBy (x : SyntacticObject) (a : LexicalItem.Token) : Prop := t.labels x = {a}

instance (x : SyntacticObject) (a : LexicalItem.Token) : Decidable (t.IsLabeledBy x a) :=
  inferInstanceAs (Decidable (_ = _))

variable {F : Type*} (Agreed : F → LexicalItem.Token → LexicalItem.Token → Prop)

/-- `x` is labeled by the feature `f`: minimal search finds several heads, none a daughter of `x`,
each two of which agree in `f`, [chomsky-2015]'s label ⟨F, F⟩ of two phrases. -/
def IsLabeledByFeature (x : SyntacticObject) (f : F) : Prop :=
  (t.labels x).Nontrivial ∧ (∀ a ∈ t.labels x, ¬ ImmediatelyContains x ↑a) ∧
    (t.labels x : Set LexicalItem.Token).Pairwise (Agreed f)

instance [∀ f, DecidableRel (Agreed f)] (x : SyntacticObject) (f : F) :
    Decidable (t.IsLabeledByFeature Agreed x f) :=
  haveI : Decidable (t.labels x).Nontrivial :=
    decidable_of_iff _ Finset.one_lt_card_iff_nontrivial
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- `x` is labeled, by a head or by a feature its heads agree in. -/
def IsLabeled (x : SyntacticObject) : Prop :=
  (∃ a, t.IsLabeledBy x a) ∨ ∃ f, t.IsLabeledByFeature Agreed x f

variable {t Agreed} {n c d q : t.val.Positions} {x y z : SyntacticObject}
  {a b : LexicalItem.Token}

/-- An object is labeled by a head exactly when minimal search finds one head. -/
theorem card_labels_eq_one_iff : (t.labels x).card = 1 ↔ ∃ a, t.IsLabeledBy x a :=
  Finset.card_eq_one

instance : Decidable (∃ a, t.IsLabeledBy x a) := decidable_of_iff _ card_labels_eq_one_iff

instance [Fintype F] [∀ f, DecidableRel (Agreed f)] : Decidable (t.IsLabeled Agreed x) :=
  inferInstanceAs (Decidable (_ ∨ _))

theorem IsLabeledByFeature.mono {Agreed' : F → LexicalItem.Token → LexicalItem.Token → Prop}
    (hA : ∀ f a b, Agreed f a b → Agreed' f a b) {f : F} (h : t.IsLabeledByFeature Agreed x f) :
    t.IsLabeledByFeature Agreed' x f :=
  ⟨h.1, h.2.1, Set.Pairwise.mono' (hA f) h.2.2⟩

theorem IsLabeled.mono {Agreed' : F → LexicalItem.Token → LexicalItem.Token → Prop}
    (hA : ∀ f a b, Agreed f a b → Agreed' f a b) (h : t.IsLabeled Agreed x) :
    t.IsLabeled Agreed' x :=
  h.imp id fun ⟨f, hf⟩ ↦ ⟨f, hf.mono hA⟩

theorem InDomain.trans (hyx : t.InDomain y x) (hxz : t.InDomain x z) : t.InDomain y z :=
  fun q hq ↦ by
    obtain ⟨m, hmq, hm⟩ := hyx q hq
    obtain ⟨m', hm'm, hm'⟩ := hxz m hm
    exact ⟨m', hm'm.trans hmq, hm'⟩

theorem mem_labelsAt : a ∈ t.labelsAt n ↔ ∃ q, t.FindsHead n q ∧ (t.termAt q).token? = some a := by
  simp [labelsAt]

theorem mem_labels : a ∈ t.labels x ↔ ∃ n, t.termAt n = x ∧ a ∈ t.labelsAt n := by
  simp [labels]

theorem labelsAt_subset_labels (hn : t.termAt n = x) : t.labelsAt n ⊆ t.labels x :=
  fun _ h ↦ mem_labels.2 ⟨n, hn, h⟩

/-- When every occurrence of `x` finds the same heads, those are its labels. -/
theorem labels_eq_of_forall_labelsAt_eq {S : Finset LexicalItem.Token}
    (hex : ∃ n, t.termAt n = x) (h : ∀ n, t.termAt n = x → t.labelsAt n = S) : t.labels x = S := by
  ext a
  rw [mem_labels]
  refine ⟨fun ⟨n, hn, ha⟩ ↦ h n hn ▸ ha, fun ha ↦ ?_⟩
  obtain ⟨n, hn⟩ := hex
  exact ⟨n, hn, (h n hn).symm ▸ ha⟩

/-! ### What minimal search finds -/

/-- Search finds the visible heads that no visible head asymmetrically c-commands. -/
theorem findsHead_iff : t.FindsHead n q ↔
    (n ≤ q ∧ t.InDomain (t.termAt q) (t.termAt n) ∧ t.IsHeadAt q) ∧
      ∀ ⦃q'⦄, n ≤ q' → t.InDomain (t.termAt q') (t.termAt n) → t.IsHeadAt q' →
        ¬ (t.val.CCommands q' q ∧ ¬ t.val.CCommands q q') := by
  rw [FindsHead, finds_above_branching_iff]
  · simp [and_assoc, and_imp, IsHeadAt]
  · exact fun p hp _ _ hne hle ↦
      hne ((IsHeadAt.isMax (t := t) (show t.IsHeadAt p from hp.2)).eq_of_le hle)

/-- A head finds itself. -/
theorem findsHead_self (hc : t.IsHeadAt c) : t.FindsHead c c :=
  findsHead_iff.2 ⟨⟨le_rfl, fun p hp ↦ ⟨p, le_rfl, hp⟩, hc⟩, fun _ hcq' _ _ hcc ↦
    hcc.2 ((hc.isMax.eq_of_le hcq').symm ▸ hcc.1)⟩

/-- A visible head merged as a daughter is found. -/
theorem findsHead_of_covBy (hc : n ⋖ c) (hh : t.IsHeadAt c)
    (hv : t.InDomain (t.termAt c) (t.termAt n)) : t.FindsHead n c := by
  refine findsHead_iff.2 ⟨⟨hc.le, hv, hh⟩, fun q' hnq' _ hq' hcc ↦ ?_⟩
  obtain rfl | hqc := eq_or_ne q' c
  · exact hcc.2 hcc.1
  · exact hcc.2 (cCommands_of_covBy hc (lt_of_le_of_ne hnq' fun h ↦ (h ▸ hq').isMax.not_lt hc.lt)
      fun h ↦ hqc (hh.isMax.eq_of_le h).symm)

/-- A head merged with a non-head labels the result, unless it has moved on. -/
theorem labelsAt_merge_head (hn : t.termAt n = SyntacticObject.merge ↑a x)
    (hx : x.token? = none) (ha : t.InDomain ↑a (SyntacticObject.merge ↑a x)) :
    t.labelsAt n = {a} := by
  obtain ⟨c, hnc, hc⟩ := exists_covBy_termAt_eq_left hn
  have hch : t.IsHeadAt c := isHeadAt_iff.2 ⟨a, hc⟩
  ext k
  rw [mem_labelsAt, Finset.mem_singleton]
  constructor
  · rintro ⟨q, hfq, hk⟩
    obtain ⟨⟨hnq, -, hq⟩, hmin⟩ := findsHead_iff.1 hfq
    obtain ⟨e, hne, heq⟩ := hq.exists_covBy_le (not_isMax_of_lt hnc.lt) hnq
    rcases termAt_eq_or_eq_of_covBy hn hne with he | he
    · rw [← (isHeadAt_iff.2 ⟨a, he⟩).isMax.eq_of_le heq, he] at hk
      simpa [eq_comm] using hk
    · have heq' : e < q := lt_of_le_of_ne heq fun h ↦ by
        rw [← h] at hq
        simp [IsHeadAt, he, hx] at hq
      have hec : e ≠ c := fun h ↦ by
        rw [h, hc] at he
        rw [← he] at hx
        simp at hx
      have hqc : q ≠ c := fun h ↦ hnc.2 hne.lt (h ▸ heq')
      exact absurd ⟨cCommands_of_covBy hnc (hne.lt.trans_le heq) fun h ↦
          hqc (hch.isMax.eq_of_le h).symm, not_cCommands_of_covBy hne hnc hec heq' le_rfl⟩
        (hmin hnc.le (by rw [hn, hc]; exact ha) hch)
  · rintro rfl
    exact ⟨c, findsHead_of_covBy hnc hch (by rw [hn, hc]; exact ha), by simp [hc]⟩

theorem isLabeledBy_merge_head (hex : ∃ n, t.termAt n = SyntacticObject.merge ↑a x)
    (hx : x.token? = none) (ha : t.InDomain ↑a (SyntacticObject.merge ↑a x)) :
    t.IsLabeledBy (SyntacticObject.merge ↑a x) a :=
  labels_eq_of_forall_labelsAt_eq hex fun _ hn ↦ labelsAt_merge_head hn hx ha

/-- Two heads merged together are both found, unless one has moved on. -/
theorem labelsAt_merge_heads (hn : t.termAt n = SyntacticObject.merge ↑a ↑b)
    (ha : t.InDomain ↑a (SyntacticObject.merge ↑a ↑b))
    (hb : t.InDomain ↑b (SyntacticObject.merge ↑a ↑b)) : t.labelsAt n = {a, b} := by
  obtain ⟨c, hnc, hc⟩ := exists_covBy_termAt_eq_left hn
  obtain ⟨d, hnd, hd⟩ := exists_covBy_termAt_eq_right hn
  ext k
  rw [mem_labelsAt, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨q, hfq, hk⟩
    obtain ⟨⟨hnq, -, hq⟩, -⟩ := findsHead_iff.1 hfq
    obtain ⟨e, hne, heq⟩ := hq.exists_covBy_le (not_isMax_of_lt hnc.lt) hnq
    rcases termAt_eq_or_eq_of_covBy hn hne with he | he <;>
      rw [← (isHeadAt_iff.2 ⟨_, he⟩).isMax.eq_of_le heq, he] at hk
    · exact .inl (by simpa using hk.symm)
    · exact .inr (by simpa using hk.symm)
  · rintro (rfl | rfl)
    · exact ⟨c, findsHead_of_covBy hnc (isHeadAt_iff.2 ⟨_, hc⟩) (by rw [hn, hc]; exact ha),
        by simp [hc]⟩
    · exact ⟨d, findsHead_of_covBy hnd (isHeadAt_iff.2 ⟨_, hd⟩) (by rw [hn, hd]; exact hb),
        by simp [hd]⟩

theorem labels_merge_heads (hex : ∃ n, t.termAt n = SyntacticObject.merge ↑a ↑b)
    (ha : t.InDomain ↑a (SyntacticObject.merge ↑a ↑b))
    (hb : t.InDomain ↑b (SyntacticObject.merge ↑a ↑b)) :
    t.labels (SyntacticObject.merge ↑a ↑b) = {a, b} :=
  labels_eq_of_forall_labelsAt_eq hex fun _ hn ↦ labelsAt_merge_heads hn ha hb

/-! ### Search below a daughter -/

/-- Where `x` immediately contains only `z` and `w`, a token outside `z` is in the domain of `x`
exactly when it is in the domain of `w`, provided `w` has not moved out of `x`. -/
theorem inDomain_iff_of_immediatelyContains {w : SyntacticObject} {tok : LexicalItem.Token}
    (hx : ∀ y, ImmediatelyContains x y → y = z ∨ y = w) (hxt : x.token? = none)
    (hw : t.InDomain w x) (hz : ¬ ContainsOrEq z ↑tok) :
    t.InDomain ↑tok x ↔ t.InDomain ↑tok w := by
  refine ⟨fun h p hp ↦ ?_, fun h ↦ h.trans hw⟩
  obtain ⟨m, hmp, hm⟩ := h p hp
  have hmp' : m < p := lt_of_le_of_ne hmp fun he ↦ by
    have := congrArg SyntacticObject.token? (hm.symm.trans (he ▸ hp))
    simp [hxt] at this
  obtain ⟨e, hme, hep⟩ := exists_covBy_le_of_lt hmp'
  rcases hx _ (hm ▸ immediatelyContains_termAt.2 ⟨e, hme, rfl⟩) with he | he
  · exact absurd (he ▸ containsOrEq_termAt.2 ⟨p, hep, hp⟩) hz
  · exact ⟨e, hep, he⟩

/-- Below a daughter `d` sharing no token with its sister, the mother's search and `d`'s see the
same heads, when `d` has not moved out of the mother. -/
theorem inDomain_iff_of_covBy {q' : t.val.Positions} (hc : n ⋖ c) (hd : n ⋖ d) (hcd : c ≠ d)
    (hdisj : Disjoint (t.termAt c).yield (t.termAt d).yield)
    (hv : t.InDomain (t.termAt d) (t.termAt n)) (hdq' : d ≤ q') (hq' : t.IsHeadAt q') :
    t.InDomain (t.termAt q') (t.termAt n) ↔ t.InDomain (t.termAt q') (t.termAt d) := by
  obtain ⟨tok, htok⟩ := isHeadAt_iff.1 hq'
  have hn : (t.termAt n).token? = none :=
    Option.not_isSome_iff_eq_none.1 fun h ↦ not_isMax_of_lt hc.lt (IsHeadAt.isMax (t := t) h)
  rw [htok]
  refine inDomain_iff_of_immediatelyContains
    (fun _ hy ↦ (immediatelyContains_termAt_iff_of_covBy hc hd hcd).1 hy) hn hv fun hct ↦
      Multiset.disjoint_left.1 hdisj (mem_yield_iff.2 (mem_terms.2 hct)) ?_
  exact mem_yield_iff.2 (mem_terms.2 (htok ▸ containsOrEq_termAt.2 ⟨q', hdq', rfl⟩))

/-- Below a daughter `d`, the mother's search finds what `d`'s finds, when the two see the same
heads below `d` and the other daughter is no visible head. -/
theorem findsHead_iff_of_covBy (hc : n ⋖ c) (hd : n ⋖ d) (hcd : c ≠ d) (hdq : d ≤ q)
    (hcv : t.IsHeadAt c → ¬ t.InDomain (t.termAt c) (t.termAt n))
    (hv : ∀ q', d ≤ q' → t.IsHeadAt q' →
      (t.InDomain (t.termAt q') (t.termAt n) ↔ t.InDomain (t.termAt q') (t.termAt d))) :
    t.FindsHead n q ↔ t.FindsHead d q := by
  rw [findsHead_iff, findsHead_iff]
  constructor
  · rintro ⟨⟨-, hvq, hq⟩, hmin⟩
    exact ⟨⟨hdq, (hv q hdq hq).1 hvq, hq⟩, fun q' hdq' hv' hq' ↦
      hmin (hd.le.trans hdq') ((hv q' hdq' hq').2 hv') hq'⟩
  · rintro ⟨⟨-, hvq, hq⟩, hmin⟩
    refine ⟨⟨hd.le.trans hdq, (hv q hdq hq).2 hvq, hq⟩, fun q' hnq' hv' hq' ↦ ?_⟩
    obtain ⟨e, hne, heq⟩ := hq'.exists_covBy_le (not_isMax_of_lt hc.lt) hnq'
    rcases eq_or_eq_of_covBy hc hd hcd hne with he | he
    · have hcq : c < q' := lt_of_le_of_ne (he ▸ heq) fun h ↦ hcv (h ▸ hq') (h ▸ hv')
      exact fun h ↦ not_cCommands_of_covBy hc hd hcd hcq hdq h.1
    · exact hmin (he ▸ heq) ((hv q' (he ▸ heq) hq').1 hv') hq'

/-- Two non-heads leave the heads of both, when neither has moved out of their merge and they
share no token. -/
theorem labelsAt_merge (hc : n ⋖ c) (hd : n ⋖ d) (hcd : c ≠ d) (hch : ¬ t.IsHeadAt c)
    (hdh : ¬ t.IsHeadAt d) (hdisj : Disjoint (t.termAt c).yield (t.termAt d).yield)
    (hvc : t.InDomain (t.termAt c) (t.termAt n)) (hvd : t.InDomain (t.termAt d) (t.termAt n)) :
    t.labelsAt n = t.labelsAt c ∪ t.labelsAt d := by
  have findC : ∀ {q}, c ≤ q → (t.FindsHead n q ↔ t.FindsHead c q) := fun hcq ↦
    findsHead_iff_of_covBy hd hc hcd.symm hcq (absurd · hdh)
      fun _ h₁ h₂ ↦ inDomain_iff_of_covBy hd hc hcd.symm hdisj.symm hvc h₁ h₂
  have findD : ∀ {q}, d ≤ q → (t.FindsHead n q ↔ t.FindsHead d q) := fun hdq ↦
    findsHead_iff_of_covBy hc hd hcd hdq (absurd · hch)
      fun _ h₁ h₂ ↦ inDomain_iff_of_covBy hc hd hcd hdisj hvd h₁ h₂
  ext k
  simp only [Finset.mem_union, mem_labelsAt]
  constructor
  · rintro ⟨q, hfq, hk⟩
    obtain ⟨⟨hnq, -, hq⟩, -⟩ := findsHead_iff.1 hfq
    obtain ⟨e, hne, heq⟩ := hq.exists_covBy_le (not_isMax_of_lt hc.lt) hnq
    rcases eq_or_eq_of_covBy hc hd hcd hne with he | he
    · exact .inl ⟨q, (findC (he ▸ heq)).1 hfq, hk⟩
    · exact .inr ⟨q, (findD (he ▸ heq)).1 hfq, hk⟩
  · rintro (⟨q, hfq, hk⟩ | ⟨q, hfq, hk⟩)
    · exact ⟨q, (findC (findsHead_iff.1 hfq).1.1).2 hfq, hk⟩
    · exact ⟨q, (findD (findsHead_iff.1 hfq).1.1).2 hfq, hk⟩

/-- A daughter that has moved on is invisible: the heads found are those of the other daughter. -/
theorem labelsAt_merge_of_not_inDomain (hc : n ⋖ c) (hd : n ⋖ d) (hcd : c ≠ d)
    (hcv : ∀ tok ∈ (t.termAt c).yield, ¬ t.InDomain ↑tok (t.termAt n))
    (hdisj : Disjoint (t.termAt c).yield (t.termAt d).yield)
    (hvd : t.InDomain (t.termAt d) (t.termAt n)) : t.labelsAt n = t.labelsAt d := by
  have invis : ∀ q', c ≤ q' → t.IsHeadAt q' → ¬ t.InDomain (t.termAt q') (t.termAt n) :=
    fun q' hcq' hq' ↦ by
      obtain ⟨tok, htok⟩ := isHeadAt_iff.1 hq'
      exact htok ▸ hcv tok (mem_yield_iff.2 (mem_terms.2
        (htok ▸ containsOrEq_termAt.2 ⟨q', hcq', rfl⟩)))
  have findD : ∀ {q}, d ≤ q → (t.FindsHead n q ↔ t.FindsHead d q) := fun hdq ↦
    findsHead_iff_of_covBy hc hd hcd hdq (invis c le_rfl)
      fun _ h₁ h₂ ↦ inDomain_iff_of_covBy hc hd hcd hdisj hvd h₁ h₂
  ext k
  simp only [mem_labelsAt]
  constructor
  · rintro ⟨q, hfq, hk⟩
    obtain ⟨⟨hnq, hvq, hq⟩, -⟩ := findsHead_iff.1 hfq
    obtain ⟨e, hne, heq⟩ := hq.exists_covBy_le (not_isMax_of_lt hc.lt) hnq
    rcases eq_or_eq_of_covBy hc hd hcd hne with he | he
    · exact absurd hvq (invis q (he ▸ heq) hq)
    · exact ⟨q, (findD (he ▸ heq)).1 hfq, hk⟩
  · rintro ⟨q, hfq, hk⟩
    exact ⟨q, (findD (findsHead_iff.1 hfq).1.1).2 hfq, hk⟩

/-! ### The head relation of labels -/

variable (t) in
/-- `c` is the label daughter of `n`: a daughter containing the one head minimal search from `n`
finds. -/
def LabelDaughter (n c : t.val.Positions) : Prop :=
  n ⋖ c ∧ ∃ a, t.labelsAt n = {a} ∧ a ∈ t.labelsAt c

/-- A head merged with a non-head not containing it is the label daughter. -/
theorem labelDaughter_iff_of_merge_head (hn : t.termAt n = SyntacticObject.merge ↑a x)
    (hx : x.token? = none) (ha : t.InDomain ↑a (SyntacticObject.merge ↑a x))
    (hax : a ∉ x.yield) : t.LabelDaughter n c ↔ n ⋖ c ∧ t.termAt c = ↑a := by
  rw [LabelDaughter, labelsAt_merge_head hn hx ha]
  refine ⟨fun ⟨hnc, k, hk, hkc⟩ ↦ ⟨hnc, ?_⟩, fun ⟨hnc, hc⟩ ↦ ⟨hnc, a, rfl, ?_⟩⟩
  · obtain rfl := Finset.singleton_injective hk
    obtain ⟨q, hfq, hq⟩ := mem_labelsAt.1 hkc
    rcases termAt_eq_or_eq_of_covBy hn hnc with he | he
    · exact he
    · refine absurd (mem_yield_iff.2 (mem_terms.2 ?_)) hax
      exact he ▸ token?_eq_some_iff.1 hq ▸ containsOrEq_termAt.2 ⟨q, (findsHead_iff.1 hfq).1.1, rfl⟩
  · exact mem_labelsAt.2 ⟨c, findsHead_self (isHeadAt_iff.2 ⟨a, hc⟩), by simp [hc]⟩

end Minimalist.LinearizedSyntacticObject

namespace Minimalist.HeadFunction

open RoseTree Core.Order PhraseStructure

/-- The label head function, [chomsky-2013]'s: the head daughter of a position is the daughter
containing the one head minimal search from it finds, and there is none where search finds no head
or several. -/
def label : HeadFunction := fun t x ↦
  if hx : x ∈ t.val.validPaths then
    (List.range 2).find? fun i ↦
      if hc : (⟨x.toList ++ [i]⟩ : TreePath) ∈ t.val.validPaths then
        decide ((t.labelsAt ⟨x, hx⟩).card = 1 ∧ t.labelsAt ⟨x, hx⟩ ⊆ t.labelsAt ⟨_, hc⟩)
      else false
  else none

/-- The head daughters of the label head function are label daughters. -/
theorem labelDaughter_of_headDaughterRel_label {t : LinearizedSyntacticObject}
    {n c : t.val.Positions} (h : headDaughterRel (label t) n.val c.val) : t.LabelDaughter n c := by
  obtain ⟨i, hi, hc⟩ := h
  have hci : (⟨n.val.toList ++ [i]⟩ : TreePath) = c.val := TreePath.ext hc.symm
  simp only [label, dite_eq_left n.2] at hi
  have hp := List.find?_some hi
  rw [dite_eq_left (hci ▸ c.2), decide_eq_true_eq] at hp
  obtain ⟨hcard, hsub⟩ := hp
  obtain ⟨a, ha⟩ := Finset.card_eq_one.1 hcard
  have hcov : n ⋖ c := Positions.covBy_iff.2 (TreePath.covBy_iff.2 ⟨i, hc⟩)
  refine ⟨hcov, a, ha, ?_⟩
  have : (⟨⟨n.val.toList ++ [i]⟩, hci ▸ c.2⟩ : t.val.Positions) = c := Subtype.ext hci
  exact this ▸ hsub (ha ▸ Finset.mem_singleton_self a)

end Minimalist.HeadFunction
