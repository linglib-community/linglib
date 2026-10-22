/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Agree.Basic

/-!
# Labeling by minimal search

The labeling algorithm is minimal search from a syntactic object for the heads it contains: a head
merged with a phrase labels the result, and two phrases leave a head of each, which label only by a
feature they share by Agree. Search sees the terms every occurrence of which lies inside an
occurrence of the object, so the lower copy of a phrase that has moved on is invisible to it.

## Main definitions

* `Minimalist.LinearizedSyntacticObject.InDomain`: every occurrence of a term lies inside an
  occurrence of another.
* `Minimalist.LinearizedSyntacticObject.FindsHead`, `labelsAt`, `labels`: what minimal search finds.
* `Minimalist.LinearizedSyntacticObject.IsLabeledBy`, `IsLabeledByFeature`, `IsLabeled`.

## Main results

* `Minimalist.LinearizedSyntacticObject.findsHead_iff`: search finds the visible heads that no
  visible head asymmetrically c-commands.
* `labelsAt_merge_head`, `labelsAt_merge_heads`, `labelsAt_merge`: a head merged with a non-head
  labels the result, two heads are both found, two non-heads leave the heads of both.
* `labelsAt_merge_of_not_inDomain`: a daughter that has moved on is invisible.

## Implementation notes

* Search runs on the tree, not on the daughters' labels, so a phrase with a specifier contributes
  the specifier's heads too. Copies of one head count once, and tokens are fresh, as chain
  reduction takes them, so repetitions are never identified.
* Under remnant or sideward movement a head occurring only in a lower copy can be found.

## TODO

* `labelsAt` depends only on the term at a position; the isomorphism between the positions of two
  occurrences is missing.
* On a derivation, labels on the contraction agree with those on the copy object when each lower
  copy is c-commanded by a higher occurrence; stating it needs the contraction's positions
  embedded in the copy object's.

## References

* [chomsky-2013]
-/

@[expose] public section

namespace Minimalist.LinearizedSyntacticObject

open RoseTree SyntacticObject Core.Order

variable (t : LinearizedSyntacticObject)

/-- `y` is in the domain of `x` in `t`: every occurrence of `y` is a term of an occurrence of `x`,
[chomsky-2013]'s condition under which the labeling algorithm searching `x` sees `y`. -/
def InDomain (x y : SyntacticObject) : Prop := ∀ q, t.termAt q = y → ∃ n ≤ q, t.termAt n = x

instance (x y : SyntacticObject) : Decidable (t.InDomain x y) := by
  unfold InDomain; infer_instance

/-- Minimal search from the occurrence at `n` finds the head at `q`: a lexical leaf in the domain of
the term at `n` that no other is closer than. -/
def FindsHead (n q : t.val.Positions) : Prop :=
  (Probe.relativized fun q ↦ (t.termAt q).token?.isSome).Finds
    {q | n ≤ q ∧ t.InDomain (t.termAt n) (t.termAt q)} (t.above t.branching) q

instance (n : t.val.Positions) : DecidablePred (t.FindsHead n) := fun _ ↦ by
  unfold FindsHead; infer_instance

/-- The heads minimal search from the occurrence at `n` finds. -/
def labelsAt (n : t.val.Positions) : Finset LexicalItem.Token :=
  (Finset.univ.filter (t.FindsHead n)).biUnion fun q ↦ (t.termAt q).token?.toFinset

/-- The labels of `x`: the heads minimal search from an occurrence of `x` finds. -/
def labels (x : SyntacticObject) : Finset LexicalItem.Token :=
  (Finset.univ.filter fun n ↦ t.termAt n = x).biUnion t.labelsAt

/-- `x` is labeled by the head `h`: minimal search finds `h` alone. -/
def IsLabeledBy (x : SyntacticObject) (h : LexicalItem.Token) : Prop := t.labels x = {h}

instance (x : SyntacticObject) (h : LexicalItem.Token) : Decidable (t.IsLabeledBy x h) :=
  inferInstanceAs (Decidable (_ = _))

variable {F : Type*} (Agreed : F → LexicalItem.Token → LexicalItem.Token → Prop)

/-- `x` is labeled by the feature `f`: minimal search finds several heads, each two of which share
`f` by Agree, [chomsky-2013]'s label ⟨F, F⟩. -/
def IsLabeledByFeature (x : SyntacticObject) (f : F) : Prop :=
  1 < (t.labels x).card ∧ ∀ h ∈ t.labels x, ∀ h' ∈ t.labels x, h ≠ h' → Agreed f h h'

instance [∀ f, DecidableRel (Agreed f)] (x : SyntacticObject) (f : F) :
    Decidable (t.IsLabeledByFeature Agreed x f) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- `x` is labeled, by a head or by a feature its heads share. -/
def IsLabeled (x : SyntacticObject) : Prop :=
  (∃ h, t.IsLabeledBy x h) ∨ ∃ f, t.IsLabeledByFeature Agreed x f

variable {t Agreed} {n q : t.val.Positions} {x : SyntacticObject}

/-- An object is labeled by a head exactly when minimal search finds one head. -/
theorem exists_isLabeledBy_iff : (∃ h, t.IsLabeledBy x h) ↔ (t.labels x).card = 1 :=
  Finset.card_eq_one.symm

instance [Fintype F] [∀ f, DecidableRel (Agreed f)] (x : SyntacticObject) :
    Decidable (t.IsLabeled Agreed x) :=
  decidable_of_iff ((t.labels x).card = 1 ∨ ∃ f, t.IsLabeledByFeature Agreed x f) <| by
    rw [IsLabeled, exists_isLabeledBy_iff]

theorem mem_labelsAt {h : LexicalItem.Token} :
    h ∈ t.labelsAt n ↔ ∃ q, t.FindsHead n q ∧ (t.termAt q).token? = some h := by
  simp [labelsAt]

theorem mem_labels {h : LexicalItem.Token} :
    h ∈ t.labels x ↔ ∃ n, t.termAt n = x ∧ h ∈ t.labelsAt n := by
  simp [labels]

theorem labelsAt_subset_labels (hn : t.termAt n = x) : t.labelsAt n ⊆ t.labels x :=
  fun _ h ↦ mem_labels.2 ⟨n, hn, h⟩

/-- A head occupies a leaf position. -/
theorem isMax_of_isSome_token? (h : (t.termAt q).token?.isSome) : IsMax q := by
  rw [Positions.isMax_iff]
  by_contra hc
  have hs := isSyntacticObject_subtree q
  rcases hq : q.subtree with ⟨v, cs⟩
  rw [hq] at hs hc
  obtain rfl := eq_bare_of_ne_nil hs hc
  simp [termAt, token?, hq, Vertex.bare] at h

/-- Search finds the visible heads that no visible head asymmetrically c-commands. -/
theorem findsHead_iff : t.FindsHead n q ↔
    (n ≤ q ∧ t.InDomain (t.termAt n) (t.termAt q) ∧ (t.termAt q).token?.isSome) ∧
      ∀ ⦃q'⦄, n ≤ q' → t.InDomain (t.termAt n) (t.termAt q') → (t.termAt q').token?.isSome →
        ¬ (t.val.CCommands q' q ∧ ¬ t.val.CCommands q q') := by
  rw [FindsHead, finds_above_branching_iff fun a ha b hb hab hle ↦
    hab ((isMax_of_isSome_token? ha.2).eq_of_le hle)]
  simp [and_assoc, and_imp]

/-! ### The daughters of a position -/

/-- A position has at most two daughters, since Merge is binary. -/
theorem eq_or_eq_of_covBy {c d e : t.val.Positions} (hc : n ⋖ c) (hd : n ⋖ d) (hcd : c ≠ d)
    (he : n ⋖ e) : e = c ∨ e = d := by
  have hlen : n.subtree.children.length = 2 := by
    have hs := isSyntacticObject_subtree n
    rcases hsub : n.subtree with ⟨v, cs⟩
    rw [hsub] at hs
    refine (SyntacticObject.length_eq_zero_or_two hs).resolve_left fun h0 ↦ ?_
    have hmax : IsMax n := Positions.isMax_iff.2 (by simpa [hsub] using h0)
    exact hmax.not_lt hc.lt
  have hlt : ∀ (p : t.val.Positions) (m : ℕ), p.val.toList = n.val.toList ++ [m] → m < 2 := by
    intro p m hm
    have hp := p.2
    rw [show p.val = ⟨n.val.toList ++ [m]⟩ from TreePath.ext hm] at hp
    obtain ⟨s, hs, hms⟩ := mem_validPaths_append_singleton_iff.1 hp
    rw [n.subtreeAt_eq, Option.some.injEq] at hs
    rw [← hs, hlen] at hms
    exact hms
  obtain ⟨i, hi⟩ := TreePath.covBy_iff.1 (Positions.covBy_iff.1 hc)
  obtain ⟨j, hj⟩ := TreePath.covBy_iff.1 (Positions.covBy_iff.1 hd)
  obtain ⟨k, hk⟩ := TreePath.covBy_iff.1 (Positions.covBy_iff.1 he)
  have := hlt c i hi
  have := hlt d j hj
  have := hlt e k hk
  have hij : i ≠ j := fun h ↦ hcd (Subtype.ext (TreePath.ext (by rw [hi, hj, h])))
  rcases (by omega : k = i ∨ k = j) with rfl | rfl
  · exact .inl (Subtype.ext (TreePath.ext (hk.trans hi.symm)))
  · exact .inr (Subtype.ext (TreePath.ext (hk.trans hj.symm)))

/-- A daughter c-commands every position below its mother outside itself. -/
theorem cCommands_of_covBy {c : t.val.Positions} (hc : n ⋖ c) (hq : n < q) (hcq : ¬ c ≤ q) :
    t.val.CCommands c q := by
  have hc0 : c.val ≠ ⊥ := fun h ↦ (not_lt_bot (a := n)) (hc.lt.trans_eq (Subtype.ext h))
  have hpar : c.val.parent = n.val := by
    rw [← Positions.pred_val, Order.pred_eq_of_covBy hc]
  rw [cCommands_iff_parent_lt hc0 (isBranchingAt_parent fun h ↦ hc0 (congrArg Subtype.val h)),
    hpar]
  exact ⟨hq, fun h ↦ hcq h⟩

/-- Positions below distinct daughters do not c-command one another, unless one is the daughter
itself. -/
theorem not_cCommands_of_covBy {c d q' : t.val.Positions} (hc : n ⋖ c) (hd : n ⋖ d) (hcd : c ≠ d)
    (hcq : c < q) (hdq' : d ≤ q') : ¬ t.val.CCommands q q' := by
  intro h
  have hq0 : q.val ≠ ⊥ := fun h0 ↦ (not_lt_bot (a := c)) (hcq.trans_eq (Subtype.ext h0))
  rw [cCommands_iff_parent_lt hq0 (isBranchingAt_parent fun h0 ↦ hq0 (congrArg Subtype.val h0))]
    at h
  have hcp : c ≤ Order.pred q := Order.le_pred_of_lt hcq
  have hcd' : c.val ≤ q'.val :=
    (Subtype.coe_le_coe.2 hcp).trans ((Positions.pred_val q).symm ▸ h.1.le)
  rcases IsLeftLinear.comparable_of_le_common (Subtype.coe_le_coe.2 hdq') hcd' with h' | h'
  · exact hcd ((hc.eq_or_eq hd.le (Subtype.coe_le_coe.1 h')).resolve_left hd.ne').symm
  · exact hcd ((hd.eq_or_eq hc.le (Subtype.coe_le_coe.1 h')).resolve_left hc.ne')

/-! ### What minimal search finds -/

/-- A visible head merged as a daughter is found. -/
theorem findsHead_of_covBy {c : t.val.Positions} (hc : n ⋖ c) (hh : (t.termAt c).token?.isSome)
    (hv : t.InDomain (t.termAt n) (t.termAt c)) : t.FindsHead n c := by
  have hmax := isMax_of_isSome_token? hh
  refine findsHead_iff.2 ⟨⟨hc.le, hv, hh⟩, fun q' hnq' _ hq' hcc ↦ ?_⟩
  by_cases hqc : q' = c
  · subst hqc
    exact hcc.2 hcc.1
  · have hnq : n < q' :=
      lt_of_le_of_ne hnq' fun h ↦ (isMax_of_isSome_token? hq').not_lt (h ▸ hc.lt)
    exact hcc.2 (cCommands_of_covBy hc hnq fun h ↦ hqc (hmax.eq_of_le h).symm)

/-- A head merged with a non-head labels the result, unless it has moved on. -/
theorem labelsAt_merge_head {h : LexicalItem.Token} (hn : t.termAt n = SyntacticObject.merge ↑h x)
    (hx : x.token? = none) (hh : t.InDomain (SyntacticObject.merge ↑h x) ↑h) :
    t.labelsAt n = {h} := by
  obtain ⟨c, hnc, hc⟩ := immediatelyContains_termAt.1
    (hn ▸ (immediatelyContains_merge _ _ _).2 (.inl rfl) :
      ImmediatelyContains (t.termAt n) ↑h)
  have hcmax : IsMax c := isMax_of_isSome_token? (by simp [hc])
  ext k
  rw [mem_labelsAt, Finset.mem_singleton]
  constructor
  · rintro ⟨q, hfq, hk⟩
    obtain ⟨⟨hnq, -, hq⟩, hmin⟩ := findsHead_iff.1 hfq
    have hqmax := isMax_of_isSome_token? hq
    have hnq' : n < q := lt_of_le_of_ne hnq fun h ↦ hqmax.not_lt (h ▸ hnc.lt)
    obtain ⟨e, hne, heq⟩ := exists_covBy_le_of_lt hnq'
    rcases (immediatelyContains_merge _ _ _).1
      (hn ▸ immediatelyContains_termAt.2 ⟨e, hne, rfl⟩) with he | he
    · rw [← (isMax_of_isSome_token? (by simp [he])).eq_of_le heq, he] at hk
      simpa [eq_comm] using hk
    · have heq' : e < q := lt_of_le_of_ne heq fun h ↦ by
        rw [← h, he, hx] at hq
        simp at hq
      have hec : e ≠ c := fun h ↦ by
        rw [h, hc] at he
        rw [← he] at hx
        simp at hx
      have hqc : q ≠ c := fun h ↦ hnc.2 hne.lt (h ▸ heq')
      refine absurd ⟨cCommands_of_covBy hnc hnq' fun h ↦ hqc (hcmax.eq_of_le h).symm,
        not_cCommands_of_covBy hne hnc hec heq' le_rfl⟩
        (hmin hnc.le (by rw [hn, hc]; exact hh) (by simp [hc]))
  · rintro rfl
    exact ⟨c, findsHead_of_covBy hnc (by simp [hc]) (by rw [hn, hc]; exact hh), by simp [hc]⟩

/-- A head merged with a non-head labels the result, unless it has moved on. -/
theorem isLabeledBy_merge_head {h : LexicalItem.Token}
    (hex : ∃ n, t.termAt n = SyntacticObject.merge ↑h x) (hx : x.token? = none)
    (hh : t.InDomain (SyntacticObject.merge ↑h x) ↑h) :
    t.IsLabeledBy (SyntacticObject.merge ↑h x) h := by
  ext k
  rw [mem_labels, Finset.mem_singleton]
  constructor
  · rintro ⟨n, hn, hk⟩
    rwa [labelsAt_merge_head hn hx hh, Finset.mem_singleton] at hk
  · rintro rfl
    obtain ⟨n, hn⟩ := hex
    exact ⟨n, hn, by rw [labelsAt_merge_head hn hx hh]; exact Finset.mem_singleton_self _⟩

/-- Two heads merged together are both found, unless one has moved on. -/
theorem labelsAt_merge_heads {h h' : LexicalItem.Token}
    (hn : t.termAt n = SyntacticObject.merge ↑h ↑h')
    (hh : t.InDomain (SyntacticObject.merge ↑h ↑h') ↑h)
    (hh' : t.InDomain (SyntacticObject.merge ↑h ↑h') ↑h') : t.labelsAt n = {h, h'} := by
  have child : ∀ y : SyntacticObject, ImmediatelyContains (t.termAt n) y →
      ∃ c, n ⋖ c ∧ t.termAt c = y := fun _ hy ↦ immediatelyContains_termAt.1 hy
  obtain ⟨c, hnc, hc⟩ := child ↑h (hn ▸ (immediatelyContains_merge _ _ _).2 (.inl rfl))
  obtain ⟨d, hnd, hd⟩ := child ↑h' (hn ▸ (immediatelyContains_merge _ _ _).2 (.inr rfl))
  ext k
  rw [mem_labelsAt, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨q, hfq, hk⟩
    obtain ⟨⟨hnq, -, hq⟩, -⟩ := findsHead_iff.1 hfq
    have hnq' : n < q := lt_of_le_of_ne hnq fun h ↦ (isMax_of_isSome_token? hq).not_lt (h ▸ hnc.lt)
    obtain ⟨e, hne, heq⟩ := exists_covBy_le_of_lt hnq'
    rcases (immediatelyContains_merge _ _ _).1
      (hn ▸ immediatelyContains_termAt.2 ⟨e, hne, rfl⟩) with he | he
    · rw [← (isMax_of_isSome_token? (by simp [he])).eq_of_le heq, he] at hk
      exact .inl (by simpa using hk.symm)
    · rw [← (isMax_of_isSome_token? (by simp [he])).eq_of_le heq, he] at hk
      exact .inr (by simpa using hk.symm)
  · rintro (rfl | rfl)
    · exact ⟨c, findsHead_of_covBy hnc (by simp [hc]) (by rw [hn, hc]; exact hh), by simp [hc]⟩
    · exact ⟨d, findsHead_of_covBy hnd (by simp [hd]) (by rw [hn, hd]; exact hh'), by simp [hd]⟩

/-- For a token outside `x`, being in the domain of `merge x y` is being in the domain of `y`, when
`y` has not moved out of `merge x y`. -/
theorem inDomain_merge_iff {y : SyntacticObject} {tok : LexicalItem.Token}
    (hy : t.InDomain (SyntacticObject.merge x y) y) (hx : ¬ ContainsOrEq x ↑tok) :
    t.InDomain (SyntacticObject.merge x y) ↑tok ↔ t.InDomain y ↑tok := by
  refine ⟨fun h p hp ↦ ?_, fun h p hp ↦ ?_⟩
  · obtain ⟨m, hmp, hm⟩ := h p hp
    have hmp' : m < p := lt_of_le_of_ne hmp fun he ↦ by
      have := congrArg SyntacticObject.token? (hm.symm.trans (he ▸ hp))
      simp at this
    obtain ⟨e, hme, hep⟩ := exists_covBy_le_of_lt hmp'
    rcases (immediatelyContains_merge _ _ _).1
      (hm ▸ immediatelyContains_termAt.2 ⟨e, hme, rfl⟩) with he | he
    · exact absurd (he ▸ containsOrEq_termAt.2 ⟨p, hep, hp⟩) hx
    · exact ⟨e, hep, he⟩
  · obtain ⟨m, hmp, hm⟩ := h p hp
    obtain ⟨m', hm'm, hm'⟩ := hy m hm
    exact ⟨m', hm'm.trans hmp, hm'⟩

/-- Below a daughter `d`, search from the mother finds what search from `d` finds, when the two
searches see the same heads below `d` and every head below the other daughter that the mother
sees lies strictly below that daughter. -/
theorem findsHead_iff_of_covBy {c d : t.val.Positions} (hc : n ⋖ c) (hd : n ⋖ d) (hcd : c ≠ d)
    (hdq : d ≤ q)
    (hcv : ∀ q', c ≤ q' → (t.termAt q').token?.isSome →
      t.InDomain (t.termAt n) (t.termAt q') → c < q')
    (hv : ∀ q', d ≤ q' → (t.termAt q').token?.isSome →
      (t.InDomain (t.termAt n) (t.termAt q') ↔ t.InDomain (t.termAt d) (t.termAt q'))) :
    t.FindsHead n q ↔ t.FindsHead d q := by
  rw [findsHead_iff, findsHead_iff]
  constructor
  · rintro ⟨⟨-, hvq, hq⟩, hmin⟩
    exact ⟨⟨hdq, (hv q hdq hq).1 hvq, hq⟩, fun q' hdq' hv' hq' ↦
      hmin (hd.le.trans hdq') ((hv q' hdq' hq').2 hv') hq'⟩
  · rintro ⟨⟨-, hvq, hq⟩, hmin⟩
    refine ⟨⟨hd.le.trans hdq, (hv q hdq hq).2 hvq, hq⟩, fun q' hnq' hv' hq' ↦ ?_⟩
    have hnq'' : n < q' :=
      lt_of_le_of_ne hnq' fun h ↦ (isMax_of_isSome_token? hq').not_lt (h ▸ hc.lt)
    obtain ⟨e, hne, heq⟩ := exists_covBy_le_of_lt hnq''
    rcases eq_or_eq_of_covBy hc hd hcd hne with rfl | rfl
    · exact fun h ↦ not_cCommands_of_covBy hc hd hcd (hcv q' heq hq' hv') hdq h.1
    · exact hmin heq ((hv q' heq hq').1 hv') hq'

/-- Two non-heads leave the heads of both, when neither has moved out of the merge and they share
no token. -/
theorem labelsAt_merge {y : SyntacticObject} {c d : t.val.Positions}
    (hn : t.termAt n = SyntacticObject.merge x y) (hc : n ⋖ c) (hd : n ⋖ d) (hcd : c ≠ d)
    (htc : t.termAt c = x) (htd : t.termAt d = y) (hx : x.token? = none) (hy : y.token? = none)
    (hxy : ∀ tok : LexicalItem.Token, ContainsOrEq x ↑tok → ¬ ContainsOrEq y ↑tok)
    (hdx : t.InDomain (SyntacticObject.merge x y) x)
    (hdy : t.InDomain (SyntacticObject.merge x y) y) :
    t.labelsAt n = t.labelsAt c ∪ t.labelsAt d := by
  have strict : ∀ {e : t.val.Positions}, t.termAt e = x ∨ t.termAt e = y →
      ∀ q', e ≤ q' → (t.termAt q').token?.isSome → e < q' := fun he q' heq hq' ↦
    lt_of_le_of_ne heq fun h ↦ by rcases he with he | he <;> simp_all
  have tokOf : ∀ q' : t.val.Positions, (t.termAt q').token?.isSome →
      ∃ tok : LexicalItem.Token, t.termAt q' = ↑tok := fun q' hq' ↦ by
    obtain ⟨tok, htok⟩ := Option.isSome_iff_exists.1 hq'
    exact ⟨tok, token?_eq_some_iff.1 htok⟩
  have hvc : ∀ q', c ≤ q' → (t.termAt q').token?.isSome →
      (t.InDomain (t.termAt n) (t.termAt q') ↔ t.InDomain (t.termAt c) (t.termAt q')) := by
    intro q' hcq' hq'
    obtain ⟨tok, htok⟩ := tokOf q' hq'
    rw [hn, htc, htok, merge_comm]
    exact inDomain_merge_iff (by rwa [merge_comm] at hdx)
      (hxy tok (htc ▸ htok ▸ containsOrEq_termAt.2 ⟨q', hcq', rfl⟩))
  have hvd : ∀ q', d ≤ q' → (t.termAt q').token?.isSome →
      (t.InDomain (t.termAt n) (t.termAt q') ↔ t.InDomain (t.termAt d) (t.termAt q')) := by
    intro q' hdq' hq'
    obtain ⟨tok, htok⟩ := tokOf q' hq'
    rw [hn, htd, htok]
    exact inDomain_merge_iff hdy fun hxt ↦
      hxy tok hxt (htd ▸ htok ▸ containsOrEq_termAt.2 ⟨q', hdq', rfl⟩)
  ext k
  simp only [Finset.mem_union, mem_labelsAt]
  constructor
  · rintro ⟨q, hfq, hk⟩
    obtain ⟨⟨hnq, -, hq⟩, -⟩ := findsHead_iff.1 hfq
    have hnq' : n < q := lt_of_le_of_ne hnq fun h ↦ (isMax_of_isSome_token? hq).not_lt (h ▸ hc.lt)
    obtain ⟨e, hne, heq⟩ := exists_covBy_le_of_lt hnq'
    rcases eq_or_eq_of_covBy hc hd hcd hne with rfl | rfl
    · exact .inl ⟨q, (findsHead_iff_of_covBy hd hc (Ne.symm hcd) heq
        (fun q' h₁ h₂ _ ↦ strict (.inr htd) q' h₁ h₂) hvc).1 hfq, hk⟩
    · exact .inr ⟨q, (findsHead_iff_of_covBy hc hd hcd heq
        (fun q' h₁ h₂ _ ↦ strict (.inl htc) q' h₁ h₂) hvd).1 hfq, hk⟩
  · rintro (⟨q, hfq, hk⟩ | ⟨q, hfq, hk⟩)
    · exact ⟨q, (findsHead_iff_of_covBy hd hc (Ne.symm hcd) (findsHead_iff.1 hfq).1.1
        (fun q' h₁ h₂ _ ↦ strict (.inr htd) q' h₁ h₂) hvc).2 hfq, hk⟩
    · exact ⟨q, (findsHead_iff_of_covBy hc hd hcd (findsHead_iff.1 hfq).1.1
        (fun q' h₁ h₂ _ ↦ strict (.inl htc) q' h₁ h₂) hvd).2 hfq, hk⟩

/-- A daughter that has moved on is invisible: the heads found are those of the other daughter. -/
theorem labelsAt_merge_of_not_inDomain {y : SyntacticObject} {c d : t.val.Positions}
    (hn : t.termAt n = SyntacticObject.merge x y) (hc : n ⋖ c) (hd : n ⋖ d) (hcd : c ≠ d)
    (htc : t.termAt c = x) (htd : t.termAt d = y)
    (hx : ∀ tok : LexicalItem.Token, ContainsOrEq x ↑tok →
      ¬ t.InDomain (SyntacticObject.merge x y) ↑tok)
    (hxy : ∀ tok : LexicalItem.Token, ContainsOrEq y ↑tok → ¬ ContainsOrEq x ↑tok)
    (hdy : t.InDomain (SyntacticObject.merge x y) y) : t.labelsAt n = t.labelsAt d := by
  have invis : ∀ q', c ≤ q' → (t.termAt q').token?.isSome →
      ¬ t.InDomain (t.termAt n) (t.termAt q') := fun q' hcq' hq' ↦ by
    obtain ⟨tok, htok⟩ := Option.isSome_iff_exists.1 hq'
    rw [token?_eq_some_iff] at htok
    rw [hn, htok]
    exact hx tok (htc ▸ htok ▸ containsOrEq_termAt.2 ⟨q', hcq', rfl⟩)
  have hvd : ∀ q', d ≤ q' → (t.termAt q').token?.isSome →
      (t.InDomain (t.termAt n) (t.termAt q') ↔ t.InDomain (t.termAt d) (t.termAt q')) := by
    intro q' hdq' hq'
    obtain ⟨tok, htok⟩ := Option.isSome_iff_exists.1 hq'
    rw [token?_eq_some_iff] at htok
    rw [hn, htd, htok]
    exact inDomain_merge_iff hdy (hxy tok (htd ▸ htok ▸ containsOrEq_termAt.2 ⟨q', hdq', rfl⟩))
  have hcv : ∀ q', c ≤ q' → (t.termAt q').token?.isSome →
      t.InDomain (t.termAt n) (t.termAt q') → c < q' := fun q' h₁ h₂ h₃ ↦ absurd h₃ (invis q' h₁ h₂)
  ext k
  simp only [mem_labelsAt]
  constructor
  · rintro ⟨q, hfq, hk⟩
    obtain ⟨⟨hnq, hvq, hq⟩, -⟩ := findsHead_iff.1 hfq
    have hnq' : n < q := lt_of_le_of_ne hnq fun h ↦ (isMax_of_isSome_token? hq).not_lt (h ▸ hc.lt)
    obtain ⟨e, hne, heq⟩ := exists_covBy_le_of_lt hnq'
    rcases eq_or_eq_of_covBy hc hd hcd hne with rfl | rfl
    · exact absurd hvq (invis q heq hq)
    · exact ⟨q, (findsHead_iff_of_covBy hc hd hcd heq hcv hvd).1 hfq, hk⟩
  · rintro ⟨q, hfq, hk⟩
    exact ⟨q, (findsHead_iff_of_covBy hc hd hcd (findsHead_iff.1 hfq).1.1 hcv hvd).2 hfq, hk⟩

end Minimalist.LinearizedSyntacticObject
