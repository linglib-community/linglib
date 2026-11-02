module

public import Mathlib.Data.Set.Basic
public import Mathlib.Order.Monotone.Basic
public import Linglib.Semantics.Exhaustification.Excluder
public import Linglib.Semantics.Presupposition.Strawson
public import Linglib.Logic.Trivalent.Pointwise

/-!
# The focus particles *only*, *even* and *too*

This file defines the exclusive *only*, the additives such as *too*, and the scalar presupposition
of *even*. Following Coppock and Beaver, *only* relates its prejacent to alternatives ranked by
strength: it presupposes that some true alternative is at least as strong as the prejacent and
asserts that no true alternative is stronger. The alternatives are indexed, each with a
proposition as its content, so that one operator is *only* over propositions, with contents `id`,
and von Fintel's *only x is P* over individuals on the identity scale; the two
[agree](##Focus.only_eq_eq_only_subset_range) unless two individuals share a predication. An
additive asserts its prejacent and presupposes what *only* asserts to be false, and the
presupposition of *even*, after Karttunen and Peters, is that the prejacent is less likely than
every alternative. On a scale refining entailment *only* is [Strawson downward
entailing](##Focus.isStrawsonDE_only) in its prejacent, and over individuals [in its
predicate](##Focus.isStrawsonDE_only_eq).

## Implementation notes

The scale is a relation `S` on the alternatives, with `S j i` read as `j` being at least as
strong as `i`; over propositions the entailment scale is `(· ⊆ ·)`. Von Fintel's *only x*
presupposes that `x` is `P`; Horn's presupposition that something is `P` gives the same Strawson
facts, as von Fintel notes. Coppock and Beaver's existential presupposition is used rather
than Beaver and Clark's, which also requires the lower-ranked alternatives to be false.
Francescotti weakens the universal force of the presupposition of *even* to a majority
threshold, in `Studies/Francescotti1995.lean`. The presupposition of an additive is existential
and pointwise; Kripke, and Beaver and Clark after him, argue that *too* needs a salient antecedent
in the discourse, which is not modelled here.

## References

* [coppock-beaver-2014]
* [beaver-clark-2008]
* [kripke-2009]
* [rooth-1992]
* [rullmann-2003]
* [von-fintel-1999]
* [horn-1996]
* [karttunen-peters-1979]
* [lahiri-1998]
* [crnic-2014]
* [francescotti-1995]
-/

@[expose] public section

namespace Focus

open Exhaustification

/-! ### *Only* -/

section Only

variable {ι W : Type*} (S : ι → ι → Prop) (C : Set ι) (P : ι → Set W) (i : ι)

/-- `atLeast S C P i` holds where some true alternative in `C` is at least as strong as the
prejacent `i` on the scale `S`, an alternative `j` being true where its content `P j` is
([coppock-beaver-2014]'s MIN). -/
def atLeast : Set W := {w | ∃ j ∈ C, w ∈ P j ∧ S j i}

/-- `atMost S C P i` holds where every true alternative in `C` is at most as strong as the
prejacent `i` on the scale `S` ([coppock-beaver-2014]'s MAX). -/
def atMost : Set W := {w | ∀ j ∈ C, w ∈ P j → S i j}

open Classical in
/-- *Only* over the alternatives `C` ranked by `S`, with contents `P`, presupposes
`atLeast S C P i` and asserts `atMost S C P i` ([coppock-beaver-2014]'s (73)). Over propositions,
`P` is `id`; over individuals, with the identity scale, it is von Fintel's *only x is P*, which
presupposes that `x` is `P` and asserts that nothing else is ([von-fintel-1999]'s (15)). -/
noncomputable def only : W → SignType :=
  (atLeast S C P i).indicator fun w ↦ SignType.ofProp (w ∈ atMost S C P i)

variable {S C P i} {j : ι} {w : W}

@[simp] theorem mem_atLeast : w ∈ atLeast S C P i ↔ ∃ j ∈ C, w ∈ P j ∧ S j i := Iff.rfl

@[simp] theorem mem_atMost : w ∈ atMost S C P i ↔ ∀ j ∈ C, w ∈ P j → S i j := Iff.rfl

@[simp] theorem only_eq_zero_iff : only S C P i w = 0 ↔ w ∉ atLeast S C P i := by
  simp [only]

theorem support_only : Function.support (only S C P i) = atLeast S C P i := by
  ext; simp

@[simp] theorem only_eq_one_iff :
    only S C P i w = 1 ↔ w ∈ atLeast S C P i ∧ w ∈ atMost S C P i := by
  simp [only]

@[simp] theorem only_eq_neg_one_iff :
    only S C P i w = -1 ↔ w ∈ atLeast S C P i ∧ w ∉ atMost S C P i := by
  simp [only]

theorem notMem_atMost (hj : j ∈ C) (hw : w ∈ P j) (h : ¬ S i j) : w ∉ atMost S C P i :=
  fun hm ↦ h (hm j hj hw)

/-- On a scale on which a weaker proposition never outranks a stronger one, strengthening the
prejacent strengthens the assertion. -/
theorem antitone_atMost {S : Set W → Set W → Prop} {C : Set (Set W)}
    (hS : ∀ ⦃p q r⦄, p ⊆ q → S q r → S p r) : Antitone (atMost S C id) :=
  fun _ _ hpq _ hw r hr hwr ↦ hS hpq (hw r hr hwr)

/-! #### The entailment scale -/

section Entailment

variable {C : Set (Set W)} {p : Set W}

theorem atMost_subset : atMost (· ⊆ ·) C id p = excludes C p := rfl

theorem atLeast_subset_subset : atLeast (· ⊆ ·) C id p ⊆ p := fun _ ⟨_, _, hw, hq⟩ ↦ hq hw

theorem atLeast_subset_eq (hp : p ∈ C) : atLeast (· ⊆ ·) C id p = p :=
  atLeast_subset_subset.antisymm fun _ hw ↦ ⟨p, hp, hw, subset_rfl⟩

open Classical in
/-- On the entailment scale, with the prejacent among the alternatives, *only* presupposes its
prejacent and asserts the exclusion ([von-fintel-1999]'s (68a)). -/
theorem only_subset_eq (hp : p ∈ C) :
    only (· ⊆ ·) C id p = p.indicator fun w ↦ SignType.ofProp (w ∈ excludes C p) := by
  rw [only, atLeast_subset_eq hp, atMost_subset]

/-- On the entailment scale *only* is true exactly where the exhaustification
`Exhaustification.exh` is. -/
theorem posSupport_only_subset (hp : p ∈ C) : posSupport (only (· ⊆ ·) C id p) = exh C p := by
  ext w; simp [only_subset_eq hp, exh]

end Entailment

/-! #### The identity scale -/

/-- When the prejacent entails no other alternative, the identity-scale assertion, that every true
alternative is the prejacent, is the entailment-scale one. -/
theorem atMost_eq_eq_atMost_subset {C : Set (Set W)} {p : Set W} (h : ∀ q ∈ C, p ⊆ q → q = p) :
    atMost (· = ·) C id p = atMost (· ⊆ ·) C id p :=
  Set.ext fun _ ↦ (forall₂_congr fun _ _ ↦ imp_congr_right fun _ ↦ eq_comm).trans
    (mem_excludes_iff_forall_eq h).symm

/-- Over individuals on the identity scale, *only x* presupposes that `x` is `P` and asserts that
no other individual is. -/
theorem only_eq_eq_one_iff {P : ι → Set W} {x : ι} (hx : x ∈ C) :
    only (· = ·) C P x w = 1 ↔ w ∈ P x ∧ ∀ y ∈ C, y ≠ x → w ∉ P y := by
  simp only [only_eq_one_iff, mem_atLeast, mem_atMost]
  exact ⟨fun ⟨⟨_, _, hw, h⟩, ha⟩ ↦ ⟨h ▸ hw, fun y hy hyx hwy ↦ hyx (ha y hy hwy).symm⟩,
    fun ⟨hw, ha⟩ ↦ ⟨⟨x, hx, hw, rfl⟩, fun y hy hwy ↦ by_contra fun h ↦ ha y hy (Ne.symm h) hwy⟩⟩

/-! #### Individuals and propositions -/

section Individuals

open Set

variable {P : ι → Set W} {x : ι}

/-- If the prejacent entails no other individual's predication, *only x* over individuals is
*only* over the propositions they generate ([coppock-beaver-2014]'s (93)). -/
theorem only_eq_eq_only_subset_range (hP : ∀ y, P x ⊆ P y → y = x) :
    only (· = ·) univ P x = only (· ⊆ ·) (range P) id (P x) := by
  funext w
  have hx := atLeast_subset_eq (mem_range_self (f := P) x)
  refine SignType.eq_of_eq_zero_iff_of_eq_one_iff (by simp [hx]) ?_
  rw [only_eq_eq_one_iff (mem_univ x), only_eq_one_iff, hx]
  simp only [mem_atMost, forall_mem_range, id, mem_univ, true_implies]
  refine and_congr_right fun _ ↦ ⟨fun h y hw ↦ ?_, fun h y hyx hw ↦ hyx (hP y (h y hw))⟩
  by_cases hyx : y = x
  · exact hyx ▸ subset_rfl
  · exact absurd hw (h y hyx)

/-- Without that condition the two come apart, since two individuals with the same predication
are one alternative proposition, entailed by the prejacent, but two individuals. -/
theorem only_eq_ne_only_subset_range :
    only (· = ·) univ (fun _ : Bool ↦ (univ : Set Unit)) true ≠
      only (· ⊆ ·) (range fun _ : Bool ↦ (univ : Set Unit)) id univ := by
  intro h
  have h0 : only (· ⊆ ·) (range fun _ : Bool ↦ (univ : Set Unit)) id univ () = 1 :=
    only_eq_one_iff.2 ⟨⟨univ, ⟨true, rfl⟩, trivial, subset_rfl⟩,
      fun q ⟨_, hq⟩ _ ↦ hq ▸ subset_rfl⟩
  rw [← h, only_eq_eq_one_iff (mem_univ _)] at h0
  exact h0.2 false trivial Bool.false_ne_true trivial

end Individuals

end Only

/-! ### Additives -/

section Additive

variable {ι W : Type*} (S : ι → ι → Prop) (C : Set ι) (P : ι → Set W) (i : ι)

/-- `additivePresup S C P i` holds where some true alternative in `C` is one that the prejacent
does not reach on the scale `S`, on the identity scale an alternative other than the prejacent
([rullmann-2003]'s (15)) and on the entailment scale one that the prejacent does not entail
([beaver-clark-2008]). -/
def additivePresup : Set W := {w | ∃ j ∈ C, w ∈ P j ∧ ¬ S i j}

open Classical in
/-- An additive particle, *too* or *also*, presupposes `additivePresup S C P i` and asserts its
prejacent `P i`. -/
noncomputable def additive : W → SignType :=
  (additivePresup S C P i).indicator fun w ↦ SignType.ofProp (w ∈ P i)

variable {S C P i} {j : ι} {w : W}

@[simp] theorem mem_additivePresup :
    w ∈ additivePresup S C P i ↔ ∃ j ∈ C, w ∈ P j ∧ ¬ S i j :=
  Iff.rfl

/-- The additive presupposes exactly what *only* asserts to be false. -/
theorem additivePresup_eq_compl_atMost : additivePresup S C P i = (atMost S C P i)ᶜ := by
  ext; simp

@[simp] theorem additive_eq_zero_iff : additive S C P i w = 0 ↔ w ∉ additivePresup S C P i := by
  simp [additive]

theorem support_additive : Function.support (additive S C P i) = additivePresup S C P i := by
  ext; simp

@[simp] theorem additive_eq_one_iff :
    additive S C P i w = 1 ↔ w ∈ additivePresup S C P i ∧ w ∈ P i := by
  simp [additive]

@[simp] theorem additive_eq_neg_one_iff :
    additive S C P i w = -1 ↔ w ∈ additivePresup S C P i ∧ w ∉ P i := by
  simp [additive]

/-- Where the prejacent and the presupposition of *only* hold, *only* is true exactly where the
additive is not. -/
theorem only_eq_one_iff_additive_ne_one (hw : w ∈ P i) (hl : w ∈ atLeast S C P i) :
    only S C P i w = 1 ↔ additive S C P i w ≠ 1 := by
  simp [-mem_atLeast, -mem_atMost, hw, hl, additivePresup_eq_compl_atMost]

theorem additivePresup_mono {C' : Set ι} (h : C ⊆ C') :
    additivePresup S C P i ⊆ additivePresup S C' P i :=
  fun _ ⟨j, hj, hw, hn⟩ ↦ ⟨j, h hj, hw, hn⟩

theorem additivePresup_insert_self (h : S i i) :
    additivePresup S (insert i C) P i = additivePresup S C P i := by
  ext; simp [h]

/-- A scale relating more alternatives gives a stronger presupposition. -/
theorem additivePresup_anti {S' : ι → ι → Prop} (h : ∀ i j, S i j → S' i j) :
    additivePresup S' C P i ⊆ additivePresup S C P i :=
  fun _ ⟨j, hj, hw, hn⟩ ↦ ⟨j, hj, hw, fun hs ↦ hn (h _ _ hs)⟩

section Propositions

variable {C : Set (Set W)} {p q : Set W}

/-- The entailment-scale presupposition is the stronger. -/
theorem additivePresup_subset_subset_eq :
    additivePresup (· ⊆ ·) C id p ⊆ additivePresup (· = ·) C id p :=
  additivePresup_anti fun _ _ h ↦ h.le

/-- When the prejacent entails every alternative the entailment-scale presupposition fails, as in
*Sam is happy. #He's ecstatic too* ([beaver-clark-2008]'s (3.39)). -/
theorem additivePresup_subset_eq_empty (h : ∀ q ∈ C, p ⊆ q) :
    additivePresup (· ⊆ ·) C id p = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ ⟨q, hq, _, hn⟩ ↦ hn (h q hq)

/-- A true alternative other than the prejacent satisfies the identity-scale presupposition, even
one that the prejacent entails. -/
theorem mem_additivePresup_eq (hq : q ∈ C) (hw : w ∈ q) (hne : q ≠ p) :
    w ∈ additivePresup (· = ·) C id p :=
  ⟨q, hq, hw, fun h ↦ hne h.symm⟩

theorem additivePresup_eq_eq_subset (h : ∀ q ∈ C, p ⊆ q → q = p) :
    additivePresup (· = ·) C id p = additivePresup (· ⊆ ·) C id p := by
  rw [additivePresup_eq_compl_atMost, additivePresup_eq_compl_atMost,
    atMost_eq_eq_atMost_subset h]

end Propositions

end Additive

/-! ### *Even* -/

section Even

variable {W α : Type*} [PartialOrder α] {μ : Set W → α} {p q : Set W} {alts : Set (Set W)}

/-- The scalar presupposition of *even* ([karttunen-peters-1979]) under a likelihood `μ` holds
when the prejacent `p` is less likely than every focus alternative. -/
def evenPresup (μ : Set W → α) (p : Set W) (alts : Set (Set W)) : Prop :=
  ∀ q ∈ alts, μ p < μ q

/-- Under a likelihood respecting entailment, an alternative that entails the prejacent is at
least as likely and so refutes the presupposition of *even*. -/
theorem not_evenPresup_of_subset (hμ : Monotone μ) (hq : q ∈ alts) (hqp : q ⊆ p) :
    ¬ evenPresup μ p alts :=
  fun h ↦ lt_irrefl _ (lt_of_lt_of_le (h q hq) (hμ hqp))

/-- When the prejacent entails every alternative, the presupposition of *even* asks only that
no alternative be exactly as likely. -/
theorem evenPresup_iff_ne (hμ : Monotone μ) (h : ∀ q ∈ alts, p ⊆ q) :
    evenPresup μ p alts ↔ ∀ q ∈ alts, μ p ≠ μ q :=
  forall₂_congr fun q hq ↦ lt_iff_le_and_ne.trans (and_iff_right (hμ (h q hq)))

end Even

/-! ### Strawson monotonicity -/

section Strawson

open Presupposition Trivalent

variable {ι W : Type*}

section Propositions

variable {S : Set W → Set W → Prop} (C : Set (Set W))

/-- On a scale refining entailment, *only* is Strawson downward entailing in its prejacent with
the alternatives held fixed ([von-fintel-1999], §3.4; [coppock-beaver-2014], fn. 22). -/
theorem isStrawsonDE_only (hS : ∀ ⦃p q r⦄, p ⊆ q → S q r → S p r) :
    IsStrawsonDE (only S C id) :=
  .of_antitone (a := fun p w ↦ w ∈ atMost S C id p) (fun _ _ hpq ↦ antitone_atMost hS hpq)
    fun _ _ h ↦ by simp_all

/-- On the entailment scale *only* is Strawson anti-additive in its prejacent. -/
theorem isStrawsonAntiAdditive_only_subset : IsStrawsonAntiAdditive (only (· ⊆ ·) C id) :=
  .of_isAntiAdditive (a := fun p w ↦ w ∈ atMost (· ⊆ ·) C id p)
    (fun p q ↦ funext fun w ↦ propext <| by
      show w ∈ Exhaustification.excludes C (p ∪ q) ↔
        w ∈ Exhaustification.excludes C p ∧ w ∈ Exhaustification.excludes C q
      rw [Exhaustification.excludes_union]
      exact Iff.rfl)
    fun _ _ h ↦ by simp_all

theorem isStrawsonDE_only_subset : IsStrawsonDE (only (· ⊆ ·) C id) :=
  (isStrawsonAntiAdditive_only_subset C).isStrawsonDE

/-- *Only* applied to the predication of an individual is Strawson downward entailing in the
predicate, so it licenses NPIs in the verb phrase ([coppock-beaver-2014]'s (93)). -/
theorem isStrawsonDE_only_apply (hS : ∀ ⦃p q r⦄, p ⊆ q → S q r → S p r) (x : ι) :
    IsStrawsonDE fun P : ι → Set W ↦ only S C id (P x) :=
  .of_antitone (a := fun P w ↦ w ∈ atMost S C id (P x))
    (fun _ _ hPQ ↦ antitone_atMost hS (hPQ x)) fun _ _ h ↦ by simp_all

/-- *There only was precipitation in Medford* does not classically entail *there only was rain in
Medford*, whose presupposition, the premise [von-fintel-1999]'s (67) adds, may fail. -/
theorem not_antitone_posSupport_only_subset :
    ¬ Antitone fun p : Set Bool ↦ posSupport (only (· ⊆ ·) {{true}, .univ} id p) :=
  not_antitone_posSupport (p := {true}) (q := .univ) (w := false) (Set.subset_univ _)
    (only_eq_one_iff.2 ⟨⟨.univ, by simp, trivial, subset_rfl⟩, fun q hq hw ↦ by
      rcases hq with rfl | rfl
      exacts [absurd hw (by simp), subset_rfl]⟩)
    (only_eq_zero_iff.2 fun ⟨_, _, hw, hsub⟩ ↦ by simpa using hsub hw)

/-- On a scale ranked by reverse entailment, *only* is not Strawson downward entailing in its
prejacent, as the footnote claims ([coppock-beaver-2014], fn. 22). -/
theorem not_isStrawsonDE_only_superset :
    ¬ IsStrawsonDE (only (· ⊇ ·) ({{true}, .univ} : Set (Set Bool)) id) := fun h ↦ by
  have := h (p := {true}) (q := .univ) (Set.subset_univ _) true
    (only_eq_one_iff.2 ⟨⟨.univ, by simp, trivial, subset_rfl⟩, fun _ _ _ ↦ Set.subset_univ _⟩)
    (by rw [Ne, only_eq_zero_iff, not_not]; exact ⟨{true}, by simp, rfl, subset_rfl⟩)
  exact absurd ((only_eq_one_iff.1 this).2 .univ (by simp) trivial (Set.mem_univ false))
    (by simp)

end Propositions

section Individuals

open Set

variable (x : ι)

/-- Over individuals on the identity scale, *only x* is Strawson anti-additive in its predicate. -/
theorem isStrawsonAntiAdditive_only_eq :
    IsStrawsonAntiAdditive fun P : ι → Set W ↦ only (· = ·) univ P x :=
  .of_isAntiAdditive (a := fun P w ↦ ∀ y, y ≠ x → w ∉ P y)
    (fun _ _ ↦ funext fun _ ↦ propext <| by
      simp only [Pi.sup_apply, Pi.inf_apply, inf_Prop_eq, Set.sup_eq_union, Set.mem_union,
        not_or, imp_and, forall_and])
    fun P w h ↦ by
      have hx : w ∈ P x := by simpa using h
      show only (· = ·) univ P x w = 1 ↔ _
      rw [only_eq_eq_one_iff (mem_univ x)]
      simp [hx]

theorem isStrawsonDE_only_eq : IsStrawsonDE fun P : ι → Set W ↦ only (· = ·) univ P x :=
  (isStrawsonAntiAdditive_only_eq x).isStrawsonDE

/-- *Only John ate vegetables* does not classically entail *only John ate kale*, whose
presupposition may fail ([von-fintel-1999]'s (11)). -/
theorem not_antitone_posSupport_only_eq :
    ¬ Antitone fun P : Bool → Set Unit ↦ posSupport (only (· = ·) univ P true) :=
  not_antitone_posSupport (p := ⊥) (q := fun y ↦ {_u | y = true}) (w := ()) bot_le
    (by rw [only_eq_eq_one_iff (mem_univ _)]; simp) (by simp)

/-- *Only John smokes* does not Strawson-entail *only John smokes or drinks*, which is defined and
false when someone else drinks, so *only* is not upward entailing in its predicate. -/
theorem not_isStrawsonUE_only_eq :
    ¬ IsStrawsonUE fun P : Bool → Set Unit ↦ only (· = ·) univ P true :=
  not_isStrawsonUE (p := fun y ↦ {_u | y = true}) (q := ⊤) (w := ()) le_top
    (by rw [only_eq_eq_one_iff (mem_univ _)]; simp) (by simp)

end Individuals

end Strawson

end Focus
