module

public import Mathlib.Data.Set.Basic
public import Mathlib.Order.Monotone.Basic
public import Linglib.Semantics.Exhaustification.Excluder
public import Linglib.Logic.Trivalent.Pointwise

/-!
# The focus particles *only*, *even* and *too*

This file defines the exclusive *only*, the additives such as *too*, and the scalar
presupposition of *even*, with propositions as `Set W`. Following Coppock and Beaver, *only*
relates its prejacent to a set of alternative propositions ranked by strength: it presupposes that
some true alternative is at least as strong as the prejacent and asserts that no true alternative
is stronger. On the
entailment scale the assertion is the exclusion `Exhaustification.excludes`, and with the
prejacent among the alternatives the presupposition is the prejacent itself, von Fintel's entry
for propositional *only*; on the identity scale the assertion is Rooth's.

An additive particle asserts its prejacent and presupposes what *only* asserts to be false, that
some true alternative lies beyond the prejacent on the scale. On the identity scale this is
Rullmann's true alternative other than the prejacent, and on the entailment scale Beaver and
Clark's true alternative that the prejacent does not entail, the stronger of the two.

A likelihood is a monotone map from propositions into a partial order, so that a stronger
proposition is at most as likely; the presupposition of *even*, after Karttunen and Peters, is
that the prejacent is less likely than every focus alternative.

## Main definitions

* `Focus.Particles.atLeast`, `Focus.Particles.atMost`: some true alternative is at least as
  strong as the prejacent, and no true alternative is stronger.
* `Focus.Particles.only`: the exclusive, presupposing `atLeast` and asserting `atMost`.
* `Focus.Particles.additivePresup`, `Focus.Particles.additive`: the presupposition of an additive
  particle, the complement of `atMost`, and the additive, presupposing it and asserting the
  prejacent.
* `Focus.Particles.evenPresup`: the prejacent is less likely than every alternative.

## Main results

* `Focus.Particles.only_subset_eq`, `Focus.Particles.posSupport_only_subset`: on the entailment
  scale *only* presupposes its prejacent and asserts the exclusion, and is true exactly where the
  exhaustification `Exhaustification.exh` is.
* `Focus.Particles.atMost_eq_eq_atMost_subset`: the identity-scale assertion is the
  entailment-scale one when the prejacent entails no other alternative.
* `Focus.Particles.antitone_atMost`: on a scale refining entailment, strengthening the prejacent
  strengthens the assertion.
* `Focus.Particles.additivePresup_eq_compl_atMost`,
  `Focus.Particles.only_eq_one_iff_additive_ne_one`: the additive presupposes what *only* denies,
  so where the prejacent and the presupposition of *only* hold, exactly one of the two is true.
* `Focus.Particles.additivePresup_subset_eq_empty`, `Focus.Particles.mem_additivePresup_eq`: an
  alternative the prejacent entails satisfies the identity-scale presupposition but not the
  entailment-scale one, Beaver and Clark's *Sam is happy. #He's ecstatic too*.
* `Focus.Particles.not_evenPresup_of_subset`: under a monotone likelihood an alternative that
  entails the prejacent refutes the presupposition of *even*, the clash from which Lahiri derives
  the distribution of *even one* items.
* `Focus.Particles.evenPresup_iff_ne`: when the prejacent entails every alternative, the
  presupposition asks only that no alternative be exactly as likely.

## Implementation notes

The scale is a relation `S`, with `S q p` read as `q` being at least as strong as `p`; the
entailment scale is `(· ⊆ ·)`. Coppock and Beaver's existential presupposition is used rather
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
* [karttunen-peters-1979]
* [lahiri-1998]
* [crnic-2014]
* [francescotti-1995]
-/

@[expose] public section

namespace Focus.Particles

open Exhaustification

/-! ### *Only* -/

section Only

variable {W : Type*} (S : Set W → Set W → Prop) (C : Set (Set W)) (p : Set W)

/-- `atLeast S C p` holds where some true alternative in `C` is at least as strong as `p` on the
scale `S` ([coppock-beaver-2014]'s MIN). -/
def atLeast : Set W := {w | ∃ q ∈ C, w ∈ q ∧ S q p}

/-- `atMost S C p` holds where every true alternative in `C` is at most as strong as `p` on the
scale `S` ([coppock-beaver-2014]'s MAX). -/
def atMost : Set W := {w | ∀ q ∈ C, w ∈ q → S p q}

open Classical in
/-- *Only p* over the alternatives `C` ranked by `S` presupposes `atLeast S C p` and asserts
`atMost S C p` ([coppock-beaver-2014]'s (73)). -/
noncomputable def only : W → SignType :=
  (atLeast S C p).indicator fun w ↦ SignType.ofProp (w ∈ atMost S C p)

variable {S C p} {q : Set W} {w : W}

@[simp] theorem mem_atLeast : w ∈ atLeast S C p ↔ ∃ q ∈ C, w ∈ q ∧ S q p := Iff.rfl

@[simp] theorem mem_atMost : w ∈ atMost S C p ↔ ∀ q ∈ C, w ∈ q → S p q := Iff.rfl

@[simp] theorem only_eq_zero_iff : only S C p w = 0 ↔ w ∉ atLeast S C p := by
  simp [only]

theorem support_only : Function.support (only S C p) = atLeast S C p := by
  ext; simp

@[simp] theorem only_eq_one_iff : only S C p w = 1 ↔ w ∈ atLeast S C p ∧ w ∈ atMost S C p := by
  simp [only]

@[simp] theorem only_eq_neg_one_iff :
    only S C p w = -1 ↔ w ∈ atLeast S C p ∧ w ∉ atMost S C p := by
  simp [only]

theorem notMem_atMost (hq : q ∈ C) (hw : w ∈ q) (h : ¬ S p q) : w ∉ atMost S C p :=
  fun hm ↦ h (hm q hq hw)

/-- On a scale on which a weaker proposition never outranks a stronger one, strengthening the
prejacent strengthens the assertion. -/
theorem antitone_atMost (hS : ∀ ⦃p q r⦄, p ⊆ q → S q r → S p r) : Antitone (atMost S C) :=
  fun _ _ hpq _ hw r hr hwr ↦ hS hpq (hw r hr hwr)

/-! #### The entailment scale -/

theorem atMost_subset : atMost (· ⊆ ·) C p = excludes C p := rfl

theorem atLeast_subset_subset : atLeast (· ⊆ ·) C p ⊆ p := fun _ ⟨_, _, hw, hq⟩ ↦ hq hw

theorem atLeast_subset_eq (hp : p ∈ C) : atLeast (· ⊆ ·) C p = p :=
  atLeast_subset_subset.antisymm fun _ hw ↦ ⟨p, hp, hw, subset_rfl⟩

open Classical in
/-- On the entailment scale, with the prejacent among the alternatives, *only* presupposes its
prejacent and asserts the exclusion ([von-fintel-1999]'s (68a)). -/
theorem only_subset_eq (hp : p ∈ C) :
    only (· ⊆ ·) C p = p.indicator fun w ↦ SignType.ofProp (w ∈ excludes C p) := by
  rw [only, atLeast_subset_eq hp, atMost_subset]

/-- On the entailment scale *only* is true exactly where the exhaustification
`Exhaustification.exh` is. -/
theorem posSupport_only_subset (hp : p ∈ C) : posSupport (only (· ⊆ ·) C p) = exh C p := by
  ext w; simp [only_subset_eq hp, exh]

/-! #### The identity scale -/

/-- When the prejacent entails no other alternative, the identity-scale assertion, that every true
alternative is the prejacent, is the entailment-scale one. -/
theorem atMost_eq_eq_atMost_subset (h : ∀ q ∈ C, p ⊆ q → q = p) :
    atMost (· = ·) C p = atMost (· ⊆ ·) C p :=
  Set.ext fun _ ↦ (forall₂_congr fun _ _ ↦ imp_congr_right fun _ ↦ eq_comm).trans
    (mem_excludes_iff_forall_eq h).symm

end Only

/-! ### Additives -/

section Additive

variable {W : Type*} (S : Set W → Set W → Prop) (C : Set (Set W)) (p : Set W)

/-- `additivePresup S C p` holds where some true alternative in `C` is one that `p` does not reach
on the scale `S`, on the identity scale an alternative other than the prejacent
([rullmann-2003]'s (15)) and on the entailment scale one that the prejacent does not entail
([beaver-clark-2008]). -/
def additivePresup : Set W := {w | ∃ q ∈ C, w ∈ q ∧ ¬ S p q}

open Classical in
/-- An additive particle, *too* or *also*, presupposes `additivePresup S C p` and asserts its
prejacent `p`. -/
noncomputable def additive : W → SignType :=
  (additivePresup S C p).indicator fun w ↦ SignType.ofProp (w ∈ p)

variable {S C p} {q : Set W} {w : W}

@[simp] theorem mem_additivePresup : w ∈ additivePresup S C p ↔ ∃ q ∈ C, w ∈ q ∧ ¬ S p q :=
  Iff.rfl

/-- The additive presupposes exactly what *only* asserts to be false. -/
theorem additivePresup_eq_compl_atMost : additivePresup S C p = (atMost S C p)ᶜ := by
  ext; simp

@[simp] theorem additive_eq_zero_iff : additive S C p w = 0 ↔ w ∉ additivePresup S C p := by
  simp [additive]

theorem support_additive : Function.support (additive S C p) = additivePresup S C p := by
  ext; simp

@[simp] theorem additive_eq_one_iff :
    additive S C p w = 1 ↔ w ∈ additivePresup S C p ∧ w ∈ p := by
  simp [additive]

@[simp] theorem additive_eq_neg_one_iff :
    additive S C p w = -1 ↔ w ∈ additivePresup S C p ∧ w ∉ p := by
  simp [additive]

/-- Where the prejacent and the presupposition of *only* hold, *only* is true exactly where the
additive is not. -/
theorem only_eq_one_iff_additive_ne_one (hw : w ∈ p) (hl : w ∈ atLeast S C p) :
    only S C p w = 1 ↔ additive S C p w ≠ 1 := by
  simp [-mem_atLeast, -mem_atMost, hw, hl, additivePresup_eq_compl_atMost]

theorem additivePresup_mono {C' : Set (Set W)} (h : C ⊆ C') :
    additivePresup S C p ⊆ additivePresup S C' p :=
  fun _ ⟨q, hq, hw, hn⟩ ↦ ⟨q, h hq, hw, hn⟩

theorem additivePresup_insert_self (h : S p p) :
    additivePresup S (insert p C) p = additivePresup S C p := by
  ext; simp [h]

/-- A scale relating more propositions gives a stronger presupposition. -/
theorem additivePresup_anti {S' : Set W → Set W → Prop} (h : ∀ p q, S p q → S' p q) :
    additivePresup S' C p ⊆ additivePresup S C p :=
  fun _ ⟨q, hq, hw, hn⟩ ↦ ⟨q, hq, hw, fun hs ↦ hn (h _ _ hs)⟩

/-- The entailment-scale presupposition is the stronger. -/
theorem additivePresup_subset_subset_eq : additivePresup (· ⊆ ·) C p ⊆ additivePresup (· = ·) C p :=
  additivePresup_anti fun _ _ h ↦ h.le

/-- When the prejacent entails every alternative the entailment-scale presupposition fails, as in
*Sam is happy. #He's ecstatic too* ([beaver-clark-2008]'s (3.39)). -/
theorem additivePresup_subset_eq_empty (h : ∀ q ∈ C, p ⊆ q) : additivePresup (· ⊆ ·) C p = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ ⟨q, hq, _, hn⟩ ↦ hn (h q hq)

/-- A true alternative other than the prejacent satisfies the identity-scale presupposition, even
one that the prejacent entails. -/
theorem mem_additivePresup_eq (hq : q ∈ C) (hw : w ∈ q) (hne : q ≠ p) :
    w ∈ additivePresup (· = ·) C p :=
  ⟨q, hq, hw, fun h ↦ hne h.symm⟩

theorem additivePresup_eq_eq_subset (h : ∀ q ∈ C, p ⊆ q → q = p) :
    additivePresup (· = ·) C p = additivePresup (· ⊆ ·) C p := by
  rw [additivePresup_eq_compl_atMost, additivePresup_eq_compl_atMost,
    atMost_eq_eq_atMost_subset h]

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

end Focus.Particles
