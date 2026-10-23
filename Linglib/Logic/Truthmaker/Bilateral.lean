module

public import Linglib.Core.Data.Set.Sups
public import Linglib.Logic.Truthmaker.Basic
public import Mathlib.Algebra.Group.DivInvMonoid

/-!
# Bilateral truthmaker propositions

This file defines Kit Fine's bilateral propositions. A bilateral proposition pairs a set of
verifiers with a set of falsifiers. Negation swaps the two sets, conjunction fuses verifiers and
pools falsifiers, and disjunction pools verifiers and fuses falsifiers.

The possible states form a lower set `P`, and two states are compatible when their fusion is
possible. A proposition is exclusive when no verifier is compatible with a falsifier, and
exhaustive when every possible state is compatible with a verifier or a falsifier. The maximal
possible states are the worlds, and a proposition is true at a world containing one of its
verifiers. When the states form a complete lattice, the subject-matter of a proposition is the
fusion of all its verifiers and falsifiers.

## Main definitions

* `Truthmaker.BilProp`: a set of verifiers and a set of falsifiers, with negation as an
  `InvolutiveNeg` instance.
* `Truthmaker.BilProp.conj`, `Truthmaker.BilProp.disj`: conjunction and disjunction.
* `Truthmaker.BilProp.Exclusive`, `Truthmaker.BilProp.Exhaustive`: the two halves of bivalence.
* `Truthmaker.BilProp.subjectMatter`: the fusion of all verifiers and falsifiers.
* `Truthmaker.Canonical.possible`, `Truthmaker.Canonical.atom`: Fine's canonical space, whose
  states are sets of literals, and its atomic propositions.
* `Truthmaker.Canonical.mirror`: the literal with the same atom and the opposite polarity.

## Main results

* `Truthmaker.BilProp.neg_conj`, `Truthmaker.BilProp.neg_disj`: De Morgan's laws.
* `Truthmaker.BilProp.Exclusive.conj`, `Truthmaker.BilProp.Exhaustive.conj`: conjunction preserves
  exclusivity and exhaustivity, and so do negation and disjunction.
* `Truthmaker.BilProp.exclusive_iff`: a proposition is exclusive exactly when no possible state
  makes it both true and false.
* `Truthmaker.BilProp.exhaustive_iff`: when every possible state is part of a world, a
  proposition is exhaustive exactly when it is true or false at every world.
* `Truthmaker.Canonical.maximal_possible_iff`, `Truthmaker.Canonical.exists_le_maximal_possible`:
  the worlds of the canonical space contain exactly one of each literal and its mirror, and every
  consistent set of literals is part of one.
* `Truthmaker.BilProp.subjectMatter_neg`, `Truthmaker.BilProp.subjectMatter_conj`: negation keeps
  the subject-matter, and conjunction fuses subject-matters.
* `Truthmaker.Canonical.mem_upperClosure_disj_neg_atom`,
  `Truthmaker.Canonical.subjectMatter_disj_neg_atom_injective`: the excluded middle `a ∨ ¬a` of
  an atom is true at every world, yet distinct atoms give excluded middles with distinct
  subject-matters, each an impossible state.

## Implementation notes

Fine defines conjunction only between propositions with a verifier and disjunction only between
propositions with a falsifier. Here both are total, and the subject-matter lemmas carry the
nonemptiness hypotheses instead.

## References

* [K. Fine, *A Theory of Truthmaker Content I: Conjunction, Disjunction and Negation*
  (2017)][fine-2017a]
* [K. Fine, *A Theory of Truthmaker Content II: Subject-matter, Common Content, Remainder and
  Ground* (2017)][fine-2017b]
* [K. Fine, *Truthmaker Semantics* (2017)][fine-2017]
-/

@[expose] public section

open SetFamily

namespace Truthmaker

/-- A bilateral proposition is a set of verifying states together with a set of falsifying
states. -/
@[ext]
structure BilProp (S : Type*) where
  /-- The states that exactly verify the proposition. -/
  ver : Set S
  /-- The states that exactly falsify the proposition. -/
  fal : Set S

namespace BilProp

variable {S : Type*}

/-- The negation of a bilateral proposition swaps its verifiers and its falsifiers. -/
instance : InvolutiveNeg (BilProp S) where
  neg A := ⟨A.fal, A.ver⟩
  neg_neg _ := rfl

@[simp] theorem ver_neg (A : BilProp S) : (-A).ver = A.fal := rfl

@[simp] theorem fal_neg (A : BilProp S) : (-A).fal = A.ver := rfl

section SemilatticeSup

variable [SemilatticeSup S] {P : LowerSet S} {A B : BilProp S}

/-- The conjunction of `A` and `B` is verified by the fusion of a verifier of each and falsified
by a falsifier of either. -/
def conj (A B : BilProp S) : BilProp S :=
  ⟨A.ver ⊻ B.ver, A.fal ∪ B.fal⟩

/-- The disjunction of `A` and `B` is verified by a verifier of either and falsified by the fusion
of a falsifier of each. -/
def disj (A B : BilProp S) : BilProp S :=
  ⟨A.ver ∪ B.ver, A.fal ⊻ B.fal⟩

@[simp] theorem ver_conj (A B : BilProp S) : (A.conj B).ver = A.ver ⊻ B.ver := rfl

@[simp] theorem fal_conj (A B : BilProp S) : (A.conj B).fal = A.fal ∪ B.fal := rfl

@[simp] theorem ver_disj (A B : BilProp S) : (A.disj B).ver = A.ver ∪ B.ver := rfl

@[simp] theorem fal_disj (A B : BilProp S) : (A.disj B).fal = A.fal ⊻ B.fal := rfl

@[simp] theorem neg_conj (A B : BilProp S) : -(A.conj B) = (-A).disj (-B) := rfl

@[simp] theorem neg_disj (A B : BilProp S) : -(A.disj B) = (-A).conj (-B) := rfl

/-- A bilateral proposition is exclusive over the possible states `P` if the fusion of a verifier
with a falsifier is never possible. -/
def Exclusive (P : LowerSet S) (A : BilProp S) : Prop :=
  ∀ ⦃s⦄, s ∈ A.ver → ∀ ⦃t⦄, t ∈ A.fal → s ⊔ t ∉ P

/-- A bilateral proposition is exhaustive over the possible states `P` if every possible state has
a possible fusion with a verifier or with a falsifier. -/
def Exhaustive (P : LowerSet S) (A : BilProp S) : Prop :=
  ∀ ⦃s⦄, s ∈ P → (∃ t ∈ A.ver, s ⊔ t ∈ P) ∨ ∃ t ∈ A.fal, s ⊔ t ∈ P

theorem Exclusive.neg (h : A.Exclusive P) : (-A).Exclusive P :=
  fun s hs t ht hst ↦ h ht hs (sup_comm s t ▸ hst)

theorem Exhaustive.neg (h : A.Exhaustive P) : (-A).Exhaustive P :=
  fun _ hs ↦ (h hs).symm

@[simp] theorem exclusive_neg : (-A).Exclusive P ↔ A.Exclusive P :=
  ⟨fun h ↦ neg_neg A ▸ h.neg, .neg⟩

@[simp] theorem exhaustive_neg : (-A).Exhaustive P ↔ A.Exhaustive P :=
  ⟨fun h ↦ neg_neg A ▸ h.neg, .neg⟩

theorem Exclusive.conj (hA : A.Exclusive P) (hB : B.Exclusive P) : (A.conj B).Exclusive P := by
  rintro _ hs t ht hst
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_sups.1 hs
  rcases ht with ht | ht
  · exact hA ha ht (P.lower (sup_le_sup_right le_sup_left t) hst)
  · exact hB hb ht (P.lower (sup_le_sup_right le_sup_right t) hst)

theorem Exhaustive.conj (hA : A.Exhaustive P) (hB : B.Exhaustive P) :
    (A.conj B).Exhaustive P := by
  intro s hs
  obtain ⟨a, ha, hsa⟩ | ⟨t, ht, hst⟩ := hA hs
  · obtain ⟨b, hb, hsab⟩ | ⟨t, ht, hsat⟩ := hB hsa
    · exact .inl ⟨a ⊔ b, Set.sup_mem_sups ha hb, sup_assoc s a b ▸ hsab⟩
    · exact .inr ⟨t, .inr ht, P.lower (sup_le_sup_right le_sup_left t) hsat⟩
  · exact .inr ⟨t, .inl ht, hst⟩

theorem Exclusive.disj (hA : A.Exclusive P) (hB : B.Exclusive P) : (A.disj B).Exclusive P :=
  (hA.neg.conj hB.neg).neg

theorem Exhaustive.disj (hA : A.Exhaustive P) (hB : B.Exhaustive P) :
    (A.disj B).Exhaustive P :=
  (hA.neg.conj hB.neg).neg

theorem exclusive_iff :
    A.Exclusive P ↔ ∀ s ∈ P, s ∈ upperClosure A.ver → s ∉ upperClosure A.fal := by
  refine ⟨fun h s hs hv hf ↦ ?_, fun h a ha b hb hab ↦ ?_⟩
  · obtain ⟨a, ha, has⟩ := mem_upperClosure.1 hv
    obtain ⟨b, hb, hbs⟩ := mem_upperClosure.1 hf
    exact h ha hb (P.lower (sup_le has hbs) hs)
  · exact h _ hab (mem_upperClosure.2 ⟨a, ha, le_sup_left⟩)
      (mem_upperClosure.2 ⟨b, hb, le_sup_right⟩)

theorem Exhaustive.mem_upperClosure (h : A.Exhaustive P) {w : S} (hw : Maximal (· ∈ P) w) :
    w ∈ upperClosure A.ver ∨ w ∈ upperClosure A.fal := by
  obtain ⟨t, ht, hwt⟩ | ⟨t, ht, hwt⟩ := h hw.prop
  · exact .inl ⟨t, ht, le_sup_right.trans (hw.le_of_ge hwt le_sup_left)⟩
  · exact .inr ⟨t, ht, le_sup_right.trans (hw.le_of_ge hwt le_sup_left)⟩

theorem exhaustive_iff (hP : ∀ s ∈ P, ∃ w, s ≤ w ∧ Maximal (· ∈ P) w) :
    A.Exhaustive P ↔
      ∀ w, Maximal (· ∈ P) w → w ∈ upperClosure A.ver ∨ w ∈ upperClosure A.fal := by
  refine ⟨fun h w hw ↦ h.mem_upperClosure hw, fun h s hs ↦ ?_⟩
  obtain ⟨w, hsw, hw⟩ := hP s hs
  rcases h w hw with h | h <;> obtain ⟨t, ht, htw⟩ := mem_upperClosure.1 h
  · exact .inl ⟨t, ht, P.lower (sup_le hsw htw) hw.prop⟩
  · exact .inr ⟨t, ht, P.lower (sup_le hsw htw) hw.prop⟩

theorem Exhaustive.mem_upperClosure_disj_neg (h : A.Exhaustive P) {w : S}
    (hw : Maximal (· ∈ P) w) : w ∈ upperClosure (A.disj (-A)).ver := by
  simpa [upperClosure_union] using h.mem_upperClosure hw

end SemilatticeSup

section CompleteLattice

variable [CompleteLattice S] {A B : BilProp S}

/-- The subject-matter of a bilateral proposition is the fusion of all its verifiers and all its
falsifiers. -/
def subjectMatter (A : BilProp S) : S :=
  sSup A.ver ⊔ sSup A.fal

@[simp] theorem subjectMatter_neg (A : BilProp S) : (-A).subjectMatter = A.subjectMatter :=
  sup_comm _ _

theorem subjectMatter_conj (hA : A.ver.Nonempty) (hB : B.ver.Nonempty) :
    (A.conj B).subjectMatter = A.subjectMatter ⊔ B.subjectMatter := by
  simp only [subjectMatter, ver_conj, fal_conj, Set.sSup_sups hA hB, sSup_union]
  exact sup_sup_sup_comm _ _ _ _

theorem subjectMatter_disj (hA : A.fal.Nonempty) (hB : B.fal.Nonempty) :
    (A.disj B).subjectMatter = A.subjectMatter ⊔ B.subjectMatter := by
  simp only [subjectMatter, ver_disj, fal_disj, Set.sSup_sups hA hB, sSup_union]
  exact sup_sup_sup_comm _ _ _ _

theorem subjectMatter_disj_neg (hv : A.ver.Nonempty) (hf : A.fal.Nonempty) :
    (A.disj (-A)).subjectMatter = A.subjectMatter := by
  rw [subjectMatter_disj hf hv, subjectMatter_neg, sup_idem]

end CompleteLattice

end BilProp

namespace Canonical

open BilProp

variable {α : Type*}

/-- The mirror image of a literal has the same atom and the opposite polarity. -/
def mirror (x : α × Bool) : α × Bool :=
  (x.1, !x.2)

@[simp] theorem mirror_mk (a : α) (b : Bool) : mirror (a, b) = (a, !b) :=
  rfl

@[simp] theorem mirror_mirror (x : α × Bool) : mirror (mirror x) = x := by
  simp [mirror]

theorem mirror_involutive : Function.Involutive (mirror (α := α)) :=
  mirror_mirror

theorem mirror_ne (x : α × Bool) : mirror x ≠ x :=
  fun h ↦ Bool.not_ne_self x.2 (congrArg Prod.snd h)

/-- The possible states of the canonical space are the consistent sets of literals, those
containing no literal together with its mirror image. The literal `(a, true)` asserts the atom
`a` and `(a, false)` denies it. -/
def possible : LowerSet (Set (α × Bool)) where
  carrier := {L | ∀ x ∈ L, mirror x ∉ L}
  lower' := by
    intro L K hKL hL x hx hx'
    exact hL x (hKL hx) (hKL hx')

theorem mem_possible {L : Set (α × Bool)} : L ∈ possible ↔ ∀ x ∈ L, mirror x ∉ L :=
  Iff.rfl

theorem maximal_possible_iff {w : Set (α × Bool)} :
    Maximal (· ∈ possible) w ↔ ∀ x, x ∈ w ↔ mirror x ∉ w := by
  refine ⟨fun hw x ↦ ⟨hw.prop x, fun hx ↦ ?_⟩, fun h ↦ ⟨fun x hx ↦ (h x).1 hx, ?_⟩⟩
  · refine hw.le_of_ge (fun y hy hy' ↦ ?_) (Set.subset_insert x w) (Set.mem_insert x w)
    rcases hy with rfl | hy <;> rcases hy' with hy' | hy'
    · exact mirror_ne _ hy'
    · exact hx hy'
    · exact hx (hy' ▸ (mirror_mirror y).symm ▸ hy)
    · exact hw.prop y hy hy'
  · intro s hs hws y hy
    by_contra hyw
    exact hs y hy (hws (not_not.1 (mt (h y).2 hyw)))

theorem mem_or_mirror_mem_of_maximal {w : Set (α × Bool)} (hw : Maximal (· ∈ possible) w)
    (x : α × Bool) : x ∈ w ∨ mirror x ∈ w :=
  or_iff_not_imp_left.2 fun hx ↦ not_not.1 (mt (maximal_possible_iff.1 hw x).2 hx)

theorem exists_le_maximal_possible {L : Set (α × Bool)} (hL : L ∈ possible) :
    ∃ w, L ≤ w ∧ Maximal (· ∈ possible) w := by
  refine ⟨{x | x ∈ L ∨ x.2 = true ∧ mirror x ∉ L}, fun x hx ↦ .inl hx,
    maximal_possible_iff.2 fun ⟨a, b⟩ ↦ ?_⟩
  have h₁ := hL (a, true)
  have h₂ := hL (a, false)
  cases b <;> simp only [Set.mem_ofPred_eq, mirror_mk, Bool.not_true, Bool.not_false] at h₁ h₂ ⊢ <;>
    tauto

/-- The atomic proposition `a` is verified by its assertion and falsified by its denial. -/
def atom (a : α) : BilProp (Set (α × Bool)) :=
  ⟨{{(a, true)}}, {{(a, false)}}⟩

@[simp] theorem ver_atom (a : α) : (atom a).ver = {{(a, true)}} :=
  rfl

@[simp] theorem fal_atom (a : α) : (atom a).fal = {{(a, false)}} :=
  rfl

theorem exclusive_atom (a : α) : (atom a).Exclusive possible := by
  rintro _ rfl _ rfl h
  exact h (a, true) (.inl rfl) (.inr rfl)

theorem exhaustive_atom (a : α) : (atom a).Exhaustive possible :=
  (exhaustive_iff fun _ ↦ exists_le_maximal_possible).2 fun _ hw ↦
    (mem_or_mirror_mem_of_maximal hw (a, true)).imp
      (fun h ↦ mem_upperClosure.2 ⟨_, rfl, Set.singleton_subset_iff.2 h⟩)
      (fun h ↦ mem_upperClosure.2 ⟨_, rfl, Set.singleton_subset_iff.2 h⟩)

theorem subjectMatter_atom (a : α) : (atom a).subjectMatter = {(a, true), (a, false)} := by
  simpa [subjectMatter, atom] using Set.pair_comm _ _

theorem mem_upperClosure_disj_neg_atom (a : α) {w : Set (α × Bool)}
    (hw : Maximal (· ∈ possible) w) : w ∈ upperClosure ((atom a).disj (-atom a)).ver :=
  (exhaustive_atom a).mem_upperClosure_disj_neg hw

theorem subjectMatter_disj_neg_atom (a : α) :
    ((atom a).disj (-atom a)).subjectMatter = {(a, true), (a, false)} := by
  rw [subjectMatter_disj_neg ⟨_, rfl⟩ ⟨_, rfl⟩, subjectMatter_atom]

theorem subjectMatter_disj_neg_atom_not_mem (a : α) :
    ((atom a).disj (-atom a)).subjectMatter ∉ possible := by
  rw [subjectMatter_disj_neg_atom]
  exact fun h ↦ h (a, true) (.inl rfl) (.inr rfl)

theorem subjectMatter_disj_neg_atom_injective :
    Function.Injective fun a : α ↦ ((atom a).disj (-atom a)).subjectMatter := by
  intro a b h
  have : (a, true) ∈ ({(b, true), (b, false)} : Set (α × Bool)) := by
    simp only [subjectMatter_disj_neg_atom] at h
    rw [← h]
    exact .inl rfl
  simpa using this

end Canonical

end Truthmaker
