module

public import Linglib.Semantics.Mereology.Basic

/-!
# Sums and the principles of part structures

A sum of a predicate, in Tarski's sense, is a bound of its members each of whose non-null parts
overlaps one of them. It [overlaps exactly what its members overlap](##Mereology.IsSum.overlap_iff),
which is the other definition of sum in use, and the two definitions agree in a part structure
that is strongly supplemented: whatever is not part of `y` has a non-null part that does not
overlap `y`. There [a sum is a least upper bound](##Mereology.IsSum.isLUB), so a predicate has at
most one. Three further principles are stated here: the product of two overlapping individuals,
the remainder of a proper part in a whole, and that a binary join is a sum. Boolean algebras
satisfy all four. Closure of a
predicate under the sums of its inhabited subpredicates is cumulative reference in its general
form, and [the predicates so closed are the fixed points](##Mereology.sumClosed_iff) of algebraic
closure under arbitrary sums, which on a finite predicate is
[closure under binary sums](##Mereology.sumClosure_iff_algClosure).

## Implementation notes

The second clause of a sum ranges over non-null parts, as `Overlap` relates non-null parts. On a
carrier without a null individual this is Tarski's definition; on a carrier with one, his
definition holds of nothing, since the null individual overlaps nothing, and the present one
holds of least upper bounds in a Boolean algebra. The sources state the remainder principle with
uniqueness; the results that use it need only existence.

## References

* [champollion-krifka-2016], [champollion-2017], [krifka-1989], [krifka-1998]
-/

@[expose] public section

namespace Mereology

variable {α : Type*}

/-! ### Sums -/

section Sum

variable [PartialOrder α] {P Q : α → Prop} {s t x y : α}

/-- `t` is a sum of the `P`-elements ([champollion-krifka-2016]) if it lies above each of them and
each of its non-null parts overlaps one of them. -/
def IsSum (P : α → Prop) (t : α) : Prop :=
  (∀ x, P x → x ≤ t) ∧ ∀ y ≤ t, ¬ IsBot y → ∃ x, P x ∧ Overlap y x

/-- Every individual is the sum of itself. -/
theorem isSum_eq (x : α) : IsSum (· = x) x :=
  ⟨fun _ h ↦ h.le, fun _ hy hy0 ↦ ⟨x, rfl, .of_le hy0 hy⟩⟩

/-- A sum overlaps exactly what its members overlap. -/
theorem IsSum.overlap_iff (h : IsSum P t) (w : α) : Overlap w t ↔ ∃ x, P x ∧ Overlap w x :=
  ⟨fun ⟨p, hp, hpw, hpt⟩ ↦ let ⟨x, hx, ho⟩ := h.2 p hpt hp; ⟨x, hx, ho.mono hpw le_rfl⟩,
    fun ⟨x, hx, ho⟩ ↦ ho.mono le_rfl (h.1 x hx)⟩

/-- A sum of sums of subpredicates of `P` is a sum of a subpredicate of `P`. -/
theorem IsSum.bind {R : α → α → Prop} (ht : IsSum Q t) (hQ : ∀ q, Q q → IsSum (R q) q) :
    IsSum (fun x ↦ ∃ q, Q q ∧ R q x) t :=
  ⟨fun _ ⟨q, hq, hx⟩ ↦ ((hQ q hq).1 _ hx).trans (ht.1 q hq), fun y hy hy0 ↦
    let ⟨q, hq, p, hp0, hpy, hpq⟩ := ht.2 y hy hy0
    let ⟨x, hx, ho⟩ := (hQ q hq).2 p hpq hp0
    ⟨x, ⟨q, hq, hx⟩, ho.mono hpy le_rfl⟩⟩

end Sum

/-! ### Strong supplementation, products and remainders -/

/-- A part structure is strongly supplemented if whatever is not part of `y` has a non-null part
that does not overlap `y`. -/
class StronglySupplemented (α : Type*) [PartialOrder α] : Prop where
  exists_not_overlap ⦃x y : α⦄ : ¬ x ≤ y → ∃ z ≤ x, ¬ IsBot z ∧ ¬ Overlap z y

/-- A part structure has products if two overlapping individuals have a greatest common part. -/
class HasProducts (α : Type*) [PartialOrder α] : Prop where
  exists_isGLB ⦃x y : α⦄ : Overlap x y → ∃ p, IsGLB {x, y} p

/-- A part structure has remainders if every proper part `x` of `y` is completed to `y` by a
part that does not overlap `x`: the remainder principle of [krifka-1998], the relative
complementarity of [krifka-1989], and the unique separation of [champollion-2017]. -/
class HasRemainders (α : Type*) [SemilatticeSup α] : Prop where
  exists_remainder : ∀ ⦃x y : α⦄, x < y → ∃ z, ¬ Overlap z x ∧ x ⊔ z = y

/-- In a part structure with binary sums, the join of two individuals is their sum: each of its
non-null parts overlaps one of the two. Boolean algebras and classical mereologies satisfy this;
the lattice of three atoms any two of which join to the top does not. -/
class SupIsSum (α : Type*) [SemilatticeSup α] : Prop where
  isSum_sup (x y : α) : IsSum (fun u ↦ u = x ∨ u = y) (x ⊔ y)

export SupIsSum (isSum_sup)

section Principles

variable [PartialOrder α] {P : α → Prop} {s t x y : α}

/-- The product of two overlapping individuals is non-null. -/
theorem Overlap.exists_isGLB [HasProducts α] (h : Overlap x y) :
    ∃ p, ¬ IsBot p ∧ IsGLB {x, y} p :=
  let ⟨p, hp⟩ := HasProducts.exists_isGLB h
  let ⟨_, hq, hqx, hqy⟩ := h
  ⟨p, fun hb ↦ hq (hb.mono (hp.2 (by rintro _ (rfl | rfl) <;> assumption))), hp⟩

variable [StronglySupplemented α]

/-- In a strongly supplemented part structure, `x` is part of whatever all its non-null parts
overlap. -/
theorem le_of_forall_overlap (h : ∀ z ≤ x, ¬ IsBot z → Overlap z y) : x ≤ y := by
  by_contra hxy
  obtain ⟨z, hzx, hz, hzy⟩ := StronglySupplemented.exists_not_overlap hxy
  exact hzy (h z hzx hz)

/-- A proper part of `y` leaves a non-null part of `y` that it does not overlap, weak
supplementation. -/
theorem exists_not_overlap_of_lt (h : x < y) : ∃ z ≤ y, ¬ IsBot z ∧ ¬ Overlap z x :=
  StronglySupplemented.exists_not_overlap h.not_ge

/-- Two individuals that overlap the same things are identical. -/
theorem eq_of_forall_overlap_iff (h : ∀ w, Overlap w x ↔ Overlap w y) : x = y :=
  le_antisymm (le_of_forall_overlap fun z hz hz0 ↦ (h z).1 (.of_le hz0 hz))
    (le_of_forall_overlap fun z hz hz0 ↦ (h z).2 (.of_le hz0 hz))

/-- In a strongly supplemented part structure, a sum is what overlaps exactly what the members
overlap. -/
theorem isSum_iff_forall_overlap :
    IsSum P t ↔ ∀ w, Overlap w t ↔ ∃ x, P x ∧ Overlap w x :=
  ⟨IsSum.overlap_iff, fun h ↦ ⟨fun x hx ↦ le_of_forall_overlap fun z hz hz0 ↦
    (h z).2 ⟨x, hx, .of_le hz0 hz⟩, fun y hy hy0 ↦ (h y).1 (.of_le hy0 hy)⟩⟩

/-- In a strongly supplemented part structure, a sum is a least upper bound. -/
theorem IsSum.isLUB (h : IsSum P t) : IsLUB {x | P x} t :=
  ⟨fun _ hx ↦ h.1 _ hx, fun _ hw ↦ le_of_forall_overlap fun y hy hy0 ↦
    let ⟨_, hx, ho⟩ := h.2 y hy hy0
    ho.mono le_rfl (hw hx)⟩

/-- In a strongly supplemented part structure, a predicate has at most one sum. -/
theorem IsSum.unique (hs : IsSum P s) (ht : IsSum P t) : s = t := hs.isLUB.unique ht.isLUB

end Principles

section GeneralizedBooleanAlgebra

variable [GeneralizedBooleanAlgebra α] {P : α → Prop} {t : α}

instance : StronglySupplemented α where
  exists_not_overlap x y h := ⟨x \ y, sdiff_le, by rwa [isBot_iff_eq_bot, sdiff_eq_bot_iff],
    overlap_iff_not_disjoint.not_left.2 disjoint_sdiff_self_left⟩

instance : HasRemainders α where
  exists_remainder _ y h :=
    ⟨y \ _, overlap_iff_not_disjoint.not_left.2 disjoint_sdiff_self_left,
      sup_sdiff_cancel_right h.le⟩

/-- In a Boolean algebra the sums are the least upper bounds. -/
theorem isSum_iff_isLUB : IsSum P t ↔ IsLUB {x | P x} t := by
  refine ⟨IsSum.isLUB, fun h ↦ ⟨fun x hx ↦ h.1 hx, fun y hy hy0 ↦ ?_⟩⟩
  by_contra! hno
  refine hy0 (isBot_iff_eq_bot.2 ?_)
  have ht : t ≤ t \ y := h.2 fun x hx ↦
    le_sdiff.2 ⟨h.1 hx, (overlap_iff_not_disjoint.not_left.1 (hno x hx)).symm⟩
  exact (disjoint_sdiff_self_right.mono_right ht).eq_bot_of_le hy

instance : SupIsSum α where
  isSum_sup _ _ := isSum_iff_isLUB.2 isLUB_pair

end GeneralizedBooleanAlgebra

instance [SemilatticeInf α] : HasProducts α where
  exists_isGLB x y _ := ⟨x ⊓ y, isGLB_pair⟩

/-! ### Closure under sums -/

section SumClosed

variable [PartialOrder α] {P : α → Prop} {x : α}

/-- A predicate is closed under sums if it holds of every sum of an inhabited subpredicate,
cumulative reference in the form that covers infinite sums ([champollion-krifka-2016]). -/
def SumClosed (P : α → Prop) : Prop :=
  ∀ Q : α → Prop, (∀ x, Q x → P x) → (∃ x, Q x) → ∀ t, IsSum Q t → P t

/-- The closure of `P` under sums ([champollion-krifka-2016]) holds of the sums of the inhabited
subpredicates of `P`. -/
def SumClosure (P : α → Prop) (x : α) : Prop :=
  ∃ Q : α → Prop, (∀ y, Q y → P y) ∧ (∃ y, Q y) ∧ IsSum Q x

theorem SumClosure.base (h : P x) : SumClosure P x :=
  ⟨(· = x), fun _ e ↦ e ▸ h, ⟨x, rfl⟩, isSum_eq x⟩

/-- The closure of a predicate under sums is closed under sums. -/
theorem sumClosed_sumClosure (P : α → Prop) : SumClosed (SumClosure P) := by
  intro Q hQ ⟨q₀, hq₀⟩ t ht
  choose! R hRP hRne hR using hQ
  obtain ⟨y, hy⟩ := hRne q₀ hq₀
  exact ⟨fun x ↦ ∃ q, Q q ∧ R q x, fun x ⟨q, hq, hx⟩ ↦ hRP q hq x hx, ⟨y, q₀, hq₀, hy⟩,
    ht.bind hR⟩

/-- A predicate is closed under sums iff its closure under sums adds nothing to it, as the
plural of a cumulative mass noun adds nothing. -/
theorem sumClosed_iff : SumClosed P ↔ ∀ x, SumClosure P x → P x :=
  ⟨fun h _ ⟨Q, hQ, hne, hx⟩ ↦ h Q hQ hne _ hx, fun h Q hQ hne _ ht ↦ h _ ⟨Q, hQ, hne, ht⟩⟩

end SumClosed

section SupIsSum

variable [SemilatticeSup α] {P : α → Prop} {x : α}

/-- A predicate closed under sums is cumulative. -/
theorem SumClosed.cum [SupIsSum α] (h : SumClosed P) : CUM P :=
  fun x hx y hy ↦ h _ (by rintro _ (rfl | rfl) <;> assumption) ⟨x, .inl rfl⟩ _ (isSum_sup x y)

/-- The closure under binary sums lies in the closure under sums. -/
theorem AlgClosure.sumClosure [SupIsSum α] (h : AlgClosure P x) : SumClosure P x :=
  supClosure_min (t := {x | SumClosure P x}) (fun _ hx ↦ .base hx)
    (sumClosed_sumClosure P).cum h

/-- The closure of a finite predicate under sums lies in its closure under binary sums. -/
theorem SumClosure.algClosure [StronglySupplemented α] (hP : {x | P x}.Finite)
    (h : SumClosure P x) : AlgClosure P x := by
  obtain ⟨Q, hQ, ⟨q, hq⟩, hx⟩ := h
  have hfin : {y | Q y}.Finite := hP.subset fun y hy ↦ hQ y hy
  have hne : hfin.toFinset.Nonempty := ⟨q, hfin.mem_toFinset.2 hq⟩
  have hlub : IsLUB {y | Q y} (hfin.toFinset.sup' hne id) := by
    simpa using Finset.isLUB_sup' hne
  rw [hx.isLUB.unique hlub]
  exact algClosure_finsetSup' hne fun y hy ↦ .base (hQ y (hfin.mem_toFinset.1 hy))

/-- The two algebraic closures of a finite predicate agree. -/
theorem sumClosure_iff_algClosure [StronglySupplemented α] [SupIsSum α]
    (hP : {x | P x}.Finite) : SumClosure P x ↔ AlgClosure P x :=
  ⟨SumClosure.algClosure hP, AlgClosure.sumClosure⟩

end SupIsSum

end Mereology
