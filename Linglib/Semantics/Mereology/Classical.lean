module

public import Mathlib.Order.CompleteBooleanAlgebra
public import Linglib.Semantics.Mereology.Sum

/-!
# Classical mereology

Classical extensional mereology is a strongly supplemented part structure in which every
inhabited predicate has a sum, which is to say
[a unique sum](##Mereology.isClassicalMereology_iff_existsUnique). Its sums are its least upper
bounds, a proper part
[has a unique remainder](##Mereology.IsClassicalMereology.existsUnique_remainder) and two
overlapping individuals have a product. A complete Boolean algebra is a classical
mereology whose null individual is its bottom, and
[the non-null individuals](##Mereology.IsClassicalMereology.instSubtypeNotIsBot) of a classical
mereology form one with no null individual, as the nonempty subsets of a set do. Conversely a
classical mereology with a null individual
[is a complete Boolean algebra](##Mereology.IsClassicalMereology.toCompleteBooleanAlgebra), and
one without becomes one when a null individual is added.

## Implementation notes

Classical mereology is defined by strong supplementation and unrestricted sums; the definition
by unique sums of Champollion's book is a theorem, and Hovda compares the axiomatizations. A
carrier may have a null individual: the sources' systems are the classical mereologies with
`NoBotOrder`. The one-point carrier, whose individual is null, is a classical mereology.

## References

* [champollion-krifka-2016], [champollion-2017], [hovda-2009], [krifka-1989], [krifka-1998]
-/

@[expose] public section

namespace Mereology

variable {α : Type*}

/-- A part structure is a classical extensional mereology ([champollion-krifka-2016]) if it is
strongly supplemented and every inhabited predicate has a sum. -/
class IsClassicalMereology (α : Type*) [PartialOrder α] : Prop
    extends StronglySupplemented α where
  exists_isSum (P : α → Prop) : (∃ x, P x) → ∃ t, IsSum P t

/-- A part structure is a classical mereology iff every inhabited predicate has exactly one sum,
the axiom of unique sums of [champollion-krifka-2016]. -/
theorem isClassicalMereology_iff_existsUnique [PartialOrder α] :
    IsClassicalMereology α ↔ ∀ P : α → Prop, (∃ x, P x) → ∃! t, IsSum P t := by
  refine ⟨fun h P hP ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨t, ht⟩ := h.exists_isSum P hP
    exact ⟨t, ht, fun s hs ↦ hs.unique ht⟩
  · have weak {x y : α} (hxy : x < y) : ∃ z ≤ y, ¬ IsBot z ∧ ¬ Overlap z x := by
      by_contra! hall
      exact hxy.ne ((h (· = x) ⟨x, rfl⟩).unique (isSum_eq x)
        ⟨fun _ e ↦ e ▸ hxy.le, fun z hz hz0 ↦ ⟨x, rfl, hall z hz hz0⟩⟩)
    refine { exists_not_overlap := fun y u hyu ↦ ?_, exists_isSum := fun P hP ↦ (h P hP).exists }
    obtain ⟨s, hs⟩ := (h (fun w ↦ w = y ∨ w = u) ⟨y, .inl rfl⟩).exists
    have hus : u < s := lt_of_le_of_ne (hs.1 u (.inr rfl)) fun e ↦ hyu (e ▸ hs.1 y (.inl rfl))
    obtain ⟨w, hws, hw0, hwu⟩ := weak hus
    obtain ⟨_, rfl | rfl, v, hv, hvw, hvy⟩ := hs.2 w hws hw0
    · exact ⟨v, hvy, hv, fun ⟨q, hq, hqv, hqu⟩ ↦ hwu ⟨q, hq, hqv.trans hvw, hqu⟩⟩
    · exact absurd ⟨v, hv, hvw, hvy⟩ hwu

namespace IsClassicalMereology

section PartialOrder

variable [PartialOrder α] [IsClassicalMereology α] {P : α → Prop} {t x y z : α}

/-- In a classical mereology the sums of an inhabited predicate are its least upper bounds. -/
theorem isSum_iff_isLUB (hP : ∃ x, P x) : IsSum P t ↔ IsLUB {x | P x} t :=
  ⟨IsSum.isLUB, fun h ↦ let ⟨_, hs⟩ := exists_isSum P hP; hs.isLUB.unique h ▸ hs⟩

theorem isSum_pair (h : IsLUB {x, y} t) : IsSum (fun u ↦ u = x ∨ u = y) t :=
  (isSum_iff_isLUB ⟨x, .inl rfl⟩).2 h

theorem exists_remainder (h : x < y) : ∃ z, ¬ Overlap z x ∧ IsLUB {x, z} y := by
  obtain ⟨w₀, hw₀y, -, hw₀x⟩ := exists_not_overlap_of_lt h
  obtain ⟨z, hz⟩ := exists_isSum (fun w ↦ w ≤ y ∧ ¬ Overlap w x) ⟨w₀, hw₀y, hw₀x⟩
  refine ⟨z, fun ⟨q, hq, hqz, hqx⟩ ↦ ?_, ⟨?_, fun u hu ↦ ?_⟩⟩
  · obtain ⟨r, ⟨_, hrx⟩, v, hv, hvq, hvr⟩ := hz.2 q hqz hq
    exact hrx ⟨v, hv, hvr, hvq.trans hqx⟩
  · rintro _ (rfl | rfl)
    exacts [h.le, hz.isLUB.2 fun _ hw ↦ hw.1]
  · refine le_of_forall_overlap fun v hv hv0 ↦ ?_
    by_cases hvx : Overlap v x
    · exact hvx.mono le_rfl (hu (.inl rfl))
    · exact .of_le hv0 ((hz.1 v ⟨hv, hvx⟩).trans (hu (.inr rfl)))

theorem remainder_unique {z' : α} (hz : ¬ Overlap z x) (hlub : IsLUB {x, z} y)
    (hz' : ¬ Overlap z' x) (hlub' : IsLUB {x, z'} y) : z = z' := by
  have key {z z' : α} (hz : ¬ Overlap z x) (hlub : IsLUB {x, z} y) (hlub' : IsLUB {x, z'} y) :
      z ≤ z' := le_of_forall_overlap fun v hv hv0 ↦ by
    obtain ⟨_, rfl | rfl, hov⟩ := (isSum_pair hlub').2 v (hv.trans (hlub.1 (.inr rfl))) hv0
    · exact absurd (hov.mono hv le_rfl) hz
    · exact hov
  exact le_antisymm (key hz hlub hlub') (key hz' hlub' hlub)

/-- A proper part of `y` has exactly one remainder in `y`, the unique separation of
[krifka-1998] and [champollion-2017]. -/
theorem existsUnique_remainder (h : x < y) : ∃! z, ¬ Overlap z x ∧ IsLUB {x, z} y :=
  let ⟨z, hz, hlub⟩ := exists_remainder h
  ⟨z, ⟨hz, hlub⟩, fun _ ⟨hz', hlub'⟩ ↦ remainder_unique hz' hlub' hz hlub⟩

/-- The product of two overlapping individuals is the sum of their common parts. -/
instance : HasProducts α where
  exists_isGLB x y := fun ⟨q, _, hqx, hqy⟩ ↦ by
    obtain ⟨p, hp⟩ := exists_isSum (fun w ↦ w ≤ x ∧ w ≤ y) ⟨q, hqx, hqy⟩
    refine ⟨p, ?_, fun w hw ↦ hp.1 w ⟨hw (.inl rfl), hw (.inr rfl)⟩⟩
    rintro _ (rfl | rfl)
    exacts [hp.isLUB.2 fun _ h ↦ h.1, hp.isLUB.2 fun _ h ↦ h.2]

/-! ### The generalized sum -/

/-- `sum P h` is the sum of the inhabited predicate `P`, the generalized sum `⊕P` of
[champollion-krifka-2016]. -/
noncomputable def sum (P : α → Prop) (h : ∃ x, P x) : α := (exists_isSum P h).choose

variable (hP : ∃ x, P x)

theorem isSum_sum : IsSum P (sum P hP) := (exists_isSum P hP).choose_spec

theorem isLUB_sum : IsLUB {x | P x} (sum P hP) := (isSum_sum hP).isLUB

theorem _root_.Mereology.IsSum.eq_sum (h : IsSum P t) : t = sum P hP := h.unique (isSum_sum hP)

theorem le_sum (hx : P x) : x ≤ sum P hP := (isSum_sum hP).1 x hx

theorem sum_le_iff : sum P hP ≤ t ↔ ∀ x, P x → x ≤ t := isLUB_le_iff (isLUB_sum hP)

@[simp]
theorem sum_eq (x : α) : sum (· = x) ⟨x, rfl⟩ = x := ((isSum_eq x).eq_sum _).symm

/-- The binary sum `a ⊕ b` of a classical mereology is the sum of the pair `{a, b}`. -/
@[reducible] noncomputable def toSemilatticeSup : SemilatticeSup α :=
  { ‹PartialOrder α› with
    sup := fun a b ↦ sum (fun u ↦ u = a ∨ u = b) ⟨a, .inl rfl⟩
    le_sup_left := fun a b ↦ le_sum (P := fun u ↦ u = a ∨ u = b) ⟨a, .inl rfl⟩ (.inl rfl)
    le_sup_right := fun a b ↦ le_sum (P := fun u ↦ u = a ∨ u = b) ⟨a, .inl rfl⟩ (.inr rfl)
    sup_le := fun _ _ _ ha hb ↦ (sum_le_iff _).2 <| by
      rintro _ (rfl | rfl)
      exacts [ha, hb] }

end PartialOrder

instance [SemilatticeSup α] [IsClassicalMereology α] : SupIsSum α where
  isSum_sup _ _ := isSum_pair isLUB_pair

/-- A predicate closed under sums has its sum as greatest member, the referent of a definite
description ([champollion-krifka-2016]). -/
theorem _root_.Mereology.SumClosed.isGreatest_sum [PartialOrder α] [IsClassicalMereology α]
    {P : α → Prop} (h : SumClosed P) (hP : ∃ x, P x) : IsGreatest {x | P x} (sum P hP) :=
  ⟨h P (fun _ hx ↦ hx) hP _ (isSum_sum hP), fun _ hx ↦ le_sum hP hx⟩

instance [SemilatticeSup α] [IsClassicalMereology α] : HasRemainders α where
  exists_remainder _ _ h :=
    let ⟨z, hz, hlub⟩ := exists_remainder h
    ⟨z, hz, (hlub.unique isLUB_pair).symm⟩

/-! ### Boolean algebras and non-null individuals -/

/-- A complete Boolean algebra is a classical mereology, its bottom the null individual and its
sums its suprema. -/
instance [CompleteBooleanAlgebra α] : IsClassicalMereology α where
  exists_isSum P _ := ⟨sSup {x | P x}, Mereology.isSum_iff_isLUB.2 (isLUB_sSup _)⟩

theorem sum_eq_sSup [CompleteBooleanAlgebra α] (P : α → Prop) (hP : ∃ x, P x) :
    sum P hP = sSup {x | P x} :=
  (isLUB_sum hP).unique (isLUB_sSup _)

section Subtype

variable [PartialOrder α] {p : α → Prop} (hp : ∀ x, p x ↔ ¬ IsBot x)

include hp

private theorem overlap_of_overlap_subtype {x y : {x // p x}} (h : Overlap x y) :
    Overlap x.1 y.1 :=
  let ⟨z, _, hzx, hzy⟩ := h
  ⟨z, (hp z).1 z.2, hzx, hzy⟩

variable [IsClassicalMereology α]

private theorem eq_of_isBot_subtype {m : {x // p x}} (hm : IsBot m) (x : {x // p x}) :
    x = m := by
  refine le_antisymm (Subtype.coe_le_coe.1 ?_) (hm x)
  by_contra h
  obtain ⟨z, -, hz, hzm⟩ := StronglySupplemented.exists_not_overlap h
  exact hzm ⟨m, (hp m).1 m.2, hm ⟨z, (hp z).2 hz⟩, le_rfl⟩

/-- The non-null individuals of a classical mereology, picked out by any predicate, form a
classical mereology. -/
theorem subtype : IsClassicalMereology {x // p x} where
  exists_not_overlap x y h := by
    obtain ⟨z, hzx, hz, hzy⟩ := StronglySupplemented.exists_not_overlap
      (fun h' ↦ h (Subtype.coe_le_coe.1 h') : ¬ x.1 ≤ y.1)
    exact ⟨⟨z, (hp z).2 hz⟩, hzx, fun hb ↦ hzy ⟨z, hz, le_rfl, hb y⟩,
      fun ho ↦ hzy (overlap_of_overlap_subtype hp ho)⟩
  exists_isSum P := fun ⟨a, ha⟩ ↦ by
    obtain ⟨t, ht⟩ := exists_isSum (fun x : α ↦ ∃ h, P ⟨x, h⟩) ⟨a, a.2, ha⟩
    have ht0 : ¬ IsBot t := fun hb ↦ (hp a).1 a.2 (hb.mono (ht.1 a ⟨a.2, ha⟩))
    refine ⟨⟨t, (hp t).2 ht0⟩, fun x hx ↦ ht.1 x ⟨x.2, hx⟩, fun y hy hy0 ↦ ?_⟩
    obtain ⟨x, ⟨hx0, hx⟩, q, hq0, hqy, hqx⟩ := ht.2 y hy ((hp y).1 y.2)
    exact ⟨⟨x, hx0⟩, hx, ⟨q, (hp q).2 hq0⟩,
      fun hb ↦ hy0 (eq_of_isBot_subtype hp hb y ▸ hb), hqy, hqx⟩

omit hp in
/-- The non-null individuals of a classical mereology form a classical mereology, as the
nonempty subsets of a set do under inclusion ([champollion-krifka-2016]). -/
instance instSubtypeNotIsBot : IsClassicalMereology {x : α // ¬ IsBot x} :=
  subtype fun _ ↦ Iff.rfl

end Subtype

/-! ### The Boolean representation

A classical mereology with a null individual is a complete Boolean algebra, and adding a null
individual to a classical mereology without one gives a classical mereology, so the classical
mereologies without a null individual are the complete Boolean algebras with the bottom
removed. -/

section OrderBot
variable [PartialOrder α] [OrderBot α] [IsClassicalMereology α]

open Classical in
/-- A classical mereology with a null individual is a complete lattice. -/
@[reducible] noncomputable def toCompleteLattice : CompleteLattice α :=
  letI : SupSet α := ⟨fun s ↦ if h : ∃ x, x ∈ s then sum (· ∈ s) h else ⊥⟩
  completeLatticeOfSup α fun s ↦ by
    change IsLUB s (if h : ∃ x, x ∈ s then sum (· ∈ s) h else ⊥)
    split_ifs with h
    · exact isLUB_sum h
    · rw [Set.not_nonempty_iff_eq_empty.1 h]
      exact isLUB_empty

/-- A classical mereology with a null individual is a complete Boolean algebra. -/
@[reducible] noncomputable def toCompleteBooleanAlgebra : CompleteBooleanAlgebra α :=
  letI L : CompleteLattice α := toCompleteLattice
  have hc (x : α) : IsSum (fun w ↦ ¬ Overlap w x) (sSup {w | ¬ Overlap w x}) :=
    (isSum_iff_isLUB ⟨⊥, fun h ↦ h.not_isBot_left isBot_bot⟩).2 (isLUB_sSup _)
  { L with
    le_sup_inf := fun x y z ↦ le_of_forall_overlap fun p hp hp0 ↦ by
      by_cases hpx : Overlap p x
      · exact hpx.mono le_rfl le_sup_left
      · have key {u : α} (hu : p ≤ x ⊔ u) : p ≤ u := le_of_forall_overlap fun q hq hq0 ↦ by
          obtain ⟨_, rfl | rfl, ho⟩ := (isSum_pair isLUB_pair).2 q (hq.trans hu) hq0
          · exact absurd (ho.mono hq le_rfl) hpx
          · exact ho
        exact .of_le hp0 (le_sup_of_le_right
          (le_inf (key (hp.trans inf_le_left)) (key (hp.trans inf_le_right))))
    compl := fun x ↦ sSup {w | ¬ Overlap w x}
    sdiff := fun x y ↦ x ⊓ sSup {w | ¬ Overlap w y}
    himp := fun x y ↦ y ⊔ sSup {w | ¬ Overlap w x}
    inf_compl_le_bot := fun x ↦ le_of_forall_overlap fun p hp hp0 ↦ by
      obtain ⟨w, hw, q, hq, hqp, hqw⟩ := (hc x).2 p (hp.trans inf_le_right) hp0
      exact absurd ⟨q, hq, hqw, hqp.trans (hp.trans inf_le_left)⟩ hw
    top_le_sup_compl := fun x ↦ le_of_forall_overlap fun p _ hp0 ↦ by
      by_cases hpx : Overlap p x
      · exact hpx.mono le_rfl le_sup_left
      · exact .of_le hp0 (le_sup_of_le_right ((hc x).1 p hpx))
    sdiff_eq := fun _ _ ↦ rfl
    himp_eq := fun _ _ ↦ rfl }
end OrderBot

section WithBot
variable [PartialOrder α]

theorem _root_.Mereology.overlap_coe_withBot [NoBotOrder α] {a b : α} :
    Overlap (a : WithBot α) b ↔ Overlap a b := by
  constructor
  · rintro ⟨z, hz, hza, hzb⟩
    induction z with
    | bot => exact absurd isBot_bot hz
    | coe c => exact ⟨c, not_isBot c, WithBot.coe_le_coe.1 hza, WithBot.coe_le_coe.1 hzb⟩
  · rintro ⟨c, -, hca, hcb⟩
    exact ⟨c, fun h ↦ WithBot.not_coe_le_bot c (h ⊥), WithBot.coe_le_coe.2 hca,
      WithBot.coe_le_coe.2 hcb⟩

/-- Adding a null individual to a classical mereology without one gives a classical
mereology. -/
instance [NoBotOrder α] [IsClassicalMereology α] : IsClassicalMereology (WithBot α) where
  exists_not_overlap x y h := by
    induction x with
    | bot => exact absurd bot_le h
    | coe a =>
      have ha : ¬ IsBot (a : WithBot α) := fun hb ↦ WithBot.not_coe_le_bot a (hb ⊥)
      induction y with
      | bot => exact ⟨a, le_rfl, ha, fun ho ↦ ho.not_isBot_right isBot_bot⟩
      | coe b =>
        obtain ⟨z, hza, -, hzb⟩ := StronglySupplemented.exists_not_overlap
          (fun h' ↦ h (WithBot.coe_le_coe.2 h') : ¬ a ≤ b)
        exact ⟨z, WithBot.coe_le_coe.2 hza, fun hb ↦ WithBot.not_coe_le_bot z (hb ⊥),
          fun ho ↦ hzb (overlap_coe_withBot.1 ho)⟩
  exists_isSum P hP := by
    by_cases h : ∃ a : α, P a
    · obtain ⟨t, ht⟩ := exists_isSum (fun a : α ↦ P a) h
      refine ⟨t, fun x hx ↦ ?_, fun y hy hy0 ↦ ?_⟩
      · induction x with
        | bot => exact bot_le
        | coe a => exact WithBot.coe_le_coe.2 (ht.1 a hx)
      · induction y with
        | bot => exact absurd isBot_bot hy0
        | coe c =>
          obtain ⟨a, ha, ho⟩ := ht.2 c (WithBot.coe_le_coe.1 hy) (not_isBot c)
          exact ⟨a, ha, overlap_coe_withBot.2 ho⟩
    · refine ⟨⊥, fun x hx ↦ ?_, fun y hy hy0 ↦ absurd (isBot_iff_eq_bot.2 (le_bot_iff.1 hy)) hy0⟩
      induction x with
      | bot => exact le_rfl
      | coe a => exact absurd ⟨a, hx⟩ h
end WithBot

end IsClassicalMereology

end Mereology
