module

public import Linglib.Semantics.Plurality.Reciprocal
public import Linglib.Data.Examples.DalrympleEtAl1998
public import Linglib.Semantics.Quantification.Basic
public import Mathlib.Algebra.Group.Fin.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Abel
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Bounds.Defs

/-!
# Dalrymple, Kanazawa, Kim, Mchombo and Peters (1998): Reciprocal Expressions and the Concept of Reciprocity

The reciprocal is one polyadic quantifier whose six settings (`Reciprocal.Recip`) order its readings
as entailment does (`Reciprocal.setOf_recip_subset_iff`); [no iteration of a quantifier and a
permutation-invariant one yields Intermediate
Reciprocity](##intermediateReciprocity_not_iterateOtherPairs). By the Strongest Meaning Hypothesis a
sentence is felicitous when one interpretation consistent with the context entails the others,
[exactly when the consistent settings are closed under joins](##felicitous_iff), as for
[measles](##measles_isLeast). As the paper concedes, it [accepts *John and Bill are taller than each
other*](##smh_mispredicts_taller) and [denies the staring pirates eye contact](##pirates_isLeast).

## Implementation notes

A situation is an extension of the scope relation over a fixed antecedent set, so an interpretation
is the set of relations satisfying a quantifier, the non-linguistic information is a set of
relations, entailment is inclusion, and the hypothesis is `IsLeast` over the interpretations
consistent with that information. Each context is stated by the properties of the relation the paper
appeals to, the symmetry of *sit alongside* among them. The witnesses of consistency carry a circle
on positions to the group along its enumeration. The footnote's argument needs only the inner
quantifier to be permutation invariant. The quantified antecedents of §7 are not formalized.

## References

* [dalrymple-et-al-1998]
* [roberts-1987]
-/

@[expose] public section

namespace DalrympleEtAl1998

open Reciprocal Relation

variable {A : Type*} {R : A → A → Prop} {X : Finset A} {I : Set (A → A → Prop)} {k : ℕ}

/-! ### The six quantifiers (§5) -/

-- §5.4
theorem recip_alternative_iff [Std.Symm R] (c : Coverage) :
    Recip (c, .alternative) R X ↔ Recip (c, .plain) R X := by
  have : SymmGen R = R := funext₂ fun x y ↦ propext ⟨fun h ↦ h.elim id (symm_of R), .inl⟩
  cases c <;> simp only [Recip, Direction.rel, this]

/-! ### The reciprocal is not an iteration (§5.2, footnote 8)

[roberts-1987]'s iteration, repaired as (89), nests a quantifier `ENOUGH₂` over pairs, of type
`⟨2, 2⟩`, under a quantifier `ENOUGH₁` of type `⟨1, 1⟩`. On a symmetric relation a pair qualifies
when both its members do, so (89) is the iteration (i) of `ENOUGH₁` and a quantifier `ENOUGH₃` of
type `⟨1, 1⟩`. A cycle of six individuals and two cycles of three give every individual two
neighbours, so (i) cannot tell them apart once `ENOUGH₃` is permutation invariant, while only the
cycle of six is connected. -/

section Iteration

open Quantifier Quantifier.Det

/-- [roberts-1987]'s iteration as repaired in (89): `Q₁` members `x` of `P` are such that `Q₂` of
the pairs `(y, z)` of other members of `P` have `x` bearing `R` to `y` and `z` bearing `R` to
`x`. -/
def iterateOtherPairs (Q₁ : Det A) (Q₂ : Det (A × A)) (P : Set A) (R : A → A → Prop) : Prop :=
  Q₁ P {x | Q₂ ((P \ {x}) ×ˢ (P \ {x})) {p | R x p.1 ∧ R p.2 x}}

-- §5.2
theorem iterateOtherPairs_every_every (hX : X.Nontrivial) :
    iterateOtherPairs every every X R ↔ StrongReciprocity R X := by
  rw [strongReciprocity_iff, and_iff_right hX]
  refine ⟨fun h x hx y hy hxy ↦ ?_, fun h x hx p hp ↦
    ⟨h hx hp.1.1 fun e ↦ hp.1.2 e.symm, h hp.2.1 hx hp.2.2⟩⟩
  have hy' : y ∈ (X : Set A) \ {x} := ⟨hy, fun e ↦ hxy e.symm⟩
  exact (h hx (Set.mk_mem_prod hy' hy')).1

-- §5.2
theorem iterateOtherPairs_every_some :
    iterateOtherPairs every Det.some X R ↔ WeakReciprocity R X := by
  refine ⟨fun h ↦ ⟨fun x hx ↦ ?_, fun z hz ↦ ?_⟩, fun ⟨h₁, h₂⟩ x hx ↦ ?_⟩
  · obtain ⟨⟨y, _⟩, ⟨⟨hy, hyx⟩, -⟩, hR, -⟩ := h hx
    exact ⟨y, hy, hR, fun e ↦ hyx e.symm⟩
  · obtain ⟨⟨_, y⟩, ⟨-, hy, hyz⟩, -, hR⟩ := h hz
    exact ⟨y, hy, hR, hyz⟩
  · obtain ⟨y, hy, hxy, hne⟩ := h₁ x hx
    obtain ⟨z, hz, hzx, hne'⟩ := h₂ x hx
    exact ⟨(y, z), ⟨⟨hy, fun e ↦ hne e.symm⟩, hz, hne'⟩, hxy, hzx⟩

/-- The iteration (i) of footnote 8, in which `Q₁` members of `P` bear `R` to `Q₂` of the other
members of `P`. -/
def iterateOthers (Q₁ Q₂ : Det A) (P : Set A) (R : A → A → Prop) : Prop :=
  Q₁ P {x | Q₂ (P \ {x}) {y | R x y}}

/-- A quantifier over pairs read on squares, the quantifier `ENOUGH₃` of footnote 8. -/
def square (Q : Det (A × A)) : Det A := fun D B ↦ Q (D ×ˢ D) (B ×ˢ B)

/-- A quantifier over pairs is permutation invariant when no permutation of the universe, applied
to both members of every pair, changes it, as a logical quantifier of type `⟨2, 2⟩` is. -/
def PermInvariant (Q : Det (A × A)) : Prop :=
  ∀ (σ : Equiv.Perm A) (B C : Set (A × A)), Q (Prod.map σ σ ⁻¹' B) (Prod.map σ σ ⁻¹' C) ↔ Q B C

theorem PermInvariant.quantityInvariant_square {Q : Det (A × A)} (hQ : PermInvariant Q) :
    (square Q).QuantityInvariant := fun σ D B ↦ by
  simpa only [DalrympleEtAl1998.square, Set.preimage_prod_map_prod] using hQ σ (D ×ˢ D) (B ×ˢ B)

-- footnote 8
theorem iterateOtherPairs_iff [Std.Symm R] (Q₁ : Det A) (Q₂ : Det (A × A)) (P : Set A) :
    iterateOtherPairs Q₁ Q₂ P R ↔ iterateOthers Q₁ (square Q₂) P R := by
  have (x : A) : {p : A × A | R x p.1 ∧ R p.2 x} = {y | R x y} ×ˢ {y | R x y} :=
    Set.ext fun _ ↦ and_congr_right' ⟨symm_of R, symm_of R⟩
  simp only [iterateOtherPairs, iterateOthers, square, this]

open Fin.NatCast in
theorem intermediate_of_succ {n : ℕ} [NeZero n] (hn : 2 ≤ n) {R : Fin n → Fin n → Prop}
    (hR : ∀ x, R x (x + 1)) : IntermediateReciprocity R Finset.univ := by
  have step (x : Fin n) :
      TransGen (fun a b ↦ a ∈ Finset.univ ∧ b ∈ Finset.univ ∧ R a b) x (x + 1) :=
    .single ⟨Finset.mem_univ _, Finset.mem_univ _, hR x⟩
  have chain (x : Fin n) (k : ℕ) :
      TransGen (fun a b ↦ a ∈ Finset.univ ∧ b ∈ Finset.univ ∧ R a b) x
        (x + ((k + 1 : ℕ) : Fin n)) := by
    induction k with
    | zero => simpa using step x
    | succ k ih =>
      have e : x + ((k + 1 + 1 : ℕ) : Fin n) = x + ((k + 1 : ℕ) : Fin n) + 1 := by
        push_cast
        abel
      exact e ▸ ih.trans (step _)
  refine intermediateReciprocity_iff.2
    ⟨Finset.univ_nontrivial_iff.2 (Fin.nontrivial_iff_two_le.2 hn), fun x _ y _ hxy ↦ ?_⟩
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_one_of_ne_zero
    (Fin.val_ne_zero_iff.2 (sub_ne_zero.2 (Ne.symm hxy)) : (y - x).val ≠ 0)
  have := chain x k
  rwa [← hk, Fin.cast_val_eq_self, add_sub_cancel] at this

/-- Individuals seated in a circle, each beside the next and the previous; for six, the model
(ii) of footnote 8. -/
def circle {n : ℕ} [NeZero n] (x y : Fin n) : Prop := y = x + 1 ∨ x = y + 1

/-- Six individuals in two cycles of three, the model (iii) of footnote 8. -/
def twoTriangles (x y : Fin 6) : Prop := x ≠ y ∧ x.val / 3 = y.val / 3

instance {n : ℕ} [NeZero n] : DecidableRel (circle (n := n)) :=
  fun _ _ ↦ inferInstanceAs (Decidable (_ ∨ _))

instance {n : ℕ} [NeZero n] : Std.Symm (circle (n := n)) := ⟨fun _ _ h ↦ h.symm⟩

instance : DecidableRel twoTriangles := fun _ _ ↦ inferInstanceAs (Decidable (_ ∧ _))

theorem intermediate_circle {n : ℕ} [NeZero n] (hn : 2 ≤ n) :
    IntermediateReciprocity (circle (n := n)) Finset.univ :=
  intermediate_of_succ hn fun _ ↦ .inl rfl

theorem not_intermediate_twoTriangles : ¬ IntermediateReciprocity twoTriangles Finset.univ := by
  intro h
  have hblock {a b : Fin 6}
      (hab : TransGen (fun a b ↦ a ∈ Finset.univ ∧ b ∈ Finset.univ ∧ twoTriangles a b) a b) :
      a.val / 3 = b.val / 3 := by
    induction hab with
    | single h => exact h.2.2.2
    | tail _ h ih => exact ih.trans h.2.2.2
  exact absurd (hblock ((intermediateReciprocity_iff.1 h).2 (Finset.mem_univ 0)
    (Finset.mem_univ 3) (by decide))) (by decide)

theorem iterateOthers_circle_iff (Q₁ Q₂ : Det (Fin 6)) (hQ₂ : Q₂.QuantityInvariant) :
    iterateOthers Q₁ Q₂ Set.univ circle ↔ iterateOthers Q₁ Q₂ Set.univ twoTriangles := by
  have key (x : Fin 6) : ∃ e : Equiv.Perm (Fin 6),
      (∀ y, e y ≠ x ↔ y ≠ x) ∧ ∀ y, circle x (e y) ↔ twoTriangles x y := by
    fin_cases x
    · exact ⟨Equiv.swap 2 5, by decide, by decide⟩
    · exact ⟨Equiv.refl _, by decide, by decide⟩
    · exact ⟨Equiv.swap 0 3, by decide, by decide⟩
    · exact ⟨Equiv.swap 2 5, by decide, by decide⟩
    · exact ⟨Equiv.refl _, by decide, by decide⟩
    · exact ⟨Equiv.swap 0 3, by decide, by decide⟩
  have h (x : Fin 6) : Q₂ (Set.univ \ {x}) {y | circle x y} ↔
      Q₂ (Set.univ \ {x}) {y | twoTriangles x y} := by
    obtain ⟨e, hA, hB⟩ := key x
    have hA' : e ⁻¹' (Set.univ \ {x}) = Set.univ \ {x} := Set.ext fun y ↦ by simpa using hA y
    rw [← hQ₂ e, hA', show e ⁻¹' {y | circle x y} = {y | twoTriangles x y} from Set.ext hB]
  simp only [iterateOthers, h]

-- footnote 8 (i)
theorem intermediateReciprocity_not_iterateOthers (Q₁ Q₂ : Det (Fin 6))
    (hQ₂ : Q₂.QuantityInvariant) :
    ¬ ∀ R : Fin 6 → Fin 6 → Prop, Std.Symm R →
      (iterateOthers Q₁ Q₂ Set.univ R ↔ IntermediateReciprocity R Finset.univ) := by
  intro h
  have h₁ := h circle inferInstance
  have h₂ := h twoTriangles ⟨fun _ _ h ↦ ⟨h.1.symm, h.2.symm⟩⟩
  exact not_intermediate_twoTriangles
    (h₂.1 ((iterateOthers_circle_iff Q₁ Q₂ hQ₂).1 (h₁.2 (intermediate_circle (by omega)))))

/-- No iteration of a quantifier over individuals and a permutation-invariant quantifier over
pairs, as [roberts-1987]'s (89) is, expresses Intermediate Reciprocity on every symmetric
relation (footnote 8). -/
theorem intermediateReciprocity_not_iterateOtherPairs (Q₁ : Det (Fin 6))
    (Q₂ : Det (Fin 6 × Fin 6)) (hQ₂ : PermInvariant Q₂) :
    ¬ ∀ R : Fin 6 → Fin 6 → Prop, Std.Symm R →
      (iterateOtherPairs Q₁ Q₂ Set.univ R ↔ IntermediateReciprocity R Finset.univ) := fun h ↦
  intermediateReciprocity_not_iterateOthers Q₁ (square Q₂) hQ₂.quantityInvariant_square
    fun R _ ↦ (iterateOtherPairs_iff Q₁ Q₂ _).symm.trans (h R ‹_›)

end Iteration

/-! ### The Strongest Meaning Hypothesis (§6.2)

The interpretations of a sentence are the images of the six settings, and by the hypothesis it is
felicitous in a context supplying the information `I` when, among the interpretations consistent
with `I`, one entails all the others: when `Set.range (interpretation X) ∩ {p | (p ∩ I).Nonempty}`
has a least element, which the sentence then expresses. The consistent settings form a lower set,
so the strongest of them, when there is one, gives that element. -/

/-- The interpretation of *the Xs R each other* with the reciprocal read at setting `q` is the
set of extensions of the scope relation that make the sentence true. -/
def interpretation (X : Finset A) (q : Coverage × Direction) : Set (A → A → Prop) :=
  {R | Recip q R X}

theorem interpretation_antitone : Antitone (interpretation X) :=
  fun _ _ hq _ hR ↦ recip_antitone hq hR

theorem isLowerSet_consistent : IsLowerSet (interpretation X ⁻¹' {p | (p ∩ I).Nonempty}) :=
  fun _ _ hq h ↦ h.mono (Set.inter_subset_inter_left _ (interpretation_antitone hq))

-- the strongest consistent setting, once `I` excludes a setting below each one not below `q`
theorem isLeast_of_blocked {q : Coverage × Direction} {t : Finset (Coverage × Direction)}
    (hq : (interpretation X q ∩ I).Nonempty) (ht : ∀ q', ¬ q' ≤ q → ∃ c ∈ t, c ≤ q')
    (hI : ∀ c ∈ t, ¬ (interpretation X c ∩ I).Nonempty) :
    IsLeast (Set.range (interpretation X) ∩ {p | (p ∩ I).Nonempty}) (interpretation X q) :=
  (isLowerSet_consistent.isGreatest_of_forall_not_le hq ht hI).isLeast_range_inter
    interpretation_antitone

/-- With four or more members, a reciprocal sentence is felicitous exactly when the settings
consistent with the context are closed under joins; it then expresses the interpretation at their
join. -/
theorem felicitous_iff (hX : 4 ≤ X.card) :
    (∃ p, IsLeast (Set.range (interpretation X) ∩ {p | (p ∩ I).Nonempty}) p) ↔
      (interpretation X ⁻¹' {p | (p ∩ I).Nonempty}).Nonempty ∧
        SupClosed (interpretation X ⁻¹' {p | (p ∩ I).Nonempty}) :=
  exists_isLeast_range_inter_iff (fun _ _ ↦ setOf_recip_subset_iff hX)
    fun _ _ h ⟨R, hR⟩ ↦ ⟨R, h hR.1, hR.2⟩

-- (95)
theorem isLeast_strong (h : ∃ R ∈ I, StrongReciprocity R X) :
    IsLeast (Set.range (interpretation X) ∩ {p | (p ∩ I).Nonempty})
      (interpretation X (.ful, .plain)) :=
  isLeast_of_blocked (let ⟨R, hRI, hR⟩ := h; ⟨R, hR, hRI⟩) (t := ∅) (by decide) (by simp)

/-! ### How many others one bears the relation to

Two contexts bound how many individuals one bears the relation to: people have only two sides,
and a pirate stares at only one other. Strong Reciprocity then bounds the antecedent set by one
more than the bound, and Strong Alternative Reciprocity by one more than twice it. -/

/-- The non-linguistic information that each individual bears `R` to at most `k` individuals. -/
def boundedDegree (k : ℕ) : Set (A → A → Prop) :=
  {R | ∀ x, {y | R x y}.encard ≤ k}

/-- In the non-linguistic information for *staring at each other*, each stares at only one
other. -/
def singleValued : Set (A → A → Prop) :=
  {R | ∀ x y y', R x y → R x y' → y = y'}

theorem singleValued_subset_boundedDegree : singleValued ⊆ boundedDegree (A := A) 1 :=
  fun _ hR x ↦ Set.encard_le_one_iff.2 fun _ _ ↦ hR x _ _

theorem card_le_of_strongReciprocity (hR : R ∈ boundedDegree k) (h : StrongReciprocity R X) :
    X.card ≤ k + 1 := by
  classical
  obtain ⟨hX, hP⟩ := strongReciprocity_iff.1 h
  obtain ⟨x, hx⟩ := hX.nonempty
  have : ((X.erase x : Finset A) : Set A).encard ≤ k := (Set.encard_le_encard fun y hy ↦
    hP hx (Finset.mem_of_mem_erase hy) (Finset.ne_of_mem_erase hy).symm).trans (hR x)
  rw [Set.encard_coe_eq_coe_finsetCard, Nat.cast_le, Finset.card_erase_of_mem hx] at this
  omega

theorem card_le_of_strongAlternative (hR : R ∈ boundedDegree k)
    (h : Recip (.ful, .alternative) R X) : X.card ≤ 2 * k + 1 := by
  classical
  let E := X.offDiag.filter fun p ↦ R p.1 p.2
  have hcover : X.offDiag ⊆ E ∪ E.image Prod.swap := by
    rintro ⟨x, y⟩ hxy
    obtain ⟨hx, hy, hne⟩ := Finset.mem_offDiag.1 hxy
    rcases (strongReciprocity_iff.1 (show StrongReciprocity (SymmGen R) X from h)).2 hx hy hne
      with hR' | hR'
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hxy, hR'⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.2
        ⟨(y, x), Finset.mem_filter.2 ⟨Finset.mem_offDiag.2 ⟨hy, hx, hne.symm⟩, hR'⟩, rfl⟩)
  have hfibre (a : A) : (E.filter fun p ↦ p.1 = a).card ≤ k := by
    have := (Set.encard_le_encard_of_injOn
      (s := ((E.filter fun p ↦ p.1 = a : Finset (A × A)) : Set (A × A)))
      (f := Prod.snd) (t := {y | R a y})
      (fun p hp ↦ ?_) fun p hp q hq hpq ↦ ?_).trans (hR a)
    · rwa [Set.encard_coe_eq_coe_finsetCard, Nat.cast_le] at this
    · obtain ⟨hpE, rfl⟩ := Finset.mem_filter.1 hp
      exact (Finset.mem_filter.1 hpE).2
    · exact Prod.ext ((Finset.mem_filter.1 hp).2.trans (Finset.mem_filter.1 hq).2.symm) hpq
  have hE : E.card ≤ k * X.card :=
    (E.card_le_mul_card_image k fun a _ ↦ hfibre a).trans <| Nat.mul_le_mul_left _ <|
      Finset.card_le_card fun x hx ↦ by
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hx
        exact (Finset.mem_offDiag.1 (Finset.mem_filter.1 hp).1).1
  have hsum := (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
  have := Finset.card_image_le (s := E) (f := Prod.swap)
  rw [Finset.offDiag_card] at hsum
  obtain h0 | hpos := Nat.eq_zero_or_pos X.card
  · omega
  have key : X.card * (X.card - 1) ≤ X.card * (2 * k) := by
    rw [Nat.mul_sub_one, Nat.mul_left_comm, Nat.mul_comm X.card k]
    generalize X.card * X.card = m at *
    omega
  have := Nat.le_of_mul_le_mul_left key hpos
  omega

/-! ### Relations carried from an enumeration

A relation on the positions `Fin X.card` carries to the members of `X` along their enumeration,
keeping Intermediate Reciprocity, symmetry, and how many others each bears it to. -/

/-- A relation on `Fin X.card` carried to the members of `X` along the enumeration of `X`. -/
def ofFin (X : Finset A) (r : Fin X.card → Fin X.card → Prop) (a b : A) : Prop :=
  ∃ (ha : a ∈ X) (hb : b ∈ X), r (X.equivFin ⟨a, ha⟩) (X.equivFin ⟨b, hb⟩)

section OfFin

variable {r : Fin X.card → Fin X.card → Prop}

instance [Std.Symm r] : Std.Symm (ofFin X r) := ⟨fun _ _ ⟨ha, hb, h⟩ ↦ ⟨hb, ha, symm_of r h⟩⟩

theorem intermediateReciprocity_ofFin (h : IntermediateReciprocity r Finset.univ) :
    IntermediateReciprocity (ofFin X r) X := by
  obtain ⟨hn, h⟩ := intermediateReciprocity_iff.1 h
  refine intermediateReciprocity_iff.2 ⟨?_, fun a ha b hb hab ↦ ?_⟩
  · rw [← Finset.one_lt_card_iff_nontrivial] at hn ⊢
    simpa using hn
  · have := TransGen.lift (p := fun x y ↦ x ∈ X ∧ y ∈ X ∧ ofFin X r x y)
      (fun i ↦ (X.equivFin.symm i : A))
      (fun i j hij ↦ ⟨(X.equivFin.symm i).2, (X.equivFin.symm j).2, (X.equivFin.symm i).2,
        (X.equivFin.symm j).2, by simpa using hij.2.2⟩) _ _
      (h (Finset.mem_univ (X.equivFin ⟨a, ha⟩)) (Finset.mem_univ (X.equivFin ⟨b, hb⟩))
        (by simpa using hab))
    simpa only [Function.onFun, Equiv.symm_apply_apply] using this

theorem ofFin_mem_boundedDegree (hr : r ∈ boundedDegree k) : ofFin X r ∈ boundedDegree k := by
  intro a
  by_cases ha : a ∈ X
  · refine (Set.encard_le_encard fun b hb ↦ ?_).trans <|
      (Set.encard_image_le (fun i ↦ (X.equivFin.symm i : A)) _).trans (hr (X.equivFin ⟨a, ha⟩))
    obtain ⟨_, hb', h⟩ := hb
    exact ⟨X.equivFin ⟨b, hb'⟩, h, by simp⟩
  · simp [ofFin, ha]

theorem ofFin_mem_singleValued (hr : r ∈ singleValued) : ofFin X r ∈ singleValued :=
  fun _ _ _ ⟨_, _, h⟩ ⟨_, _, h'⟩ ↦ congrArg Subtype.val (X.equivFin.injective (hr _ _ _ h h'))

end OfFin

/-! ### Pitchers sitting alongside each other (§6.1) -/

/-- In the non-linguistic information for *sat alongside each other*, sitting alongside is
symmetric, and a person, having only two sides, sits alongside at most two others. -/
def alongside : Set (A → A → Prop) :=
  {R | Std.Symm R ∧ R ∈ boundedDegree 2}

theorem circle_mem_boundedDegree {n : ℕ} [NeZero n] : circle ∈ boundedDegree (A := Fin n) 2 :=
  fun x ↦ (Set.encard_le_encard (t := {x + 1, x - 1}) fun y hy ↦ by
    rcases hy with rfl | rfl
    · exact .inl rfl
    · exact .inr (add_sub_cancel_right y 1).symm).trans <|
    (Set.encard_insert_le _ _).trans (by simp [one_add_one_eq_two])

-- (96)
theorem pitchers_isLeast (hX : 4 ≤ X.card) :
    IsLeast (Set.range (interpretation X) ∩ {p | (p ∩ alongside).Nonempty})
      (interpretation X (.lin, .plain)) := by
  have : NeZero X.card := ⟨by omega⟩
  refine isLeast_of_blocked ⟨ofFin X circle,
    intermediateReciprocity_ofFin (intermediate_circle (n := X.card) (by omega)), inferInstance,
    ofFin_mem_boundedDegree circle_mem_boundedDegree⟩ (t := {(.ful, .alternative)}) (by decide) ?_
  simp only [Finset.mem_singleton, forall_eq]
  rintro ⟨R, h, _, hR⟩
  have := card_le_of_strongReciprocity hR ((recip_alternative_iff (R := R) .ful).1 h)
  omega

/-- Five individuals in a round, each bearing the relation to the next two. -/
def nextTwo (x y : Fin 5) : Prop := y = x + 1 ∨ y = x + 2

instance : DecidableRel nextTwo := fun _ _ ↦ inferInstanceAs (Decidable (_ ∨ _))

-- (96): without the symmetry of *sit alongside*, Strong Alternative and Intermediate Reciprocity
-- are both consistent with two sides, but their join, Strong Reciprocity, is not
theorem not_felicitous_boundedDegree :
    ¬ ∃ p, IsLeast (Set.range (interpretation (Finset.univ : Finset (Fin 5))) ∩
      {p | (p ∩ boundedDegree 2).Nonempty}) p := by
  rw [felicitous_iff (by simp)]
  rintro ⟨-, h⟩
  have hT : (Coverage.ful, Direction.alternative) ∈ interpretation Finset.univ ⁻¹'
      {p | (p ∩ boundedDegree 2).Nonempty} :=
    ⟨nextTwo, show StrongReciprocity (SymmGen nextTwo) Finset.univ by decide, fun x ↦
      (Set.encard_le_encard (t := {x + 1, x + 2}) fun _ hy ↦ hy).trans <|
        (Set.encard_insert_le _ _).trans (by simp [one_add_one_eq_two])⟩
  have hC : (Coverage.lin, Direction.plain) ∈ interpretation Finset.univ ⁻¹'
      {p | (p ∩ boundedDegree 2).Nonempty} :=
    ⟨circle, intermediate_circle (n := 5) (by omega), circle_mem_boundedDegree⟩
  have := h hT hC
  rw [show ((Coverage.ful, Direction.alternative) ⊔ (Coverage.lin, Direction.plain) :
    Coverage × Direction) = (.ful, .plain) by decide] at this
  obtain ⟨R, hR, hdeg⟩ := this
  simpa using card_le_of_strongReciprocity hdeg hR

/-! ### Measles (§6.1) -/

/-- In the non-linguistic information for *gave each other measles*, a person catches measles
from at most one person, and measles is not passed around in a circle. -/
def measles : Set (A → A → Prop) :=
  {R | (∀ x x' y, R x y → R x' y → x = x') ∧ ∀ x, ¬ TransGen R x x}

-- (99)
theorem not_oneWayWeak_of_measles (hR : R ∈ measles) : ¬ OneWayWeakReciprocity R X := fun h ↦
  let ⟨x, _, hx⟩ := h.exists_transGen_self
  hR.2 x hx

theorem not_strongAlternative_of_measles (hR : R ∈ measles) (hX : 3 ≤ X.card) :
    ¬ Recip (.ful, .alternative) R X := by
  classical
  intro h
  obtain ⟨z, hz, hlast⟩ : ∃ z ∈ X, ∀ y ∈ X, R z y → z = y := by
    by_contra! hall
    exact not_oneWayWeak_of_measles hR <| oneWayWeakReciprocity_iff.2
      ⟨Finset.one_lt_card_iff_nontrivial.1 (by omega), fun x hx ↦
        let ⟨y, hy, hxy, hne⟩ := hall x hx
        ⟨y, hy, hne, hxy⟩⟩
  have h' : StrongReciprocity (SymmGen R) X := h
  have hin {y} (hy : y ∈ X) (hyz : y ≠ z) : R y z :=
    Or.elim ((strongReciprocity_iff.1 h').2 hy hz hyz) id fun hzy ↦
      absurd (hlast y hy hzy).symm hyz
  obtain ⟨y, hy, hyz⟩ := X.exists_mem_ne (by omega) z
  obtain ⟨y', hy', hy'y⟩ := (X.erase z).exists_mem_ne
    (by have := Finset.pred_card_le_card_erase (s := X) (a := z); omega) y
  obtain ⟨hy'z, hy'X⟩ := Finset.mem_erase.1 hy'
  exact hy'y (hR.1 _ _ _ (hin hy'X hy'z) (hin hy hyz))

theorem exists_intermediateAlternative_measles (hX : X.Nontrivial) {s : A} (hs : s ∈ X) :
    ∃ R ∈ measles, Recip (.lin, .alternative) R X := by
  refine ⟨fun x y ↦ x = s ∧ y ≠ s, ⟨fun x x' y hx hx' ↦ hx.1.trans hx'.1.symm, fun x hx ↦ ?_⟩, ?_⟩
  · obtain ⟨b, ⟨rfl, -⟩, -⟩ := TransGen.head'_iff.1 hx
    obtain ⟨c, -, -, hne⟩ := TransGen.tail'_iff.1 hx
    exact hne rfl
  · show IntermediateReciprocity (SymmGen fun x y ↦ x = s ∧ y ≠ s) X
    refine intermediateReciprocity_iff.2 ⟨hX, fun x hx y hy hxy ↦ ?_⟩
    by_cases hxs : x = s
    · exact .single ⟨hx, hy, .of_rel ⟨hxs, hxs ▸ hxy.symm⟩⟩
    by_cases hys : y = s
    · exact .single ⟨hx, hy, .of_rel_symm ⟨hys, hys ▸ hxy⟩⟩
    exact .tail (.single ⟨hx, hs, .of_rel_symm ⟨rfl, hxs⟩⟩) ⟨hs, hy, .of_rel ⟨rfl, hys⟩⟩

/-- With three or more students, *gave each other measles* expresses Intermediate Alternative
Reciprocity (98), since every stronger quantifier is inconsistent with the measles facts. -/
theorem measles_isLeast (hX : 3 ≤ X.card) :
    IsLeast (Set.range (interpretation X) ∩ {p | (p ∩ measles).Nonempty})
      (interpretation X (.lin, .alternative)) := by
  obtain ⟨s, hs⟩ := Finset.card_pos.1 (by omega : 0 < X.card)
  obtain ⟨R₀, hR₀, h₀⟩ :=
    exists_intermediateAlternative_measles (Finset.one_lt_card_iff_nontrivial.1 (by omega)) hs
  refine isLeast_of_blocked ⟨R₀, h₀, hR₀⟩ (t := {(.ful, .alternative), (.tot, .plain)})
    (by decide) ?_
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨fun ⟨R, h, hR⟩ ↦ not_strongAlternative_of_measles hR hX h,
    fun ⟨R, h, hR⟩ ↦ not_oneWayWeak_of_measles hR h⟩

/-! ### Two members and an asymmetric relation (§6.3) -/

section Pair

variable [DecidableEq A]

/-- The non-linguistic information that the relation is asymmetric, as *on top of* and *taller
than* are. -/
def asymmetric : Set (A → A → Prop) :=
  {R | ∀ x y, R x y → ¬ R y x}

-- (108): on two members every coverage gives the same reading, and asymmetry leaves only the
-- alternative relation
theorem pair_isLeast {a b : A} (hab : a ≠ b) :
    IsLeast (Set.range (interpretation {a, b}) ∩ {p | (p ∩ asymmetric).Nonempty})
      (interpretation {a, b} (.tot, .alternative)) := by
  rw [show interpretation {a, b} (.tot, .alternative) = interpretation {a, b} (.ful, .alternative)
    from Set.ext fun R ↦ (recip_pair .tot .alternative).trans (recip_pair .ful .alternative).symm]
  refine isLeast_of_blocked ⟨fun x y ↦ x = a ∧ y = b, (recip_pair .ful .alternative).2
    ⟨hab, Or.inl ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩⟩, ?_⟩
    (t := {(.tot, .plain)}) (by decide) ?_
  · rintro x y ⟨rfl, rfl⟩ ⟨rfl, -⟩
    exact hab rfl
  · simp only [Finset.mem_singleton, forall_eq]
    rintro ⟨R, h, hR⟩
    obtain ⟨-, hab', hba'⟩ := (recip_pair .tot .plain).1 h
    exact hR _ _ hab' hba'

/-- The hypothesis cannot tell (108) from (109): on two members and an asymmetric relation it
makes both felicitous, but only (108) is. -/
theorem smh_mispredicts_taller {a b : A} (hab : a ≠ b) :
    ((∃ p, IsLeast (Set.range (interpretation {a, b}) ∩ {p | (p ∩ asymmetric).Nonempty}) p) ↔
        Examples.ex108.judgment = .acceptable) ∧
      ¬ ((∃ p, IsLeast (Set.range (interpretation {a, b}) ∩
        {p | (p ∩ asymmetric).Nonempty}) p) ↔ Examples.ex109.judgment = .acceptable) :=
  have h : ∃ p, IsLeast (Set.range (interpretation {a, b}) ∩
      {p | (p ∩ asymmetric).Nonempty}) p := ⟨_, pair_isLeast hab⟩
  ⟨iff_of_true h rfl, fun h' ↦ absurd (h'.1 h) (by decide)⟩

end Pair

/-! ### The staring pirates (§6.3) -/

theorem not_mutual_of_intermediate (hR : R ∈ singleValued) (h : IntermediateReciprocity R X)
    (hX : 3 ≤ X.card) {a b : A} (ha : a ∈ X) (hab : R a b) (hba : R b a) : False := by
  classical
  have hreach (y) (hy : TransGen (fun u v ↦ u ∈ X ∧ v ∈ X ∧ R u v) a y) : y = a ∨ y = b := by
    induction hy with
    | single h => exact .inr (hR _ _ _ h.2.2 hab)
    | tail _ hcy ih =>
      rcases ih with rfl | rfl
      · exact .inr (hR _ _ _ hcy.2.2 hab)
      · exact .inl (hR _ _ _ hcy.2.2 hba)
  obtain ⟨c, hc⟩ : ((X.erase a).erase b).Nonempty := Finset.card_pos.1 (by
    have := Finset.pred_card_le_card_erase (s := X) (a := a)
    have := Finset.pred_card_le_card_erase (s := X.erase a) (a := b)
    omega)
  obtain ⟨hcb, hca, hcX⟩ : c ≠ b ∧ c ≠ a ∧ c ∈ X := by simpa using hc
  rcases hreach c ((intermediateReciprocity_iff.1 h).2 ha hcX hca.symm) with rfl | rfl
  · exact hca rfl
  · exact hcb rfl

/-- Pirates each staring at the next around a circle. -/
def stareRound {n : ℕ} [NeZero n] (x y : Fin n) : Prop := y = x + 1

/-- Four pirates in two pairs, each staring at the other of the pair. -/
def stareBack (x y : Fin 4) : Prop := x ≠ y ∧ x.val / 2 = y.val / 2

instance : DecidableRel stareBack := fun _ _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- With four or more pirates, the fewest for which the paper's argument excludes both quantifiers
built on `FUL`, the hypothesis makes *staring at each other* express Intermediate Reciprocity
(110), which a single-valued relation satisfies only without eye contact. -/
theorem pirates_isLeast (hX : 4 ≤ X.card) :
    IsLeast (Set.range (interpretation X) ∩ {p | (p ∩ singleValued).Nonempty})
      (interpretation X (.lin, .plain)) := by
  have : NeZero X.card := ⟨by omega⟩
  refine isLeast_of_blocked ⟨ofFin X stareRound,
    intermediateReciprocity_ofFin (intermediate_of_succ (n := X.card) (by omega) fun _ ↦ rfl),
    ofFin_mem_singleValued fun _ _ _ h h' ↦ h.trans h'.symm⟩ (t := {(.ful, .alternative)})
    (by decide) ?_
  simp only [Finset.mem_singleton, forall_eq]
  rintro ⟨R, h, hR⟩
  have := card_le_of_strongAlternative (singleValued_subset_boundedDegree hR) h
  omega

-- (110)
theorem pirates_eyeContact :
    stareBack ∈ singleValued ∧ OneWayWeakReciprocity stareBack Finset.univ ∧
      stareBack ∉ interpretation Finset.univ (.lin, .plain) := by
  have hR : stareBack ∈ singleValued := by
    show ∀ x y y' : Fin 4, stareBack x y → stareBack x y' → y = y'
    decide
  exact ⟨hR, by decide, fun h ↦ not_mutual_of_intermediate hR h (by decide)
    (Finset.mem_univ 0) (b := 1) (by decide) (by decide)⟩

end DalrympleEtAl1998
