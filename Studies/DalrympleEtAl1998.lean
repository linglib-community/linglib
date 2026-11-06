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

The reciprocal is one polyadic quantifier whose strength among the six settings of two parameters
(`Reciprocal.Recip`) context fixes; [iterating a quantifier and a permutation-invariant one never
yields Intermediate Reciprocity](##intermediateReciprocity_not_iterateOtherPairs). By the Strongest
Meaning Hypothesis a sentence is felicitous when one interpretation consistent with the context
entails the others, and expresses it: [Intermediate Reciprocity for the
pitchers](##pitchers_isLeast), [Intermediate Alternative Reciprocity for
measles](##measles_isLeast). As the paper concedes, it [accepts *John and Bill are taller than each
other*](##smh_mispredicts_taller) and [denies the staring pirates eye contact](##pirates_isLeast).

## Implementation notes

A situation is an extension of the scope relation over a fixed antecedent set, so an
interpretation is the set of relations satisfying a quantifier, the non-linguistic information is
a set of relations, and entailment is inclusion. Each context is stated by the properties of the
relation the paper appeals to, the symmetry of *sit alongside* among them. The pitchers'
consistency witness seats them in a circle rather than a row; either puts each beside at most two
others. The footnote's argument needs only the inner quantifier to be permutation invariant. The
quantified antecedents of §7 are not formalized.

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

/-! ### The Strongest Meaning Hypothesis (§6.2) -/

/-- The interpretation of *the Xs R each other* with the reciprocal read at setting `q` is the
set of extensions of the scope relation that make the sentence true. -/
def interpretation (X : Finset A) (q : Coverage × Direction) : Set (A → A → Prop) :=
  {R | Recip q R X}

/-- The interpretations consistent with the non-linguistic information `I`. -/
def candidates (X : Finset A) (I : Set (A → A → Prop)) : Set (Set (A → A → Prop)) :=
  {p | ∃ q, interpretation X q = p ∧ (p ∩ I).Nonempty}

/-- By the Strongest Meaning Hypothesis a reciprocal sentence is felicitous in the context `I`
when one of its candidates entails all the others, and it then expresses that one. -/
def Felicitous (X : Finset A) (I : Set (A → A → Prop)) : Prop :=
  ∃ p, IsLeast (candidates X I) p

theorem interpretation_antitone : Antitone (interpretation X) :=
  fun _ _ hq _ hR ↦ recip_antitone hq hR

theorem nonempty_inter_of_le {q q' : Coverage × Direction} (hq : q ≤ q')
    (h : (interpretation X q' ∩ I).Nonempty) : (interpretation X q ∩ I).Nonempty :=
  h.mono (Set.inter_subset_inter_left _ (interpretation_antitone hq))

theorem isLeast_of_isGreatest {q : Coverage × Direction}
    (h : IsGreatest {q | (interpretation X q ∩ I).Nonempty} q) :
    IsLeast (candidates X I) (interpretation X q) :=
  ⟨⟨q, rfl, h.1⟩, by
    rintro _ ⟨q', rfl, hq'⟩
    exact interpretation_antitone (h.2 hq')⟩

-- (95)
theorem isLeast_strong (h : ∃ R ∈ I, StrongReciprocity R X) :
    IsLeast (candidates X I) (interpretation X (.ful, .plain)) :=
  isLeast_of_isGreatest ⟨let ⟨R, hRI, hR⟩ := h; ⟨R, hR, hRI⟩, fun ⟨c, d⟩ _ ↦
    Prod.mk_le_mk.2 ⟨by cases c <;> decide, by cases d <;> decide⟩⟩

/-! ### How many others one bears the relation to

Two contexts bound how many individuals one bears the relation to: people have only two sides,
and a pirate stares at only one other. Strong Reciprocity then bounds the antecedent set by one
more than the bound, and Strong Alternative Reciprocity by one more than twice it. -/

/-- The non-linguistic information that each individual bears `R` to at most `k` individuals. -/
def boundedDegree (k : ℕ) : Set (A → A → Prop) :=
  {R | ∀ x, {y | R x y}.encard ≤ k}

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

/-- With five pitchers, *sat alongside each other* expresses Intermediate Reciprocity (96):
symmetry makes each quantifier its own alternative, and two sides leave no room for Strong
Reciprocity. -/
theorem pitchers_isLeast :
    IsLeast (candidates (Finset.univ : Finset (Fin 5)) alongside)
      (interpretation Finset.univ (.lin, .plain)) := by
  refine isLeast_of_isGreatest ⟨⟨circle, intermediate_circle (by omega), inferInstance,
    circle_mem_boundedDegree⟩, ?_⟩
  have hsr : ¬ (interpretation (Finset.univ : Finset (Fin 5)) (.ful, .alternative) ∩
      alongside).Nonempty := by
    rintro ⟨R, h, _, hR⟩
    simpa using card_le_of_strongReciprocity hR ((recip_alternative_iff (R := R) .ful).1 h)
  rintro ⟨c, d⟩ h
  cases c <;> cases d
  all_goals first
    | decide
    | exact absurd (nonempty_inter_of_le (by decide) h) hsr

/-- Five individuals in a round, each bearing the relation to the next two. -/
def nextTwo (x y : Fin 5) : Prop := y = x + 1 ∨ y = x + 2

instance : DecidableRel nextTwo := fun _ _ ↦ inferInstanceAs (Decidable (_ ∨ _))

-- (96): without the symmetry of *sit alongside*, two sides leave Strong Alternative and
-- Intermediate Reciprocity both consistent, and neither entails the other
theorem not_felicitous_boundedDegree :
    ¬ Felicitous (Finset.univ : Finset (Fin 5)) (boundedDegree 2) := by
  have hT : nextTwo ∈ interpretation Finset.univ (.ful, .alternative) :=
    show StrongReciprocity (SymmGen nextTwo) Finset.univ by decide
  have hTdeg : nextTwo ∈ boundedDegree 2 := fun x ↦
    (Set.encard_le_encard (t := {x + 1, x + 2}) fun _ hy ↦ hy).trans <|
      (Set.encard_insert_le _ _).trans (by simp [one_add_one_eq_two])
  have hsar : circle ∉ interpretation (Finset.univ : Finset (Fin 5)) (.ful, .alternative) :=
    show ¬ StrongReciprocity (SymmGen circle) Finset.univ by decide
  have hlt : (· < ·) ∈ interpretation (Finset.univ : Finset (Fin 5)) (.ful, .alternative) :=
    show StrongReciprocity (SymmGen (· < ·)) Finset.univ by decide
  have hir : (· < ·) ∉ interpretation (Finset.univ : Finset (Fin 5)) (.lin, .plain) := fun h ↦
    absurd (IntermediateReciprocity.oneWayWeak (R := fun x y : Fin 5 ↦ x < y) h) (by decide)
  have hcirc : circle ∈ interpretation (Finset.univ : Finset (Fin 5)) (.lin, .plain) :=
    intermediate_circle (by omega)
  rintro ⟨_, ⟨⟨c, d⟩, rfl, hq⟩, hle⟩
  have hc₁ := hle ⟨(.ful, .alternative), rfl, nextTwo, hT, hTdeg⟩
  have hc₂ := hle ⟨(.lin, .plain), rfl, circle, hcirc, circle_mem_boundedDegree⟩
  cases c <;> cases d
  all_goals first
    | exact hsar (hc₁ (interpretation_antitone (by decide) hcirc))
    | exact hir (hc₂ hlt)
    | obtain ⟨R, h, hR⟩ := hq
      simpa using card_le_of_strongReciprocity hR h

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
    IsLeast (candidates X measles) (interpretation X (.lin, .alternative)) := by
  obtain ⟨s, hs⟩ := Finset.card_pos.1 (by omega : 0 < X.card)
  obtain ⟨R₀, hR₀, h₀⟩ :=
    exists_intermediateAlternative_measles (Finset.one_lt_card_iff_nontrivial.1 (by omega)) hs
  refine isLeast_of_isGreatest ⟨⟨R₀, h₀, hR₀⟩, ?_⟩
  have howr : ¬ (interpretation X (.tot, .plain) ∩ measles).Nonempty := fun ⟨R, h, hR⟩ ↦
    not_oneWayWeak_of_measles hR h
  rintro ⟨c, d⟩ h
  cases c <;> cases d
  all_goals first
    | decide
    | exact absurd (nonempty_inter_of_le (by decide) h) howr
    | exact absurd h fun ⟨R, h, hR⟩ ↦ not_strongAlternative_of_measles hR hX h

/-! ### Two members and an asymmetric relation (§6.3) -/

section Pair

variable [DecidableEq A]

/-- The non-linguistic information that the relation is asymmetric, as *on top of* and *taller
than* are. -/
def asymmetric : Set (A → A → Prop) :=
  {R | ∀ x y, R x y → ¬ R y x}

private theorem mem_pair (a b : A) {y : A} : y ∈ ({a, b} : Finset A) ↔ y = a ∨ y = b := by
  simp

theorem interpretation_pair_alternative {a b : A} (hab : a ≠ b) :
    interpretation {a, b} (.tot, .alternative) = interpretation {a, b} (.ful, .alternative) := by
  ext R
  show OneWayWeakReciprocity (SymmGen R) {a, b} ↔ StrongReciprocity (SymmGen R) {a, b}
  rw [oneWayWeakReciprocity_iff, strongReciprocity_iff, Finset.coe_pair, Set.pairwise_pair,
    imp_iff_right hab]
  refine and_congr_right fun _ ↦ ⟨fun h ↦ ?_, fun ⟨hab', hba'⟩ x hx ↦ ?_⟩
  · obtain ⟨y, hy, hne, hay⟩ := h a (by simp)
    obtain rfl := ((mem_pair _ _).1 hy).resolve_left (Ne.symm hne)
    exact ⟨hay, hay.symm⟩
  · obtain rfl | rfl := (mem_pair _ _).1 hx
    · exact ⟨b, by simp, hab, hab'⟩
    · exact ⟨a, by simp, Ne.symm hab, hba'⟩

-- (108)
theorem pair_isLeast {a b : A} (hab : a ≠ b) :
    IsLeast (candidates {a, b} asymmetric) (interpretation {a, b} (.tot, .alternative)) := by
  rw [interpretation_pair_alternative hab]
  refine isLeast_of_isGreatest ⟨⟨fun x y ↦ x = a ∧ y = b, ?_, ?_⟩, ?_⟩
  · show StrongReciprocity (SymmGen fun x y ↦ x = a ∧ y = b) {a, b}
    rw [strongReciprocity_iff, Finset.coe_pair, Set.pairwise_pair]
    exact ⟨Finset.one_lt_card_iff_nontrivial.1 (by rw [Finset.card_pair hab]; omega),
      fun _ ↦ ⟨.of_rel ⟨rfl, rfl⟩, .of_rel_symm ⟨rfl, rfl⟩⟩⟩
  · rintro x y ⟨rfl, rfl⟩ ⟨rfl, -⟩
    exact hab rfl
  have howr : ¬ (interpretation {a, b} (.tot, .plain) ∩ asymmetric).Nonempty := by
    rintro ⟨R, h, hR⟩
    have h' := (oneWayWeakReciprocity_iff (R := R) (X := {a, b})).1 h
    obtain ⟨y, hy, hne, hay⟩ := h'.2 a (by simp)
    obtain ⟨y', hy', hne', hby'⟩ := h'.2 b (by simp)
    obtain rfl := ((mem_pair _ _).1 hy).resolve_left (Ne.symm hne)
    obtain rfl := ((mem_pair _ _).1 hy').resolve_right (Ne.symm hne')
    exact hR _ _ hay hby'
  rintro ⟨c, d⟩ h
  cases c <;> cases d
  all_goals first
    | decide
    | exact absurd (nonempty_inter_of_le (by decide) h) howr

/-- The hypothesis cannot tell (108) from (109): with two members and an asymmetric relation it
makes both felicitous, but only (108) is. -/
theorem smh_mispredicts_taller {a b : A} (hab : a ≠ b) :
    (Felicitous {a, b} asymmetric ↔ Examples.ex108.judgment = .acceptable) ∧
      ¬ (Felicitous {a, b} asymmetric ↔ Examples.ex109.judgment = .acceptable) :=
  have h : Felicitous {a, b} asymmetric := ⟨_, pair_isLeast hab⟩
  ⟨iff_of_true h rfl, fun h' ↦ absurd (h'.1 h) (by decide)⟩

end Pair

/-! ### The staring pirates (§6.3) -/

/-- In the non-linguistic information for *staring at each other*, each stares at only one
other. -/
def singleValued : Set (A → A → Prop) :=
  {R | ∀ x y y', R x y → R x y' → y = y'}

theorem singleValued_subset_boundedDegree : singleValued ⊆ boundedDegree (A := A) 1 :=
  fun _ hR x ↦ Set.encard_le_one_iff.2 fun _ _ ↦ hR x _ _

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

/-- Four pirates, each staring at the next around a circle. -/
def stareRound (x y : Fin 4) : Prop := y = x + 1

/-- Four pirates in two pairs, each staring at the other of the pair. -/
def stareBack (x y : Fin 4) : Prop := x ≠ y ∧ x.val / 2 = y.val / 2

instance : DecidableRel stareBack := fun _ _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- With four pirates, the fewest for which the paper's argument excludes both quantifiers built
on `FUL`, the hypothesis makes *staring at each other* express Intermediate Reciprocity (110),
which a single-valued relation satisfies only without eye contact. -/
theorem pirates_isLeast :
    IsLeast (candidates (Finset.univ : Finset (Fin 4)) singleValued)
      (interpretation Finset.univ (.lin, .plain)) := by
  refine isLeast_of_isGreatest ⟨⟨stareRound, intermediate_of_succ (by omega) fun _ ↦ rfl,
    fun _ _ _ h h' ↦ h.trans h'.symm⟩, ?_⟩
  have hsar : ¬ (interpretation (Finset.univ : Finset (Fin 4)) (.ful, .alternative) ∩
      singleValued).Nonempty := fun ⟨_, h, hR⟩ ↦
    absurd (card_le_of_strongAlternative (singleValued_subset_boundedDegree hR) h) (by decide)
  rintro ⟨c, d⟩ h
  cases c <;> cases d
  all_goals first
    | decide
    | exact absurd (nonempty_inter_of_le (by decide) h) hsar

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
