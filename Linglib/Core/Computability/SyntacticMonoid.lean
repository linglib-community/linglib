/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins

[UPSTREAM] candidate: `Mathlib.Computability.SyntacticMonoid`, extending
`Mathlib.Computability.MyhillNerode`'s residual program to the two-sided
congruence.
-/
module

public import Mathlib.Computability.MyhillNerode
public import Mathlib.GroupTheory.Congruence.Basic
public import Mathlib.Data.Set.Finite.Range
public import Linglib.Core.Computability.TransitionMonoid
public import Linglib.Core.GroupTheory.Congruence.Hom
public import Linglib.Core.GroupTheory.Congruence.Syntactic
public import Linglib.Core.Algebra.Group.Subquotient
public import Linglib.Core.Logic.Function.FactorsThrough

/-!
# The syntactic monoid of a language

The *syntactic monoid* of a language `L : Language α` is the quotient of the free monoid
`FreeMonoid α` by the *syntactic congruence* `Con.syntactic` of `L`: two words are identified when
no two-sided context distinguishes them as `L`-members, `∀ x y, x ++ u ++ y ∈ L ↔ x ++ v ++ y ∈ L`.

It is the coarsest congruence saturating `L`, so the syntactic morphism factors through every
recognizing homomorphism, and the quotient is finite exactly when `L` is regular. This is the
two-sided refinement of the one-sided right-Nerode quotient `Language.leftQuotient`, carrying a
monoid structure rather than a bare set of states.

## Main definitions

* `Language.syntacticCon`: the syntactic congruence of `L` as a subset of the free monoid.
* `Language.SyntacticMonoid`: the quotient monoid `(syntacticCon L).Quotient`.
* `Language.toSyntacticMonoid`: the projection `FreeMonoid α →* L.SyntacticMonoid`.
* `Language.syntacticClass`: the syntactic class of a word.
* `Language.Recognizes`: `φ` recognizes `L` when `L` is a union of `φ`-fibres.
* `Language.rightQuotient`: the right-quotient dual of `Language.leftQuotient`.

## Main results

* `Language.recognizes_iff_ker_le`: a homomorphism recognizes `L` exactly when its kernel refines
  the syntactic congruence.
* `Language.syntacticMonoidEquivTransitionMonoid`: the syntactic monoid is the transition monoid
  of the minimal DFA `L.toDFA`.
* `Language.isRegular_iff_finite_syntacticMonoid`: a language is regular exactly when its
  syntactic monoid is finite.

## References

* [pin-mfa]
-/

@[expose] public section

namespace Language

variable {α : Type*} {L : Language α}

/-! ### The syntactic congruence and monoid -/

/-- The *syntactic congruence* of `L` is the syntactic congruence of its words in the free
monoid. -/
def syntacticCon (L : Language α) : Con (FreeMonoid α) := Con.syntactic (FreeMonoid.toList ⁻¹' L)

theorem syntacticCon_iff {u v : FreeMonoid α} :
    L.syntacticCon u v ↔ ∀ x y : List α, x ++ u.toList ++ y ∈ L ↔ x ++ v.toList ++ y ∈ L :=
  ⟨fun h x y ↦ by simpa using h (.ofList x) (.ofList y),
    fun h x y ↦ by simpa using h x.toList y.toList⟩

theorem syntacticCon_iff_leftQuotient {u v : FreeMonoid α} :
    L.syntacticCon u v ↔
      ∀ x, L.leftQuotient (x ++ u.toList) = L.leftQuotient (x ++ v.toList) :=
  forall_congr' fun _ ↦ Set.ext_iff.symm

/-- The *syntactic monoid* of `L` is the quotient of `FreeMonoid α` by the syntactic congruence. -/
abbrev SyntacticMonoid (L : Language α) := (syntacticCon L).Quotient

/-- The *syntactic morphism* of `L` projects `FreeMonoid α` onto the syntactic monoid. -/
def toSyntacticMonoid (L : Language α) : FreeMonoid α →* L.SyntacticMonoid := (syntacticCon L).mk'

theorem toSyntacticMonoid_eq_iff {u v : FreeMonoid α} :
    L.toSyntacticMonoid u = L.toSyntacticMonoid v ↔ L.syntacticCon u v :=
  Con.eq _

theorem ker_toSyntacticMonoid (L : Language α) : Con.ker L.toSyntacticMonoid = L.syntacticCon :=
  Con.mk'_ker _

/-! ### The syntactic class of a word -/

/-- The *syntactic class* of a word `w` is its image in the syntactic monoid. -/
def syntacticClass (L : Language α) (w : List α) : L.SyntacticMonoid :=
  L.toSyntacticMonoid (FreeMonoid.ofList w)

@[simp] theorem syntacticClass_nil (L : Language α) : L.syntacticClass [] = 1 := map_one _

@[simp] theorem syntacticClass_append (L : Language α) (u v : List α) :
    L.syntacticClass (u ++ v) = L.syntacticClass u * L.syntacticClass v := map_mul _ _ _

theorem syntacticClass_flatten (L : Language α) (ws : List (List α)) :
    L.syntacticClass ws.flatten = (ws.map L.syntacticClass).prod := by
  induction ws <;> simp [*]

theorem syntacticClass_surjective (L : Language α) : Function.Surjective L.syntacticClass :=
  Con.mk'_surjective.comp FreeMonoid.ofList.surjective

theorem syntacticClass_eq_iff {u v : List α} :
    L.syntacticClass u = L.syntacticClass v ↔ ∀ x y : List α, x ++ u ++ y ∈ L ↔ x ++ v ++ y ∈ L :=
  toSyntacticMonoid_eq_iff.trans syntacticCon_iff

theorem mem_iff_of_syntacticClass_eq {u v : List α}
    (h : L.syntacticClass u = L.syntacticClass v) : u ∈ L ↔ v ∈ L :=
  Con.mem_iff_of_syntactic (M := FreeMonoid α) (toSyntacticMonoid_eq_iff.mp h)

theorem syntacticClass_reverse_eq_iff {u v : List α} :
    L.reverse.syntacticClass u = L.reverse.syntacticClass v ↔
      L.syntacticClass u.reverse = L.syntacticClass v.reverse := by
  rw [syntacticClass_eq_iff, syntacticClass_eq_iff]
  refine ⟨fun h x y ↦ ?_, fun h x y ↦ ?_⟩ <;> simpa using h y.reverse x.reverse

/-! ### Universal property -/

/-- `φ` *recognizes* `L` when `L` is the `FreeMonoid.ofList`-pullback of a union of
`φ`-fibres. -/
def Recognizes {M : Type*} [Monoid M] (φ : FreeMonoid α →* M) (L : Language α) : Prop :=
  ∃ S : Set M, L = FreeMonoid.ofList ⁻¹' (φ ⁻¹' S)

section

variable {M : Type*} [Monoid M] {φ : FreeMonoid α →* M}

theorem recognizes_iff_ker_le : Recognizes φ L ↔ Con.ker φ ≤ syntacticCon L :=
  (Con.ker_le_syntactic_iff (S := FreeMonoid.toList ⁻¹' L)).symm

theorem ker_le_syntacticCon_of_recognizes (hrec : Recognizes φ L) :
    Con.ker φ ≤ syntacticCon L :=
  recognizes_iff_ker_le.1 hrec

theorem Recognizes.comap {β : Type*} (hrec : Recognizes φ L) (ψ : FreeMonoid β →* FreeMonoid α) :
    Recognizes (φ.comp ψ) {w : List β | ψ (FreeMonoid.ofList w) ∈ L} := by
  obtain ⟨S, rfl⟩ := hrec
  exact ⟨S, rfl⟩

theorem Recognizes.syntacticMonoid_isSubquotient (hrec : Recognizes φ L) :
    Monoid.IsSubquotient L.SyntacticMonoid M :=
  ((Monoid.IsSubquotient.of_surjective _ <| Con.lift_surjective_of_surjective
      ((ker_le_syntacticCon_of_recognizes hrec).trans L.ker_toSyntacticMonoid.ge)
      L.syntacticCon.mk'_surjective).trans (Con.quotientKerEquivRange φ).isSubquotient).trans
    (Submonoid.isSubquotient _)

end

theorem recognizes_toSyntacticMonoid (L : Language α) : Recognizes L.toSyntacticMonoid L :=
  recognizes_iff_ker_le.2 L.ker_toSyntacticMonoid.le

/-! ### Connection to the minimal DFA -/

theorem recognizes_transitionHom {σ : Type*} (M : DFA α σ) :
    Recognizes M.transitionHom M.accepts :=
  ⟨{t | t.unop M.start ∈ M.accept}, rfl⟩

@[simp] theorem evalFrom_toDFA (s : Set.range L.leftQuotient) (w : List α) :
    (L.toDFA.evalFrom s w).val = s.val.leftQuotient w := by
  induction w using List.reverseRecOn <;> simp_all [leftQuotient_append]

theorem ker_transitionHom_toDFA_iff {u v : FreeMonoid α} :
    Con.ker L.toDFA.transitionHom u v ↔
      ∀ x, L.leftQuotient (x ++ u.toList) = L.leftQuotient (x ++ v.toList) := by
  simp [DFA.transitionHom_eq_iff, Subtype.ext_iff, ← leftQuotient_append]

theorem syntacticCon_eq_ker_transitionHom : L.syntacticCon = Con.ker L.toDFA.transitionHom :=
  Con.ext fun _ _ ↦ syntacticCon_iff_leftQuotient.trans ker_transitionHom_toDFA_iff.symm

/-- The syntactic monoid of `L` is the transition monoid of its minimal DFA. -/
noncomputable def syntacticMonoidEquivTransitionMonoid (L : Language α) :
    L.SyntacticMonoid ≃* L.toDFA.transitionMonoid :=
  (Con.congr (.refl _) syntacticCon_eq_ker_transitionHom).trans (Con.quotientKerEquivRange _)

/-! ### Myhill–Nerode -/

theorem IsRegular.finite_syntacticMonoid (h : L.IsRegular) : Finite L.SyntacticMonoid :=
  have := h.finite_range_leftQuotient.to_subtype
  .of_equiv _ L.syntacticMonoidEquivTransitionMonoid.symm.toEquiv

theorem IsRegular.of_finite_syntacticMonoid (h : Finite L.SyntacticMonoid) : L.IsRegular :=
  .of_finite_range_leftQuotient <| Function.FactorsThrough.finite_range
    (fun _ _ e ↦ Set.ext (syntacticClass_eq_iff.mp e [] ·) :
      Function.FactorsThrough L.leftQuotient L.syntacticClass) (Set.toFinite _)

/-- `L` is regular iff `L.SyntacticMonoid` is finite. -/
theorem isRegular_iff_finite_syntacticMonoid : L.IsRegular ↔ Finite L.SyntacticMonoid :=
  ⟨IsRegular.finite_syntacticMonoid, IsRegular.of_finite_syntacticMonoid⟩

/-! ### Boolean combinations -/

theorem syntacticCon_compl : Lᶜ.syntacticCon = L.syntacticCon := Con.syntactic_compl

theorem inf_syntacticCon_le_syntacticCon_inf {L' : Language α} :
    L.syntacticCon ⊓ L'.syntacticCon ≤ (L ⊓ L').syntacticCon :=
  Con.inf_le_syntactic_inter

theorem inf_syntacticCon_le_syntacticCon_sup {L' : Language α} :
    L.syntacticCon ⊓ L'.syntacticCon ≤ (L ⊔ L').syntacticCon :=
  Con.inf_le_syntactic_union

/-- The syntactic monoid of `L` is trivial exactly when `L` is empty or full. -/
theorem subsingleton_syntacticMonoid_iff : Subsingleton L.SyntacticMonoid ↔ L = ⊥ ∨ L = ⊤ := by
  refine ⟨fun _ ↦ ?_, ?_⟩
  · have h (w : List α) : w ∈ L ↔ [] ∈ L := mem_iff_of_syntacticClass_eq (Subsingleton.elim _ _)
    by_cases hnil : [] ∈ L
    exacts [.inr (eq_top_iff.2 fun w _ ↦ (h w).2 hnil),
      .inl (eq_bot_iff.2 fun w hw ↦ hnil ((h w).1 hw))]
  · have h (hL : L = ⊥ ∨ L = ⊤) (u v : List α) : L.syntacticClass u = L.syntacticClass v :=
      syntacticClass_eq_iff.2 fun _ _ ↦ by rcases hL with rfl | rfl <;> exact Iff.rfl
    exact fun hL ↦ ⟨fun a b ↦ by
      obtain ⟨u, rfl⟩ := L.syntacticClass_surjective a
      obtain ⟨v, rfl⟩ := L.syntacticClass_surjective b
      exact h hL u v⟩

/-! ### Quotients -/

/-- The *right quotient* of `L` by `u` is the set of prefixes `w` such that `w ++ u` is in `L`. -/
def rightQuotient (L : Language α) (u : List α) : Language α := {w | w ++ u ∈ L}

@[simp] theorem mem_rightQuotient {u w : List α} :
    w ∈ L.rightQuotient u ↔ w ++ u ∈ L := Iff.rfl

@[simp] theorem rightQuotient_nil (L : Language α) : L.rightQuotient [] = L := by
  ext w; simp

theorem rightQuotient_append (L : Language α) (u v : List α) :
    L.rightQuotient (u ++ v) = (L.rightQuotient v).rightQuotient u := by
  ext w; simp [List.append_assoc]

theorem rightQuotient_eq_reverse_leftQuotient (L : Language α) (u : List α) :
    L.rightQuotient u = (L.reverse.leftQuotient u.reverse).reverse := by
  ext w; simp [List.reverse_append]

theorem syntacticCon_le_leftQuotient (L : Language α) (u : List α) :
    L.syntacticCon ≤ (L.leftQuotient u).syntacticCon :=
  Con.syntactic_le_syntactic_preimage_mul_left (FreeMonoid.ofList u)

theorem syntacticCon_le_rightQuotient (L : Language α) (u : List α) :
    L.syntacticCon ≤ (L.rightQuotient u).syntacticCon :=
  Con.syntactic_le_syntactic_preimage_mul_right (FreeMonoid.ofList u)

end Language
