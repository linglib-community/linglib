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
public import Linglib.Core.Algebra.Group.Subquotient
public import Linglib.Core.Logic.Function.FactorsThrough

/-!
# The syntactic monoid of a language

The *syntactic monoid* of a language `L : Language α` is the quotient of the free monoid
`FreeMonoid α` by the *syntactic congruence*: two words are identified when no two-sided context
distinguishes them as `L`-members, `∀ x y, x ++ u ++ y ∈ L ↔ x ++ v ++ y ∈ L`.

It is the coarsest congruence saturating `L`, so the syntactic morphism factors through every
recognizing homomorphism, and the quotient is finite exactly when `L` is regular. This is the
two-sided refinement of the one-sided right-Nerode quotient `Language.leftQuotient`, carrying a
monoid structure rather than a bare set of states.

## Main definitions

* `Language.syntacticCon`: the syntactic congruence, two-sided context equivalence.
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

/-! ### Syntactic equivalence -/

/-- Two words are *syntactically equivalent* for `L` when no two-sided context distinguishes
them as `L`-members. -/
def SyntacticEquiv (L : Language α) (u v : List α) : Prop :=
  ∀ x y : List α, x ++ u ++ y ∈ L ↔ x ++ v ++ y ∈ L

namespace SyntacticEquiv

variable {u u' v v' w : List α}

@[refl] theorem refl (u : List α) : L.SyntacticEquiv u u := fun _ _ ↦ Iff.rfl

@[symm] theorem symm (h : L.SyntacticEquiv u v) : L.SyntacticEquiv v u :=
  fun x y ↦ (h x y).symm

@[trans] theorem trans (h : L.SyntacticEquiv u v) (h' : L.SyntacticEquiv v w) :
    L.SyntacticEquiv u w := fun x y ↦ (h x y).trans (h' x y)

theorem append (h : L.SyntacticEquiv u u') (h' : L.SyntacticEquiv v v') :
    L.SyntacticEquiv (u ++ v) (u' ++ v') := by grind [SyntacticEquiv]

theorem mem_iff (h : L.SyntacticEquiv u v) : u ∈ L ↔ v ∈ L := by
  simpa using h [] []

theorem leftQuotient_eq (h : L.SyntacticEquiv u v) : L.leftQuotient u = L.leftQuotient v :=
  Set.ext (h [])

theorem compl_iff : Lᶜ.SyntacticEquiv u v ↔ L.SyntacticEquiv u v :=
  forall_congr' fun _ ↦ forall_congr' fun _ ↦ not_iff_not

theorem reverse_iff :
    L.reverse.SyntacticEquiv u v ↔ L.SyntacticEquiv u.reverse v.reverse := by
  refine ⟨fun h x y ↦ ?_, fun h x y ↦ ?_⟩ <;> simpa using h y.reverse x.reverse

end SyntacticEquiv

/-! ### The syntactic congruence and monoid -/

/-- The *syntactic congruence* of `L` identifies two words when no two-sided context distinguishes
them as `L`-members. -/
def syntacticCon (L : Language α) : Con (FreeMonoid α) where
  r u v := L.SyntacticEquiv u.toList v.toList
  iseqv := ⟨fun _ ↦ .refl _, .symm, .trans⟩
  mul' hab hcd := hab.append hcd

theorem syntacticCon_iff {u v : FreeMonoid α} :
    L.syntacticCon u v ↔ L.SyntacticEquiv u.toList v.toList := Iff.rfl

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
    L.syntacticClass u = L.syntacticClass v ↔ L.SyntacticEquiv u v :=
  toSyntacticMonoid_eq_iff

theorem mem_iff_of_syntacticClass_eq {u v : List α}
    (h : L.syntacticClass u = L.syntacticClass v) : u ∈ L ↔ v ∈ L :=
  (syntacticClass_eq_iff.mp h).mem_iff

theorem syntacticClass_reverse_eq_iff {u v : List α} :
    L.reverse.syntacticClass u = L.reverse.syntacticClass v ↔
      L.syntacticClass u.reverse = L.syntacticClass v.reverse := by
  simp [syntacticClass_eq_iff, SyntacticEquiv.reverse_iff]

/-! ### Universal property -/

/-- `φ` *recognizes* `L` when `L` is the `FreeMonoid.ofList`-pullback of a union of
`φ`-fibres. -/
def Recognizes {M : Type*} [Monoid M] (φ : FreeMonoid α →* M) (L : Language α) : Prop :=
  ∃ S : Set M, L = FreeMonoid.ofList ⁻¹' (φ ⁻¹' S)

section

variable {M : Type*} [Monoid M] {φ : FreeMonoid α →* M}

theorem ker_le_syntacticCon_of_recognizes (hrec : Recognizes φ L) :
    Con.ker φ ≤ syntacticCon L := by
  obtain ⟨S, rfl⟩ := hrec
  intro u v huv x y
  show φ (.ofList (x ++ u.toList ++ y)) ∈ S ↔ φ (.ofList (x ++ v.toList ++ y)) ∈ S
  simp [FreeMonoid.ofList_append, FreeMonoid.ofList_toList, map_mul, Con.ker_apply.mp huv]

theorem recognizes_of_ker_le (h : Con.ker φ ≤ syntacticCon L) :
    Recognizes φ L :=
  ⟨φ '' (FreeMonoid.ofList '' L), Set.ext fun w ↦
    ⟨fun hw ↦ ⟨.ofList w, ⟨w, hw, rfl⟩, rfl⟩, fun ⟨_, ⟨u, hu, rfl⟩, hφ⟩ ↦
      (SyntacticEquiv.mem_iff (h (Con.ker_apply.mpr hφ))).mp hu⟩⟩

theorem recognizes_iff_ker_le :
    Recognizes φ L ↔ Con.ker φ ≤ syntacticCon L :=
  ⟨ker_le_syntacticCon_of_recognizes, recognizes_of_ker_le⟩

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
  recognizes_of_ker_le L.ker_toSyntacticMonoid.le

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
    (fun _ _ e ↦ (syntacticClass_eq_iff.mp e).leftQuotient_eq) (Set.toFinite _)

/-- `L` is regular iff `L.SyntacticMonoid` is finite. -/
theorem isRegular_iff_finite_syntacticMonoid : L.IsRegular ↔ Finite L.SyntacticMonoid :=
  ⟨IsRegular.finite_syntacticMonoid, IsRegular.of_finite_syntacticMonoid⟩

/-! ### Boolean combinations -/

theorem syntacticCon_compl : Lᶜ.syntacticCon = L.syntacticCon :=
  Con.ext fun _ _ ↦ SyntacticEquiv.compl_iff

theorem inf_syntacticCon_le_syntacticCon_inf {L' : Language α} :
    L.syntacticCon ⊓ L'.syntacticCon ≤ (L ⊓ L').syntacticCon :=
  fun {_ _} huv x y ↦ and_congr (huv.1 x y) (huv.2 x y)

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
    L.syntacticCon ≤ (L.leftQuotient u).syntacticCon := fun {p q} h x y ↦ by
  simpa [List.append_assoc] using h (u ++ x) y

theorem syntacticCon_le_rightQuotient (L : Language α) (u : List α) :
    L.syntacticCon ≤ (L.rightQuotient u).syntacticCon := fun {p q} h x y ↦ by
  simpa [List.append_assoc] using h x (y ++ u)

end Language
