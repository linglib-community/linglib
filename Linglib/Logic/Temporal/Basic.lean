/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Logic.Temporal.Defs
public import Linglib.Logic.Modal.Basic

/-!
# T × W tense-modal logic: the modal algebra of satisfaction

This file states the satisfaction clauses of T × W logic and of its dual operators, and proves
the hierarchy `box ⊃ N ⊃ A`. Historical necessity `N` is necessity along historical equivalence,
and `box` is necessity along the universal relation. Both are S5 by modal correspondence, since
historical equivalence is reflexive, symmetric and transitive.

## Main results

* `sat_neg`, `sat_and`, `sat_G`, `sat_H`, `sat_N`, `sat_box`: the satisfaction clauses.
* `sat_M`: historical possibility is `∃` over historical alternatives.
* `sat_box_imp_N`, `sat_N_imp_self`, `sat_box_imp_self`: the hierarchy `box ⊃ N ⊃ A`.
* `sat_N_imp_N_N`, `sat_M_imp_N_M`, `sat_box_imp_box_box`, `sat_dia_imp_box_dia`: `N` and `box`
  are S5.
* `Fut_adjoint_H`, `Pst_adjoint_G`: the tense adjunctions.

## References

* [thomason-1984]
* [von-kutschera-1997]
* [gallin-1975]
* [burgess-1984]
-/

@[expose] public section


namespace Temporal.TWFrame

variable {T : Type*} {World : Type*} {Atom : Type*} [Preorder T]
  (F : TWFrame World T) (V : Atom → T → World → Prop)

open ModalLogic (box_T box_four box_restrict box_isIndicial IsIndicial)
open scoped ModalLogic

/-! ### Historical equivalence as accessibility -/

instance (t : T) : (F.alt t).IsRefl := ⟨(F.sim t).iseqv.refl⟩

instance (t : T) : (F.alt t).IsSymm := ⟨fun _ _ ↦ (F.sim t).iseqv.symm⟩

instance (t : T) : (F.alt t).IsTrans := ⟨fun _ _ _ ↦ (F.sim t).iseqv.trans⟩

/-! ### Satisfaction clauses -/

@[simp] theorem sat_atom (p : Atom) (t : T) (w : World) :
    F.sat V (.atom p) t w ↔ V p t w := Iff.rfl

@[simp] theorem sat_neg (a : OForm Atom) (t : T) (w : World) :
    F.sat V (.neg a) t w ↔ ¬ F.sat V a t w := Iff.rfl

@[simp] theorem sat_and (a b : OForm Atom) (t : T) (w : World) :
    F.sat V (.and a b) t w ↔ F.sat V a t w ∧ F.sat V b t w := Iff.rfl

@[simp] theorem sat_G (a : OForm Atom) (t : T) (w : World) :
    F.sat V (.G a) t w ↔ ∀ t', t < t' → F.sat V a t' w := Iff.rfl

@[simp] theorem sat_H (a : OForm Atom) (t : T) (w : World) :
    F.sat V (.H a) t w ↔ ∀ t', t' < t → F.sat V a t' w := Iff.rfl

@[simp] theorem sat_N (a : OForm Atom) (t : T) (w : World) :
    F.sat V (.N a) t w ↔ ∀ w', F.sim t w w' → F.sat V a t w' := Iff.rfl

@[simp] theorem sat_box (a : OForm Atom) (t : T) (w : World) :
    F.sat V (.box a) t w ↔ ∀ w', F.sat V a t w' :=
  ⟨fun h w' => h w' trivial, fun h w' _ => h w'⟩

/-! ### Dual operators -/

@[simp] theorem sat_M (a : OForm Atom) (t : T) (w : World) :
    F.sat V a.M t w ↔ ∃ w', F.sim t w w' ∧ F.sat V a t w' := by
  simp only [OForm.M, sat_neg, sat_N, not_forall, not_not, exists_prop]

@[simp] theorem sat_dia (a : OForm Atom) (t : T) (w : World) :
    F.sat V a.dia t w ↔ ∃ w', F.sat V a t w' := by
  simp only [OForm.dia, sat_neg, sat_box, not_forall, not_not]

@[simp] theorem sat_Fut (a : OForm Atom) (t : T) (w : World) :
    F.sat V a.Fut t w ↔ ∃ t', t < t' ∧ F.sat V a t' w := by
  simp only [OForm.Fut, sat_neg, sat_G, not_forall, not_not, exists_prop]

@[simp] theorem sat_Pst (a : OForm Atom) (t : T) (w : World) :
    F.sat V a.Pst t w ↔ ∃ t', t' < t ∧ F.sat V a t' w := by
  simp only [OForm.Pst, sat_neg, sat_H, not_forall, not_not, exists_prop]

/-! ### The modality hierarchy `box ⊃ N ⊃ A` and S5, from modal correspondence

`N` and `box` are necessities along relations, so the hierarchy and the S5 axioms follow from
modal correspondence. `box ⊃ N` holds because the universal relation contains historical
equivalence (`box_restrict`). The `T` axioms follow from reflexivity (`box_T`), the `4` axioms from
transitivity (`box_four`), and the `5` axioms from symmetry and transitivity. -/

theorem sat_box_imp_N {a : OForm Atom} {t : T} {w : World} :
    F.sat V (.box a) t w → F.sat V (.N a) t w :=
  fun h => box_restrict _ (Set.subset_univ _) _ h

theorem sat_N_imp_self {a : OForm Atom} {t : T} {w : World} :
    F.sat V (.N a) t w → F.sat V a t w :=
  fun h ↦ box_T h

theorem sat_box_imp_self {a : OForm Atom} {t : T} {w : World} :
    F.sat V (.box a) t w → F.sat V a t w :=
  fun h => box_T h

theorem sat_N_imp_N_N {a : OForm Atom} {t : T} {w : World} :
    F.sat V (.N a) t w → F.sat V (.N (.N a)) t w :=
  fun h ↦ box_four h

theorem sat_box_imp_box_box {a : OForm Atom} {t : T} {w : World} :
    F.sat V (.box a) t w → F.sat V (.box (.box a)) t w :=
  fun h => box_four h

theorem sat_M_imp_N_M {a : OForm Atom} {t : T} {w : World} :
    F.sat V a.M t w → F.sat V a.M.N t w := by
  intro h w' hww'
  rw [sat_M] at h ⊢
  obtain ⟨w₀, hww₀, ha⟩ := h
  exact ⟨w₀, (F.sim t).iseqv.trans ((F.sim t).iseqv.symm hww') hww₀, ha⟩

theorem sat_dia_imp_box_dia {a : OForm Atom} {t : T} {w : World} :
    F.sat V a.dia t w → F.sat V a.dia.box t w := by
  intro h w' _
  rw [sat_dia] at h ⊢
  obtain ⟨w₀, ha⟩ := h
  exact ⟨w₀, ha⟩

/-- Historical necessity `N`, necessity along historical equivalence, is an indicial modality in
the sense of [gallin-1975]. -/
theorem N_isIndicial (t : T) : IsIndicial □[F.alt t] :=
  box_isIndicial _

/-! ### The temporal adjunctions `Fut ⊣ H`, `Pst ⊣ G`

The tense operators are Galois-adjoint on each model's entailment preorder ([burgess-1984]): `Fut`
(future `∃`) is left adjoint to `H` (past `∀`), and `Pst` (past `∃`) to `G` (future `∀`). -/

theorem Fut_adjoint_H (a b : OForm Atom) :
    F.entails V a.Fut b ↔ F.entails V a (.H b) := by
  simp only [entails, sat_Fut, sat_H]
  constructor
  · intro h t w hat t' ht
    exact h t' w ⟨t, ht, hat⟩
  · rintro h t w ⟨u, htu, hau⟩
    exact h u w hau t htu

theorem Pst_adjoint_G (a b : OForm Atom) :
    F.entails V a.Pst b ↔ F.entails V a (.G b) := by
  simp only [entails, sat_Pst, sat_G]
  constructor
  · intro h t w hat t' ht
    exact h t' w ⟨t, ht, hat⟩
  · rintro h t w ⟨u, hut, hau⟩
    exact h u w hau t hut

end Temporal.TWFrame
