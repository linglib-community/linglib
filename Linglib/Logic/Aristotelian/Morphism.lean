module

public import Linglib.Core.Order.BooleanSubalgebra
public import Linglib.Logic.Aristotelian.Basic

/-!
# Isomorphisms of Aristotelian diagrams

An *Aristotelian diagram* is a fragment of a Boolean algebra, here an indexed family
`φ : ι → α`. Demey and Smessaert call a bijection of corners an *Aristotelian isomorphism* when
it preserves and reflects the four Aristotelian relations, and a *Boolean isomorphism* when it
extends to an order isomorphism of the Boolean closures. Every Boolean isomorphism is an
Aristotelian one but not conversely, as their Keynes–Johnson octagons show. Aristotelian
isomorphisms form a groupoid, the core of De Klerck, Vignero and Demey's category of
Aristotelian diagrams. Demey and Smessaert's bitstring semantics sends each element of the
closure of a diagram to the set of its minterms below it, and carries the diagram to an
Aristotelian isomorphic diagram of bitstrings.

## Main definitions

* `AristotelianIso`, with `refl`, `symm` and `trans`.
* `BooleanIso`, with `refl`, `symm` and `trans`.

## Main results

* `BooleanIso.toAristotelianIso`: every Boolean isomorphism is an Aristotelian isomorphism.
* `BooleanIso.ofInjective`: a diagram is Boolean isomorphic to its image along an injective
  homomorphism.
* `BooleanIso.ofMintermEqBot`: a corner bijection is a Boolean isomorphism when the minterms of
  the two diagrams vanish at the same polarity assignments.
* `AristotelianIso.toSetOfMinterms`: a diagram and its bitstrings are Aristotelian isomorphic.

## Implementation notes

The family `φ : ι → α` stands in for the paper's set `F ⊆ α`, and a corner bijection is a
bijection of index types. `AristotelianIso` asks for `Disjoint`, `Codisjoint` and `<` to be
preserved and reflected. This is equivalent to asking it of the four relations, since each of
`IsCompl`, `IsContrary`, `IsSubcontrary` and `<` is a Boolean combination of the three, and
conversely (`disjoint_iff_isCompl_or_isContrary`, `codisjoint_iff_isCompl_or_isSubcontrary`).

The bitstring semantics is Boolean-algebra theory and lives in `Core/Order`. Demey and
Smessaert's partition induced by a fragment (2018, Definition 5; 2024, Definition 3) is
`Finpartition.minterms`, with anchor formulas `minterm`; their Lemma 3 is `disjoint_minterm`
and `sup_minterm`, Lemma 4 `Finpartition.minterms_sumElim`, Lemma 6
`BooleanSubalgebra.minterm_le_or_le_compl`, Lemma 7
`BooleanSubalgebra.le_iff_forall_mem_minterms`, Lemma 9 `BooleanSubalgebra.isAtom_iff_mem_minterms`,
and Theorem 1 `BooleanSubalgebra.toSetOfMinterms` with `BooleanSubalgebra.card_closure`. They
number the minterms and write a set of them as a string of bits; `toSetOfMinterms` keeps the set.
Their Theorem 2, proved there from Theorem 1 through the Boolean-to-Aristotelian lemma, is
proved here directly.

## References

* [demey-smessaert-2018]
* [demey-smessaert-2024]
* [deklerck-vignero-demey-2024]
-/

@[expose] public section

namespace Aristotelian

variable {ι ι' ι'' α α' α'' : Type*} [BooleanAlgebra α] [BooleanAlgebra α'] [BooleanAlgebra α'']
  {φ : ι → α} {φ' : ι' → α'} {φ'' : ι'' → α''}

open BooleanSubalgebra
open Equiv (toFun_as_coe apply_symm_apply)

/-- An **Aristotelian isomorphism** is a corner bijection preserving and reflecting `Disjoint`,
`Codisjoint` and `<`, and hence the four Aristotelian relations (`map_isCompl` and
siblings). -/
structure AristotelianIso (φ : ι → α) (φ' : ι' → α') extends ι ≃ ι' where
  /-- Joint inconsistency (`⊓ = ⊥`) is preserved and reflected. -/
  map_disjoint : ∀ i j, Disjoint (φ i) (φ j) ↔ Disjoint (φ' (toFun i)) (φ' (toFun j))
  /-- Joint exhaustiveness (`⊔ = ⊤`) is preserved and reflected. -/
  map_codisjoint : ∀ i j, Codisjoint (φ i) (φ j) ↔ Codisjoint (φ' (toFun i)) (φ' (toFun j))
  /-- Subalternation (`<`) is preserved and reflected. -/
  map_lt : ∀ i j, φ i < φ j ↔ φ' (toFun i) < φ' (toFun j)

namespace AristotelianIso

instance : EquivLike (AristotelianIso φ φ') ι ι' where
  coe e := e.toFun
  inv e := e.invFun
  left_inv e := e.left_inv
  right_inv e := e.right_inv
  coe_injective' e e' h _ := by
    obtain ⟨e, _, _, _⟩ := e; obtain ⟨e', _, _, _⟩ := e'; congr; exact Equiv.coe_fn_injective h

@[simp] theorem coe_fn_toEquiv (e : AristotelianIso φ φ') : (e.toEquiv : ι → ι') = e := rfl

@[ext]
theorem ext {e e' : AristotelianIso φ φ'} (h : ∀ i, e i = e' i) : e = e' := DFunLike.ext _ _ h

/-- The identity Aristotelian isomorphism. -/
@[refl] protected def refl (φ : ι → α) : AristotelianIso φ φ where
  toEquiv := Equiv.refl ι
  map_disjoint _ _ := Iff.rfl
  map_codisjoint _ _ := Iff.rfl
  map_lt _ _ := Iff.rfl

/-- The inverse Aristotelian isomorphism. -/
@[symm] protected def symm (e : AristotelianIso φ φ') : AristotelianIso φ' φ where
  toEquiv := e.toEquiv.symm
  map_disjoint i j := by
    simpa only [toFun_as_coe, apply_symm_apply]
      using (e.map_disjoint (e.toEquiv.symm i) (e.toEquiv.symm j)).symm
  map_codisjoint i j := by
    simpa only [toFun_as_coe, apply_symm_apply]
      using (e.map_codisjoint (e.toEquiv.symm i) (e.toEquiv.symm j)).symm
  map_lt i j := by
    simpa only [toFun_as_coe, apply_symm_apply]
      using (e.map_lt (e.toEquiv.symm i) (e.toEquiv.symm j)).symm

/-- Composition of Aristotelian isomorphisms. -/
@[trans] protected def trans (e : AristotelianIso φ φ') (e' : AristotelianIso φ' φ'') :
    AristotelianIso φ φ'' where
  toEquiv := e.toEquiv.trans e'.toEquiv
  map_disjoint i j := (e.map_disjoint i j).trans (e'.map_disjoint _ _)
  map_codisjoint i j := (e.map_codisjoint i j).trans (e'.map_codisjoint _ _)
  map_lt i j := (e.map_lt i j).trans (e'.map_lt _ _)

theorem map_isCompl (e : AristotelianIso φ φ') (i j : ι) :
    IsCompl (φ i) (φ j) ↔ IsCompl (φ' (e i)) (φ' (e j)) := by
  simp only [isCompl_iff, e.map_disjoint, e.map_codisjoint, toFun_as_coe, coe_fn_toEquiv]

theorem map_isContrary (e : AristotelianIso φ φ') (i j : ι) :
    IsContrary (φ i) (φ j) ↔ IsContrary (φ' (e i)) (φ' (e j)) := by
  simp only [IsContrary, e.map_disjoint, e.map_codisjoint, toFun_as_coe, coe_fn_toEquiv]

theorem map_isSubcontrary (e : AristotelianIso φ φ') (i j : ι) :
    IsSubcontrary (φ i) (φ j) ↔ IsSubcontrary (φ' (e i)) (φ' (e j)) := by
  simp only [IsSubcontrary, e.map_disjoint, e.map_codisjoint, toFun_as_coe, coe_fn_toEquiv]

end AristotelianIso

/-! ### Boolean isomorphism (Definition 7) and the nesting -/

/-- The `i`-th corner of a diagram, viewed inside its Boolean closure. -/
def corner (φ : ι → α) (i : ι) : closure (Set.range φ) :=
  ⟨φ i, subset_closure (Set.mem_range_self i)⟩

@[simp, norm_cast]
theorem coe_corner (φ : ι → α) (i : ι) : (corner φ i : α) = φ i := rfl

/-- A **Boolean isomorphism** is a corner bijection that extends to an order isomorphism of the
Boolean closures. -/
@[ext]
structure BooleanIso (φ : ι → α) (φ' : ι' → α') where
  /-- The underlying corner bijection. -/
  toEquiv : ι ≃ ι'
  /-- The order-isomorphism of Boolean closures extending it. -/
  closureIso : closure (Set.range φ) ≃o closure (Set.range φ')
  /-- `closureIso` carries corners to corners. -/
  extends_corners : ∀ i, closureIso (corner φ i) = corner φ' (toEquiv i)

namespace BooleanIso

/-- The identity Boolean isomorphism. -/
@[refl] protected def refl (φ : ι → α) : BooleanIso φ φ :=
  ⟨Equiv.refl ι, OrderIso.refl _, fun _ ↦ rfl⟩

/-- The inverse Boolean isomorphism. -/
@[symm] protected def symm (e : BooleanIso φ φ') : BooleanIso φ' φ where
  toEquiv := e.toEquiv.symm
  closureIso := e.closureIso.symm
  extends_corners i := by rw [e.closureIso.symm_apply_eq, e.extends_corners, apply_symm_apply]

/-- Composition of Boolean isomorphisms. -/
@[trans] protected def trans (e : BooleanIso φ φ') (e' : BooleanIso φ' φ'') : BooleanIso φ φ'' where
  toEquiv := e.toEquiv.trans e'.toEquiv
  closureIso := e.closureIso.trans e'.closureIso
  extends_corners i := by
    simp only [OrderIso.trans_apply, e.extends_corners, e'.extends_corners, Equiv.trans_apply]

/-- A diagram is Boolean isomorphic to its image along an injective homomorphism. -/
noncomputable def ofInjective (g : BoundedLatticeHom α α') (hg : Function.Injective g) :
    BooleanIso φ (g ∘ φ) where
  toEquiv := .refl ι
  closureIso := (orderIsoMapOfInjective _ hg).trans <|
    Set.orderIsoOfEq _ _ (by rw [map_closure, ← Set.range_comp])
  extends_corners _ := rfl

/-- A corner bijection is a Boolean isomorphism when the minterms of the two diagrams, matched
along it, vanish together. -/
noncomputable def ofMintermEqBot [Fintype ι] [DecidableEq ι] [DecidableEq α] [DecidableEq α']
    (e : ι ≃ ι') (h : ∀ σ, minterm φ σ = ⊥ ↔ minterm (φ' ∘ e) σ = ⊥) : BooleanIso φ φ' where
  toEquiv := e
  closureIso := (closureOrderIsoOfMintermEqBot h).trans <|
    Set.orderIsoOfEq _ _ (by rw [e.surjective.range_comp])
  extends_corners i :=
    Subtype.ext (congrArg Subtype.val (closureOrderIsoOfMintermEqBot_apply h i) :)

/-- Every Boolean isomorphism is an Aristotelian isomorphism. -/
def toAristotelianIso (bi : BooleanIso φ φ') : AristotelianIso φ φ' where
  toEquiv := bi.toEquiv
  map_disjoint i j := by
    simp only [toFun_as_coe, ← coe_corner φ, ← coe_corner φ', disjoint_coe, ← bi.extends_corners,
      disjoint_map_orderIso_iff]
  map_codisjoint i j := by
    simp only [toFun_as_coe, ← coe_corner φ, ← coe_corner φ', codisjoint_coe,
      ← bi.extends_corners, codisjoint_map_orderIso_iff]
  map_lt i j := by
    simp only [toFun_as_coe, ← coe_corner φ, ← coe_corner φ', Subtype.coe_lt_coe,
      ← bi.extends_corners, bi.closureIso.lt_iff_lt]

/-- Forget a Boolean isomorphism down to its underlying Aristotelian isomorphism. -/
instance : CoeOut (BooleanIso φ φ') (AristotelianIso φ φ') := ⟨toAristotelianIso⟩

end BooleanIso

/-! ### Bitstrings -/

variable [Fintype ι] [DecidableEq ι] [DecidableEq α] in
variable (φ) in
/-- The bitstrings of the elements of a diagram form a diagram Aristotelian isomorphic to it
([demey-smessaert-2018] Theorem 2). -/
noncomputable def AristotelianIso.toSetOfMinterms :
    AristotelianIso φ fun i ↦ BooleanSubalgebra.toSetOfMinterms φ (corner φ i) where
  toEquiv := .refl ι
  map_disjoint i j := (disjoint_coe (a := corner φ i) (b := corner φ j)).trans
    (disjoint_map_orderIso_iff (BooleanSubalgebra.toSetOfMinterms φ)).symm
  map_codisjoint i j := (codisjoint_coe (a := corner φ i) (b := corner φ j)).trans
    (codisjoint_map_orderIso_iff (BooleanSubalgebra.toSetOfMinterms φ)).symm
  map_lt i j := (Subtype.coe_lt_coe (x := corner φ i) (y := corner φ j)).trans
    (BooleanSubalgebra.toSetOfMinterms φ).lt_iff_lt.symm

end Aristotelian
