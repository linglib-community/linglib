module

public import Linglib.Core.Order.BooleanSubalgebra
public import Linglib.Logic.Aristotelian.Basic

/-!
# Isomorphisms of Aristotelian diagrams

An *Aristotelian diagram* is a fragment of a Boolean algebra, here an indexed family
`φ : ι → α`. A bijection of corners is an *Aristotelian isomorphism* when it preserves and
reflects the Aristotelian relations, and a *Boolean isomorphism* when it extends to an order
isomorphism of the Boolean closures, an extension that is then
[unique](##BooleanIso.toEquiv_injective). Every Boolean isomorphism is an Aristotelian one, and
the bitstring semantics, sending each element of the closure to the set of minterms below it,
[carries a diagram to a Boolean isomorphic diagram of bitstrings](##BooleanIso.toSetOfMinterms).

The Aristotelian relations are binary, so they see the minterms of a diagram only through pairs
of literals. A polarity assignment is *consistent* with the relations when no two of its
literals are contradictory or contrary, and consistency depends only on the relations. Every
nonzero minterm is at a consistent assignment, so [the consistent assignments bound the nonzero
minterms of every diagram Aristotelian isomorphic to a given
one](##AristotelianIso.consistent_of_minterm_ne_bot). A consistent assignment whose literals each
lie above one of two of them [has a nonzero minterm in every such
diagram](##AristotelianIso.minterm_ne_bot_of_consistent). Only the remaining consistent
assignments can vanish in one diagram of a family and not in another, and a bijection under which
none does is a [Boolean isomorphism](##BooleanIso.ofMintermEqBot). The upper bound is attained by
the canonical diagram, which reads the corners on the consistent assignments themselves: it is
[Aristotelian isomorphic to the original](##AristotelianIso.toCanonical) and [has a nonzero
minterm at each of them](##minterm_canonical_ne_bot_iff), so the largest number of cells in an
Aristotelian family is its number of consistent assignments.

## Implementation notes

The family `φ : ι → α` stands in for the papers' set `F ⊆ α`, and a corner bijection is a
bijection of index types. `AristotelianIso` asks for `Disjoint`, `Codisjoint` and `≤` to be
preserved and reflected, which is to say disjointness of any two literals. On injective families
this is the papers' definition by the four relations (`AristotelianIso.mk'`). Asking for `<` in
place of `≤` would let an isomorphism send two copies of one corner to two unconnected corners,
and consistency would not be preserved. Two literals are contradictory or contrary exactly when
they are disjoint (`disjoint_iff_isCompl_or_isContrary`), which is how `Consistent` states
Demey's condition. Demey argues informally that his consistent conjunctions form the largest
partition an Aristotelian family can induce; `card_parts_minterms_canonical` proves it.

The bitstring semantics is Boolean-algebra theory and lives in `Core/Order`. Demey and
Smessaert's partition induced by a fragment (2018, Definition 5; 2024, Definition 3) is
`Finpartition.minterms`, with anchor formulas `minterm`; their Lemma 3 is `disjoint_minterm`
and `sup_minterm`, Lemma 4 `Finpartition.minterms_sumElim`, Lemma 6
`BooleanSubalgebra.minterm_le_or_le_compl`, Lemma 7
`BooleanSubalgebra.le_iff_forall_mem_minterms`, Lemma 9
`BooleanSubalgebra.isAtom_iff_mem_minterms`, and the bitstring semantics of Theorem 1
`BooleanSubalgebra.toSetOfMinterms`, with `BooleanSubalgebra.card_closure`. They number the
minterms and write a set of them as a string of bits; `toSetOfMinterms` keeps the set. Their
Theorem 2 is `BooleanIso.toSetOfMinterms` coerced to an Aristotelian isomorphism, the route of
their proof.

## References

* [demey-smessaert-2018]
* [demey-2018]
* [demey-smessaert-2024]
* [deklerck-vignero-demey-2024]
-/

@[expose] public section

namespace Aristotelian

variable {ι ι' ι'' α α' α'' : Type*} [BooleanAlgebra α] [BooleanAlgebra α'] [BooleanAlgebra α'']
  {φ : ι → α} {φ' : ι' → α'} {φ'' : ι'' → α''}

open BooleanSubalgebra

/-- An **Aristotelian isomorphism** is a corner bijection preserving and reflecting `Disjoint`,
`Codisjoint` and `≤`, and hence the four Aristotelian relations (`map_isCompl` and
siblings). -/
structure AristotelianIso (φ : ι → α) (φ' : ι' → α') extends ι ≃ ι' where
  /-- Joint inconsistency (`⊓ = ⊥`) is preserved and reflected. -/
  map_disjoint' {i j : ι} : Disjoint (φ' (toEquiv i)) (φ' (toEquiv j)) ↔ Disjoint (φ i) (φ j)
  /-- Joint exhaustiveness (`⊔ = ⊤`) is preserved and reflected. -/
  map_codisjoint' {i j : ι} :
    Codisjoint (φ' (toEquiv i)) (φ' (toEquiv j)) ↔ Codisjoint (φ i) (φ j)
  /-- Entailment is preserved and reflected. -/
  map_le' {i j : ι} : φ' (toEquiv i) ≤ φ' (toEquiv j) ↔ φ i ≤ φ j

namespace AristotelianIso

theorem toEquiv_injective : Function.Injective (toEquiv : AristotelianIso φ φ' → ι ≃ ι')
  | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩, rfl => rfl

instance : EquivLike (AristotelianIso φ φ') ι ι' where
  coe e := e.toEquiv
  inv e := e.toEquiv.symm
  left_inv e := e.left_inv
  right_inv e := e.right_inv
  coe_injective' _ _ h _ := toEquiv_injective (Equiv.coe_fn_injective h)

@[simp] theorem coe_fn_toEquiv (e : AristotelianIso φ φ') : (e.toEquiv : ι → ι') = e := rfl

@[ext]
theorem ext {e e' : AristotelianIso φ φ'} (h : ∀ i, e i = e' i) : e = e' := DFunLike.ext _ _ h

variable (e : AristotelianIso φ φ') {i j : ι}

@[simp] theorem map_disjoint : Disjoint (φ' (e i)) (φ' (e j)) ↔ Disjoint (φ i) (φ j) :=
  e.map_disjoint'

@[simp] theorem map_codisjoint : Codisjoint (φ' (e i)) (φ' (e j)) ↔ Codisjoint (φ i) (φ j) :=
  e.map_codisjoint'

@[simp] theorem map_le : φ' (e i) ≤ φ' (e j) ↔ φ i ≤ φ j := e.map_le'

@[simp] theorem map_lt : φ' (e i) < φ' (e j) ↔ φ i < φ j := by
  simp only [lt_iff_le_not_ge, map_le]

@[simp] theorem map_isCompl : IsCompl (φ' (e i)) (φ' (e j)) ↔ IsCompl (φ i) (φ j) := by
  simp only [isCompl_iff, map_disjoint, map_codisjoint]

@[simp] theorem map_isContrary : IsContrary (φ' (e i)) (φ' (e j)) ↔ IsContrary (φ i) (φ j) := by
  simp only [IsContrary, map_disjoint, map_codisjoint]

@[simp] theorem map_isSubcontrary :
    IsSubcontrary (φ' (e i)) (φ' (e j)) ↔ IsSubcontrary (φ i) (φ j) := by
  simp only [IsSubcontrary, map_disjoint, map_codisjoint]

/-- An Aristotelian isomorphism of injective families from a bijection preserving and reflecting
the four Aristotelian relations, as [demey-smessaert-2018] and [demey-smessaert-2024] define
it. -/
def mk' (hφ : Function.Injective φ) (hφ' : Function.Injective φ') (e : ι ≃ ι')
    (hc : ∀ {i j}, IsCompl (φ' (e i)) (φ' (e j)) ↔ IsCompl (φ i) (φ j))
    (hC : ∀ {i j}, IsContrary (φ' (e i)) (φ' (e j)) ↔ IsContrary (φ i) (φ j))
    (hS : ∀ {i j}, IsSubcontrary (φ' (e i)) (φ' (e j)) ↔ IsSubcontrary (φ i) (φ j))
    (hL : ∀ {i j}, φ' (e i) < φ' (e j) ↔ φ i < φ j) : AristotelianIso φ φ' where
  toEquiv := e
  map_disjoint' := by
    simp only [disjoint_iff_isCompl_or_isContrary]
    exact or_congr hc hC
  map_codisjoint' := by
    simp only [codisjoint_iff_isCompl_or_isSubcontrary]
    exact or_congr hc hS
  map_le' := by
    simp only [le_iff_lt_or_eq]
    exact or_congr hL ((hφ'.eq_iff.trans e.injective.eq_iff).trans hφ.eq_iff.symm)

/-- The identity Aristotelian isomorphism. -/
@[refl] protected def refl (φ : ι → α) : AristotelianIso φ φ where
  toEquiv := .refl ι
  map_disjoint' := .rfl
  map_codisjoint' := .rfl
  map_le' := .rfl

/-- The inverse Aristotelian isomorphism. -/
@[symm] protected def symm : AristotelianIso φ' φ where
  toEquiv := e.toEquiv.symm
  map_disjoint' {i j} := by
    rw [← e.map_disjoint', Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  map_codisjoint' {i j} := by
    rw [← e.map_codisjoint', Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  map_le' {i j} := by rw [← e.map_le', Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- Composition of Aristotelian isomorphisms. -/
@[trans] protected def trans (e' : AristotelianIso φ' φ'') : AristotelianIso φ φ'' where
  toEquiv := e.toEquiv.trans e'.toEquiv
  map_disjoint' := e'.map_disjoint'.trans e.map_disjoint'
  map_codisjoint' := e'.map_codisjoint'.trans e.map_codisjoint'
  map_le' := e'.map_le'.trans e.map_le'

@[simp] theorem refl_apply (i : ι) : AristotelianIso.refl φ i = i := rfl

@[simp] theorem trans_apply (e' : AristotelianIso φ' φ'') (i : ι) : e.trans e' i = e' (e i) := rfl

@[simp] theorem symm_apply_apply (i : ι) : e.symm (e i) = i := e.toEquiv.symm_apply_apply i

@[simp] theorem apply_symm_apply (i : ι') : e (e.symm i) = i := e.toEquiv.apply_symm_apply i

end AristotelianIso

/-! ### Literals -/

section Literal

/-- The literal of `x` at a polarity: `x` itself where the polarity is true, its complement where
it is false. -/
def literal (x : α) (b : Bool) : α := if b then x else xᶜ

@[simp] theorem literal_true (x : α) : literal x true = x := rfl

@[simp] theorem literal_false (x : α) : literal x false = xᶜ := rfl

theorem disjoint_literal_of_ne {x : α} {a b : Bool} (h : a ≠ b) :
    Disjoint (literal x a) (literal x b) := by
  cases a <;> cases b <;> simp_all [disjoint_compl_left, disjoint_compl_right]

/-- A literal lies below another iff it is disjoint from the opposite one. -/
theorem literal_le_literal_iff_disjoint {x y : α} {a b : Bool} :
    literal x a ≤ literal y b ↔ Disjoint (literal x a) (literal y !b) := by
  cases b <;> simp only [literal_true, literal_false, Bool.not_true, Bool.not_false,
    le_compl_iff_disjoint_right, disjoint_compl_right_iff]

/-- A minterm lies below each of its literals. -/
theorem minterm_le_literal [Fintype ι] (σ : ι → Bool) (i : ι) :
    minterm φ σ ≤ literal (φ i) (σ i) :=
  Finset.inf_le (Finset.mem_univ i)

namespace AristotelianIso

/-- An Aristotelian isomorphism from a corner bijection preserving and reflecting disjointness of
literals, which is what preserving `Disjoint`, `Codisjoint` and `≤` amounts to
(`disjoint_literal_iff`). -/
def ofDisjointLiteral (e : ι ≃ ι')
    (h : ∀ a b i j, Disjoint (literal (φ' (e i)) a) (literal (φ' (e j)) b) ↔
      Disjoint (literal (φ i) a) (literal (φ j) b)) : AristotelianIso φ φ' where
  toEquiv := e
  map_disjoint' {i j} := by simpa only [literal_true] using h true true i j
  map_codisjoint' {i j} := by
    simpa only [literal_false, disjoint_compl_left_iff, ← codisjoint_iff_compl_le_left] using
      h false false i j
  map_le' {i j} := by
    simpa only [literal_true, literal_false, disjoint_compl_right_iff] using h true false i j

/-- An Aristotelian isomorphism preserves and reflects disjointness of literals. -/
theorem disjoint_literal_iff (e : AristotelianIso φ φ') (a b : Bool) (i j : ι) :
    Disjoint (literal (φ' (e i)) a) (literal (φ' (e j)) b) ↔
      Disjoint (literal (φ i) a) (literal (φ j) b) := by
  cases a <;> cases b <;>
    simp only [literal_true, literal_false, disjoint_compl_left_iff, disjoint_compl_right_iff,
      ← codisjoint_iff_compl_le_left, e.map_disjoint, e.map_codisjoint, e.map_le]

/-- An Aristotelian isomorphism preserves and reflects entailment between literals. -/
theorem literal_le_literal_iff (e : AristotelianIso φ φ') (a b : Bool) (i j : ι) :
    literal (φ' (e i)) a ≤ literal (φ' (e j)) b ↔ literal (φ i) a ≤ literal (φ j) b := by
  rw [literal_le_literal_iff_disjoint, literal_le_literal_iff_disjoint, e.disjoint_literal_iff]

end AristotelianIso

end Literal

/-! ### Consistency with the Aristotelian relations -/

section Consistent

/-- A polarity assignment `σ` is **consistent** with the Aristotelian relations of `φ` when no
two of its literals are contradictory or contrary, that is disjoint ([demey-2018] Section 4,
[demey-smessaert-2024] Definition 9). -/
def Consistent (φ : ι → α) (σ : ι → Bool) : Prop :=
  ∀ i j, ¬ Disjoint (literal (φ i) (σ i)) (literal (φ j) (σ j))

instance [Fintype ι] [DecidableRel (Disjoint : α → α → Prop)] : DecidablePred (Consistent φ) :=
  fun _ ↦ inferInstanceAs (Decidable (∀ _ _, _))

variable {σ : ι → Bool}

/-- Consistency depends only on the Aristotelian relations. -/
theorem AristotelianIso.consistent_comp_iff (e : AristotelianIso φ φ') :
    Consistent (φ' ∘ e) σ ↔ Consistent φ σ :=
  forall₂_congr fun i j ↦ (e.disjoint_literal_iff (σ i) (σ j) i j).not

variable [Fintype ι]

/-- A nonzero minterm is at a consistent assignment ([demey-2018] Section 4). -/
theorem consistent_of_minterm_ne_bot (h : minterm φ σ ≠ ⊥) : Consistent φ σ := fun i j hd ↦
  h <| le_bot_iff.1 <| (le_inf (minterm_le_literal σ i) (minterm_le_literal σ j)).trans hd.le_bot

/-- A consistent assignment whose literals all lie above one of two of them has a nonzero
minterm: the minterm is the meet of those two literals, which are not disjoint
([demey-smessaert-2024] Section 5). -/
theorem minterm_ne_bot_of_consistent {i j : ι} (hσ : Consistent φ σ)
    (h : ∀ k, literal (φ i) (σ i) ≤ literal (φ k) (σ k) ∨
      literal (φ j) (σ j) ≤ literal (φ k) (σ k)) :
    minterm φ σ ≠ ⊥ := fun h0 ↦ hσ i j <| disjoint_iff_inf_le.2 <|
  (Finset.le_inf fun k _ ↦ (h k).elim inf_le_left.trans inf_le_right.trans).trans_eq h0

variable (e : AristotelianIso φ φ')

/-- The nonzero minterms of a diagram are at assignments consistent with the Aristotelian
relations of any diagram Aristotelian isomorphic to it. -/
theorem AristotelianIso.consistent_of_minterm_ne_bot (h : minterm (φ' ∘ e) σ ≠ ⊥) :
    Consistent φ σ :=
  e.consistent_comp_iff.1 (Aristotelian.consistent_of_minterm_ne_bot h)

/-- A consistent assignment of `φ` whose literals all lie above one of two of them has a nonzero
minterm in every diagram Aristotelian isomorphic to `φ`. -/
theorem AristotelianIso.minterm_ne_bot_of_consistent {i j : ι} (hσ : Consistent φ σ)
    (h : ∀ k, literal (φ i) (σ i) ≤ literal (φ k) (σ k) ∨
      literal (φ j) (σ j) ≤ literal (φ k) (σ k)) :
    minterm (φ' ∘ e) σ ≠ ⊥ :=
  Aristotelian.minterm_ne_bot_of_consistent (e.consistent_comp_iff.2 hσ) fun k ↦
    (h k).imp (e.literal_le_literal_iff _ _ _ _).2 (e.literal_le_literal_iff _ _ _ _).2

section Card

open Finset

variable [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] [DecidableEq α']
  [DecidablePred (Consistent φ)]

omit [Fintype ι'] [DecidableEq ι'] in
private theorem filter_minterm_ne_bot_subset :
    (univ.filter fun σ ↦ minterm (φ' ∘ e.toEquiv) σ ≠ ⊥) ⊆ univ.filter (Consistent φ) :=
  fun _ hσ ↦ mem_filter.2 ⟨mem_univ _, e.consistent_of_minterm_ne_bot (mem_filter.1 hσ).2⟩

include e in
/-- A diagram Aristotelian isomorphic to `φ` has at most as many nonzero minterms as `φ` has
consistent assignments ([demey-2018] Section 4). -/
theorem AristotelianIso.card_parts_minterms_le :
    #(Finpartition.minterms φ').parts ≤ #(univ.filter (Consistent φ)) := by
  rw [← Finpartition.parts_minterms_comp_equiv e.toEquiv, Finpartition.card_parts_minterms]
  exact card_le_card (filter_minterm_ne_bot_subset e)

/-- A diagram Aristotelian isomorphic to `φ` with as many nonzero minterms as `φ` has consistent
assignments has its nonzero minterms exactly at them. -/
theorem AristotelianIso.minterm_ne_bot_iff_of_card_eq
    (h : #(Finpartition.minterms φ').parts = #(univ.filter (Consistent φ))) :
    minterm (φ' ∘ e) σ ≠ ⊥ ↔ Consistent φ σ := by
  have := eq_of_subset_of_card_le (filter_minterm_ne_bot_subset e) <| by
    rw [← h, ← Finpartition.parts_minterms_comp_equiv e.toEquiv,
      Finpartition.card_parts_minterms]
  simpa using congrArg (σ ∈ ·) this

end Card

end Consistent

/-! ### The canonical diagram -/

section Canonical

variable (φ) in
/-- The **canonical diagram** of `φ` reads its corners on the assignments consistent with it,
the `i`-th corner being the set of those that make `i` true. -/
def canonical (i : ι) : Set {σ : ι → Bool // Consistent φ σ} := {σ | σ.1 i = true}

theorem literal_canonical (i : ι) (a : Bool) : literal (canonical φ i) a = {σ | σ.1 i = a} := by
  cases a <;> ext <;> simp [canonical]

variable [Fintype ι] {σ : ι → Bool}

theorem mem_minterm_canonical {τ : {σ : ι → Bool // Consistent φ σ}} :
    τ ∈ minterm (canonical φ) σ ↔ τ.1 = σ := by
  refine ⟨fun h ↦ funext fun i ↦ ?_, fun h ↦ ?_⟩
  · have := minterm_le_literal (φ := canonical φ) σ i h
    rwa [literal_canonical] at this
  · refine Set.singleton_subset_iff.1 (Finset.le_inf fun i _ ↦ ?_)
    change {τ} ⊆ literal (canonical φ i) (σ i)
    rw [literal_canonical, Set.singleton_subset_iff]
    exact congrFun h i

/-- The canonical diagram has a nonzero minterm at every consistent assignment. -/
theorem minterm_canonical_ne_bot_iff : minterm (canonical φ) σ ≠ ⊥ ↔ Consistent φ σ := by
  rw [Set.bot_eq_empty, ← Set.nonempty_iff_ne_empty]
  exact ⟨fun ⟨τ, hτ⟩ ↦ mem_minterm_canonical.1 hτ ▸ τ.2,
    fun h ↦ ⟨⟨σ, h⟩, mem_minterm_canonical.2 rfl⟩⟩

variable [DecidableEq ι]

/-- Two literals of the canonical diagram are disjoint iff those of `φ` are: two literals of `φ`
that are not disjoint meet a nonzero minterm, which is at a consistent assignment. -/
theorem disjoint_literal_canonical_iff (a b : Bool) (i j : ι) :
    Disjoint (literal (canonical φ i) a) (literal (canonical φ j) b) ↔
      Disjoint (literal (φ i) a) (literal (φ j) b) := by
  rw [literal_canonical, literal_canonical, Set.disjoint_left]
  refine ⟨fun h ↦ by_contra fun hd ↦ ?_, fun hd τ hi hj ↦ τ.2 i j (by rwa [hi, hj])⟩
  obtain ⟨σ, hσ⟩ := exists_not_disjoint_minterm (φ := φ) (disjoint_iff.not.1 hd)
  have hne : minterm φ σ ≠ ⊥ := fun h0 ↦ hσ (h0 ▸ disjoint_bot_right)
  have hpol (k : ι) (c : Bool) (hk : literal (φ i) a ⊓ literal (φ j) b ≤ literal (φ k) c) :
      σ k = c := by_contra fun hc ↦ hσ <| Disjoint.mono_left hk <|
    ((disjoint_literal_of_ne hc).mono_left (minterm_le_literal σ k)).symm
  exact h (a := ⟨σ, consistent_of_minterm_ne_bot hne⟩) (hpol i a inf_le_left)
    (hpol j b inf_le_right)

variable (φ) in
/-- A diagram is Aristotelian isomorphic to its canonical diagram. -/
def AristotelianIso.toCanonical : AristotelianIso φ (canonical φ) :=
  ofDisjointLiteral (.refl ι) disjoint_literal_canonical_iff

variable (φ) in
open Finset in
open scoped Classical in
/-- The canonical diagram has as many nonzero minterms as `φ` has consistent assignments, so the
bound of `AristotelianIso.card_parts_minterms_le` is attained: the largest number of cells of a
diagram Aristotelian isomorphic to `φ` is its number of consistent assignments
([demey-2018] Section 4). -/
theorem card_parts_minterms_canonical [DecidablePred (Consistent φ)] :
    #(Finpartition.minterms (canonical φ)).parts = #(univ.filter (Consistent φ)) := by
  rw [Finpartition.card_parts_minterms]
  exact congrArg card (filter_congr fun _ _ ↦ minterm_canonical_ne_bot_iff)

end Canonical

/-! ### Boolean isomorphisms -/

/-- The `i`-th corner of a diagram, viewed inside its Boolean closure. -/
def corner (φ : ι → α) (i : ι) : closure (Set.range φ) :=
  ⟨φ i, subset_closure (Set.mem_range_self i)⟩

@[simp, norm_cast]
theorem coe_corner (φ : ι → α) (i : ι) : (corner φ i : α) = φ i := rfl

/-- A **Boolean isomorphism** is a corner bijection that extends to an order isomorphism of the
Boolean closures. -/
structure BooleanIso (φ : ι → α) (φ' : ι' → α') extends ι ≃ ι' where
  /-- The order isomorphism of Boolean closures extending the bijection. -/
  closureIso : closure (Set.range φ) ≃o closure (Set.range φ')
  /-- `closureIso` carries each corner to its image. -/
  closureIso_corner' (i : ι) : closureIso (corner φ i) = corner φ' (toEquiv i)

namespace BooleanIso

/-- A Boolean isomorphism is determined by its corner bijection: the corners generate the
closure, so the extension is unique. -/
theorem toEquiv_injective : Function.Injective (toEquiv : BooleanIso φ φ' → ι ≃ ι') := by
  rintro ⟨e, f, hf⟩ ⟨_, g, hg⟩ rfl
  obtain rfl : f = g := closure_hom_ext <| by
    rintro _ ⟨i, rfl⟩
    exact (hf i).trans (hg i).symm
  rfl

instance : EquivLike (BooleanIso φ φ') ι ι' where
  coe e := e.toEquiv
  inv e := e.toEquiv.symm
  left_inv e := e.left_inv
  right_inv e := e.right_inv
  coe_injective' _ _ h _ := toEquiv_injective (Equiv.coe_fn_injective h)

@[simp] theorem coe_fn_toEquiv (e : BooleanIso φ φ') : (e.toEquiv : ι → ι') = e := rfl

@[ext]
theorem ext {e e' : BooleanIso φ φ'} (h : ∀ i, e i = e' i) : e = e' := DFunLike.ext _ _ h

@[simp] theorem closureIso_corner (e : BooleanIso φ φ') (i : ι) :
    e.closureIso (corner φ i) = corner φ' (e i) :=
  e.closureIso_corner' i

@[simp] theorem coe_closureIso_corner (e : BooleanIso φ φ') (i : ι) :
    (e.closureIso (corner φ i) : α') = φ' (e i) :=
  congrArg Subtype.val (e.closureIso_corner i)

/-- The identity Boolean isomorphism. -/
@[refl] protected def refl (φ : ι → α) : BooleanIso φ φ where
  toEquiv := .refl ι
  closureIso := .refl _
  closureIso_corner' _ := rfl

/-- The inverse Boolean isomorphism. -/
@[symm] protected def symm (e : BooleanIso φ φ') : BooleanIso φ' φ where
  toEquiv := e.toEquiv.symm
  closureIso := e.closureIso.symm
  closureIso_corner' i := by
    rw [OrderIso.symm_apply_eq, e.closureIso_corner', Equiv.apply_symm_apply]

/-- Composition of Boolean isomorphisms. -/
@[trans] protected def trans (e : BooleanIso φ φ') (e' : BooleanIso φ' φ'') : BooleanIso φ φ'' where
  toEquiv := e.toEquiv.trans e'.toEquiv
  closureIso := e.closureIso.trans e'.closureIso
  closureIso_corner' i := by
    rw [OrderIso.trans_apply, e.closureIso_corner', e'.closureIso_corner']
    rfl

/-- A diagram is Boolean isomorphic to its image along an injective homomorphism. -/
noncomputable def ofInjective (g : BoundedLatticeHom α α') (hg : Function.Injective g) :
    BooleanIso φ (g ∘ φ) where
  toEquiv := .refl ι
  closureIso := (orderIsoMapOfInjective _ hg).trans <|
    Set.orderIsoOfEq _ _ (by rw [map_closure, ← Set.range_comp])
  closureIso_corner' _ := rfl

/-- A diagram of sets of types is Boolean isomorphic to its preimage along a surjection onto the
types, such as the map sending each model of a logic to its type. -/
noncomputable def ofSurjective {X T : Type*} [Fintype T] [DecidableEq T] {φ : ι → Finset T}
    (t : X → T) (ht : Function.Surjective t) : BooleanIso φ fun i ↦ t ⁻¹' ↑(φ i) :=
  ofInjective (φ := φ) ((CompleteLatticeHom.setPreimage t).toBoundedLatticeHom.comp
    (Fintype.finsetOrderIsoSet (α := T) : BoundedLatticeHom (Finset T) (Set T)))
    ((Set.preimage_injective.2 ht).comp Finset.coe_injective)

/-- A corner bijection is a Boolean isomorphism when the minterms of the two diagrams, matched
along it, vanish together. -/
noncomputable def ofMintermEqBot [Fintype ι] [DecidableEq ι] [DecidableEq α] [DecidableEq α']
    (e : ι ≃ ι') (h : ∀ σ, minterm φ σ = ⊥ ↔ minterm (φ' ∘ e) σ = ⊥) : BooleanIso φ φ' where
  toEquiv := e
  closureIso := (closureOrderIsoOfMintermEqBot h).trans <|
    Set.orderIsoOfEq _ _ (by rw [e.surjective.range_comp])
  closureIso_corner' i :=
    Subtype.ext (congrArg Subtype.val (closureOrderIsoOfMintermEqBot_apply h i) :)

/-- Every Boolean isomorphism is an Aristotelian isomorphism ([demey-smessaert-2018] Lemma 1). -/
def toAristotelianIso (e : BooleanIso φ φ') : AristotelianIso φ φ' where
  toEquiv := e.toEquiv
  map_disjoint' {i j} := by
    change Disjoint (φ' (e i)) (φ' (e j)) ↔ _
    rw [← e.coe_closureIso_corner i, ← e.coe_closureIso_corner j, disjoint_coe,
      disjoint_map_orderIso_iff]
    exact disjoint_coe.symm
  map_codisjoint' {i j} := by
    change Codisjoint (φ' (e i)) (φ' (e j)) ↔ _
    rw [← e.coe_closureIso_corner i, ← e.coe_closureIso_corner j, codisjoint_coe,
      codisjoint_map_orderIso_iff]
    exact codisjoint_coe.symm
  map_le' {i j} := by
    change φ' (e i) ≤ φ' (e j) ↔ _
    rw [← e.coe_closureIso_corner i, ← e.coe_closureIso_corner j, Subtype.coe_le_coe,
      e.closureIso.le_iff_le]
    exact Subtype.coe_le_coe.symm

/-- Forget a Boolean isomorphism down to its underlying Aristotelian isomorphism. -/
instance : CoeOut (BooleanIso φ φ') (AristotelianIso φ φ') := ⟨toAristotelianIso⟩

variable [Fintype ι] [DecidableEq ι] [DecidableEq α] in
variable (φ) in
/-- The bitstring semantics carries a diagram to a Boolean isomorphic diagram of bitstrings, the
sets of minterms below its corners ([demey-smessaert-2018] Theorem 1). -/
noncomputable def toSetOfMinterms :
    BooleanIso φ fun i ↦ BooleanSubalgebra.toSetOfMinterms φ (corner φ i) :=
  (ofInjective (φ := corner φ) (closure (Set.range φ)).subtype
    (closure (Set.range φ)).subtype_injective).symm.trans <|
    ofInjective (φ := corner φ) (BooleanSubalgebra.toSetOfMinterms φ :
      BoundedLatticeHom (closure (Set.range φ)) (Set (Finpartition.minterms φ).parts))
      (BooleanSubalgebra.toSetOfMinterms φ).injective

end BooleanIso

end Aristotelian
