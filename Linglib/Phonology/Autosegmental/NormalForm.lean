/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Basic.Finite.Sigma
public import Mathlib.Basic.Finite.Sum
public import Mathlib.Data.Fintype.Sort
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Logic.Equiv.Fin.Basic
public import Linglib.Phonology.Autosegmental.AR
public import Linglib.Phonology.Autosegmental.NonCrossing

/-!
# Normal forms of autosegmental representations

Every finite representation is isomorphic to its **normal form**: the same
representation reindexed onto the canonical vertex type `(i : ι) × Fin nᵢ`,
each tier fiber enumerated in ascending precedence order
(the fiber `IsStrictTotalOrder` instance → `linearOrderOfSTO` → `monoEquivOfFin`).
The normal form is an `AR` — not a separate carrier — and `normalizeIso` is
definitional: `normalize` pulls the graph back along the enumeration equivalence.

## Main definitions

* `AR.fiber`, `AR.fiberEnum`, `AR.vertexEquiv`: the tier fibers of a finite
  representation and their canonical enumerations.
* `AR.tierLength`, `AR.tierWord`, `AR.linkRel`, `AR.link`: the tuple reading —
  per-tier sizes, label words, and position-coordinate links.
* `AR.normalize`: the normal form; `AR.ofData`: representations from tuple data.

## Main results

* `AR.normalizeIso`: `X.normalize ≅ X`.
* `AR.arcs_normalize`, `AR.edges_normalize`: on normal forms the arcs are the
  ascending position order and the edges are `linkRel`, so the tiered presentation is
  recovered as a theorem.
* `AR.tierWord_tensor`, `AR.link_tensor`: concatenation appends tier words and
  shifts links blockwise.
* `AR.nonempty_fullIso_iff`: `(tierWord, link)` is a complete isomorphism invariant.
* `AR.noCrossing_iff`: the NCC says that the link relation of each tier pair is
  `IsNonCrossing`.
-/

@[expose] public section

namespace Autosegmental

open CategoryTheory

variable {ι : Type*} {τ : ι → Type*}

/-- Representations over the sigma alphabet `(i : ι) × τ i` with its tier projection
`Sigma.fst`, the coordinate carrier of the normal-form theory. -/
abbrev TieredAR (ι : Type*) (τ : ι → Type*) := AR (Sigma.fst : ((i : ι) × τ i) → ι)

namespace AR

section NormalForm
open scoped Classical

/-- The vertices of `X.obj` labelled to tier `i`. -/
def fiber (X : TieredAR ι τ) (i : ι) :
    Type _ := {v : X.obj.V // (X.obj.label v).1 = i}

variable {X : TieredAR ι τ}

/-- The `τ i` component of a fiber element, extracted from the labeling by
    transporting along the fiber's tier-membership witness. -/
def fiberLabel {i : ι} (v : X.fiber i) : τ i :=
  v.property ▸ (X.obj.label v.val).2

/-- The label of a fiber element decomposes as tier plus `fiberLabel`. -/
theorem label_fiber {i : ι} (v : X.fiber i) :
    X.obj.label v.val = ⟨i, X.fiberLabel v⟩ := by
  obtain ⟨u, hu⟩ := v
  show X.obj.label u = _
  simp only [fiberLabel]
  conv_lhs => rw [← Sigma.eta (X.obj.label u)]
  exact Sigma.eq hu rfl

instance fiber.instFinite [Finite X.obj.V] (i : ι) : Finite (X.fiber i) :=
  Subtype.finite

/-- The arcs restricted to a tier fiber form a strict total order. -/
instance fiber.instIsStrictTotalOrder (i : ι) :
    IsStrictTotalOrder (X.fiber i) (fun a b ↦ X.obj.arcs.Adj a.val b.val) where
  trichotomous a b hab hba := Subtype.ext <| of_not_not fun hne ↦
    (X.property.1.total hne (a.2.trans b.2.symm)).elim hab hba
  irrefl a := X.property.1.irrefl a.1
  trans _ _ _ hab hbc := X.property.1.trans _ _ _ hab hbc

/-- Classical linear order on the fiber, from `IsStrictTotalOrder` via
    `linearOrderOfSTO`. -/
noncomputable instance fiber.instLinearOrder (i : ι) :
    LinearOrder (X.fiber i) := by
  classical
  exact linearOrderOfSTO (fun a b : X.fiber i ↦ X.obj.arcs.Adj a.val b.val)

/-- The number of tier-`i` vertices. -/
noncomputable def tierLength (X : TieredAR ι τ)
    [Finite X.obj.V] (i : ι) : ℕ :=
  letI := Fintype.ofFinite (X.fiber i)
  Fintype.card (X.fiber i)

/-- The canonical ascending enumeration of a tier fiber. -/
noncomputable def fiberEnum [Finite X.obj.V] (i : ι) :
    Fin (X.tierLength i) ≃o X.fiber i :=
  letI := Fintype.ofFinite (X.fiber i)
  monoEquivOfFin (X.fiber i) rfl

/-- The canonical enumeration of a finite representation's vertex type lists the tier
fibers in ascending precedence order, assembled over the tier index. -/
noncomputable def vertexEquiv [Finite X.obj.V] :
    ((i : ι) × Fin (X.tierLength i)) ≃ X.obj.V :=
  letI : ∀ i : ι, Fintype (X.fiber i) := fun _ ↦ Fintype.ofFinite _
  (Equiv.sigmaCongrRight (fun i : ι ↦ (X.fiberEnum i).toEquiv)).trans
    (Equiv.sigmaFiberEquiv (fun v : X.obj.V ↦ (X.obj.label v).1))

/-- The tier-`i` label word reads off the fiber's labels in ascending precedence order. -/
noncomputable def tierWord [Finite X.obj.V] (i : ι) : List (τ i) :=
  letI := Fintype.ofFinite (X.fiber i)
  List.ofFn fun p : Fin (X.tierLength i) ↦ X.fiberLabel (X.fiberEnum i p)

@[simp] theorem length_tierWord [Finite X.obj.V] (i : ι) :
    (X.tierWord i).length = X.tierLength i := by
  simp [tierWord]

/-- Tier-`i` position `p` associates to tier-`j` position `q`; with `tierWord`, this is the
complete tuple reading of a finite representation. -/
noncomputable def linkRel [Finite X.obj.V] (i j : ι)
    (p : Fin (X.tierLength i)) (q : Fin (X.tierLength j)) : Prop :=
  X.obj.edges.Adj (X.vertexEquiv ⟨i, p⟩) (X.vertexEquiv ⟨j, q⟩)

theorem linkRel_def [Finite X.obj.V] {i j : ι} {p : Fin (X.tierLength i)}
    {q : Fin (X.tierLength j)} :
    X.linkRel i j p q ↔
      X.obj.edges.Adj (X.vertexEquiv ⟨i, p⟩) (X.vertexEquiv ⟨j, q⟩) := Iff.rfl

/-- The normal form reindexes `X` onto the canonical vertex type, pulling edges, arcs and
labels back along `vertexEquiv`. -/
noncomputable def normalize
    (X : TieredAR ι τ) [Finite X.obj.V] :
    TieredAR ι τ where
  obj :=
    { V := (i : ι) × Fin (X.tierLength i)
      edges := X.obj.edges.comap X.vertexEquiv
      arcs := ⟨fun v w ↦ X.obj.arcs.Adj (X.vertexEquiv v) (X.vertexEquiv w)⟩
      label := fun v ↦ X.obj.label (X.vertexEquiv v) }
  property :=
    ⟨{ irrefl := fun _ h ↦ X.property.1.irrefl _ h,
       trans := fun _ _ _ huv hvw ↦ X.property.1.trans _ _ _ huv hvw,
       tier_eq := fun _ _ h ↦ X.property.1.tier_eq h,
       total := fun _ _ hne htier ↦
         X.property.1.total (fun hv ↦ hne (X.vertexEquiv.injective hv)) htier },
     fun _ _ hadj harc ↦ X.property.2 hadj harc⟩

/-- The normal form is fully isomorphic to the original. -/
noncomputable def normalizeFullIso [Finite X.obj.V] :
    Graph.Iso (X.normalize).obj X.obj where
  toEquiv := X.vertexEquiv
  edges_iff _ _ := Iff.rfl
  arcs_iff _ _ := Iff.rfl
  label_comp _ := rfl

/-- The normal form is isomorphic to the original. -/
noncomputable def normalizeIso [Finite X.obj.V] : X.normalize ≅ X :=
  mkIso X.normalizeFullIso

/-- On normal forms the edges are exactly `linkRel`. -/
theorem edges_normalize [Finite X.obj.V] (i j : ι)
    (p : Fin (X.tierLength i)) (q : Fin (X.tierLength j)) :
    (X.normalize).obj.edges.Adj ⟨i, p⟩ ⟨j, q⟩ ↔ X.linkRel i j p q := Iff.rfl

/-- On normal forms the arcs are the ascending position order. -/
theorem arcs_normalize [Finite X.obj.V] (i : ι)
    (p q : Fin (X.tierLength i)) :
    (X.normalize).obj.arcs.Adj ⟨i, p⟩ ⟨i, q⟩ ↔ p < q :=
  (X.fiberEnum i).lt_iff_lt

end NormalForm

/-! ### Tier words of tensors

Concatenation appends tier content: within a tier, the bridge arc puts every
left-factor vertex before every right-factor vertex, so the tensor's fiber is
the lexicographic sum of the factors' fibers and its ascending enumeration is
the two enumerations in sequence (`Subsingleton (Fin n ≃o ·)` — monotone
enumerations are unique). -/

section TierWordTensor
open scoped MonoidalCategory

variable {ι : Type*} {τ : ι → Type*}
variable {X Y : TieredAR ι τ}

instance [Finite X.obj.V] [Finite Y.obj.V] : Finite ((X ⊗ Y).obj.V) :=
  inferInstanceAs (Finite (X.obj.V ⊕ Y.obj.V))

/-- A tensor's tier fiber splits as the sum of the factors' fibers. -/
def fiberTensorEquiv (i : ι) :
    (X ⊗ Y).fiber i ≃ X.fiber i ⊕ Y.fiber i where
  toFun v := match v with
    | ⟨.inl w, h⟩ => .inl ⟨w, h⟩
    | ⟨.inr w, h⟩ => .inr ⟨w, h⟩
  invFun := Sum.elim (fun w ↦ ⟨.inl w.val, w.property⟩) (fun w ↦ ⟨.inr w.val, w.property⟩)
  left_inv := by rintro ⟨w | w, h⟩ <;> rfl
  right_inv := by rintro (w | w) <;> rfl

theorem fiberLabel_symm_inl {i : ι} (w : X.fiber i) :
    fiberLabel ((fiberTensorEquiv (X := X) (Y := Y) i).symm
      (.inl w)) = X.fiberLabel w := rfl

theorem fiberLabel_symm_inr {i : ι} (w : Y.fiber i) :
    fiberLabel ((fiberTensorEquiv (X := X) (Y := Y) i).symm
      (.inr w)) = Y.fiberLabel w := rfl

variable [Finite X.obj.V] [Finite Y.obj.V]

attribute [local instance] Fintype.ofFinite

@[simp] theorem tierLength_tensor (i : ι) :
    (X ⊗ Y).tierLength i = X.tierLength i + Y.tierLength i := by
  let := Fintype.ofFinite ((X ⊗ Y).fiber i)
  let := Fintype.ofFinite (X.fiber i)
  let := Fintype.ofFinite (Y.fiber i)
  simp only [tierLength]
  rw [Fintype.card_congr (fiberTensorEquiv i), Fintype.card_sum]

open AR in
/-- The blockwise enumeration of a tensor's fiber lists the left factor first, then the
right; it is monotone because the bridge arc orders the blocks. -/
noncomputable def tensorEnum (i : ι) :
    Fin (X.tierLength i + Y.tierLength i) ≃o (X ⊗ Y).fiber i := by
  letI := Fintype.ofFinite (X.fiber i)
  letI := Fintype.ofFinite (Y.fiber i)
  refine StrictMono.orderIsoOfSurjective
    (finSumFinEquiv.symm.trans
      (((X.fiberEnum i).toEquiv.sumCongr
        (Y.fiberEnum i).toEquiv).trans
        (fiberTensorEquiv i).symm))
    ?_ (Equiv.surjective _)
  intro p q hpq
  simp only [Equiv.trans_apply]
  induction p using Fin.addCases with
  | left p₁ =>
    rw [finSumFinEquiv_symm_apply_castAdd]
    induction q using Fin.addCases with
    | left q₁ =>
      rw [finSumFinEquiv_symm_apply_castAdd]
      exact (X.fiberEnum i).strictMono
        (by simp only [Fin.lt_def, Fin.val_castAdd] at hpq ⊢; exact hpq)
    | right q₂ =>
      rw [finSumFinEquiv_symm_apply_natAdd]
      exact (X.fiberEnum i p₁).property.trans
        ((Y.fiberEnum i q₂).property).symm
  | right p₂ =>
    induction q using Fin.addCases with
    | left q₁ =>
      exact absurd hpq (by simp only [Fin.lt_def, Fin.val_natAdd, Fin.val_castAdd]; omega)
    | right q₂ =>
      rw [finSumFinEquiv_symm_apply_natAdd, finSumFinEquiv_symm_apply_natAdd]
      exact (Y.fiberEnum i).strictMono
        (by simp only [Fin.lt_def, Fin.val_natAdd] at hpq ⊢; omega)

theorem tensorEnum_apply_castAdd (i : ι) (p : Fin (X.tierLength i)) :
    tensorEnum i (Fin.castAdd (Y.tierLength i) p) =
      (fiberTensorEquiv i).symm
        (.inl (X.fiberEnum i p)) := by
  simp [tensorEnum, finSumFinEquiv_symm_apply_castAdd]

theorem tensorEnum_apply_natAdd (i : ι) (p : Fin (Y.tierLength i)) :
    tensorEnum i (Fin.natAdd (X.tierLength i) p) =
      (fiberTensorEquiv (X := X) i).symm
        (.inr (Y.fiberEnum i p)) := by
  simp [tensorEnum, finSumFinEquiv_symm_apply_natAdd]

/-- Any monotone enumeration computes the tier word. -/
theorem tierWord_eq_ofFn {Z : TieredAR ι τ}
    [Finite Z.obj.V] {i : ι} {n : ℕ} (e : Fin n ≃o Z.fiber i) :
    Z.tierWord i = List.ofFn fun p ↦ Z.fiberLabel (e p) := by
  have hn : Z.tierLength i = n := by
    simpa [tierLength] using (Fintype.card_congr e.toEquiv).symm
  subst hn
  rw [Subsingleton.elim e (Z.fiberEnum i)]
  rfl

/-- The tier word of a tensor is the concatenation of the factors' tier words. -/
@[simp] theorem tierWord_tensor (i : ι) :
    (X ⊗ Y).tierWord i = X.tierWord i ++ Y.tierWord i := by
  rw [tierWord_eq_ofFn (tensorEnum i), List.ofFn_add]
  congr 1
  · rw [tierWord_eq_ofFn (X.fiberEnum i)]
    exact congrArg List.ofFn (funext fun p ↦
      (congrArg fiberLabel (tensorEnum_apply_castAdd i p)).trans
        (fiberLabel_symm_inl _))
  · rw [tierWord_eq_ofFn (Y.fiberEnum i)]
    exact congrArg List.ofFn (funext fun p ↦
      (congrArg fiberLabel (tensorEnum_apply_natAdd i p)).trans
        (fiberLabel_symm_inr _))

theorem fiberEnum_tensor (i : ι) :
    (X ⊗ Y).fiberEnum i =
      (Fin.castOrderIso (tierLength_tensor i)).trans
        (tensorEnum i) :=
  Subsingleton.elim _ _

theorem vertexEquiv_tensor_of_lt {i : ι} {r : Fin ((X ⊗ Y).tierLength i)}
    (h : (r : ℕ) < X.tierLength i) :
    (X ⊗ Y).vertexEquiv ⟨i, r⟩ = Sum.inl (X.vertexEquiv ⟨i, ⟨r, h⟩⟩) := by
  show ((X ⊗ Y).fiberEnum i r).val = _
  rw [fiberEnum_tensor, OrderIso.trans_apply,
    show Fin.castOrderIso (tierLength_tensor (X := X) (Y := Y) i) r
      = Fin.castAdd (Y.tierLength i) ⟨r, h⟩ from rfl,
    tensorEnum_apply_castAdd]
  rfl

theorem vertexEquiv_tensor_of_ge {i : ι} {r : Fin ((X ⊗ Y).tierLength i)}
    (h : X.tierLength i ≤ (r : ℕ)) :
    (X ⊗ Y).vertexEquiv ⟨i, r⟩ = Sum.inr (Y.vertexEquiv ⟨i,
      ⟨(r : ℕ) - X.tierLength i, by
        have _h1 := r.isLt
        have h2 : (X ⊗ Y).tierLength i = X.tierLength i + Y.tierLength i :=
          tierLength_tensor i
        omega⟩⟩) := by
  show ((X ⊗ Y).fiberEnum i r).val = _
  rw [fiberEnum_tensor, OrderIso.trans_apply,
    show Fin.castOrderIso (tierLength_tensor (X := X) (Y := Y) i) r
      = Fin.natAdd (X.tierLength i) ⟨(r : ℕ) - X.tierLength i, by
          have h1 := r.isLt
          have h2 : (X ⊗ Y).tierLength i = X.tierLength i + Y.tierLength i :=
            tierLength_tensor i
          omega⟩ from
      Fin.ext (by simpa using (Nat.add_sub_cancel' h).symm),
    tensorEnum_apply_natAdd]
  rfl

instance : Finite ((𝟙_ (TieredAR ι τ)).obj.V) :=
  inferInstanceAs (Finite PEmpty)

@[simp] theorem tierWord_unit (i : ι) :
    (𝟙_ (TieredAR ι τ)).tierWord i = [] := by
  have : IsEmpty ((𝟙_ (TieredAR ι τ)).fiber i) :=
    ⟨fun v ↦ v.val.elim⟩
  rw [tierWord_eq_ofFn (OrderIso.ofIsEmpty (Fin 0) _)]
  exact List.ofFn_zero

@[simp] theorem tierLength_unit (i : ι) : (𝟙_ (TieredAR ι τ)).tierLength i = 0 := by
  rw [← length_tierWord, tierWord_unit, List.length_nil]

end TierWordTensor

/-! ### Readers in ℕ coordinates

`link` reads the link relation at plain ℕ positions (out-of-bounds positions
link to nothing); `linearize` is the two-tier phonetic reading. `link_tensor`
is the blockwise companion of `tierWord_tensor`. -/

section LinkReader

variable {ι : Type*} {τ : ι → Type*}
variable (X : TieredAR ι τ)

/-- Tier-`i` position `p` links to tier-`j` position `q`, in ℕ coordinates
    (out-of-bounds positions link to nothing). -/
def link [Finite X.obj.V] (i j : ι) (p q : ℕ) : Prop :=
  ∃ (hp : p < X.tierLength i) (hq : q < X.tierLength j), X.linkRel i j ⟨p, hp⟩ ⟨q, hq⟩

open scoped MonoidalCategory in
@[simp] theorem not_link_unit (i j : ι) (p q : ℕ) : ¬ (𝟙_ (TieredAR ι τ)).link i j p q :=
  fun ⟨hp, _, _⟩ ↦ by simp at hp

open scoped Classical in
/-- The two-tier reading of tiers `i` over `j` pairs each tier-`j` position's label
    with its linked tier-`i` labels in ascending order. -/
noncomputable def linearize [Finite X.obj.V] (i j : ι) :
    List (τ j × List (τ i)) :=
  (X.tierWord j).zipIdx.map fun bq ↦
    (bq.1, ((X.tierWord i).zipIdx.filter fun ap ↦ X.link i j ap.2 bq.2).map (·.1))

/-- Link conditions are supported on the factor's tier ranges. -/
theorem forall_link_iff_bounded
    {F : TieredAR ι τ} [Finite F.obj.V]
    {C : ι → ι → ℕ → ℕ → Prop} :
    (∀ i j p q, F.link i j p q → C i j p q) ↔
      ∀ i j, ∀ p < F.tierLength i, ∀ q < F.tierLength j,
        F.link i j p q → C i j p q := by
  refine ⟨fun h i j p _ q _ hl ↦ h i j p q hl, fun h i j p q hl ↦ ?_⟩
  obtain ⟨hp, hq, -⟩ := id hl
  exact h i j p hp q hq hl

open scoped MonoidalCategory in
/-- A tensor link lies within the left factor, or within the right factor shifted by the
left factor's tier lengths. -/
theorem link_tensor {X Y : TieredAR ι τ}
    [Finite X.obj.V] [Finite Y.obj.V] (i j : ι) (p q : ℕ) :
    (X ⊗ Y).link i j p q ↔
      X.link i j p q ∨ X.tierLength i ≤ p ∧ X.tierLength j ≤ q ∧
        Y.link i j (p - X.tierLength i) (q - X.tierLength j) := by
  have h2i : (X ⊗ Y).tierLength i = X.tierLength i + Y.tierLength i :=
    tierLength_tensor i
  have h2j : (X ⊗ Y).tierLength j = X.tierLength j + Y.tierLength j :=
    tierLength_tensor j
  constructor
  · rintro ⟨hp, hq, hl⟩
    rw [linkRel_def] at hl
    rcases lt_or_ge p (X.tierLength i) with hpi | hpi <;>
      rcases lt_or_ge q (X.tierLength j) with hqj | hqj
    · rw [vertexEquiv_tensor_of_lt (h := hpi),
        vertexEquiv_tensor_of_lt (h := hqj)] at hl
      exact Or.inl ⟨hpi, hqj, by simpa [linkRel_def] using hl⟩
    · rw [vertexEquiv_tensor_of_lt (h := hpi),
        vertexEquiv_tensor_of_ge (h := hqj)] at hl
      simp at hl
    · rw [vertexEquiv_tensor_of_ge (h := hpi),
        vertexEquiv_tensor_of_lt (h := hqj)] at hl
      simp at hl
    · rw [vertexEquiv_tensor_of_ge (h := hpi),
        vertexEquiv_tensor_of_ge (h := hqj)] at hl
      exact Or.inr ⟨hpi, hqj, by omega, by omega,
        by simpa [linkRel_def] using hl⟩
  · rintro (⟨hp, hq, hl⟩ | ⟨hpi, hqj, hp', hq', hl⟩)
    · rw [linkRel_def] at hl
      refine ⟨by omega, by omega, ?_⟩
      rw [linkRel_def, vertexEquiv_tensor_of_lt (h := hp),
        vertexEquiv_tensor_of_lt (h := hq)]
      simpa using hl
    · rw [linkRel_def] at hl
      refine ⟨by omega, by omega, ?_⟩
      rw [linkRel_def,
        vertexEquiv_tensor_of_ge (h := by omega),
        vertexEquiv_tensor_of_ge (h := by omega)]
      simpa using hl

end LinkReader

/-! ### Classification: the readers determine the representation

Two finite representations with the same tier words and the same links are
isomorphic, so `(tierWord, link)` is a complete invariant of finite representations. -/

section Classification
open scoped MonoidalCategory

variable {ι : Type*} {τ : ι → Type*}
variable {X : TieredAR ι τ}

/-- The label of a canonical vertex sits on its own tier. -/
theorem label_vertexEquiv [Finite X.obj.V] (i : ι)
    (p : Fin (X.tierLength i)) : (X.obj.label (X.vertexEquiv ⟨i, p⟩)).1 = i :=
  (X.fiberEnum i p).property

theorem linkRel_iff_link [Finite X.obj.V] {i j : ι}
    {p : Fin (X.tierLength i)} {q : Fin (X.tierLength j)} :
    X.linkRel i j p q ↔ X.link i j (p : ℕ) (q : ℕ) :=
  ⟨fun h ↦ ⟨p.isLt, q.isLt, h⟩, fun ⟨_, _, h⟩ ↦ by convert h⟩

theorem tierWord_getElem [Finite X.obj.V] {i : ι}
    (p : Fin (X.tierLength i)) :
    (X.tierWord i)[(p : ℕ)]'(by simp) = X.fiberLabel (X.fiberEnum i p) := by
  simp [tierWord]

theorem label_normalize [Finite X.obj.V] {i : ι}
    (p : Fin (X.tierLength i)) :
    (X.normalize).obj.label ⟨i, p⟩ = ⟨i, X.fiberLabel (X.fiberEnum i p)⟩ :=
  X.label_fiber (X.fiberEnum i p)

theorem arcs_normalize_ne [Finite X.obj.V] {i j : ι} (h : i ≠ j)
    (p : Fin (X.tierLength i)) (q : Fin (X.tierLength j)) :
    ¬ (X.normalize).obj.arcs.Adj ⟨i, p⟩ ⟨j, q⟩ := fun ha ↦ by
  have h2 := X.property.1.tier_eq ha
  rw [show Graph.tier Sigma.fst X.obj (X.vertexEquiv ⟨i, p⟩) = i from
      X.label_vertexEquiv i p,
    show Graph.tier Sigma.fst X.obj (X.vertexEquiv ⟨j, q⟩) = j from
      X.label_vertexEquiv j q] at h2
  exact h h2

/-- Links are symmetric in coordinates. -/
theorem link_symm [Finite X.obj.V] {i j : ι} {p q : ℕ}
    (h : X.link i j p q) : X.link j i q p := by
  obtain ⟨hp, hq, hl⟩ := h
  exact ⟨hq, hp, hl.symm⟩

/-- Same-tier vertices are never linked. -/
theorem not_link_self_tier [Finite X.obj.V] (i : ι) (p q : ℕ) :
    ¬ X.link i i p q := by
  rintro ⟨hp, hq, hl⟩
  rw [linkRel_def] at hl
  have hlab : X.obj.tier Sigma.fst (X.vertexEquiv ⟨i, ⟨p, hp⟩⟩)
      = X.obj.tier Sigma.fst (X.vertexEquiv ⟨i, ⟨q, hq⟩⟩) := by
    show (X.obj.label _).1 = (X.obj.label _).1
    rw [label_vertexEquiv, label_vertexEquiv]
  exact (X.property.1.total hl.ne hlab).elim (X.property.2 hl) (X.property.2 hl.symm)

/-- The classification isomorphism as a full-structure `Graph.Iso`. -/
noncomputable def fullIsoOfReaderEq
    {A B : TieredAR ι τ}
    [Finite A.obj.V] [Finite B.obj.V]
    (hw : ∀ i, A.tierWord i = B.tierWord i)
    (hl : ∀ i j p q, A.link i j p q ↔ B.link i j p q) :
    Graph.Iso A.obj B.obj := by
  have hlen : ∀ i, A.tierLength i = B.tierLength i := fun i ↦ by
    rw [← length_tierWord, hw, length_tierWord]
  refine A.normalizeFullIso.symm.trans (Graph.Iso.trans ?_ B.normalizeFullIso)
  refine
    { toEquiv := Equiv.sigmaCongrRight fun i ↦ finCongr (hlen i)
      edges_iff := fun v w ↦ ?_
      arcs_iff := fun v w ↦ ?_
      label_comp := fun v ↦ ?_ }
  · obtain ⟨i, p⟩ := v
    obtain ⟨j, q⟩ := w
    show B.normalize.obj.edges.Adj ⟨i, Fin.cast (hlen i) p⟩ ⟨j, Fin.cast (hlen j) q⟩
      ↔ A.normalize.obj.edges.Adj ⟨i, p⟩ ⟨j, q⟩
    rw [edges_normalize, edges_normalize,
      linkRel_iff_link, linkRel_iff_link]
    exact (hl i j p q).symm
  · obtain ⟨i, p⟩ := v
    obtain ⟨j, q⟩ := w
    show B.normalize.obj.arcs.Adj ⟨i, Fin.cast (hlen i) p⟩ ⟨j, Fin.cast (hlen j) q⟩
      ↔ A.normalize.obj.arcs.Adj ⟨i, p⟩ ⟨j, q⟩
    rcases eq_or_ne i j with rfl | h
    · rw [arcs_normalize, arcs_normalize]
      exact (Fin.castOrderIso (hlen i)).lt_iff_lt
    · exact iff_of_false (arcs_normalize_ne h _ _)
        (arcs_normalize_ne h _ _)
  · obtain ⟨i, p⟩ := v
    show B.normalize.obj.label ⟨i, Fin.cast (hlen i) p⟩ = A.normalize.obj.label ⟨i, p⟩
    rw [label_normalize, label_normalize]
    congr 1
    rw [← tierWord_getElem, ← tierWord_getElem]
    simp only [hw, Fin.val_cast]

/-- Finite representations with equal tier words and equal links are isomorphic;
    the tuple reading is a complete invariant. -/
noncomputable def isoOfReaderEq
    {A B : TieredAR ι τ}
    [Finite A.obj.V] [Finite B.obj.V]
    (hw : ∀ i, A.tierWord i = B.tierWord i)
    (hl : ∀ i j p q, A.link i j p q ↔ B.link i j p q) : A ≅ B :=
  mkIso (fullIsoOfReaderEq hw hl)

/-! #### The readers are invariant -/

/-- A full isomorphism restricts to an order isomorphism of tier fibers. -/
noncomputable def fiberOrderIso {A B : TieredAR ι τ} (e : Graph.Iso A.obj B.obj) (i : ι) :
    A.fiber i ≃o B.fiber i :=
  StrictMono.orderIsoOfSurjective
    (fun v ↦ ⟨e.toEquiv v.1, (congrArg Sigma.fst (e.label_comp v.1)).trans v.2⟩)
    (fun _ _ h ↦ (e.arcs_iff _ _).mpr h)
    fun w ↦ ⟨⟨e.toEquiv.symm w.1, by
      rw [← e.label_comp, e.toEquiv.apply_symm_apply]; exact w.2⟩,
      Subtype.ext (e.toEquiv.apply_symm_apply w.1)⟩

theorem fiberLabel_fiberOrderIso {A B : TieredAR ι τ} (e : Graph.Iso A.obj B.obj) {i : ι}
    (v : A.fiber i) : B.fiberLabel (fiberOrderIso e i v) = A.fiberLabel v := by
  have h := (B.label_fiber (fiberOrderIso e i v)).symm.trans
    ((e.label_comp v.1).trans (A.label_fiber v))
  exact eq_of_heq (Sigma.mk.inj_iff.mp h).2

variable {A B : TieredAR ι τ} [Finite A.obj.V] [Finite B.obj.V]

theorem tierLength_eq_of_iso (e : Graph.Iso A.obj B.obj) (i : ι) :
    A.tierLength i = B.tierLength i := by
  unfold tierLength
  exact @Fintype.card_congr _ _ (Fintype.ofFinite _) (Fintype.ofFinite _)
    (fiberOrderIso e i).toEquiv

theorem vertexEquiv_of_iso (e : Graph.Iso A.obj B.obj) {i : ι} (p : Fin (A.tierLength i)) :
    e.toEquiv (A.vertexEquiv ⟨i, p⟩) =
      B.vertexEquiv ⟨i, Fin.cast (tierLength_eq_of_iso e i) p⟩ :=
  congrArg (fun φ : Fin (A.tierLength i) ≃o B.fiber i ↦ (φ p).val)
    (Subsingleton.elim ((A.fiberEnum i).trans (fiberOrderIso e i))
      ((Fin.castOrderIso (tierLength_eq_of_iso e i)).trans (B.fiberEnum i)))

/-- Fully isomorphic representations have the same tier words. -/
theorem tierWord_eq_of_iso (e : Graph.Iso A.obj B.obj) (i : ι) :
    A.tierWord i = B.tierWord i := by
  rw [tierWord_eq_ofFn (Z := B) ((A.fiberEnum i).trans (fiberOrderIso e i))]
  simp only [OrderIso.trans_apply, fiberLabel_fiberOrderIso]
  rfl

private theorem link_of_iso (e : Graph.Iso A.obj B.obj) {i j : ι} {p q : ℕ}
    (h : A.link i j p q) : B.link i j p q := by
  obtain ⟨hp, hq, hl⟩ := h
  refine ⟨tierLength_eq_of_iso e i ▸ hp, tierLength_eq_of_iso e j ▸ hq, ?_⟩
  have := (e.edges_iff _ _).mpr hl
  rw [vertexEquiv_of_iso, vertexEquiv_of_iso] at this
  exact this

/-- Fully isomorphic representations have the same links. -/
theorem link_iff_of_iso (e : Graph.Iso A.obj B.obj) (i j : ι) (p q : ℕ) :
    A.link i j p q ↔ B.link i j p q :=
  ⟨link_of_iso e, link_of_iso e.symm⟩

/-- Finite representations are fully isomorphic exactly when they have the same tier words and
the same links. -/
theorem nonempty_fullIso_iff :
    Nonempty (Graph.Iso A.obj B.obj) ↔
      (∀ i, A.tierWord i = B.tierWord i) ∧ ∀ i j p q, A.link i j p q ↔ B.link i j p q :=
  ⟨fun ⟨e⟩ ↦ ⟨tierWord_eq_of_iso e, link_iff_of_iso e⟩, fun ⟨hw, hl⟩ ↦ ⟨fullIsoOfReaderEq hw hl⟩⟩

end Classification

/-! ### The No-Crossing Constraint in coordinates -/

section NoCrossing

variable {ι : Type*} {τ : ι → Type*} (X : TieredAR ι τ) [Finite X.obj.V]

/-- On a normal form the arcs are the position order within a tier. -/
theorem arcs_normalize_iff {i j : ι} (p : Fin (X.tierLength i)) (q : Fin (X.tierLength j)) :
    (X.normalize).obj.arcs.Adj ⟨i, p⟩ ⟨j, q⟩ ↔ i = j ∧ (p : ℕ) < q := by
  rcases eq_or_ne i j with rfl | h
  · exact (arcs_normalize (X := X) i p q).trans ⟨fun h ↦ ⟨rfl, h⟩, fun h ↦ h.2⟩
  · exact iff_of_false (arcs_normalize_ne h p q) fun h' ↦ h h'.1

/-- A finite representation obeys the NCC iff the link relation of each tier pair is
non-crossing in position coordinates. -/
theorem noCrossing_iff :
    NoCrossing X.obj.edges X.obj.arcs ↔
      ∀ i j, IsNonCrossing {x : ℕ × ℕ | X.link i j x.1 x.2} := by
  rw [← X.normalizeFullIso.noCrossing_iff]
  constructor
  · rintro h i j ⟨p, q⟩ ⟨hp, hq, hl⟩ ⟨p', q'⟩ ⟨hp', hq', hl'⟩ hpp'
    by_contra! hqq'
    exact h (v := ⟨i, ⟨p, hp⟩⟩) (v' := ⟨j, ⟨q, hq⟩⟩) (w := ⟨i, ⟨p', hp'⟩⟩)
      (w' := ⟨j, ⟨q', hq'⟩⟩) hl hl' ((arcs_normalize_iff X _ _).mpr ⟨rfl, hpp'⟩)
      ((arcs_normalize_iff X _ _).mpr ⟨rfl, hqq'⟩)
  · rintro h ⟨i, p⟩ ⟨j, q⟩ ⟨i', p'⟩ ⟨j', q'⟩ hvv' hww' hvw hw'v'
    obtain ⟨rfl, hpp'⟩ := (arcs_normalize_iff X _ _).mp hvw
    obtain ⟨rfl, hqq'⟩ := (arcs_normalize_iff X _ _).mp hw'v'
    exact (h i j' (show ((p : ℕ), (q : ℕ)) ∈ _ from linkRel_iff_link.mp hvv')
      (show ((p' : ℕ), (q' : ℕ)) ∈ _ from linkRel_iff_link.mp hww') hpp').not_gt hqq'

end NoCrossing

/-! ### Building representations from tuple data

The constructor inverse to the readers: tier words plus a position-coordinate
link relation determine a representation on the canonical carrier. This is the
tiered presentation as a *function* — the essential-surjectivity direction of
the classification. -/

section OfData

variable {ι : Type*} {τ : ι → Type*}

/-- The representation presented by tier words `ws` and cross-tier links `L`
    (positions in ℕ coordinates; same-tier and out-of-bounds pairs are
    ignored, and same-tier links are excluded by construction). Arcs are the
    ascending position order on each tier. -/
def ofData (ws : ∀ i, List (τ i)) (L : ι → ι → ℕ → ℕ → Prop) :
    TieredAR ι τ where
  obj :=
    { V := (i : ι) × Fin (ws i).length
      edges :=
        { Adj := fun v w ↦ v.1 ≠ w.1 ∧
            (L v.1 w.1 v.2 w.2 ∨ L w.1 v.1 w.2 v.2)
          symm := ⟨fun _ _ h ↦ ⟨h.1.symm, h.2.symm⟩⟩
          loopless := ⟨fun _ h ↦ h.1 rfl⟩ }
      arcs := ⟨fun v w ↦ v.1 = w.1 ∧ (v.2 : ℕ) < (w.2 : ℕ)⟩
      label := fun v ↦ ⟨v.1, (ws v.1)[v.2]⟩ }
  property := by
    refine ⟨{ irrefl := fun v h ↦ lt_irrefl _ h.2,
              trans := fun u v w huv hvw ↦ ⟨huv.1.trans hvw.1, huv.2.trans hvw.2⟩,
              tier_eq := fun v w h ↦ h.1,
              total := fun v w hne htier ↦ ?_ },
      fun v w hadj harc ↦ hadj.1 harc.1⟩
    obtain ⟨i, p⟩ := v
    obtain ⟨j, q⟩ := w
    obtain rfl : i = j := htier
    rcases Nat.lt_trichotomy (p : ℕ) (q : ℕ) with h | h | h
    · exact Or.inl ⟨rfl, h⟩
    · exact absurd (by rw [Fin.ext h]) hne
    · exact Or.inr ⟨rfl, h⟩

variable [Finite ι] {ws : ∀ i, List (τ i)} {L : ι → ι → ℕ → ℕ → Prop}

instance : Finite (ofData ws L).obj.V :=
  inferInstanceAs (Finite ((i : ι) × Fin (ws i).length))

/-- The canonical carrier's fiber at `i` is its position range. -/
noncomputable def ofDataFiberEnum (i : ι) :
    Fin ((ws i).length) ≃o (ofData ws L).fiber i := by
  refine StrictMono.orderIsoOfSurjective (fun p ↦ ⟨⟨i, p⟩, rfl⟩) (fun p q h ↦ ⟨rfl, h⟩)
    fun v ↦ ?_
  obtain ⟨⟨j, q⟩, hp⟩ := v
  obtain rfl : j = i := hp
  exact ⟨q, rfl⟩

@[simp] theorem tierLength_ofData (i : ι) :
    (ofData ws L).tierLength i = (ws i).length := by
  rw [← length_tierWord,
    tierWord_eq_ofFn (ofDataFiberEnum i), List.length_ofFn]

theorem fiberEnum_ofData (i : ι) :
    (ofData ws L).fiberEnum i =
      (Fin.castOrderIso (tierLength_ofData i)).trans
        (ofDataFiberEnum i) :=
  Subsingleton.elim _ _

theorem vertexEquiv_ofData {i : ι}
    (r : Fin ((ofData ws L).tierLength i)) :
    (ofData ws L).vertexEquiv ⟨i, r⟩ =
      ⟨i, Fin.cast (tierLength_ofData i) r⟩ := by
  show ((ofData ws L).fiberEnum i r).val = _
  rw [fiberEnum_ofData]
  rfl

/-- `ofData` reads back its words. -/
@[simp] theorem tierWord_ofData (i : ι) :
    (ofData ws L).tierWord i = ws i := by
  rw [tierWord_eq_ofFn (ofDataFiberEnum i)]
  exact List.ofFn_getElem

/-- `ofData` reads back its links, symmetrized, on in-bounds cross-tier
    pairs. -/
theorem link_ofData (i j : ι) (p q : ℕ) :
    (ofData ws L).link i j p q ↔
      i ≠ j ∧ p < (ws i).length ∧ q < (ws j).length ∧ (L i j p q ∨ L j i q p) := by
  constructor
  · rintro ⟨hp, hq, hl⟩
    rw [linkRel_def, vertexEquiv_ofData,
      vertexEquiv_ofData] at hl
    obtain ⟨hne, hor⟩ := hl
    have hp' : p < (ws i).length := tierLength_ofData i ▸ hp
    have hq' : q < (ws j).length := tierLength_ofData j ▸ hq
    exact ⟨hne, hp', hq', by simpa using hor⟩
  · rintro ⟨hij, hp, hq, hor⟩
    have hp' : p < (ofData ws L).tierLength i := by
      rw [← length_tierWord, tierWord_ofData]; exact hp
    have hq' : q < (ofData ws L).tierLength j := by
      rw [← length_tierWord, tierWord_ofData]; exact hq
    refine ⟨hp', hq', ?_⟩
    rw [linkRel_def, vertexEquiv_ofData,
      vertexEquiv_ofData]
    exact ⟨hij, by simpa using hor⟩

end OfData

end AR

end Autosegmental
