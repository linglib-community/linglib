module

public import Mathlib.ModelTheory.Satisfiability
public import Linglib.Logic.Modal.FirstOrder.Correspondence
public import Linglib.Logic.Team.QBSML.Properties

/-!
# Classical model theory for the NE-free fragment of QBSML

[aloni-vanormondt-2023] Proposition 4.1 composed with the standard
translation (`Logic/Modal/FirstOrder/Correspondence.lean`): NE-free QBSML
support at a singleton state is mathlib `Formula.Realize` over the
correspondence structure (`support_singleton_iff_st`), support forces the
closed translation as a sentence and conversely
(`models_toSentence_of_support`, `exists_support_of_models_toSentence`),
and by mathlib's first-order compactness, if every finite subfamily of a family
of formulas is supported at a singleton state, their closed translations are
jointly satisfiable (`isSatisfiable_stClose_of_support`).

## Implementation notes

Each closed translation binds its own world variable, so a structure satisfying
the family need only verify each formula at some world of its own. The
theorem is therefore not compactness of team support, which fails: models
have finitely many successors at each world, so no singleton state supports
the family of `◇φₙ` for infinitely many sentences `φₙ` together with
`□¬(φᵢ ∧ φⱼ)` for `i ≠ j`, although every finite subfamily is supported, as
`BSML/Completeness.lean` notes for the propositional fragment.

## TODO

* Non-compactness of NE-free support at singleton states, by such a family.

## References

* [aloni-vanormondt-2023]
* [puljujarvi-quadrellaro-2024]
-/

@[expose] public section

universe u v

namespace QBSML

open FirstOrder Language

variable {W Var Const Pred Domain : Type*}
variable [DecidableEq W] [DecidableEq Var] [Fintype Var]
variable [DecidableEq Domain] [Fintype Domain] [Inhabited Domain]

/-! ### Proposition 4.1, composed: QBSML support is first-order realization -/

/-- At a singleton state, NE-free QBSML support is first-order satisfaction of the standard
translation ([aloni-vanormondt-2023] Proposition 4.1). -/
theorem support_singleton_iff_st (M : Model W Domain Const Pred)
    {φ : Formula Var Const Pred}
    {τ : ModalFormula ((Language.monadic Pred)[[Const]]) Var} {k : ℕ}
    (hτ : φ.toModal? = some τ)
    {i : Index W Var Domain} {v : Var → Domain} (u : ℕ → W)
    (hv : ∀ y, i.assign y = ↑(v y)) (hu : u k = i.world) :
    support M φ {i} ↔
      (letI := M.correspondence
       (τ.st k).Realize (stVal v u)) :=
  (support_singleton_iff_realize M hτ hv).trans (hu ▸ realize_st M)

theorem models_toSentence_of_support (M : Model W Domain Const Pred)
    {φ : Formula Var Const Pred}
    {τ : ModalFormula ((Language.monadic Pred)[[Const]]) Var}
    (hτ : φ.toModal? = some τ)
    (hcl : (stClose 0 (τ.st 0)).freeVarFinset = ∅)
    {i : Index W Var Domain} {v : Var → Domain}
    (hv : ∀ y, i.assign y = ↑(v y)) (hsupp : support M φ {i}) :
    (letI := M.correspondence
     (W ⊕ Domain) ⊨ (stClose 0 (τ.st 0)).toSentence hcl) := by
  let _S := M.correspondence
  have h1 : (τ.st 0).Realize (stVal v (fun _ => i.world)) :=
    (support_singleton_iff_st M hτ (fun _ => i.world) hv rfl).mp hsupp
  refine (Formula.realize_toSentence _ hcl
    (stVal v (fun _ => i.world))).mpr ?_
  refine (realize_stClose 0 (τ.st 0) _ fun _ => Iff.rfl).mpr ⟨i.world, ?_⟩
  rw [show Function.update (stVal v (fun _ => i.world))
      (Sum.inr 0) (Sum.inl i.world) = stVal v (fun _ => i.world) from
    Function.update_eq_self _ _]
  exact h1

theorem exists_support_of_models_toSentence
    (M : Model W Domain Const Pred)
    {φ : Formula Var Const Pred}
    {τ : ModalFormula ((Language.monadic Pred)[[Const]]) Var}
    (hτ : φ.toModal? = some τ)
    (hcl : (stClose 0 (τ.st 0)).freeVarFinset = ∅)
    (h : letI := M.correspondence
         (W ⊕ Domain) ⊨ (stClose 0 (τ.st 0)).toSentence hcl) :
    ∃ (i : Index W Var Domain) (v : Var → Domain),
      (∀ y, i.assign y = ↑(v y)) ∧ support M φ {i} := by
  let _S := M.correspondence
  have d₀ : Domain := default
  obtain ⟨w₀, -⟩ := (realize_stClose 0 (τ.st 0) _ fun _ => Iff.rfl).mp
    ((Formula.realize_toSentence _ hcl (fun _ => (Sum.inr d₀ : W ⊕ Domain))).mp h)
  obtain ⟨w, hw⟩ := (realize_stClose 0 (τ.st 0) _ fun _ => Iff.rfl).mp
    ((Formula.realize_toSentence _ hcl (stVal (fun _ => d₀) (fun _ => w₀))).mp h)
  rw [stVal_update_world] at hw
  have hmodal := (realize_st (u := Function.update (fun _ => w₀) 0 w) M).mpr hw
  rw [Function.update_self] at hmodal
  exact ⟨⟨w, fun _ => ↑d₀⟩, fun _ => d₀, fun _ => rfl,
    (support_singleton_iff_realize M hτ fun _ => rfl).mpr hmodal⟩

/-! ### Compactness for the NE-free fragment -/

/-- If every finite subfamily of a family of NE-free formulas is supported at a singleton state of
some model, the closed standard translations of the family, each closing its own world variable,
are jointly satisfiable in one first-order structure ([aloni-vanormondt-2023] Proposition 4.1 with
mathlib's `Theory.isSatisfiable_iff_isFinitelySatisfiable`).

No team model is recovered from that structure, which would need `Finset`-branching accessibility
and a `Fintype` domain, and the formulas may hold at different worlds of it. For first-order team
logics such as independence logic, [puljujarvi-quadrellaro-2024] prove compactness for sets of
formulas by ultraproducts and by saturated models through existential second-order logic. -/
theorem isSatisfiable_stClose_of_support {Var : Type*} [DecidableEq Var] [Fintype Var]
    {Const : Type u} {Pred : Type v} {ι : Type*}
    {φs : ι → Formula Var Const Pred}
    {τs : ι → ModalFormula ((Language.monadic Pred)[[Const]]) Var}
    (hτ : ∀ i, (φs i).toModal? = some (τs i))
    (hcl : ∀ i, (stClose 0 ((τs i).st 0)).freeVarFinset = ∅)
    (hfin : ∀ s : Finset ι, ∃ (W Domain : Type max u v)
      (_ : DecidableEq W) (_ : DecidableEq Domain) (_ : Fintype Domain) (_ : Inhabited Domain)
      (M : Model W Domain Const Pred) (i : Index W Var Domain)
      (v : Var → Domain), (∀ y, i.assign y = ↑(v y)) ∧
        ∀ j ∈ s, support M (φs j) {i}) :
    Theory.IsSatisfiable
      (Set.range fun i => (stClose 0 ((τs i).st 0)).toSentence (hcl i)) := by
  rw [Theory.isSatisfiable_iff_isFinitelySatisfiable]
  intro T₀ hT₀
  classical
  choose f hf using fun x : T₀ => hT₀ x.2
  obtain ⟨W, Domain, _, _, _, _, M, i, v, hv, hs⟩ := hfin (Finset.univ.image f)
  let _S := M.correspondence
  have : Nonempty (W ⊕ Domain) := ⟨Sum.inl i.world⟩
  have : (W ⊕ Domain) ⊨ (T₀ : ((Language.monadic Pred)[[Const]]).correspondence.Theory) := by
    refine ⟨fun σ hσ => ?_⟩
    obtain ⟨x, rfl⟩ : ∃ x : T₀,
        (stClose 0 ((τs (f x)).st 0)).toSentence (hcl (f x)) = σ :=
      ⟨⟨σ, hσ⟩, hf ⟨σ, hσ⟩⟩
    exact models_toSentence_of_support M (hτ (f x)) (hcl (f x))
      hv (hs (f x) (Finset.mem_image_of_mem f (Finset.mem_univ x)))
  exact Theory.Model.isSatisfiable (W ⊕ Domain)

end QBSML
