/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Logic.Function.Basic
public import Mathlib.Data.Set.Image
public import Linglib.Logic.Modal.Extensional

/-!
# Rigid designation

An intension over an index type `W` is a function `W → τ`, and it is *rigid* when it takes the
same value at every index, a rigid designator in the sense of Kripke. The designator whose
reference `f` fixes at `w` is the constant intension `fun _ ↦ f w`, and `f` is rigid iff it is
the designator whose reference it fixes at every index. Rigidity is subsingletonness of the
range, and rigid intensions that agree at one index agree everywhere, which is the necessity
of identity.

An operator `O` governing the predication of `P` of a designator `f` has a large scope reading,
which evaluates `f` at the index of the whole sentence, and a small scope reading, which
evaluates it at each index the operator reaches. The large scope reading of `f` is the small
scope reading of the designator whose reference `f` fixes at that index. The two readings
coincide when `f` is constant on the indices on which the operator's value depends: under every
operator when `f` is rigid, and for every designator when the operator is extensional.

## Main definitions

* `IsRigid f`: constancy of `f : W → τ`.
* `largeScope O P f`, `smallScope O P f`: the two scope readings of `O` over `P` of `f`.

## Main results

* `isRigid_iff_forall_eq_const`: a rigid designator is the one whose reference it fixes.
* `isRigid_iff_subsingleton_range`: the mathlib face.
* `IsRigid.eq_of_apply_eq`: the necessity of identity.
* `largeScope_eq_smallScope_const`: the large scope reading as fixing the reference.
* `largeScope_eq_smallScope_of_dependsOn`: the scope readings coincide for a designator constant
  on the indices the operator reads.
* `largeScope_eq_smallScope`: the scope readings coincide for a rigid designator.
* `ModalLogic.IsExtensionalAt.largeScope_eq_smallScope`: the scope readings coincide under an
  extensional operator.

## References

* [S. Kripke, *Naming and Necessity* (1980)][kripke-1980]
* [D. Gallin, *Intensional and Higher-Order Modal Logic* (1975)][gallin-1975]
-/

@[expose] public section

variable {W τ τ' : Type*} {f g : W → τ}

/-- An intension is rigid when it takes the same value at every index. -/
def IsRigid (f : W → τ) : Prop := ∀ w₁ w₂, f w₁ = f w₂

theorem isRigid_iff_forall_eq_const : IsRigid f ↔ ∀ w, f = fun _ ↦ f w :=
  ⟨fun h w ↦ funext fun v ↦ h v w, fun h v w ↦ congrFun (h w) v⟩

theorem IsRigid.eq_const (h : IsRigid f) (w : W) : f = fun _ ↦ f w :=
  isRigid_iff_forall_eq_const.1 h w

theorem isRigid_iff_subsingleton_range : IsRigid f ↔ (Set.range f).Subsingleton := by
  simp [IsRigid, Set.Subsingleton]

theorem isRigid_const (x : τ) : IsRigid fun _ : W ↦ x := fun _ _ ↦ rfl

/-- Over a single index every intension is rigid. -/
theorem isRigid_of_subsingleton [Subsingleton W] (f : W → τ) : IsRigid f :=
  isRigid_iff_subsingleton_range.2 (Set.subsingleton_range f)

/-- Rigid intensions that agree at one index are equal, which is the necessity of identity. -/
theorem IsRigid.eq_of_apply_eq (hf : IsRigid f) (hg : IsRigid g) {w : W} (h : f w = g w) :
    f = g :=
  funext fun v ↦ (hf v w).trans (h.trans (hg w v))

theorem IsRigid.ne (hf : IsRigid f) (hg : ¬ IsRigid g) : f ≠ g :=
  fun e ↦ hg (e ▸ hf)

theorem IsRigid.map (h : IsRigid f) (g : τ → τ') : IsRigid (g ∘ f) :=
  fun w₁ w₂ ↦ congrArg g (h w₁ w₂)

theorem Function.Injective.isRigid_comp_iff {g : τ → τ'} (hg : Function.Injective g) :
    IsRigid (g ∘ f) ↔ IsRigid f :=
  ⟨fun h w₁ w₂ ↦ hg (h w₁ w₂), fun h ↦ h.map g⟩

/-! ### Scope -/

/-- The large scope reading of the operator `O` over the predication of `P` of `f`, which
evaluates `f` at the index of the whole sentence. -/
def largeScope (O : (W → Prop) → W → Prop) (P : τ → W → Prop) (f : W → τ) (w : W) : Prop :=
  O (P (f w)) w

/-- The small scope reading, which evaluates `f` at each index the operator reaches. -/
def smallScope (O : (W → Prop) → W → Prop) (P : τ → W → Prop) (f : W → τ) : W → Prop :=
  O fun v ↦ P (f v) v

/-- The large scope reading of `f` is the small scope reading of the designator whose reference
`f` fixes at the index of the whole sentence. -/
theorem largeScope_eq_smallScope_const (O : (W → Prop) → W → Prop) (P : τ → W → Prop)
    (f : W → τ) (w : W) : largeScope O P f w = smallScope O P (fun _ ↦ f w) w :=
  rfl

/-- The two scope readings of `f` coincide at `w` when `f` is constant on a set of indices on
which the operator's value at `w` depends. -/
theorem largeScope_eq_smallScope_of_dependsOn {O : (W → Prop) → W → Prop} {s : Set W} {w : W}
    (hO : DependsOn (O · w) s) (hf : Set.EqOn f (fun _ ↦ f w) s) (P : τ → W → Prop) :
    largeScope O P f w = smallScope O P f w :=
  hO fun v hv ↦ congrArg (P · v) (hf hv).symm

theorem largeScope_eq_smallScope (h : IsRigid f) (O : (W → Prop) → W → Prop)
    (P : τ → W → Prop) : largeScope O P f = smallScope O P f :=
  funext fun w ↦ largeScope_eq_smallScope_of_dependsOn (dependsOn_univ _) (fun v _ ↦ h v w) P

/-- The two scope readings of every designator coincide under an operator extensional at `w`. -/
theorem ModalLogic.IsExtensionalAt.largeScope_eq_smallScope {O : (W → Prop) → W → Prop} {w : W}
    (h : ModalLogic.IsExtensionalAt O w) (P : τ → W → Prop) (f : W → τ) :
    largeScope O P f w = smallScope O P f w :=
  largeScope_eq_smallScope_of_dependsOn (ModalLogic.isExtensionalAt_iff_dependsOn.1 h)
    (Set.eqOn_singleton.2 rfl) P
