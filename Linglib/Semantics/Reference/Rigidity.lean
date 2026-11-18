/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Logic.Function.Const
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

## Implementation notes

`IsRigid` is mathlib's `Function.IsConst` under the name the field gives it, so that the lemmas
about constant functions apply: a constant intension is rigid by `Function.IsConst.const`, and
rigidity is subsingletonness of the range by `Set.subsingleton_range_iff`.

## References

* [S. Kripke, *Naming and Necessity* (1980)][kripke-1980]
* [D. Gallin, *Intensional and Higher-Order Modal Logic* (1975)][gallin-1975]
-/

@[expose] public section

variable {W τ τ' : Type*} {f g : W → τ}

/-- An intension is rigid when it takes the same value at every index. -/
abbrev IsRigid (f : W → τ) : Prop := Function.IsConst f

namespace Function

theorem isConst_iff_forall_eq_const : IsConst f ↔ ∀ w, f = fun _ ↦ f w :=
  ⟨fun h w ↦ funext fun v ↦ h v w, fun h v w ↦ congrFun (h w) v⟩

/-- A rigid designator is the designator whose reference it fixes at any index. -/
theorem IsConst.eq_const (h : IsConst f) (w : W) : f = fun _ ↦ f w :=
  isConst_iff_forall_eq_const.1 h w

/-- Rigid intensions that agree at one index are equal, which is the necessity of identity. -/
theorem IsConst.eq_of_apply_eq (hf : IsConst f) (hg : IsConst g) {w : W} (h : f w = g w) :
    f = g :=
  funext fun v ↦ (hf v w).trans (h.trans (hg w v))

theorem Injective.isConst_comp_iff {g : τ → τ'} (hg : Injective g) :
    IsConst (g ∘ f) ↔ IsConst f :=
  ⟨fun h w₁ w₂ ↦ hg (h w₁ w₂), fun h ↦ h.comp_left g⟩

end Function

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
theorem IsExtensionalAt.largeScope_eq_smallScope {O : (W → Prop) → W → Prop} {w : W}
    (h : IsExtensionalAt O w) (P : τ → W → Prop) (f : W → τ) :
    largeScope O P f w = smallScope O P f w :=
  largeScope_eq_smallScope_of_dependsOn (isExtensionalAt_iff_dependsOn.1 h)
    (Set.eqOn_singleton.2 rfl) P
