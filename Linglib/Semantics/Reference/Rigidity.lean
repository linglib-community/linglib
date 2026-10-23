module

public import Mathlib.Logic.Function.Basic
public import Mathlib.Data.Set.Image

/-!
# Rigid designation

An intension over an index type `W` is a function `W → τ`, and it is *rigid* when it takes
the same value at every index: a rigid designator in the sense of Kripke, a stable content
in the sense of Kaplan. Rigidity is subsingletonness of the range
(`isRigid_iff_subsingleton_range`), and rigidity on a set is subsingletonness of the image
(`isRigidOn_iff_subsingleton_image`); the closure properties are those of `Set.Subsingleton`.
Rigid intensions that agree at one index agree everywhere, which is the necessity of identity.

## Main definitions

* `IsRigid f`, `IsRigidOn f S`: constancy of `f : W → τ` everywhere, or on `S`.

## Main results

* `isRigid_iff_subsingleton_range`, `isRigidOn_iff_subsingleton_image`: the mathlib face.
* `isRigid_of_subsingleton`: over a single index every intension is rigid.
* `IsRigid.eq_of_apply_eq`: rigid intensions that agree at one index are equal.
* `IsRigid.map`, `IsRigid.of_comp_injective`, `IsRigid.precomp`, `IsRigidOn.precomp`,
  `IsRigidOn.mono`: closure under composition and restriction.

## References

* [S. Kripke, *Naming and Necessity* (1980)][kripke-1980]
* [D. Kaplan, *Demonstratives* (1989)][kaplan-1989]
* [D. Gallin, *Intensional and Higher-Order Modal Logic* (1975)][gallin-1975]
-/

@[expose] public section

variable {W W' τ τ' : Type*} {f : W → τ} {S T : Set W}

/-- An intension is rigid when it takes the same value at every index. -/
def IsRigid (f : W → τ) : Prop := ∀ w₁ w₂, f w₁ = f w₂

/-- An intension is rigid on `S` when it takes the same value at every index in `S`. -/
def IsRigidOn (f : W → τ) (S : Set W) : Prop := ∀ w₁ ∈ S, ∀ w₂ ∈ S, f w₁ = f w₂

theorem isRigid_iff_subsingleton_range : IsRigid f ↔ (Set.range f).Subsingleton := by
  simp [IsRigid, Set.Subsingleton]

theorem isRigidOn_iff_subsingleton_image : IsRigidOn f S ↔ (f '' S).Subsingleton := by
  simp [IsRigidOn, Set.Subsingleton]

theorem isRigid_const (x : τ) : IsRigid fun _ : W => x := fun _ _ => rfl

theorem isRigid_of_subsingleton [Subsingleton W] (f : W → τ) : IsRigid f :=
  isRigid_iff_subsingleton_range.2 (Set.subsingleton_range f)

theorem IsRigidOn.mono (h : IsRigidOn f S) (hT : T ⊆ S) : IsRigidOn f T :=
  fun w₁ hw₁ w₂ hw₂ => h w₁ (hT hw₁) w₂ (hT hw₂)

theorem IsRigid.isRigidOn {f : W → τ} (h : IsRigid f) (S : Set W) : IsRigidOn f S :=
  fun w₁ _ w₂ _ => h w₁ w₂

theorem IsRigid.eq_const {f : W → τ} (h : IsRigid f) (w : W) : f = fun _ => f w :=
  funext fun w' => h w' w

theorem IsRigid.eq_of_apply_eq {f g : W → τ} (hf : IsRigid f) (hg : IsRigid g) {w : W}
    (h : f w = g w) : f = g :=
  funext fun w' => (hf w' w).trans (h.trans (hg w w'))

theorem const_ne_of_not_isRigid {f : W → τ} (h : ¬ IsRigid f) (w : W) :
    (fun _ => f w) ≠ f :=
  fun e => h (e ▸ isRigid_const (f w))

theorem IsRigid.map {f : W → τ} (h : IsRigid f) (g : τ → τ') : IsRigid (g ∘ f) :=
  fun w₁ w₂ => congrArg g (h w₁ w₂)

theorem IsRigid.of_comp_injective {g : τ → τ'} (hg : Function.Injective g)
    (h : IsRigid (g ∘ f)) : IsRigid f :=
  fun w₁ w₂ => hg (h w₁ w₂)

theorem IsRigid.precomp {f : W → τ} (h : IsRigid f) (g : W' → W) : IsRigid (f ∘ g) :=
  fun w₁ w₂ => h (g w₁) (g w₂)

theorem IsRigidOn.precomp {f : W → τ} {S : Set W} (h : IsRigidOn f S) (g : W' → W) :
    IsRigidOn (f ∘ g) (g ⁻¹' S) :=
  fun w₁ hw₁ w₂ hw₂ => h (g w₁) hw₁ (g w₂) hw₂

