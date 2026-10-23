module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Piecewise

/-!
# The DRT box

In discourse representation theory, a box contains two pieces of information:
a universe of discourse referents, and a set of conditions recording what has
been established about them. Boxes can be nested, and different theories
instantiate conditions in different ways
([venhuizen-bos-hendriks-brouwer-2018]; [liu-2021]). This file defines boxes and the
extension relation of a box, between embeddings that agree off its universe.

## Implementation notes

An embedding of discourse referents into a model is a total function `V → M`; the
textbook's are partial, so a sub-box *extends* its input on its universe, rendered here as
agreement off the universe (`Box.Extends`).
-/

@[expose] public section

namespace DRT

universe w x

variable {V : Type w} {C : Type x} {M : Type*}

/-- A DRT *box*, generic over the condition type `C`; `DRS` instantiates `C`
at `Condition L V`. -/
@[ext] structure Box (V : Type w) (C : Type x) where
  /-- The universe `U`: the discourse referents the box introduces. -/
  referents : Finset V
  /-- The box's conditions. -/
  conditions : List C

namespace Box

/-! ### The extension relation -/

/-- `K.Extends f g` (written `f [K] g`) if the output embedding `g` differs
from the input `f` at most on `K`'s universe — the total-assignment rendering
of "`f ⊆ g` and `Dom g = Dom f ∪ U_K`". -/
def Extends (K : Box V C) (f g : V → M) : Prop := ∀ x ∉ K.referents, g x = f x

section Extends

variable {K : Box V C} {f f₁ f₂ g : V → M}

theorem Extends.refl (K : Box V C) (f : V → M) : K.Extends f f := fun _ _ => rfl

variable [DecidableEq V]

theorem extends_piecewise (K : Box V C) (f g : V → M) :
    K.Extends f (K.referents.piecewise g f) :=
  fun _ hx => Finset.piecewise_eq_of_notMem _ _ _ hx

theorem eqOn_piecewise_of_extends (h₁ : K.Extends f₁ g) {S : Set V}
    (h : Set.EqOn f₁ f₂ (S \ ↑K.referents)) : Set.EqOn g (K.referents.piecewise g f₂) S :=
  fun x _ => by grind [Extends, Set.EqOn, Finset.piecewise_eq_of_mem, Finset.piecewise_eq_of_notMem]

theorem exists_extends_imp (K : Box V C) {S : Set V} {P : (V → M) → Prop}
    (hP : ∀ g g', Set.EqOn g g' S → P g → P g') (h : Set.EqOn f₁ f₂ (S \ ↑K.referents)) :
    (∃ g, K.Extends f₁ g ∧ P g) → ∃ g, K.Extends f₂ g ∧ P g := fun ⟨g, hg, hPg⟩ =>
  ⟨_, extends_piecewise K f₂ g, hP _ _ (eqOn_piecewise_of_extends hg h) hPg⟩

theorem exists_extends_congr (K : Box V C) {S : Set V} {P : (V → M) → Prop}
    (hP : ∀ g g', Set.EqOn g g' S → P g → P g') (h : Set.EqOn f₁ f₂ (S \ ↑K.referents)) :
    (∃ g, K.Extends f₁ g ∧ P g) ↔ ∃ g, K.Extends f₂ g ∧ P g :=
  ⟨exists_extends_imp K hP h, exists_extends_imp K hP h.symm⟩

theorem forall_extends_imp (K : Box V C) {S : Set V} {P : (V → M) → Prop}
    (hP : ∀ g g', Set.EqOn g g' S → P g → P g') (h : Set.EqOn f₁ f₂ (S \ ↑K.referents)) :
    (∀ g, K.Extends f₁ g → P g) → ∀ g, K.Extends f₂ g → P g := fun H g hg =>
  hP _ g (eqOn_piecewise_of_extends hg h.symm).symm (H _ (extends_piecewise K f₁ g))

theorem forall_extends_congr (K : Box V C) {S : Set V} {P : (V → M) → Prop}
    (hP : ∀ g g', Set.EqOn g g' S → P g → P g') (h : Set.EqOn f₁ f₂ (S \ ↑K.referents)) :
    (∀ g, K.Extends f₁ g → P g) ↔ ∀ g, K.Extends f₂ g → P g :=
  ⟨forall_extends_imp K hP h, forall_extends_imp K hP h.symm⟩

end Extends

end Box

end DRT
