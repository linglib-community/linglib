module

public import Mathlib.Logic.Function.DependsOn
public import Linglib.Logic.Modal.Defs

/-!
# Extensional operators

An operator on intensions is *extensional* at an index when the value it yields there depends only
on the extension of its argument at that index. Negation is extensional: whether *it is not
raining* is true at a world depends only on whether *it is raining* is true there. Necessity is
not, since whether *it must be raining* is true at a world depends on whether *it is raining* is
true at the worlds accessible from it. Among adjectives, which map properties to properties,
*gray* is extensional and *skillful* is not: where the cobblers are exactly the darts players, the
gray cobblers are the gray darts players, but the skillful cobblers need not be the skillful darts
players.

An operator is extensional exactly when it is
[a function on extensions applied index by index](##isExtensional_iff_exists_eq_piMap). At an
index where it is extensional, an operator
[gives the same value on an intension and on the constant intension with the same
extension](##isExtensionalAt_iff_forall_const), and so
[cannot tell a variable it binds from one fixed at that index](##isExtensionalAt_iff_forall_diag):
a situation variable bound under negation reads as if it were free. The truth-functional
connectives are extensional, and so are composites of extensional operators.

In general the value of an operator at an index depends on its argument at some set of indices,
and the operator is extensional there when that set can be taken to be the index alone. Necessity
in a Kripke frame depends at a world on
[exactly the worlds accessible from it](##ModalLogic.dependsOn_box_iff), so it is
[extensional only at a world that accesses no world but itself](##isExtensionalAt_box_iff).

## Main definitions

* `Montague.IsExtensionalAt O w`: the value of `O` at `w` depends only on the extension of its
  argument at `w`.
* `Montague.IsExtensional O`: `O` is extensional at every index.

## Implementation notes

Extensionality at `w` is the statement that `O · w` factors through evaluation at `w`, and that it
depends, in the sense of mathlib's `DependsOn`, on the coordinate `w` alone. Kamp's condition for
an extensional adjective takes a single function on extensions for every index; the function here
may vary with the index, as in his gloss of the condition and as his claim that every predicative
adjective is extensional requires.

## References

* [kamp-1975]
* [zimmermann-2026]
-/

@[expose] public section

namespace Montague

open Function

variable {W α β γ δ : Type*}

/-- `O` is extensional at `w` when its value at `w` depends on its argument only through the
argument's extension at `w`. -/
def IsExtensionalAt (O : (W → α) → W → β) (w : W) : Prop :=
  ∀ ⦃p q : W → α⦄, p w = q w → O p w = O q w

/-- `O` is extensional when it is extensional at every index. -/
def IsExtensional (O : (W → α) → W → β) : Prop :=
  ∀ w, IsExtensionalAt O w

variable {O : (W → α) → W → β} {w : W}

theorem isExtensionalAt_iff_factorsThrough :
    IsExtensionalAt O w ↔ FactorsThrough (O · w) (· w) :=
  .rfl

theorem isExtensionalAt_iff_dependsOn : IsExtensionalAt O w ↔ DependsOn (O · w) {w} := by
  simp [IsExtensionalAt, DependsOn]

theorem not_isExtensionalAt_iff : ¬ IsExtensionalAt O w ↔ ∃ p q, p w = q w ∧ O p w ≠ O q w := by
  simp [IsExtensionalAt]

/-- An operator is extensional at `w` exactly when it does not distinguish its argument from the
constant intension with the same extension at `w`. -/
theorem isExtensionalAt_iff_forall_const :
    IsExtensionalAt O w ↔ ∀ p, O p w = O (fun _ ↦ p w) w :=
  ⟨fun h _ ↦ h rfl, fun h p q hpq ↦ by rw [h p, h q, hpq]⟩

theorem isExtensionalAt_iff_exists : IsExtensionalAt O w ↔ ∃ f : α → β, ∀ p, O p w = f (p w) :=
  ⟨fun h ↦ ⟨fun a ↦ O (fun _ ↦ a) w, fun _ ↦ h rfl⟩, fun ⟨f, hf⟩ p q hpq ↦ by rw [hf, hf, hpq]⟩

/-- An operator is extensional exactly when it applies a function on extensions at each index. -/
theorem isExtensional_iff_exists_eq_piMap : IsExtensional O ↔ ∃ f : W → α → β, O = Pi.map f :=
  ⟨fun h ↦ ⟨fun w a ↦ O (fun _ ↦ a) w, funext₂ fun _ w ↦ h w rfl⟩,
    fun ⟨f, hf⟩ w _ _ hpq ↦ hf ▸ congrArg (f w) hpq⟩

theorem isExtensional_piMap (f : W → α → β) : IsExtensional (Pi.map f) :=
  isExtensional_iff_exists_eq_piMap.2 ⟨f, rfl⟩

/-- An operator is extensional at `w` exactly when it does not distinguish an argument whose index
it binds, `fun v ↦ g v v`, from the same argument with the index fixed at `w`, `g w`. -/
theorem isExtensionalAt_iff_forall_diag :
    IsExtensionalAt O w ↔ ∀ g : W → W → α, O (fun v ↦ g v v) w = O (g w) w :=
  ⟨fun h _ ↦ h rfl, fun h ↦ isExtensionalAt_iff_forall_const.2 fun p ↦ h fun u _ ↦ p u⟩

/-! ### Necessity -/

open ModalLogic SetRel in
theorem isExtensionalAt_box_iff {R : SetRel W W} :
    IsExtensionalAt □[R] w ↔ ∀ v, w ~[R] v → v = w := by
  rw [isExtensionalAt_iff_dependsOn, dependsOn_box_iff, Set.subset_singleton_iff]
  rfl

/-! ### Closure -/

theorem isExtensionalAt_id : IsExtensionalAt (id : (W → α) → W → α) w :=
  fun _ _ ↦ id

theorem isExtensionalAt_const (c : W → β) : IsExtensionalAt (fun _ : W → α ↦ c) w :=
  fun _ _ _ ↦ rfl

theorem isExtensionalAt_not : IsExtensionalAt (fun (p : W → Prop) v ↦ ¬ p v) w :=
  fun _ _ ↦ congrArg Not

namespace IsExtensionalAt

theorem comp {O' : (W → β) → W → γ} (h' : IsExtensionalAt O' w) (h : IsExtensionalAt O w) :
    IsExtensionalAt (O' ∘ O) w :=
  fun _ _ hpq ↦ h' (h hpq)

theorem comp_left (h : IsExtensionalAt O w) (g : β → γ) :
    IsExtensionalAt (fun p v ↦ g (O p v)) w :=
  fun _ _ hpq ↦ congrArg g (h hpq)

theorem comp₂ {O' : (W → α) → W → γ} (h : IsExtensionalAt O w) (h' : IsExtensionalAt O' w)
    (g : β → γ → δ) : IsExtensionalAt (fun p v ↦ g (O p v) (O' p v)) w :=
  fun _ _ hpq ↦ congrArg₂ g (h hpq) (h' hpq)

theorem not {O : (W → α) → W → Prop} (h : IsExtensionalAt O w) :
    IsExtensionalAt (fun p v ↦ ¬ O p v) w :=
  h.comp_left Not

theorem and {O O' : (W → α) → W → Prop} (h : IsExtensionalAt O w) (h' : IsExtensionalAt O' w) :
    IsExtensionalAt (fun p v ↦ O p v ∧ O' p v) w :=
  h.comp₂ h' And

theorem or {O O' : (W → α) → W → Prop} (h : IsExtensionalAt O w) (h' : IsExtensionalAt O' w) :
    IsExtensionalAt (fun p v ↦ O p v ∨ O' p v) w :=
  h.comp₂ h' Or

end IsExtensionalAt

end Montague
