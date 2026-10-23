module

public import Linglib.Logic.PIP.Semantics

/-!
# Intensional models of PIP

This file defines the models of PIP whose atoms are worlds and entities. A
world is the singleton plurality of its atom, and a family of world-relative
relations on atoms is lifted distributively to relation symbols: a symbol holds
of a world and nonempty pluralities iff it holds at that world of every tuple
of their members, and it holds of nothing whose world argument is not a world.

## Main definitions

* `Atom`, `world` — worlds and entities as atoms; a world as a plurality.
* `Model.intensional` — the distributive lifting of world-relative relations.

## Main statements

* `Model.intensional_apply₁`, `Model.intensional_apply₂` — the lifting on one
  and two arguments.
* `Term.realize_sigma_world_eq` — a summation over worlds whose body relates each
  world to the value of a local: the plurality of the worlds so related to some
  plurality; `Term.realize_sigma_world_eq_of_distributive` — for a body distributive
  in that local.

## Implementation notes

A plurality of worlds or of entities is the image `Sum.inl '' s` or `Sum.inr '' s` of a set
of them, so that the values of summations and the modal relations between them, overlap
and inclusion, reduce to relations between those sets through the injectivity of
`Sum.inl` and `Sum.inr`.

## References

* [keshet-abney-2024]
* [abney-keshet-2025]
-/

@[expose] public section

namespace PIP

variable {V L : Type*} {P : ℕ → Type*}

/-- The atoms of an intensional model: worlds and entities. -/
abbrev Atom (W E : Type*) := W ⊕ E

variable {W E : Type*}

/-- A world as a singleton plurality. -/
def world (w : W) : Set (Atom W E) := {Sum.inl w}

theorem world_inj {w w' : W} : (world w : Set (Atom W E)) = world w' ↔ w = w' :=
  Set.singleton_eq_singleton_iff.trans Sum.inl_injective.eq_iff

/-- The intensional model of a family of relations on atoms at each world: a
relation symbol holds of a world and nonempty pluralities iff it holds at that
world of every tuple of their members, and of nothing whose world argument is
not a world. -/
def Model.intensional (rel : ∀ {n : ℕ}, P n → W → (Fin n → Atom W E) → Prop) :
    Model P (Atom W E) where
  I r Wp ts := ∃ w, Wp = world w ∧ (∀ i, (ts i).Nonempty) ∧
    ∀ as, (∀ i, as i ∈ ts i) → rel r w as

variable {rel : ∀ {n : ℕ}, P n → W → (Fin n → Atom W E) → Prop}

theorem Model.intensional_apply₁ (r : P 1) (Wp X : Set (Atom W E)) :
    (Model.intensional rel).I r Wp ![X] ↔
      ∃ w, Wp = world w ∧ X.Nonempty ∧ ∀ a ∈ X, rel r w ![a] := by
  simp only [Model.intensional, Fin.forall_fin_one, Fin.forall_fin_succ_pi,
    Fin.forall_fin_zero_pi, Fin.cons_zero, Matrix.cons_val_zero]
  rfl

theorem Model.intensional_apply₂ (r : P 2) (Wp X Y : Set (Atom W E)) :
    (Model.intensional rel).I r Wp ![X, Y] ↔
      ∃ w, Wp = world w ∧ X.Nonempty ∧ Y.Nonempty ∧
        ∀ a ∈ X, ∀ b ∈ Y, rel r w ![a, b] := by
  simp only [Model.intensional, Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    and_assoc]
  refine exists_congr fun w => and_congr_right fun _ => and_congr_right fun _ =>
    and_congr_right fun _ => ⟨fun H a ha b hb => H ![a, b] ⟨ha, hb⟩, fun H as h => ?_⟩
  rw [show as = ![as 0, as 1] from funext (Fin.forall_fin_two.2 ⟨rfl, rfl⟩)]
  exact H _ h.1 _ h.2

/-- The value of a summation over a world variable whose body, on the assignments
agreeing outside the summation variable and its locals, holds iff the variable is a
world standing in the relation `B` to the value of the local `y`: the worlds so
related to some plurality. -/
theorem Term.realize_sigma_world_eq [DecidableEq V] (M : Model P (Atom W E))
    (g : V → Set (Atom W E)) {x y : V} (hxy : y ≠ x) {φ : Formula V L P}
    {B : Set (Atom W E) → W → Prop}
    (hφ : ∀ g', Set.EqOn g' g {z | z ∉ φ.locals ∧ z ≠ x} →
      (Formula.Realize M g' φ ↔ ∃ w, g' x = world w ∧ B (g' y) w))
    (hy : y ∈ φ.locals) :
    Term.realize M g (.sigma x φ) = Sum.inl '' {w | ∃ Y, B Y w} := by
  rw [Term.realize_sigma_eq_of_mem_locals M g hxy
    (C := fun X Y => ∃ w, X = world w ∧ B Y w) hφ hy]
  ext a
  simp only [world, Set.mem_sUnion, Set.mem_ofPred_eq, Set.mem_image]
  exact ⟨fun ⟨_, ⟨_, w, rfl, hB⟩, ha⟩ => ⟨w, ⟨_, hB⟩, ha.symm⟩,
    fun ⟨w, ⟨Y, hB⟩, ha⟩ => ⟨_, ⟨Y, w, rfl, hB⟩, ha.symm⟩⟩

/-- A summation over worlds whose body is distributive in a local `y`, true of the nonempty
pluralities within `s w` at each world `w`: the worlds where `s w` is nonempty. -/
theorem Term.realize_sigma_world_eq_of_distributive [DecidableEq V] (M : Model P (Atom W E))
    (g : V → Set (Atom W E)) {x y : V} (hxy : y ≠ x) {φ : Formula V L P}
    {s : W → Set (Atom W E)}
    (hφ : ∀ g', Set.EqOn g' g {z | z ∉ φ.locals ∧ z ≠ x} →
      (Formula.Realize M g' φ ↔ ∃ w, g' x = world w ∧ (g' y).Nonempty ∧ g' y ⊆ s w))
    (hy : y ∈ φ.locals) :
    Term.realize M g (.sigma x φ) = Sum.inl '' {w | (s w).Nonempty} := by
  rw [Term.realize_sigma_world_eq M g hxy (B := fun Y w => Y.Nonempty ∧ Y ⊆ s w) hφ hy]
  congr 1
  ext w
  exact ⟨fun ⟨_, hY, hYs⟩ => hY.mono hYs, fun hs => ⟨_, hs, subset_rfl⟩⟩

end PIP
