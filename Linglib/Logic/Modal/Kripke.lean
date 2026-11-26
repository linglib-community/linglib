module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Logic.Relation
public import Linglib.Core.Data.Set.Functor
public import Linglib.Logic.Modal.Basic

/-!
# Kripke models

A Kripke model gives each world the finite set of worlds it accesses and each atom the worlds
at which it is true. `KripkeModel.accessible` reads the successor sets as the relation that `□`
and `◇` of `Logic/Modal/Basic.lean` take.

A relation between the worlds of two models is a bisimulation, `KripkeModel.IsBisimulation`,
when related worlds make the same atoms true and each successor of one is related to a
successor of the other. The converse of a bisimulation is one (`IsBisimulation.symm`), and a
world reached from one of two related worlds is related to a world reached from the other
(`IsBisimulation.exists_reflTransGen`).

## Implementation notes

The sources take any relation `R ⊆ W × W` and a valuation `V : X → ℘(W)`
([aloni-anttila-yang-2024] Definition 2.2). Successor sets here are `Finset`s, since the team
logics of `Logic/Team/` evaluate subformulas on `R[w]` as a team; frames are therefore
image-finite. The valuation is `Prop`-valued, and decision procedures for support take
`[DecidableRel M.val]`.

## References

* [aloni-anttila-yang-2024] Aloni, Anttila and Yang, State-based Modal Logics for Free Choice
* [blackburn-derijke-venema-2001] Blackburn, de Rijke and Venema, Modal Logic
-/

@[expose] public section

namespace ModalLogic

/-- A **Kripke model** over worlds `W` and atoms `Atom` has successor sets and a valuation. -/
structure KripkeModel (W : Type*) (Atom : Type*) where
  /-- `access w` is the set of worlds accessible from `w`. -/
  access : W → Finset W
  /-- `val p w` says that the atom `p` is true at the world `w`. -/
  val : Atom → W → Prop

variable {W W' : Type*} {Atom : Type*}

/-- The disjoint union of two Kripke models. -/
def KripkeModel.sum (M : KripkeModel W Atom) (M' : KripkeModel W' Atom) :
    KripkeModel (W ⊕ W') Atom where
  access := Sum.elim (fun w ↦ (M.access w).map .inl) (fun w ↦ (M'.access w).map .inr)
  val p := Sum.elim (M.val p) (M'.val p)

section Sum

variable {M : KripkeModel W Atom} {M' : KripkeModel W' Atom}

@[simp] theorem KripkeModel.sum_access_inl (w : W) :
    (M.sum M').access (.inl w) = (M.access w).map .inl := rfl

@[simp] theorem KripkeModel.sum_access_inr (w : W') :
    (M.sum M').access (.inr w) = (M'.access w).map .inr := rfl

@[simp] theorem KripkeModel.sum_val_inl (p : Atom) (w : W) :
    (M.sum M').val p (.inl w) ↔ M.val p w := .rfl

@[simp] theorem KripkeModel.sum_val_inr (p : Atom) (w : W') :
    (M.sum M').val p (.inr w) ↔ M'.val p w := .rfl

end Sum

open SetRel in
/-- In the accessibility relation of `M`, `v` is accessible from `w` when `v ∈ M.access w`.
This is the relation that `□` and `◇` of `Logic/Modal/Basic.lean` take. -/
def KripkeModel.accessible (M : KripkeModel W Atom) : SetRel W W :=
  .ofSuccessors fun w ↦ ↑(M.access w)

open SetRel in
@[simp] theorem KripkeModel.mem_accessible {M : KripkeModel W Atom} {w v : W} :
    w ~[M.accessible] v ↔ v ∈ M.access w := .rfl

open SetRel in
instance [DecidableEq W] (M : KripkeModel W Atom) (w v : W) : Decidable (w ~[M.accessible] v) :=
  inferInstanceAs (Decidable (v ∈ M.access w))

/-! ### Bisimulation -/

/-- A relation between the worlds of two Kripke models is a **bisimulation** when related worlds
make the same atoms true and their successor sets are related by its lifting. -/
structure KripkeModel.IsBisimulation (M : KripkeModel W Atom) (M' : KripkeModel W' Atom)
    (r : W → W' → Prop) : Prop where
  /-- Related worlds make the same atoms true. -/
  val_iff : ∀ ⦃w w'⦄, r w w' → ∀ p, M.val p w ↔ M'.val p w'
  /-- Each successor of one of two related worlds is related to a successor of the other. -/
  liftRel_access : ∀ ⦃w w'⦄, r w w' → Set.LiftRel r ↑(M.access w) ↑(M'.access w')

namespace KripkeModel.IsBisimulation

variable {M : KripkeModel W Atom} {M' : KripkeModel W' Atom} {r : W → W' → Prop}
  {w : W} {w' : W'}

/-- The converse of a bisimulation is a bisimulation. -/
protected theorem symm (h : M.IsBisimulation M' r) : M'.IsBisimulation M (Function.swap r) :=
  ⟨fun _ _ hr p ↦ (h.val_iff hr p).symm, fun _ _ hr ↦ Set.liftRel_swap.2 (h.liftRel_access hr)⟩

/-- A world reached from one of two related worlds is related to a world reached from the
other. -/
theorem exists_reflTransGen (h : M.IsBisimulation M' r) (hr : r w w') {u : W}
    (hu : Relation.ReflTransGen (fun a b ↦ b ∈ M.access a) w u) :
    ∃ u', Relation.ReflTransGen (fun a b ↦ b ∈ M'.access a) w' u' ∧ r u u' := by
  induction hu with
  | refl => exact ⟨w', .refl, hr⟩
  | tail _ hbc ih =>
    obtain ⟨b', hb', hrb⟩ := ih
    obtain ⟨hforth, -⟩ := h.liftRel_access hrb
    obtain ⟨c', hc', hrc⟩ := hforth _ hbc
    exact ⟨c', hb'.tail hc', hrc⟩

end KripkeModel.IsBisimulation

end ModalLogic
