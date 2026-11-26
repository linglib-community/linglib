module

public import Linglib.Core.Relation.SetRel
public import Mathlib.Order.GaloisConnection.Basic
public import Mathlib.Order.Hom.Set
public import Mathlib.Logic.Function.DependsOn

/-!
# Necessity and possibility along a relation

In Kripke semantics a proposition is *necessary* at a world when it is true at every world
accessible from it, and *possible* when it is true at some; the accessibility relation fixes the
kind of modality. This file defines the two operators along a relation `R`, on propositions
`W → Prop`: `□[R] p w` says that `p` holds at every `v` with `w ~[R] v`, and `◇[R] p w` that it
holds at some. Possibility is left adjoint to necessity along the converse relation, so necessity
preserves meets and possibility joins, and both compose as relations do.

## Main definitions

* `ModalLogic.Box`, `ModalLogic.Diamond`: necessity and possibility along a relation, with
  notation `□[R]` and `◇[R]`.

## Main results

* `ModalLogic.box_eq_core`, `ModalLogic.diamond_eq_preimage`: the operators are mathlib's core
  and preimage of a relation.
* `ModalLogic.setOf_box`, `ModalLogic.setOf_diamond`: the same for propositions held as sets.
* `ModalLogic.diamond_box_gc`: possibility is left adjoint to necessity along the converse.
* `ModalLogic.diamond_le_diamond_iff`: possibility is monotone in the relation, and reflects
  inclusion.
* `ModalLogic.dependsOn_box_iff`: necessity at a world depends on exactly the worlds it accesses.

## Implementation notes

Necessity and possibility are operators on propositions `W → Prop` along a relation
`R : SetRel W' W`, which may relate two types. They are mathlib's `SetRel.core` and
`SetRel.preimage` conjugated by `Set.memOrderIso`, the isomorphism between sets and predicates.
The adjunction is `SetRel.image_core_gc` carried across it, and the composition, identity and
conjunction lemmas are `SetRel.core_comp`, `SetRel.preimage_comp`, `SetRel.core_id` and
`SetRel.core_inter`; propositions stated as sets use mathlib's lemmas directly. The axioms of
modal logic and the frame conditions they define are in `Logic/Modal/Definability.lean`.

## References

* [kripke-1963]
* [hintikka-1962]
* [prior-1967]
-/

@[expose] public section

namespace ModalLogic

open SetRel

/-! ### Box and diamond -/

section Operators

variable {W W' : Type*} (R : SetRel W' W) (p : W → Prop) (w : W')

/-- `p` is necessary at `w` along `R` when it holds at every world `w` accesses. -/
def Box : Prop := ∀ v, w ~[R] v → p v

/-- `p` is possible at `w` along `R` when it holds at some world `w` accesses. -/
def Diamond : Prop := ∃ v, w ~[R] v ∧ p v

@[inherit_doc] scoped notation:max "□[" R "]" => Box R
@[inherit_doc] scoped notation:max "◇[" R "]" => Diamond R

variable {R p w}

theorem box_iff : □[R] p w ↔ ∀ v, w ~[R] v → p v := .rfl

theorem diamond_iff : ◇[R] p w ↔ ∃ v, w ~[R] v ∧ p v := .rfl

theorem box_iff_mem_core : □[R] p w ↔ w ∈ R.core {v | p v} := .rfl

theorem diamond_iff_mem_preimage : ◇[R] p w ↔ w ∈ R.preimage {v | p v} :=
  exists_congr fun _ ↦ and_comm

variable (R) in
/-- Necessity along `R` is the core of `R`, read on predicates. -/
theorem box_eq_core : □[R] = Set.memOrderIso ∘ R.core ∘ Set.memOrderIso.symm := rfl

variable (R) in
/-- Possibility along `R` is the preimage of `R`, read on predicates. -/
theorem diamond_eq_preimage : ◇[R] = Set.memOrderIso ∘ R.preimage ∘ Set.memOrderIso.symm :=
  funext fun _ ↦ funext fun _ ↦ propext diamond_iff_mem_preimage

variable (R p) in
/-- The worlds where `p` is necessary are the core of the worlds where `p` holds. -/
theorem setOf_box : {w | □[R] p w} = R.core {v | p v} := rfl

variable (R p) in
/-- The worlds where `p` is possible are the preimage of the worlds where `p` holds. -/
theorem setOf_diamond : {w | ◇[R] p w} = R.preimage {v | p v} :=
  Set.ext fun _ ↦ diamond_iff_mem_preimage

theorem box_mem_iff {s : Set W} : □[R] (· ∈ s) w ↔ w ∈ R.core s := .rfl

theorem diamond_mem_iff {s : Set W} : ◇[R] (· ∈ s) w ↔ w ∈ R.preimage s :=
  diamond_iff_mem_preimage

@[simp] theorem not_box : ¬ □[R] p w ↔ ◇[R] (fun v ↦ ¬ p v) w := by
  simp [Box, Diamond, not_forall]

@[simp] theorem not_diamond : ¬ ◇[R] p w ↔ □[R] (fun v ↦ ¬ p v) w := by
  simp [Box, Diamond, not_and]

variable (R) in
/-- Necessity distributes over conjunction. For belief this is [hintikka-1962]'s principle that
*a* believes *A and B* exactly when *a* believes *A* and *a* believes *B*. -/
theorem box_and (q : W → Prop) : □[R] (fun v ↦ p v ∧ q v) w ↔ □[R] p w ∧ □[R] q w :=
  Set.ext_iff.1 (core_inter R {v | p v} {v | q v}) w

variable (R) in
theorem box_iUnion {ι : Sort*} (R : ι → SetRel W' W) : □[⋃ i, R i] p w ↔ ∀ i, □[R i] p w := by
  simp only [Box, Set.mem_iUnion, forall_exists_index]
  exact forall_comm

theorem box_union (S : SetRel W' W) : □[R ∪ S] p w ↔ □[R] p w ∧ □[S] p w := by
  simp only [Box, Set.mem_union, or_imp, forall_and]

theorem box_id {u : W} : □[SetRel.id] p u ↔ p u :=
  Set.ext_iff.1 (core_id {v | p v}) u

/-- Necessity along a union of relations is the meet of necessity along each. -/
theorem box_sup (R S : SetRel W' W) : □[R ⊔ S] = □[R] ⊓ □[S] :=
  funext fun _ ↦ funext fun _ ↦ propext (box_union S)

/-- Necessity along the identity relation is the identity. -/
theorem box_id_eq_id : □[(SetRel.id : SetRel W W)] = id :=
  funext fun _ ↦ funext fun _ ↦ propext box_id

theorem box_congr_left {w'' : W'} (h : ∀ v, w ~[R] v ↔ w'' ~[R] v) : □[R] p w ↔ □[R] p w'' :=
  forall_congr' fun v ↦ imp_congr_left (h v)

/-- A proposition that does not vary with the world is necessary at `w` when it is true or `w`
accesses no world. -/
theorem box_const {c : Prop} : □[R] (fun _ ↦ c) w ↔ (w ∈ R.dom → c) :=
  ⟨fun h ⟨v, hv⟩ ↦ h v hv, fun h v hv ↦ h ⟨v, hv⟩⟩

/-- A proposition that does not vary with the world is possible at `w` when it is true and `w`
accesses some world. -/
theorem diamond_const {c : Prop} : ◇[R] (fun _ ↦ c) w ↔ w ∈ R.dom ∧ c :=
  ⟨fun ⟨v, hv, hc⟩ ↦ ⟨⟨v, hv⟩, hc⟩, fun ⟨⟨v, hv⟩, hc⟩ ↦ ⟨v, hv, hc⟩⟩

/-- Necessity at `w` depends on its argument at a set of worlds exactly when the set contains every
world `w` accesses. -/
theorem dependsOn_box_iff {s : Set W} : DependsOn (□[R] · w) s ↔ {v | w ~[R] v} ⊆ s := by
  refine ⟨fun h v hv ↦ by_contra fun hvs ↦ ?_, fun h p q hpq ↦
    propext <| forall₂_congr fun v hv ↦ iff_of_eq (hpq v (h hv))⟩
  have := @h (· ≠ v) (fun _ ↦ True) fun u hu ↦ eq_true (ne_of_mem_of_not_mem hu hvs)
  exact this.mpr (fun _ _ ↦ trivial) v hv rfl

end Operators

/-! ### The Galois connection and normality -/

section Galois

variable {W W' : Type*} (R : SetRel W' W) {p q : W → Prop}

/-- `◇` along `R` is left adjoint to `□` along the converse relation. -/
theorem diamond_box_gc : GaloisConnection ◇[R] □[R.inv] := by
  rw [diamond_eq_preimage, box_eq_core]
  exact (Set.memOrderIso.symm.to_galoisConnection.compose (image_core_gc (R := R.inv))).compose
    Set.memOrderIso.to_galoisConnection

theorem box_mono : Monotone □[R] := by
  simpa using (diamond_box_gc R.inv).monotone_u

theorem diamond_mono : Monotone ◇[R] :=
  (diamond_box_gc R).monotone_l

theorem box_inf : □[R] (p ⊓ q) = □[R] p ⊓ □[R] q := by
  simpa using (diamond_box_gc R.inv).u_inf

theorem diamond_sup : ◇[R] (p ⊔ q) = ◇[R] p ⊔ ◇[R] q :=
  (diamond_box_gc R).l_sup

theorem box_top : □[R] ⊤ = ⊤ := by
  simpa using (diamond_box_gc R.inv).u_top

variable {R} in
/-- Possibility along `R` entails possibility along `S` exactly when `S` contains `R`, so a law
between possibilities defines an inclusion of relations. -/
theorem diamond_le_diamond_iff {S : SetRel W' W} : Diamond R ≤ Diamond S ↔ R ⊆ S where
  mp h := fun ⟨w, v⟩ hwv ↦ match h (· = v) w ⟨v, hwv, rfl⟩ with | ⟨_, hS, rfl⟩ => hS
  mpr h _ _ := fun ⟨v, hwv, hv⟩ ↦ ⟨v, h hwv, hv⟩

/-- Along any relation $p$ entails $\Box_{R^{-1}} \Diamond_R p$, the unit of the adjunction. For
tense this is the mixing principle $A \supset GPA$ that [prior-1967] takes from Ockham: what is the
case will always have been the case. -/
theorem le_box_inv_diamond (p : W → Prop) : p ≤ □[R.inv] (◇[R] p) :=
  (diamond_box_gc R).le_u_l p

end Galois

variable {W : Type*} (R : SetRel W W)

theorem box_comp (S : SetRel W W) (p : W → Prop) : □[R ○ S] p = □[R] (□[S] p) :=
  congrArg Set.memOrderIso (core_comp R S _)

theorem diamond_comp (S : SetRel W W) (p : W → Prop) : ◇[R ○ S] p = ◇[R] (◇[S] p) := by
  simp only [diamond_eq_preimage, Function.comp_apply, OrderIso.symm_apply_apply, preimage_comp]

/-- If every `A`-predecessor of a world that `C`-accesses a second world `B`-accesses a world
the second one `D`-accesses, then what is possibly necessary is necessarily possible. -/
theorem diamond_box_le_box_diamond {A B C D : SetRel W W} (h : A.inv ○ C ⊆ B ○ D.inv)
    (p : W → Prop) : ◇[A] (□[B] p) ≤ □[C] (◇[D] p) :=
  fun i ⟨k, hik, hk⟩ j hij ↦
    let ⟨m, hkm, hjm⟩ := h (show (k, j) ∈ A.inv ○ C from ⟨i, hik, hij⟩)
    ⟨m, hjm, hk m hkm⟩

end ModalLogic
