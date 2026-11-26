/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Logic.Modal.Defs

/-!
# Modal axioms and the frame conditions they define

An axiom of modal logic, read as an inequality between operators on propositions, holds along a
relation exactly when the relation has a certain property: T when it is reflexive, D when it is
serial, B when it is symmetric, 4 when it is transitive and 5 when it is Euclidean. Required at
one world, excluded middle `□p ∨ □¬p` holds exactly when the world accesses at most one world,
and Negation Swap `□¬p ↔ ¬□p` exactly when it accesses one, so that Negation Swap holds
everywhere exactly when the relation is the graph of a function.

For two unrelated relations, the schema `p → □[R] ◇[S] p` is valid exactly when the converse of
`R` lies in `S`, and `◇[S]` is left adjoint to `□[R]` exactly when `S` is the converse of `R`.
With `R` the relation of the future operators and `S` that of the past operators, these are the
two interaction axioms of the minimal tense logic, which together say that past and future run
along converse relations ([goranko-2023]).

## Main definitions

* `ModalLogic.IsSerial`, `ModalLogic.IsEuclidean`: the frame conditions of D and 5.

## Main results

* `ModalLogic.box_T_iff`, `ModalLogic.box_D_iff`, `ModalLogic.box_B_iff`,
  `ModalLogic.box_four_iff`, `ModalLogic.box_five_iff`: the five classical correspondences.
* `ModalLogic.box_compl_eq_iff`: Negation Swap defines the graphs of functions.
* `ModalLogic.id_le_box_comp_diamond_iff`: `p → □[R] ◇[S] p` is valid iff `R.inv ⊆ S`.
* `ModalLogic.gc_diamond_box_iff`: `◇[S]` is left adjoint to `□[R]` iff `R.inv = S`.

## Implementation notes

Reflexivity, symmetry and transitivity are mathlib's `SetRel.IsRefl`, `SetRel.IsSymm` and
`SetRel.IsTrans`.

## References

* [blackburn-derijke-venema-2001]
* [prior-1967]
* [goranko-2023]
-/

@[expose] public section

namespace ModalLogic

open SetRel

section Frame

variable {W : Type*} (R : SetRel W W)

/-! ### Frame conditions -/

/-- `R` is *serial* when every world accesses some world. -/
class IsSerial : Prop where
  serial : ∀ w, ∃ v, w ~[R] v

/-- `R` is *Euclidean* when any two worlds accessed from one world access each other. -/
class IsEuclidean : Prop where
  eucl : ∀ w v u, w ~[R] v → w ~[R] u → v ~[R] u

variable {R}

instance : IsEuclidean (.univ : SetRel W W) := ⟨fun _ _ _ _ _ ↦ trivial⟩

/-- Reflexive relations are serial. -/
instance [R.IsRefl] : IsSerial R := ⟨fun w ↦ ⟨w, R.rfl⟩⟩

/-- A composite of serial relations is serial. -/
instance {S : SetRel W W} [IsSerial R] [IsSerial S] : IsSerial (R ○ S) where
  serial w := let ⟨v, hv⟩ := IsSerial.serial (R := R) w; let ⟨u, hu⟩ := IsSerial.serial (R := S) v
    ⟨u, v, hv, hu⟩

/-- Reflexive and Euclidean implies symmetric. -/
instance [R.IsRefl] [IsEuclidean R] : R.IsSymm where
  symm w v h := IsEuclidean.eucl w v w h R.rfl

/-- Reflexive and Euclidean implies transitive. -/
instance [R.IsRefl] [IsEuclidean R] : R.IsTrans where
  trans w v u hwv hvu := IsEuclidean.eucl v w u (IsEuclidean.eucl w v w hwv R.rfl) hvu

/-- Symmetric and transitive implies Euclidean. -/
instance [R.IsSymm] [R.IsTrans] : IsEuclidean R where
  eucl _ _ _ hwv hwu := R.trans (R.symm hwv) hwu

/-! ### Axiom correspondence -/

variable {p q : W → Prop} {w : W}

theorem box_K (hpq : □[R] (fun v ↦ p v → q v) w) (hp : □[R] p w) : □[R] q w :=
  fun v hwv ↦ hpq v hwv (hp v hwv)

theorem box_T [R.IsRefl] (h : □[R] p w) : p w := h w R.rfl

theorem box_D [IsSerial R] (h : □[R] p w) : ◇[R] p w :=
  let ⟨v, hwv⟩ := IsSerial.serial (R := R) w; ⟨v, hwv, h v hwv⟩

/-- If `w` accesses some world along both `R` and `S`, then necessity along `R` at `w` entails
possibility along `S`; `box_D` is the case `S = R`. -/
theorem diamond_of_box {S : SetRel W W} (h : ◇[R] (w ~[S] ·) w) (hp : □[R] p w) : ◇[S] p w :=
  let ⟨v, hR, hS⟩ := h; ⟨v, hS, hp v hR⟩

theorem box_B [R.IsSymm] (h : p w) : □[R] (◇[R] p) w := fun _ hwv ↦ ⟨w, R.symm hwv, h⟩

theorem box_four [R.IsTrans] (h : □[R] p w) : □[R] (□[R] p) w :=
  fun _ hwv u hvu ↦ h u (R.trans hwv hvu)

theorem diamond_four [R.IsTrans] (h : ◇[R] (◇[R] p) w) : ◇[R] p w :=
  let ⟨_, hwv, u, hvu, hu⟩ := h; ⟨u, R.trans hwv hvu, hu⟩

theorem box_five [IsEuclidean R] (h : ◇[R] p w) : □[R] (◇[R] p) w :=
  let ⟨u, hwu, hpu⟩ := h
  fun v hwv ↦ ⟨u, IsEuclidean.eucl w v u hwv hwu, hpu⟩

theorem box_of_diamond_box [IsEuclidean R] (h : ◇[R] (□[R] p) w) : □[R] p w :=
  let ⟨u, hwu, hpu⟩ := h
  fun v hwv ↦ hpu v (IsEuclidean.eucl w u v hwu hwv)

theorem diamond_box_of_box [IsSerial R] [R.IsTrans] (h : □[R] p w) : ◇[R] (□[R] p) w :=
  box_D (box_four h)

/-! ### Frame definability

Each axiom, read as an inequality between operators on `W → Prop`, characterizes its frame
condition. -/

/-- T defines reflexivity. -/
theorem box_T_iff : Box R ≤ id ↔ R.IsRefl where
  mp h := ⟨fun w ↦ h (w ~[R] ·) w fun _ hv ↦ hv⟩
  mpr _ _ _ := box_T

/-- Axiom T for the diamond, `p → ◇p`, defines reflexivity. -/
theorem diamond_T_iff : id ≤ Diamond R ↔ R.IsRefl where
  mp h := ⟨fun w ↦ match h (· = w) w rfl with | ⟨_, hv, rfl⟩ => hv⟩
  mpr hR _ w hp := ⟨w, hR.refl w, hp⟩

/-- D defines seriality. -/
theorem box_D_iff : Box R ≤ Diamond R ↔ IsSerial R where
  mp h := ⟨fun w ↦ let ⟨v, hv, _⟩ := h (fun _ ↦ True) w fun _ _ ↦ trivial; ⟨v, hv⟩⟩
  mpr _ _ _ := box_D

/-- B defines symmetry. -/
theorem box_B_iff : id ≤ Box R ∘ Diamond R ↔ R.IsSymm where
  mp h := ⟨fun w v hwv ↦ match h (· = w) w rfl v hwv with | ⟨_, hvw, rfl⟩ => hvw⟩
  mpr _ _ _ := box_B

/-- 4 defines transitivity. -/
theorem box_four_iff : Box R ≤ Box R ∘ Box R ↔ R.IsTrans where
  mp h := ⟨fun w _ _ hwv hvu ↦ h (w ~[R] ·) w (fun _ hv ↦ hv) _ hwv _ hvu⟩
  mpr _ _ _ := box_four

/-- 5 defines the Euclidean property. -/
theorem box_five_iff : Diamond R ≤ Box R ∘ Diamond R ↔ IsEuclidean R where
  mp h := ⟨fun w v u hwv hwu ↦ match h (· = u) w ⟨u, hwu, rfl⟩ v hwv with | ⟨_, hvu, rfl⟩ => hvu⟩
  mpr _ _ _ := box_five

/-- Den, `◇p → ◇◇p`, the converse of 4 for possibility, defines density: whatever `R` relates, it
relates through an intermediate world. A reflexive relation validates it trivially, through the
endpoints, as [prior-1967] notes of a reflexive *later than* (p. 39). -/
theorem diamond_den_iff : Diamond R ≤ Diamond R ∘ Diamond R ↔ R ⊆ R ○ R := by
  rw [show Diamond R ∘ Diamond R = Diamond (R ○ R) from (funext (diamond_comp R R)).symm,
    diamond_le_diamond_iff]

/-- `p → ◇_R ◇_{R⁻¹} p` defines seriality: a world can return to itself through a successor
exactly when it has one. For the future this is the observation of [prior-1967] that if time has
an end, *it will have been that p* is not implied by *p* (p. 40). -/
theorem le_diamond_diamond_inv_iff : id ≤ Diamond R ∘ Diamond R.inv ↔ IsSerial R where
  mp h := ⟨fun w ↦ let ⟨v, hv, _⟩ := h (fun _ ↦ True) w trivial; ⟨v, hv⟩⟩
  mpr _ _ w hp := let ⟨v, hv⟩ := IsSerial.serial (R := R) w; ⟨v, hv, w, hv, hp⟩

/-! ### Seriality and functionality at a world

Each of the following laws, required at a world `w` for every `p`, defines a condition on the
worlds `w` sees. Excluded middle `□p ∨ □¬p` holds iff `w` sees at most one world (Alt₁),
non-contradiction `¬(□p ∧ □¬p)` iff it sees at least one (D), and Negation Swap `□¬p ↔ ¬□p` iff it
sees exactly one. For possibility the two conditions trade places. Negation Swap holds at every
world iff the relation is the graph of a function, along which necessity is precomposition. -/

end Frame

section Functional

variable {W W' : Type*} {R : SetRel W' W} {w : W'}

/-- Axiom Alt₁, `◇p → □p` for every `p`, holds at `w` iff `w` sees at most one world. -/
theorem diamond_le_box_at_iff :
    (∀ p : W → Prop, ◇[R] p w → □[R] p w) ↔ ∀ ⦃v⦄, w ~[R] v → ∀ ⦃u⦄, w ~[R] u → v = u where
  mp h v hv _ hu := (h (· = v) ⟨v, hv, rfl⟩ _ hu).symm
  mpr h _ := fun ⟨_, hu, hpu⟩ _ hv ↦ h hu hv ▸ hpu

/-- Alt₁ defines partial functionality. -/
theorem diamond_le_box_iff :
    Diamond R ≤ Box R ↔ ∀ w ⦃v⦄, w ~[R] v → ∀ ⦃u⦄, w ~[R] u → v = u :=
  ⟨fun h _ ↦ diamond_le_box_at_iff.1 fun p ↦ h p _,
    fun h p _ ↦ diamond_le_box_at_iff.2 (h _) p⟩

theorem box_or_box_not_at_iff :
    (∀ p : W → Prop, □[R] p w ∨ □[R] (fun v ↦ ¬ p v) w) ↔
      ∀ ⦃v⦄, w ~[R] v → ∀ ⦃u⦄, w ~[R] u → v = u := by
  rw [← diamond_le_box_at_iff]
  refine forall_congr' fun p ↦ ?_
  rw [← not_diamond, or_comm, or_iff_not_imp_left, not_not]

/-- The neg-raising inference for every `p` at `w`, `¬□p → □¬p`, holds iff `w` sees at most
one world. -/
theorem box_not_of_not_box_at_iff :
    (∀ p : W → Prop, ¬ □[R] p w → □[R] (fun v ↦ ¬ p v) w) ↔
      ∀ ⦃v⦄, w ~[R] v → ∀ ⦃u⦄, w ~[R] u → v = u := by
  rw [← box_or_box_not_at_iff]
  exact forall_congr' fun p ↦ (or_iff_not_imp_left).symm

theorem not_box_and_box_not_at_iff :
    (∀ p : W → Prop, ¬ (□[R] p w ∧ □[R] (fun v ↦ ¬ p v) w)) ↔ ∃ v, w ~[R] v := by
  refine ⟨fun h ↦ ?_, fun ⟨v, hv⟩ p ⟨h₁, h₂⟩ ↦ h₂ v hv (h₁ v hv)⟩
  by_contra hn
  exact h (fun _ ↦ True) ⟨fun _ _ ↦ trivial, fun v hv _ ↦ hn ⟨v, hv⟩⟩

/-- Negation Swap for every `p` at `w`, `□¬p ↔ ¬□p`, holds iff `w` sees exactly one world. -/
theorem box_not_iff_not_box_at_iff :
    (∀ p : W → Prop, □[R] (fun v ↦ ¬ p v) w ↔ ¬ □[R] p w) ↔ ∃! v, w ~[R] v := by
  constructor
  · intro h
    obtain ⟨v, hv⟩ := not_box_and_box_not_at_iff.1 fun p ⟨h₁, h₂⟩ ↦ (h p).1 h₂ h₁
    exact ⟨v, hv, fun u hu ↦ box_or_box_not_at_iff.1 (fun p ↦ (em _).imp_right (h p).2) hu hv⟩
  · rintro ⟨v, hv, hu⟩ p
    have key (q : W → Prop) : □[R] q w ↔ q v := ⟨fun h ↦ h v hv, fun hq u hwu ↦ hu u hwu ▸ hq⟩
    rw [key, key]

theorem diamond_or_diamond_not_at_iff :
    (∀ p : W → Prop, ◇[R] p w ∨ ◇[R] (fun v ↦ ¬ p v) w) ↔ ∃ v, w ~[R] v := by
  refine ⟨fun h ↦ ?_, fun ⟨v, hv⟩ p ↦ ?_⟩
  · rcases h fun _ ↦ True with ⟨v, hv, -⟩ | ⟨v, hv, -⟩ <;> exact ⟨v, hv⟩
  · by_cases hp : p v
    exacts [.inl ⟨v, hv, hp⟩, .inr ⟨v, hv, hp⟩]

theorem not_diamond_and_diamond_not_at_iff :
    (∀ p : W → Prop, ¬ (◇[R] p w ∧ ◇[R] (fun v ↦ ¬ p v) w)) ↔
      ∀ ⦃v⦄, w ~[R] v → ∀ ⦃u⦄, w ~[R] u → v = u := by
  rw [← box_or_box_not_at_iff]
  refine forall_congr' fun p ↦ ?_
  rw [not_and_or, not_diamond, not_diamond, or_comm]
  simp only [not_not]

@[simp] theorem box_graph (f : W' → W) (p : W → Prop) : □[Function.graph f] p = p ∘ f :=
  funext fun _ ↦ propext ⟨fun h ↦ h _ rfl, fun h _ hv ↦ hv ▸ h⟩

/-- Negation Swap at every world holds iff the relation is the graph of a function. -/
theorem box_compl_eq_iff :
    (∀ p : W → Prop, □[R] pᶜ = (□[R] p)ᶜ) ↔ ∃ f : W' → W, Function.graph f = R := by
  have : (∀ p : W → Prop, □[R] pᶜ = (□[R] p)ᶜ) ↔ ∀ w, ∃! v, w ~[R] v := by
    simp only [← box_not_iff_not_box_at_iff, funext_iff, Pi.compl_apply, compl_iff_not,
      eq_iff_iff]
    exact forall_comm
  rw [this, ← R.exists_graph_eq_iff]
  exact ⟨fun ⟨f, hf, _⟩ ↦ ⟨f, hf⟩,
    fun ⟨f, hf⟩ ↦ ⟨f, hf, fun _ hg ↦ Function.graph_injective (hg.trans hf.symm)⟩⟩

end Functional

/-! ### A pair of relations -/

section Pair

variable {W W' : Type*} {R : SetRel W W'} {S : SetRel W' W}

/-- The schema `p → □[R] ◇[S] p` defines inclusion of the converse of `R` in `S`. Axiom B is the
case of one relation. -/
theorem id_le_box_comp_diamond_iff : id ≤ Box R ∘ Diamond S ↔ R.inv ⊆ S where
  mp h := fun ⟨v, w⟩ hvw ↦ match h (· = w) w rfl v hvw with | ⟨_, hu, rfl⟩ => hu
  mpr h _ w hp _ hv := ⟨w, h hv, hp⟩

/-- Both interaction schemas are valid exactly when the two relations are converse. -/
theorem id_le_box_comp_diamond_and_iff :
    id ≤ Box R ∘ Diamond S ∧ id ≤ Box S ∘ Diamond R ↔ R.inv = S := by
  rw [id_le_box_comp_diamond_iff, id_le_box_comp_diamond_iff]
  exact ⟨fun ⟨h₁, h₂⟩ ↦ h₁.antisymm fun _ hx ↦ h₂ hx, by rintro rfl; exact ⟨subset_rfl, subset_rfl⟩⟩

/-- A possibility is left adjoint to a necessity exactly when their relations are converse. -/
theorem gc_diamond_box_iff : GaloisConnection (Diamond S) (Box R) ↔ R.inv = S := by
  refine ⟨fun h ↦ ?_, by rintro rfl; exact diamond_box_gc _⟩
  have key (p : W → Prop) : Diamond R.inv p = Diamond S p :=
    le_antisymm ((diamond_box_gc R.inv).l_le (h.le_u_l p))
      (h.l_le ((diamond_box_gc R.inv).le_u_l p))
  exact (diamond_le_diamond_iff.1 fun p ↦ (key p).le).antisymm
    (diamond_le_diamond_iff.1 fun p ↦ (key p).ge)

end Pair

end ModalLogic
