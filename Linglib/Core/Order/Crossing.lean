module

public import Linglib.Core.Order.RelSeries
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Hom.Bounded
public import Mathlib.Order.Interval.Set.OrdConnected
public import Mathlib.Order.UpperLower.Basic

/-!
# How a map from a bounded linear order meets a set

Let `γ : ι → α` be a map from a bounded linear order, such as the positions of a finite series
or the unit interval of a curve, and let `R : Set α`. This file defines the ways `γ` can meet
`R`, by the positions it sends into `R`: `γ` *enters* `R` if they are an upper set that contains
the last position and not the first, *leaves* it if they are a lower set that contains the first
and not the last, and *crosses* it if they are one stretch that contains neither.

For a series, each of these fixes the number of steps into `R` and out of it.

## Main definitions

* `Order.Enters`, `Order.Leaves`, `Order.Crosses`, `Order.StaysIn`: the map ends inside `R`
  having started outside, starts inside and ends outside, passes through, or never leaves.
* `Order.Reaches`, `Order.Departs`: the map is inside `R` at its last position only, or at its
  first only.
* `Order.Approaches`, `Order.Recedes`: the map stays outside `R` and a measure of the distance
  to it strictly decreases, or strictly increases.

## Main results

* `Order.Enters.entries_eq`, `Order.Enters.exits_eq`: a series that enters `R` has one step into
  it and none out of it; likewise for `Order.Leaves`, `Order.Crosses` and `Order.StaysIn`.
-/

@[expose] public section

namespace Order

open OrderDual Set

variable {ι κ α β : Type*} [LinearOrder ι] [BoundedOrder ι] [LinearOrder κ] [BoundedOrder κ]
  (γ : ι → α) (R : Set α)

/-- `γ` enters `R`: it starts outside `R`, ends inside it, and stays inside once in. -/
def Enters : Prop := IsUpperSet (γ ⁻¹' R) ∧ γ ⊥ ∉ R ∧ γ ⊤ ∈ R

/-- `γ` leaves `R`: it starts inside `R`, ends outside it, and stays outside once out. -/
def Leaves : Prop := IsLowerSet (γ ⁻¹' R) ∧ γ ⊥ ∈ R ∧ γ ⊤ ∉ R

/-- `γ` crosses `R`: it starts and ends outside `R` and is inside it over one stretch. -/
def Crosses : Prop := (γ ⁻¹' R).OrdConnected ∧ (γ ⁻¹' R).Nonempty ∧ γ ⊥ ∉ R ∧ γ ⊤ ∉ R

/-- `γ` reaches `R`: it is inside `R` at its last position only. -/
def Reaches : Prop := γ ⁻¹' R = {⊤} ∧ (⊥ : ι) ≠ ⊤

/-- `γ` departs from `R`: it is inside `R` at its first position only. -/
def Departs : Prop := γ ⁻¹' R = {⊥} ∧ (⊥ : ι) ≠ ⊤

/-- `γ` stays in `R`: it is inside `R` throughout. -/
def StaysIn : Prop := ∀ i, γ i ∈ R

/-- `γ` approaches `R`: it is outside `R` throughout and nearer to it by `d` at each later
position, of which it has more than one. -/
def Approaches (d : α → β) [Preorder β] : Prop :=
  (∀ i, γ i ∉ R) ∧ StrictAnti (d ∘ γ) ∧ (⊥ : ι) ≠ ⊤

/-- `γ` recedes from `R`: it is outside `R` throughout and farther from it by `d` at each later
position, of which it has more than one. -/
def Recedes (d : α → β) [Preorder β] : Prop :=
  (∀ i, γ i ∉ R) ∧ StrictMono (d ∘ γ) ∧ (⊥ : ι) ≠ ⊤

variable {R γ}

theorem Reaches.enters (h : Reaches γ R) : Enters γ R := by
  obtain ⟨hS, hne⟩ := h
  refine ⟨?_, fun h ↦ ?_, ?_⟩
  · rw [hS, ← Ici_top]; exact .Ici ⊤
  · have : (⊥ : ι) ∈ γ ⁻¹' R := h
    rw [hS] at this
    exact hne this
  · show ⊤ ∈ γ ⁻¹' R; rw [hS]; rfl

theorem Departs.leaves (h : Departs γ R) : Leaves γ R := by
  obtain ⟨hS, hne⟩ := h
  refine ⟨?_, ?_, fun h ↦ ?_⟩
  · rw [hS, ← Iic_bot]; exact .Iic ⊥
  · show ⊥ ∈ γ ⁻¹' R; rw [hS]; rfl
  · have : (⊤ : ι) ∈ γ ⁻¹' R := h
    rw [hS] at this
    exact hne this.symm

/-- No map both enters and leaves a set. -/
theorem Enters.not_leaves (h : Enters γ R) : ¬ Leaves γ R :=
  fun h' ↦ h'.2.2 h.2.2

/-- A map enters `R` if and only if the positions it sends into `R` are one stretch that
includes the last position and not the first. -/
theorem enters_iff_ordConnected :
    Enters γ R ↔ (γ ⁻¹' R).OrdConnected ∧ γ ⊥ ∉ R ∧ γ ⊤ ∈ R :=
  ⟨fun h ↦ ⟨h.1.ordConnected, h.2⟩, fun ⟨h, h₀, h₁⟩ ↦
    ⟨fun _ _ hab ha ↦ h.out ha h₁ ⟨hab, le_top⟩, h₀, h₁⟩⟩

/-- A map leaves `R` if and only if the positions it sends into `R` are one stretch that
includes the first position and not the last. -/
theorem leaves_iff_ordConnected :
    Leaves γ R ↔ (γ ⁻¹' R).OrdConnected ∧ γ ⊥ ∈ R ∧ γ ⊤ ∉ R :=
  ⟨fun h ↦ ⟨h.1.ordConnected, h.2⟩, fun ⟨h, h₀, h₁⟩ ↦
    ⟨fun _ _ hab hb ↦ h.out h₀ hb ⟨bot_le, hab⟩, h₀, h₁⟩⟩

/-! ### Entries and exits of a series -/

section Counts

open RelSeries

variable {r : SetRel α α} {p : RelSeries r} {R : Set α}

theorem Enters.exits_eq (h : Enters p R) : p.exits R = 0 :=
  stepCount_eq_zero_iff.2 fun _ hi ↦ hi.2 (h.1 Fin.castSucc_lt_succ.le hi.1)

theorem Enters.entries_eq (h : Enters p R) : p.entries R = 1 := by
  classical
  have h0 : p.head ∉ R := h.2.1
  have h1 : p.last ∈ R := h.2.2
  have := entries_add_head R p
  simpa [h.exits_eq, h0, h1] using this

theorem Leaves.entries_eq (h : Leaves p R) : p.entries R = 0 :=
  stepCount_eq_zero_iff.2 fun _ hi ↦ hi.1 (h.1 Fin.castSucc_lt_succ.le hi.2)

theorem Leaves.exits_eq (h : Leaves p R) : p.exits R = 1 := by
  classical
  have h0 : p.head ∈ R := h.2.1
  have h1 : p.last ∉ R := h.2.2
  have := entries_add_head R p
  simpa [h.entries_eq, h0, h1] using this.symm

theorem StaysIn.entries_eq (h : StaysIn p R) : p.entries R = 0 :=
  stepCount_eq_zero_iff.2 fun _ hi ↦ hi.1 (h _)

theorem StaysIn.exits_eq (h : StaysIn p R) : p.exits R = 0 :=
  stepCount_eq_zero_iff.2 fun _ hi ↦ hi.2 (h _)

/-- A series that crosses `R` has one step into it. -/
theorem Crosses.entries_eq (h : Crosses p R) : p.entries R = 1 := by
  obtain ⟨hc, ⟨k, hk⟩, h0, -⟩ := h
  refine le_antisymm (stepCount_le_one fun i j hi hj ↦ ?_) (Nat.one_le_iff_ne_zero.2 fun hz ↦ ?_)
  · by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact hj.1 (hc.out (x := i.succ) (y := j.succ) hi.2 hj.2
        ⟨by simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]; exact hlt,
          Fin.castSucc_lt_succ.le⟩)
    · exact hi.1 (hc.out (x := j.succ) (y := i.succ) hj.2 hi.2
        ⟨by simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc]; exact hlt,
          Fin.castSucc_lt_succ.le⟩)
  · have hall : ∀ i : Fin (p.length + 1), p i ∉ R := fun i ↦ by
      induction i using Fin.induction with
      | zero => exact h0
      | succ i ih => exact fun hi ↦ stepCount_eq_zero_iff.1 hz i ⟨ih, hi⟩
    exact hall k hk

/-- A series that crosses `R` has one step out of it. -/
theorem Crosses.exits_eq (h : Crosses p R) : p.exits R = 1 := by
  classical
  have h0 : p.head ∉ R := h.2.2.1
  have h1 : p.last ∉ R := h.2.2.2
  have := entries_add_head R p
  simpa [h.entries_eq, h0, h1] using this.symm

end Counts

end Order
