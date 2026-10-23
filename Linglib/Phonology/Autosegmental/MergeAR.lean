/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Autosegmental.OCP

/-!
# Merging concatenation of autosegmental representations

Jardine and Heinz concatenate two representations by bridging them and merging the seam: on the
melody tier, the last node of the first factor and the first node of the second become one node
when they bear the same label, and that node keeps the lines of both. `MergeAR m τ` is `AR τ`
with this concatenation at melody tier `m` as its multiplication, the repointing of the bridging
concatenation along `OCP.mergeIdx`; a string realizes as the product of its symbols' primitives.

The merge happens at the seam only, so a primitive that itself violates the OCP keeps its
violation. Collapsing every run after concatenating would merge it away. The two realizations
agree when the primitives are OCP-clean, because the collapse is a monoid hom from bridging to
merging concatenation.

## Main definitions

* `MergeAR m τ`: representations under merging concatenation at melody tier `m`, a monoid
  (Jardine and Heinz's Theorems 1 and 3).
* `MergeAR.collapseHom`: the collapse, as a monoid hom from bridging concatenation.

## Main statements

* `MergeAR.link_toAR_mul`: a line of a merging concatenation is a line of the first factor, or
  a shifted line of the second.
* `MergeAR.noCrossing_toAR_mul`, `MergeAR.isCleanAt_toAR_mul`: merging concatenation preserves
  the NCC, and the OCP of OCP-clean factors.
* `MergeAR.prod_map_ofAR`: over OCP-clean primitives, the realization by merging
  concatenation is the collapsed realization.

## Implementation notes

Jardine and Heinz merge at every melody tier; `MergeAR m τ` merges at one tier `m`, the two-tier
case their primitives assume. They prove associativity for the graphs generated from primitives,
whose tiers are strings; here the tiers are words, so it holds for all representations.

## References

* [jardine-heinz-2015]
* [jardine-2019]
-/

@[expose] public section

namespace Autosegmental

/-- Representations under merging concatenation at melody tier `m`: a type synonym of `AR τ`
whose multiplication merges the seam of tier `m`. -/
def MergeAR {ι : Type*} (_m : ι) (τ : ι → Type*) : Type _ := AR τ

namespace MergeAR

variable {ι : Type*} {τ : ι → Type*} {m : ι}

/-- A representation as an element of the merging monoid. -/
def ofAR : AR τ ≃ MergeAR m τ := Equiv.refl _

/-- An element of the merging monoid as a representation. -/
def toAR : MergeAR m τ ≃ AR τ := ofAR.symm

@[simp] theorem toAR_ofAR (X : AR τ) : toAR (ofAR X : MergeAR m τ) = X := rfl

@[simp] theorem ofAR_toAR (X : MergeAR m τ) : ofAR (toAR X) = X := rfl

instance [Fintype ι] [∀ i, DecidableEq (τ i)] : DecidableEq (MergeAR m τ) :=
  inferInstanceAs (DecidableEq (AR τ))

/-- The empty representation. -/
instance : One (MergeAR m τ) := ⟨ofAR 1⟩

@[simp] theorem toAR_one : toAR (1 : MergeAR m τ) = 1 := rfl

section Mul

variable [DecidableEq ι] [DecidableEq (τ m)] (X Y : MergeAR m τ)

/-- Where tier `i` of the second factor starts in a merging concatenation. -/
def offset (i : ι) : ℕ :=
  if i = m then OCP.mergeOffset ((toAR X).word m) ((toAR Y).word m) else ((toAR X).word i).length

section
variable {X Y}

private theorem repointIdx_mergeIdx_of_lt {i : ι} {p : ℕ} (hp : p < ((toAR X).word i).length) :
    repointIdx m (OCP.mergeIdx ((toAR X).word m) ((toAR Y).word m)) i p = p := by
  rcases eq_or_ne i m with rfl | hi
  · exact (repointIdx_self p).trans (OCP.mergeIdx_of_lt hp)
  · exact repointIdx_of_ne hi p

private theorem repointIdx_runIdx_append_left {X Y : AR τ} {i : ι} {p : ℕ}
    (hp : p < (X.word i).length) :
    repointIdx m (OCP.runIdx (X.word m ++ Y.word m)) i p =
      repointIdx m (OCP.runIdx (X.word m)) i p := by
  rcases eq_or_ne i m with rfl | hi
  · simp only [repointIdx_self]
    exact OCP.runIdx_append_left hp
  · simp [hi]

private theorem repointIdx_mergeIdx_add (i : ι) (p : ℕ) :
    repointIdx m (OCP.mergeIdx ((toAR X).word m) ((toAR Y).word m)) i
      (((toAR X).word i).length + p) = offset X Y i + p := by
  rcases eq_or_ne i m with rfl | hi
  · rw [repointIdx_self, OCP.mergeIdx_length_add]
    simp [offset]
  · simp [offset, hi]

end

variable [Fintype ι]

/-- **Merging concatenation**: the bridging concatenation with the seam of melody tier `m`
merged, the last node of `X` and the first node of `Y` becoming one node when they bear the
same label. -/
instance : Mul (MergeAR m τ) where
  mul X Y := ofAR <| (toAR X * toAR Y).repoint m
    (OCP.mergeAppend ((toAR X).word m) ((toAR Y).word m))
    (f := OCP.mergeIdx ((toAR X).word m) ((toAR Y).word m))
    fun _ hp ↦ OCP.mergeIdx_lt (by simpa using hp)

theorem toAR_mul : toAR (X * Y) = (toAR X * toAR Y).repoint m
    (OCP.mergeAppend ((toAR X).word m) ((toAR Y).word m))
    (f := OCP.mergeIdx ((toAR X).word m) ((toAR Y).word m))
    (fun _ hp ↦ OCP.mergeIdx_lt (by simpa using hp)) := rfl

variable {X Y}

@[simp] theorem word_toAR_mul_self :
    (toAR (X * Y)).word m = OCP.mergeAppend ((toAR X).word m) ((toAR Y).word m) := by
  rw [toAR_mul]
  exact AR.word_repoint_self ..

@[simp] theorem word_toAR_mul_of_ne {i : ι} (h : i ≠ m) :
    (toAR (X * Y)).word i = (toAR X).word i ++ (toAR Y).word i := by
  rw [toAR_mul]
  exact AR.word_repoint_of_ne _ _ _ _ h

/-- A line of a merging concatenation is a line of the first factor, or a line of the second
shifted to where that factor starts. -/
theorem link_toAR_mul {i j : ι} {r s : ℕ} :
    (toAR (X * Y)).Link i j r s ↔ (toAR X).Link i j r s ∨
      ∃ p q, (toAR Y).Link i j p q ∧ offset X Y i + p = r ∧ offset X Y j + q = s := by
  rw [toAR_mul, AR.link_repoint]
  constructor
  · rintro ⟨p, q, hl, rfl, rfl⟩
    rcases (AR.link_mul i j p q).mp hl with hX | ⟨hp, hq, hY⟩
    · left
      rwa [repointIdx_mergeIdx_of_lt hX.lt_left, repointIdx_mergeIdx_of_lt hX.lt_right]
    · refine .inr ⟨_, _, hY, ?_, ?_⟩
      · rw [← repointIdx_mergeIdx_add, Nat.add_sub_cancel' hp]
      · rw [← repointIdx_mergeIdx_add, Nat.add_sub_cancel' hq]
  · rintro (hX | ⟨p, q, hY, rfl, rfl⟩)
    · exact ⟨r, s, (AR.link_mul i j r s).mpr (.inl hX), repointIdx_mergeIdx_of_lt hX.lt_left,
        repointIdx_mergeIdx_of_lt hX.lt_right⟩
    · exact ⟨((toAR X).word i).length + p, ((toAR X).word j).length + q,
        (AR.link_mul i j _ _).mpr (.inr ⟨by omega, by omega, by simpa using hY⟩),
        repointIdx_mergeIdx_add i p, repointIdx_mergeIdx_add j q⟩

/-! ### The theorems of Jardine and Heinz -/

section Offset
variable {Z : MergeAR m τ}

private theorem offset_mul_left (i : ι) :
    offset (X * Y) Z i = offset X (Y * Z) i + offset Y Z i := by
  rcases eq_or_ne i m with rfl | hi
  · simp [offset, OCP.mergeOffset_mergeAppend_left]
  · simp [offset, hi]

private theorem offset_mul_right {i : ι} (h : 0 < ((toAR Y).word i).length) :
    offset X (Y * Z) i = offset X Y i := by
  rcases eq_or_ne i m with rfl | hi
  · simp [offset, OCP.mergeOffset_mergeAppend_right (List.length_pos_iff.mp h)]
  · simp [offset, hi]

end Offset

end Mul

variable [DecidableEq ι] [DecidableEq (τ m)] [Fintype ι]

/-- Merging concatenation is a monoid with the empty representation as unit
([jardine-heinz-2015] Theorems 1 and 3). -/
instance : Monoid (MergeAR m τ) where
  one_mul X := toAR.injective <| AR.ext (funext fun i ↦ by
    rcases eq_or_ne i m with rfl | hi
    · simp
    · simp [hi])
    fun i j r s ↦ by simp [link_toAR_mul, offset]
  mul_one X := toAR.injective <| AR.ext (funext fun i ↦ by
    rcases eq_or_ne i m with rfl | hi
    · simp
    · simp [hi])
    fun i j r s ↦ by simp [link_toAR_mul]
  mul_assoc X Y Z := by
    refine toAR.injective <| AR.ext (funext fun i ↦ ?_) fun i j r s ↦ ?_
    · rcases eq_or_ne i m with rfl | hi
      · simp [OCP.mergeAppend_assoc]
      · simp [hi]
    simp only [link_toAR_mul]
    constructor
    · rintro ((hX | ⟨p, q, hY, rfl, rfl⟩) | ⟨p, q, hZ, rfl, rfl⟩)
      · exact .inl hX
      · have hp := hY.lt_left
        have hq := hY.lt_right
        exact .inr ⟨p, q, .inl hY, by rw [offset_mul_right (by omega)],
          by rw [offset_mul_right (by omega)]⟩
      · exact .inr ⟨_, _, .inr ⟨p, q, hZ, rfl, rfl⟩, by rw [offset_mul_left]; omega,
          by rw [offset_mul_left]; omega⟩
    · rintro (hX | ⟨_, _, hY | ⟨p, q, hZ, rfl, rfl⟩, rfl, rfl⟩)
      · exact .inl (.inl hX)
      · have hp := hY.lt_left
        have hq := hY.lt_right
        exact .inl (.inr ⟨_, _, hY, by rw [offset_mul_right (by omega)],
          by rw [offset_mul_right (by omega)]⟩)
      · exact .inr ⟨p, q, hZ, by rw [offset_mul_left]; omega, by rw [offset_mul_left]; omega⟩

variable {X Y : MergeAR m τ}

/-- Merging concatenation preserves the NCC, the inductive step of [jardine-heinz-2015]
Theorem 4. -/
theorem noCrossing_toAR_mul (hX : (toAR X).NoCrossing) (hY : (toAR Y).NoCrossing) :
    (toAR (X * Y)).NoCrossing := by
  rw [toAR_mul]
  exact (hX.mul hY).repoint _ OCP.mergeIdx_monotone

/-- Merging concatenation of OCP-clean factors is OCP-clean, the inductive step of
[jardine-heinz-2015] Theorem 5. -/
theorem isCleanAt_toAR_mul (hX : (toAR X).IsCleanAt m) (hY : (toAR Y).IsCleanAt m) :
    (toAR (X * Y)).IsCleanAt m := by
  simpa [AR.IsCleanAt] using OCP.isClean_mergeAppend hX hY

/-- Over primitives obeying the NCC, every realization by merging concatenation obeys it
([jardine-heinz-2015] Theorem 4). -/
theorem noCrossing_toAR_prod {l : List (MergeAR m τ)} (h : ∀ X ∈ l, (toAR X).NoCrossing) :
    (toAR l.prod).NoCrossing := by
  induction l with
  | nil => exact AR.NoCrossing.one
  | cons X l ih =>
    rw [List.prod_cons]
    exact noCrossing_toAR_mul (h X (by simp)) (ih fun Y hY ↦ h Y (by simp [hY]))

/-- Over OCP-clean primitives, every realization by merging concatenation is OCP-clean
([jardine-heinz-2015] Theorem 5). -/
theorem isCleanAt_toAR_prod {l : List (MergeAR m τ)} (h : ∀ X ∈ l, (toAR X).IsCleanAt m) :
    (toAR l.prod).IsCleanAt m := by
  induction l with
  | nil => simp [AR.IsCleanAt]
  | cons X l ih =>
    rw [List.prod_cons]
    exact isCleanAt_toAR_mul (h X (by simp)) (ih fun Y hY ↦ h Y (by simp [hY]))

/-! ### Collapse as a homomorphism -/

section Collapse

variable {X Y : AR τ}

private theorem repointIdx_runIdx_append_right {i : ι} {p : ℕ} (hp : p < (Y.word i).length) :
    repointIdx m (OCP.runIdx (X.word m ++ Y.word m)) i ((X.word i).length + p) =
      offset (ofAR (X.collapse m) : MergeAR m τ) (ofAR (Y.collapse m)) i +
        repointIdx m (OCP.runIdx (Y.word m)) i p := by
  rcases eq_or_ne i m with rfl | hi
  · simp only [repointIdx_self, offset, ↓reduceIte, toAR_ofAR, AR.word_collapse_self]
    exact OCP.runIdx_append_right hp
  · simp [offset, hi]

variable (X Y) in
theorem collapse_mul :
    ofAR ((X * Y).collapse m) = (ofAR (X.collapse m) * ofAR (Y.collapse m) : MergeAR m τ) := by
  refine toAR.injective <| AR.ext (funext fun i ↦ ?_) fun i j r s ↦ ?_
  · rcases eq_or_ne i m with rfl | hi
    · simp [OCP.collapse_append]
    · simp [hi]
  simp only [toAR_ofAR, AR.link_collapse, link_toAR_mul, AR.word_mul]
  constructor
  · rintro ⟨p, q, hl, rfl, rfl⟩
    rcases (AR.link_mul i j p q).mp hl with hX | ⟨hp, hq, hY⟩
    · exact .inl ⟨p, q, hX, (repointIdx_runIdx_append_left hX.lt_left).symm,
        (repointIdx_runIdx_append_left hX.lt_right).symm⟩
    · refine .inr ⟨_, _, ⟨_, _, hY, rfl, rfl⟩, ?_, ?_⟩
      · rw [← repointIdx_runIdx_append_right hY.lt_left, Nat.add_sub_cancel' hp]
      · rw [← repointIdx_runIdx_append_right hY.lt_right, Nat.add_sub_cancel' hq]
  · rintro (⟨p, q, hX, rfl, rfl⟩ | ⟨_, _, ⟨p, q, hY, rfl, rfl⟩, rfl, rfl⟩)
    · exact ⟨p, q, (AR.link_mul i j p q).mpr (.inl hX), repointIdx_runIdx_append_left hX.lt_left,
        repointIdx_runIdx_append_left hX.lt_right⟩
    · exact ⟨(X.word i).length + p, (X.word j).length + q,
        (AR.link_mul i j _ _).mpr (.inr ⟨by omega, by omega, by simpa using hY⟩),
        repointIdx_runIdx_append_right hY.lt_left, repointIdx_runIdx_append_right hY.lt_right⟩

end Collapse

variable (m) in
/-- The collapse at melody tier `m`, a monoid hom from bridging to merging concatenation. -/
def collapseHom : AR τ →* MergeAR m τ where
  toFun X := ofAR (X.collapse m)
  map_one' := AR.IsCleanAt.collapse_eq (by simp [AR.IsCleanAt])
  map_mul' := collapse_mul

@[simp] theorem toAR_collapseHom (X : AR τ) : toAR (collapseHom m X) = X.collapse m := rfl

theorem collapseHom_of_isCleanAt {X : AR τ} (h : X.IsCleanAt m) :
    collapseHom m X = (ofAR X : MergeAR m τ) :=
  h.collapse_eq

/-- Over OCP-clean primitives, the realization by merging concatenation is the collapsed
realization. -/
theorem prod_map_ofAR {S : Type*} {g₀ : S → AR τ} (hg : ∀ s, (g₀ s).IsCleanAt m) (w : List S) :
    (w.map fun s ↦ (ofAR (g₀ s) : MergeAR m τ)).prod = ofAR ((w.map g₀).prod.collapse m) := by
  rw [← toAR_collapseHom, ofAR_toAR, map_list_prod, List.map_map]
  exact congrArg List.prod (List.map_congr_left fun s _ ↦ (collapseHom_of_isCleanAt (hg s)).symm)

end MergeAR

end Autosegmental
