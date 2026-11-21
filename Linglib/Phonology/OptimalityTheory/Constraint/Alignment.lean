/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.OptimalityTheory.Constraint.Defs
public import Linglib.Phonology.OptimalityTheory.Correspondence.Basic
public import Linglib.Core.Computability.Edge
public import Linglib.Core.Data.List.Matching
public import Mathlib.Order.Interval.Basic

/-!
# Alignment constraints

A Generalized Alignment constraint `Align(Cat₁, Edge₁, Cat₂, Edge₂)` of [mccarthy-prince-1993b]
requires that for each constituent of the category `Cat₁` there be a constituent of `Cat₂` such
that `Edge₁` of the first and `Edge₂` of the second coincide. We take the two categories of a
candidate as two families of constituents and the coincidence of edges as a relation `R` between
them, and define `Constraint.align R` to count the members of the first family bearing `R` to no
member of the second, so that `align R (l, m) = 0` exactly when every member of `l` bears `R` to
some member of `m` (`Constraint.align_eq_zero_iff`). For two families of spans,
`Constraint.alignEdge e₁ e₂` takes for `R` the equality of the endpoint of the first span at the
edge `e₁` with the endpoint of the second at `e₂`. With `R` the equality of spans, both edges of
a constituent coinciding with those of one constituent of the other family, `align Eq` is the
Match constraint of [selkirk-2011].

We also define `Constraint.deficiency R`, which counts the members of the first family left
unpaired when each member of the second may be paired with at most one of the first: the length
of the family less the matching number of `R`. It is the least number of
violations of MAX of [mccarthy-prince-1995] among the correspondences between the positions of the
two families that lie within `R` and satisfy UNIFORMITY (`Constraint.deficiency_le_maxViol`,
`Constraint.exists_maxViol_eq_deficiency`). Pairing demands at least as much as
alignment along the same relation, and no more than alignment along a relation contained in it
that relates no two members to one: `align R ≤ deficiency R ≤ align S`
(`Constraint.align_le_deficiency`, `Constraint.deficiency_le_align`).

## Implementation notes

`align` assesses a constituent categorically, one violation when it is aligned with nothing, the
assessment [mccarthy-2003] argues for. [mccarthy-prince-1993b] assess the alignment of feet and
of infixes by the distance between the two edges; for feet that count is
`Prosody.Footing.footOffsets`.

A candidate enters as a pair of lists, not of finsets, so that two constituents of the same span
are counted twice. A constraint on candidates of another type is the `Constraint.comap` of one of
these along the map giving the two families of a candidate.

## References

* [mccarthy-prince-1993b]
* [mccarthy-prince-1995]
* [mccarthy-2003]
* [selkirk-2011]
-/

@[expose] public section

/-- The endpoint of a span at an edge, its start at the left and its end at the right. -/
def Edge.endpoint {α : Type*} [LE α] : Edge → NonemptyInterval α → α
  | .left, s => s.fst
  | .right, s => s.snd

@[simp] theorem Edge.endpoint_left {α : Type*} [LE α] (s : NonemptyInterval α) :
    Edge.left.endpoint s = s.fst := rfl

@[simp] theorem Edge.endpoint_right {α : Type*} [LE α] (s : NonemptyInterval α) :
    Edge.right.endpoint s = s.snd := rfl

namespace OptimalityTheory.Constraint

variable {β γ β' γ' : Type*} (R : β → γ → Prop) [DecidableRel R]

/-- Alignment of one family of constituents to another along `R`, assessed categorically: one
violation for each member of the first family that bears `R` to no member of the second. -/
def align : Constraint (List β × List γ) := fun x ↦ x.1.countP fun a ↦ ∀ b ∈ x.2, ¬ R a b

variable {R}

theorem align_eq_zero_iff {x : List β × List γ} : align R x = 0 ↔ ∀ a ∈ x.1, ∃ b ∈ x.2, R a b := by
  simp [align, List.countP_eq_zero]

/-- The members of a family are those aligned with nothing and those aligned with something. -/
theorem align_add_countP (x : List β × List γ) :
    align R x + x.1.countP (fun a ↦ ∃ b ∈ x.2, R a b) = x.1.length := by
  have h₁ := List.length_eq_countP_add_countP (fun a ↦ decide (∃ b ∈ x.2, R a b)) (l := x.1)
  have h₂ : align R x = x.1.countP fun a ↦ ¬ decide (∃ b ∈ x.2, R a b) :=
    List.countP_congr fun a _ ↦ by simp
  omega

/-- Alignment of the images of two families is alignment along the pullback of the relation. -/
theorem align_map (f : β' → β) (g : γ' → γ) (l : List β') (m : List γ') :
    align R (l.map f, m.map g) = align (fun a b ↦ R (f a) (g b)) (l, m) := by
  simp [align, List.countP_map, Function.comp_def]

/-- (4): `Align(Cat₁, Edge₁, Cat₂, Edge₂)` of [mccarthy-prince-1993b] over spans, one violation
for each span of the first family whose endpoint at `e₁` is the endpoint at `e₂` of no span of
the second. -/
abbrev alignEdge {α : Type*} [LE α] [DecidableEq α] (e₁ e₂ : Edge) :
    Constraint (List (NonemptyInterval α) × List (NonemptyInterval α)) :=
  align fun a b ↦ e₁.endpoint a = e₂.endpoint b

-- A phrase over two words is right-aligned with the second word, not left-aligned with it, and
-- matches neither. A suffix begins where the foot before it ends.
example : alignEdge (α := ℕ) .right .right
    ([⟨(0, 2), by decide⟩], [⟨(0, 1), by decide⟩, ⟨(1, 2), by decide⟩]) = 0 := by
  decide
example : alignEdge (α := ℕ) .left .left ([⟨(1, 2), by decide⟩], [⟨(0, 2), by decide⟩]) = 1 := by
  decide
example : align Eq ([(⟨(0, 2), by decide⟩ : NonemptyInterval ℕ)],
    [⟨(0, 1), by decide⟩, ⟨(1, 2), by decide⟩]) = 1 := by
  decide
example : alignEdge (α := ℕ) .left .right ([⟨(2, 3), by decide⟩], [⟨(0, 2), by decide⟩]) = 0 := by
  decide

/-! ### One-to-one correspondence -/

section Deficiency

variable (R) [DecidableEq γ]

/-- The deficiency of `R` between two families: one violation for each member of the first left
unpaired by a largest pairing along `R` in which each member of the second answers to at most one
of the first (`List.le_matchingNumber_iff`). -/
def deficiency : Constraint (List β × List γ) := fun x ↦ x.1.length - x.1.matchingNumber R x.2

variable {R}

/-- A member aligned with nothing along `R` is left unpaired along `R`. -/
theorem align_le_deficiency (x : List β × List γ) : align R x ≤ deficiency R x := by
  have h₁ := List.matchingNumber_le_countP (R := R) x.1 x.2
  have h₂ := align_add_countP (R := R) x
  simp only [deficiency]
  omega

/-- Where `S` is contained in `R` and no two members of a duplicate-free family bear `S` to one
member, the members left unpaired along `R` are at most those aligned with nothing along `S`. -/
theorem deficiency_le_align {S : β → γ → Prop} [DecidableRel S] {x : List β × List γ}
    (hx : x.1.Nodup) (hSR : ∀ a ∈ x.1, ∀ b, S a b → R a b)
    (hS : ∀ a ∈ x.1, ∀ a' ∈ x.1, ∀ b, S a b → S a' b → a = a') : deficiency R x ≤ align S x := by
  have h₁ := List.countP_le_matchingNumber hx hSR hS x.2
  have h₂ := align_add_countP (R := S) x
  simp only [deficiency]
  omega

variable {l : List β} {m : List γ}

/-- A correspondence between the positions of two families that lies within `R` and violates
UNIFORMITY nowhere violates MAX at least `deficiency R` times. -/
theorem deficiency_le_maxViol {ℜ : Correspondence (Fin l.length) (Fin m.length)}
    (hR : ∀ i j, (i, j) ∈ ℜ → R l[i] m[j]) (hU : ℜ.uniformityViol = 0) :
    deficiency R (l, m) ≤ ℜ.maxViol := by
  rcases ℜ.eq_empty_or_nonempty with rfl | ⟨⟨i₀, j₀⟩, -⟩
  · simp [deficiency, Correspondence.maxViol]
  have : Nonempty (Fin m.length) := ⟨j₀⟩
  have hdom : ∀ i ∈ ℜ.image Prod.fst, ∃ j, (i, j) ∈ ℜ := fun i hi ↦ by
    obtain ⟨⟨i', j⟩, h, rfl⟩ := Finset.mem_image.1 hi
    exact ⟨j, h⟩
  choose! f hf using hdom
  have hU := (Correspondence.uniformityViol_eq_zero_iff ℜ).1 hU
  let idxs := (List.finRange l.length).filter (· ∈ ℜ.image Prod.fst)
  have hmem : ∀ i ∈ idxs, i ∈ ℜ.image Prod.fst := fun i hi ↦ by simpa [idxs] using hi
  have hnd : idxs.Nodup := (List.nodup_finRange _).filter _
  have hcard : (ℜ.image Prod.fst).card = idxs.length := by
    rw [← List.toFinset_card_of_nodup hnd]
    congr 1
    ext i
    simp [idxs]
  have hl : (idxs.map l.get).Sublist l := by
    simpa [List.map_get_finRange] using (List.filter_sublist (l := List.finRange l.length)).map l.get
  have hm : ((idxs.map f).map m.get).Subperm m := by
    obtain ⟨js, hp, hs⟩ := List.subperm_of_subset (hnd.map_on fun i hi i' hi' (h : f i = f i') ↦
      hU (Finset.mem_coe.2 (hf i (hmem i hi)))
        (Finset.mem_coe.2 (show (i', f i) ∈ ℜ from h ▸ hf i' (hmem i' hi'))))
      fun j _ ↦ List.mem_finRange j
    exact ⟨js.map m.get, hp.map _, by simpa [List.map_get_finRange] using hs.map m.get⟩
  have hle : idxs.length ≤ l.matchingNumber R m := List.le_matchingNumber_iff.2
    ⟨_, _, hl, hm, by
      rw [List.map_map, List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
      exact fun i hi ↦ hR i (f i) (hf i (hmem i hi)), by simp⟩
  have hmax : ℜ.maxViol = l.length - (ℜ.image Prod.fst).card := by
    simp [Correspondence.maxViol, Finset.card_univ_sdiff]
  simp only [deficiency, hmax, hcard]
  omega

/-- Some correspondence between the positions of two families that lies within `R` and violates
UNIFORMITY nowhere violates MAX exactly `deficiency R` times. -/
theorem exists_maxViol_eq_deficiency (R : β → γ → Prop) [DecidableRel R] (l : List β)
    (m : List γ) : ∃ ℜ : Correspondence (Fin l.length) (Fin m.length),
      (∀ i j, (i, j) ∈ ℜ → R l[i] m[j]) ∧ ℜ.uniformityViol = 0 ∧
        ℜ.maxViol = deficiency R (l, m) := by
  have h₀ : l.matchingNumber R m ≤
      l.matchingNumber (fun a j ↦ R a (m.get j)) (List.finRange m.length) := by
    simpa [List.map_get_finRange] using
      List.matchingNumber_map_right_le (R := R) m.get l (List.finRange m.length)
  obtain ⟨l₁, js, hl, ⟨js', hp, hs⟩, hF, hk⟩ := List.le_matchingNumber_iff.1
    (le_refl (l.matchingNumber (fun a j ↦ R a (m.get j)) (List.finRange m.length)))
  obtain ⟨e, he⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.1 hl
  have hnd : js.Nodup := hp.nodup_iff.1 (hs.nodup (List.nodup_finRange _))
  obtain ⟨hlen, hget⟩ := List.forall₂_iff_get.1 hF
  let ℜ : Correspondence (Fin l.length) (Fin m.length) :=
    Finset.univ.image fun k : Fin l₁.length ↦ (e k, js.get (k.cast hlen))
  have hR : ∀ i j, (i, j) ∈ ℜ → R l[i] m[j] := fun i j h ↦ by
    obtain ⟨k, -, hk'⟩ := Finset.mem_image.1 h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hk'
    have := hget k k.2 (hlen ▸ k.2)
    rw [he k] at this
    simpa using this
  have hU : ℜ.uniformityViol = 0 :=
    (Correspondence.uniformityViol_eq_zero_iff ℜ).2 fun i i' j h h' ↦ by
      obtain ⟨k, -, hk₁⟩ := Finset.mem_image.1 (Finset.mem_coe.1 h)
      obtain ⟨k', -, hk₂⟩ := Finset.mem_image.1 (Finset.mem_coe.1 h')
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hk₁
      obtain ⟨rfl, hj⟩ := Prod.mk.inj hk₂
      rw [Fin.cast_injective hlen (hnd.get_inj_iff.1 hj)]
  refine ⟨ℜ, hR, hU, le_antisymm ?_ (deficiency_le_maxViol hR hU)⟩
  have himg : ℜ.image Prod.fst = Finset.univ.image e := by
    simp [ℜ, Finset.image_image, Function.comp_def]
  have hmax : ℜ.maxViol = l.length - l₁.length := by
    simp [Correspondence.maxViol, Finset.card_univ_sdiff, himg,
      Finset.card_image_of_injective _ e.injective]
  simp only [deficiency, hmax]
  omega

end Deficiency

-- Two words inside one phrase both align to it, but only one can have it as correspondent.
example : align (· ≤ ·) ([(⟨(0, 1), by decide⟩ : NonemptyInterval ℕ), ⟨(1, 2), by decide⟩],
    [⟨(0, 2), by decide⟩]) = 0 := by
  decide
example : deficiency (· ≤ ·) ([(⟨(0, 1), by decide⟩ : NonemptyInterval ℕ), ⟨(1, 2), by decide⟩],
    [⟨(0, 2), by decide⟩]) = 1 := by
  decide

end OptimalityTheory.Constraint
