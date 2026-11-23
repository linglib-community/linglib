/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Autosegmental.Basic

/-!
# Maps of autosegmental representations

An autosegmental representation has positions on each tier, a label at each position, and
association lines between the tiers. This file defines the map of a representation along each
of the three.

Given words `w` and a map of positions `f i` on each tier `i`, the representation `X.map w f hf`
has the words `w` and the lines of `X`, each moved along `f`. Given a map of alphabets
`g i : τ i → τ' i` for each tier, the relabelling `X.mapRange g` applies `g i` to each label of
tier `i` and keeps the lines. Given a map of tiers `h : κ → ι`, the restriction
`X.comapDomain h` is the representation on the tiers `κ` whose tier `k` is tier `h k` of `X`,
with the lines of `X` between these tiers.

A monotone map of positions preserves the No-Crossing Constraint. Relabelling and restriction
are monoid homomorphisms, and both preserve it.

## Implementation notes

`AR.map` moves lines along a map of positions as `SimpleGraph.map` moves edges along a map of
vertices. The names `mapRange` and `comapDomain` follow `DFinsupp.mapRange` and
`DFinsupp.comapDomain`, which map a dependent family along its values and along its index.

## TODO

* The melody of a restriction, when `h` is a map of trees of tiers. `AR.flatten` followed by a
  restriction covers the case where the tiers dropped lie between the tiers kept.
* The merger of two tiers into one.
-/

@[expose] public section

namespace Autosegmental.AR

variable {ι κ κ' : Type*} {τ τ' τ'' : ι → Type*}

/-! ### Moving positions -/

section Map

variable {X : AR τ} (w : ∀ i, List (τ i)) (f g : ι → ℕ → ℕ)
  (hf : ∀ i, ∀ p < (X.word i).length, f i p < (w i).length)

variable (X) in
/-- The representation with words `w` whose lines are those of `X`, each position moved
along `f` on its tier; positions merged by `f` keep the lines of all of them. -/
def map : AR τ where
  word := w
  lines i j := (X.lines i j).image (Prod.map (f i) (f j))
  lines_self i := by simp [X.lines_self]
  swap_mem_lines i j p q h := by
    simp only [Finset.mem_image, Prod.map, Prod.mk.injEq, Prod.exists] at h ⊢
    obtain ⟨a, b, h, rfl, rfl⟩ := h
    exact ⟨b, a, X.swap_mem_lines h, rfl, rfl⟩
  fst_lt_of_mem_lines i j p q h := by
    simp only [Finset.mem_image, Prod.map, Prod.mk.injEq, Prod.exists] at h
    obtain ⟨a, b, h, rfl, rfl⟩ := h
    exact hf i a (X.fst_lt_of_mem_lines h)

@[simp] theorem word_map : (X.map w f hf).word = w := rfl

theorem lines_map (i j : ι) :
    (X.map w f hf).lines i j = (X.lines i j).image (Prod.map (f i) (f j)) := rfl

variable {w f hf} in
theorem link_map {i j : ι} {r s : ℕ} :
    (X.map w f hf).Link i j r s ↔ ∃ p q, X.Link i j p q ∧ f i p = r ∧ f j q = s := by
  simp [Link, map]

/-- A move depends only on where it sends the positions of the words. -/
theorem map_congr (hg : ∀ i, ∀ p < (X.word i).length, g i p < (w i).length)
    (h : ∀ i, ∀ p < (X.word i).length, f i p = g i p) : X.map w f hf = X.map w g hg :=
  ext rfl fun i j r s ↦ by
    simp only [link_map]
    constructor <;> rintro ⟨p, q, hl, rfl, rfl⟩
    · exact ⟨p, q, hl, (h i p hl.lt_left).symm, (h j q hl.lt_right).symm⟩
    · exact ⟨p, q, hl, h i p hl.lt_left, h j q hl.lt_right⟩

/-- Moving positions monotonically preserves the No-Crossing Constraint. -/
theorem NoCrossing.map (hmono : ∀ i, MonotoneOn (f i) (Set.Iio (X.word i).length))
    (h : X.NoCrossing) : (X.map w f hf).NoCrossing := fun i j ↦
  isNonCrossing_lines_iff.2 fun r s r' s' h₁ h₂ hlt ↦ by
    obtain ⟨p, q, hl, rfl, rfl⟩ := link_map.1 h₁
    obtain ⟨p', q', hl', rfl, rfl⟩ := link_map.1 h₂
    have hpp' : p < p' := lt_of_not_ge fun hge ↦
      (hmono i hl'.lt_left hl.lt_left hge).not_gt hlt
    exact hmono j hl.lt_right hl'.lt_right (isNonCrossing_lines_iff.1 (h i j) hl hl' hpp')

variable (X) in
@[simp] theorem map_id : X.map X.word (fun _ ↦ id) (fun _ _ h ↦ h) = X :=
  ext rfl fun i j p q ↦ by simp [link_map]

end Map

/-! ### Relabelling -/

section MapRange

variable (g : ∀ i, τ i → τ' i) (X Y : AR τ)

/-- The relabelling of `X` by `g`: the word of tier `i` is mapped by `g i`, and the lines are those
of `X`. -/
def mapRange : AR τ' where
  word i := (X.word i).map (g i)
  lines := X.lines
  lines_self := X.lines_self
  swap_mem_lines := X.swap_mem_lines
  fst_lt_of_mem_lines _ _ _ _ h := by simpa using X.fst_lt_of_mem_lines h

@[simp] theorem word_mapRange (i : ι) : (X.mapRange g).word i = (X.word i).map (g i) := rfl

@[simp] theorem lines_mapRange : (X.mapRange g).lines = X.lines := rfl

@[simp] theorem link_mapRange {i j : ι} {p q : ℕ} :
    (X.mapRange g).Link i j p q ↔ X.Link i j p q := .rfl

@[simp] theorem mapRange_id : X.mapRange (fun _ ↦ id) = X :=
  AR.ext (funext fun _ ↦ List.map_id _) fun _ _ _ _ ↦ .rfl

theorem mapRange_mapRange (g' : ∀ i, τ' i → τ'' i) :
    (X.mapRange g).mapRange g' = X.mapRange fun i ↦ g' i ∘ g i :=
  AR.ext (funext fun _ ↦ List.map_map) fun _ _ _ _ ↦ .rfl

@[simp] theorem mapRange_one : (1 : AR τ).mapRange g = 1 := rfl

@[simp] theorem mapRange_mul : (X * Y).mapRange g = X.mapRange g * Y.mapRange g :=
  AR.ext (funext fun _ ↦ List.map_append) fun i j p q ↦ by simp [link_mul]

/-- `AR.mapRange` as a monoid homomorphism. -/
def mapRangeHom : AR τ →* AR τ' where
  toFun X := X.mapRange g
  map_one' := mapRange_one g
  map_mul' := mapRange_mul g

@[simp] theorem mapRangeHom_apply : mapRangeHom g X = X.mapRange g := rfl

theorem mapRangeHom_id : mapRangeHom (τ := τ) (fun _ ↦ id) = MonoidHom.id _ :=
  MonoidHom.ext mapRange_id

theorem mapRangeHom_comp (g' : ∀ i, τ' i → τ'' i) :
    mapRangeHom (fun i ↦ g' i ∘ g i) = (mapRangeHom g').comp (mapRangeHom g) :=
  MonoidHom.ext fun X ↦ (mapRange_mapRange g X g').symm

/-- A relabelling satisfies the No-Crossing Constraint if and only if the representation does. -/
@[simp] theorem noCrossing_mapRange : (X.mapRange g).NoCrossing ↔ X.NoCrossing := .rfl

/-- The word of tier `i` of a relabelling is the word of tier `i` mapped by `g i`. -/
theorem wordHom_comp_mapRangeHom (i : ι) :
    (wordHom i).comp (mapRangeHom g) = (FreeMonoid.map (g i)).comp (wordHom i) :=
  MonoidHom.ext fun _ ↦ rfl

end MapRange

/-! ### Restriction -/

section ComapDomain

variable (h : κ → ι) (X Y : AR τ)

/-- The restriction of `X` along `h`: tier `k` is tier `h k` of `X`, and the lines between tiers `k`
and `k'` are those of `X` between `h k` and `h k'`. -/
def comapDomain : AR fun k ↦ τ (h k) where
  word k := X.word (h k)
  lines k k' := X.lines (h k) (h k')
  lines_self k := X.lines_self (h k)
  swap_mem_lines _ _ _ _ hl := X.swap_mem_lines hl
  fst_lt_of_mem_lines _ _ _ _ hl := X.fst_lt_of_mem_lines hl

@[simp] theorem word_comapDomain (k : κ) : (X.comapDomain h).word k = X.word (h k) := rfl

@[simp] theorem lines_comapDomain (k k' : κ) :
    (X.comapDomain h).lines k k' = X.lines (h k) (h k') := rfl

@[simp] theorem link_comapDomain {k k' : κ} {p q : ℕ} :
    (X.comapDomain h).Link k k' p q ↔ X.Link (h k) (h k') p q := .rfl

@[simp] theorem comapDomain_id : X.comapDomain id = X := rfl

theorem comapDomain_comapDomain (h' : κ' → κ) :
    (X.comapDomain h).comapDomain h' = X.comapDomain (h ∘ h') := rfl

@[simp] theorem comapDomain_one : (1 : AR τ).comapDomain h = 1 := rfl

@[simp] theorem comapDomain_mul : (X * Y).comapDomain h = X.comapDomain h * Y.comapDomain h :=
  rfl

/-- `AR.comapDomain` as a monoid homomorphism. -/
def comapDomainHom : AR τ →* AR fun k ↦ τ (h k) where
  toFun X := X.comapDomain h
  map_one' := comapDomain_one h
  map_mul' := comapDomain_mul h

@[simp] theorem comapDomainHom_apply : comapDomainHom h X = X.comapDomain h := rfl

/-- A restriction of a representation that satisfies the No-Crossing Constraint satisfies it. -/
theorem NoCrossing.comapDomain {X : AR τ} (hX : X.NoCrossing) : (X.comapDomain h).NoCrossing :=
  fun _ _ ↦ hX _ _

/-- The word of tier `k` of a restriction along `h` is the word of tier `h k`. -/
theorem wordHom_comp_comapDomainHom (k : κ) :
    (wordHom k).comp (comapDomainHom (τ := τ) h) = wordHom (h k) := rfl

/-- The restriction of a relabelling is the relabelling of the restriction. -/
theorem comapDomain_mapRange (g : ∀ i, τ i → τ' i) :
    (X.mapRange g).comapDomain h = (X.comapDomain h).mapRange fun k ↦ g (h k) := rfl

end ComapDomain

end Autosegmental.AR
