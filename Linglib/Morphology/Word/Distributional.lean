/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Morphology.Morph
public import Mathlib.Data.List.Dedup
public import Mathlib.Data.List.Duplicate
public import Mathlib.Data.List.Infix
public import Mathlib.Order.FixedPoints
public import Mathlib.Tactic.MkIffOfInductiveProp

/-!
# Distributional definitions of the word and its parts

Haspelmath defines the word and its parts for comparing languages by the distribution of morphs
over a language's free forms, the forms that can be used on their own. A morph is bound when it is
not a free form, and a root is a morph that denotes an action, an object or a property. A morph
occurs on a root when it is next to the root or next to an affix that occurs on the root, and an
affix is a bound morph that is not a root and always occurs on roots of one class. A clitic is a
bound morph that is neither a root nor an affix, and a word is a free morph, a clitic, or a root
with its affixes.

The definitions take the free forms `F`, a list of sequences of morphs, and a function `cls`
giving the class of each root. The definition of an affix refers to the affixes. For a set `A` of
morphs, the step of `A` is the set of bound morphs that are not roots and have a root class such
that each of their occurrences is next, through the morphs of `A`, to a root of that class. The
step is monotone, and we define the affixes as its greatest fixed point, the largest set of morphs
each of which is an affix given that the others are.

## Main definitions

* `Distributional.RootClass`: the classes of roots denoting actions, objects and properties.
* `Distributional.Form`: a morph with the class of what it denotes.
* `Distributional.IsRoot`, `Distributional.rootClass`: the contentful morphs that occur without
  another contentful morph, and their classes.
* `Distributional.OccursOn`: a morph is next to another through a set of morphs.
* `Distributional.Selects`: a morph selects a root class when each of its occurrences occurs on a
  root of that class.
* `Distributional.AffixStep`, `Distributional.affixStep`: one step of the definition of an affix,
  and the step as a monotone map on sets of morphs.
* `Distributional.affixes`: the affixes, the greatest fixed point of the step.
* `Distributional.affixList`: the affixes computed by discarding, round after round, the morphs
  that fail the step.
* `Distributional.IsClitic`: a bound morph that is neither a root nor an affix.
* `Distributional.RequiresAffix`, `Distributional.IsRequiredAffix`: a root that never occurs
  without an affix, and an affix on such a root.
* `Distributional.IsWord`: a free morph, a clitic, or a root with its affixes.

## Main results

* `Distributional.mem_affixes_iff`: an affix is a bound morph that is not a root and selects a
  root class through the affixes.
* `Distributional.isGreatest_affixes`: the affixes are the greatest set of morphs each of which
  passes the step taken through the set.
* `Distributional.mem_affixList`: the computation yields the affixes.
* `Distributional.mem_affixes_of_subset`: an affix on some free forms is an affix on each part of
  them in which it occurs, so a morph that is not an affix on some free forms is not an affix on
  more.
* `Distributional.notMem_affixes_of_not_affixStep`: a morph that fails the step even when every
  morph that is not a root is taken to be an affix is not an affix.

## Implementation notes

* The free forms are a finite sample, and boundness and affixhood are relative to it. A morph that
  can be used on its own counts as bound unless the sample lists it as a free form.
* One function `cls` says which morphs are roots and of what class, in any type of classes;
  `RootClass` and `Form` are the classes and morphs of the papers' examples. A root is a morph that
  denotes an action, an object or a property in [haspelmath-2021c], where `cls` is the class a
  morph denotes, and such a morph that occurs without another in [haspelmath-2023], where `cls`
  is `rootClass`.
* The definition is printed as two conditions, that an affix must occur on a root and that it
  cannot occur on roots of different classes. `Selects` asks for one root class with a root of
  that class at each occurrence, so an occurrence between roots of two classes counts for either.
  If every root next to an occurrence had to be of the one class, enlarging `A` could both add
  morphs to the step and remove them, and the definition could have several incomparable
  solutions.
* The least fixed point of the step would leave out two suffixes that follow a root in either
  order, each of which occurs on the root only through the other in one of the two forms.
* A required affix may be replaced by any other affix on its root, since replacement within one
  slot would need paradigm structure. Compounds are not covered.

## TODO

* Relate `Morph.wordsAt`, the words a spelling marks off at an attachment, to `IsWord`.

## References

* [haspelmath-2021c]
* [haspelmath-2023]
-/

@[expose] public section

namespace Morphology.Distributional

/-- The class of a root says whether it denotes an action, an object or a property. -/
inductive RootClass where
  /-- The root denotes an action, as a verb root does. -/
  | action
  /-- The root denotes an object, as a noun root does. -/
  | object
  /-- The root denotes a property, as an adjective root does. -/
  | property
  deriving DecidableEq, Fintype, Repr

/-- A form pairs a morph, its shape, with the class of what it denotes, if it denotes an action,
an object or a property. -/
structure Form where
  /-- The morph. -/
  shape : Morph
  /-- The class of what the form denotes, if any. -/
  meaning : Option RootClass
  deriving DecidableEq, Repr

variable {M : Type*}

/-! ### Occurrence on a root -/

/-- Read outward from a position, the morphs `v` reach `y` through the morphs of `A` when `y` is
next, or the next morph is in `A` and the rest reach `y`. -/
def Reaches (A : Set M) : List M → M → Prop
  | [], _ => False
  | z :: v, y => z = y ∨ z ∈ A ∧ Reaches A v y

instance decReaches [DecidableEq M] (A : Set M) [DecidablePred (· ∈ A)] :
    ∀ v y, Decidable (Reaches A v y)
  | [], _ => .isFalse id
  | z :: v, y =>
    have := decReaches A v y
    inferInstanceAs (Decidable (z = y ∨ z ∈ A ∧ Reaches A v y))

@[simp] theorem reaches_nil (A : Set M) (y : M) : ¬ Reaches A [] y := id

@[simp] theorem reaches_cons {A : Set M} {z y : M} {v : List M} :
    Reaches A (z :: v) y ↔ z = y ∨ z ∈ A ∧ Reaches A v y := Iff.rfl

/-- In the free form `w`, the morph at `i` occurs on `y` through the morphs of `A` when it is next
to `y`, or next to a morph of `A` that occurs on `y`. -/
def OccursOn (A : Set M) (w : List M) (i : ℕ) (y : M) : Prop :=
  Reaches A (w.drop (i + 1)) y ∨ Reaches A (w.take i).reverse y

instance [DecidableEq M] (A : Set M) [DecidablePred (· ∈ A)] (w : List M) (i : ℕ) (y : M) :
    Decidable (OccursOn A w i y) := inferInstanceAs (Decidable (_ ∨ _))

section
variable {A B : Set M} {v w : List M} {i : ℕ} {y : M}

theorem Reaches.mono (h : A ⊆ B) (hv : Reaches A v y) : Reaches B v y := by
  induction v with
  | nil => exact hv
  | cons z v ih => exact hv.imp_right fun hz ↦ ⟨h hz.1, ih hz.2⟩

theorem Reaches.mem (hv : Reaches A v y) : y ∈ v := by
  induction v with
  | nil => exact hv.elim
  | cons z v ih => rcases hv with rfl | hv; exacts [List.mem_cons_self, .tail _ (ih hv.2)]

/-- The morphs through which `v` reaches `y` are morphs of `v`. -/
theorem Reaches.inter_mem (hv : Reaches A v y) : Reaches (A ∩ {z | z ∈ v}) v y := by
  induction v with
  | nil => exact hv
  | cons z v ih =>
    exact hv.imp_right fun hz ↦ ⟨⟨hz.1, List.mem_cons_self⟩,
      (ih hz.2).mono (Set.inter_subset_inter_right _ fun _ h ↦ List.mem_cons_of_mem _ h)⟩

theorem OccursOn.mono (h : A ⊆ B) (ho : OccursOn A w i y) : OccursOn B w i y :=
  ho.imp (Reaches.mono h) (Reaches.mono h)

theorem OccursOn.mem (ho : OccursOn A w i y) : y ∈ w :=
  ho.elim (fun h ↦ List.mem_of_mem_drop h.mem)
    fun h ↦ List.mem_of_mem_take (List.mem_reverse.1 h.mem)

/-- The morphs through which a morph occurs on another are morphs of the free form. -/
theorem OccursOn.inter_mem (ho : OccursOn A w i y) : OccursOn (A ∩ {z | z ∈ w}) w i y :=
  ho.imp
    (fun h ↦ h.inter_mem.mono
      (Set.inter_subset_inter_right _ fun _ hz ↦ List.mem_of_mem_drop hz))
    fun h ↦ h.inter_mem.mono
      (Set.inter_subset_inter_right _ fun _ hz ↦ List.mem_of_mem_take (List.mem_reverse.1 hz))

end

variable {C : Type*} (F : List (List M)) (cls : M → Option C)

/-! ### Roots -/

/-- A contentful morph is a root when it occurs in a free form with no other contentful morph,
`cls` being the class a morph denotes. -/
def IsRoot (x : M) : Prop := cls x ≠ none ∧ ∃ w ∈ F, x ∈ w ∧ ∀ y ∈ w, y ≠ x → cls y = none

instance [DecidableEq M] (x : M) : Decidable (IsRoot F cls x) :=
  inferInstanceAs (Decidable (_ ∧ ∃ w ∈ F, _))

/-- The class of a morph if it is a root, `cls` being the class a morph denotes. -/
def rootClass [DecidableEq M] (x : M) : Option C := if IsRoot F cls x then cls x else none

/-! ### The step of the definition -/

section Step

/-- The morph `x` selects the root class `c` through `A` when each occurrence of `x` in a free
form occurs on a root of class `c` through the morphs of `A`. -/
def Selects (A : Set M) (x : M) (c : C) : Prop :=
  ∀ w ∈ F, ∀ i, w[i]? = some x → ∃ y, OccursOn A w i y ∧ cls y = some c

instance [DecidableEq M] [DecidableEq C] (A : Set M) [DecidablePred (· ∈ A)] (x : M) (c : C) :
    Decidable (Selects F cls A x c) :=
  decidable_of_iff (∀ w ∈ F, ∀ i < w.length, w[i]? = some x →
      ∃ y ∈ w, OccursOn A w i y ∧ cls y = some c)
    ⟨fun h w hw i hx ↦
      let ⟨y, _, hy⟩ := h w hw i (List.getElem?_eq_some_iff.1 hx).1 hx
      ⟨y, hy⟩,
    fun h w hw i _ hx ↦ let ⟨y, hy⟩ := h w hw i hx; ⟨y, hy.1.mem, hy⟩⟩

/-- `AffixStep F cls A x` is one step of the definition of an affix: given that the morphs of `A`
are affixes, `x` is an affix. -/
@[mk_iff]
structure AffixStep (A : Set M) (x : M) : Prop where
  /-- An affix is bound: it is not a free form. -/
  notMem : [x] ∉ F
  /-- An affix is not a root. -/
  cls_eq_none : cls x = none
  /-- An affix occurs in a free form. -/
  mem_flatten : x ∈ F.flatten
  /-- An affix always occurs on roots of one class. -/
  selects : ∃ c, Selects F cls A x c

instance [DecidableEq M] [Fintype C] [DecidableEq C] (A : Set M) [DecidablePred (· ∈ A)] (x : M) :
    Decidable (AffixStep F cls A x) :=
  decidable_of_iff' _ (affixStep_iff F cls A x)

variable {F cls} {A B : Set M} {x : M}

theorem Selects.mono (h : A ⊆ B) {c : C} (hs : Selects F cls A x c) :
    Selects F cls B x c :=
  fun w hw i hx ↦ (hs w hw i hx).imp fun _ hy ↦ ⟨hy.1.mono h, hy.2⟩

theorem AffixStep.mono (h : A ⊆ B) (hx : AffixStep F cls A x) : AffixStep F cls B x :=
  ⟨hx.notMem, hx.cls_eq_none, hx.mem_flatten, hx.selects.imp fun _ hc ↦ hc.mono h⟩

variable (F cls)

/-- The step of the definition of an affix is a monotone map on sets of morphs. -/
def affixStep : Set M →o Set M where
  toFun A := {x | AffixStep F cls A x}
  monotone' _ _ h _ hx := hx.mono h

/-- The affixes are the greatest fixed point of the step. -/
def affixes : Set M := (affixStep F cls).gfp

variable {F cls}

@[simp] theorem mem_affixStep : x ∈ affixStep F cls A ↔ AffixStep F cls A x := Iff.rfl

@[simp] theorem affixStep_affixes : affixStep F cls (affixes F cls) = affixes F cls :=
  (affixStep F cls).map_gfp

/-- An affix is a bound morph that is not a root and selects a root class through the affixes. -/
theorem mem_affixes_iff : x ∈ affixes F cls ↔ AffixStep F cls (affixes F cls) x := by
  rw [← mem_affixStep, affixStep_affixes]

theorem subset_affixes (h : A ⊆ affixStep F cls A) : A ⊆ affixes F cls :=
  (affixStep F cls).le_gfp h

theorem isGreatest_affixes : IsGreatest {A | A ⊆ affixStep F cls A} (affixes F cls) :=
  (affixStep F cls).isGreatest_gfp_le

theorem affixes_subset : affixes F cls ⊆ {z | cls z = none} :=
  fun _ hz ↦ (mem_affixes_iff.1 hz).cls_eq_none

/-- A morph that fails the step even when every morph that is not a root is taken to be an affix
is not an affix. -/
theorem notMem_affixes_of_not_affixStep (h : ¬ AffixStep F cls {z | cls z = none} x) :
    x ∉ affixes F cls :=
  fun hx ↦ h ((mem_affixes_iff.1 hx).mono affixes_subset)

/-- An affix on some free forms is an affix on each part of them in which it occurs. -/
theorem mem_affixes_of_subset {F' : List (List M)} (hF : F ⊆ F') (hx : x ∈ F.flatten)
    (h : x ∈ affixes F' cls) : x ∈ affixes F cls := by
  refine subset_affixes (A := affixes F' cls ∩ {z | z ∈ F.flatten}) (fun z hz ↦ ?_) ⟨h, hx⟩
  obtain ⟨hb, hr, -, c, hc⟩ := mem_affixes_iff.1 hz.1
  refine mem_affixStep.2 ⟨fun hzF ↦ hb (hF hzF), hr, hz.2, c, fun w hw i hi ↦ ?_⟩
  obtain ⟨y, hy, hyc⟩ := hc w (hF hw) i hi
  exact ⟨y, hy.inter_mem.mono
    (Set.inter_subset_inter_right _ fun _ h ↦ List.mem_flatten.2 ⟨w, hw, h⟩), hyc⟩

end Step

/-! ### Computing the affixes -/

section Compute

private theorem iterate_fixed_of_sublist {α : Type*} {g : List α → List α}
    (hg : ∀ S, (g S).Sublist S) :
    ∀ (m : ℕ) (S : List α), S.length ≤ m → g (g^[m] S) = g^[m] S
  | 0, S, h => by
    obtain rfl := List.length_eq_zero_iff.1 (Nat.le_zero.1 h)
    simpa using hg []
  | m + 1, S, h => by
    rw [Function.iterate_succ_apply]
    by_cases hS : g S = S
    · rw [hS, Function.iterate_fixed hS, hS]
    · refine iterate_fixed_of_sublist hg m (g S) ?_
      have := (hg S).length_le
      have : (g S).length ≠ S.length := fun e ↦ hS ((hg S).eq_of_length e)
      omega

variable [DecidableEq M] [Fintype C] [DecidableEq C]

/-- One round of the computation keeps the morphs of `S` that pass the step taken through `S`. -/
def prune (S : List M) : List M := S.filter fun x ↦ AffixStep F cls {z | z ∈ S} x

/-- The affixes, computed from the morphs of the free forms by as many rounds as there are
morphs. -/
def affixList : List M := (prune F cls)^[F.flatten.dedup.length] F.flatten.dedup

variable {F cls} {x : M}

private theorem mem_iterate_prune (k : ℕ) :
    ∀ x ∈ affixes F cls, x ∈ (prune F cls)^[k] F.flatten.dedup := by
  induction k with
  | zero => exact fun x hx ↦ List.mem_dedup.2 (mem_affixes_iff.1 hx).mem_flatten
  | succ k ih =>
    intro x hx
    rw [Function.iterate_succ_apply']
    exact List.mem_filter.2
      ⟨ih x hx, decide_eq_true ((mem_affixes_iff.1 hx).mono fun z hz ↦ ih z hz)⟩

/-- The computation yields the affixes. -/
theorem mem_affixList : x ∈ affixList F cls ↔ x ∈ affixes F cls := by
  refine ⟨fun hx ↦ subset_affixes (A := {z | z ∈ affixList F cls}) (fun z hz ↦ ?_) hx,
    mem_iterate_prune _ x⟩
  have hz' : z ∈ prune F cls (affixList F cls) := by
    rw [affixList,
      iterate_fixed_of_sublist (g := prune F cls) (fun _ ↦ List.filter_sublist) _ _ le_rfl]
    exact hz
  exact mem_affixStep.2 (of_decide_eq_true (List.mem_filter.1 hz').2)

instance (x : M) : Decidable (x ∈ affixes F cls) := decidable_of_iff _ mem_affixList

end Compute

/-! ### Clitics, required affixes and words -/

section Word

/-- A clitic is a bound morph that is neither a root nor an affix. -/
@[mk_iff]
structure IsClitic (x : M) : Prop where
  /-- A clitic is bound: it is not a free form. -/
  notMem : [x] ∉ F
  /-- A clitic is not a root. -/
  cls_eq_none : cls x = none
  /-- A clitic is not an affix. -/
  notMem_affixes : x ∉ affixes F cls
  /-- A clitic occurs in a free form. -/
  mem_flatten : x ∈ F.flatten

/-- In the free form `w`, the morph `y` at `i` is an affix that occurs on the root `r`. -/
def IsAffixOnAt (w : List M) (i : ℕ) (y r : M) : Prop :=
  w[i]? = some y ∧ y ∈ affixes F cls ∧ cls r ≠ none ∧ OccursOn (affixes F cls) w i r

/-- A root requires an affix when every free form containing it has an affix on it. -/
def RequiresAffix (r : M) : Prop :=
  ∀ w ∈ F, r ∈ w → ∃ i < w.length, ∃ y ∈ w, IsAffixOnAt F cls w i y r

/-- A required affix of a root is an affix on it when the root requires an affix, so that the
affix must be present unless another replaces it. -/
def IsRequiredAffix (x r : M) : Prop :=
  RequiresAffix F cls r ∧ ∃ w ∈ F, ∃ i < w.length, IsAffixOnAt F cls w i x r

/-- A word is a form of the language that is a free morph, a clitic, or a root with affixes,
among them an affix if the root requires one. -/
def IsWord (w : List M) : Prop :=
  (∃ f ∈ F, w <:+: f) ∧
    ((∃ x ∈ w, w = [x] ∧ ([x] ∈ F ∨ IsClitic F cls x)) ∨
      ∃ r ∈ w, cls r ≠ none ∧ ¬ List.Duplicate r w ∧ (∀ y ∈ w, y = r ∨ y ∈ affixes F cls) ∧
        (RequiresAffix F cls r → ∃ y ∈ w, y ≠ r))

section Decidable
variable [DecidableEq M] [Fintype C] [DecidableEq C]

instance (x : M) : Decidable (IsClitic F cls x) := decidable_of_iff' _ (isClitic_iff F cls x)

instance (w : List M) (i : ℕ) (y r : M) : Decidable (IsAffixOnAt F cls w i y r) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

instance (r : M) : Decidable (RequiresAffix F cls r) :=
  inferInstanceAs (Decidable (∀ w ∈ F, _))

instance (x r : M) : Decidable (IsRequiredAffix F cls x r) :=
  inferInstanceAs (Decidable (_ ∧ ∃ w ∈ F, _))

instance (w : List M) : Decidable (IsWord F cls w) :=
  inferInstanceAs (Decidable ((∃ f ∈ F, _) ∧ _))

end Decidable

end Word

end Morphology.Distributional
