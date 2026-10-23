/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.List.Dedup
public import Mathlib.Data.List.Duplicate
public import Mathlib.Data.List.Infix
public import Mathlib.Data.List.Sublists
public import Mathlib.Order.FixedPoints
public import Mathlib.Tactic.DeriveFintype

/-!
# Words and their parts as comparative concepts

Haspelmath defines the parts of words for comparing languages by their distribution over a
language's free forms, the forms that can be used on their own. A bound morph is not a free
form. A root is a contentful morph that can occur in a free form without another contentful
morph. An affix is a bound morph that is not a root, must occur on a root, and cannot occur on
roots of different classes, where a morph occurs on a root when it is next to the root or next
to an affix that occurs on it. A clitic is a bound morph that is neither a root nor an affix, and
a word is a free morph, a clitic, or a root with its affixes.

## Main definitions

* `Comparative.RootClass`: the classes of roots denoting actions, objects and properties.
* `Comparative.Inventory`: a language's free forms, with the root class each morph denotes.
* `Comparative.Inventory.IsBound`, `Comparative.Inventory.IsContentful`,
  `Comparative.Inventory.IsRoot`: bound morphs, contentful morphs, and roots.
* `Comparative.OccursOn`: occurrence on a root through candidate affixes.
* `Comparative.Inventory.AffixStep`, `Comparative.Inventory.IsAffix`: one step of the definition
  of an affix, and its greatest solution.
* `Comparative.Inventory.IsClitic`, `Comparative.Inventory.IsRequiredAffix`,
  `Comparative.Inventory.IsWord`: clitics, required affixes and words.

## Main results

* `Comparative.Inventory.isAffix_iff_sublists`: affixhood is decided over the bound morphs of the
  inventory.
* `Comparative.Inventory.setOf_isAffix_eq_gfp`: when the roots of every free form are adjacent,
  the affixes are the greatest fixed point of the step.

## Implementation notes

The definition of an affix refers to affixes, and its fixed points need not be unique; the
affixes are its greatest solution, the union of the sets the step maps into themselves. It is
parametric in the roots, which are the contentful morphs in the 2021 paper and those of `IsRoot`
in the 2023 one. A required affix may be replaced by any other affix on its root, since
replacement within one slot would need paradigm structure. Compounds are not covered.

## References

* [haspelmath-2021c]
* [haspelmath-2023]
-/

@[expose] public section

namespace Morphology.Comparative

/-- The class of a root says whether it denotes an action, an object or a property. -/
inductive RootClass where
  /-- The root denotes an action, as a verb root does. -/
  | action
  /-- The root denotes an object, as a noun root does. -/
  | object
  /-- The root denotes a property, as an adjective root does. -/
  | property
  deriving DecidableEq, Fintype, Repr

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

theorem Reaches.mono {A B : Set M} (h : A ⊆ B) {v : List M} {y : M} (hv : Reaches A v y) :
    Reaches B v y := by
  induction v with
  | nil => exact hv
  | cons z v ih => exact hv.imp_right fun hz ↦ ⟨h hz.1, ih hz.2⟩

theorem Reaches.mem {A : Set M} {v : List M} {y : M} (hv : Reaches A v y) : y ∈ v := by
  induction v with
  | nil => exact hv.elim
  | cons z v ih => rcases hv with rfl | hv; exacts [List.mem_cons_self, .tail _ (ih hv.2)]

theorem Reaches.find?_eq {A : Set M} {p : M → Prop} [DecidablePred p] (hA : ∀ z ∈ A, ¬ p z)
    {v : List M} {y : M} (hv : Reaches A v y) (hy : p y) : v.find? (p ·) = some y := by
  induction v with
  | nil => exact hv.elim
  | cons z v ih => rcases hv with rfl | hv; exacts [by simp [hy], by simp [hA z hv.1, ih hv.2]]

section
variable (root : M → Prop)

/-- In the free form `w`, the morph at `i` occurs on the root `y` through the morphs of `A` when it
is next to `y`, or next to a morph of `A` that occurs on `y`. -/
def OccursOn (A : Set M) (w : List M) (i : ℕ) (y : M) : Prop :=
  root y ∧ (Reaches A (w.drop (i + 1)) y ∨ Reaches A (w.take i).reverse y)

instance [DecidableEq M] [DecidablePred root] (A : Set M) [DecidablePred (· ∈ A)] (w : List M)
    (i : ℕ) (y : M) : Decidable (OccursOn root A w i y) := inferInstanceAs (Decidable (_ ∧ _))

/-- The roots of the form `w` are contiguous when no morph that is not a root lies between two
roots, as in a compound. -/
def RootsContiguous (w : List M) : Prop :=
  ∀ i (hi : i < w.length), ¬ root w[i] →
    (∀ y ∈ w.take i, ¬ root y) ∨ ∀ y ∈ w.drop (i + 1), ¬ root y

instance [DecidablePred root] (w : List M) : Decidable (RootsContiguous root w) :=
  inferInstanceAs (Decidable (∀ i (_ : i < w.length), _))

end

/-! ### Inventories -/

/-- An inventory is a language's free forms, each a sequence of morphs, with the class of root
each morph denotes, if any. -/
structure Inventory (M : Type*) where
  /-- The free forms, the forms that can be used on their own. -/
  forms : List (List M)
  /-- The class of root a morph denotes, if any. -/
  rootClass : M → Option RootClass

namespace Inventory

variable (L : Inventory M)

/-! ### Free forms and roots -/

/-- A morph is bound when it is not a free form. -/
def IsBound (x : M) : Prop := [x] ∉ L.forms

instance [DecidableEq M] (x : M) : Decidable (L.IsBound x) :=
  inferInstanceAs (Decidable (_ ∉ _))

/-- A morph is contentful when it denotes an action, an object or a property. -/
def IsContentful (x : M) : Prop := L.rootClass x ≠ none

instance (x : M) : Decidable (L.IsContentful x) := inferInstanceAs (Decidable (_ ≠ _))

/-- A root is a contentful morph that occurs in a free form with no other contentful morph. -/
def IsRoot (x : M) : Prop :=
  L.IsContentful x ∧ ∃ w ∈ L.forms, x ∈ w ∧ ∀ y ∈ w, y ≠ x → ¬ L.IsContentful y

instance [DecidableEq M] (x : M) : Decidable (L.IsRoot x) :=
  inferInstanceAs (Decidable (_ ∧ ∃ w ∈ L.forms, _))

theorem IsRoot.isContentful {L : Inventory M} {x : M} (h : L.IsRoot x) : L.IsContentful x := h.1

/-! ### Affixes -/

variable (root : M → Prop)

/-- `L.AffixStep root A x` is one step of the definition of an affix. Given that the morphs of `A`
are affixes, `x` is an affix when it is a bound morph that is not a root, and there is a root class
such that every occurrence of `x` occurs on a root and every root it occurs on is of that class. -/
def AffixStep (A : Set M) (x : M) : Prop :=
  L.IsBound x ∧ ¬ root x ∧ (∃ w ∈ L.forms, x ∈ w) ∧ ∃ c : RootClass, ∀ w ∈ L.forms, ∀ i < w.length,
    w[i]? = some x → (∃ y ∈ w, OccursOn root A w i y) ∧
      ∀ y ∈ w, OccursOn root A w i y → L.rootClass y = some c

instance [DecidableEq M] [DecidablePred root] (A : Set M) [DecidablePred (· ∈ A)] (x : M) :
    Decidable (L.AffixStep root A x) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ ∃ _ : RootClass, _))

/-- An affix is a morph in a set of morphs each of which is an affix given that the members of
the set are, so the affixes are the greatest solution of the definition. -/
def IsAffix (x : M) : Prop := ∃ A : Set M, x ∈ A ∧ ∀ y ∈ A, L.AffixStep root A y

variable {L root}

theorem AffixStep.not_root {A : Set M} {x : M} (h : L.AffixStep root A x) : ¬ root x :=
  h.2.1

theorem AffixStep.mem_flatten {A : Set M} {x : M} (h : L.AffixStep root A x) :
    x ∈ L.forms.flatten := by
  obtain ⟨w, hw, hx⟩ := h.2.2.1
  exact List.mem_flatten.2 ⟨w, hw, hx⟩

/-- The candidate sets can be restricted to sublists of the bound morphs of the inventory that
are not roots. -/
theorem isAffix_iff_sublists [DecidableEq M] [DecidablePred root] {x : M} :
    L.IsAffix root x ↔
      ∃ A ∈ (L.forms.flatten.dedup.filter fun y ↦ L.IsBound y ∧ ¬ root y).sublists,
        x ∈ A ∧ ∀ y ∈ A, L.AffixStep root {z | z ∈ A} y := by
  constructor
  · rintro ⟨A, hx, hA⟩
    classical
    refine ⟨(L.forms.flatten.dedup.filter fun y ↦ L.IsBound y ∧ ¬ root y).filter (· ∈ A),
      List.mem_sublists.2 (List.filter_sublist), ?_, fun y hy ↦ ?_⟩
    · have := hA x hx
      simp [hx, this.mem_flatten, this.1, this.not_root]
    · have hset : {z | z ∈ (L.forms.flatten.dedup.filter fun y ↦ L.IsBound y ∧ ¬ root y).filter
          (· ∈ A)} = A := by
        ext z
        simp only [Set.mem_ofPred_eq, List.mem_filter, List.mem_dedup, decide_eq_true_eq]
        exact ⟨fun h ↦ h.2, fun h ↦ ⟨⟨(hA z h).mem_flatten, (hA z h).1, (hA z h).not_root⟩, h⟩⟩
      rw [hset]
      exact hA y (by simpa using (List.mem_filter.1 hy).2)
  · rintro ⟨A, -, hx, hA⟩
    exact ⟨{z | z ∈ A}, hx, hA⟩

instance [DecidableEq M] [DecidablePred root] (x : M) : Decidable (L.IsAffix root x) :=
  decidable_of_iff _ isAffix_iff_sublists.symm

/-! ### The greatest solution -/

theorem AffixStep.mono (hF : ∀ w ∈ L.forms, RootsContiguous root w) {A B : Set M} (hAB : A ⊆ B)
    (hB : ∀ z ∈ B, ¬ root z) {x : M} (h : L.AffixStep root A x) : L.AffixStep root B x := by
  classical
  obtain ⟨hb, hr, ho, c, hc⟩ := h
  refine ⟨hb, hr, ho, c, fun w hw i hi hx ↦ ?_⟩
  obtain ⟨⟨y, hy, hyr, hyA⟩, hcA⟩ := hc w hw i hi hx
  have hyB := hyA.imp (·.mono hAB) (·.mono hAB)
  refine ⟨⟨y, hy, hyr, hyB⟩, fun y' hy' ⟨hy'r, hy'B⟩ ↦ ?_⟩
  suffices y' = y by subst this; exact hcA y' hy ⟨hyr, hyA⟩
  have hwi : w[i] = x := by simpa [List.getElem?_eq_getElem hi] using hx
  have side := hF w hw i hi (hwi ▸ hr)
  rcases hyB with hR | hL <;> rcases hy'B with hR' | hL'
  · exact Option.some_injective _ ((hR'.find?_eq hB hy'r).symm.trans (hR.find?_eq hB hyr))
  · exfalso
    rcases side with h | h
    exacts [h y' (List.mem_reverse.1 hL'.mem) hy'r, h y hR.mem hyr]
  · exfalso
    rcases side with h | h
    exacts [h y (List.mem_reverse.1 hL.mem) hyr, h y' hR'.mem hy'r]
  · exact Option.some_injective _ ((hL'.find?_eq hB hy'r).symm.trans (hL.find?_eq hB hyr))

variable (L root) in
/-- When roots are contiguous in every free form, the step taken over the morphs that are not
roots is a monotone map on sets of morphs. -/
def affixStep (hF : ∀ w ∈ L.forms, RootsContiguous root w) : Set M →o Set M where
  toFun A := {x | L.AffixStep root (A ∩ {z | ¬ root z}) x}
  monotone' _ _ h _ hx := hx.mono hF (Set.inter_subset_inter_left _ h) fun _ hz ↦ hz.2

/-- When roots are contiguous in every free form, the affixes are the greatest fixed point of the
step. -/
theorem setOf_isAffix_eq_gfp (hF : ∀ w ∈ L.forms, RootsContiguous root w) :
    {x | L.IsAffix root x} = (L.affixStep root hF).gfp := by
  have key {A : Set M} (hA : ∀ z ∈ A, ¬ root z) : A ∩ {z | ¬ root z} = A :=
    Set.inter_eq_left.2 hA
  apply le_antisymm
  · rintro x ⟨A, hx, hA⟩
    refine (L.affixStep root hF).le_gfp (fun y hy ↦ ?_) hx
    show L.AffixStep root (A ∩ {z | ¬ root z}) y
    rw [key fun z hz ↦ (hA z hz).not_root]
    exact hA y hy
  · intro x hx
    have hnr : ∀ z ∈ (L.affixStep root hF).gfp, ¬ root z := fun z hz ↦ by
      rw [← (L.affixStep root hF).map_gfp] at hz; exact hz.not_root
    refine ⟨_, hx, fun y hy ↦ ?_⟩
    rw [← (L.affixStep root hF).map_gfp] at hy
    have : L.AffixStep root (_ ∩ {z | ¬ root z}) y := hy
    rwa [key hnr] at this

/-! ### Clitics, required affixes and words -/

variable (L root)

/-- A clitic is a bound morph that is neither a root nor an affix. -/
def IsClitic (x : M) : Prop :=
  L.IsBound x ∧ ¬ root x ∧ ¬ L.IsAffix root x ∧ ∃ w ∈ L.forms, x ∈ w

/-- In the free form `w`, the morph `y` at `i` is an affix that occurs on the root `r`. -/
def IsAffixOnAt (w : List M) (i : ℕ) (y r : M) : Prop :=
  w[i]? = some y ∧ L.IsAffix root y ∧ OccursOn root {z | L.IsAffix root z} w i r

/-- A root requires an affix when every free form containing it has an affix on it. -/
def RequiresAffix (r : M) : Prop :=
  ∀ w ∈ L.forms, r ∈ w → ∃ i < w.length, ∃ y ∈ w, L.IsAffixOnAt root w i y r

/-- A required affix of a root is an affix on it when the root requires an affix, so that the
affix must be present unless another replaces it. -/
def IsRequiredAffix (x r : M) : Prop :=
  L.RequiresAffix root r ∧ ∃ w ∈ L.forms, ∃ i < w.length, L.IsAffixOnAt root w i x r

/-- A word is a form of the language that is a free morph, a clitic, or a root with affixes,
among them an affix if the root requires one. Compounds are not covered. -/
def IsWord (w : List M) : Prop :=
  (∃ f ∈ L.forms, w <:+: f) ∧
    ((∃ x ∈ w, w = [x] ∧ ([x] ∈ L.forms ∨ L.IsClitic root x)) ∨
      ∃ r ∈ w, root r ∧ ¬ List.Duplicate r w ∧ (∀ y ∈ w, y = r ∨ L.IsAffix root y) ∧
        (L.RequiresAffix root r → ∃ y ∈ w, y ≠ r))

section Decidable
variable [DecidableEq M] [DecidablePred root]

instance (x : M) : Decidable (L.IsClitic root x) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ ∃ w ∈ L.forms, _))

instance (w : List M) (i : ℕ) (y r : M) : Decidable (L.IsAffixOnAt root w i y r) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

instance (r : M) : Decidable (L.RequiresAffix root r) :=
  inferInstanceAs (Decidable (∀ w ∈ L.forms, _))

instance (x r : M) : Decidable (L.IsRequiredAffix root x r) :=
  inferInstanceAs (Decidable (_ ∧ ∃ w ∈ L.forms, _))

instance (w : List M) : Decidable (L.IsWord root w) :=
  inferInstanceAs (Decidable ((∃ f ∈ L.forms, _) ∧ _))

end Decidable

end Inventory

end Morphology.Comparative
