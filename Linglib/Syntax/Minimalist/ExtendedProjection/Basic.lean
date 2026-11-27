/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.ExtendedProjection.Cited
public import Linglib.Syntax.Spine.ExtendedProjection
public import Linglib.Syntax.Spine.Hierarchy
public import Mathlib.Order.Comparable

/-!
# The hierarchy of the categories

This file defines a preorder on `Minimalist.Cat`, the hierarchy of the cited spines. A category `c`
is no higher than a category `d`, written `c ≤ d`, when steps of the cited spines lead from `c` up
to `d`.

Categories that the cited structures order in both ways are each no higher than the other. This
holds of tense and each of aspect, modality, mood, the evidential, negation and polarity, of topic
and focus, and of Force and each of the complementizer and the speech-act head. The order is strict
from the verb through little v, Voice, tense, finiteness and focus to Force, and from the noun
through the dividing head, the counting head and the determiner to the case shell. The nominalizer
and the complementizer are incomparable.

The order relates only categories of the same family, and the lexical head of a family is no higher
than any category of the family. A spine of categories is therefore an extended projection, with
respect to the families of the categories and this order, if and only if it is a chain for the
order.

## Main definitions

* `Minimalist.Cat.preorder`: the order, a scoped instance.
* `Cartography.Head.catHom`: the category of a head of Cinque's hierarchy, as an order
  homomorphism.

## Main results

* `Minimalist.Cat.monotone_iff`: a map from the categories to a preorder is monotone if and only if
  its values do not decrease along any cited spine.
* `Minimalist.Cat.le_iff_forall_le`: `c ≤ d` if and only if `f c ≤ f d` for every `f : Cat → ℕ`
  whose values do not decrease along any cited spine.
* `Minimalist.Cat.family_eq_of_le`, `Minimalist.Cat.lexical_le_iff`: the order relates only
  categories of the same family, and the lexical head of a family is no higher than exactly the
  categories of that family.
* `Minimalist.Cat.antisymmRel_T`, `Minimalist.Cat.antisymmRel_Top_Foc`,
  `Minimalist.Cat.antisymmRel_Force`, `Minimalist.Cat.isChain_lt`,
  `Minimalist.Cat.incompRel_Nmlz_C`: the facts about particular categories stated above.
* `Spine.isExtendedProjection_family_iff_isChain`: a spine of categories is an extended projection
  if and only if it is a chain for the order.

## Implementation notes

The instance is scoped. `Minimalist.Cat` carries no order unless a file opens the namespace
`Minimalist.ExtendedProjection`, and an account that orders heads by selection alone uses the
categories without it.

Citing a further structure can only enlarge the order. A statement `c ≤ d` therefore remains true
under further citations, while a statement `c < d` or `IncompRel (· ≤ ·) c d` is about the
structures cited so far.

Grimshaw leaves open whether the functional value must increase from each head to the next or may
stay the same. Here it may stay the same, since a cited spine can repeat a head. For Grimshaw the
adposition is the highest head of the nominal projection, as the complementizer is of the verbal
one. Here it is the lexical head of a family of its own.

## References

* [grimshaw-2000]
-/

@[expose] public section

namespace Minimalist

namespace Cat

variable {c d : Cat} {s : Spine Cat} {x : CitedStructure}

/-! ### The order -/

/-- A category `c` is **no higher than** a category `d`, written `c ≤ d`, when steps of the cited
spines lead from `c` up to `d`. The instance is scoped and is opened with
`open scoped Minimalist.ExtendedProjection`. -/
@[instance_reducible]
protected def preorder : Preorder Cat where
  le := Relation.ReflTransGen (Spine.Step {s | s ∈ citedSpines})
  le_refl _ := .refl
  le_trans _ _ _ := .trans

namespace _root_.Minimalist.ExtendedProjection

scoped[Minimalist.ExtendedProjection] attribute [instance] Minimalist.Cat.preorder

end _root_.Minimalist.ExtendedProjection

open scoped ExtendedProjection

theorem le_iff_reflTransGen :
    c ≤ d ↔ Relation.ReflTransGen (Spine.Step {s | s ∈ citedSpines}) c d := Iff.rfl

/-- The order of the categories is decidable, by search along the steps of the cited spines. The
definition is irreducible, so that elaboration does not unfold it; `decide +kernel` evaluates
it. -/
@[irreducible] protected def decidableLE : DecidableLE Cat :=
  Spine.decidableReflTransGenStep citedSpines

@[instance_reducible]
protected def decidableLT : DecidableLT Cat := @decidableLTOfDecidableLE _ _ Cat.decidableLE

namespace _root_.Minimalist.ExtendedProjection

scoped[Minimalist.ExtendedProjection] attribute [instance] Minimalist.Cat.decidableLE
  Minimalist.Cat.decidableLT

end _root_.Minimalist.ExtendedProjection

theorem isChain_le (hs : s ∈ x.spines) : s.heads.IsChain (· ≤ ·) :=
  Spine.isChain_reflTransGen_step (mem_citedSpines hs)

theorem pairwise_le (hs : s ∈ x.spines) : s.heads.Pairwise (· ≤ ·) :=
  List.isChain_iff_pairwise.1 (isChain_le hs)

theorem rel_of_le {β : Type*} {r : β → β → Prop} [Std.Refl r] [IsTrans β r] (f : Cat → β)
    (hf : ∀ s ∈ citedSpines, (s.map f).heads.IsChain r) (h : c ≤ d) : r (f c) (f d) :=
  Spine.forall_reflTransGen_step_iff.2 hf c d h

/-- A map from the categories to a preorder is monotone if and only if its values do not decrease
along any cited spine. -/
theorem monotone_iff {β : Type*} [Preorder β] {f : Cat → β} :
    Monotone f ↔ ∀ s ∈ citedSpines, (s.map f).heads.IsChain (· ≤ ·) :=
  ⟨fun hf ↦ Spine.forall_reflTransGen_step_iff.1 fun _ _ h ↦ hf h,
    fun h _ _ hcd ↦ rel_of_le _ h hcd⟩

/-- `c ≤ d` if and only if `f c ≤ f d` for every `f : Cat → ℕ` whose values do not decrease along
any cited spine. -/
theorem le_iff_forall_le :
    c ≤ d ↔ ∀ f : Cat → ℕ, (∀ s ∈ citedSpines, (s.map f).heads.IsChain (· ≤ ·)) → f c ≤ f d :=
  Spine.reflTransGen_step_iff_forall_le

/-! ### Families -/

/-- Categories related by the order have the same family. -/
theorem family_eq_of_le (h : c ≤ d) : c.family = d.family :=
  rel_of_le family (r := (· = ·)) (by decide +kernel) h

/-- The lexical head of the family of `c` is no higher than `c`. -/
theorem lexical_le (c : Cat) : c.family.lexical ≤ c := by
  cases c <;> decide +kernel

/-- The lexical head of a family `f` is no higher than `c` if and only if `c` is of family `f`. -/
theorem lexical_le_iff {f : CatFamily} : f.lexical ≤ c ↔ c.family = f :=
  ⟨fun h ↦ by simpa using (family_eq_of_le h).symm, fun h ↦ h ▸ lexical_le c⟩

/-! ### Particular categories -/

/-- Each of aspect, modality, mood, the evidential, negation and polarity is no higher than tense,
and tense is no higher than it. -/
theorem antisymmRel_T : ∀ c ∈ [Cat.Asp, .Mod, .Mood, .Evid, .Neg, .Pol],
    AntisymmRel (· ≤ ·) c .T := by
  decide +kernel

/-- Topic is no higher than focus, and focus is no higher than topic. -/
theorem antisymmRel_Top_Foc : AntisymmRel (· ≤ ·) Cat.Top .Foc := by decide +kernel

/-- Each of the complementizer and the speech-act head is no higher than Force, and Force is no
higher than it. -/
theorem antisymmRel_Force : ∀ c ∈ [Cat.C, .SA], AntisymmRel (· ≤ ·) c .Force := by
  decide +kernel

/-- The order is strict from the verb through little v, Voice, tense, finiteness and focus to
Force, and from the noun through the dividing head, the counting head and the determiner to the
case shell. -/
theorem isChain_lt :
    [Cat.V, .v, .Voice, .T, .Fin, .Foc, .Force].IsChain (· < ·) ∧
      [Cat.N, .Q, .Num, .D, .K].IsChain (· < ·) := by
  decide +kernel

/-- The nominalizer and the complementizer are incomparable. -/
theorem incompRel_Nmlz_C : IncompRel (· ≤ ·) Cat.Nmlz .C := by decide +kernel

end Cat

end Minimalist

namespace Cartography.Head

open Minimalist

open scoped Minimalist.ExtendedProjection

/-- `Cartography.Head.cat` is monotone from Cinque's hierarchy to the order of the categories. -/
theorem cat_mono : Monotone cat := fun x y h ↦ by
  have hp : hierarchy.Pairwise fun x y ↦ x.cat ≤ y.cat :=
    List.pairwise_map.1 (Cat.pairwise_le (x := .cinque1999) List.mem_cons_self)
  exact List.Pairwise.forall_of_forall_of_flip (R := fun x y ↦ x ≤ y → x.cat ≤ y.cat)
    (fun _ _ _ ↦ le_rfl) (hp.imp (S := fun x y : Head ↦ x ≤ y → x.cat ≤ y.cat) fun h _ ↦ h)
    (pairwise_hierarchy.imp fun hlt hle ↦ absurd hlt hle.not_gt) (mem_hierarchy x)
    (mem_hierarchy y) h

/-- The order homomorphism `catHom` is `Cartography.Head.cat`, from Cinque's hierarchy to the
categories. -/
def catHom : Head →o Cat := ⟨cat, cat_mono⟩

@[simp] theorem coe_catHom : ⇑catHom = cat := rfl

end Cartography.Head

namespace Spine

open Minimalist

open scoped Minimalist.ExtendedProjection

variable {s : Spine Cat} {x : CitedStructure}

/-! ### Extended projections of the categories -/

/-- A spine of categories is an extended projection, with respect to the families of the categories
and their order, if and only if it is a chain for the order. -/
theorem isExtendedProjection_family_iff_isChain :
    s.IsExtendedProjection Cat.family (· ≤ ·) ↔ s.heads.IsChain (· ≤ ·) :=
  isExtendedProjection_iff_isChain fun _ _ ↦ Cat.family_eq_of_le

/-- Every spine of a cited structure is an extended projection. -/
theorem isExtendedProjection_of_mem_spines (hs : s ∈ x.spines) :
    s.IsExtendedProjection Cat.family (· ≤ ·) :=
  isExtendedProjection_family_iff_isChain.2 (Cat.isChain_le hs)

end Spine
