module

public import Linglib.Semantics.Mereology.Atomic
public import Linglib.Semantics.Mereology.Classical
public import Linglib.Semantics.Plurality.Number

/-!
# Link's algebra of plurals

Link models plural and mass reference with a join semilattice `E` of individuals, in which
`x ⊔ y` is the sum of `x` and `y`. The plural closure `*P` of a predicate holds of the sums of
its members, and the proper plural `⊕P` holds of the sums that are not atoms. A materialization
sends each individual to the matter it is made of and preserves sums. On finite sets of
individuals, `*` reduces to distribution over members.

## Definitions

* `Mereology.properPlural P`: the non-atomic elements of `*P`.
* `Mereology.IsDistr P`: `P` holds of atoms only.
* `Mereology.Inv h P`: `P` does not distinguish `h`-equivalent individuals.
* `Mereology.D P x`: Link's 1987 distributive operator.
* `Mereology.Materialization E M`: a `SupHom E M`, with `Mereology.mPart` and
  `Mereology.mEquiv` the preorder and equivalence it induces on `E`.
* `Mereology.Individual α`: Link's model, the nonempty sets of atoms under union.

## Main results

* `Mereology.mem_supClosure_iff_of_atom`: on an atom, `*P` and `P` agree.
* `Mereology.IsDistr.of_mem_supClosure_of_atom_le`: Link's distributive inference, where joins
  are sums.
* `Mereology.IsDistr.properPlural_sup`, `Mereology.cum_properPlural`: the sum
  of two distinct atoms of a distributive predicate is a proper plural, and proper plurals are
  closed under sum.
* `Mereology.mem_supClosure_image_singleton`: on finite sets of individuals, taken as
  singletons, `*` holds of exactly the nonempty subsets, Sternefeld's identification of `*P` with
  `D P` (15), and the full closure `Mereology.fullSupClosure`, Bylinina and Nouwen's `×`, of
  all subsets (`mem_fullSupClosure_image_singleton`).
* `Mereology.card_image_fullSupClosure`, `Mereology.card_image_supClosure`: the
  pluralities of `×S` have `0, …, |S|` atoms and those of `*S` have `1, …, |S|`, so only with
  the empty sum does a count's set of degrees reach `0`.

## Implementation notes

Link's model is a complete join semilattice with atoms and without a bottom; only `SemilatticeSup E`
and `Mereology.Atom` are used here. The plural closure `*P` is mathlib's
`supClosure` of the extension of `P`. The complete atomic Boolean algebra of Landman and Champollion
is a stronger assumption, which enters only through `Mereology.SupIsSum`. Schwarzschild's set-based
ontology, where an individual is its singleton and sum is union, is the `Finset α` instance; Link's
own model of nonempty sets of atoms (`Individual`) is a classical mereology. Where the carrier has
a bottom, `*P` still excludes it unless `P` holds of it, and `×P` adds it whatever `P` is.

## References

* [G. Link, *The logical analysis of plurals and mass terms* (1983)][link-1983]
* [G. Link, *Generalized quantifiers and plurals* (1987)][link-1987]
* [M. Krifka, *Nominal reference, temporal constitution and quantification in event semantics*
  (1989)][krifka-1989]
* [F. Landman, *Events and plurality* (2000)][landman-2000]
* [L. Champollion, *Parts of a whole* (2017)][champollion-2017]
* [L. Champollion, *Distributivity in formal semantics* (2019)][champollion-2019]
* [R. Schwarzschild, *Pluralities* (1996)][schwarzschild-1996]
* [W. Sternefeld, *Reciprocity and cumulative predication* (1998)][sternefeld-1998]
* [L. Bylinina and R. Nouwen, *On 'zero' and semantic plurality* (2018)][bylinina-nouwen-2018]
-/

@[expose] public section

namespace Mereology

variable {E : Type*} [SemilatticeSup E] {P Q : E → Prop} {s : Set E} {x y : E}

/-! ### Predicate operators -/

/-- The proper plural `⊕P` holds of the elements of `*P` that are not atoms (D.12), Harbour's
`[−atomic]` of the closure. -/
def properPlural (s : Set E) : Set E :=
  supClosure s \ {x | Atom x}

/-- A distributive predicate holds of atoms only (D.19). -/
def IsDistr (P : E → Prop) : Prop :=
  ∀ x, P x → Atom x

/-- An invariant predicate does not distinguish individuals that `h` identifies (D.21). -/
def Inv {M : Type*} (h : E → M) (P : E → Prop) : Prop :=
  ∀ x y, h x = h y → (P x ↔ P y)

/-- The distributive operator `D P` holds of `x` when every atomic part of `x` satisfies `P`. -/
def D (P : E → Prop) (x : E) : Prop :=
  ∀ y ≤ x, Atom y → P y

theorem D_of_atom (hx : Atom x) (hP : P x) : D P x :=
  fun _ hle hy ↦ (hx.eq hle hy.not_isBot) ▸ hP

theorem D_mono (h : ∀ x, P x → Q x) (hD : D P x) : D Q x :=
  fun y hle hy ↦ h y (hD y hle hy)

/-! ### Materialization -/

section Constitution

variable {M : Type*} [SemilatticeSup M]

/-- A materialization (D.22) is a sum-preserving map from individuals to their portions of
matter. -/
abbrev Materialization (E M : Type*) [SemilatticeSup E] [SemilatticeSup M] :=
  SupHom E M

/-- `x` is a material part of `y` (D.23) when the matter of `x` is part of the matter of `y`. -/
def mPart (h : Materialization E M) (x y : E) : Prop :=
  h x ≤ h y

/-- `x` and `y` are materially equivalent (D.24) when they are made of the same matter. -/
def mEquiv (h : Materialization E M) (x y : E) : Prop :=
  h x = h y

theorem mPart_of_le (h : Materialization E M) (hxy : x ≤ y) : mPart h x y :=
  OrderHomClass.mono h hxy

theorem equivalence_mEquiv (h : Materialization E M) : Equivalence (mEquiv h) :=
  ⟨fun _ ↦ rfl, Eq.symm, Eq.trans⟩

theorem mEquiv_iff (h : Materialization E M) : mEquiv h x y ↔ mPart h x y ∧ mPart h y x :=
  le_antisymm_iff

theorem Inv.iff_of_mEquiv {h : Materialization E M} (hP : Inv (⇑h) P) (hxy : mEquiv h x y) :
    P x ↔ P y :=
  hP x y hxy

end Constitution

/-! ### Link's theorems -/

/-- On an atom, `*P` and `P` agree (T.8). -/
theorem mem_supClosure_iff_of_atom (hx : Atom x) : x ∈ supClosure s ↔ x ∈ s :=
  ⟨(mem_of_mem_supClosure_of_atom · hx), fun h ↦ subset_supClosure h⟩

theorem IsDistr.not_properPlural (hP : IsDistr P) (hx : P x) : x ∉ properPlural {x | P x} :=
  fun h ↦ h.2 (hP x hx)

/-- The sum of two distinct atoms of a distributive predicate is a proper plural. -/
theorem IsDistr.properPlural_sup (hP : IsDistr P) (hx : P x) (hy : P y) (hne : x ≠ y) :
    x ⊔ y ∈ properPlural {x | P x} :=
  ⟨supClosed_supClosure (subset_supClosure hx) (subset_supClosure hy),
    not_atom_sup_of_ne (hP x hx) (hP y hy) hne⟩

/-- Proper plurals are closed under sum. -/
theorem cum_properPlural : CUM (properPlural s) := by
  rintro x ⟨hx, hx'⟩ y ⟨hy, hy'⟩
  refine ⟨supClosed_supClosure hx hy, fun h ↦ ?_⟩
  by_cases hx0 : IsBot x
  · rw [sup_eq_right.mpr (hx0 _)] at h
    exact hy' h
  · exact hx' ((h.eq le_sup_left hx0) ▸ h)

/-- Where joins are sums, every atomic part of an element of `*P` satisfies a distributive
`P`. -/
theorem IsDistr.of_mem_supClosure_of_atom_le [SupIsSum E] (hP : IsDistr P)
    (h : x ∈ supClosure {x | P x}) (hy : Atom y) (hle : y ≤ x) : P y := by
  induction h using supClosure_induction with
  | mem a hp => exact ((hP _ hp).eq hle hy.not_isBot) ▸ hp
  | sup a b _ _ iha ihb => exact (hy.le_sup_iff.1 hle).elim iha ihb

/-! ### Sets of individuals

In Schwarzschild's set-based ontology, pluralities are finite sets of individuals, an
individual is its singleton, and sum is union. -/

section Finset
variable {α : Type*} [DecidableEq α]

/-- `*` of a set of individuals, taken as singletons, holds of exactly its nonempty subsets. -/
theorem mem_supClosure_image_singleton (S : Set α) (x : Finset α) :
    x ∈ supClosure (({·} : α → Finset α) '' S) ↔ x.Nonempty ∧ ↑x ⊆ S := by
  constructor
  · intro h
    induction h using supClosure_induction with
    | mem _ h => obtain ⟨a, ha, rfl⟩ := h; exact ⟨Finset.singleton_nonempty a, by simpa⟩
    | sup _ _ _ _ ih ih' =>
      refine ⟨ih.1.mono Finset.subset_union_left, ?_⟩
      rw [Finset.coe_union]
      exact Set.union_subset ih.2 ih'.2
  · rintro ⟨hx, hS⟩
    have key : x.sup' hx (fun a ↦ ({a} : Finset α)) = x :=
      le_antisymm ((Finset.sup'_le_iff _ _).2 fun a ha ↦ Finset.singleton_subset_iff.2 ha)
        (Finset.subset_iff.2 fun a ha ↦
          Finset.singleton_subset_iff.1 (Finset.le_sup' (fun a ↦ ({a} : Finset α)) ha))
    rw [← key]
    exact finsetSup'_mem_supClosure hx fun a ha ↦ ⟨a, hS ha, rfl⟩

theorem mem_supClosure_iff_of_subset_range_singleton {s : Set (Finset α)}
    (hs : s ⊆ Set.range ({·} : α → Finset α)) (x : Finset α) :
    x ∈ supClosure s ↔ x.Nonempty ∧ ∀ a ∈ x, {a} ∈ s := by
  have : s = ({·} : α → Finset α) '' {a | {a} ∈ s} := by
    ext t
    constructor
    · intro ht
      obtain ⟨a, rfl⟩ := hs ht
      exact ⟨a, ht, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ha
  conv_lhs => rw [this]
  rw [mem_supClosure_image_singleton]
  exact Iff.rfl

/-- `×` of a set of individuals, taken as singletons, holds of exactly its subsets, the empty one
among them. -/
theorem mem_fullSupClosure_image_singleton (S : Set α) (x : Finset α) :
    x ∈ fullSupClosure (({·} : α → Finset α) '' S) ↔ ↑x ⊆ S := by
  rw [fullSupClosure, Set.mem_insert_iff, mem_supClosure_image_singleton]
  refine ⟨fun h ↦ h.elim (fun h ↦ by simp [h]) And.right, fun h ↦ ?_⟩
  rcases x.eq_empty_or_nonempty with rfl | hx
  exacts [.inl rfl, .inr ⟨hx, h⟩]

/-- The pluralities of `×S` for a finite `S` number `0, …, |S|` atoms. -/
theorem card_image_fullSupClosure {S : Set α} (h : S.Finite) :
    Finset.card '' fullSupClosure (({·} : α → Finset α) '' S) = Set.Iic S.ncard := by
  rw [show fullSupClosure (({·} : α → Finset α) '' S) = {x | x ⊆ h.toFinset} from
    Set.ext fun x ↦ (mem_fullSupClosure_image_singleton S x).trans h.subset_toFinset.symm,
    Set.ncard_eq_toFinset_card _ h]
  ext d
  exact ⟨fun ⟨x, hx, hd⟩ ↦ hd ▸ Finset.card_le_card hx,
    fun hd ↦ let ⟨y, hy, hc⟩ := Finset.exists_subset_card_eq hd; ⟨y, hy, hc⟩⟩

/-- Those of `*S` number `1, …, |S|`: without the empty sum no plurality has zero atoms. -/
theorem card_image_supClosure {S : Set α} (h : S.Finite) :
    Finset.card '' supClosure (({·} : α → Finset α) '' S) = Set.Icc 1 S.ncard := by
  rw [show supClosure (({·} : α → Finset α) '' S) = {x | x.Nonempty ∧ x ⊆ h.toFinset} from
    Set.ext fun x ↦
      (mem_supClosure_image_singleton S x).trans (and_congr_right' h.subset_toFinset.symm),
    Set.ncard_eq_toFinset_card _ h]
  ext d
  refine ⟨fun ⟨x, ⟨hx, hS⟩, hd⟩ ↦ hd ▸ ⟨hx.card_pos, Finset.card_le_card hS⟩, fun ⟨h1, hd⟩ ↦ ?_⟩
  obtain ⟨y, hy, hc⟩ := Finset.exists_subset_card_eq hd
  exact ⟨y, ⟨Finset.card_pos.1 (hc ▸ h1), hy⟩, hc⟩

end Finset

/-! ### Link's model

An individual is a nonempty set of atoms, an atom its singleton, and sum is union. The
individuals are the non-null elements of the Boolean algebra of sets, so they form a classical
mereology, atomic and with no null individual once there are two atoms. -/

section Link

variable {α : Type*}

/-- An individual of Link's model is a nonempty set of atoms. -/
abbrev Individual (α : Type*) := {s : Set α // s.Nonempty}

instance : SemilatticeSup (Individual α) := Subtype.semilatticeSup fun _ _ hx _ ↦ hx.inl

/-- The atomic individual `Individual.atom a` is the singleton of `a`. -/
def Individual.atom (a : α) : Individual α := ⟨{a}, Set.singleton_nonempty a⟩

instance : IsClassicalMereology (Individual α) :=
  .subtype fun s ↦ by rw [isBot_iff_eq_bot, Set.bot_eq_empty, Set.nonempty_iff_ne_empty]

instance [Nontrivial α] : NoBotOrder (Individual α) where
  exists_not_ge x :=
    let ⟨a, ha⟩ := x.2
    let ⟨b, hb⟩ := exists_ne a
    ⟨.atom b, fun h ↦ hb.symm (h ha)⟩

/-- With two atoms or more, the singletons are atoms. -/
theorem Individual.atom_atom [Nontrivial α] (a : α) : Atom (Individual.atom a) :=
  atom_iff_isMin.2 fun y hy b hb ↦ by
    obtain ⟨c, hc⟩ := y.2
    rwa [Set.mem_singleton_iff.1 hb, ← Set.mem_singleton_iff.1 (hy hc)]

instance [Nontrivial α] : Atomic (Individual α) where
  exists_atom_le x _ :=
    let ⟨a, ha⟩ := x.2
    ⟨.atom a, Individual.atom_atom a, Set.singleton_subset_iff.2 ha⟩

end Link

end Mereology
