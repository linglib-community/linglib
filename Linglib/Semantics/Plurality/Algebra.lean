module

public import Linglib.Semantics.Mereology

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
* `Mereology.AtomJoinPrime E`: an atom below a sum lies below a summand.
* `Mereology.Individual α`: Link's model, the nonempty sets of atoms under union.

## Main results

* `Mereology.algClosure_iff_of_atom`: on an atom, `*P` and `P` agree.
* `Mereology.IsDistr.of_algClosure_of_atom_le`: Link's distributive inference, for
  join-prime atoms.
* `Mereology.IsDistr.properPlural_sup`, `Mereology.cum_properPlural`: the sum
  of two distinct atoms of a distributive predicate is a proper plural, and proper plurals are
  closed under sum.
* `Mereology.algClosure_image_singleton`: on finite sets of individuals, taken as
  singletons, `*` holds of exactly the nonempty subsets, Sternefeld's identification of `*P` with
  `D P` (15), and the full closure `Mereology.FullAlgClosure`, Bylinina and Nouwen's `×`, of
  all subsets (`fullAlgClosure_image_singleton`).
* `Mereology.card_image_fullAlgClosure`, `Mereology.card_image_algClosure`: the
  pluralities of `×S` have `0, …, |S|` atoms and those of `*S` have `1, …, |S|`, so only with
  the empty sum does a count's set of degrees reach `0`.

## Implementation notes

Link's model is a complete join semilattice with atoms and without a bottom; only `SemilatticeSup E`
and `Mereology.Atom` are used here. The plural closure `*P` is `Mereology.AlgClosure P`, mathlib's
`supClosure` of the extension of `P`. The complete atomic Boolean algebra of Landman and Champollion
is a stronger assumption, which enters only through `AtomJoinPrime`. Schwarzschild's set-based
ontology, where an individual is its singleton and sum is union, is the `Finset α` instance; Link's
own model of nonempty sets of atoms has no bottom (`Individual`). Where the carrier has one,
`*P` still excludes it unless `P` holds of it, and `×P` adds it whatever `P` is.

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

variable {E : Type*} [SemilatticeSup E] {P Q : E → Prop} {x y : E}

/-! ### Predicate operators -/

/-- The proper plural `⊕P` holds of the elements of `*P` that are not atoms (D.12). -/
def properPlural (P : E → Prop) (x : E) : Prop :=
  AlgClosure P x ∧ ¬ Atom x

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
theorem algClosure_iff_of_atom (hx : Atom x) : AlgClosure P x ↔ P x :=
  ⟨(of_algClosure_of_atom · hx), .base⟩

theorem IsDistr.not_properPlural (hP : IsDistr P) (hx : P x) : ¬ properPlural P x :=
  fun h ↦ h.2 (hP x hx)

/-- The sum of two distinct atoms of a distributive predicate is a proper plural. -/
theorem IsDistr.properPlural_sup (hP : IsDistr P) (hx : P x) (hy : P y) (hne : x ≠ y) :
    properPlural P (x ⊔ y) :=
  ⟨.sum (.base hx) (.base hy), not_atom_sup_of_ne (hP x hx) (hP y hy) hne⟩

/-- Proper plurals are closed under sum. -/
theorem cum_properPlural : CUM (properPlural P) := by
  rintro x ⟨hx, hx'⟩ y ⟨hy, hy'⟩
  refine ⟨.sum hx hy, fun h ↦ ?_⟩
  by_cases hx0 : IsBot x
  · rw [sup_eq_right.mpr (hx0 _)] at h
    exact hy' h
  · exact hx' ((h.eq le_sup_left hx0) ▸ h)

/-- Atoms are join-prime when an atom below a sum lies below one of the summands, as in a
Boolean algebra. -/
def AtomJoinPrime (E : Type*) [SemilatticeSup E] : Prop :=
  ∀ (a : E), Atom a → ∀ (x y : E), a ≤ x ⊔ y → a ≤ x ∨ a ≤ y

/-- If atoms are join-prime, every atomic part of an element of `*P` satisfies a distributive
`P`. -/
theorem IsDistr.of_algClosure_of_atom_le (hP : IsDistr P) (hJP : AtomJoinPrime E)
    (h : AlgClosure P x) (hy : Atom y) (hle : y ≤ x) : P y := by
  induction h with
  | base hp => exact ((hP _ hp).eq hle hy.not_isBot) ▸ hp
  | @sum a b _ _ iha ihb => exact (hJP y hy a b hle).elim iha ihb

/-! ### Sets of individuals

In Schwarzschild's set-based ontology, pluralities are finite sets of individuals, an
individual is its singleton, and sum is union. -/

section Finset
variable {α : Type*} [DecidableEq α]

/-- `*` of a set of individuals, taken as singletons, holds of exactly its nonempty subsets. -/
theorem algClosure_image_singleton (S : Set α) (x : Finset α) :
    AlgClosure (· ∈ ({·} : α → Finset α) '' S) x ↔ x.Nonempty ∧ ↑x ⊆ S := by
  constructor
  · intro h
    induction h with
    | base h => obtain ⟨a, ha, rfl⟩ := h; exact ⟨Finset.singleton_nonempty a, by simpa⟩
    | sum _ _ ih ih' =>
      refine ⟨ih.1.mono Finset.subset_union_left, ?_⟩
      rw [Finset.sup_eq_union, Finset.coe_union]
      exact Set.union_subset ih.2 ih'.2
  · rintro ⟨hx, hS⟩
    have key : x.sup' hx (fun a ↦ ({a} : Finset α)) = x :=
      le_antisymm ((Finset.sup'_le_iff _ _).2 fun a ha ↦ Finset.singleton_subset_iff.2 ha)
        (Finset.subset_iff.2 fun a ha ↦
          Finset.singleton_subset_iff.1 (Finset.le_sup' (fun a ↦ ({a} : Finset α)) ha))
    rw [← key]
    exact algClosure_finsetSup' hx fun a ha ↦ .base ⟨a, hS ha, rfl⟩

theorem algClosure_iff_of_subset_range_singleton {P : Finset α → Prop}
    (hP : {x | P x} ⊆ Set.range ({·} : α → Finset α)) (x : Finset α) :
    AlgClosure P x ↔ x.Nonempty ∧ ∀ a ∈ x, P {a} := by
  have : P = (· ∈ ({·} : α → Finset α) '' {a | P {a}}) := by
    ext s
    constructor
    · intro hs
      obtain ⟨a, rfl⟩ := hP hs
      exact ⟨a, hs, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ha
  conv_lhs => rw [this]
  rw [algClosure_image_singleton]
  exact Iff.rfl

/-- `×` of a set of individuals, taken as singletons, holds of exactly its subsets, the empty one
among them. -/
theorem fullAlgClosure_image_singleton (S : Set α) (x : Finset α) :
    FullAlgClosure (· ∈ ({·} : α → Finset α) '' S) x ↔ ↑x ⊆ S := by
  rw [FullAlgClosure, algClosure_image_singleton]
  refine ⟨fun h ↦ h.elim And.right fun h ↦ by simp [h], fun h ↦ ?_⟩
  rcases x.eq_empty_or_nonempty with rfl | hx
  exacts [.inr rfl, .inl ⟨hx, h⟩]

/-- The pluralities of `×S` for a finite `S` number `0, …, |S|` atoms. -/
theorem card_image_fullAlgClosure {S : Set α} (h : S.Finite) :
    Finset.card '' {x | FullAlgClosure (· ∈ ({·} : α → Finset α) '' S) x} = Set.Iic S.ncard := by
  rw [show {x | FullAlgClosure (· ∈ ({·} : α → Finset α) '' S) x} = {x | x ⊆ h.toFinset} from
    Set.ext fun x ↦ (fullAlgClosure_image_singleton S x).trans h.subset_toFinset.symm,
    Set.ncard_eq_toFinset_card _ h]
  ext d
  exact ⟨fun ⟨x, hx, hd⟩ ↦ hd ▸ Finset.card_le_card hx,
    fun hd ↦ let ⟨y, hy, hc⟩ := Finset.exists_subset_card_eq hd; ⟨y, hy, hc⟩⟩

/-- Those of `*S` number `1, …, |S|`: without the empty sum no plurality has zero atoms. -/
theorem card_image_algClosure {S : Set α} (h : S.Finite) :
    Finset.card '' {x | AlgClosure (· ∈ ({·} : α → Finset α) '' S) x} = Set.Icc 1 S.ncard := by
  rw [show {x | AlgClosure (· ∈ ({·} : α → Finset α) '' S) x} =
      {x | x.Nonempty ∧ x ⊆ h.toFinset} from
    Set.ext fun x ↦
      (algClosure_image_singleton S x).trans (and_congr_right' h.subset_toFinset.symm),
    Set.ncard_eq_toFinset_card _ h]
  ext d
  refine ⟨fun ⟨x, ⟨hx, hS⟩, hd⟩ ↦ hd ▸ ⟨hx.card_pos, Finset.card_le_card hS⟩, fun ⟨h1, hd⟩ ↦ ?_⟩
  obtain ⟨y, hy, hc⟩ := Finset.exists_subset_card_eq hd
  exact ⟨y, ⟨Finset.card_pos.1 (hc ▸ h1), hy⟩, hc⟩

end Finset

/-! ### Link's model

An individual is a nonempty set of atoms, an atom its singleton, and sum is union. The empty set
is no individual, so the carrier has no bottom. -/

section Link

variable {α : Type*}

/-- An individual of Link's model is a nonempty set of atoms. -/
abbrev Individual (α : Type*) := {s : Set α // s.Nonempty}

instance : SemilatticeSup (Individual α) := Subtype.semilatticeSup fun _ _ hx _ ↦ hx.inl

/-- The atomic individual `Individual.atom a` is the singleton of `a`. -/
def Individual.atom (a : α) : Individual α := ⟨{a}, Set.singleton_nonempty a⟩

end Link

end Mereology
