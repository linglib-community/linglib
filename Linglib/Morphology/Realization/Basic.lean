/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Finset.Option
public import Mathlib.Logic.Relator
public import Mathlib.Data.Set.Image
public import Mathlib.Order.Setoid.Basic

/-!
# Realizations: indices realized in context

A realization assigns to an index `r` and a context `c` the finite set `realize r c` of forms that
realize `r` in `c`: the exponent of a root at Vocabulary Insertion, the stem of a lexeme at a cell
of its paradigm. Each index has a relation `Rel r` between contexts and forms, and the deviations
from one form per cell are the ways this relation fails to be a bijection: the index is defective
where the relation is not total, overabundant where it is not single-valued, and syncretic where
it is not injective. The forms of an index across its contexts are its exponents; it is invariant
when they are at most one and suppletive when they are at least two. Read backwards, a realization
analyses a form: the cells of a form are the contexts in which it realizes an index. Realizations
are ordered by inclusion of the forms of each cell.

## Main definitions

* `Realization`: the forms that realize each index in each context.
* `Realization.Rel`, `Realization.IsLicensed`: the relation of an index between contexts and
  forms, and the contexts in which the index has a form.
* `Realization.IsDefective`, `Realization.IsOverabundant`, `Realization.IsSyncretic`: the three
  deviations from one form per cell.
* `Realization.exponents`, `Realization.IsInvariant`, `Realization.IsSuppletive`: the forms of an
  index, and whether they are at most one or at least two.
* `Realization.cells`: the contexts in which a form realizes an index.
* `Realization.ofOption`: the realization of a map that selects at most one form.

## Main results

* `Realization.isSuppletive_iff_isOverabundant_or_isProperlySuppletive`: an index is suppletive
  within one cell or across two.
* `Realization.isSyncretic_iff_cells`: an index is syncretic exactly when one of its forms fills
  two cells.
* `Realization.IsSuppletive.mono`, `Realization.IsOverabundant.mono`,
  `Realization.IsSyncretic.mono`: suppletion, overabundance and syncretism pass to a realization
  with more forms.

## Implementation notes

* The index is opaque, and the frameworks that separate an item from its form choose it
  differently: a root of Distributed Morphology, a phonological index in Borer's sense, a lexeme of
  Paradigm Function Morphology, Spencer's lexemic index. The interface does not say whether indices
  are listed or constructed.
* Totality, univalence and the absence of syncretism are `Relator.LeftTotal`, `Relator.RightUnique`
  and `Relator.LeftUnique` of `Rel r`, and the same properties of the transpose compare indices in
  one context. Invariance and suppletion are `Set.Subsingleton` and `Set.Nontrivial` of
  `exponents`.
* Syncretism is two contexts sharing a form. Where no cell has two forms this is the kernel of
  `realize r`, an equivalence on contexts; with overabundant cells it need not be transitive.

## References

* [harley-2014]
* [marantz-1997]
* [embick-2021]
* [borer-2013]
* [stump-2001]
* [bonami-stump-2016]
* [spencer-2013]
* [beard-1995]
* [haspelmath-2025b]
* [lohndal-2020]
* [blevins-2016]
* [arad-2005]
* [gouskova-bobaljik-2020]
* [corbett-2007]
* [stump-2016]
* [thornton-2011]
-/

@[expose] public section

namespace Morphology

open Function Relator

variable {R Ctx F G M K : Type*}

/-- A realization assigns to each index and context the finite set of forms realizing the index
there, as Vocabulary Insertion, a paradigm function or spellout computes it. -/
@[ext] structure Realization (R Ctx F : Type*) where
  /-- `realize r c` is the set of forms realizing the index `r` in the context `c`: empty where `r`
  is unlicensed, and of two or more forms at an overabundant cell. -/
  realize : R → Ctx → Finset F

namespace Realization

variable (S : Realization R Ctx F) {T : Realization R Ctx F} {r r' : R} {c c' : Ctx} {f f' : F}

/-! ### The relation of an index -/

/-- `Rel r` relates each context to the forms that realize `r` in it. -/
def Rel (r : R) (c : Ctx) (f : F) : Prop := f ∈ S.realize r c

@[simp] theorem rel_iff : S.Rel r c f ↔ f ∈ S.realize r c := Iff.rfl

/-- `r` is licensed in `c` when some form realizes it there. -/
def IsLicensed (r : R) (c : Ctx) : Prop := (S.realize r c).Nonempty

/-- A realization is total when every index is licensed in every context, as a paradigm function
is. -/
def IsTotal : Prop := ∀ r, LeftTotal (S.Rel r)

/-- A realization is univalent when no cell has more than one form, as the output of an engine
that selects one exponent is. -/
def IsUnivalent : Prop := ∀ r, RightUnique (S.Rel r)

/-- `r` is defective when some context does not license it, as a verb that lacks a tense is. -/
def IsDefective (r : R) : Prop := ¬ LeftTotal (S.Rel r)

/-- `r` is overabundant when one of its cells offers two forms, as *dived* and *dove* share a cell
([thornton-2011]'s cell-mates). -/
def IsOverabundant (r : R) : Prop := ¬ RightUnique (S.Rel r)

/-- `r` is syncretic when two of its contexts share a form, as the nominative and the accusative
of a Latin neuter do. Of the transpose this says that two indices share a form in one context. -/
def IsSyncretic (r : R) : Prop := ¬ LeftUnique (S.Rel r)

variable {S}

theorem leftTotal_rel_iff : LeftTotal (S.Rel r) ↔ ∀ c, S.IsLicensed r c := Iff.rfl

theorem isTotal_iff : S.IsTotal ↔ ∀ r c, S.IsLicensed r c := Iff.rfl

theorem rightUnique_rel_iff : RightUnique (S.Rel r) ↔ ∀ c, (S.realize r c).card ≤ 1 :=
  ⟨fun h _ ↦ Finset.card_le_one.2 fun _ hf _ hf' ↦ h hf hf',
    fun h _ _ _ hf hf' ↦ Finset.card_le_one.1 (h _) _ hf _ hf'⟩

theorem isUnivalent_iff_card : S.IsUnivalent ↔ ∀ r c, (S.realize r c).card ≤ 1 :=
  forall_congr' fun _ ↦ rightUnique_rel_iff

theorem leftUnique_rel_iff : LeftUnique (S.Rel r) ↔ Pairwise (Disjoint on S.realize r) :=
  ⟨fun h _ _ hne ↦ Finset.disjoint_left.2 fun _ hf hf' ↦ hne (h hf hf'),
    fun h _ _ _ hf hf' ↦ by_contra fun hne ↦ Finset.disjoint_left.1 (h hne) hf hf'⟩

@[simp, push] theorem not_isDefective_iff : ¬ S.IsDefective r ↔ LeftTotal (S.Rel r) := not_not

@[simp, push] theorem not_isOverabundant_iff : ¬ S.IsOverabundant r ↔ RightUnique (S.Rel r) :=
  not_not

@[simp, push] theorem not_isSyncretic_iff : ¬ S.IsSyncretic r ↔ LeftUnique (S.Rel r) := not_not

theorem isDefective_iff : S.IsDefective r ↔ ∃ c, S.realize r c = ∅ := by
  simp [IsDefective, LeftTotal, Finset.eq_empty_iff_forall_notMem]

theorem isOverabundant_iff : S.IsOverabundant r ↔ ∃ c, (S.realize r c).Nontrivial := by
  simp [IsOverabundant, rightUnique_rel_iff, ← Finset.one_lt_card_iff_nontrivial]

theorem isSyncretic_iff :
    S.IsSyncretic r ↔ ∃ c c', c ≠ c' ∧ ∃ f ∈ S.realize r c, f ∈ S.realize r c' := by
  simp only [IsSyncretic, LeftUnique, rel_iff]; push Not
  exact ⟨fun ⟨c, c', f, hf, hf', hne⟩ ↦ ⟨c, c', hne, f, hf, hf'⟩,
    fun ⟨c, c', hne, f, hf, hf'⟩ ↦ ⟨c, c', f, hf, hf', hne⟩⟩

@[simp, push] theorem not_isTotal_iff : ¬ S.IsTotal ↔ ∃ r, S.IsDefective r := by
  simp [IsTotal, IsDefective]

theorem isUnivalent_iff : S.IsUnivalent ↔ ∀ r, ¬ S.IsOverabundant r := by
  simp [IsUnivalent]

theorem isSyncretic_of_not_disjoint (hne : c ≠ c')
    (h : ¬ Disjoint (S.realize r c) (S.realize r c')) : S.IsSyncretic r :=
  fun hu ↦ h (leftUnique_rel_iff.1 hu hne)

theorem isSyncretic_of_mem (hne : c ≠ c') (hf : f ∈ S.realize r c) (hf' : f ∈ S.realize r c') :
    S.IsSyncretic r :=
  isSyncretic_iff.2 ⟨c, c', hne, f, hf, hf'⟩

/-- Two distinct contexts that realize a licensed index by the same forms make it syncretic. -/
theorem isSyncretic_of_realize_eq (hne : c ≠ c') (hc : S.IsLicensed r c)
    (h : S.realize r c = S.realize r c') : S.IsSyncretic r :=
  let ⟨_, hf⟩ := hc
  isSyncretic_of_mem hne hf (h ▸ hf)

/-- Where no cell has two forms, the syncretic contexts of an index are those the kernel of its
realization identifies. -/
theorem IsUnivalent.isSyncretic_iff (h : S.IsUnivalent) : S.IsSyncretic r ↔
    ∃ c c', c ≠ c' ∧ S.IsLicensed r c ∧ S.realize r c = S.realize r c' := by
  refine ⟨fun hs ↦ ?_, fun ⟨c, c', hne, hc, he⟩ ↦ isSyncretic_of_realize_eq hne hc he⟩
  obtain ⟨c, c', hne, f, hf, hf'⟩ := Realization.isSyncretic_iff.1 hs
  have key {c} (hf : f ∈ S.realize r c) : S.realize r c = {f} :=
    Finset.eq_singleton_iff_unique_mem.2 ⟨hf, fun _ hg ↦ h r hg hf⟩
  exact ⟨c, c', hne, ⟨f, hf⟩, (key hf).trans (key hf').symm⟩

/-- In a total realization with no cell of two forms, an index is syncretic exactly when its
realization is not injective on contexts. -/
theorem IsUnivalent.isSyncretic_iff_not_injective (h : S.IsUnivalent) (ht : S.IsTotal) :
    S.IsSyncretic r ↔ ¬ Injective (S.realize r) := by
  simp [h.isSyncretic_iff, leftTotal_rel_iff.1 (ht r) _, Function.not_injective_iff, and_comm]

/-! ### Exponents, invariance and suppletion -/

variable (S)

/-- `exponents r` is the set of forms that realize `r` in some context, its allomorphs. -/
def exponents (r : R) : Set F := {f | ∃ c, f ∈ S.realize r c}

@[simp] theorem mem_exponents : f ∈ S.exponents r ↔ ∃ c, f ∈ S.realize r c := Iff.rfl

theorem exponents_eq_iUnion (r : R) : S.exponents r = ⋃ c, (S.realize r c : Set F) := by
  ext; simp

/-- `r` is invariant when it has one form wherever it is licensed, as the classical morpheme
does. -/
def IsInvariant (r : R) : Prop := (S.exponents r).Subsingleton

/-- `r` is suppletive when it has two distinct forms, in contexts that need not differ, as √GO has
*go* and *went*, the case behind [harley-2014]'s argument that indices, not forms, individuate
roots. When the forms are competing Vocabulary Items this is suppletive allomorphy, of a root or of
an affix alike ([gouskova-bobaljik-2020]); when they are stems it is variance in [corbett-2007]'s
lexical material, which is suppletion in [stump-2016]'s sense where no inflection class determines
it (`IsClassDetermined`). -/
def IsSuppletive (r : R) : Prop := (S.exponents r).Nontrivial

/-- `r` is properly suppletive when two contexts that license it realize it by different sets of
forms, as √GO is realized by *go* and by *went*. An unlicensed cell never witnesses it. -/
def IsProperlySuppletive (r : R) : Prop :=
  ∃ c c', S.IsLicensed r c ∧ S.IsLicensed r c' ∧ S.realize r c ≠ S.realize r c'

/-- The forms of `r` are class-determined by the patterns `A`, the paradigms of stems that the
inflection classes of a language generate, when they are drawn from one pattern, so that they
alternate as kindred stems; an alternation between stems no pattern determines is suppletive
([stump-2016]). -/
def IsClassDetermined (A : Set (Ctx → F)) (r : R) : Prop :=
  ∃ p ∈ A, ∀ c, ∀ f ∈ S.realize r c, f = p c

/-- The distinct indices `r` and `r'` are homophonous when they have the same forms in every
context, as *bank₁* and *bank₂* do. -/
def IsHomophonous (r r' : R) : Prop := r ≠ r' ∧ S.realize r = S.realize r'

variable {S}

theorem isInvariant_iff : S.IsInvariant r ↔
    ∀ c c', ∀ f ∈ S.realize r c, ∀ f' ∈ S.realize r c', f = f' :=
  ⟨fun h _ _ _ hf _ hf' ↦ h ⟨_, hf⟩ ⟨_, hf'⟩, fun h _ ⟨_, hf⟩ _ ⟨_, hf'⟩ ↦ h _ _ _ hf _ hf'⟩

theorem isSuppletive_iff : S.IsSuppletive r ↔
    ∃ c c', ∃ f ∈ S.realize r c, ∃ f' ∈ S.realize r c', f ≠ f' :=
  ⟨fun ⟨f, ⟨c, hf⟩, f', ⟨c', hf'⟩, hne⟩ ↦ ⟨c, c', f, hf, f', hf', hne⟩,
    fun ⟨c, c', f, hf, f', hf', hne⟩ ↦ ⟨f, ⟨c, hf⟩, f', ⟨c', hf'⟩, hne⟩⟩

theorem isSuppletive_of_mem (hf : f ∈ S.realize r c) (hf' : f' ∈ S.realize r c')
    (hne : f ≠ f') : S.IsSuppletive r :=
  ⟨f, ⟨c, hf⟩, f', ⟨c', hf'⟩, hne⟩

@[simp, push] theorem not_isInvariant_iff : ¬ S.IsInvariant r ↔ S.IsSuppletive r :=
  Set.not_subsingleton_iff

@[simp, push] theorem not_isSuppletive_iff : ¬ S.IsSuppletive r ↔ S.IsInvariant r :=
  Set.not_nontrivial_iff

theorem IsSuppletive.not_isInvariant (h : S.IsSuppletive r) : ¬ S.IsInvariant r :=
  not_isInvariant_iff.2 h

theorem IsInvariant.not_isSuppletive (h : S.IsInvariant r) : ¬ S.IsSuppletive r :=
  not_isSuppletive_iff.2 h

theorem IsOverabundant.isSuppletive (h : S.IsOverabundant r) : S.IsSuppletive r :=
  let ⟨c, hc⟩ := isOverabundant_iff.1 h
  Set.Nontrivial.mono hc fun _ hf ↦ ⟨c, hf⟩

/-- An invariant index has the same forms in any two contexts that license it. -/
theorem IsInvariant.realize_eq (h : S.IsInvariant r) (hc : S.IsLicensed r c)
    (hc' : S.IsLicensed r c') : S.realize r c = S.realize r c' :=
  let ⟨_, hf⟩ := hc
  let ⟨_, hf'⟩ := hc'
  Finset.ext fun _ ↦ ⟨fun hg ↦ h ⟨c, hg⟩ ⟨c', hf'⟩ ▸ hf', fun hg ↦ h ⟨c', hg⟩ ⟨c, hf⟩ ▸ hf⟩

theorem IsProperlySuppletive.isSuppletive (h : S.IsProperlySuppletive r) : S.IsSuppletive r :=
  let ⟨_, _, hc, hc', hne⟩ := h
  not_isInvariant_iff.1 fun hi ↦ hne (hi.realize_eq hc hc')

/-- Variance of form at an index is overabundance in one cell or suppletion across two. -/
theorem isSuppletive_iff_isOverabundant_or_isProperlySuppletive :
    S.IsSuppletive r ↔ S.IsOverabundant r ∨ S.IsProperlySuppletive r := by
  refine ⟨fun ⟨f, ⟨c, hf⟩, f', ⟨c', hf'⟩, hne⟩ ↦ ?_,
    fun h ↦ h.elim IsOverabundant.isSuppletive IsProperlySuppletive.isSuppletive⟩
  by_cases h : S.realize r c = S.realize r c'
  · exact .inl (isOverabundant_iff.2 ⟨c, f, hf, f', h ▸ hf', hne⟩)
  · exact .inr ⟨c, c', ⟨f, hf⟩, ⟨f', hf'⟩, h⟩

/-- Where no cell has two forms, suppletion is suppletion across cells. -/
theorem IsUnivalent.isSuppletive_iff (h : S.IsUnivalent) :
    S.IsSuppletive r ↔ S.IsProperlySuppletive r := by
  rw [isSuppletive_iff_isOverabundant_or_isProperlySuppletive, or_iff_right (isUnivalent_iff.1 h r)]

/-- Where every pattern is constant, the class-determined forms are the invariant ones, so
suppletion is any variance. -/
theorem isClassDetermined_range_const_iff [Nonempty F] :
    S.IsClassDetermined (Set.range (const Ctx)) r ↔ S.IsInvariant r := by
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨_, ⟨b, rfl⟩, h⟩
    exact Set.subsingleton_of_forall_eq b fun f ⟨c, hf⟩ ↦ h c f hf
  · obtain hr | ⟨f₀, hf₀⟩ := (S.exponents r).eq_empty_or_nonempty
    · exact ⟨_, ⟨Classical.arbitrary F, rfl⟩, fun c f hf ↦ (hr ▸ ⟨c, hf⟩ : f ∈ (∅ : Set F)).elim⟩
    · exact ⟨_, ⟨f₀, rfl⟩, fun c f hf ↦ h ⟨c, hf⟩ hf₀⟩

theorem IsHomophonous.symm (h : S.IsHomophonous r r') : S.IsHomophonous r' r :=
  ⟨h.1.symm, h.2.symm⟩

/-- Some two indices are homophonous exactly when realization is not injective on indices. -/
theorem exists_isHomophonous_iff : (∃ r r', S.IsHomophonous r r') ↔ ¬ Injective S.realize := by
  simp [IsHomophonous, Function.not_injective_iff, and_comm]

/-! ### The cells of a form

Realization runs from an index and a context to forms. Read backwards it analyses a form: the
contexts in which a given form realizes a given index. -/

variable (S)

/-- `cells r f` is the set of contexts in which `f` realizes `r`: the cells of the paradigm of `r`
that the form `f` fills, one for an unambiguous form and several for a syncretic one. -/
def cells (r : R) (f : F) : Set Ctx := {c | f ∈ S.realize r c}

variable {S}

@[simp] theorem mem_cells : c ∈ S.cells r f ↔ f ∈ S.realize r c := Iff.rfl

/-- A form is an exponent of an index exactly when it fills one of its cells. -/
theorem mem_exponents_iff_cells_nonempty : f ∈ S.exponents r ↔ (S.cells r f).Nonempty := Iff.rfl

theorem cells_eq_empty_iff : S.cells r f = ∅ ↔ f ∉ S.exponents r := by
  rw [mem_exponents_iff_cells_nonempty, Set.not_nonempty_iff_eq_empty]

/-- No two contexts of an index share a form exactly when each form fills at most one cell. -/
theorem leftUnique_rel_iff_cells : LeftUnique (S.Rel r) ↔ ∀ f, (S.cells r f).Subsingleton :=
  ⟨fun h _ _ hc _ hc' ↦ h hc hc', fun h _ _ _ hc hc' ↦ h _ hc hc'⟩

/-- An index is syncretic exactly when some form fills two of its cells. -/
theorem isSyncretic_iff_cells : S.IsSyncretic r ↔ ∃ f, (S.cells r f).Nontrivial := by
  simp [IsSyncretic, leftUnique_rel_iff_cells, Set.not_subsingleton_iff]

/-- A form of an index that is not syncretic determines its cell. -/
theorem eq_of_mem_cells (h : ¬ S.IsSyncretic r) (hc : c ∈ S.cells r f) (hc' : c' ∈ S.cells r f) :
    c = c' :=
  not_isSyncretic_iff.1 h hc hc'

/-! ### Decidability

Each instance decides a characterization that quantifies over contexts and their finite sets of
forms, so none needs a `Fintype F`. -/

section Decidable

variable (S) [Fintype Ctx] [DecidableEq F]

instance (r : R) (c : Ctx) : Decidable (S.IsLicensed r c) :=
  inferInstanceAs (Decidable (S.realize r c).Nonempty)

instance (r : R) : Decidable (LeftTotal (S.Rel r)) :=
  inferInstanceAs (Decidable (∀ c, S.IsLicensed r c))

instance (r : R) : Decidable (RightUnique (S.Rel r)) := decidable_of_iff _ rightUnique_rel_iff.symm

instance [DecidableEq Ctx] (r : R) : Decidable (LeftUnique (S.Rel r)) :=
  decidable_of_iff (∀ c c', c ≠ c' → Disjoint (S.realize r c) (S.realize r c'))
    leftUnique_rel_iff.symm

instance (r : R) : Decidable (S.IsDefective r) := inferInstanceAs (Decidable (¬ _))

instance (r : R) : Decidable (S.IsOverabundant r) := inferInstanceAs (Decidable (¬ _))

instance [DecidableEq Ctx] (r : R) : Decidable (S.IsSyncretic r) :=
  inferInstanceAs (Decidable (¬ _))

instance (r : R) : Decidable (S.IsInvariant r) := decidable_of_iff _ isInvariant_iff.symm

instance (r : R) : Decidable (S.IsSuppletive r) := decidable_of_iff _ isSuppletive_iff.symm

instance (r : R) : Decidable (S.IsProperlySuppletive r) :=
  inferInstanceAs (Decidable (∃ _ _, _ ∧ _ ∧ _))

instance [DecidableEq R] (r r' : R) : Decidable (S.IsHomophonous r r') :=
  inferInstanceAs (Decidable (_ ∧ _))

omit [Fintype Ctx] in
instance (r : R) (f : F) : DecidablePred (· ∈ S.cells r f) := fun c ↦
  inferInstanceAs (Decidable (f ∈ S.realize r c))

instance (r : R) (f : F) : Decidable (f ∈ S.exponents r) :=
  inferInstanceAs (Decidable (∃ c, f ∈ S.realize r c))

variable [Fintype R]

instance : Decidable S.IsTotal := inferInstanceAs (Decidable (∀ r, LeftTotal (S.Rel r)))

instance : Decidable S.IsUnivalent := inferInstanceAs (Decidable (∀ r, RightUnique (S.Rel r)))

end Decidable

/-! ### The order and its monotone properties -/

/-- Realizations are ordered by inclusion of the forms of each cell. -/
instance : PartialOrder (Realization R Ctx F) :=
  PartialOrder.lift realize fun _ _ ↦ Realization.ext

theorem le_def : S ≤ T ↔ ∀ r c, S.realize r c ⊆ T.realize r c := Iff.rfl

section Mono

variable (h : S ≤ T)
include h

theorem IsLicensed.mono (hc : S.IsLicensed r c) : T.IsLicensed r c :=
  Finset.Nonempty.mono (h r c) hc

theorem exponents_mono (r : R) : S.exponents r ⊆ T.exponents r := fun _ ⟨c, hf⟩ ↦ ⟨c, h r c hf⟩

theorem cells_mono (r : R) (f : F) : S.cells r f ⊆ T.cells r f := fun _ hc ↦ h r _ hc

theorem IsSuppletive.mono (hs : S.IsSuppletive r) : T.IsSuppletive r :=
  Set.Nontrivial.mono hs (exponents_mono h r)

theorem IsInvariant.anti (ht : T.IsInvariant r) : S.IsInvariant r :=
  Set.Subsingleton.anti ht (exponents_mono h r)

theorem rightUnique_rel_anti (ht : RightUnique (T.Rel r)) : RightUnique (S.Rel r) :=
  fun _ _ _ hf hf' ↦ ht (h r _ hf) (h r _ hf')

theorem leftUnique_rel_anti (ht : LeftUnique (T.Rel r)) : LeftUnique (S.Rel r) :=
  fun _ _ _ hf hf' ↦ ht (h r _ hf) (h r _ hf')

theorem IsOverabundant.mono (hs : S.IsOverabundant r) : T.IsOverabundant r :=
  mt (rightUnique_rel_anti h) hs

theorem IsSyncretic.mono (hs : S.IsSyncretic r) : T.IsSyncretic r := mt (leftUnique_rel_anti h) hs

theorem IsUnivalent.anti (ht : T.IsUnivalent) : S.IsUnivalent :=
  fun r ↦ rightUnique_rel_anti h (ht r)

theorem IsTotal.mono (hs : S.IsTotal) : T.IsTotal := fun r c ↦ IsLicensed.mono h (hs r c)

end Mono

/-! ### Realizations that select one form -/

/-- The realization of a map that selects at most one form for each index and context, as an
engine that picks one exponent does. -/
def ofOption (g : R → Ctx → Option F) : Realization R Ctx F := ⟨fun r c ↦ (g r c).toFinset⟩

section OfOption

variable {g : R → Ctx → Option F}

@[simp] theorem ofOption_realize (g : R → Ctx → Option F) (r : R) (c : Ctx) :
    (ofOption g).realize r c = (g r c).toFinset := rfl

theorem mem_ofOption_realize : f ∈ (ofOption g).realize r c ↔ g r c = some f := by simp

theorem mem_cells_ofOption : c ∈ (ofOption g).cells r f ↔ g r c = some f := mem_ofOption_realize

theorem isLicensed_ofOption_iff : (ofOption g).IsLicensed r c ↔ (g r c).isSome := by
  simp [IsLicensed, Finset.Nonempty, Option.isSome_iff_exists]

theorem isUnivalent_ofOption (g : R → Ctx → Option F) : (ofOption g).IsUnivalent :=
  fun _ _ _ _ hf hf' ↦ Option.some.inj ((mem_ofOption_realize.1 hf).symm.trans
    (mem_ofOption_realize.1 hf'))

/-- An index is suppletive exactly when two of its contexts select distinct forms. -/
theorem isSuppletive_ofOption_iff : (ofOption g).IsSuppletive r ↔
    ∃ c c' f f', g r c = some f ∧ g r c' = some f' ∧ f ≠ f' := by
  simp [isSuppletive_iff]

end OfOption

end Realization

end Morphology
