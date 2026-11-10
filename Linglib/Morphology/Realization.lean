/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Finset.Option
public import Mathlib.Data.Set.Image
public import Mathlib.Order.Setoid.Basic

/-!
# Realizations: indices realized in context

A realization assigns to an index `r` and a context `c` the finite set `realize r c` of forms that
realize `r` in `c`: the exponent of a root at Vocabulary Insertion, the stem of a lexeme at a cell
of its paradigm. An empty set says that `r` is not licensed in `c`, and a set of two forms is an
overabundant cell. The forms of an index across all its contexts are its `exponents`; an index is
invariant when they are at most one and suppletive when they are at least two, which happens
[within one cell or across two](##isSuppletive_iff_isOverabundant_or_isProperlySuppletive).
An interpreted realization pairs the forms with a second realization, of readings.

A homomorphism merges indices and translates contexts so that the forms of each cell are
preserved, so [the indices it merges have the same forms in every
context](##Realization.Hom.ker_onIndex_le), and the quotient `reduce` by that equivalence merges
[exactly those](##Realization.ker_reduceHom_onIndex), as an inflection class collects the lexemes
that inflect alike. A lax homomorphism includes forms
where a homomorphism preserves them; it still carries suppletion forward and invariance back.
Homomorphisms of interpreted realizations treat readings the same way.

## Implementation notes

* The index is opaque, and the frameworks that separate an item from its form choose it
  differently: a root of Distributed Morphology, a phonological index in Borer's sense, a lexeme of
  Paradigm Function Morphology, Spencer's lexemic index. The interface does not say whether indices
  are listed or constructed.
* Invariance and suppletion are `Set.Subsingleton` and `Set.Nontrivial` of `exponents`, so that
  mathlib's lemmas on images and inclusions give their behaviour under `map` and under
  homomorphisms.
* A homomorphism cannot consult the index when it translates contexts, so categorial information
  has to sit in the context.
* Profiles are extensional and underdetermine individuation. Criteria such as the locality of
  first categorization are further structure on admissible mergers, which studies supply.

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

open Function

variable {R Ctx F G M K : Type*}

/-- A realization assigns to each index and context the finite set of forms realizing the index
there, as Vocabulary Insertion, a paradigm function or spellout computes it. -/
@[ext] structure Realization (R Ctx F : Type*) where
  /-- `realize r c` is the set of forms realizing the index `r` in the context `c`: empty where `r`
  is unlicensed, and of two or more forms at an overabundant cell. -/
  realize : R → Ctx → Finset F

namespace Realization

variable (S : Realization R Ctx F) {r r' : R} {c c' : Ctx} {f f' : F}

/-! ### Licensing -/

/-- `r` is licensed in `c` when some form realizes it there. -/
def IsLicensed (r : R) (c : Ctx) : Prop := (S.realize r c).Nonempty

/-- A realization is total when every index is licensed in every context, as a paradigm function
is. -/
def IsTotal : Prop := ∀ r c, S.IsLicensed r c

/-- A realization is univalent when no cell has more than one form, as the output of an engine
that selects one exponent is. -/
def IsUnivalent : Prop := ∀ r c, (S.realize r c).card ≤ 1

/-- `r` is cross-categorial when it is licensed in two contexts whose categories `k` differ, as a
category-free root is ([marantz-1997], [arad-2005]). -/
def IsCrossCategorial (k : Ctx → K) (r : R) : Prop :=
  ∃ c c', k c ≠ k c' ∧ S.IsLicensed r c ∧ S.IsLicensed r c'

/-! ### Exponents, invariance and suppletion -/

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

/-- `r` is overabundant when one of its cells offers two forms, as *dived* and *dove* share a cell
([thornton-2011]'s cell-mates). -/
def IsOverabundant (r : R) : Prop := ∃ c, (S.realize r c).Nontrivial

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

theorem isSuppletive_of_mem (hf : f ∈ S.realize r c) (hf' : f' ∈ S.realize r c') (hne : f ≠ f') :
    S.IsSuppletive r :=
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
  let ⟨c, hc⟩ := h
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
  · exact .inl ⟨c, f, hf, f', h ▸ hf', hne⟩
  · exact .inr ⟨c, c', ⟨f, hf⟩, ⟨f', hf'⟩, h⟩

theorem isUnivalent_iff : S.IsUnivalent ↔ ∀ r, ¬ S.IsOverabundant r := by
  simp [IsUnivalent, IsOverabundant, ← Finset.one_lt_card_iff_nontrivial]

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

theorem IsHomophonous.symm (h : S.IsHomophonous r r') : S.IsHomophonous r' r := ⟨h.1.symm, h.2.symm⟩

/-- Some two indices are homophonous exactly when realization is not injective on indices. -/
theorem exists_isHomophonous_iff : (∃ r r', S.IsHomophonous r r') ↔ ¬ Injective S.realize := by
  simp [IsHomophonous, Function.not_injective_iff, and_comm]

/-! ### Decidability

Invariance and suppletion are decided through `isInvariant_iff` and `isSuppletive_iff`, which
quantify over contexts and their finite sets of forms, so they need no `Fintype F`. -/

section Decidable

variable (S) [Fintype Ctx] [DecidableEq F]

instance (r : R) (c : Ctx) : Decidable (S.IsLicensed r c) :=
  inferInstanceAs (Decidable (S.realize r c).Nonempty)

instance (r : R) : Decidable (S.IsInvariant r) := decidable_of_iff _ isInvariant_iff.symm

instance (r : R) : Decidable (S.IsSuppletive r) := decidable_of_iff _ isSuppletive_iff.symm

instance (r : R) : Decidable (S.IsOverabundant r) :=
  inferInstanceAs (Decidable (∃ c, (S.realize r c).Nontrivial))

instance (r : R) : Decidable (S.IsProperlySuppletive r) :=
  inferInstanceAs (Decidable (∃ _ _, _ ∧ _ ∧ _))

instance [DecidableEq K] (k : Ctx → K) (r : R) : Decidable (S.IsCrossCategorial k r) :=
  inferInstanceAs (Decidable (∃ _ _, _ ∧ _ ∧ _))

instance [DecidableEq R] (r r' : R) : Decidable (S.IsHomophonous r r') :=
  inferInstanceAs (Decidable (_ ∧ _))

variable [Fintype R]

instance : Decidable S.IsTotal := inferInstanceAs (Decidable (∀ r c, S.IsLicensed r c))

instance : Decidable S.IsUnivalent := inferInstanceAs (Decidable (∀ r c, (S.realize r c).card ≤ 1))

end Decidable

/-! ### Transpose, image and composition -/

variable (S)

/-- The transpose of `S` realizes each context at each index as `S` realizes the index in the
context, so that comparing one context across indices is comparing one index of the transpose
across contexts. -/
def transpose (S : Realization R Ctx F) : Realization Ctx R F := ⟨swap S.realize⟩

@[simp] theorem transpose_realize (c : Ctx) (r : R) : S.transpose.realize c r = S.realize r c :=
  rfl

@[simp] theorem transpose_transpose : S.transpose.transpose = S := rfl

/-- The image of `S` under a map of forms. -/
def map [DecidableEq G] (g : F → G) (S : Realization R Ctx F) : Realization R Ctx G :=
  ⟨fun r c ↦ (S.realize r c).image g⟩

section Map

variable [DecidableEq G] (g : F → G)

@[simp] theorem map_realize (r : R) (c : Ctx) : (S.map g).realize r c = (S.realize r c).image g :=
  rfl

@[simp] theorem exponents_map (r : R) : (S.map g).exponents r = g '' S.exponents r := by
  ext; simp only [mem_exponents, map_realize, Finset.mem_image, Set.mem_image]; tauto

variable {S}

theorem IsInvariant.map (h : S.IsInvariant r) : (S.map g).IsInvariant r := by
  simpa [IsInvariant] using Set.Subsingleton.image h g

variable {g}

theorem IsSuppletive.of_map (h : (S.map g).IsSuppletive r) : S.IsSuppletive r :=
  Set.nontrivial_of_image g _ (by simpa [IsSuppletive] using h)

@[simp] theorem isLicensed_map_iff : (S.map g).IsLicensed r c ↔ S.IsLicensed r c :=
  Finset.image_nonempty

@[simp] theorem isTotal_map_iff : (S.map g).IsTotal ↔ S.IsTotal := by simp [IsTotal]

end Map

/-! ### Realizations that select one form -/

/-- The realization of a map that selects at most one form for each index and context, as an
engine that picks one exponent does. -/
def ofOption (g : R → Ctx → Option F) : Realization R Ctx F := ⟨fun r c ↦ (g r c).toFinset⟩

section OfOption

variable {g : R → Ctx → Option F}

@[simp] theorem ofOption_realize (g : R → Ctx → Option F) (r : R) (c : Ctx) :
    (ofOption g).realize r c = (g r c).toFinset := rfl

theorem mem_ofOption_realize : f ∈ (ofOption g).realize r c ↔ g r c = some f := by simp

theorem isLicensed_ofOption_iff : (ofOption g).IsLicensed r c ↔ (g r c).isSome := by
  simp [IsLicensed, Finset.Nonempty, Option.isSome_iff_exists]

theorem isUnivalent_ofOption (g : R → Ctx → Option F) : (ofOption g).IsUnivalent := fun r c ↦ by
  rw [ofOption_realize, Option.card_toFinset]; cases g r c <;> simp

/-- An index is suppletive exactly when two of its contexts select distinct forms. -/
theorem isSuppletive_ofOption_iff : (ofOption g).IsSuppletive r ↔
    ∃ c c' f f', g r c = some f ∧ g r c' = some f' ∧ f ≠ f' := by
  simp [isSuppletive_iff]

end OfOption

/-- The composite `S.comp T` realizes an index through the intermediate forms of `S`, each
realized in the same context by `T`: the Kleisli composition of `Finset`-valued maps. A
late-insertion grammar factors its realization this way, and so does a choice of stem followed by
its inflection. -/
def comp [DecidableEq G] (S : Realization R Ctx F) (T : Realization F Ctx G) :
    Realization R Ctx G :=
  ⟨fun r c ↦ (S.realize r c).biUnion fun f ↦ T.realize f c⟩

section Comp

variable [DecidableEq G] {S} {T : Realization F Ctx G} {g : G}

@[simp] theorem mem_comp_realize :
    g ∈ (S.comp T).realize r c ↔ ∃ f ∈ S.realize r c, g ∈ T.realize f c :=
  Finset.mem_biUnion

theorem IsTotal.comp (hS : S.IsTotal) (hT : T.IsTotal) : (S.comp T).IsTotal := fun r c ↦
  let ⟨f, hf⟩ := hS r c
  let ⟨g, hg⟩ := hT f c
  ⟨g, mem_comp_realize.2 ⟨f, hf, hg⟩⟩

theorem comp_assoc {H : Type*} [DecidableEq H] (S : Realization R Ctx F) (T : Realization F Ctx G)
    (U : Realization G Ctx H) : (S.comp T).comp U = S.comp (T.comp U) := by
  ext r c h; simp only [mem_comp_realize]; tauto

end Comp

/-! ### Homomorphisms -/

section Hom

variable {R₁ C₁ R₂ C₂ R₃ C₃ : Type*} {S₁ : Realization R₁ C₁ F} {S₂ : Realization R₂ C₂ F}
  {S₃ : Realization R₃ C₃ F}

/-- A lax homomorphism of realizations merges indices and translates contexts so that the forms
of each cell of the source are among those of its image, as the forms of a lexeme are among
those of its root ([arad-2005]). -/
@[ext] structure LaxHom (S : Realization R₁ C₁ F) (T : Realization R₂ C₂ F) where
  /-- The translation of indices, which merges those it identifies. -/
  onIndex : R₁ → R₂
  /-- The translation of contexts. -/
  onCtx : C₁ → C₂
  /-- Forms are included. -/
  realize_subset (r : R₁) (c : C₁) : S.realize r c ⊆ T.realize (onIndex r) (onCtx c)

/-- A homomorphism of realizations merges indices and translates contexts so that the forms of
each cell are preserved. The translation of contexts does not consult the index, so the target
context cannot encode the source index. -/
@[ext] structure Hom (S : Realization R₁ C₁ F) (T : Realization R₂ C₂ F) where
  /-- The translation of indices, which merges those it identifies. -/
  onIndex : R₁ → R₂
  /-- The translation of contexts. -/
  onCtx : C₁ → C₂
  /-- Forms are preserved. -/
  realize_eq (r : R₁) (c : C₁) : T.realize (onIndex r) (onCtx c) = S.realize r c

attribute [simp] Hom.realize_eq

namespace LaxHom

/-- The identity lax homomorphism. -/
@[simps] protected def id (S : Realization R Ctx F) : LaxHom S S := ⟨id, id, fun _ _ ↦ subset_rfl⟩

/-- The composite of two lax homomorphisms. -/
@[simps] def comp (ψ : LaxHom S₂ S₃) (φ : LaxHom S₁ S₂) : LaxHom S₁ S₃ :=
  ⟨ψ.onIndex ∘ φ.onIndex, ψ.onCtx ∘ φ.onCtx,
    fun r c ↦ (φ.realize_subset r c).trans (ψ.realize_subset _ _)⟩

@[simp] theorem id_comp (φ : LaxHom S₁ S₂) : (LaxHom.id S₂).comp φ = φ := rfl

@[simp] theorem comp_id (φ : LaxHom S₁ S₂) : φ.comp (LaxHom.id S₁) = φ := rfl

variable (φ : LaxHom S₁ S₂) {r : R₁} {c : C₁}

theorem isLicensed (h : S₁.IsLicensed r c) : S₂.IsLicensed (φ.onIndex r) (φ.onCtx c) :=
  h.mono (φ.realize_subset r c)

/-- Merging indices can only enlarge their sets of allomorphs. -/
theorem exponents_subset (r : R₁) : S₁.exponents r ⊆ S₂.exponents (φ.onIndex r) :=
  fun _ ⟨c, hf⟩ ↦ ⟨φ.onCtx c, φ.realize_subset r c hf⟩

theorem isSuppletive (h : S₁.IsSuppletive r) : S₂.IsSuppletive (φ.onIndex r) :=
  h.mono (φ.exponents_subset r)

theorem isInvariant (h : S₂.IsInvariant (φ.onIndex r)) : S₁.IsInvariant r :=
  h.anti (φ.exponents_subset r)

theorem isOverabundant (h : S₁.IsOverabundant r) : S₂.IsOverabundant (φ.onIndex r) :=
  let ⟨c, hc⟩ := h
  ⟨φ.onCtx c, Set.Nontrivial.mono hc (Finset.coe_subset.2 (φ.realize_subset r c))⟩

end LaxHom

namespace Hom

/-- A homomorphism is lax. -/
@[simps] def toLaxHom (φ : Hom S₁ S₂) : LaxHom S₁ S₂ :=
  ⟨φ.onIndex, φ.onCtx, fun r c ↦ (φ.realize_eq r c).ge⟩

/-- The identity homomorphism. -/
@[simps] protected def id (S : Realization R Ctx F) : Hom S S := ⟨id, id, fun _ _ ↦ rfl⟩

/-- The composite of two homomorphisms, so that coarsenings chain. -/
@[simps] def comp (ψ : Hom S₂ S₃) (φ : Hom S₁ S₂) : Hom S₁ S₃ :=
  ⟨ψ.onIndex ∘ φ.onIndex, ψ.onCtx ∘ φ.onCtx, fun r c ↦ by simp⟩

@[simp] theorem id_comp (φ : Hom S₁ S₂) : (Hom.id S₂).comp φ = φ := rfl

@[simp] theorem comp_id (φ : Hom S₁ S₂) : φ.comp (Hom.id S₁) = φ := rfl

theorem comp_assoc {R₄ C₄ : Type*} {S₄ : Realization R₄ C₄ F} (χ : Hom S₃ S₄) (ψ : Hom S₂ S₃)
    (φ : Hom S₁ S₂) : (χ.comp ψ).comp φ = χ.comp (ψ.comp φ) := rfl

variable (φ : Hom S₁ S₂) {r r' : R₁} {c : C₁}

@[simp] theorem isLicensed_iff : S₂.IsLicensed (φ.onIndex r) (φ.onCtx c) ↔ S₁.IsLicensed r c := by
  simp [IsLicensed]

/-- Indices that a homomorphism merges have the same forms in every context. -/
theorem realize_eq_of_onIndex_eq (h : φ.onIndex r = φ.onIndex r') : S₁.realize r = S₁.realize r' :=
  funext fun c ↦ by rw [← φ.realize_eq, ← φ.realize_eq r', h]

/-- A homomorphism merges only indices with the same forms in every context. -/
theorem ker_onIndex_le : Setoid.ker φ.onIndex ≤ Setoid.ker S₁.realize :=
  fun _ _ ↦ φ.realize_eq_of_onIndex_eq

end Hom

end Hom

/-! ### Reduction -/

/-- The reduction of `S` merges the indices that have the same forms in every context, as the
lexemes that inflect alike make up an inflection class. -/
def reduce : Realization (Quotient (Setoid.ker S.realize)) Ctx F := ⟨Setoid.kerLift S.realize⟩

@[simp] theorem reduce_realize_mk (r : R) : S.reduce.realize ⟦r⟧ = S.realize r := rfl

/-- Distinct indices of the reduction differ in their forms in some context. -/
theorem reduce_realize_injective : Injective S.reduce.realize := Setoid.kerLift_injective _

/-- The homomorphism from `S` to its reduction. -/
@[simps] def reduceHom : Hom S S.reduce := ⟨Quotient.mk'', id, fun _ _ ↦ rfl⟩

/-- Reduction merges exactly the indices with the same forms in every context, which by
`Hom.ker_onIndex_le` is as much as a homomorphism can merge. -/
theorem ker_reduceHom_onIndex : Setoid.ker S.reduceHom.onIndex = Setoid.ker S.realize :=
  Setoid.ker_mk_eq _

end Realization

/-- An interpreted realization pairs the realization of indices by forms with a realization of the
same indices, in the same contexts, by readings: the separation of the Vocabulary from the
Encyclopedia in [marantz-1997]. -/
structure Realization.Interpreted (R Ctx F M : Type*) extends Realization R Ctx F where
  /-- `interp.realize r c` is the set of readings of `r` in `c`. -/
  interp : Realization R Ctx M

namespace Realization.Interpreted

variable (S : Interpreted R Ctx F M) {r r' : R}

/-- `r` is intrinsic when it has one reading wherever it has any, as a lexeme with a listed meaning
does. -/
abbrev IsIntrinsic (r : R) : Prop := S.interp.IsInvariant r

/-- `r` is allosemous when it has two distinct readings, the counterpart in meaning of
suppletion. -/
abbrev IsAllosemous (r : R) : Prop := S.interp.IsSuppletive r

/-- The profile of `r` is its forms and its readings in every context. -/
def profile (r : R) : (Ctx → Finset F) × (Ctx → Finset M) := (S.realize r, S.interp.realize r)

@[simp] theorem profile_fst (r : R) : (S.profile r).1 = S.realize r := rfl

@[simp] theorem profile_snd (r : R) : (S.profile r).2 = S.interp.realize r := rfl

/-! ### Homomorphisms of interpreted realizations -/

section Hom

variable {R₁ C₁ R₂ C₂ R₃ C₃ : Type*} {S₁ : Interpreted R₁ C₁ F M} {S₂ : Interpreted R₂ C₂ F M}
  {S₃ : Interpreted R₃ C₃ F M}

/-- A lax homomorphism of interpreted realizations is a lax homomorphism of the realizations by
forms that also includes readings, as the listed properties of a lexeme are among those of its
root ([arad-2005]). -/
structure LaxHom (S : Interpreted R₁ C₁ F M) (T : Interpreted R₂ C₂ F M) extends
    Realization.LaxHom S.toRealization T.toRealization where
  /-- Readings are included. -/
  interp_subset (r : R₁) (c : C₁) :
    S.interp.realize r c ⊆ T.interp.realize (onIndex r) (onCtx c)

/-- A homomorphism of interpreted realizations is a homomorphism of the realizations by forms
that also preserves readings. -/
structure Hom (S : Interpreted R₁ C₁ F M) (T : Interpreted R₂ C₂ F M) extends
    Realization.Hom S.toRealization T.toRealization where
  /-- Readings are preserved. -/
  interp_eq (r : R₁) (c : C₁) : T.interp.realize (onIndex r) (onCtx c) = S.interp.realize r c

attribute [simp] Hom.interp_eq

namespace LaxHom

/-- The lax homomorphism of the realizations by readings. -/
@[simps] def interpHom (φ : LaxHom S₁ S₂) : Realization.LaxHom S₁.interp S₂.interp :=
  ⟨φ.onIndex, φ.onCtx, φ.interp_subset⟩

/-- The identity lax homomorphism. -/
protected def id (S : Interpreted R Ctx F M) : LaxHom S S :=
  ⟨.id S.toRealization, fun _ _ ↦ subset_rfl⟩

/-- The composite of two lax homomorphisms. -/
def comp (ψ : LaxHom S₂ S₃) (φ : LaxHom S₁ S₂) : LaxHom S₁ S₃ :=
  ⟨ψ.toLaxHom.comp φ.toLaxHom, (ψ.interpHom.comp φ.interpHom).realize_subset⟩

variable (φ : LaxHom S₁ S₂) {r : R₁}

theorem isAllosemous (h : S₁.IsAllosemous r) : S₂.IsAllosemous (φ.onIndex r) :=
  φ.interpHom.isSuppletive h

theorem isIntrinsic (h : S₂.IsIntrinsic (φ.onIndex r)) : S₁.IsIntrinsic r :=
  φ.interpHom.isInvariant h

end LaxHom

namespace Hom

/-- The homomorphism of the realizations by readings. -/
@[simps] def interpHom (φ : Hom S₁ S₂) : Realization.Hom S₁.interp S₂.interp :=
  ⟨φ.onIndex, φ.onCtx, φ.interp_eq⟩

/-- A homomorphism of interpreted realizations is lax. -/
def toLaxHom (φ : Hom S₁ S₂) : LaxHom S₁ S₂ :=
  ⟨φ.toHom.toLaxHom, φ.interpHom.toLaxHom.realize_subset⟩

/-- The identity homomorphism. -/
protected def id (S : Interpreted R Ctx F M) : Hom S S := ⟨.id S.toRealization, fun _ _ ↦ rfl⟩

/-- The composite of two homomorphisms. -/
def comp (ψ : Hom S₂ S₃) (φ : Hom S₁ S₂) : Hom S₁ S₃ :=
  ⟨ψ.toHom.comp φ.toHom, (ψ.interpHom.comp φ.interpHom).realize_eq⟩

variable (φ : Hom S₁ S₂) {r r' : R₁}

/-- Indices that a homomorphism merges have the same forms and readings in every context. -/
theorem profile_eq_of_onIndex_eq (h : φ.onIndex r = φ.onIndex r') : S₁.profile r = S₁.profile r' :=
  Prod.ext (φ.toHom.realize_eq_of_onIndex_eq h) (φ.interpHom.realize_eq_of_onIndex_eq h)

/-- A homomorphism of interpreted realizations merges only indices with the same profile. -/
theorem ker_onIndex_le : Setoid.ker φ.onIndex ≤ Setoid.ker S₁.profile :=
  fun _ _ ↦ φ.profile_eq_of_onIndex_eq

end Hom

end Hom

/-! ### Reduction of an interpreted realization -/

/-- The reduction of `S` takes as its indices the profiles of `S`, merging the indices that have
the same forms and readings in every context. -/
def reduce : Interpreted (Quotient (Setoid.ker S.profile)) Ctx F M where
  realize q := (Setoid.kerLift S.profile q).1
  interp := ⟨fun q ↦ (Setoid.kerLift S.profile q).2⟩

@[simp] theorem reduce_profile : S.reduce.profile = Setoid.kerLift S.profile := rfl

/-- Distinct indices of the reduction have distinct profiles. -/
theorem reduce_profile_injective : Injective S.reduce.profile := Setoid.kerLift_injective _

/-- The homomorphism from `S` to its reduction. -/
def reduceHom : Hom S S.reduce := ⟨⟨Quotient.mk'', id, fun _ _ ↦ rfl⟩, fun _ _ ↦ rfl⟩

/-- Reduction merges exactly the indices with the same profile, which by `Hom.ker_onIndex_le` is as
much as a homomorphism can merge. -/
theorem ker_reduceHom_onIndex : Setoid.ker S.reduceHom.onIndex = Setoid.ker S.profile :=
  Setoid.ker_mk_eq _

end Realization.Interpreted

end Morphology
