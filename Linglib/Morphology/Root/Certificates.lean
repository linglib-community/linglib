/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Morphology.Realization
public import Linglib.Morphology.Root.Basic
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Finset.Dedup

/-!
# Root certificates: roothood as a role

Roothood is not a data type but a **role** an index plays in a
`Morphology.Realization`, adjudicated by extensional certificates — the
`Prime`-over-a-monoid pattern, where a predicate relative to a structure
replaces a distinguished carrier. Three orthogonal axes probe the role, each
decidable per fragment:

* **Atomicity** — does every licensed cell decompose to a nonempty set of
  cores? `cellCores` is the *third* instantiation of the
  `IsConstantIn`/`IsVariantIn` pair (after `realize` and `interp`): its
  constancy cut splits form-variance into affixal inflection (*cat*/*cats*,
  cores constant) and a suppletive core (*go*/*went*, cores vary), refining
  the landed `IsOverabundant`/`IsProperlySuppletive` cell-locus cut along a
  perpendicular axis.
* **Listedness** — does the profile factor through a grammatical type (an
  f-morpheme inventory), or does some index do lexical work its type cannot
  predict (an l-morpheme)? The Harley–Noyer l/f divide ([harley-noyer-1999],
  [embick-2021]) as a provable dichotomy.
* **Categorial freedom** — is one index licensed under two distinct
  categorizers? DM acategoriality ([marantz-1997], [arad-2005]) as a
  per-fragment decidable complement to the hom-tier merger theorems.

Core extraction is parametric in `extract : F → Finset C`, so the axis is not
tied to concatenative form: the concatenative instance `coreMorphsIn` filters
a word's morphs by `Morph.IsCoreIn` ([bloomfield-1933], [qin-2025]); a
consonantal-melody instance would take `fun r => r.segments.toFinset` for
`ConsonantalRoot` (`Root/Consonantal.lean`), not built here.

These certificates adjudicate the descriptive taxonomy — the suppletion
trichotomy, l-vs-f, per-fragment categorial freedom — and are deliberately
**extensional**: they do not settle the derivational disputes (Arad-vs-Borer
first-categorization locality), which live in the admissible lax mergers of
`Realization.lean` (see its underdetermination paragraph). This is the
root-*question* layer over `Realization`, co-equal with `Paradigm/`,
`Exponence/`, and `Construction/` — not a foundation beneath them.

## Main declarations

* `cellCores`, `HasNonemptyCores` — parametric core extraction and the
  atomicity certificate.
* `HasSuppletiveCore`, `IsAffixallyInflected`, `suppletive_core_dichotomy`,
  `suppletive_taxonomy` — the constancy pair's third instantiation and the
  suppletion trichotomy.
* `coreMorphsIn` — the concatenative core-extraction instance.
* `IsFunctionalInventory`, `DoesLexicalWork`,
  `isFunctionalInventory_iff_no_lexicalWork` — the l/f-morpheme divide.
* `IsCrossCategorial` — categorial freedom.
-/

@[expose] public section

namespace Morphology.Root

open Morphology

variable {R Ctx F M C K T X : Type*}

/-! ### The constancy pair as a negation dichotomy -/

theorem isConstantIn_iff_not_isVariantIn {g : R → Ctx → Finset X} {r : R} :
    IsConstantIn g r ↔ ¬ IsVariantIn g r := by
  constructor
  · exact fun h hv => not_isConstantIn_of_isVariantIn hv h
  · intro h c c' x hx x' hx'
    by_contra hne
    exact h ⟨c, c', x, hx, x', hx', hne⟩

/-! ### Atomicity: parametric core extraction -/

/-- The cores a realization exposes at a cell: the union, over the cell's
forms, of each form's cores under `extract`. The **third** instantiation of
the `IsConstantIn`/`IsVariantIn` contextual-map slot, after `realize` and
`interp`. -/
def cellCores (S : Realization R Ctx F) (extract : F → Finset C) [DecidableEq C] :
    R → Ctx → Finset C :=
  fun r c => (S.realize r c).biUnion extract

@[simp] theorem cellCores_singleton (S : Realization R Ctx F) [DecidableEq F]
    (r : R) (c : Ctx) : cellCores S (fun f => {f}) r c = S.realize r c := by
  simp [cellCores, Finset.biUnion_singleton_eq_self]

/-- **Atomicity**: every licensed cell decomposes to at least one core — the
root always contributes segmental substance where it is realized. -/
def HasNonemptyCores (S : Realization R Ctx F) (extract : F → Finset C)
    [DecidableEq C] : Prop :=
  ∀ r c, S.IsLicensed r c → (cellCores S extract r c).Nonempty

theorem hasNonemptyCores_of_extract_nonempty (S : Realization R Ctx F)
    (extract : F → Finset C) [DecidableEq C] (hne : ∀ f, (extract f).Nonempty) :
    HasNonemptyCores S extract := by
  intro r c hlic
  obtain ⟨f, hf⟩ := hlic
  obtain ⟨x, hx⟩ := hne f
  exact ⟨x, Finset.mem_biUnion.mpr ⟨f, hf, hx⟩⟩

/-! ### The suppletion trichotomy -/

/-- **Suppletive core**: the cores themselves vary across contexts — *go*/*went*,
where no shared core survives the alternation. The `IsVariantIn` instance at
`cellCores`. -/
def HasSuppletiveCore (S : Realization R Ctx F) (extract : F → Finset C)
    [DecidableEq C] (r : R) : Prop :=
  IsVariantIn (cellCores S extract) r

/-- **Affixal inflection**: forms vary but cores do not — *cat*/*cats*, one
core across an added affix. Form-variance with a constant core. -/
def IsAffixallyInflected (S : Realization R Ctx F) (extract : F → Finset C)
    [DecidableEq C] (r : R) : Prop :=
  S.IsSuppletive r ∧ IsConstantIn (cellCores S extract) r

theorem isAffixallyInflected_iff (S : Realization R Ctx F) (extract : F → Finset C)
    [DecidableEq C] {r : R} :
    IsAffixallyInflected S extract r ↔
      S.IsSuppletive r ∧ ¬ HasSuppletiveCore S extract r := by
  rw [IsAffixallyInflected, HasSuppletiveCore, isConstantIn_iff_not_isVariantIn]

/-- **The core-axis dichotomy**: a form-variant root is either affixally
inflected (*cat*/*cats*) or has a suppletive core (*go*/*went*), exhaustively
and exclusively. -/
theorem suppletive_core_dichotomy (S : Realization R Ctx F) (extract : F → Finset C)
    [DecidableEq C] {r : R} (h : S.IsSuppletive r) :
    IsAffixallyInflected S extract r ∨ HasSuppletiveCore S extract r := by
  by_cases hv : HasSuppletiveCore S extract r
  · exact Or.inr hv
  · exact Or.inl ⟨h, isConstantIn_iff_not_isVariantIn.mpr hv⟩

/-- **The suppletion trichotomy**: a form-variant root is classified by two
orthogonal cuts — the landed cell-locus cut (`IsOverabundant`, cell-internal
*dived*/*dove*, versus `IsProperlySuppletive`, cross-cell *go*/*went*) and the
core-axis cut (`IsAffixallyInflected` versus `HasSuppletiveCore`). Their cross
product is the descriptive taxonomy of root-form variation. -/
theorem suppletive_taxonomy (S : Realization R Ctx F) (extract : F → Finset C)
    [DecidableEq C] {r : R} (h : S.IsSuppletive r) :
    (S.IsOverabundant r ∨ S.IsProperlySuppletive r) ∧
      (IsAffixallyInflected S extract r ∨ HasSuppletiveCore S extract r) :=
  ⟨S.isSuppletive_iff.mp h, suppletive_core_dichotomy S extract h⟩

theorem hasSuppletiveCore_singleton (S : Realization R Ctx F) [DecidableEq F]
    (r : R) : HasSuppletiveCore S (fun f => {f}) r ↔ S.IsSuppletive r := by
  have h : cellCores S (fun f => {f}) = S.realize := by
    funext r c; exact cellCores_singleton S r c
  rw [HasSuppletiveCore, h]; rfl

/-! ### The concatenative core-extraction instance -/

/-- The cores of a word ([bloomfield-1933], [qin-2025]): its morphs that occur
in some primary word, i.e. that satisfy `Morph.IsCoreIn` relative to the
fragment's word and free-form inventories. The affix side (`-s`, `-ness`) is
filtered out, so *cat* and *cats* share the single core *cat*. -/
def coreMorphsIn (words freeForms : List (List Morph)) (w : List Morph) :
    Finset Morph :=
  w.toFinset.filter (fun m => m.IsCoreIn words freeForms)

/-! ### Listedness: the l/f-morpheme divide -/

/-- An **f-morpheme inventory** ([harley-noyer-1999]): the interpretation-and-form
profile factors through a grammatical type — same type, same profile — so the
index carries no information its type does not. -/
def IsFunctionalInventory (S : Realization.Interpreted R Ctx F M) (τ : R → T) :
    Prop :=
  ∀ r r', τ r = τ r' → S.ProfileEq r r'

/-- An index **does lexical work** ([embick-2021]): another index shares its
type yet differs in profile, so the type underdetermines it — the l-morpheme
witness against `IsFunctionalInventory`. -/
def DoesLexicalWork (S : Realization.Interpreted R Ctx F M) (τ : R → T) (r : R) :
    Prop :=
  ∃ r', τ r = τ r' ∧ ¬ S.ProfileEq r r'

/-- **The l/f dichotomy**: an inventory is functional iff no index does lexical
work. The Harley–Noyer split ([harley-noyer-1999], [embick-2021]) as the
negation duality between the two certificates. -/
theorem isFunctionalInventory_iff_no_lexicalWork
    (S : Realization.Interpreted R Ctx F M) (τ : R → T) :
    IsFunctionalInventory S τ ↔ ∀ r, ¬ DoesLexicalWork S τ r := by
  simp only [IsFunctionalInventory, DoesLexicalWork, not_exists, not_and, not_not]

/-! ### Categorial freedom -/

/-- **Categorial freedom** ([marantz-1997], [arad-2005]): one index is licensed
in two contexts of distinct category `k` — DM acategoriality, the per-fragment
decidable complement to the hom-tier merger theorems of `Realization.lean`. -/
def IsCrossCategorial (S : Realization R Ctx F) (k : Ctx → K) (r : R) : Prop :=
  ∃ c c', k c ≠ k c' ∧ S.IsLicensed r c ∧ S.IsLicensed r c'

/-! ### Decidability -/

section Decidable

variable (S : Realization R Ctx F) (extract : F → Finset C)

instance [Fintype R] [Fintype Ctx] [DecidableEq F] [DecidableEq C] :
    Decidable (HasNonemptyCores S extract) :=
  inferInstanceAs (Decidable (∀ r c, S.IsLicensed r c →
    (cellCores S extract r c).Nonempty))

instance [Fintype Ctx] [DecidableEq C] (r : R) :
    Decidable (HasSuppletiveCore S extract r) :=
  inferInstanceAs (Decidable (∃ c c', ∃ x ∈ cellCores S extract r c,
    ∃ x' ∈ cellCores S extract r c', x ≠ x'))

instance [Fintype Ctx] [DecidableEq F] [DecidableEq C] (r : R) :
    Decidable (IsAffixallyInflected S extract r) :=
  inferInstanceAs (Decidable (S.IsSuppletive r ∧ ∀ c c' : Ctx,
    ∀ x ∈ cellCores S extract r c, ∀ x' ∈ cellCores S extract r c', x = x'))

instance [Fintype Ctx] [DecidableEq F] [DecidableEq K] (k : Ctx → K) (r : R) :
    Decidable (IsCrossCategorial S k r) :=
  inferInstanceAs (Decidable (∃ c c', k c ≠ k c' ∧
    S.IsLicensed r c ∧ S.IsLicensed r c'))

end Decidable

section DecidableInterpreted

variable (S : Realization.Interpreted R Ctx F M) (τ : R → T)

instance [Fintype Ctx] [DecidableEq F] [DecidableEq M] (r r' : R) :
    Decidable (S.ProfileEq r r') :=
  inferInstanceAs (Decidable ((∀ c, S.realize r c = S.realize r' c) ∧
    (∀ c, S.interp r c = S.interp r' c)))

instance [Fintype R] [Fintype Ctx] [DecidableEq T] [DecidableEq F] [DecidableEq M] :
    Decidable (IsFunctionalInventory S τ) :=
  inferInstanceAs (Decidable (∀ r r', τ r = τ r' → S.ProfileEq r r'))

instance [Fintype R] [Fintype Ctx] [DecidableEq T] [DecidableEq F] [DecidableEq M]
    (r : R) : Decidable (DoesLexicalWork S τ r) :=
  inferInstanceAs (Decidable (∃ r', τ r = τ r' ∧ ¬ S.ProfileEq r r'))

end DecidableInterpreted

end Morphology.Root
