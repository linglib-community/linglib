module

public import Linglib.Morphology.Inflection
public import Linglib.Morphology.Realization
public import Linglib.Morphology.Exponence.Select
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Finset.Card

/-!
# Paradigm linkage

This file defines Stump's paradigm linkage, which realizes a lexeme's content cell `⟨l, σ⟩`
through form cells `⟨z, τ⟩` of its stems. A linkage is a stem selection, a `Realization` of
lexemes by stems, together with a lexeme-sensitive property mapping from content property sets
to form property sets. Each deviation from canonical linkage negates one of its axes, after
Corbett's canonical typology. Stump maintains that PRAMEN, whose stem is phonologically constant
across two inflection classes, exhibits "a kind of stem suppletion", on which view heteroclisis
"simply entails suppletion". Stump's rules of paradigm linkage compete by Pāṇini's principle,
here the Elsewhere selection of a narrowest applicable rule, and a cell that no rule reaches
takes the lexeme's root.

## Main definitions

* `Linkage`, `Linkage.corr`, `Linkage.realized`: the linkage, its form correspondents, and the
  realized paradigm.
* `Linkage.IsCanonical`, relative to an identification `ι` of content with form property sets,
  with the deviations `IsDefective`, `IsSyncretic`, `IsUnfaithful`.
* `Linkage.IsInvariantAlong`, `Linkage.IsHeteroclite`: per-lexeme invariance and variance of
  stems along a projection, such as their inflection class.
* `Linkage.ofFun`, `Linkage.canonical`: the linkage of a stem-choice function.
* `Linkage.ofRules`: the linkage of rules of paradigm linkage, each cell taking the stem its
  lexeme's rules realize over the lexeme's root.
* `Linkage.toInflectionalParadigm`: the inflectional paradigm of a linkage's form
  correspondents.

## Main results

* `Linkage.IsHeteroclite.isSuppletive`, `Linkage.IsHeteroclite.not_isClassDetermined`: heteroclisis
  entails suppletion, the stems of a heteroclite lexeme being determined by no one class.
* `Linkage.realized_eq_of_corr_eq`: equal correspondent sets force equal realizations.
* `Linkage.ofFun_isCanonical_iff`: under an injective identification, the linkage of a stem
  choice is canonical exactly when each lexeme's stem is constant.
* `Linkage.ofRules_nil`: with no language-specific rules, the linkage of rules is the canonical
  linkage of the roots.

## Implementation notes

`IsTotal`, `IsUnivalent`, and the per-lexeme `IsInvariant`, `IsSuppletive`, and
`IsOverabundant` (Thornton's cell-mates) are inherited from `Realization`; defectiveness and
syncretism are its `IsDefective` of the stems and `IsSyncretic` of the form correspondents.
Taking `S = M` and `ι = id` recovers a single type of property sets. The universal default rule (5) is not a
listed rule of `ofRules` but the fallback of `RuleSet.realizeMinimalD`, the lexeme's
root.

## References

* [corbett-2007]
* [stump-2006]
* [stump-2012-mmm8]
* [stump-2016]
* [thornton-2011]
-/

@[expose] public section

namespace Morphology

/-- A paradigm linkage ([stump-2012-mmm8]) consists of a stem selection, the inherited
`realize`, which gives the finite set of stems realizing each content cell `⟨l, σ⟩`, and a
property mapping `pm`. The stem set is empty at a gap in the stem specification and has several
members at an overabundant cell. Content and form cells carry property sets of types `S` and
`M`, since [stump-2006] (p. 288) distinguishes a language's s-properties, "any property
belonging to σ in a content-cell ⟨L, σ⟩", from its m-properties, "any property belonging to τ in
a form-cell ⟨s, τ⟩", so that the relation between their property sets "can be represented as a
function from sets of s-properties to sets of m-properties", a property mapping; "in the
simplest cases—those determined by the default rule of paradigm linkage in 5—the relevant
property mapping is an identity function". -/
structure Linkage (L Z S M : Type*) extends Realization L S Z where
  /-- The property mapping carries a content cell's property set to that of its form
  correspondents, and may consult the lexeme. -/
  pm : L → S → M

namespace Linkage

variable {L Z S M W X Y K : Type*} (ℓ : Linkage L Z S M)

/-- The form correspondents of a content cell `⟨l, σ⟩` pair each of its stems with the mapped
property set `ℓ.pm l σ`. -/
def corr (l : L) (σ : S) : Finset (Z × M) := ℓ.realize l σ ×ˢ {ℓ.pm l σ}

@[simp] theorem mem_corr {l : L} {σ : S} {zτ : Z × M} :
    zτ ∈ ℓ.corr l σ ↔ zτ.1 ∈ ℓ.realize l σ ∧ zτ.2 = ℓ.pm l σ := by
  rw [corr, Finset.mem_product, Finset.mem_singleton]

@[simp] theorem corr_nonempty (l : L) (σ : S) :
    (ℓ.corr l σ).Nonempty ↔ (ℓ.realize l σ).Nonempty := by
  simp [corr]

@[simp] theorem card_corr (l : L) (σ : S) : (ℓ.corr l σ).card = (ℓ.realize l σ).card := by
  simp [corr]

/-- The realization of each content cell by its form correspondents. -/
def correspondents : Realization L S (Z × M) := ⟨ℓ.corr⟩

@[simp] theorem correspondents_realize (l : L) (σ : S) :
    ℓ.correspondents.realize l σ = ℓ.corr l σ := rfl

/-- The realized paradigm of a content cell realizes each form correspondent `⟨z, τ⟩` as
`rf z τ`, keeping the property set `τ`. -/
def realized [DecidableEq W] (rf : Z → M → W) (l : L) (σ : S) : Finset (W × M) :=
  ((ℓ.realize l σ).image fun z ↦ rf z (ℓ.pm l σ)) ×ˢ {ℓ.pm l σ}

@[simp] theorem mem_realized [DecidableEq W] {rf : Z → M → W} {l : L} {σ : S} {wτ : W × M} :
    wτ ∈ ℓ.realized rf l σ ↔ ∃ z ∈ ℓ.realize l σ, (rf z (ℓ.pm l σ), ℓ.pm l σ) = wτ := by
  simp [realized, Prod.ext_iff]

/-! ### Canonical linkage -/

/-- A linkage is stem-invariant when each lexeme draws the stems of all its cells from a single
stem. -/
def IsStemInvariant : Prop := ∀ l, ℓ.IsInvariant l

/-- A linkage is injective when no two content cells of a lexeme share a form correspondent. -/
def IsInjective : Prop := ∀ l, Relator.LeftUnique (ℓ.correspondents.Rel l)

/-- A linkage is property-preserving relative to an identification `ι` of content with form
property sets when every form correspondent carries the image under `ι` of its content cell's
property set. -/
def IsPropertyPreserving (ι : S → M) : Prop := ∀ l σ, ℓ.pm l σ = ι σ

/-- (13): A linkage is canonical ([stump-2012-mmm8]) relative to an identification `ι` of content
with form property sets when the relation between each lexeme's content cells and their form
correspondents is a total function, (13a), drawn from one stem, (13b), and one-to-one, (13c), and
every form correspondent is faithful to its content cell, (13d). Totality and univalence are
stated of the stems, which is the same by `isTotal_correspondents_iff` and
`isUnivalent_correspondents_iff`. -/
structure IsCanonical (ι : S → M) : Prop where
  /-- Every content cell has a form correspondent. -/
  total : ℓ.IsTotal
  /-- No content cell has more than one form correspondent. -/
  univalent : ℓ.IsUnivalent
  /-- All of a lexeme's form correspondents share one stem. -/
  stemInvariant : ℓ.IsStemInvariant
  /-- No two content cells of a lexeme share a form correspondent. -/
  injective : ℓ.IsInjective
  /-- Every form correspondent carries the image of its content cell's property set. -/
  propertyPreserving : ℓ.IsPropertyPreserving ι

/-! ### Deviations from canonical linkage -/

/-- A linkage is defective ([stump-2012-mmm8]) when some content cell has no stem. -/
def IsDefective : Prop := ∃ l, ℓ.toRealization.IsDefective l

/-- A linkage is syncretic ([stump-2012-mmm8]) when two distinct content cells of a lexeme share
a form correspondent. -/
def IsSyncretic : Prop := ∃ l, ℓ.correspondents.IsSyncretic l

/-- A linkage is unfaithful ([stump-2012-mmm8]) relative to `ι` when some content cell's form
correspondents carry a property set other than its image under `ι`, as under deponency and
functor-argument reversal. -/
def IsUnfaithful (ι : S → M) : Prop := ∃ l σ, ℓ.pm l σ ≠ ι σ

/-- A form cell is virtual ([stump-2012-mmm8]) when no content cell corresponds to it. -/
def IsVirtual (zτ : Z × M) : Prop := ∀ l σ, zτ ∉ ℓ.corr l σ

@[simp, push] theorem not_isTotal_iff : ¬ ℓ.IsTotal ↔ ℓ.IsDefective :=
  Realization.not_isTotal_iff

@[simp, push] theorem not_isInjective_iff : ¬ ℓ.IsInjective ↔ ℓ.IsSyncretic := by
  simp [IsSyncretic, IsInjective, Realization.IsSyncretic]

/-- A content cell has a form correspondent exactly when it has a stem. -/
theorem isTotal_correspondents_iff : ℓ.correspondents.IsTotal ↔ ℓ.IsTotal :=
  forall₂_congr fun l σ ↦ ℓ.corr_nonempty l σ

/-- A content cell has at most one form correspondent exactly when it has at most one stem. -/
theorem isUnivalent_correspondents_iff : ℓ.correspondents.IsUnivalent ↔ ℓ.IsUnivalent := by
  simp [Realization.isUnivalent_iff_card]

theorem isDefective_iff : ℓ.IsDefective ↔ ∃ l σ, ℓ.realize l σ = ∅ :=
  exists_congr fun _ ↦ Realization.isDefective_iff

theorem isInjective_iff :
    ℓ.IsInjective ↔ ∀ l σ₁ σ₂, σ₁ ≠ σ₂ → Disjoint (ℓ.corr l σ₁) (ℓ.corr l σ₂) :=
  forall_congr' fun _ ↦ Realization.leftUnique_rel_iff

variable {ℓ} in
theorem isSyncretic_of_not_disjoint {l : L} {σ₁ σ₂ : S} (hne : σ₁ ≠ σ₂)
    (h : ¬ Disjoint (ℓ.corr l σ₁) (ℓ.corr l σ₂)) : ℓ.IsSyncretic :=
  ⟨l, Realization.isSyncretic_of_not_disjoint hne h⟩

@[simp, push] theorem not_isPropertyPreserving_iff (ι : S → M) :
    ¬ ℓ.IsPropertyPreserving ι ↔ ℓ.IsUnfaithful ι := by
  simp [IsUnfaithful, IsPropertyPreserving]

theorem isInjective_of_injective_pm {ℓ : Linkage L Z S M}
    (h : ∀ l, Function.Injective (ℓ.pm l)) : ℓ.IsInjective :=
  fun l _ _ _ h₁ h₂ ↦ h l (((mem_corr ℓ).mp h₁).2.symm.trans ((mem_corr ℓ).mp h₂).2)

/-! ### Invariance along a projection -/

/-- A lexeme is invariant along `p` when the stems of all its cells have one image under `p`;
along `id` this is `IsInvariant`. -/
def IsInvariantAlong (p : Z → X) (l : L) : Prop := (p '' ℓ.exponents l).Subsingleton

/-- A lexeme is heteroclite along a classification `cls` of stems ([stump-2006]) when two of
its cells draw on stems of distinct classes; along `id` this is `IsSuppletive`. -/
def IsHeteroclite (cls : Z → K) (l : L) : Prop := (cls '' ℓ.exponents l).Nontrivial

variable {ℓ} {p : Z → X} {cls : Z → K} {l : L}

theorem isInvariantAlong_iff : ℓ.IsInvariantAlong p l ↔
    ∀ σ σ', ∀ z ∈ ℓ.realize l σ, ∀ z' ∈ ℓ.realize l σ', p z = p z' :=
  ⟨fun h _ _ _ hz _ hz' ↦ h ⟨_, ⟨_, hz⟩, rfl⟩ ⟨_, ⟨_, hz'⟩, rfl⟩,
    fun h ↦ by rintro _ ⟨z, ⟨σ, hz⟩, rfl⟩ _ ⟨z', ⟨σ', hz'⟩, rfl⟩; exact h σ σ' z hz z' hz'⟩

theorem isHeteroclite_iff : ℓ.IsHeteroclite cls l ↔
    ∃ σ σ', ∃ z ∈ ℓ.realize l σ, ∃ z' ∈ ℓ.realize l σ', cls z ≠ cls z' :=
  ⟨by rintro ⟨_, ⟨z, ⟨σ, hz⟩, rfl⟩, _, ⟨z', ⟨σ', hz'⟩, rfl⟩, hne⟩
      exact ⟨σ, σ', z, hz, z', hz', hne⟩,
    fun ⟨σ, σ', z, hz, z', hz', hne⟩ ↦ ⟨_, ⟨z, ⟨σ, hz⟩, rfl⟩, _, ⟨z', ⟨σ', hz'⟩, rfl⟩, hne⟩⟩

theorem isInvariantAlong_id_iff : ℓ.IsInvariantAlong id l ↔ ℓ.IsInvariant l := by
  rw [IsInvariantAlong, Set.image_id, Realization.IsInvariant]

theorem isHeteroclite_id_iff : ℓ.IsHeteroclite id l ↔ ℓ.IsSuppletive l := by
  rw [IsHeteroclite, Set.image_id, Realization.IsSuppletive]

@[simp, push] theorem not_isInvariantAlong_iff :
    ¬ ℓ.IsInvariantAlong p l ↔ ℓ.IsHeteroclite p l :=
  Set.not_subsingleton_iff

theorem IsInvariantAlong.comp (h : ℓ.IsInvariantAlong p l) (q : X → Y) :
    ℓ.IsInvariantAlong (q ∘ p) l := by
  rw [IsInvariantAlong, Set.image_comp]; exact h.image q

theorem _root_.Morphology.Realization.IsInvariant.isInvariantAlong (h : ℓ.IsInvariant l)
    (p : Z → X) : ℓ.IsInvariantAlong p l :=
  Set.Subsingleton.image h p

/-- Heteroclisis entails suppletion, since stems of two classes are two stems. -/
theorem IsHeteroclite.isSuppletive (h : ℓ.IsHeteroclite cls l) : ℓ.IsSuppletive l :=
  Set.nontrivial_of_image cls _ h

/-- When each pattern draws its stems from one class, a heteroclite lexeme's stems are not
class-determined, so their alternation is suppletion in [stump-2016]'s sense. -/
theorem IsHeteroclite.not_isClassDetermined {A : Set (S → Z)}
    (hA : ∀ p ∈ A, ∀ σ σ', cls (p σ) = cls (p σ')) (h : ℓ.IsHeteroclite cls l) :
    ¬ ℓ.IsClassDetermined A l := fun ⟨p, hp, hl⟩ ↦
  let ⟨σ, σ', z, hz, z', hz', hne⟩ := isHeteroclite_iff.1 h
  hne (by rw [hl σ z hz, hl σ' z' hz']; exact hA p hp σ σ')

/-! ### Decidability

The per-lexeme instances quantify over cells and their finite sets of stems, so they need no
`Fintype Z`. -/

section Decidable

variable (ℓ) [Fintype S]

instance [DecidableEq X] (p : Z → X) (l : L) : Decidable (ℓ.IsInvariantAlong p l) :=
  decidable_of_iff _ isInvariantAlong_iff.symm

instance [DecidableEq K] (cls : Z → K) (l : L) : Decidable (ℓ.IsHeteroclite cls l) :=
  decidable_of_iff _ isHeteroclite_iff.symm

variable [Fintype L]

instance [DecidableEq Z] : Decidable ℓ.IsStemInvariant :=
  inferInstanceAs (Decidable (∀ l, ℓ.IsInvariant l))

instance [DecidableEq Z] [DecidableEq S] [DecidableEq M] : Decidable ℓ.IsInjective :=
  inferInstanceAs (Decidable (∀ l, Relator.LeftUnique (ℓ.correspondents.Rel l)))

instance [DecidableEq M] (ι : S → M) : Decidable (ℓ.IsPropertyPreserving ι) :=
  inferInstanceAs (Decidable (∀ l σ, ℓ.pm l σ = ι σ))

instance [DecidableEq Z] : Decidable ℓ.IsDefective :=
  inferInstanceAs (Decidable (∃ l, ℓ.toRealization.IsDefective l))

instance [DecidableEq Z] [DecidableEq S] [DecidableEq M] : Decidable ℓ.IsSyncretic :=
  inferInstanceAs (Decidable (∃ l, ℓ.correspondents.IsSyncretic l))

instance [DecidableEq M] (ι : S → M) : Decidable (ℓ.IsUnfaithful ι) :=
  inferInstanceAs (Decidable (∃ l σ, ℓ.pm l σ ≠ ι σ))

instance [DecidableEq Z] [DecidableEq M] (zτ : Z × M) : Decidable (ℓ.IsVirtual zτ) :=
  inferInstanceAs (Decidable (∀ l σ, zτ ∉ ℓ.corr l σ))

end Decidable

/-! ### Realization through correspondents -/

section Realized

variable (ℓ) [DecidableEq W] (rf : Z → M → W)

theorem realized_eq_image_corr [DecidableEq M] (l : L) (σ : S) :
    ℓ.realized rf l σ = (ℓ.corr l σ).image fun zτ ↦ (rf zτ.1 zτ.2, zτ.2) := by
  ext; simp

/-- Equal correspondent sets force equal realizations, within a lexeme (the mechanism of
syncretism) and across lexemes. -/
theorem realized_eq_of_corr_eq {l₁ l₂ : L} {σ₁ σ₂ : S} (h : ℓ.corr l₁ σ₁ = ℓ.corr l₂ σ₂) :
    ℓ.realized rf l₁ σ₁ = ℓ.realized rf l₂ σ₂ := by
  classical
  rw [realized_eq_image_corr, realized_eq_image_corr, h]

end Realized

/-! ### The inflectional paradigm of a linkage -/

/-- The inflectional paradigm of a linkage with realization rules `rf` builds the forms of each
content cell from its form correspondents. -/
def toInflectionalParadigm (rf : Z → M → W) : InflectionalParadigm L S Z M W :=
  ⟨ℓ.correspondents, rf⟩

section ToInflectionalParadigm

variable (rf : Z → M → W)

/-- The stems of a linkage's inflectional paradigm are the stems it selects. -/
theorem toInflectionalParadigm_stem [DecidableEq Z] :
    (ℓ.toInflectionalParadigm rf).stem = ℓ.toRealization := by
  show (⟨fun l σ ↦ (ℓ.corr l σ).image Prod.fst⟩ : Realization L S Z) = ⟨ℓ.realize⟩
  congr 1
  funext l σ
  ext z
  simp

/-- A linkage is stem-invariant exactly when its inflectional paradigm's stems are invariant, the
lexical row of canonical inflection. -/
theorem isStemInvariant_iff_stem_isInvariant [DecidableEq Z] :
    ℓ.IsStemInvariant ↔ ∀ l, (ℓ.toInflectionalParadigm rf).stem.IsInvariant l := by
  rw [toInflectionalParadigm_stem]; rfl

theorem toInflectionalParadigm_realization_realize [DecidableEq W] (l : L) (σ : S) :
    (ℓ.toInflectionalParadigm rf).realization.realize l σ =
      (ℓ.realize l σ).image fun z ↦ rf z (ℓ.pm l σ) := by
  ext w
  simp [InflectionalParadigm.realization, toInflectionalParadigm]

end ToInflectionalParadigm

/-! ### Linkages of stem-choice functions -/

/-- The linkage of a stem choice `f` under an identification `ι` gives the content cell
`⟨l, σ⟩` the single stem `f l σ` and the form property set `ι σ`. -/
def ofFun (ι : S → M) (f : L → S → Z) : Linkage L Z S M where
  realize l σ := {f l σ}
  pm _ σ := ι σ

section OfFun

variable (ι : S → M) (f : L → S → Z)

@[simp] theorem ofFun_realize (l : L) (σ : S) : (ofFun ι f).realize l σ = {f l σ} := rfl

@[simp] theorem ofFun_pm (l : L) (σ : S) : (ofFun ι f).pm l σ = ι σ := rfl

@[simp] theorem ofFun_corr (l : L) (σ : S) : (ofFun ι f).corr l σ = {(f l σ, ι σ)} :=
  Finset.singleton_product_singleton

@[simp] theorem ofFun_realized [DecidableEq W] (rf : Z → M → W) (l : L) (σ : S) :
    (ofFun ι f).realized rf l σ = {(rf (f l σ) (ι σ), ι σ)} := by
  simp [realized]

variable {ι f}

@[simp] theorem ofFun_isInvariantAlong_iff :
    (ofFun ι f).IsInvariantAlong p l ↔ ∀ σ σ', p (f l σ) = p (f l σ') := by
  simp [isInvariantAlong_iff]

@[simp] theorem ofFun_isHeteroclite_iff :
    (ofFun ι f).IsHeteroclite cls l ↔ ∃ σ σ', cls (f l σ) ≠ cls (f l σ') := by
  simp [isHeteroclite_iff]

/-- Under an injective identification, the linkage of a stem choice is canonical exactly when
each lexeme's stem is independent of the property set. -/
theorem ofFun_isCanonical_iff (hι : Function.Injective ι) :
    (ofFun ι f).IsCanonical ι ↔ ∀ l σ σ', f l σ = f l σ' := by
  have key l : (ofFun ι f).IsInvariant l ↔ ∀ σ σ', f l σ = f l σ' := by
    simp [Realization.isInvariant_iff]
  exact ⟨fun h l ↦ (key l).1 (h.stemInvariant l), fun h ↦
    ⟨fun _ _ ↦ Finset.singleton_nonempty _,
      Realization.isUnivalent_iff_card.2 fun _ _ ↦ (Finset.card_singleton _).le,
      fun l ↦ (key l).2 (h l), isInjective_of_injective_pm fun _ ↦ hι, fun _ _ ↦ rfl⟩⟩

end OfFun

/-- The canonical linkage of `st` under `ι` gives every cell of the lexeme `l` the stem `st l`
and the image under `ι` of its property set. It is the linkage of the universal default rule of
paradigm linkage (5) of [stump-2006] with no language-specific rules (`ofRules_nil`), `st l`
being the root of `l`. -/
abbrev canonical (ι : S → M) (st : L → Z) : Linkage L Z S M := ofFun ι fun l _ ↦ st l

theorem canonical_isCanonical {ι : S → M} (hι : Function.Injective ι) (st : L → Z) :
    (canonical ι st).IsCanonical ι :=
  (ofFun_isCanonical_iff hι).mpr fun _ _ _ ↦ rfl

/-! ### Rules of paradigm linkage -/

section Rules

variable {R : Type*} [ExponenceRule R S Z] {κ : Type*} [Preorder κ]
  [DecidableRel (· < · : κ → κ → Prop)] [DecidableRel (Applies : R → S → Prop)]

/-- The linkage of rules of paradigm linkage gives each content cell the stem that its
lexeme's rules realize, the exponent of an applicable rule that no applicable rule is narrower
than under `key`, or the lexeme's root, by the universal default rule (5) of [stump-2006], where
none of its rules applies; its form property set is the image under `ι` of the cell's. -/
abbrev ofRules (ι : S → M) (key : R → κ) (rules : L → List R) (root : L → Z) :
    Linkage L Z S M :=
  ofFun ι fun l σ ↦ RuleSet.realizeMinimalD (rules l) key (fun _ ↦ root l) σ

/-- With no language-specific rules, the linkage of rules is the canonical linkage of the
roots. -/
theorem ofRules_nil (ι : S → M) (key : R → κ) (st : L → Z) :
    ofRules ι key (fun _ ↦ ([] : List R)) st = canonical ι st :=
  rfl

end Rules

end Linkage

end Morphology
