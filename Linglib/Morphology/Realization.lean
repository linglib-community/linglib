/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Union

/-!
# Root realizations: indices realized in context

A realization assigns to an index `r` and a context `c` the finite set `realize r c` of forms
that realize `r` in `c`. The index is opaque, and the frameworks that separate an item from its
form choose it differently: a root of Distributed Morphology, given its form at Vocabulary
Insertion; one of Borer's roots, a phonological index whose form its categorial context selects,
as *grow* and *growth*; a lexeme of Paradigm Function Morphology, realized at a cell; Spencer's
lexemic index. An empty set says that `r` is not licensed in `c`, and a set of two forms is an
overabundant cell. An interpreted realization adds a second contextual map, to readings, which
is Marantz's separation of the forms of List 2 from the meanings of List 3.

A homomorphism of realizations merges indices and translates contexts so that realization is
preserved. The strict homomorphisms of interpreted realizations translate contexts independently
of the index and preserve readings too, so the indices they merge have the same forms and
readings in every context, and passing to these profiles, `Interpreted.reduce`, merges as much
as any strict homomorphism can. The disputes over individuation, such as fat roots against sister
roots, are mergers at the lax tier, which include forms and readings rather than preserving them.

## Main definitions

* `Morphology.Realization`: indices realized in context, with `IsLicensed`, `Realizes`,
  `exponents`, `IsTotal` and `IsUnivalent`.
* `Morphology.IsConstantIn`, `Morphology.IsVariantIn`: constancy and variance of a contextual map
  at an index, which give `IsInvariant` and `IsSuppletive` for forms and `IsIntrinsic` and
  `IsAllosemous` for readings.
* `Morphology.Realization.Hom`, `Morphology.Realization.Interpreted.Hom`,
  `Morphology.Realization.Interpreted.LaxHom`: mergers of indices, the strict ones preserving
  readings.
* `Morphology.Realization.comp`: realization through an intermediate inventory.
* `Morphology.Realization.Interpreted.reduce`: the realization on profiles.

## Main statements

* `Morphology.Realization.isSuppletive_iff`: form variance at an index is overabundance in one
  cell or suppletion across cells.
* `Morphology.Realization.Interpreted.Hom.profileEq_of_onRoot_eq`: indices that a strict
  homomorphism merges have the same profile.

## Implementation notes

* Sign-based lexicalism, Construction Morphology and Haspelmath's morph-based comparative root
  are rival ontologies that the parameters of a realization measure, not instances of it. The
  interface does not say whether indices are listed or constructed.
* A strict homomorphism cannot consult the index when it translates contexts, so categorial
  information has to sit in the context, which quietly encodes the Categorization Assumption.
* Extensional profiles underdetermine individuation. The criteria the literature uses, such as
  locality of first categorization, are further structure on admissible mergers that studies
  supply.

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
-/

@[expose] public section

namespace Morphology

variable {R Ctx F M X : Type*}

/-- `IsConstantIn g r` says all values of the contextual map `g` at the index
`r` coincide across all contexts. -/
def IsConstantIn (g : R → Ctx → Finset X) (r : R) : Prop :=
  ∀ ⦃c c' : Ctx⦄, ∀ x ∈ g r c, ∀ x' ∈ g r c', x = x'

/-- `IsVariantIn g r` says two distinct values of the contextual map `g` arise
at the index `r`. -/
def IsVariantIn (g : R → Ctx → Finset X) (r : R) : Prop :=
  ∃ c c', ∃ x ∈ g r c, ∃ x' ∈ g r c', x ≠ x'

theorem not_isConstantIn_of_isVariantIn {g : R → Ctx → Finset X} {r : R}
    (h : IsVariantIn g r) : ¬ IsConstantIn g r := by
  obtain ⟨c, c', x, hx, x', hx', hne⟩ := h
  exact fun hc => hne (hc x hx x' hx')

theorem isConstantIn_iff_subsingleton {g : R → Ctx → Finset X} {r : R} :
    IsConstantIn g r ↔ {x | ∃ c, x ∈ g r c}.Subsingleton := by
  constructor
  · rintro h x ⟨c, hx⟩ x' ⟨c', hx'⟩
    exact h x hx x' hx'
  · intro h c c' x hx x' hx'
    exact h ⟨c, hx⟩ ⟨c', hx'⟩

/-- A root realization realizes an opaque index type in context. The fiber
`realize r c` is empty where `r` is unlicensed and non-singleton at an
overabundant cell. -/
structure Realization (R Ctx F : Type*) where
  /-- `realize r c` is the set of forms realizing the index `r` in the context
  `c`, computed by Vocabulary Insertion (DM), the paradigm function (PFM) or
  spellout (nanosyntax). -/
  realize : R → Ctx → Finset F

namespace Realization

variable (S : Realization R Ctx F)

/-- `r` is licensed in `c` when some realization of it exists there. -/
def IsLicensed (r : R) (c : Ctx) : Prop := (S.realize r c).Nonempty

/-- `f` realizes `r` in some context. -/
def Realizes (r : R) (f : F) : Prop := ∃ c, f ∈ S.realize r c

/-- `exponents r` is the allomorph set of the root `r`. -/
def exponents (r : R) : Set F := {f | S.Realizes r f}

@[simp] theorem mem_exponents {r : R} {f : F} :
    f ∈ S.exponents r ↔ S.Realizes r f := Iff.rfl

/-- `IsTotal` says every index is licensed everywhere, PFM's stratum. -/
def IsTotal : Prop := ∀ r c, (S.realize r c).Nonempty

/-- `IsUnivalent` says every cell has at most one form, the stratum of
`Option`-shaped engine outputs. -/
def IsUnivalent : Prop := ∀ r c, (S.realize r c).card ≤ 1

/-- `IsInvariant r` says `r` has one form wherever it is licensed, the
classical context-free morpheme as the degenerate case. -/
def IsInvariant (r : R) : Prop := IsConstantIn S.realize r

/-- `IsSuppletive r` says `r` has two distinct forms, in contexts that need not
differ, as √GO has *go* and *went*, the case behind [harley-2014]'s argument
that indices, not forms, individuate. -/
def IsSuppletive (r : R) : Prop := IsVariantIn S.realize r

theorem not_isInvariant_of_isSuppletive {r : R} (h : S.IsSuppletive r) :
    ¬ S.IsInvariant r :=
  not_isConstantIn_of_isVariantIn h

theorem isInvariant_iff_subsingleton_exponents {r : R} :
    S.IsInvariant r ↔ (S.exponents r).Subsingleton :=
  isConstantIn_iff_subsingleton

/-- An index is overabundant when some cell offers two forms, as *dived* and *dove*
share one cell ([thornton-2011]'s cell-mates). This is cell-internal variance,
disjoint in kind from suppletion. -/
def IsOverabundant (r : R) : Prop := ∃ c, 1 < (S.realize r c).card

/-- `IsProperlySuppletive r` says two licensed contexts of `r` are realized by
different fibers, as √GO is by *go* and *went*. An unlicensed cell never
witnesses it. -/
def IsProperlySuppletive (r : R) : Prop :=
  ∃ c c', (S.realize r c).Nonempty ∧ (S.realize r c').Nonempty ∧
    S.realize r c ≠ S.realize r c'

/-- Form variance at an index decomposes into overabundance or suppletion
proper. -/
theorem isSuppletive_iff {r : R} :
    S.IsSuppletive r ↔ S.IsOverabundant r ∨ S.IsProperlySuppletive r := by
  constructor
  · rintro ⟨c, c', x, hx, x', hx', hne⟩
    by_cases hfib : S.realize r c = S.realize r c'
    · exact Or.inl ⟨c, Finset.one_lt_card.mpr ⟨x, hx, x', hfib ▸ hx', hne⟩⟩
    · exact Or.inr ⟨c, c', ⟨x, hx⟩, ⟨x', hx'⟩, hfib⟩
  · rintro (⟨c, hc⟩ | ⟨c, c', ⟨x, hx⟩, ⟨x', hx'⟩, hne⟩)
    · obtain ⟨y, hy, y', hy', hne⟩ := Finset.one_lt_card.mp hc
      exact ⟨c, c, y, hy, y', hy', hne⟩
    · by_cases hsub : S.realize r c ⊆ S.realize r c'
      · have hns : ¬ S.realize r c' ⊆ S.realize r c :=
          fun h => hne (Finset.Subset.antisymm hsub h)
        obtain ⟨y, hy, hy'⟩ := Finset.not_subset.mp hns
        exact ⟨c', c, y, hy, x, hx, fun h => hy' (h ▸ hx)⟩
      · obtain ⟨y, hy, hy'⟩ := Finset.not_subset.mp hsub
        exact ⟨c, c', y, hy, x', hx', fun h => hy' (h ▸ hx')⟩

/-- `RealizeEq r r'` says `r` and `r'` have the same realization in every
context. -/
def RealizeEq (r r' : R) : Prop := ∀ c, S.realize r c = S.realize r' c

theorem RealizeEq.symm {r r' : R} (h : S.RealizeEq r r') :
    S.RealizeEq r' r := fun c => (h c).symm

/-- `IsHomophonous r r'` says the distinct indices `r` and `r'` share every
realization, as *bank₁* and *bank₂* do; spellout is nowhere required to be
injective. -/
def IsHomophonous (r r' : R) : Prop := r ≠ r' ∧ S.RealizeEq r r'

theorem IsHomophonous.symm {r r' : R} (h : S.IsHomophonous r r') :
    S.IsHomophonous r' r :=
  ⟨h.1.symm, fun c => (h.2 c).symm⟩

section Decidable

variable [Fintype Ctx] [DecidableEq F]

instance (r : R) (c : Ctx) : Decidable (S.IsLicensed r c) :=
  inferInstanceAs (Decidable (S.realize r c).Nonempty)

instance (r : R) (f : F) : Decidable (S.Realizes r f) :=
  inferInstanceAs (Decidable (∃ c, f ∈ S.realize r c))

instance (r : R) : Decidable (S.IsInvariant r) :=
  inferInstanceAs (Decidable (∀ c c' : Ctx,
    ∀ x ∈ S.realize r c, ∀ x' ∈ S.realize r c', x = x'))

instance (r : R) : Decidable (S.IsSuppletive r) :=
  inferInstanceAs (Decidable (∃ c c',
    ∃ x ∈ S.realize r c, ∃ x' ∈ S.realize r c', x ≠ x'))

instance (r : R) : Decidable (S.IsOverabundant r) :=
  inferInstanceAs (Decidable (∃ c, 1 < (S.realize r c).card))

instance (r : R) : Decidable (S.IsProperlySuppletive r) :=
  inferInstanceAs (Decidable (∃ c c', (S.realize r c).Nonempty ∧
    (S.realize r c').Nonempty ∧ S.realize r c ≠ S.realize r c'))

instance (r r' : R) : Decidable (S.RealizeEq r r') :=
  inferInstanceAs (Decidable (∀ c : Ctx, S.realize r c = S.realize r' c))

instance [DecidableEq R] (r r' : R) : Decidable (S.IsHomophonous r r') :=
  inferInstanceAs (Decidable (_ ∧ _))

variable [Fintype R]

instance : Decidable S.IsTotal :=
  inferInstanceAs (Decidable (∀ r c, (S.realize r c).Nonempty))

instance : Decidable S.IsUnivalent :=
  inferInstanceAs (Decidable (∀ r c, (S.realize r c).card ≤ 1))

end Decidable

/-- The pipeline composition `S.comp T` realizes through an intermediate
inventory, the Kleisli composition of `Finset` over a shared context.
Late-insertion architectures factor the grammar's realization as such a
composite; PFM's stem-choice-then-blocks cascade is another. -/
def comp {G : Type*} [DecidableEq G] (S : Realization R Ctx F)
    (T : Realization F Ctx G) : Realization R Ctx G :=
  ⟨fun r c => (S.realize r c).biUnion (fun f => T.realize f c)⟩

theorem comp_isTotal {G : Type*} [DecidableEq G] {S : Realization R Ctx F}
    {T : Realization F Ctx G} (hS : S.IsTotal) (hT : T.IsTotal) :
    (S.comp T).IsTotal := by
  intro r c
  obtain ⟨f, hf⟩ := hS r c
  obtain ⟨g, hg⟩ := hT f c
  exact ⟨g, Finset.mem_biUnion.mpr ⟨f, hf, hg⟩⟩

section Hom

variable {R₁ C₁ R₂ C₂ R₃ C₃ : Type*}

/-- A hom is an index merger that tracks spellout, in which `onRoot` may merge
indices and `onCtx` translates contexts and may consult the source index. It is
the transport tier; individuation disputes are adjudicated with
`Realization.Interpreted.Hom`, whose root-independent context translation blocks
re-encoding the source index in the target context. -/
structure Hom (S : Realization R₁ C₁ F) (T : Realization R₂ C₂ F) where
  /-- `onRoot` translates indices, and its non-injectivity is individuation
  coarsening. -/
  onRoot : R₁ → R₂
  /-- `onCtx` translates contexts. -/
  onCtx : R₁ → C₁ → C₂
  /-- Realization is preserved. -/
  realize_eq : ∀ r c, S.realize r c = T.realize (onRoot r) (onCtx r c)

/-- The identity hom leaves indices and contexts unchanged. -/
def Hom.id (S : Realization R Ctx F) : Hom S S :=
  ⟨fun r => r, fun _ c => c, fun _ _ => rfl⟩

/-- Homs compose, so coarsenings chain (morph-level to lexeme-level to
√-level). -/
def Hom.comp {S₁ : Realization R₁ C₁ F} {S₂ : Realization R₂ C₂ F}
    {S₃ : Realization R₃ C₃ F} (g : Hom S₂ S₃) (f : Hom S₁ S₂) : Hom S₁ S₃ :=
  ⟨fun r => g.onRoot (f.onRoot r),
   fun r c => g.onCtx (f.onRoot r) (f.onCtx r c),
   fun r c => (f.realize_eq r c).trans
     (g.realize_eq (f.onRoot r) (f.onCtx r c))⟩

theorem Hom.isLicensed {S : Realization R₁ C₁ F} {T : Realization R₂ C₂ F}
    (φ : Hom S T) {r : R₁} {c : C₁} (h : S.IsLicensed r c) :
    T.IsLicensed (φ.onRoot r) (φ.onCtx r c) := by
  obtain ⟨f, hf⟩ := h
  exact ⟨f, φ.realize_eq r c ▸ hf⟩

/-- Homs preserve realization, so merging indices can only grow allomorph
sets. -/
theorem Hom.realizes {S : Realization R₁ C₁ F} {T : Realization R₂ C₂ F}
    (φ : Hom S T) {r : R₁} {f : F} (h : S.Realizes r f) :
    T.Realizes (φ.onRoot r) f := by
  obtain ⟨c, hc⟩ := h
  exact ⟨φ.onCtx r c, φ.realize_eq r c ▸ hc⟩

end Hom

end Realization

/-- An interpreted realization adds a contextual interpretation to a
realization, the two-map extension of [marantz-1997], in which spellout is
List 2 and `interp` is List 3, allosemy (`DistributedMorphology/Allosemy.lean`).
A [borer-2013]-style system stays a bare `Realization`; a lexicalist lexeme is
an `Interpreted` system whose interpretation is `IsIntrinsic`. -/
structure Realization.Interpreted (R Ctx F M : Type*) extends
    Realization R Ctx F where
  /-- `interp r c` is the set of readings of `r` in `c`, given by Encyclopedia
  access. -/
  interp : R → Ctx → Finset M

namespace Realization.Interpreted

variable (S : Interpreted R Ctx F M)

/-- `IsIntrinsic r` says `r` has one meaning in every context, the lexicalist
degenerate case. -/
def IsIntrinsic (r : R) : Prop := IsConstantIn S.interp r

/-- `IsAllosemous r` says `r` has two distinct meanings, DM allosemy, the
failure of intrinsic meaning. -/
def IsAllosemous (r : R) : Prop := IsVariantIn S.interp r

theorem not_isIntrinsic_of_isAllosemous {r : R} (h : S.IsAllosemous r) :
    ¬ S.IsIntrinsic r :=
  not_isConstantIn_of_isVariantIn h

instance [Fintype Ctx] [DecidableEq M] (r : R) : Decidable (S.IsIntrinsic r) :=
  inferInstanceAs (Decidable (∀ c c' : Ctx,
    ∀ x ∈ S.interp r c, ∀ x' ∈ S.interp r c', x = x'))

instance [Fintype Ctx] [DecidableEq M] (r : R) :
    Decidable (S.IsAllosemous r) :=
  inferInstanceAs (Decidable (∃ c c',
    ∃ x ∈ S.interp r c, ∃ x' ∈ S.interp r c', x ≠ x'))

section Hom

variable {R₁ C₁ R₂ C₂ : Type*}

/-- A strict hom, the tier on which individuation disputes are stated,
translates contexts independently of the root, so that the target context
cannot re-encode the source index, and preserves interpretation alongside
spellout. -/
structure Hom (S : Interpreted R₁ C₁ F M) (T : Interpreted R₂ C₂ F M) where
  /-- `onRoot` translates indices. -/
  onRoot : R₁ → R₂
  /-- `onCtx` translates contexts independently of the root. -/
  onCtx : C₁ → C₂
  /-- Realization is preserved. -/
  realize_eq : ∀ r c, S.realize r c = T.realize (onRoot r) (onCtx c)
  /-- Interpretation is preserved. -/
  interp_eq : ∀ r c, S.interp r c = T.interp (onRoot r) (onCtx c)

/-- A strict hom is in particular a realization hom. -/
def Hom.toRealizationHom {S : Interpreted R₁ C₁ F M} {T : Interpreted R₂ C₂ F M}
    (φ : Hom S T) : Realization.Hom S.toRealization T.toRealization :=
  ⟨φ.onRoot, fun _ c => φ.onCtx c, φ.realize_eq⟩

theorem Hom.interp_eq_of_onRoot_eq {S : Interpreted R₁ C₁ F M}
    {T : Interpreted R₂ C₂ F M} (φ : Hom S T) {r r' : R₁}
    (h : φ.onRoot r = φ.onRoot r') (c : C₁) :
    S.interp r c = S.interp r' c := by
  rw [φ.interp_eq r c, φ.interp_eq r' c, h]

theorem Hom.realize_eq_of_onRoot_eq {S : Interpreted R₁ C₁ F M}
    {T : Interpreted R₂ C₂ F M} (φ : Hom S T) {r r' : R₁}
    (h : φ.onRoot r = φ.onRoot r') (c : C₁) :
    S.realize r c = S.realize r' c := by
  rw [φ.realize_eq r c, φ.realize_eq r' c, h]

/-- At the lax tier, a hom *includes* realization and interpretation rather
than matching them. Where a strict `Hom` merger asserts identity, a lax merger
asserts subsumption, so that each source index's forms and readings are among
its image's, as when a lexeme's listed properties are among its root's
Encyclopedia entry ([arad-2005]). Pattern-bound lexemes lax-merge into a total
root without ever strict-merging. -/
structure LaxHom (S : Interpreted R₁ C₁ F M) (T : Interpreted R₂ C₂ F M) where
  /-- `onRoot` translates indices. -/
  onRoot : R₁ → R₂
  /-- `onCtx` translates contexts independently of the root. -/
  onCtx : C₁ → C₂
  /-- Realizations are included. -/
  realize_sub : ∀ r c, S.realize r c ⊆ T.realize (onRoot r) (onCtx c)
  /-- Interpretations are included. -/
  interp_sub : ∀ r c, S.interp r c ⊆ T.interp (onRoot r) (onCtx c)

/-- A strict hom is in particular lax. -/
def Hom.toLaxHom {S : Interpreted R₁ C₁ F M} {T : Interpreted R₂ C₂ F M}
    (φ : Hom S T) : LaxHom S T :=
  ⟨φ.onRoot, φ.onCtx, fun r c => (φ.realize_eq r c).le,
   fun r c => (φ.interp_eq r c).le⟩

/-- Lax homs compose. -/
def LaxHom.comp {R₃ C₃ : Type*} {S₁ : Interpreted R₁ C₁ F M}
    {S₂ : Interpreted R₂ C₂ F M} {S₃ : Interpreted R₃ C₃ F M}
    (g : LaxHom S₂ S₃) (f : LaxHom S₁ S₂) : LaxHom S₁ S₃ :=
  ⟨fun r => g.onRoot (f.onRoot r), fun c => g.onCtx (f.onCtx c),
   fun r c =>
     (f.realize_sub r c).trans (g.realize_sub (f.onRoot r) (f.onCtx c)),
   fun r c =>
     (f.interp_sub r c).trans (g.interp_sub (f.onRoot r) (f.onCtx c))⟩

end Hom

/-- `ProfileEq r r'` says `r` and `r'` are contextwise indistinguishable, with
equal realization and interpretation profiles. -/
def ProfileEq (r r' : R) : Prop :=
  (∀ c, S.realize r c = S.realize r' c) ∧ (∀ c, S.interp r c = S.interp r' c)

/-- `profileSetoid` is profile equality as a setoid. -/
def profileSetoid : Setoid R where
  r := S.ProfileEq
  iseqv :=
    ⟨fun _ => ⟨fun _ => rfl, fun _ => rfl⟩,
     fun h => ⟨fun c => (h.1 c).symm, fun c => (h.2 c).symm⟩,
     fun h h' => ⟨fun c => (h.1 c).trans (h'.1 c),
                  fun c => (h.2 c).trans (h'.2 c)⟩⟩

/-- The reduced presentation takes its indices to be
realization-and-interpretation profiles. Every system presents its reduction;
the strict hom tier is change of presentation, and only the lax tier merges
beyond profiles. -/
def reduce : Interpreted (Quotient S.profileSetoid) Ctx F M where
  realize := Quotient.lift S.realize (fun _ _ h => funext h.1)
  interp := Quotient.lift S.interp (fun _ _ h => funext h.2)

/-- Reduction is a strict hom, so passing to profiles loses nothing. -/
def reduceHom : Hom S S.reduce :=
  ⟨Quotient.mk S.profileSetoid, id, fun _ _ => rfl, fun _ _ => rfl⟩

/-- Mergers along any strict hom refine profile equality, so `reduce` merges
as much as the strict tier ever can. Mergers beyond profiles, such as the
*hammer* carvings or pattern-bound lexemes into an [arad-2005] root, are
necessarily lax. -/
theorem Hom.profileEq_of_onRoot_eq {R₂ C₂ : Type*}
    {T : Interpreted R₂ C₂ F M} (φ : Hom S T) {r r' : R}
    (h : φ.onRoot r = φ.onRoot r') : S.ProfileEq r r' :=
  ⟨fun c => φ.realize_eq_of_onRoot_eq h c,
   fun c => φ.interp_eq_of_onRoot_eq h c⟩

end Realization.Interpreted

end Morphology
