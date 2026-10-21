module

public import Linglib.Semantics.Reference.Iota
public import Linglib.Semantics.Mereology
public import Linglib.Syntax.Category.Determiner.Basic
public import Linglib.Semantics.Presupposition.PhiFeatures
public import Mathlib.Basic.Rel
public import Linglib.Semantics.Genericity.MeaningPreservation
public import Linglib.Fragments.English.Determiners
public import Linglib.Fragments.German.Determiners
public import Linglib.Fragments.Mandarin.Determiners
public import Linglib.Fragments.Thai.Determiners
public import Linglib.Fragments.Shan.Determiners
public import Studies.Jenks2018

/-!
# Moroney (2021): definiteness and quantification in Shan

Moroney shows that Shan (Southwestern Tai) bare nouns express both unique and anaphoric
definiteness, instantiating an unmarked cell that Jenks's definiteness typology had no slot for.
Because Shan has no articles, no covert type-shift is blocked — ι, ι^x and ∩ are all available to
bare nouns — while the optional demonstratives *nâj/nân* only add spatial content. The cell is
derived from `Shan.Determiners.inventory`, the bare-noun readings as the shifts the inventory leaves
unblocked that are maximal under Dayal's Meaning Preservation, her (79), and the refutation is
stated against `Jenks2018.attested`.

Her comparison of Shan and English bare nouns (Table 2.3) finds them alike on the low-scope
existential, kind and generic readings, alike in lacking a high-scope existential, and different
only on the definite reading; that difference is derived here (`shan_iota_english_none`) rather than
tabulated. On the mass/count side she adopts Deal's generalized homogeneity — a predicate is
g-homogeneous when it is cumulative and, among other options, lacks minimal parts — and argues that
Shan count nouns, like English *furniture*, are cumulative but have identifiable atomic parts
(`maa_cumulative_not_divisive`). The demonstratives are the definite with the referent's closeness
to the speaker added: *nâj* presupposes a unique `P` in the situation and refers to it if it is
close (`demDenotation`, her (147)–(148)).

## Implementation notes

Moroney leaves close.to.speaker and far.from.speaker primitive. Here a demonstrative's spatial
content is the vicinity of a referent whose participants form one of its participant sets, as in
Harbour's account of spatial deixis: *nâj* covers the sets containing the speaker and *nân* the
others, so close.to.speaker is the vicinity of a referent including the speaker
(`mem_image_naj_iff`) and far.from.speaker the vicinity of one excluding the speaker
(`mem_image_nan_iff`). Where she treats far.from.speaker as the opposite of close.to.speaker, the
two vicinities may overlap here, as when the addressee stands by the speaker.

## References

* [moroney-2021]
* [dayal-2004], [deal-2017], [harbour-2016], [jenks-2018], [schwarz-2013]
-/

@[expose] public section

namespace Moroney2021

open Reference
open Genericity
open Mereology (CUM)
open scoped SetRel

/-! ### Type-shift selection -/

/-- With a non-kind predicate a Shan bare noun type-shifts by ι, the definite reading, while an
English bare singular has no shift available at all, since *the* blocks ι and ι^x, *a* blocks ∃,
and ∩ is undefined for a singular count noun. -/
theorem shan_iota_english_none :
    MaximalFor (Shan.Determiners.inventory.Available False) (· ≠ .exists) .iota ∧
      ∀ τ, ¬ English.Determiners.inventory.Available False τ := by
  decide

/-- With a kind-compatible predicate ∩, ι and ι^x are all maximal, which is the kind and definite
ambiguity of Shan bare nouns. -/
theorem shan_kind_ambiguity :
    MaximalFor (Shan.Determiners.inventory.Available True) (· ≠ .exists) .down ∧
      MaximalFor (Shan.Determiners.inventory.Available True) (· ≠ .exists) .iota ∧
      MaximalFor (Shan.Determiners.inventory.Available True) (· ≠ .exists) .iotaAnaphoric := by
  decide

/-- Shan blocks no ι^x, so bare nouns reach anaphoric definiteness; Thai's demonstrative marks
familiarity and blocks it. -/
theorem shan_thai_anaphoric_contrast :
    Shan.Determiners.inventory.Available False .iotaAnaphoric ∧
      ¬ Thai.Determiners.inventory.Available False .iotaAnaphoric := by
  decide

/-- Under Meaning Preservation ι outranks ∃, which is available to a Shan bare noun but never
selected beside ι, so Shan bare nouns default to definite or kind readings and the existential
reading arises only through existential closure at vP, whence the missing high-scope
existential. -/
theorem shan_exists_is_last_resort :
    Shan.Determiners.inventory.Available False .exists ∧
      ¬ MaximalFor (Shan.Determiners.inventory.Available False) (· ≠ .exists) .exists := by
  decide

/-! ### The typology, derived per language -/

/-- Each language's marking strategy, computed by `Determiner.Inventory.markingStrategy`
from its declared inventory: the four languages fill all four cells of the revised
typology. -/
theorem derive_all_languages :
    English.Determiners.inventory.markingStrategy = .generallyMarked ∧
      German.Determiners.inventory.markingStrategy = .bipartite ∧
      Thai.Determiners.inventory.markingStrategy = .markedAnaphoric ∧
      Shan.Determiners.inventory.markingStrategy = .unmarked :=
  ⟨English.Determiners.marking, German.Determiners.marking, Thai.Determiners.marking,
    Shan.Determiners.marking⟩

/-- The [schwarz-2013]-style article-type projection of the same inventories. -/
theorem derive_article_types :
    English.Determiners.inventory.articleType = .weakOnly ∧
      German.Determiners.inventory.articleType = .weakAndStrong ∧
      Thai.Determiners.inventory.articleType = .weakOnly ∧
      Shan.Determiners.inventory.articleType = .articleless := by
  decide

/-- `ArticleType` is lossy where `MarkingStrategy` is not, since English and Mandarin differ in
strategy yet collapse to the same article type. -/
theorem articleType_lossy :
    English.Determiners.inventory.markingStrategy ≠
        Mandarin.Determiners.inventory.markingStrategy ∧
      English.Determiners.inventory.articleType = Mandarin.Determiners.inventory.articleType := by
  decide

/-- Shan has no determiner realizing anaphoric definiteness, yet expresses it — through bare
nouns (unblocked ι^x) and the optional demonstratives, which it does realize. -/
theorem shan_anaphoric_without_article :
    ¬ Shan.Determiners.inventory.Realizes .anaphoric ∧
      Shan.Determiners.inventory.Realizes .demonstrative := by
  constructor <;> decide

/-- English realizes anaphoric definiteness through syncretic *the* and German through its
dedicated strong article. -/
theorem english_german_anaphoric_realized :
    English.Determiners.inventory.Realizes .anaphoric ∧
      German.Determiners.inventory.Realizes .anaphoric := by
  decide

/-- Shan's derived strategy, the unmarked type, is none that the languages of [jenks-2018]'s
Table 2 attest. -/
theorem shan_refutes_jenks_typology :
    Shan.Determiners.inventory.markingStrategy ∉ Jenks2018.attested := by
  rw [Shan.Determiners.marking]; decide

/-! ### Shan count nouns are cumulative but not homogeneous -/

/-- `P` lacks minimal parts, the first clause of [deal-2017]'s generalized homogeneity, when
every `P`-element has a proper `P`-part. -/
def LacksMinimalParts {α : Type*} [Preorder α] (P : α → Prop) : Prop :=
  ∀ x, P x → ∃ y < x, P y

/-- The dog-pluralities over two dogs are the nonempty subsets. -/
abbrev isDog (x : Finset (Fin 2)) : Prop := x.Nonempty

/-- Shan *mǎa* 'dog' patterns with English *furniture*. The sum of dogs is dogs, but the individual
dogs are minimal, so the predicate is cumulative without being homogeneous. -/
theorem maa_cumulative_not_divisive : CUM isDog ∧ ¬ LacksMinimalParts isDog := by
  refine ⟨fun _ hx _ _ ↦ hx.mono Finset.subset_union_left, fun h ↦ ?_⟩
  obtain ⟨y, hy, hne⟩ := h {0} (Finset.singleton_nonempty 0)
  exact hne.ne_empty ((Finset.subset_singleton_iff.1 hy.le).resolve_right hy.ne)

/-! ### Demonstratives add spatial content -/

/-- The bare definite description denotes the unique referent satisfying the restrictor, the
uniqueness reading available to Shan bare nouns. -/
noncomputable def bareDefinite {E : Type*} (restrictor : E → Prop) : Option E :=
  iota restrictor

section Demonstrative

variable {W E P T : Type*} [PartialOrder E] (c : Reference.Context W E P T) (χ : SetRel E E)

/-- The demonstrative of Moroney's (147)–(148) denotes the unique referent satisfying the restrictor
and lying in its deictic domain, `ιx[P(x) ∧ close.to.speaker(x)]` for *nâj*. -/
noncomputable def demDenotation (d : DemonstrativeDeterminer) (restrictor : E → Prop) :
    Option E :=
  iota fun x ↦ restrictor x ∧ x ∈ χ.image (c.participants ⁻¹' d.deixis)

/-- The demonstrative refers to the bare definite's referent whenever that referent lies in the
demonstrative's deictic domain, so *nâj/nân* are optional wherever the bare noun already
provides the definite reading. -/
theorem demDenotation_eq_some_of_bareDefinite {d : DemonstrativeDeterminer}
    {restrictor : E → Prop} {e : E} (h : bareDefinite restrictor = some e)
    (hs : e ∈ χ.image (c.participants ⁻¹' d.deixis)) :
    demDenotation c χ d restrictor = some e := by
  rw [bareDefinite, iota_eq_some_iff] at h
  exact (iota_eq_some_iff _).2 ⟨⟨h.1, hs⟩, fun x hx ↦ h.2 x hx.1⟩

/-- *nâj*'s close.to.speaker of (147) is the vicinity of a referent including the speaker. -/
theorem mem_image_naj_iff {x : E} :
    x ∈ χ.image (c.participants ⁻¹' Shan.Determiners.naj.deixis) ↔
      ∃ y, c.agent ≤ y ∧ y ~[χ] x := by
  simp [Shan.Determiners.naj, SetRel.image, Person.participants_mem_participantSets_first]

/-- *nân*'s far.from.speaker of (148) is the vicinity of a referent excluding the speaker. -/
theorem mem_image_nan_iff {x : E} :
    x ∈ χ.image (c.participants ⁻¹' Shan.Determiners.nan.deixis) ↔
      ∃ y, ¬ c.agent ≤ y ∧ y ~[χ] x := by
  simp [Shan.Determiners.nan, SetRel.image, Person.participants_mem_participantSets_first]

end Demonstrative

end Moroney2021
