module

public import Linglib.Semantics.Reference.Description
public import Linglib.Semantics.Mereology
public import Linglib.Syntax.Category.Determiner.Basic
public import Linglib.Semantics.Presupposition.PhiFeatures
public import Mathlib.Basic.Rel
public import Linglib.Semantics.Genericity.MeaningPreservation
public import Linglib.Fragments.English.Determiners
public import Linglib.Fragments.German.Determiners
public import Linglib.Fragments.Cantonese.Determiners
public import Linglib.Fragments.Thai.Determiners
public import Linglib.Fragments.Shan.Determiners
public import Studies.Jenks2018
public import Studies.Schwarz2013

/-!
# Moroney (2021): definiteness and quantification in Shan

Moroney shows that Shan (Southwestern Tai) bare nouns express both unique and anaphoric
definiteness. Shan has no articles, and its demonstratives block no covert type shift, so ι, ι^x and
∩ are all available to bare nouns, which take those maximal under Dayal's Meaning Preservation. A
presupposition is marked where the Blocking Principle removes the covert shift that would express
it. Shan marks neither and so [falls in none of the four types](##shan_refutes_jenks_typology) of
Jenks's typology, which an unmarked type completes. Jenks's own principles fare worse: Index! takes
Shan's demonstratives for the indexed forms it calls for and so [excludes Shan's anaphoric bare
nouns](##jenks_excludes_shan_bare_anaphora). Neither account tells Shan from Thai, [to which each
assigns Shan's type](##thai_shan_same_type), though Thai's demonstrative is obligatory and Shan's
optional.

The optional demonstratives *nâj* 'this' and *nân* 'that' presuppose what the bare definite does,
a unique referent in the situation, and [refer to it when it lies in their deictic
domain](##demDenotation_eq_some_iff), near the speaker for *nâj* and away from the speaker for
*nân*. That spatial content is why a demonstrative [is not the
definite](##demDenotation_eq_bare_iff) and so blocks none of the bare noun's readings.

Shan and English bare nouns are alike on the low-scope existential, kind and generic readings,
alike in lacking a high-scope existential, and different only on the definite reading, which is
derived here (`shan_iota_english_none`). On the mass/count side Moroney adopts Deal's generalized
homogeneity, under which a predicate is g-homogeneous when it is cumulative and, among other
options, lacks minimal parts, and argues that Shan count nouns, like English *furniture*, are
cumulative but have identifiable atomic parts (`maa_cumulative_not_divisive`).

## Implementation notes

* Moroney leaves close.to.speaker and far.from.speaker primitive. Here a demonstrative's spatial
  content is the vicinity of a referent whose participants form one of its participant sets, as in
  Harbour's account of spatial deixis: *nâj* covers the sets containing the speaker and *nân* the
  others, so close.to.speaker is the vicinity of a referent including the speaker
  (`mem_image_naj_iff`) and far.from.speaker the vicinity of one excluding the speaker
  (`mem_image_nan_iff`). Where she treats far.from.speaker as the opposite of close.to.speaker, the
  two vicinities may overlap here, as when the addressee stands by the speaker.
* Moroney's Lakhota is Schwarz's tentative construal of *kiŋ* as a weak article only. The Lakhota
  fragment also gives *kiŋ* its anaphoric uses, so by the fragment Lakhota is generally marked.
* A determiner blocks a shift when it denotes what the shift denotes, the theory layer's
  `Determiner.Entry.Lexicalizes`, so a demonstrative, whose deictic presupposition can fail where
  the definite's does not, blocks nothing.
* No fragment records a demonstrative as obligatory, obligatoriness being each account's
  prediction. Under Index! Mandarin and Thai are marked anaphoric, as Jenks reports; under the
  Blocking Principle both are unmarked, as Moroney concludes once an economy principle chooses
  between the bare noun and the demonstrative, a principle not modelled here.

## TODO

* The judgments on bare nouns and demonstratives in each definite use, as data. The bare noun is
  licit in every use; the demonstrative with a classifier is not licit for a referent unique in
  the situation, which the non-uniqueness Moroney ascribes to that phrase would derive.
* The kind-level predictions for each type, which turn on number marking.

## References

* [moroney-2021]
* [dayal-2004], [deal-2017], [harbour-2016], [jenks-2018], [schwarz-2013]
-/

@[expose] public section

namespace Moroney2021

open Determiner Determiner.Inventory
open Jenks2018 (IsBipartite IsMarkedAnaphoric IsGenerallyMarked IsMarkedUnique)
open Genericity
open Mereology (CUM)
open scoped SetRel Denotes

/-! ### Type-shift selection -/

theorem shan_iota_english_none :
    MaximalFor (Shan.Determiners.inventory.Available .general False) (· ≠ .exists) .iota ∧
      ∀ num down, ¬ English.Determiners.inventory.Available num down .iota :=
  ⟨by decide, fun _ _ h ↦ h.2 ((blocks_iff_lexicalizes (by decide)).2 (by decide))⟩

theorem shan_kind_ambiguity :
    MaximalFor (Shan.Determiners.inventory.Available .general True) (· ≠ .exists) .down ∧
      MaximalFor (Shan.Determiners.inventory.Available .general True) (· ≠ .exists) .iota ∧
      MaximalFor (Shan.Determiners.inventory.Available .general True) (· ≠ .exists)
        .iotaAnaphoric := by
  decide

theorem shan_exists_is_last_resort :
    Shan.Determiners.inventory.Available .general False .exists ∧
      ¬ MaximalFor (Shan.Determiners.inventory.Available .general False) (· ≠ .exists) .exists := by
  decide

/-! ### The revised typology -/

open DefiniteDescription (Strength)

/-- In Moroney's analysis a presupposition is marked when a determiner lexicalizes the covert shift
that would express it, ι for uniqueness and ι^x for familiarity, so that the Blocking Principle
removes it. -/
def Marked (ds : Inventory) : Strength → Prop
  | .uniqueness => ds.Lexicalizes .iota
  | .familiarity => ds.Lexicalizes .iotaAnaphoric

instance (ds : Inventory) : DecidablePred (Marked ds) := fun p ↦ by
  cases p <;> unfold Marked <;> infer_instance

/-- An unmarked inventory marks neither presupposition. -/
def IsUnmarked (M : Strength → Prop) : Prop := ¬ M .uniqueness ∧ ¬ M .familiarity

/-- Shan marks neither presupposition and so falls in none of the four types of Jenks's typology
(Table 4.1). -/
theorem shan_refutes_jenks_typology :
    ¬ (IsGenerallyMarked (Marked Shan.Determiners.inventory) Shan.Determiners.inventory ∨
      IsBipartite (Marked Shan.Determiners.inventory) Shan.Determiners.inventory ∨
      IsMarkedUnique (Marked Shan.Determiners.inventory) ∨
      IsMarkedAnaphoric (Marked Shan.Determiners.inventory)) := by
  simp only [IsBipartite, IsMarkedAnaphoric, IsGenerallyMarked, IsMarkedUnique]
  decide

/-- Under Jenks's principles Shan's demonstratives supply the index that Index! calls for, so Shan
is marked anaphoric and its anaphoric bare nouns, as in (489)–(491), are excluded. -/
theorem jenks_excludes_shan_bare_anaphora :
    IsMarkedAnaphoric (Jenks2018.Marked Shan.Determiners.inventory) ∧
      ¬ Jenks2018.BareLicit Shan.Determiners.inventory .anaphoric .none := by
  simp only [IsMarkedAnaphoric]
  decide

/-- Each account gives Thai Shan's type, unmarked under the Blocking Principle and marked anaphoric
under Index!, though Jenks reports Thai's demonstrative obligatory in the anaphoric uses and Moroney
finds Shan's optional: the contrast lies outside the inventories (p. 193). -/
theorem thai_shan_same_type :
    IsUnmarked (Marked Thai.Determiners.inventory) ∧
      IsUnmarked (Marked Shan.Determiners.inventory) ∧
      IsMarkedAnaphoric (Jenks2018.Marked Thai.Determiners.inventory) ∧
      IsMarkedAnaphoric (Jenks2018.Marked Shan.Determiners.inventory) := by
  simp only [IsUnmarked, IsMarkedAnaphoric]
  decide

-- Table 4.5
theorem typology_complete (M : Strength → Prop) (ds : Inventory) :
    IsGenerallyMarked M ds ∨ IsBipartite M ds ∨ IsMarkedUnique M ∨ IsMarkedAnaphoric M ∨
      IsUnmarked M := by
  simp only [IsGenerallyMarked, IsBipartite, IsMarkedUnique, IsMarkedAnaphoric, IsUnmarked]
  tauto

-- Table 4.5; Hausa, both marked with different forms, p. 186
theorem table4_5 :
    IsGenerallyMarked (Marked Cantonese.Determiners.inventory) Cantonese.Determiners.inventory ∧
      IsGenerallyMarked (Marked English.Determiners.inventory) English.Determiners.inventory ∧
      IsBipartite (Marked German.Determiners.inventory) German.Determiners.inventory ∧
      IsBipartite (Marked Schwarz2013.lakhotaWeakStrongConstrual)
        Schwarz2013.lakhotaWeakStrongConstrual ∧
      IsBipartite (Marked Hausa.Determiners.inventory) Hausa.Determiners.inventory ∧
      IsMarkedAnaphoric (Marked Akan.Determiners.inventory) ∧
      IsMarkedAnaphoric (Marked MauritianCreole.Determiners.inventory) ∧
      IsUnmarked (Marked Shan.Determiners.inventory) := by
  simp only [IsGenerallyMarked, IsBipartite, IsMarkedAnaphoric, IsUnmarked]
  decide

theorem shan_anaphoric_without_article :
    ¬ Shan.Determiners.inventory.Realizes .anaphoric ∧
      Shan.Determiners.inventory.Realizes .demonstrative := by
  constructor <;> decide

/-! ### Definite shifts by type (Tables 4.7 to 4.9) -/

section Shifts

variable {ds : Inventory} {num : Number} {down : Prop}

-- Table 4.9
theorem available_of_isUnmarked (h : IsUnmarked (Marked ds)) :
    ds.Available num down .iota ∧ ds.Available num down .iotaAnaphoric :=
  ⟨⟨nofun, fun hb ↦ h.1 hb.lexicalizes⟩, ⟨nofun, fun hb ↦ h.2 hb.lexicalizes⟩⟩

variable (hn : ∀ e ∈ ds, e.numberRestriction = none)
include hn

-- Table 4.8
theorem available_of_isMarkedAnaphoric (h : IsMarkedAnaphoric (Marked ds)) :
    ds.Available num down .iota ∧ ¬ ds.Available num down .iotaAnaphoric :=
  ⟨⟨nofun, fun hb ↦ h.1 hb.lexicalizes⟩,
    fun h' ↦ h'.2 ((blocks_iff_lexicalizes fun e he _ ↦ hn e he).2 h.2)⟩

-- Table 4.7
theorem not_available_of_marked (hu : Marked ds .uniqueness) (hf : Marked ds .familiarity) :
    ¬ ds.Available num down .iota ∧ ¬ ds.Available num down .iotaAnaphoric :=
  ⟨fun h ↦ h.2 ((blocks_iff_lexicalizes fun e he _ ↦ hn e he).2 hu),
    fun h ↦ h.2 ((blocks_iff_lexicalizes fun e he _ ↦ hn e he).2 hf)⟩

omit hn in
theorem akan_iota_not_iotaAnaphoric :
    Akan.Determiners.inventory.Available .general False .iota ∧
      ¬ Akan.Determiners.inventory.Available .general False .iotaAnaphoric :=
  available_of_isMarkedAnaphoric (by decide) (by simp only [IsMarkedAnaphoric]; decide)

end Shifts

/-! ### Shan count nouns are cumulative but not homogeneous -/

/-- `P` lacks minimal parts, the first clause of [deal-2017]'s generalized homogeneity, when
every `P`-element has a proper `P`-part. -/
def LacksMinimalParts {α : Type*} [Preorder α] (P : α → Prop) : Prop :=
  ∀ x, P x → ∃ y < x, P y

/-- The dog-pluralities over two dogs are the nonempty subsets. -/
abbrev isDog (x : Finset (Fin 2)) : Prop := x.Nonempty

theorem maa_cumulative_not_divisive : CUM isDog ∧ ¬ LacksMinimalParts isDog := by
  refine ⟨fun _ hx _ _ ↦ hx.mono Finset.subset_union_left, fun h ↦ ?_⟩
  obtain ⟨y, hy, hne⟩ := h {0} (Finset.singleton_nonempty 0)
  exact hne.ne_empty ((Finset.subset_singleton_iff.1 hy.le).resolve_right hy.ne)

/-! ### Demonstratives add spatial content -/

section Demonstrative

open DefiniteDescription (Restrictor bare)

variable {W E P T : Type} [PartialOrder E] (c : Kaplan.Context W E P T) (χ : SetRel E E)
  (d : DemonstrativeDeterminer)

/-- The demonstrative of (147)–(148) presupposes, as the bare definite does, a unique `P` in the
situation, and denotes the `P` in its deictic domain, `ιx[P(x) ∧ close.to.speaker(x)]` for
*nâj*. -/
noncomputable def demDenotation (R : Restrictor E W) (g : Assignment E) (s : W) : Option E :=
  (⟦bare R⟧ g s).bind fun _ ↦ iota fun x ↦ R g s x ∧ x ∈ χ.image (c.participants ⁻¹' d.deixis)

/-- A demonstrative refers to the bare noun's referent when that referent lies in its deictic
domain. -/
theorem demDenotation_eq_some_iff {R : Restrictor E W} {g : Assignment E} {s : W} {x : E} :
    demDenotation c χ d R g s = some x ↔
      ⟦bare R⟧ g s = some x ∧ x ∈ χ.image (c.participants ⁻¹' d.deixis) := by
  simp only [demDenotation, Option.bind_eq_some_iff, DefiniteDescription.denote_bare_eq_some_iff,
    iota_eq_some_iff]
  constructor
  · rintro ⟨y, ⟨-, hy⟩, ⟨hx, hxd⟩, -⟩
    exact ⟨⟨hx, fun z hz ↦ (hy z hz).trans (hy x hx).symm⟩, hxd⟩
  · rintro ⟨⟨hx, hu⟩, hxd⟩
    exact ⟨x, ⟨hx, hu⟩, ⟨hx, hxd⟩, fun z hz ↦ hu z hz.1⟩

/-- A demonstrative agrees with the bare definite wherever that is defined exactly when its deictic
domain holds every referent, so a demonstrative with spatial content is not the definite and
blocks no definite reading of the bare noun (p. 62). -/
theorem demDenotation_eq_bare_iff (g : Assignment E) (s : W) :
    (∀ R : Restrictor E W, (⟦bare R⟧ g s).isSome → demDenotation c χ d R g s = ⟦bare R⟧ g s) ↔
      ∀ x, x ∈ χ.image (c.participants ⁻¹' d.deixis) := by
  refine ⟨fun h x ↦ ?_, fun h R hR ↦ ?_⟩
  · have hb : ⟦bare fun (_ : Assignment E) (_ : W) y ↦ y = x⟧ g s = some x :=
      (DefiniteDescription.denote_bare_eq_some_iff _ g s).2 ⟨rfl, fun _ ↦ id⟩
    exact ((demDenotation_eq_some_iff c χ d).1
      ((h _ (Option.isSome_iff_exists.2 ⟨x, hb⟩)).trans hb)).2
  · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hR
    rw [hx, demDenotation_eq_some_iff]
    exact ⟨hx, h x⟩

-- close.to.speaker, (147)
theorem mem_image_naj_iff {x : E} :
    x ∈ χ.image (c.participants ⁻¹' Shan.Determiners.naj.deixis) ↔
      ∃ y, c.agent ≤ y ∧ y ~[χ] x := by
  simp [Shan.Determiners.naj, SetRel.image, Person.participants_mem_participantSets_first]

-- far.from.speaker, (148)
theorem mem_image_nan_iff {x : E} :
    x ∈ χ.image (c.participants ⁻¹' Shan.Determiners.nan.deixis) ↔
      ∃ y, ¬ c.agent ≤ y ∧ y ~[χ] x := by
  simp [Shan.Determiners.nan, SetRel.image, Person.participants_mem_participantSets_first]

end Demonstrative

end Moroney2021
