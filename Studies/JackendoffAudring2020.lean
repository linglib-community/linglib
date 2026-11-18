/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Data.Examples.JackendoffAudring2020
public import Linglib.Data.Wordlist.JackendoffAudring2020
public import Linglib.Fragments.English.Phonology
public import Linglib.Fragments.German.Phonology
public import Linglib.Morphology.ConstructionMorphology.Pattern
public import Linglib.Morphology.ConstructionMorphology.Schema
public import Linglib.Phonology.Prosody.Syllable
public import Linglib.Logic.Nonmonotonic.Inheritance
public import Linglib.Core.Relation.ReflTransGen
public import Linglib.Morphology.Paradigm.Linkage
public import Linglib.Morphology.Paradigm.Morphome
public import Linglib.Core.Order.Flat
public import Studies.Audring2019
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.DeriveFintype

/-!
# Jackendoff and Audring (2020): The Texture of the Lexicon

This file formalizes the Relational Morphology of [jackendoff-audring-2020], in which
morphological motivation is shared structure recorded by nondirectional relational links
between fully specified lexical entries, not inheritance from an abstract base.

The words *assassin* and *assassinate* are the test. The second is built on the first in
phonology and the first on the second in semantics, so
[no acyclic inheritance hierarchy holds both demands](##assassin_cycle), though
[default inheritance itself computes as intended](##ostrich_overrides). A sister link holds
both: the two entries are one pattern, which
[coindexes each shared part and leaves each word a part of its own](##assassinPair_coindex_iff).
The same link between two schemas
[pairs the *-ism* noun of an ideology with the *-ist* noun of its adherents](##ismist_pairs_iff),
[whatever the base and the ideology](##ismist_pairs).

Ablaut is a sister link off the syllabic nucleus. The general schema
[pairs exactly the stems and pasts that are the same except at the nucleus](##ablaut_pairs_iff)
and [subsumes the *sing* ~ *sang* subschema](##ablaut_le_nucleusPair), whose pairs
[are nucleus contrasts](##contrast_of_nucleusPair). The cells that the German present-tense
schema serves, the second and third singular, [are a morphome](##spricht_morphome). Two lexemes
that share a pivot of morphosyntax and phonology without sharing a semantics
[inflect alike at every cell](##realize_eq_of_sameVerb). Structural Intersection is the meet:
the *-ish* schema [is the intersection of its three sisters](##ishSchema_body_eq_inf), is
[the most they have in common](##instantiates_ishSchema_iff), and
[absorbs a newly encountered sister](##ishSchema_inf_foolish).

## Implementation notes

* Lexical entries and schemas are slot-indexed descriptions over a flat carrier, a constant
  above `⊥` and a variable at `⊥`. A linked pair of words or of schemas is one
  `ConstructionMorphology.Pattern` over the positions of both, and a relational coindex is its
  coindexation. The containment of the semantics of *assassinate* in that of *assassin*, (41),
  is rendered as a shared slot.
* The variables of the linked *-ism* and *-ist* schemas range over all the material of the
  schemas, so the pattern does not restrict the base variable to bases.
* The zero exponence of the present and the infinitive of *walk*, (19), the double
  coindexation of Section 4.3, appears as a syncretism of the paradigm (`walk_syncretism`).
* The cycle theorem renders the paradox of Objection 10 through the well-foundedness of an
  inheritance hierarchy; the book argues from the above-and-below paradox and makes no
  well-foundedness claim.
* The syllables, the *-ish* adjectives and the toponyms are the CLDF forms of
  `Data/Wordlist/JackendoffAudring2020.json`. An adjective or a toponym is read one morph per
  slot by `CLDF.Wordlist.Form.morphSlots`. A syllable is read through its language's
  transcription and split at its nucleus, so the slot before the nucleus also holds the *s* of
  *str-* and the *ʃ* of *spr-*, which core syllabification leaves outside the onset.
* The correspondence between a schema's variable coindices and the constant coindices of its
  instances, left unformalized in Section 4.13.2, is subsumption: a pattern subsumes a pair of
  words when the words fill its coindexed variables alike. A productive variable is one marked
  open over and above its attested fillers.

## References

* [jackendoff-audring-2020]
* [audring-2019]
* [booij-2010]
* [aronoff-1994]
* [spencer-2013]
* [albright-hayes-2003]
* [clements-1990]
-/

@[expose] public section

namespace JackendoffAudring2020

open Morphology ConstructionMorphology Pattern
open Phonology (Segment)

/-! ### Open and closed variables, (17) and (18)

The toponym patterns (17): a name and the type of a geographical feature, the name an open
variable and the feature type a closed one, whose fillers are learned pattern by pattern; in
(18d) *the* and *of* are constants. -/

/-- The pattern (18a) puts the name before the feature, with the name open and the feature
closed. -/
def toponymA : Schema (Fin 2) (Flat String) := ⟨fun _ ↦ ⊥, {0}, fun _ _ ↦ rfl⟩

/-- The pattern (18b) puts the feature before the name. -/
def toponymB : Schema (Fin 2) (Flat String) := ⟨fun _ ↦ ⊥, {1}, fun _ _ ↦ rfl⟩

/-- The pattern (18d), *the* feature *of* name, has two constants, a closed feature and an
open name. -/
def toponymD : Schema (Fin 4) (Flat String) :=
  ⟨![↑"the", ⊥, ↑"of", ⊥], {3}, by rintro _ rfl; rfl⟩

/-- `toponymsA` holds the stored toponyms of (17a). -/
def toponymsA : Set (Fin 2 → Flat String) :=
  {Wordlist.arrowheadLake.morphSlots, Wordlist.loonMountain.morphSlots,
    Wordlist.wissahickonCreek.morphSlots, Wordlist.laurelHill.morphSlots,
    Wordlist.sugarIsland.morphSlots}

/-- `toponymsB` holds the stored toponyms of (17b). -/
def toponymsB : Set (Fin 2 → Flat String) :=
  {Wordlist.mountEverest.morphSlots, Wordlist.lakeMichigan.morphSlots,
    Wordlist.capeCod.morphSlots}

/-- `toponymsD` holds the stored toponyms of (17d). -/
def toponymsD : Set (Fin 4 → Flat String) :=
  {Wordlist.bayOfFundy.morphSlots, Wordlist.gulfOfStLawrence.morphSlots,
    Wordlist.capeOfGoodHope.morphSlots, Wordlist.isleOfWight.morphSlots}

-- (18a)
theorem morrisMountain_generates :
    toponymA.Generates toponymsA Wordlist.morrisMountain.morphSlots :=
  ⟨fun i ↦ bot_le, fun i hi ↦ by
    fin_cases i
    · exact absurd (Set.mem_singleton _) hi.2
    · exact ⟨Wordlist.loonMountain.morphSlots, ⟨by simp [toponymsA], fun _ ↦ bot_le⟩, by decide⟩⟩

-- (18b)
theorem mountMorris_generates : toponymB.Generates toponymsB Wordlist.mountMorris.morphSlots :=
  ⟨fun i ↦ bot_le, fun i hi ↦ by
    fin_cases i
    · exact ⟨Wordlist.mountEverest.morphSlots, ⟨by simp [toponymsB], fun _ ↦ bot_le⟩, by decide⟩
    · exact absurd (Set.mem_singleton _) hi.2⟩

-- (18b)
theorem not_mountainMorris_generates :
    ¬ toponymB.Generates toponymsB ![↑"Mountain", ↑"Morris"] := by
  rintro ⟨-, h⟩
  obtain ⟨w, ⟨hw, -⟩, hw0⟩ := h 0 ⟨rfl, by simp [toponymB]⟩
  simp only [toponymsB, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  rcases hw with rfl | rfl | rfl <;> exact absurd hw0 (by decide)

-- (18d)
theorem not_mountOfHalle_generates :
    ¬ toponymD.Generates toponymsD ![↑"the", ↑"Mount", ↑"of", ↑"Halle"] := by
  rintro ⟨-, h⟩
  obtain ⟨w, ⟨hw, -⟩, hw1⟩ := h 1 ⟨rfl, by simp [toponymD]⟩
  simp only [toponymsD, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> exact absurd hw1 (by decide)

/-! ### Default inheritance and override, Figure 3.5

The taxonomy of Figure 3.5: birds fly by default, the ostrich overrides, and the canary
inherits flight. -/

/-- `Animal` has the nodes of Figure 3.5. -/
inductive Animal
  | animal
  | bird
  | fish
  | canary
  | ostrich
  deriving DecidableEq, Fintype

/-- In the taxonomy, birds and fish are animals, and canaries and ostriches are birds. -/
def Animal.parents : Animal → List Animal
  | .animal => []
  | .bird | .fish => [.animal]
  | .canary | .ostrich => [.bird]

instance : PartialOrder Animal :=
  partialOrderOfAcyclic (fun a b : Animal ↦ b ∈ a.parents) (by decide)

instance : DecidableLE Animal :=
  decidableLEOfCovers (covers := fun a b : Animal ↦ b ∈ a.parents) [.animal, .bird] (by decide)

/-- `flies` specifies flight locally, so that birds fly and the ostrich overrides. -/
def flies : Animal → Option Bool
  | .bird => some true
  | .ostrich => some false
  | _ => none

theorem ostrich_overrides :
    DefaultInheritance.inherited flies .ostrich = {false} ∧
      DefaultInheritance.inherited flies .canary = {true} :=
  ⟨DefaultInheritance.inherited_eq_singleton_of_eq_some rfl,
    DefaultInheritance.inherited_eq_singleton_of_isLeast (m := .bird) (by decide) rfl⟩

/-! ### Sister words -/

/-- The parts of the entries (41) are the shared phonology, the shared predicate MURDER, the
person that *assassin* adds and the affix that *assassinate* adds. -/
inductive Part
  | asasin
  | murder
  | person
  | ate
  deriving DecidableEq, Inhabited

/-- (41a): The entry of *assassin* is its phonology, the predicate it contains, and the person. -/
def assassin : Fin 3 → Flat Part := ![↑Part.asasin, ↑Part.murder, ↑Part.person]

/-- (41b): The entry of *assassinate* is its base, its affix, and its predicate. -/
def assassinate : Fin 3 → Flat Part := ![↑Part.asasin, ↑Part.ate, ↑Part.murder]

/-- (41): The two entries with their coindices are one pattern over the positions of both. -/
abbrev assassinPair : Pattern (Fin 3 ⊕ Fin 3) (Flat Part) :=
  ofItem (Sum.elim assassin assassinate)

/-- The sister link coindexes the phonology of *assassin* with the base of *assassinate* and the
predicate of one with the predicate of the other, and nothing else, so each word has a part
outside the link. -/
theorem assassinPair_coindex_iff {p q : Fin 3} :
    assassinPair.coindex (.inl p) (.inr q) ↔ p = 0 ∧ q = 0 ∨ p = 1 ∧ q = 2 := by
  decide +revert

/-- `Pair` has the two words as the nodes of an inheritance hierarchy. -/
inductive Pair
  | assassin
  | assassinate
  deriving DecidableEq

theorem assassin_cycle [PartialOrder Pair] (hphon : Pair.assassinate < .assassin)
    (hsem : Pair.assassin < .assassinate) : False :=
  hphon.asymm hsem

/-! ### Sister schemas -/

/-- The material of the schemas (47) over bases `B` and ideologies `I` is a base, an ideology,
the two affixes, and the relation ADHERENT. -/
inductive Atom (B I : Type*)
  | base (b : B)
  | ideology (i : I)
  | ism
  | ist
  | adherent

variable {B I : Type*}

instance : Nonempty (Atom B I) := ⟨.ism⟩

/-- (47): The *-ism* schema, a base, the affix and an ideology, and the *-ist* schema, a base,
the affix and ADHERENT of an ideology, are one pattern whose bases are coindexed (α) and whose
ideologies are coindexed (β). -/
abbrev ismist : Pattern (Fin 3 ⊕ Fin 4) (Flat (Atom B I)) :=
  .ofTerms (X := Fin 2)
    (Sum.elim ![.inr 0, .inl .ism, .inr 1] ![.inr 0, .inl .ist, .inl .adherent, .inr 1])

/-- `ismWord b i` is the *-ism* noun on base `b` denoting the ideology `i`. -/
def ismWord (b : B) (i : I) : Fin 3 → Atom B I := ![.base b, .ism, .ideology i]

/-- `istWord b i` is the *-ist* noun on base `b` denoting an adherent of `i`. -/
def istWord (b : B) (i : I) : Fin 4 → Atom B I := ![.base b, .ist, .adherent, .ideology i]

/-- The linked schemas pair an *-ism* noun with an *-ist* noun exactly when the two have the same
base and the same ideology. -/
theorem ismist_pairs_iff {p : Fin 3 → Atom B I} {q : Fin 4 → Atom B I} :
    ismist ≤ ofItem (Sum.elim (Flat.some ∘ p) (Flat.some ∘ q)) ↔
      ∃ x y, p = ![x, .ism, y] ∧ q = ![x, .ist, .adherent, y] := by
  refine ofTerms_sumElim_le_ofItem_iff.trans
    ⟨fun ⟨x, hp, hq⟩ ↦ ⟨x 0, x 1, ?_, ?_⟩, fun ⟨x, y, hp, hq⟩ ↦ ⟨![x, y], ?_, ?_⟩⟩ <;>
  · subst_vars
    funext i
    fin_cases i <;> rfl

theorem ismist_pairs (b : B) (i : I) :
    ismist ≤ ofItem (Sum.elim (Flat.some ∘ ismWord b i) (Flat.some ∘ istWord b i)) :=
  ismist_pairs_iff.2 ⟨_, _, rfl, rfl⟩

/-! ### Ablaut as a link off the nucleus -/

/-- A form read through a transcription as what precedes its nucleus, the nucleus and the coda,
or as `⊥` throughout if the transcription fails. -/
def syllable (transcribe : List String → Option (List Segment)) {C : Type*}
    (f : CLDF.Wordlist.Form C) : Fin 3 → Flat (List Segment) :=
  (transcribe f.segments).elim ⊥ fun w ↦
    ![↑(Prosody.nucleusSplit w).1, ↑(Prosody.nucleusSplit w).2.1, ↑(Prosody.nucleusSplit w).2.2]

theorem transcribe_ne_none :
    (∀ f ∈ [Wordlist.sing, Wordlist.sang, Wordlist.string, Wordlist.strung],
      English.Phonology.transcribe f.segments ≠ none) ∧
      ∀ f ∈ [Wordlist.sprech, Wordlist.sprich], German.Phonology.transcribe f.segments ≠ none := by
  decide

variable {σ : Type*}

/-- (25): The general ablaut schema is the stem and the past as one pattern that coindexes what
precedes the nucleus and coindexes the coda, with each nucleus a variable of its own. It is
also the phonological shape of the German present-tense schema (45). -/
abbrev ablaut : Pattern (Fin 3 ⊕ Fin 3) (Flat (List σ)) :=
  .ofTerms (X := Fin 4) (Sum.elim ![.inr 0, .inr 1, .inr 2] ![.inr 0, .inr 3, .inr 2])

/-- `nucleusPair v w` is the ablaut schema with the nucleus pinned to `v` in the stem and to `w`
in the past, the shape of the subschemas (26). -/
abbrev nucleusPair (v w : List σ) : Pattern (Fin 3 ⊕ Fin 3) (Flat (List σ)) :=
  .ofTerms (X := Fin 2) (Sum.elim ![.inr 0, .inl v, .inr 1] ![.inr 0, .inl w, .inr 1])

/-- The *sing*/*sang* subschema (26) pins /ɪ/ in the stem and /æ/ in the past. -/
abbrev singSang : Pattern (Fin 3 ⊕ Fin 3) (Flat (List Segment)) :=
  nucleusPair [English.Phonology.smallCapitalI] [English.Phonology.æ]

/-- The *string*/*strung* subschema is (26) with /ʌ/ for /æ/. -/
abbrev stringStrung : Pattern (Fin 3 ⊕ Fin 3) (Flat (List Segment)) :=
  nucleusPair [English.Phonology.smallCapitalI] [English.Phonology.wedge]

-- (25)
theorem ablaut_pairs_iff {s p : Fin 3 → List σ} :
    ablaut ≤ ofItem (Sum.elim (Flat.some ∘ s) (Flat.some ∘ p)) ↔ Set.EqOn s p {1}ᶜ := by
  refine ofTerms_sumElim_le_ofItem_iff.trans ⟨?_, fun h ↦ ⟨![s 0, s 1, s 2, p 1], ?_, ?_⟩⟩
  · rintro ⟨x, rfl, rfl⟩ i hi
    fin_cases i <;> first | rfl | exact (hi rfl).elim
  · funext i
    fin_cases i <;> rfl
  · funext i
    fin_cases i <;> first | rfl | exact (h (by simp)).symm

theorem nucleusPair_pairs_iff {v w : List σ} {s p : Fin 3 → List σ} :
    nucleusPair v w ≤ ofItem (Sum.elim (Flat.some ∘ s) (Flat.some ∘ p)) ↔
      ∃ o c, s = ![o, v, c] ∧ p = ![o, w, c] := by
  refine ofTerms_sumElim_le_ofItem_iff.trans
    ⟨fun ⟨x, hs, hp⟩ ↦ ⟨x 0, x 1, ?_, ?_⟩, fun ⟨o, c, hs, hp⟩ ↦ ⟨![o, c], ?_, ?_⟩⟩ <;>
  · subst_vars
    funext i
    fin_cases i <;> rfl

/-- A subschema with pinned nuclei is a special case of the general ablaut schema, which
subsumes it, so every pair of (26) is a pair of (25). -/
theorem ablaut_le_nucleusPair (v w : List σ) : ablaut ≤ nucleusPair v w :=
  ofTerms_le_ofTerms_iff.2 ⟨![.inr 0, .inl v, .inr 1, .inl w], by
    funext i
    rcases i with i | i <;> fin_cases i <;> rfl⟩

-- (25), (26), p. 147: the subschema fills the nucleus variables of the general schema
theorem instantiation_nucleusPair (v w : List σ) :
    Instantiation (ablaut (σ := σ)).content (nucleusPair v w).content {.inl 1, .inr 1} := by
  refine ⟨fun x hx ↦ ?_, fun x hx ↦ ?_⟩
  · rcases x with i | i <;> fin_cases i <;> first | rfl | simp at hx
  · rcases hx with rfl | rfl <;> exact bot_lt_iff_ne_bot.2 Flat.coe_ne_bot

theorem contrast_of_nucleusPair {v w : List σ} (hvw : v ≠ w) {s p : Fin 3 → List σ}
    (h : nucleusPair v w ≤ ofItem (Sum.elim (Flat.some ∘ s) (Flat.some ∘ p))) :
    Contrast (Flat.some ∘ s) (Flat.some ∘ p) {1} := by
  obtain ⟨o, c, rfl, rfl⟩ := nucleusPair_pairs_iff.1 h
  rw [contrast_iff_of_forall_isMax fun _ ↦ Flat.isMax_of_ne_bot]
  refine ⟨fun i hi ↦ ?_, fun q hq ↦ ?_⟩
  · fin_cases i <;> first | rfl | exact (hi rfl).elim
  · rw [Set.mem_singleton_iff] at hq
    subst hq
    exact ⟨Flat.coe_ne_bot, Flat.coe_ne_bot, fun h ↦ hvw (Flat.coe_injective h)⟩

-- (24), (26), (43), (45)
theorem ablaut_words :
    singSang ≤ ofItem (Sum.elim (syllable English.Phonology.transcribe Wordlist.sing)
        (syllable English.Phonology.transcribe Wordlist.sang)) ∧
      stringStrung ≤ ofItem (Sum.elim (syllable English.Phonology.transcribe Wordlist.string)
        (syllable English.Phonology.transcribe Wordlist.strung)) ∧
      ablaut ≤ ofItem (Sum.elim (syllable German.Phonology.transcribe Wordlist.sprech)
        (syllable German.Phonology.transcribe Wordlist.sprich)) :=
  ⟨by decide, by decide, by decide⟩

/-! ### The present-tense cells of (45) as a morphome -/

/-- `Person` lists the three persons. -/
inductive Person
  | first
  | second
  | third
  deriving DecidableEq, Fintype

/-- `Number` distinguishes singular and plural. -/
inductive Number
  | sg
  | pl
  deriving DecidableEq, Fintype

/-- A present-tense cell of the paradigm (41) pairs a person with a number. -/
abbrev GCell := Person × Number

/-- `GStem` has the two present-tense stems of *sprechen*, (41) to (43). -/
inductive GStem
  | sprech
  | sprich
  deriving DecidableEq

/-- `sprechen` gives the stem of each present-tense cell of *sprechen*, (41). -/
def sprechen : GCell → GStem
  | (.second, .sg) | (.third, .sg) => .sprich
  | _ => .sprech

/-- `GFeature` lists the features of the paradigm, person and number. -/
inductive GFeature
  | person
  | number
  deriving DecidableEq, Fintype

/-- Each feature induces the partition of the cells by its value. -/
def gFeatures : GFeature → Setoid GCell
  | .person => Setoid.ker Prod.fst
  | .number => Setoid.ker Prod.snd

instance (i : GFeature) : DecidableRel (gFeatures i) := by
  cases i <;> exact Setoid.ker.decidableRel _

/-- The cells of the special stem are the second and third singular. -/
def specialCells : Finset GCell := {(.second, .sg), (.third, .sg)}

theorem sprechen_formCells : formCells sprechen .sprich = specialCells := by decide

theorem specialCells_not_natural : ¬ IsValueConjunction gFeatures ↑specialCells := by
  rw [isValueConjunction_coe_iff]
  decide

-- (45) [aronoff-1994]
theorem spricht_morphome : IsMorphome sprechen (IsValueConjunction gFeatures) ↑specialCells :=
  isMorphome_of_formCells sprechen (.second, .sg) _ sprechen_formCells (by decide)
    specialCells_not_natural

/-! ### The Same Verb Problem -/

/-- `Lexeme` lists the lexemes of Section 5.6, main verb *take* and *take part*, (57) to (59);
the two *draw*s of (60) and *withdraw*, (62); and the homophones *ring*, *wring* and *ring*
'encircle'. -/
inductive Lexeme
  | take
  | takePart
  | drawPicture
  | drawElicit
  | withdraw
  | ring
  | wring
  | ringCity
  deriving DecidableEq, Fintype

/-- `Pivot` has the morphosyntax-phonology pivots, one per relational coindex shared across
lexemes. -/
inductive Pivot
  | take
  | draw
  | ring
  | wring
  | ringCity
  deriving DecidableEq, Fintype

/-- `Tense` distinguishes present and past. -/
inductive Tense
  | pres
  | past
  deriving DecidableEq, Fintype

/-- In the paradigm linkage, each lexeme selects its pivot in every cell, with the cell's own
property set. -/
def linkage : Linkage Lexeme Pivot Tense Tense where
  realize
    | .take, _ | .takePart, _ => {.take}
    | .drawPicture, _ | .drawElicit, _ | .withdraw, _ => {.draw}
    | .ring, _ => {.ring}
    | .wring, _ => {.wring}
    | .ringCity, _ => {.ringCity}
  pm _ σ := σ

/-- Two lexemes are the same verb when they share their form correspondents at every cell,
as under the relational coindex 23 of (60), a shared morphosyntax and phonology with no
shared semantics. -/
def SameVerb (l₁ l₂ : Lexeme) : Prop := ∀ σ, linkage.corr l₁ σ = linkage.corr l₂ σ

instance : DecidableRel SameVerb := fun l₁ l₂ ↦
  inferInstanceAs (Decidable (∀ σ, linkage.corr l₁ σ = linkage.corr l₂ σ))

/-- Same verbs inflect alike at every cell, whatever their semantics, as in (57) to (61). -/
theorem realize_eq_of_sameVerb {W : Type*} [DecidableEq W] (rf : Pivot → Tense → W)
    {l₁ l₂ : Lexeme} (h : SameVerb l₁ l₂) (σ : Tense) :
    linkage.realized rf l₁ σ = linkage.realized rf l₂ σ :=
  linkage.realized_eq_of_corr_eq rf (h σ)

-- Section 3.6
theorem SameVerb.symm {l₁ l₂ : Lexeme} (h : SameVerb l₁ l₂) : SameVerb l₂ l₁ :=
  fun σ ↦ (h σ).symm

/-- The two *draw*s, (60), *take* with *take part*, (58), and *withdraw* with *draw*, (62), are
the same verb; the homophones *ring*, *wring* and *ring* 'encircle' are not. -/
example : SameVerb .drawPicture .drawElicit ∧ SameVerb .take .takePart ∧
    SameVerb .withdraw .drawPicture ∧ ¬ SameVerb .ring .wring ∧ ¬ SameVerb .ring .ringCity := by
  decide

/-! ### The regular paradigm -/

/-- `VCell` lists the six cells of (16). -/
inductive VCell
  | pres
  | pres3sg
  | past
  | inf
  | prespt
  | ptcp
  deriving DecidableEq, Fintype

/-- `Exponent` lists the exponents of the regular paradigm (19), with none (`bare`) for the
present and the infinitive, whose phonology is coindexed with the stem's. -/
inductive Exponent
  | bare
  | s
  | t
  | ing
  deriving DecidableEq

/-- `walk` gives the exponent of each cell in the paradigm of *walk*, (19). -/
def walk : VCell → Exponent
  | .pres | .inf => .bare
  | .pres3sg => .s
  | .past | .ptcp => .t
  | .prespt => .ing

-- Section 4.3
theorem walk_syncretism :
    formCells walk .bare = {.pres, .inf} ∧ formCells walk .t = {.past, .ptcp} := by
  decide

/-! ### Structural Intersection

The schema (6) is the `Audring2019.ishSchema` of [audring-2019], the affix pinned and the base a
variable. -/

-- (6), (5)
theorem ishSchema_body_eq_inf :
    Audring2019.ishSchema.body = Wordlist.piggish.morphSlots ⊓ Wordlist.childish.morphSlots ⊓
      Wordlist.sluggish.morphSlots := by
  funext v
  fin_cases v <;> decide

/-- The schema is the most the sisters have in common, since a description is instantiated by
all three exactly when it is instantiated by the schema's description. -/
theorem instantiates_ishSchema_iff {s : Schema (Fin 2) (Flat String)} :
    s.Instantiates Audring2019.ishSchema.body ↔
      s.Instantiates Wordlist.piggish.morphSlots ∧ s.Instantiates Wordlist.childish.morphSlots ∧
        s.Instantiates Wordlist.sluggish.morphSlots := by
  rw [ishSchema_body_eq_inf, Schema.instantiates_inf_iff, Schema.instantiates_inf_iff,
    and_assoc]

theorem ishSchema_le_foolish : Audring2019.ishSchema.body ≤ Wordlist.foolish.morphSlots :=
  fun i ↦ by fin_cases i <;> decide

theorem ishSchema_inf_foolish :
    Audring2019.ishSchema.body ⊓ Wordlist.foolish.morphSlots = Audring2019.ishSchema.body :=
  inf_eq_left.2 ishSchema_le_foolish

end JackendoffAudring2020
