module

public import Linglib.Data.Examples.JackendoffAudring2020
public import Linglib.Data.Wordlist.JackendoffAudring2020
public import Linglib.Morphology.ConstructionMorphology.Schema
public import Linglib.Logic.Nonmonotonic.Inheritance
public import Linglib.Core.Relation.ReflTransGen
public import Linglib.Morphology.Paradigm.Linkage
public import Linglib.Morphology.Paradigm.Morphome
public import Linglib.Core.Order.Flat
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.DeriveFintype

/-!
# Jackendoff and Audring (2020): The Texture of the Lexicon

This file formalizes the Relational Morphology of [jackendoff-audring-2020], in which
morphological motivation is shared structure recorded by nondirectional relational links
between fully specified lexical entries, not inheritance from an abstract base. The
mixed-direction pairs of Objection 10 to inheritance, Section 3.4.4, are the test: *assassin*
and *assassinate* build the second on the first in phonology and the first on the second in
semantics, so no acyclic inheritance hierarchy holds both demands (`assassin_cycle`), though
default inheritance itself computes as the taxonomy of Figure 3.5 intends
(`ostrich_overrides`), while a
sister link with a coindex per shared part carries both, (41) (`assassin_pairs`), and reads the
same transposed (`assassin_pairs_symm`). Bumped up a level, Section 4.8.2, the link between the
*-ism* and *-ist* schemas, (47), pairs every ideology's noun with its adherent's, whatever the
base and the ideology (`ismist_pairs`), the open-ended relation the book illustrates with
*Trumpism*. Ablaut, Section 5.3, is a sister link off the syllabic nucleus: the general schema
(25) pairs exactly the stems and pasts that are the same except at the nucleus
(`ablaut_pairs_iff`), the *sing*/*sang* subschema (26) is a special case of it
(`ablaut_pairs_of_nucleusPair`) whose pairs are nucleus contrasts
(`contrast_of_nucleusPair`), and the German present-tense schema (45) has the same
phonological shape. The cells (45) serves, the second and third singular present, are a
morphome, Section 5.4.4: the syncretism class of the special stem of *sprechen* is a value
conjunction of no feature of the paradigm (`spricht_morphome`). The Same Verb Problem, Section
5.6, is a shared morphosyntax-phonology pivot without a shared semantics: two lexemes selecting
the same pivot inflect alike at every cell (`realize_eq_of_sameVerb`), which pairs the two
*draw*s of (60) and *take* with *take part*, (57) to (59), and separates the homophones *ring*
and *wring*. Structural Intersection, Section 7.8.1, is the meet: the schema (6) is the
intersection of its three sisters (5) (`ishSchema_body_eq_inf`), is the most they have in
common (`instantiates_ishSchema_iff`), and absorbs a newly encountered sister
(`ishSchema_inf_foolish`).

## Implementation notes

* Lexical entries and schemas are slot-indexed descriptions over a flat carrier, a constant
  above `⊥` and a variable at `⊥`; a relational coindex is a variable subscripting a slot of
  each entry, which a paired instantiation fills alike
  (`ConstructionMorphology.Schema.InstantiatesAt`). The containment of
  the semantics of *assassinate* in that of *assassin*, (41), is rendered as a shared slot.
* The zero exponence of the present and the infinitive of *walk*, (19), the double
  coindexation of Section 4.3, appears as a syncretism of the paradigm (`walk_syncretism`).
* The cycle theorem renders the paradox of Objection 10 through the well-foundedness of an
  inheritance hierarchy; the book argues from the above-and-below paradox and makes no
  well-foundedness claim.
* The syllables and the *-ish* adjectives are the CLDF forms of
  `Data/Wordlist/JackendoffAudring2020.json`, read as slot-indexed segments by
  `CLDF.Wordlist.Form.slots`; a syllable's positions are onset, nucleus and coda.
* The correspondence between a schema's variable coindices and the constant coindices of its
  instances, left unformalized in Section 4.13.2, is the subscripting of
  `ConstructionMorphology.Schema.InstantiatesAt`; a productive variable is one marked open
  over and above its attested fillers.

## References

* [jackendoff-audring-2020]
* [booij-2010]
* [aronoff-1994]
* [spencer-2013]
* [albright-hayes-2003]
-/

@[expose] public section

namespace JackendoffAudring2020

open Morphology ConstructionMorphology

/-! ### Open and closed variables, (17) and (18)

The toponym patterns (17): a name and the type of a geographical feature, the name an open
variable and the feature type a closed one, whose fillers are learned pattern by pattern; in
(18d) *the* and *of* are constants. -/

/-- The pattern (18a) puts the name before the feature, with the name open and the feature
closed. -/
def toponymA : Schema (Fin 2) (Flat String) := ⟨fun _ ↦ ⊥, {0}⟩

/-- The pattern (18b) puts the feature before the name. -/
def toponymB : Schema (Fin 2) (Flat String) := ⟨fun _ ↦ ⊥, {1}⟩

/-- The pattern (18d), *the* feature *of* name, has two constants, a closed feature and an
open name. -/
def toponymD : Schema (Fin 4) (Flat String) := ⟨![↑"the", ⊥, ↑"of", ⊥], {3}⟩

/-- `toponymsA` holds the stored toponyms of (17a). -/
def toponymsA : Set (Fin 2 → Flat String) :=
  {Wordlist.arrowheadLake.slots, Wordlist.loonMountain.slots, Wordlist.wissahickonCreek.slots,
    Wordlist.laurelHill.slots, Wordlist.sugarIsland.slots}

/-- `toponymsB` holds the stored toponyms of (17b). -/
def toponymsB : Set (Fin 2 → Flat String) :=
  {Wordlist.mountEverest.slots, Wordlist.lakeMichigan.slots, Wordlist.capeCod.slots}

/-- `toponymsD` holds the stored toponyms of (17d). -/
def toponymsD : Set (Fin 4 → Flat String) :=
  {Wordlist.bayOfFundy.slots, Wordlist.gulfOfStLawrence.slots, Wordlist.capeOfGoodHope.slots,
    Wordlist.isleOfWight.slots}

/-- *Morris Mountain* is licensed by (18a), since the name is open and *Mountain* is
attested. -/
theorem morrisMountain_generates : toponymA.Generates toponymsA Wordlist.morrisMountain.slots :=
  ⟨fun i ↦ bot_le, fun i _ hi ↦ by
    fin_cases i
    · exact absurd (Set.mem_singleton _) hi
    · exact ⟨Wordlist.loonMountain.slots, ⟨by simp [toponymsA], fun _ ↦ bot_le⟩, by decide⟩⟩

/-- *Mount Morris* is licensed by (18b) likewise. -/
theorem mountMorris_generates : toponymB.Generates toponymsB Wordlist.mountMorris.slots :=
  ⟨fun i ↦ bot_le, fun i _ hi ↦ by
    fin_cases i
    · exact ⟨Wordlist.mountEverest.slots, ⟨by simp [toponymsB], fun _ ↦ bot_le⟩, by decide⟩
    · exact absurd (Set.mem_singleton _) hi⟩

/-- *Mountain Morris* is not licensed, since *Mountain* is not an attested feature of the
pattern (18b). -/
theorem not_mountainMorris_generates :
    ¬ toponymB.Generates toponymsB ![↑"Mountain", ↑"Morris"] := by
  rintro ⟨-, h⟩
  obtain ⟨w, ⟨hw, -⟩, hw0⟩ := h 0 rfl (by simp [toponymB])
  simp only [toponymsB, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  rcases hw with rfl | rfl | rfl <;> exact absurd hw0 (by decide)

/-- *The Mount of Halle* is not licensed by (18d), since *Mount* is not among its attested
features. -/
theorem not_mountOfHalle_generates :
    ¬ toponymD.Generates toponymsD ![↑"the", ↑"Mount", ↑"of", ↑"Halle"] := by
  rintro ⟨-, h⟩
  obtain ⟨w, ⟨hw, -⟩, hw1⟩ := h 1 rfl (by simp [toponymD])
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
  partialOrderOfCovers (fun a b : Animal ↦ b ∈ a.parents)
    (fun | .animal => 0 | .bird | .fish => 1 | .canary | .ostrich => 2) (by decide)

instance : DecidableLE Animal :=
  decidableLEOfCovers (covers := fun a b : Animal ↦ b ∈ a.parents) [.animal, .bird] (by decide)

/-- `flies` specifies flight locally, so that birds fly and the ostrich overrides. -/
def flies : Animal → Option Bool
  | .bird => some true
  | .ostrich => some false
  | _ => none

/-- The ostrich's override and the canary's inheritance compute as intended. -/
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
  deriving DecidableEq

/-- The variables of (41) are the phonology of *assassin*, which is the base of *assassinate*
(coindex 2), the predicate MURDER of both (coindex 1), the person that *assassin* adds and the
affix that *assassinate* adds. -/
inductive AssassinVar
  | phon
  | murder
  | person
  | ate
  deriving DecidableEq

/-- The slots of *assassin* are its phonology, the predicate it contains, and the person. -/
inductive AssassinSlot
  | phon
  | murder
  | person
  deriving DecidableEq

/-- The slots of *assassinate* are its base, its affix, and its predicate. -/
inductive AssassinateSlot
  | base
  | affix
  | murder
  deriving DecidableEq

/-- `assassinPair` presents the entries (41a) and (41b) with their coindices as one fully
specified description over the shared variables. -/
def assassinPair : Schema AssassinVar (Flat Part) :=
  ⟨fun | .phon => ↑Part.asasin | .murder => ↑Part.murder | .person => ↑Part.person
       | .ate => ↑Part.ate, ∅⟩

/-- `assassinSub` subscripts the slots of *assassin* by the variables of (41). -/
def assassinSub : AssassinSlot → AssassinVar
  | .phon => .phon
  | .murder => .murder
  | .person => .person

/-- `assassinateSub` subscripts the slots of *assassinate* by the variables of (41). -/
def assassinateSub : AssassinateSlot → AssassinVar
  | .base => .phon
  | .affix => .ate
  | .murder => .murder

/-- The entry (41a) is the pair read at the slots of *assassin*. -/
def assassin : Schema AssassinSlot (Flat Part) := assassinPair.comap assassinSub

/-- The entry (41b) is the pair read at the slots of *assassinate*. -/
def assassinate : Schema AssassinateSlot (Flat Part) := assassinPair.comap assassinateSub

/-- The two entries are a paired instantiation of (41), so they share the base phonology and
the predicate through their coindices. -/
theorem assassin_pairs :
    assassinPair.InstantiatesAt (Sum.elim assassinSub assassinateSub)
      (Sum.elim assassin.body assassinate.body) :=
  ⟨assassinPair.body, le_rfl, funext fun p ↦ by rcases p with p | p <;> cases p <;> rfl⟩

/-- The link is nondirectional, since the two entries paired in the opposite order also
instantiate (41). -/
theorem assassin_pairs_symm :
    assassinPair.InstantiatesAt (Sum.elim assassinateSub assassinSub)
      (Sum.elim assassinate.body assassin.body) :=
  Schema.instantiatesAt_elim_swap.2 assassin_pairs

/-- `Pair` has the two words as the nodes of an inheritance hierarchy. -/
inductive Pair
  | assassin
  | assassinate
  deriving DecidableEq

/-- By Objection 10, the phonology demands that *assassinate* inherit from *assassin* and the
semantics that *assassin* inherit from *assassinate*, and no acyclic hierarchy holds both. -/
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

/-- The variables of the schemas (47) are the base `X` and the ideology, shared by the two
schemas (coindices α and β), the two affixes and the relation ADHERENT. -/
inductive IsmIstVar
  | base
  | ideology
  | ism
  | ist
  | adherent
  deriving DecidableEq

/-- The slots of the *-ism* schema are its base, its affix and its semantics. -/
inductive IsmSlot
  | base
  | affix
  | sem
  deriving DecidableEq

/-- The slots of the *-ist* schema are its base, its affix, the relation ADHERENT, and its
ideology. -/
inductive IstSlot
  | base
  | affix
  | relation
  | ideology
  deriving DecidableEq

variable {B I : Type*}

/-- `ismist` presents the *-ism* and *-ist* schemas of (47) with their coindices as one
description, with the affixes and ADHERENT pinned and the base and the ideology open. -/
def ismist : Schema IsmIstVar (Flat (Atom B I)) :=
  ⟨fun | .ism => ↑(Atom.ism : Atom B I) | .ist => ↑(Atom.ist : Atom B I)
       | .adherent => ↑(Atom.adherent : Atom B I) | _ => ⊥, {.base, .ideology}⟩

/-- `ismSub` subscripts the slots of the *-ism* schema by the variables of (47). -/
def ismSub : IsmSlot → IsmIstVar
  | .base => .base
  | .affix => .ism
  | .sem => .ideology

/-- `istSub` subscripts the slots of the *-ist* schema by the variables of (47). -/
def istSub : IstSlot → IsmIstVar
  | .base => .base
  | .affix => .ist
  | .relation => .adherent
  | .ideology => .ideology

/-- The schema (47a) pins the affix to *-ism* and leaves the base and the ideology open. -/
def ismSchema : Schema IsmSlot (Flat (Atom B I)) := ismist.comap ismSub

/-- The schema (47b) pins the affix to *-ist* and the semantics to ADHERENT of an open
ideology. -/
def istSchema : Schema IstSlot (Flat (Atom B I)) := ismist.comap istSub

/-- `ismWord b i` is the *-ism* noun on base `b` denoting the ideology `i`. -/
def ismWord (b : B) (i : I) : IsmSlot → Flat (Atom B I)
  | .base => ↑(Atom.base b : Atom B I)
  | .affix => ↑(Atom.ism : Atom B I)
  | .sem => ↑(Atom.ideology i : Atom B I)

/-- `istWord b i` is the *-ist* noun on base `b` denoting an adherent of `i`. -/
def istWord (b : B) (i : I) : IstSlot → Flat (Atom B I)
  | .base => ↑(Atom.base b : Atom B I)
  | .affix => ↑(Atom.ist : Atom B I)
  | .relation => ↑(Atom.adherent : Atom B I)
  | .ideology => ↑(Atom.ideology i : Atom B I)

/-- `ismistWord b i` fills the variables of (47) with the base `b` and the ideology `i`. -/
def ismistWord (b : B) (i : I) : IsmIstVar → Flat (Atom B I)
  | .base => ↑(Atom.base b : Atom B I)
  | .ideology => ↑(Atom.ideology i : Atom B I)
  | .ism => ↑(Atom.ism : Atom B I)
  | .ist => ↑(Atom.ist : Atom B I)
  | .adherent => ↑(Atom.adherent : Atom B I)

/-- The relation is open-ended, since for any base and any ideology *X-ism* and *X-ist* are a
paired instantiation of the sister schemas, *Trumpism* and *Trumpist* included. -/
theorem ismist_pairs (b : B) (i : I) :
    ismist.InstantiatesAt (Sum.elim ismSub istSub) (Sum.elim (ismWord b i) (istWord b i)) :=
  ⟨ismistWord b i, fun v ↦ by cases v <;> first | exact bot_le | exact le_rfl,
    funext fun p ↦ by rcases p with p | p <;> cases p <;> rfl⟩

/-! ### Ablaut as a link off the nucleus -/

/-- The variables of the ablaut schemas are the onset and the coda, shared by stem and past,
and the two nuclei. -/
inductive NucleusVar
  | onset
  | coda
  | stem
  | past
  deriving DecidableEq

/-- `stemSub` subscripts the stem's three positions, onset, nucleus and coda, by the
variables of the ablaut schemas. -/
def stemSub : Fin 3 → NucleusVar := ![.onset, .stem, .coda]

/-- `pastSub` subscripts the past's positions by the variables of the ablaut schemas. -/
def pastSub : Fin 3 → NucleusVar := ![.onset, .past, .coda]

/-- `nucleusPair v w` links two syllables at every position but the nucleus and pins the
nuclei `v` and `w`, with `⊥` for an open nucleus. It is the shape of the ablaut schemas (25)
and (26) and of the German present-tense schema (45). -/
def nucleusPair (v w : Flat String) : Schema NucleusVar (Flat String) :=
  ⟨fun | .stem => v | .past => w | _ => ⊥, {.onset, .coda}⟩

/-- The general ablaut schema (25) leaves both nuclei open. -/
def ablaut : Schema NucleusVar (Flat String) := nucleusPair ⊥ ⊥

/-- The *sing*/*sang* subschema (26) pins /ɪ/ in the stem and /æ/ in the past. -/
def singSang : Schema NucleusVar (Flat String) := nucleusPair ↑"ɪ" ↑"æ"

/-- The *string*/*strung* subschema is (26) with /ʌ/ for /æ/. -/
def stringStrung : Schema NucleusVar (Flat String) := nucleusPair ↑"ɪ" ↑"ʌ"

/-- A syllable instantiates a nucleus pair's stem side exactly when its nucleus is the pinned
one. -/
theorem comap_stemSub_instantiates_iff {v w : Flat String} {s : Fin 3 → Flat String} :
    ((nucleusPair v w).comap stemSub).Instantiates s ↔ v ≤ s 1 :=
  ⟨fun h ↦ h 1, fun h i ↦ by fin_cases i <;> first | exact bot_le | exact h⟩

theorem comap_pastSub_instantiates_iff {v w : Flat String} {p : Fin 3 → Flat String} :
    ((nucleusPair v w).comap pastSub).Instantiates p ↔ w ≤ p 1 :=
  ⟨fun h ↦ h 1, fun h i ↦ by fin_cases i <;> first | exact bot_le | exact h⟩

/-- A paired instantiation of a nucleus pair is a stem and a past that are the same except at
the nucleus, with the pinned nuclei. -/
theorem nucleusPair_iff {v w : Flat String} {s p : Fin 3 → Flat String} :
    (nucleusPair v w).InstantiatesAt (Sum.elim stemSub pastSub) (Sum.elim s p) ↔
      v ≤ s 1 ∧ w ≤ p 1 ∧ Set.EqOn s p {1}ᶜ := by
  rw [Schema.instantiatesAt_elim_iff_eqOn (S := {1}) (by decide) (by decide) (by decide),
    comap_stemSub_instantiates_iff, comap_pastSub_instantiates_iff]

/-- (25) pairs exactly the stems and pasts that are the same except at the nucleus. -/
theorem ablaut_pairs_iff {s p : Fin 3 → Flat String} :
    ablaut.InstantiatesAt (Sum.elim stemSub pastSub) (Sum.elim s p) ↔ Set.EqOn s p {1}ᶜ := by
  simp [ablaut, nucleusPair_iff]

/-- A subschema with pinned nuclei is a special case of the general ablaut schema, so every
pair of (26) is a pair of (25). -/
theorem ablaut_pairs_of_nucleusPair {v w : Flat String} {s p : Fin 3 → Flat String}
    (h : (nucleusPair v w).InstantiatesAt (Sum.elim stemSub pastSub) (Sum.elim s p)) :
    ablaut.InstantiatesAt (Sum.elim stemSub pastSub) (Sum.elim s p) :=
  ablaut_pairs_iff.2 (nucleusPair_iff.1 h).2.2

/-- A pair under a subschema with distinct pinned nuclei is a nucleus contrast, the same
except at the nucleus, where both are present and differ. -/
theorem contrast_of_nucleusPair {v w : String} (hvw : v ≠ w) {s p : Fin 3 → Flat String}
    (h : (nucleusPair ↑v ↑w).InstantiatesAt (Sum.elim stemSub pastSub) (Sum.elim s p)) :
    Contrast s p {1} := by
  obtain ⟨hv, hw, hs⟩ := nucleusPair_iff.1 h
  rw [Flat.coe_le_iff] at hv hw
  rw [contrast_iff_of_forall_isMax fun _ ↦ Flat.isMax_of_ne_bot]
  refine ⟨hs, fun q hq ↦ ?_⟩
  rw [Set.mem_singleton_iff] at hq
  subst hq
  rw [hv, hw]
  exact ⟨Flat.coe_ne_bot, Flat.coe_ne_bot, fun h ↦ hvw (Flat.coe_injective h)⟩

/-- Two syllables differing only in their nucleus are a paired instantiation of the subschema
pinning those nuclei. -/
theorem syllable_pairs (o v w c : String) :
    (nucleusPair ↑v ↑w).InstantiatesAt (Sum.elim stemSub pastSub)
      (Sum.elim ![↑o, ↑v, ↑c] ![↑o, ↑w, ↑c]) := by
  rw [nucleusPair_iff]
  refine ⟨le_rfl, le_rfl, fun q hq ↦ ?_⟩
  fin_cases q <;> first | rfl | exact (hq rfl).elim

/-- The pair *sing*/*sang*, (24), instantiates (26), *string*/*strung* instantiates its
subschema, and the German *sprech-*/*sprich-* of (43) instantiates the shape of (45). -/
theorem ablaut_words :
    singSang.InstantiatesAt (Sum.elim stemSub pastSub)
        (Sum.elim Wordlist.sing.slots Wordlist.sang.slots) ∧
      stringStrung.InstantiatesAt (Sum.elim stemSub pastSub)
        (Sum.elim Wordlist.string.slots Wordlist.strung.slots) ∧
      ablaut.InstantiatesAt (Sum.elim stemSub pastSub)
        (Sum.elim Wordlist.sprech.slots Wordlist.sprich.slots) := by
  simp only [singSang, stringStrung, ablaut, nucleusPair_iff]
  refine ⟨⟨by decide, by decide, ?_⟩, ⟨by decide, by decide, ?_⟩,
    ⟨bot_le, bot_le, ?_⟩⟩
  all_goals intro q hq; fin_cases q <;> first | decide | exact (hq rfl).elim

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

/-- The special cells are a value conjunction of neither feature. -/
theorem specialCells_not_natural : ¬ IsValueConjunction gFeatures ↑specialCells := by
  rw [isValueConjunction_coe_iff]
  decide

/-- The pattern (45) is morphomic, as the book says citing [aronoff-1994], because the cells
the special stem serves are a syncretism class and no natural class of the paradigm. -/
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

/-- Sameness of verb is nondirectional, so no use is the basic one, Section 3.6. -/
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

/-- The double coindexation of Section 4.3 appears as a syncretism, since the present and the
infinitive share the stem's phonology, and the past the past participle's. -/
theorem walk_syncretism :
    formCells walk .bare = {.pres, .inf} ∧ formCells walk .t = {.past, .ptcp} := by
  decide

/-! ### Structural Intersection -/

/-- The schema (6) over the two slots of an *-ish* adjective, base and affix, pins the affix
and makes the base a variable. -/
def ishSchema : Schema (Fin 2) (Flat String) := Schema.productive ![⊥, ↑"ish"]

/-- Structural Intersection constructs the schema, since the description of (6) is the meet of
the three sisters of (5), keeping what they share and leaving a variable where they differ. -/
theorem ishSchema_body_eq_inf :
    ishSchema.body =
      Wordlist.piggish.slots ⊓ Wordlist.childish.slots ⊓ Wordlist.sluggish.slots := by
  funext v
  fin_cases v <;> decide

/-- The schema is the most the sisters have in common, since a description is instantiated by
all three exactly when it is instantiated by the schema's description. -/
theorem instantiates_ishSchema_iff {s : Schema (Fin 2) (Flat String)} :
    s.Instantiates ishSchema.body ↔
      s.Instantiates Wordlist.piggish.slots ∧ s.Instantiates Wordlist.childish.slots ∧
        s.Instantiates Wordlist.sluggish.slots := by
  rw [ishSchema_body_eq_inf, Schema.instantiates_inf_iff, Schema.instantiates_inf_iff,
    and_assoc]

theorem ishSchema_le_foolish : ishSchema.body ≤ Wordlist.foolish.slots := fun i ↦ by
  fin_cases i <;> decide

/-- A newly encountered sister intersected with the schema yields the schema again, the
Minimal Generalization Learner's fixed point. -/
theorem ishSchema_inf_foolish : ishSchema.body ⊓ Wordlist.foolish.slots = ishSchema.body :=
  inf_eq_left.2 ishSchema_le_foolish

end JackendoffAudring2020
