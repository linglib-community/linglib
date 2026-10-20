module

public import Mathlib.Data.Finset.Card
public import Studies.Corbett1991
public import Linglib.Morphology.DistributedMorphology.Gender
public import Linglib.Morphology.DistributedMorphology.VocabularyInsertion.Basic
public import Linglib.Fragments.Romance.Spanish.Gender
public import Linglib.Fragments.Slavic.Russian.Gender
public import Linglib.Fragments.Hausa.Gender

/-!
# Kramer (2020): Grammatical Gender: A Close Look at Gender Assignment Across Languages

This file formalizes the review's account of how nouns are sorted into genders. Every gender
system assigns gender to some nouns by animacy, humanness, or social gender/biological sex, the
semantic core generalization, and the remainder nouns take one gender or several, recycled from
the core or novel, in every combination (Table 2). Russian's remainder follows declension class
up to the Class III exceptions, and Hausa's feminine remainder ends in *-ā*, a correlation that
fails in the other direction. Against these facts the review sets Harris's lexical rules
beside Kramer's gender-on-*n* analysis for Spanish: the two agree on
Spanish, but a lexical entry holds one gender feature, so hybrid nouns call for a second
structural source, and the thesis of radical interpretability derives the semantic core from
the structural account alone.

## Implementation notes

The semantic core generalization is checked over the assignment survey of `Corbett1991`, and the
Spanish, Russian, and Hausa data are the Fragments' nouns rather than the review's tables;
`Remainder.spanish` reads the split of Table 1 off the Fragment, and the two assignment accounts are
compared on every noun of the Fragment's shape rather than on its list, the lexical one on every
noun but a hybrid. A noun is [human] for Harris when its referents are human or animals whose gender
is their sex, read off the Fragment's animacy and natural gender. The determiner items of (25) go
through the library's Subset Principle, so *el* for [−fem] and for featureless *n* is a computation
rather than a listing, checked against the Fragment's article. The hybrid datum (27) is the one
hand-typed example, since the Russian Fragment records only the morphological gender of *vrač*.

## References

* [kramer-2020]
* [corbett-1991] — the assignment survey and the Russian declension rule
* [harris-1991] — lexical gender assignment
* [kramer-2015] — structural gender assignment
-/

@[expose] public section

namespace Kramer2020

open DistributedMorphology
open Spanish.Gender (Value allNouns estudiante persona numberSystem)

/-! ### The semantic core (§1.2) -/

/-- The minimal properties of (3) are animacy, humanness, and social gender or
biological sex. -/
def IsCore (b : Corbett1991.Criterion) : Prop := b ∈ ({.animacy, .humanness, .sex} : Finset _)

instance : DecidablePred IsCore := fun _ ↦ inferInstanceAs (Decidable (_ ∈ _))

/-- By the semantic core generalization (2), a language with gender assigns it
to some nouns by a property of (3). -/
def SatisfiesSemanticCore (e : Corbett1991.SurveyEntry) : Prop := ∃ b ∈ e.criteria, IsCore b

instance : DecidablePred SatisfiesSemanticCore := fun _ ↦ by
  unfold SatisfiesSemanticCore; infer_instance

theorem semantic_core_holds : ∀ e ∈ Corbett1991.survey, SatisfiesSemanticCore e := by decide

/-! ### Remainder nouns (§2.3.1) -/

/-- The genders a language assigns semantically and the genders of its
remainder nouns. -/
structure Remainder (G : Type*) where
  core : Finset G
  remainder : Finset G

namespace Remainder

variable {G : Type*} (r : Remainder G)

/-- The remainder nouns all take one gender. -/
def AllSame : Prop := r.remainder.card = 1

/-- The remainder genders are recycled from the core. -/
def Recycled : Prop := r.remainder ⊆ r.core

/-- The remainder genders are novel. -/
def Novel : Prop := Disjoint r.remainder r.core

/-- Recycled and novel genders both occur. -/
def Mixed : Prop := ¬ r.Recycled ∧ ¬ r.Novel

instance : Decidable r.AllSame := inferInstanceAs (Decidable (r.remainder.card = 1))

instance [DecidableEq G] : Decidable r.Recycled :=
  inferInstanceAs (Decidable (r.remainder ⊆ r.core))

instance [DecidableEq G] : Decidable r.Novel :=
  inferInstanceAs (Decidable (Disjoint r.remainder r.core))

instance [DecidableEq G] : Decidable r.Mixed := inferInstanceAs (Decidable (_ ∧ _))

/-- The cell of Table 2 marked not applicable is empty, since a single remainder gender is
recycled or novel but not both. -/
theorem not_mixed_of_allSame (h : r.AllSame) : ¬ r.Mixed := by
  obtain ⟨g, hg⟩ := Finset.card_eq_one.mp h
  rintro ⟨hr, hn⟩
  simp only [Recycled, Novel, hg, Finset.singleton_subset_iff,
    Finset.disjoint_singleton_left] at hr hn
  exact hn hr

/-- The core and remainder genders of a lexicon, the core being the nouns whose gender is
natural. -/
def ofNouns {N : Type*} (nouns : List N) (natural : N → Prop) [DecidablePred natural]
    (gender : N → Gender) : Remainder Gender where
  core := ((nouns.filter (natural ·)).map gender).toFinset
  remainder := ((nouns.filter (¬ natural ·)).map gender).toFinset

/-- Dieri makes female humans feminine and male humans and every other noun
masculine. -/
def dieri : Remainder Gender := ⟨{.masculine, .feminine}, {.masculine}⟩

/-- Tamil has Dieri's core and puts the remainder in a novel neuter. -/
def tamil : Remainder Gender := ⟨{.masculine, .feminine}, {.neuter}⟩

/-- Spanish splits the remainder arbitrarily over both core genders (Table 1), as the
Fragment records. -/
def spanish : Remainder Gender :=
  ofNouns allNouns (·.IsNaturalGender Value.toLabel) (·.gender.toLabel)

/-- Blackfoot makes animates animate and puts inanimates in a novel inanimate gender or
the recycled animate one. -/
def blackfoot : Remainder Gender := ⟨{.animate}, {.animate, .inanimate}⟩

/-- Table 2 has one remainder gender recycled (Dieri) or novel (Tamil), and different
remainder genders recycled (Spanish) or both (Blackfoot). -/
theorem table2 :
    dieri.AllSame ∧ dieri.Recycled ∧ tamil.AllSame ∧ tamil.Novel ∧
      ¬ spanish.AllSame ∧ spanish.Recycled ∧ ¬ blackfoot.AllSame ∧ blackfoot.Mixed := by
  decide

/-- Akɔɔse has the human gender as its core and at least seven other remainder genders, so
its remainder takes different, novel genders. -/
theorem akoose_cell (r : Remainder ℕ) (hcore : r.core = {1}) (hcard : 7 ≤ r.remainder.card)
    (h : 1 ∉ r.remainder) : ¬ r.AllSame ∧ r.Novel :=
  ⟨fun h₁ ↦ by unfold AllSame at h₁; omega,
    by rw [Novel, hcore]; exact Finset.disjoint_singleton_right.mpr h⟩

end Remainder

/-! ### Declension class in Russian (§2.3.2) -/

/-- [corbett-1991]'s assignment for the Russian remainder (18) makes Class I
masculine, Class II or III feminine, and all others neuter. -/
def declensionGender : Russian.Gender.DeclClass → Gender
  | .I => .masculine
  | .II | .III => .feminine
  | .IV => .neuter

/-- (18) misassigns exactly the Class III nouns of (19), neuter *znamja*
and masculine *put'*. -/
theorem declension_exceptions :
    Russian.Gender.remainderNouns.filter
        (fun n ↦ n.declClass.map declensionGender ≠ some n.gender.toLabel) =
      [Russian.Gender.znamja, Russian.Gender.put'] := by
  decide

/-! ### The final vowel in Hausa (§2.3.2, §3.3.1) -/

/-- The disputed rule (26) makes a noun in *-ā* feminine and any other
masculine. -/
def phonologicalRule (n : Hausa.Noun) : Gender :=
  if n.EndsInAa then .feminine else .masculine

/-- In (22e) *kadā̀* 'crocodile' ends in *-ā* and is masculine, so (26) is
false. -/
theorem phonologicalRule_kada : phonologicalRule Hausa.kada ≠ Hausa.kada.gender := by
  decide

/-- In its valid direction, every feminine noun outside the semantic core ends in *-ā*. -/
theorem feminine_remainder_aa :
    ∀ n ∈ Hausa.allNouns,
      ¬ n.IsNaturalGender id → n.gender = .feminine → n.EndsInAa := by
  decide

/-! ### Lexical gender assignment (§3.2) -/

/-- A lexical entry in [harris-1991]'s system bears the semantic features
[human] and [female] and the gender feature [f]. -/
structure LexicalEntry where
  human : Bool
  female : Bool
  f : Bool
  deriving DecidableEq, Repr, Fintype

namespace LexicalEntry

/-- Human Cloning (Figure 1) doubles a [human] entry into a [male] and a
[female] entry. -/
def humanCloning (e : LexicalEntry) : List LexicalEntry :=
  if e.human then [{ e with female := false }, { e with female := true }] else [e]

/-- The Human Gender rule (23) is [female] → [f] / __ [human]. -/
def humanGender (e : LexicalEntry) : LexicalEntry :=
  { e with f := e.f || (e.human && e.female) }

/-- Agreement is feminine with [f] and masculine by default. -/
def gender (e : LexicalEntry) : Gender := if e.f then .feminine else .masculine

end LexicalEntry

/-- A noun is a hybrid when its referents have a gender other than its own. -/
def IsHybrid (n : Spanish.Gender.Noun) : Prop := ∃ g ∈ n.naturalGender, g ≠ n.gender.toLabel

instance (n : Spanish.Gender.Noun) : Decidable (IsHybrid n) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- A Fragment noun's lexical entry is [human] when its referents are human, or animals whose
gender is their sex (higher animals honoris causa), [female] when its referents are female,
and carries a listed [f] when it is feminine without its referents having a gender. -/
def lexicalEntry (n : Spanish.Gender.Noun) : LexicalEntry :=
  ⟨decide (n.animacy = .human ∨ n.naturalGender.isSome),
    decide (n.naturalGender = some .feminine),
    decide (n.naturalGender = none ∧ n.gender = .fem)⟩

/-- The lexical account recovers the gender of every noun of the Fragment's shape but a
hybrid. -/
theorem lexical_faithful (n : Spanish.Gender.Noun) (h : ¬ IsHybrid n) :
    (lexicalEntry n).humanGender.gender = n.gender.toLabel := by
  obtain ⟨⟨_, g, b⟩, _⟩ := n
  cases g <;> rcases b with _ | l <;> (try cases l) <;>
    simp_all [IsHybrid, lexicalEntry, LexicalEntry.humanGender, LexicalEntry.gender,
      Value.toLabel]

/-- No noun of the Fragment is a hybrid, so the lexical account recovers the gender of each. -/
theorem allNouns_not_hybrid : ∀ n ∈ allNouns, ¬ IsHybrid n := by
  decide

/-- Human Cloning of *el estudiante* yields an entry of each gender: the lexical account
derives *la estudiante* (14a). -/
theorem estudiante_cloned :
    (lexicalEntry (estudiante .masc)).humanCloning.map (·.humanGender.gender) =
      [.masculine, .feminine] := by
  decide

/-- *persona*, listed with [f], stays feminine under Human Cloning. -/
theorem persona_cloned_feminine :
    (lexicalEntry persona).humanCloning.map (·.humanGender.gender) =
      [.feminine, .feminine] := by
  decide

/-! ### Structural gender assignment (§3.2) -/

/-- The four n's of (24). -/
def spanishHeads : List Categorizer.Head := [.n_iFem, .n_iMasc, .n_plain, .n_uFem]

/-- A Fragment noun's n bears interpretable gender for the natural-gender
nouns and u[+fem] for the arbitrarily feminine remainder, *persona* among
them, and is plain otherwise. -/
def nHead (n : Spanish.Gender.Noun) : Categorizer.Head :=
  match n.gender, n.naturalGender with
  | .fem, some .feminine => .n_iFem
  | .masc, some .masculine => .n_iMasc
  | .fem, _ => .n_uFem
  | _, _ => .n_plain

theorem nHead_mem_spanishHeads (n : Spanish.Gender.Noun) : nHead n ∈ spanishHeads := by
  obtain ⟨⟨_, g, b⟩, _⟩ := n; cases g <;> rcases b with _ | l <;> (try cases l) <;>
    simp [nHead, spanishHeads]

/-- The n of either entry of *estudiante* bears an interpretable gender feature: its gender is
its referent's (14a). -/
theorem nHead_estudiante (g : Value) :
    (nHead (estudiante g)).gender.map (·.interp) = some .interpretable := by
  cases g <;> decide

/-- A definite determiner bears [d], [def], and the gender it
acquires by agreement. -/
inductive DetFeature where
  | d
  | definite
  | gender (v : GenderValue)
  deriving DecidableEq, Repr

/-- What the determiner carries after agreeing with a head. -/
def determinerFeatures (ch : Categorizer.Head) : Finset DetFeature :=
  {.d, .definite} ∪ (ch.gender.map fun gf ↦ .gender gf.val).toFinset

/-- Of the Spanish definite determiners (25), *la* carries [+fem] and *el* is
underspecified. -/
def determiners : List (VocabularyItem DetFeature String) :=
  [{.d, .definite, .gender ⟨.fem, .pos⟩} ⟷ "la", {.d, .definite} ⟷ "el"]

/-- The determiner a head takes, by the Subset Principle. -/
def determiner (ch : Categorizer.Head) : Option String :=
  subsetPrinciple determiners (determinerFeatures ch)

/-- A determiner with [−fem] and one with no gender feature both take
*el*: *la* carries a feature neither bears. -/
theorem determiner_iMasc_eq_plain :
    determiner .n_iMasc = some "el" ∧ determiner .n_plain = some "el" := by decide

/-- Natural and arbitrary feminine share *la*, since both bear [+fem]. -/
theorem determiner_iFem_eq_uFem :
    determiner .n_iFem = some "la" ∧ determiner .n_uFem = some "la" := by decide

/-- The structural account recovers the Fragment's singular definite article for every noun of
its shape. -/
theorem structural_faithful (n : Spanish.Gender.Noun) :
    determiner (nHead n) = some (n.gender.definiteArticle (numberSystem.value .singular)) := by
  obtain ⟨⟨_, g, b⟩, _⟩ := n; cases g <;> rcases b with _ | l <;> (try cases l) <;>
    dsimp only [nHead] <;> decide

/-- On Spanish the two accounts agree (§3.3), noun by noun, for every noun but a hybrid. -/
theorem lexical_eq_structural (n : Spanish.Gender.Noun) (h : ¬ IsHybrid n) :
    (lexicalEntry n).humanGender.gender = .feminine ↔ determiner (nHead n) = some "la" := by
  rw [lexical_faithful n h, structural_faithful]
  obtain ⟨⟨_, g, _⟩, _⟩ := n
  cases g <;> dsimp only <;> decide

/-! ### Hybrid nouns (§3.3.2) -/

/-- In (27) the agreement targets of *vrač* 'doctor', the Fragment's
morphologically masculine Class I noun, take both genders in one phrase. -/
def hybridTargets : List (String × Gender) := [("xoroš-aja", .feminine), ("glavn-yj", .masculine)]

/-- No lexical entry fits agreement targets of both genders, since an entry has one gender;
the structural account adds a second source of gender features above n. -/
theorem no_lexical_hybrid {targets : List (String × Gender)}
    (hf : ∃ t ∈ targets, t.2 = .feminine) (hm : ∃ t ∈ targets, t.2 = .masculine) :
    ¬ ∃ e : LexicalEntry, ∀ t ∈ targets, t.2 = e.gender := by
  rintro ⟨e, he⟩
  obtain ⟨t, ht, hft⟩ := hf
  obtain ⟨t', ht', hmt⟩ := hm
  exact Gender.noConfusion ((hft.symm.trans (he t ht)).trans (hmt.symm.trans (he t' ht')).symm)

/-- (27) is such a case. -/
theorem lexical_no_hybrid : ¬ ∃ e : LexicalEntry, ∀ t ∈ hybridTargets, t.2 = e.gender :=
  no_lexical_hybrid ⟨_, List.mem_cons_self .., rfl⟩
    ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), rfl⟩

/-! ### Radical interpretability and the semantic core (§3.3.3) -/

/-- The thesis of radical interpretability (29) requires of a language's gender features that
an uninterpretable instantiation of a dimension imply an interpretable one. -/
def RadicallyInterpretable (fs : List GenderFeature) : Prop :=
  ∀ gf ∈ fs, gf.interp = .uninterpretable →
    ∃ gf' ∈ fs, gf'.interp = .interpretable ∧ gf'.val.dim = gf.val.dim

instance (fs : List GenderFeature) : Decidable (RadicallyInterpretable fs) := by
  unfold RadicallyInterpretable; infer_instance

theorem spanish_radicallyInterpretable :
    RadicallyInterpretable (spanishHeads.filterMap (·.gender)) := by decide

/-- Under radical interpretability a language with gender features has an
interpretable one, so some nouns are gendered semantically: the semantic
core, from the structural account. -/
theorem exists_interpretable {fs : List GenderFeature} (h : RadicallyInterpretable fs)
    (hne : fs ≠ []) : ∃ gf ∈ fs, gf.interp = .interpretable := by
  obtain ⟨gf, hgf⟩ := List.exists_mem_of_ne_nil fs hne
  cases hi : gf.interp with
  | interpretable => exact ⟨gf, hgf, hi⟩
  | uninterpretable => obtain ⟨gf', h₁, h₂, -⟩ := h gf hgf hi; exact ⟨gf', h₁, h₂⟩

/-- The lexical account excludes nothing, since a lexicon whose two agreement
classes track no semantic feature is well formed, though no such language
is attested. -/
theorem lexical_allows_arbitrary_only :
    ∃ L : List LexicalEntry, (∀ e ∈ L, e.human = false) ∧
      (∃ e ∈ L, e.gender = .feminine) ∧ ∃ e ∈ L, e.gender = .masculine :=
  ⟨[⟨false, false, true⟩, ⟨false, false, false⟩], by decide⟩

end Kramer2020
