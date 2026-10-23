module

public import Linglib.Morphology.DistributedMorphology.VocabularyInsertion.Basic
public import Linglib.Fragments.English.Pronouns
public import Linglib.Data.Examples.KonnellyCowper2020

/-!
# Konnelly and Cowper (2020): gender diversity and morphosyntax

Konnelly and Cowper account for singular *they* as a grammatical change in three stages. A
third-person pronoun spells out by the Elsewhere Principle the features it copies from its
antecedent, *she* for [sg][fem], *he* for [sg][masc], *it* for [sg, inanim] and *they* elsewhere
(11). In the structure (14), [sg] and [inanim] sit on Num and are always copied, while [masc] or
[fem] on n is copied from a referential antecedent and only optionally from a quantified one. The
stages differ in the gender features n may bear. At Stage 1 they are contrastive and a noun for a
referent of known gender must receive one, at Stage 2 that insertion is optional, and at Stage 3
they are Wiltschko's non-contrastive modifiers, so that *they* is available for every singular
animate antecedent. Bjorkman's rival condition, that a pronoun bear a superset of its
antecedent's features, admits (24) *the women said that she was leaving* and excludes the Stage 3
uses of *they*.

## Main definitions

* `KonnellyCowper2020.items`: the vocabulary items (11), those of the English pronouns.
* `KonnellyCowper2020.Stage`, `KonnellyCowper2020.Antecedent`: the stages, ordered, and what a
  pronoun may copy from its antecedent.
* `KonnellyCowper2020.forms`: the pronouns available for an antecedent at a stage.

## Main results

* `spellout_pronounFeatures`, `subsetPrinciple_append_they_sg`: each English third-person
  pronoun spells out its own features, and singular *they* needs no item of its own.
* `they_mem_forms_iff`, `none_mem_genders_one_iff`, `none_mem_genders_two_iff`: where singular
  *they* is available at each stage.
* `monotone_they_mem_forms`: each stage keeps the uses of singular *they* of the stage before.
* `forms_three_lexical`: at Stage 3 the gender a noun bears lexically no longer matters (§6).
* `rows_judgment`, `rows_firstStage`: the examples' judgments, and the stage from which each
  example of singular *they* is grammatical.
* `bjorkman_overgenerates`, `bjorkman_excludes_stage3`: Bjorkman's condition admits (24) and
  excludes every Stage 3 example.

## Implementation notes

The items (11) are read off the English pronoun entries, a neuter bearing [inanim]; the case of a
pronoun is not modelled. An antecedent records its number, whether D hosts a quantifier, the class
its noun bears lexically, and the binary gender the discourse assigns its referent, which the
insertion rule of Stages 1 and 2 may place on n and which Stage 3's modifier expresses, as in
(26). The paper leaves
the gender of some referents open, as for *Kelly* in (6a); a row then says only that it is known,
and the theorems over rows hold for either binary gender.

## References

* [konnelly-cowper-2020]
* [bjorkman-2017]
* [wiltschko-2008]
-/

@[expose] public section

namespace KonnellyCowper2020

open DistributedMorphology
open scoped DistributedMorphology

/-- The privative features of the third-person pronoun (11), [sg] and [inanim] on Num and [masc]
and [fem] on n (14). -/
inductive Feature
  | sg
  | inanim
  | masc
  | fem
  deriving DecidableEq, Repr, Fintype

/-- The binary genders n may bear. -/
inductive Gender
  | masc
  | fem
  deriving DecidableEq, Repr, Fintype

/-- The feature of a gender. -/
def Gender.feature : Gender → Feature
  | .masc => .masc
  | .fem => .fem

/-- The class a noun bears lexically, a gender on n, as for *mother* and *Susan*, or [inanim] on
Num, as for *watch* (§4.1). -/
inductive Class
  | gender (g : Gender)
  | inanim
  deriving DecidableEq, Repr

/-- The features an English third-person pronoun spells out, [sg] for a singular, [masc] or [fem]
for a masculine or feminine, and [inanim] for the neuter *it*. -/
def pronounFeatures (p : PersonalPronoun) : Finset Feature :=
  (if p.number = some .singular then {.sg} else ∅) ∪
    match p.gender with
    | some .masculine => {.masc}
    | some .feminine => {.fem}
    | some .neuter => {.inanim}
    | _ => ∅

/-- The Vocabulary Item of a pronoun spells out its features as its form. -/
def vocabularyItem (p : PersonalPronoun) : VocabularyItem Feature String :=
  pronounFeatures p ⟷ p.form

/-- The vocabulary items (11), those of *she*, *he*, *it* and plural *they*, constant across the
stages. -/
def items : List (VocabularyItem Feature String) :=
  [English.Pronouns.she, English.Pronouns.he, English.Pronouns.it, English.Pronouns.they].map
    vocabularyItem

/-- The items are (11), *she* for [sg][fem], *he* for [sg][masc], *it* for [sg, inanim] and
*they* elsewhere. -/
theorem items_eq :
    items = [{.sg, .fem} ⟷ "she", {.sg, .masc} ⟷ "he", {.sg, .inanim} ⟷ "it", ∅ ⟷ "they"] := by
  decide

/-- The exponent of a feature bundle under the Subset Principle. -/
def spellout (b : Finset Feature) : Option String := subsetPrinciple items b

theorem spellout_pronounFeatures :
    ∀ p ∈ English.Pronouns.pronouns, p.person = some .third → .nom ∈ p.cases →
      spellout (pronounFeatures p) = some p.form := by
  decide

theorem subsetPrinciple_append_they_sg (b : Finset Feature) :
    subsetPrinciple (items ++ [vocabularyItem English.Pronouns.they_sg]) b = spellout b := by
  revert b
  decide

/-- A feature is contrastive when its absence conveys its negation, and a non-contrastive
modifier when its absence conveys nothing ([wiltschko-2008]). -/
inductive Contrastivity
  | contrastive
  | nonContrastive
  deriving DecidableEq, Repr

/-- The three stages of the change (§4). -/
inductive Stage
  | one
  | two
  | three
  deriving DecidableEq, Repr, Fintype

namespace Stage

/-- The stages are ordered as the change proceeds. -/
instance : LinearOrder Stage := LinearOrder.lift' Stage.ctorIdx (by decide)

/-- [masc] and [fem] are contrastive at Stages 1 and 2 and non-contrastive modifiers at Stage 3
(§4.2). -/
def genderContrastivity : Stage → Contrastivity
  | .one | .two => .contrastive
  | .three => .nonContrastive

end Stage

/-- What the D head of an antecedent hosts, a quantifier or, in a referential DP, nothing. -/
inductive Determiner
  | quantifier
  | referential
  deriving DecidableEq, Repr

/-- An antecedent as a pronoun sees it (14). -/
structure Antecedent where
  /-- The number of the antecedent, whose singular is the marked value [sg]. -/
  number : Number
  /-- What its D head hosts. -/
  det : Determiner
  /-- The class its noun bears lexically. -/
  lexical : Option Class
  /-- The binary gender the discourse assigns its referent, if any. -/
  referentGender : Option Gender
  deriving DecidableEq, Repr

namespace Antecedent

variable (a : Antecedent)

/-- The antecedent is inanimate, its noun bearing [inanim]. -/
def Inanimate : Prop := a.lexical = some .inanim

instance : Decidable a.Inanimate := inferInstanceAs (Decidable (_ = _))

/-- The gender its noun bears lexically. -/
def lexicalGender : Option Gender :=
  match a.lexical with
  | some (.gender g) => some g
  | _ => none

/-- The features of Num, copied to the pronoun in every case. -/
def numFeatures : Finset Feature :=
  (if a.number = .singular then {.sg} else ∅) ∪ (if a.Inanimate then {.inanim} else ∅)

end Antecedent

/-- The gender features n may bear at a stage. Without a lexical gender, n bears the referent's
gender obligatorily at Stage 1, optionally at Stage 2, and as a modifier at Stage 3. -/
def Stage.genders (s : Stage) (a : Antecedent) : List (Option Gender) :=
  if a.Inanimate then [none] else
  match s.genderContrastivity, a.lexicalGender with
  | .nonContrastive, _ => [none, a.referentGender]
  | .contrastive, some g => [some g]
  | .contrastive, none => (if s = .one then [] else [none]) ++ [a.referentGender]

/-- The bundles a pronoun with antecedent `a` may spell out at stage `s`, the features of Num with
the gender of n where it is copied, which a quantifier makes optional. -/
def bundles (s : Stage) (a : Antecedent) : List (Finset Feature) :=
  List.map (fun g ↦ a.numFeatures ∪ (g.map Gender.feature).toFinset)
    ((if a.det = .quantifier then [none] else []) ++ s.genders a)

/-- The pronoun forms available for an antecedent at a stage. -/
def forms (s : Stage) (a : Antecedent) : List String := (bundles s a).filterMap spellout

/-! ### Singular *they* across the stages -/

variable {s : Stage} {a : Antecedent}

/-- A contrastive lexical gender is the only option, the source of (15) and (21) at Stages 1
and 2. -/
theorem lexical_forces_gender {g : Gender} (h : s.genderContrastivity = .contrastive)
    (hl : a.lexical = some (.gender g)) : s.genders a = [some g] := by
  simp [Stage.genders, Antecedent.Inanimate, Antecedent.lexicalGender, h, hl]

theorem they_mem_forms (h : none ∈ s.genders a ∨ a.det = .quantifier) (hi : ¬ a.Inanimate) :
    "they" ∈ forms s a := by
  refine List.mem_filterMap.2 ⟨a.numFeatures, List.mem_map.2 ⟨none, ?_, by simp⟩, ?_⟩
  · rcases h with h | h
    · exact List.mem_append_right _ h
    · simp [h]
  · by_cases hs : a.number = .singular <;> simp [Antecedent.numFeatures, hs, hi] <;> decide

theorem they_mem_forms_iff (hs : a.number = .singular) (hi : ¬ a.Inanimate) :
    "they" ∈ forms s a ↔ a.det = .quantifier ∨ none ∈ s.genders a := by
  refine ⟨fun h ↦ ?_, fun h ↦ they_mem_forms h.symm hi⟩
  obtain ⟨b, hb, hsp⟩ := List.mem_filterMap.1 h
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hb
  cases g with
  | none =>
    rcases List.mem_append.1 hg with hg | hg
    · split at hg
      · exact .inl ‹_›
      · simp at hg
    · exact .inr hg
  | some g =>
    exfalso
    cases g <;> simp [Antecedent.numFeatures, hs, hi, Gender.feature] at hsp <;> revert hsp <;>
      decide

/-- At Stage 1, n of an animate antecedent may lack a gender only for a noun with none whose
referent's gender is unknown (5). -/
theorem none_mem_genders_one_iff (hi : ¬ a.Inanimate) :
    none ∈ Stage.one.genders a ↔ a.lexical = none ∧ a.referentGender = none := by
  rcases a with ⟨n, d, _ | _ | _, r⟩ <;>
    simp_all [Stage.genders, Antecedent.Inanimate, Antecedent.lexicalGender,
      Stage.genderContrastivity, eq_comm]

/-- At Stage 2, n of an animate antecedent may lack a gender exactly when its noun bears none
(6), (21). -/
theorem none_mem_genders_two_iff (hi : ¬ a.Inanimate) :
    none ∈ Stage.two.genders a ↔ a.lexical = none := by
  rcases a with ⟨n, d, _ | _ | _, r⟩ <;>
    simp_all [Stage.genders, Antecedent.Inanimate, Antecedent.lexicalGender,
      Stage.genderContrastivity]

theorem none_mem_genders_three (hi : ¬ a.Inanimate) : none ∈ Stage.three.genders a := by
  simp [Stage.genders, Stage.genderContrastivity, hi]

/-- At Stage 3 *they* is the default for every animate antecedent, (7) and (25). -/
theorem stage3_they (hi : ¬ a.Inanimate) : "they" ∈ forms .three a :=
  they_mem_forms (.inl (none_mem_genders_three hi)) hi

/-- A singular antecedent outside a quantifier whose noun bears a contrastive gender does not
take *they*, so Stages 1 and 2 agree on nouns bearing gender (§4.2). -/
theorem they_not_mem_forms_of_lexical {g : Gender} (h : s.genderContrastivity = .contrastive)
    (hs : a.number = .singular) (hq : a.det = .referential) (hl : a.lexical = some (.gender g)) :
    "they" ∉ forms s a := by
  rw [they_mem_forms_iff hs (by simp [Antecedent.Inanimate, hl]), lexical_forces_gender h hl]
  simp [hq]

/-- Each stage keeps the uses of singular *they* of the stage before (§4). -/
theorem monotone_they_mem_forms (hs : a.number = .singular) (hi : ¬ a.Inanimate) :
    Monotone fun s ↦ "they" ∈ forms s a := by
  intro s t hst h
  rw [they_mem_forms_iff hs hi] at h ⊢
  refine h.imp id fun hn ↦ ?_
  cases s <;> cases t <;> first
    | exact hn
    | exact absurd hst (by decide)
    | exact none_mem_genders_three hi
    | exact (none_mem_genders_two_iff hi).2 ((none_mem_genders_one_iff hi).1 hn).1

/-- At Stage 3 the gender a noun bears lexically has no consequences for the pronouns it
antecedes, which depend on the gender of its referent alone (§6). -/
theorem forms_three_lexical {l : Option Class} (hl : l ≠ some .inanim) (hi : ¬ a.Inanimate) :
    forms .three { a with lexical := l } = forms .three a := by
  rw [Antecedent.Inanimate] at hi
  simp [forms, bundles, Stage.genders, Stage.genderContrastivity, Antecedent.numFeatures,
    Antecedent.Inanimate, hl, hi]

/-- A singular inanimate antecedent is *it* at every stage, (10) and (13), since [inanim] sits on
Num and is always copied. -/
theorem it_of_inanimate (hs : a.number = .singular) (hi : a.Inanimate) :
    ∀ f ∈ forms s a, f = "it" := by
  intro f hf
  obtain ⟨b, hb, hsp⟩ := List.mem_filterMap.1 hf
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hb
  have hg' : g = none := by
    simp only [Stage.genders, hi, ite_true, List.mem_append, List.mem_singleton] at hg
    rcases hg with h | h
    · split at h <;> simp at h; exact h
    · exact h
  subst hg'
  simp only [Antecedent.numFeatures, hs, hi, ite_true, Option.map_none, Option.toFinset_none,
    Finset.union_empty, Finset.singleton_union] at hsp
  rw [(by decide : spellout {.sg, .inanim} = some "it")] at hsp
  exact (Option.some.inj hsp).symm

/-! ### The examples -/

/-- The antecedent a row describes, with `g` as the gender of a referent the row says only is
known. -/
def Antecedent.ofRow (g : Gender) (e : Datum) : Option Antecedent := do
  let det ← e.parse? "antecedent" [("quantified", .quantifier), ("referential", .referential)]
  let lexical ← e.parse? "noun" [("ungendered", none), ("fem", some (.gender .fem)),
    ("masc", some (.gender .masc)), ("inanimate", some .inanim)]
  let referentGender ← e.parse? "referent"
    [("unknown", none), ("known", some g), ("fem", some .fem), ("masc", some .masc)]
  pure ⟨if e.feature? "number" = some "plural" then .plural else .singular, det, lexical,
    referentGender⟩

/-- The stage a row's feature `key` names. -/
def Stage.ofRow? (key : String) (e : Datum) : Option Stage :=
  e.parse? key [("1", .one), ("2", .two), ("3", .three)]

theorem rows_described :
    ∀ e ∈ Examples.all, ∀ g, (Antecedent.ofRow g e).isSome ∧ (e.feature? "pronoun").isSome ∧
      ((Stage.ofRow? "stage" e).isSome ∨ (Stage.ofRow? "firstStage" e).isSome) := by
  decide +kernel

theorem rows_judgment :
    ∀ e ∈ Examples.all, ∀ g, ∀ a ∈ Antecedent.ofRow g e, ∀ p ∈ e.feature? "pronoun",
      ∀ s ∈ Stage.ofRow? "stage" e, (p ∈ forms s a ↔ e.judgment = .acceptable) := by
  decide +kernel

/-- An example of Stage `k` singular *they*, (1), (3)–(7), (12), (16) and (25), is grammatical
from Stage `k` on and not before. -/
theorem rows_firstStage :
    ∀ e ∈ Examples.all, ∀ g, ∀ a ∈ Antecedent.ofRow g e, ∀ p ∈ e.feature? "pronoun",
      ∀ k ∈ Stage.ofRow? "firstStage" e, ∀ s, (p ∈ forms s a ↔ k ≤ s) := by
  decide +kernel

/-! ### Bjorkman's dynamic condition, §5 -/

/-- [bjorkman-2017]'s condition requires a referential pronoun's features to include those
already associated with its referent. -/
abbrev BjorkmanCondition (pronoun antecedent : Finset Feature) : Prop := antecedent ⊆ pronoun

/-- The features a discourse associates with an antecedent, those of its Num and of its noun. -/
def Antecedent.features (a : Antecedent) : Finset Feature :=
  a.numFeatures ∪ (a.lexicalGender.map Gender.feature).toFinset

/-- In (23) the pronoun of *the women* bears <fem> without [sg], and no item spells that out but
*they*. -/
theorem bjorkman_women_they : BjorkmanCondition {.fem} {.fem} ∧ spellout {.fem} = some "they" := by
  decide

/-- In (24) a pronoun bearing <fem> and [sg] satisfies the condition for *the women* and spells
out as *she*, which the condition therefore wrongly licenses. -/
theorem bjorkman_overgenerates :
    BjorkmanCondition {.sg, .fem} {.fem} ∧ spellout {.sg, .fem} = some "she" := by
  decide

/-- Every example of Stage 3 singular *they*, (4), (7) and (25), fails Bjorkman's condition, since
its noun bears a gender that *they* lacks, though the Stage 3 grammar admits it (§5.3). -/
theorem bjorkman_excludes_stage3 :
    ∀ e ∈ Examples.all, ∀ g, ∀ a ∈ Antecedent.ofRow g e, Stage.ofRow? "firstStage" e = some .three →
      ¬ BjorkmanCondition a.numFeatures a.features := by
  decide +kernel

end KonnellyCowper2020
