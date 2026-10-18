module

public import Linglib.Morphology.DistributedMorphology.VocabularyInsertion.Basic

/-!
# Konnelly and Cowper (2020): Gender Diversity and Morphosyntax

This file formalizes Konnelly and Cowper's account of singular *they* as a grammatical
change in three stages. A third-person pronoun spells out a bundle of privative features by
the Elsewhere Principle, the vocabulary items of (11) being *she* for [sg][fem], *he* for
[sg][masc], *it* for [sg, inanim] and *they* elsewhere (`items`, `spellout`); the items are
constant across the stages, and what changes is which features a pronoun's antecedent
projects. On the structure (14), [sg] and [inanim] sit on Num and are always copied to the
pronoun, while the gender feature on n is copied only optionally under a quantifier, which is
why (12) *every girl … their* is fine and (13) *every book … their* is not (`quantified`). At
Stage 1, [masc] and [fem] are contrastive and a noun referring to a person of known gender
obligatorily bears one, so *they* needs an antecedent of unknown gender or a quantifier, (5).
At Stage 2 the features are still contrastive but the insertion rule is optional, so an
ungendered name like *Kelly* antecedes *they*, (6), while a lexically gendered noun does not,
(15) and (21), a fact of nominals bearing gender, on which Stages 1 and 2 agree
(`they_not_mem_forms_of_lexical`). At Stage 3 the features are Wiltschko's non-contrastive
modifiers (`Contrastivity`), so *they* is the default for any singular animate antecedent,
(7) and (25), with *he* and *she* still available, (8), and *it* still forced for inanimates,
(10) (`Stage.genders`, `forms`, `stage3_they`, `it_of_inanimate`). Against
Bjorkman's dynamic condition, which asks a pronoun's features to include its
antecedent's, (24) *the women said that she was leaving* is wrongly licensed, whereas the
number contrast excludes it here (`bjorkman_overgenerates`, `women_not_she`).

## Implementation notes

* An antecedent records what the pronoun sees: the Num features, the gender feature n bears
  lexically, the referent's known binary gender that the insertion rule may add, and whether
  D hosts a quantifier. Stage 3's modifier, when present, is the referent's gender, as in
  (26).

## References

* [konnelly-cowper-2020]
* [bjorkman-2017]
* [wiltschko-2008]
-/

@[expose] public section

namespace KonnellyCowper2020

open DistributedMorphology
open scoped DistributedMorphology

/-- The third-person pronoun has the privative features of (11), [sg] and [inanim] on Num and
[masc] and [fem] on n, (14). -/
inductive Feature
  | sg
  | inanim
  | masc
  | fem
  deriving DecidableEq, Repr

/-- The binary gender feature n may bear. -/
inductive Gender
  | masc
  | fem
  deriving DecidableEq, Repr

def Gender.feature : Gender → Feature
  | .masc => .masc
  | .fem => .fem

/-- The class feature a nominal bears lexically, a gender on n or [inanim] on Num, §4.1. -/
inductive Class
  | gender (g : Gender)
  | inanim
  deriving DecidableEq, Repr

/-- The vocabulary items (11), constant across the stages. -/
def items : List (VocabularyItem Feature String) :=
  [{.sg, .fem} ⟷ "she", {.sg, .masc} ⟷ "he", {.sg, .inanim} ⟷ "it", ∅ ⟷ "they"]

/-- The exponent of a feature bundle under the Subset Principle. -/
def spellout (b : List Feature) : Option String := subsetPrinciple items b

theorem spellout_items :
    spellout [.sg, .fem] = some "she" ∧ spellout [.sg, .masc] = some "he" ∧
      spellout [.sg, .inanim] = some "it" ∧ spellout [.sg] = some "they" ∧
      spellout [] = some "they" := by
  decide

/-- A feature is contrastive when its absence conveys its negation, and a non-contrastive
modifier when its absence conveys nothing ([wiltschko-2008]). -/
inductive Contrastivity
  | contrastive
  | nonContrastive
  deriving DecidableEq, Repr

/-- The three stages of the change, §4. -/
inductive Stage
  | one
  | two
  | three
  deriving DecidableEq, Repr

namespace Stage

/-- [masc] and [fem] are contrastive at Stages 1 and 2 and non-contrastive modifiers at
Stage 3, §4.2. -/
def genderContrastivity : Stage → Contrastivity
  | .one | .two => .contrastive
  | .three => .nonContrastive

/-- The rule inserting a known referent's gender on an ungendered noun is obligatory at Stage
1 and optional at Stage 2, §4.1 and §4.2. -/
def insertionObligatory : Stage → Bool
  | .one => true
  | .two | .three => false

end Stage

/-- An antecedent as the pronoun sees it, (14). -/
structure Antecedent where
  singular : Bool
  /-- The class feature the nominal bears lexically, as for *mother*, *Susan* or *watch*. -/
  lexical : Option Class
  /-- The referent's known binary gender, which the insertion rule may place on n. -/
  known : Option Gender
  /-- Whether D hosts a quantifier. -/
  quantified : Bool
  deriving DecidableEq, Repr

namespace Antecedent

variable (a : Antecedent)

def inanimate : Bool := a.lexical = some .inanim

/-- The gender feature n bears lexically. -/
def lexicalGender : Option Gender :=
  match a.lexical with
  | some (.gender g) => some g
  | _ => none

/-- The features of Num, copied to the pronoun in every case. -/
def numFeatures : List Feature :=
  (if a.singular then [.sg] else []) ++ (if a.inanimate then [.inanim] else [])

end Antecedent

/-- The gender features n may bear at a stage. Without a lexical gender, n bears the referent's
known gender obligatorily at Stage 1, optionally at Stage 2, and as a modifier at Stage 3. -/
def Stage.genders (s : Stage) (a : Antecedent) : List (Option Gender) :=
  if a.inanimate then [none] else
  match s.genderContrastivity, a.lexicalGender with
  | .nonContrastive, _ => [none, a.known]
  | .contrastive, some g => [some g]
  | .contrastive, none => (if s.insertionObligatory then [] else [none]) ++ [a.known]

/-- The bundles a pronoun with antecedent `a` may spell out at stage `s`. -/
def bundles (s : Stage) (a : Antecedent) : List (List Feature) :=
  ((if a.quantified then [none] else []) ++ s.genders a).map
    fun g : Option Gender ↦ a.numFeatures ++ (g.map Gender.feature).toList

/-- The pronoun forms available for an antecedent at a stage. -/
def forms (s : Stage) (a : Antecedent) : List String := (bundles s a).filterMap spellout

/-! ### The stages in general -/

/-- A contrastive lexical gender feature is the only option, the source of (15) and (21) at
Stages 1 and 2. -/
theorem lexical_forces_gender {s : Stage} {a : Antecedent} {g : Gender}
    (h : s.genderContrastivity = .contrastive) (hl : a.lexical = some (.gender g)) :
    s.genders a = [some g] := by
  simp [Stage.genders, Antecedent.inanimate, Antecedent.lexicalGender, h, hl]

/-- A singular antecedent outside a quantifier whose entry bears a contrastive gender does not
take *they*, so Stages 1 and 2 agree on nominals bearing gender features, §4.2. -/
theorem they_not_mem_forms_of_lexical {s : Stage} {a : Antecedent} {g : Gender}
    (h : s.genderContrastivity = .contrastive) (hs : a.singular = true)
    (hq : a.quantified = false) (hl : a.lexical = some (.gender g)) : "they" ∉ forms s a := by
  cases g <;>
    simp [forms, bundles, lexical_forces_gender h hl, hq, hs, hl, Antecedent.numFeatures,
      Antecedent.inanimate, Gender.feature] <;> decide

/-- *They* is available whenever the pronoun may omit the gender feature and the antecedent is
not inanimate. -/
theorem they_mem_forms {s : Stage} {a : Antecedent}
    (h : none ∈ s.genders a ∨ a.quantified = true) (hi : a.inanimate = false) :
    "they" ∈ forms s a := by
  refine List.mem_filterMap.2 ⟨a.numFeatures, List.mem_map.2 ⟨none, ?_, by simp⟩, ?_⟩
  · rcases h with h | h
    · exact List.mem_append_right _ h
    · simp [h]
  · cases hs : a.singular <;> simp [Antecedent.numFeatures, hs, hi] <;> decide

/-- At Stage 3 *they* is the default for every animate antecedent, (7) and (25). -/
theorem stage3_they {a : Antecedent} (hi : a.inanimate = false) : "they" ∈ forms .three a :=
  they_mem_forms (Or.inl (by simp [Stage.genders, Stage.genderContrastivity, hi])) hi

/-- A singular inanimate antecedent is *it* at every stage, (10) and (13), since [inanim] sits
on Num and is always copied. -/
theorem it_of_inanimate {s : Stage} {a : Antecedent} (hs : a.singular = true)
    (hi : a.inanimate = true) : ∀ f ∈ forms s a, f = "it" := by
  intro f hf
  obtain ⟨b, hb, hsp⟩ := List.mem_filterMap.1 hf
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hb
  have hg' : g = none := by
    simp only [Stage.genders, hi, ite_true, List.mem_append, List.mem_singleton] at hg
    rcases hg with h | h
    · split at h <;> simp at h; exact h
    · exact h
  subst hg'
  simp only [Antecedent.numFeatures, hs, hi, ite_true, Option.map_none, Option.toList_none,
    List.append_nil, List.singleton_append] at hsp
  rw [(by decide : spellout [.sg, .inanim] = some "it")] at hsp
  exact (Option.some.inj hsp).symm

/-! ### The paper's antecedents -/

/-- (5a) *anyone*, a quantified antecedent of unknown gender. -/
def anyone : Antecedent := ⟨true, none, none, true⟩

/-- (5b) *the person at the door*, a referential antecedent of unknown gender. -/
def thePerson : Antecedent := ⟨true, none, none, false⟩

/-- (6a) *Kelly*, an ungendered name for a referent of known gender. -/
def kelly : Antecedent := ⟨true, none, some .fem, false⟩

/-- (7a) *Maria*, a lexically gendered name. -/
def maria : Antecedent := ⟨true, some (.gender .fem), some .fem, false⟩

/-- (7d) *your brother*, a lexically gendered noun. -/
def yourBrother : Antecedent := ⟨true, some (.gender .masc), some .masc, false⟩

/-- (10) *my favourite watch*, an inanimate antecedent. -/
def theWatch : Antecedent := ⟨true, some .inanim, none, false⟩

/-- (12b) *every girl*, a quantified and lexically gendered antecedent. -/
def everyGirl : Antecedent := ⟨true, some (.gender .fem), none, true⟩

/-- (13) *every book*, a quantified inanimate antecedent. -/
def everyBook : Antecedent := ⟨true, some .inanim, none, true⟩

/-- *the women* of (23) and (24), a plural and lexically gendered antecedent. -/
def theWomen : Antecedent := ⟨false, some (.gender .fem), some .fem, false⟩

/-- At Stage 1, (5) against (6) and (7), *they* takes only a quantified or gender-unknown
antecedent. -/
theorem stage1 :
    "they" ∈ forms .one anyone ∧ "they" ∈ forms .one thePerson ∧ "they" ∉ forms .one kelly ∧
      "they" ∉ forms .one maria := by
  decide +kernel

/-- At Stage 2, (6) against (15) and (21), an ungendered name antecedes *they* and a lexically
gendered one does not. -/
theorem stage2 : "they" ∈ forms .two kelly ∧ "they" ∉ forms .two maria := by decide +kernel

/-- At Stage 3, (7), (8) and (10), every animate antecedent takes *they*, *she* is still
available, and the watch takes *it* alone. -/
theorem stage3 :
    (∀ a ∈ [anyone, thePerson, kelly, maria, yourBrother], "they" ∈ forms .three a) ∧
      "she" ∈ forms .three kelly ∧ forms .three theWatch = ["it"] := by
  decide +kernel

/-- Under a quantifier, (12) and (13), the gender feature on n is optional while [inanim] on Num
is not. -/
theorem quantified :
    "they" ∈ forms .one everyGirl ∧ "she" ∈ forms .one everyGirl ∧
      forms .one everyBook = ["it", "it"] := by
  decide +kernel

/-! ### Bjorkman's dynamic condition, §5 -/

/-- [bjorkman-2017]'s condition requires a referential pronoun's features to include those
already associated with its referent. -/
abbrev BjorkmanCondition (pronoun antecedent : List Feature) : Prop := antecedent ⊆ pronoun

/-- In (23) the pronoun of *the women* bears <fem> without [sg], and no item spells that out but
*they*. -/
theorem bjorkman_women_they : BjorkmanCondition [.fem] [.fem] ∧ spellout [.fem] = some "they" := by
  decide

/-- In (24) a pronoun bearing <fem> and [sg] satisfies the condition for *the women* and spells
out as *she*, which the condition therefore wrongly licenses. -/
theorem bjorkman_overgenerates :
    BjorkmanCondition [.sg, .fem] [.fem] ∧ spellout [.sg, .fem] = some "she" := by
  decide

/-- On the present account the number feature on Num is copied, so a plural antecedent never
yields *she*. -/
theorem women_not_she (s : Stage) : "she" ∉ forms s theWomen := by
  cases s <;> decide +kernel

end KonnellyCowper2020
