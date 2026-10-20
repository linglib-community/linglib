module

public import Studies.Bondarenko2022
public import Studies.Roussou2010
public import Linglib.Fragments.Greek.StandardModern.Complementizers
public import Linglib.Fragments.Greek.StandardModern.Verbs
public import Linglib.Syntax.Category.Verb.ArgumentFrame.Takes
public import Linglib.Semantics.Attitudes.Anchor
public import Linglib.Data.Examples.Angelopoulos2026

/-!
# Angelopoulos 2026: on clausal complementation, once more

Greek *oti*- and *pu*-clauses are in near-complementary distribution after verbs, are internal
arguments and derived subjects but never external arguments, and a *pu*-complement forces a
stative matrix verb where adverbial and relative *pu* does not. The analysis reverses selection:
*oti* and *pu* carry an [n]-feature checked by a light noun in their specifier, which must
incorporate into a lexical verbal head — possible from the complement position but not from
Spec,vP, whose nearest host is T, nor after P. The complementizers sort their clauses as content
(*oti*) and situation (*pu*), and the incorporating noun must match, so a verb's sort fixes its
complementizer; situations anchor to the evaluation world, whence *pu*'s factivity. The stativity
restriction is the selectional feature of the aspectual heads introducing internal arguments:
vState takes otiP or puP, vEvent only otiP, and adjunct *pu*, which selects its host rather than
being selected, escapes it. Bare *oti*-clauses are true complements that compose as modifiers,
against the transparent syntax–semantics mapping.

## Main definitions

* `clauseSort`: the sort a complementizer imposes; `selectsClause` the aspectual heads'
  selection (§4.1).
* `Predicted`: a verb–complementizer pairing derived from the verb's sort and Vendler class,
  with the sample verbs' sorts in `lexicon`.
* `licensedIn`: incorporation licensing by clause position (§3.1).

## References

* [angelopoulos-2026]
* [arsenijevic-2009] — the light noun in the complementizer's specifier
* [bondarenko-2022] — content and situation; the transparent mapping contested in §7.3
* [elliott-2020-embedding] — explanans by Predicate Modification
* [hale-keyser-1993] — incorporation into lexical heads
* [roussou-2010] — *oti* and *pu* as distinct lexical items
-/

@[expose] public section

namespace Angelopoulos2026

open Greek.StandardModern.Complementizers Greek.StandardModern.Verbs
open Bondarenko2022 (NominalSort CompositionPath)
open Aspect
open Anchor (existsClosure)

/-! ### Sorts and aspectual selection -/

/-- The sort of clause each complementizer introduces — *oti* content, *pu* situation, *na*
neither (§3.2); the sorted complementizers are the light-noun selectors of §3.1. -/
def clauseSort (c : Complementizer) : Option NominalSort :=
  if c = oti then some .content else if c = pu then some .situation else none

/-- Aspectual heads introducing internal arguments (§4.1). -/
inductive AspectualHead
  | vState
  | vEvent
  deriving DecidableEq

/-- The aspectual head a verb's Vendler class determines. -/
def AspectualHead.ofVendler (vc : VendlerClass) : AspectualHead :=
  match vc.dynamicity with
  | .stative => .vState
  | .dynamic => .vEvent

/-- vState selects otiP or puP, vEvent only otiP — the stativity restriction as a selectional
feature (§4.1, fn. 19). -/
def selectsClause : AspectualHead → Complementizer → Prop
  | .vState, c => c = oti ∨ c = pu
  | .vEvent, c => c = oti

instance (h : AspectualHead) (c : Complementizer) : Decidable (selectsClause h c) := by
  cases h <;> unfold selectsClause <;> infer_instance

/-- A *pu*-complement forces the stative head (§2.3). -/
theorem pu_requires_stative {h : AspectualHead} (hp : selectsClause h pu) : h = .vState := by
  cases h
  · rfl
  · exact absurd (show pu = oti from hp) (by decide)

/-- A verb of sort `s` takes complementizer `c` iff `c` imposes `s` and the verb's aspectual
head selects `c`'s clause. -/
def Predicted (v : Verb) (s : NominalSort) (c : Complementizer) : Prop :=
  clauseSort c = some s ∧
    ∀ h ∈ (v.vendlerClass.map AspectualHead.ofVendler).toList, selectsClause h c

instance (v : Verb) (s : NominalSort) (c : Complementizer) : Decidable (Predicted v s c) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The sample verbs with the sort of noun each verbalizes (§3.2, where saying, belief, and
knowledge verbs are content-denoting like *rumor*, emotive factives situation-denoting like
*sadness*), keyed as in the example rows; *thimame* splits into its attitude and perception
senses (fn. 16), and *simveni* 'happen' is a situation verb (fn. 14). -/
def lexicon : List (String × Verb × NominalSort) :=
  [("leo", leo, .content), ("pistevo", pistevo, .content), ("ksero", ksero, .content),
    ("katalaveno", katalaveno, .content), ("sinidhitopio", sinidhitopio, .content),
    ("eksigo", eksigo, .content), ("thimame", thimame, .content),
    ("metaniono", metaniono, .situation), ("areso", areso, .situation),
    ("xerome", xerome, .situation), ("thimame_perception", thimameStat, .situation),
    ("thimono_stative", thimonoStat, .situation), ("simveni", simveni, .situation)]

def Complementizer.ofString? : String → Option Complementizer
  | "oti" => some oti
  | "pu" => some pu
  | _ => none

/-- Every verb–complementizer pairing in the paper's examples, apart from those testing an
adverb, a factivity continuation or the ban on a preposition, is acceptable exactly when
predicted from the verb's sort and Vendler class — including *simveni*, which no complementizer
fits (fn. 14). -/
theorem rows_track_selection :
    ∀ r ∈ Examples.all, r.feature? "confound" = none →
      ∀ e ∈ ((r.feature? "verb").bind fun name ↦ lexicon.lookup name).toList,
        ∀ c ∈ ((r.feature? "complementizer").bind Complementizer.ofString?).toList,
          (r.judgment = .acceptable ↔ Predicted e.1 e.2 c) := by
  decide +kernel

/-- Under a manner adverb or an in-adverbial, a *pu*-complement is never acceptable while an
*oti*-complement of an eventive verb is (§2.3). -/
theorem rows_stativity :
    ∀ r ∈ Examples.all, r.feature? "confound" = some "manner_adverb" →
      ∀ c ∈ ((r.feature? "complementizer").bind Complementizer.ofString?).toList,
        (r.judgment = .acceptable ↔ c = oti) := by
  decide +kernel

/-! ### Incorporation licensing and the argument asymmetry (§3.1) -/

/-- Heads adjacent to a clause's light noun. -/
inductive NounHost
  | vLex
  | t
  | p
  deriving DecidableEq

/-- Only a lexical verbal head hosts light-noun incorporation; T and P do not. -/
def NounHost.licenses : NounHost → Prop
  | .vLex => True
  | .t => False
  | .p => False

instance : DecidablePred NounHost.licenses
  | .vLex => isTrue trivial
  | .t => isFalse id
  | .p => isFalse id

/-- Positions a bare clause can be merged in. -/
inductive ClausePosition
  | internalArgument
  | derivedSubject
  | externalArgument
  | pComplement
  deriving DecidableEq

/-- The nearest potential host of a position is the aspectual v for the complement position
(before any movement to subject), T for Spec,vP, and P after a preposition. -/
def ClausePosition.nearestHost : ClausePosition → NounHost
  | .internalArgument => .vLex
  | .derivedSubject => .vLex
  | .externalArgument => .t
  | .pComplement => .p

/-- A bare clause is licensed where its nearest host licenses incorporation. -/
def licensedIn (pos : ClausePosition) : Prop := pos.nearestHost.licenses

instance : DecidablePred licensedIn := fun pos ↦
  inferInstanceAs (Decidable pos.nearestHost.licenses)

def ClausePosition.ofString? : String → Option ClausePosition
  | "internal_argument" => some .internalArgument
  | "derived_subject" => some .derivedSubject
  | "external_argument" => some .externalArgument
  | "p_complement" => some .pComplement
  | _ => none

/-- Across the paper's bare clauses, grammaticality in a position is incorporation licensing
from it: internal arguments and derived subjects in, external arguments and P-complements
out. Nominalized clauses carry a full noun and are exempt (§5). -/
theorem rows_track_licensing :
    ∀ r ∈ Examples.all, r.feature? "nominalized" = none →
      ∀ pos ∈ ((r.feature? "position").bind ClausePosition.ofString?).toList,
        (licensedIn pos ↔ r.judgment ≠ .ungrammatical) := by
  decide +kernel

/-! ### Content and situation (§3.2) -/

def NominalSort.ofString? : String → Option NominalSort
  | "content" => some .content
  | "situation" => some .situation
  | _ => none

/-- On nouns and nominalized verbs, truth predicates accept content and reject situations, and
occurrence predicates do the reverse ((33)–(34), (36)–(37)). -/
theorem rows_sort_diagnostics :
    ∀ r ∈ Examples.all, ∀ s ∈ ((r.feature? "nounSort").bind NominalSort.ofString?).toList,
      (r.feature? "diagnostic" = some "truth-predicates" →
        (r.judgment = .acceptable ↔ s.truthEvaluable)) ∧
      (r.feature? "diagnostic" = some "occurrence-predicates" →
        (r.judgment = .acceptable ↔ s.occurrenceCompatible)) := by
  decide +kernel

/-- The situation-sorted complementizer is the lexically factive one. -/
theorem situation_clause_factive :
    ∀ c ∈ complementizers, clauseSort c = some .situation → c.factive = true := by
  decide

/-- *oti* and *pu* are distinct lexical items here (content vs situation) as in
[roussou-2010] (indefinite vs definite), against fn. 17's allomorphy alternative. -/
theorem oti_pu_lexically_distinct :
    clauseSort oti ≠ clauseSort pu ∧ Roussou2010.profile oti ≠ Roussou2010.profile pu := by
  decide

/-! ### Factivity from situation semantics (§3.2) -/

/-- A situation verb is anchored when it relates agents only to situations realized at the
evaluation situation. -/
def Anchored {S X : Type*} (verb : X → SituationIndividual S → S → Prop) : Prop :=
  ∀ a xs s, verb a xs s → xs.sit s

/-- An anchored verb's *pu*-report entails its complement — *pu*'s factivity from situation
semantics (38b). -/
theorem pu_report_factive {S X : Type*} {verb : X → SituationIndividual S → S → Prop}
    (h : Anchored verb) (a : X) (q : S → Prop) (s : S) : existsClosure verb a q s → q s := by
  rintro ⟨xs, hv, hq⟩
  rw [← show xs.sit = q from hq]
  exact h a xs s hv

/-- Content reports carry no such entailment (38a). -/
theorem content_report_not_factive :
    ¬ ∀ (verb : Unit → ContentIndividual Bool → Bool → Prop) (a : Unit) (p : Bool → Prop)
        (w : Bool), existsClosure verb a p w → p w :=
  fun h ↦ h (fun _ _ _ ↦ True) () (fun _ ↦ False) true ⟨⟨fun _ ↦ False⟩, trivial, rfl⟩

/-! ### Against the transparent syntax–semantics mapping (§7.3) -/

/-- A clitic-doubled bare *oti*-clause is a complement with the explanans reading, composing
as a modifier: the cell [bondarenko-2022]'s transparent mapping leaves empty is filled. -/
theorem transparency_conflates_axes :
    ¬ Bondarenko2022.transparentSSMapping .bareArgument ∧
      ∃ r ∈ Examples.all, r.feature? "position" = some "internal_argument" ∧
        r.feature? "diagnostic" = some "clitic-doubling" ∧
        r.feature? "composition" = some "predicate_modification" :=
  ⟨Bondarenko2022.not_transparentSSMapping_bareArgument, by decide +kernel⟩

end Angelopoulos2026
