module

public import Linglib.Discourse.Accessibility
public import Linglib.Discourse.Givenness
public import Linglib.Discourse.Centering.Basic
public import Linglib.Data.Examples.Ariel2001

/-!
# Ariel 2001: accessibility theory

Referring expressions are accessibility markers: each codes a degree of mental accessibility
of the representation the addressee is to retrieve, and the eighteen classes of the
Accessibility Marking Scale run from full name with modifier down to zero. The scale is
motivated by three partially overlapping criteria — informativity, rigidity, and
attenuation — each anti-correlated with the accessibility a form codes. The accessibility of
a representation is a composite of the antecedent's salience (discourse topics, speaker and
addressee, frame-induced entities), competition among antecedents, distance, and the unity
between antecedent and anaphor; no single factor decides, as when a topical but distant
antecedent takes the higher marker over a recent non-topical one. Against the rival
theories, the Givenness Hierarchy maps many forms of distinct accessibility to one status
and one form to several, and Centering's pronoun rule is silent on lexical anaphors, so it
does not predict the repeated-name penalty.

## Main definitions

* `head`, `modified`, `lexical`, `full`, `deixis`, `stressed`, `bound`: the form features
  the scale's labels name.
* `Factors`: the accessibility factors, with `Factors.Dominates` the factor-wise comparison.
* `givenness`: the Givenness Hierarchy statuses of the scale's forms, as the paper reports
  them.

## References

* [ariel-2001]
* [ariel-1990] — the scale and its distributional basis
* [gundel-hedberg-zacharski-1993] — the Givenness Hierarchy
* [grosz-joshi-weinstein-1995] — Centering's pronoun rule
-/

@[expose] public section

namespace Ariel2001

open Discourse

/-! ### Form-function criteria (§1.1) -/

theorem informativity_modifier :
    ∀ a b : AccessibilityLevel, a.head = b.head → a.deixis = b.deixis →
      a.modified → ¬ b.modified → a < b := by
  decide

theorem informativity_lexical :
    ∀ a b : AccessibilityLevel, a.head = b.head → a.deixis = b.deixis →
      ¬ a.modified → ¬ b.modified → a.lexical → ¬ b.lexical → a < b := by
  decide

theorem informativity_partial_name :
    ∀ a b : AccessibilityLevel, a.head = .name → b.head = .name →
      ¬ a.modified → ¬ b.modified → a.full → ¬ b.full → a < b := by
  decide

theorem rigidity_full_name :
    ∀ a b : AccessibilityLevel, a.head = .name → a.full → b.head = .description →
      a.modified = b.modified → a < b := by
  decide

theorem rigidity_not_sufficient :
    AccessibilityLevel.shortDefDescription < AccessibilityLevel.lastName := by
  decide

theorem attenuation_stress :
    ∀ a b : AccessibilityLevel, a.head = .pronoun → b.head = .pronoun →
      a.stressed → ¬ b.stressed → a < b := by
  decide

theorem attenuation_reduction :
    ∀ a b : AccessibilityLevel,
      (a.head = .pronoun ∧ b.head = .pronoun ∧ ¬ a.stressed ∧ ¬ a.bound ∧ b.bound) ∨
        (a.head = .pronoun ∧ b.head = .inflection) ∨ (a.head = .inflection ∧ b.head = .zero) →
      a < b := by
  decide

/-- The proximate demonstrative codes higher accessibility than the distal one of the same
shape (§5.1 records Kirsner's Dutch data against this). -/
theorem deixis_proximate :
    ∀ a b : AccessibilityLevel, a.head = .demonstrative → b.head = .demonstrative →
      a.modified = b.modified → a.lexical = b.lexical →
      a.deixis = some Person.first.participantSetsᶜ → b.deixis = some Person.first.participantSets →
        a < b := by
  decide

/-! ### Accessibility as a complex concept (§1.2) -/

/-- The salience of an antecedent by discourse role. -/
inductive Topicality
  | nonTopic
  | localTopic
  | globalTopic
  deriving DecidableEq, Repr

/-- Topicality in increasing order. -/
def Topicality.rank : Topicality → ℕ
  | .nonTopic => 0
  | .localTopic => 1
  | .globalTopic => 2

/-- A degree of accessibility is assessed from distance since the last mention, competing
antecedents, topicality, and the unity of antecedent and anaphor. -/
structure Factors where
  distance : ℕ
  competitors : ℕ
  topicality : Topicality
  tight : Bool
  deriving DecidableEq, Repr

/-- `a` is at least as accessible as `b` on every factor. -/
def Factors.Dominates (a b : Factors) : Prop :=
  a.distance ≤ b.distance ∧ a.competitors ≤ b.competitors ∧
    b.topicality.rank ≤ a.topicality.rank ∧ (b.tight → a.tight)

instance (a b : Factors) : Decidable (a.Dominates b) := by unfold Factors.Dominates; infer_instance

/-- In *Maya kissed Rachel. And then she/SHE …* the first-mentioned Maya is topical but more
distant, Rachel more recent but not topical. -/
def maya : Factors := ⟨2, 1, .localTopic, false⟩

/-- Rachel's factors in the same example. -/
def rachel : Factors := ⟨1, 1, .nonTopic, false⟩

theorem maya_rachel_incomparable : ¬ maya.Dominates rachel ∧ ¬ rachel.Dominates maya := by
  decide

/-- The scale label of a marker feature. -/
def ofLabel : String → Option AccessibilityLevel
  | "fullNameMod" => some .fullNameMod
  | "fullName" => some .fullName
  | "longDefDescription" => some .longDefDescription
  | "shortDefDescription" => some .shortDefDescription
  | "lastName" => some .lastName
  | "firstName" => some .firstName
  | "distalDemMod" => some .distalDemMod
  | "proxDemMod" => some .proxDemMod
  | "distalDemNP" => some .distalDemNP
  | "proxDemNP" => some .proxDemNP
  | "distalDem" => some .distalDem
  | "proxDem" => some .proxDem
  | "stressedPronGesture" => some .stressedPronGesture
  | "stressedPron" => some .stressedPron
  | "unstressedPron" => some .unstressedPron
  | "cliticizedPron" => some .cliticizedPron
  | "verbalAgreement" => some .verbalAgreement
  | "zero" => some .zero
  | _ => none

/-- The marker a row records under a feature. -/
def marker (r : Datum) (key : String) : Option AccessibilityLevel :=
  r.feature? key >>= ofLabel

/-- All the markers a row lists, in order. -/
def markers (r : Datum) : List AccessibilityLevel :=
  (r.features "marker").filterMap ofLabel

theorem rows_topicality_over_distance :
    ∀ r ∈ Examples.all, ∀ m ∈ (marker r "maya").toList, ∀ c ∈ (marker r "rachel").toList,
      c < m := by
  decide +kernel

/-- A newspaper codes the entity whose point of view it takes by the higher accessibility marker
((3), (4)). -/
theorem rows_perspective :
    ∀ r ∈ Examples.all, ∀ v ∈ (marker r "victim").toList, ∀ p ∈ (marker r "rapists").toList,
      (r.feature? "perspective" = some "victim" → p < v) ∧
        (r.feature? "perspective" = some "rapists" → v < p) := by
  decide +kernel

/-- Every referring expression of the article's opening sentence codes lower accessibility than its
counterpart in the headline (8). -/
theorem rows_headline :
    ∀ a ∈ Examples.all, ∀ b ∈ Examples.all,
      a.source.paperLabel = "(8a)" → b.source.paperLabel = "(8b)" →
        ∀ p ∈ (markers a).zip (markers b), p.2 < p.1 := by
  decide +kernel

/-! ### Competing theories (§4) -/

/-- The Givenness Hierarchy statuses of the scale's forms, as the paper reports them for
English: the pronominal forms are all *in focus*, *that*, *this*, stressed *IT*, and *this
N* all *activated*, and a full name *uniquely identifiable* or *familiar*, a partial name
*familiar* or *activated*. -/
def givenness : AccessibilityLevel → Finset GivennessStatus
  | .zero | .verbalAgreement | .cliticizedPron | .unstressedPron => {.inFocus}
  | .stressedPronGesture | .stressedPron | .proxDem | .distalDem | .proxDemNP
  | .proxDemMod => {.activated}
  | .distalDemNP | .distalDemMod => {.familiar}
  | .longDefDescription | .shortDefDescription => {.uniquelyIdentifiable}
  | .fullNameMod | .fullName => {.uniquelyIdentifiable, .familiar}
  | .lastName | .firstName => {.familiar, .activated}

theorem activated_many_forms :
    (∀ l ∈ [AccessibilityLevel.distalDem, .proxDem, .stressedPron, .proxDemNP],
      givenness l = {.activated}) ∧
      ([AccessibilityLevel.distalDem, .proxDem, .stressedPron, .proxDemNP].map
        AccessibilityLevel.rank).Nodup := by
  decide

theorem full_name_two_statuses :
    GivennessStatus.uniquelyIdentifiable ∈ givenness .fullName ∧
      GivennessStatus.familiar ∈ givenness .fullName := by
  decide

theorem in_focus_collapse :
    (∀ l ∈ [AccessibilityLevel.zero, .verbalAgreement, .cliticizedPron, .unstressedPron],
      givenness l = {.inFocus}) ∧
      ([AccessibilityLevel.zero, .verbalAgreement, .cliticizedPron, .unstressedPron].map
        AccessibilityLevel.rank).Nodup := by
  decide

open Discourse.Centering in
theorem pronominalization_vacuous {E R : Type*} [DecidableEq E] [LinearOrder R]
    (prev cur : Utterance E R) (h : ∀ e, ¬ cur.Pronominalizes e) :
    PronominalizationConstraint prev cur :=
  pronominalizationConstraint_of_forall_not h

/-- The discourse topic takes a higher accessibility marker than the local subject (12). -/
theorem rows_topic_over_subject :
    ∀ r ∈ Examples.all, ∀ t ∈ (marker r "topicMarker").toList,
      ∀ s ∈ (marker r "subjectMarker").toList, s < t := by
  decide +kernel

end Ariel2001
