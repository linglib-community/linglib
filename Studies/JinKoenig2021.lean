module

public import Linglib.Data.Examples.JinKoenig2021
public import Linglib.Logic.Modal.Defs
public import Linglib.Semantics.Tense.RunTimes
public import Linglib.Semantics.Conditionals.Basic
public import Linglib.Fragments.English.Verbs.Inventory
public import Linglib.Fragments.English.Negation
public import Linglib.Fragments.Romance.French.Negation
public import Linglib.Fragments.Januubi.Negation
public import Linglib.Fragments.Mandarin.Negation
public import Linglib.Fragments.ZarmaSonrai.Negation
public import Linglib.Data.Examples.Readers
public import Linglib.Data.Examples.Languages

/-!
# Jin and Koenig (2021): A Cross-Linguistic Study of Expletive Negation

Jin and Koenig restrict expletive negation to a negator in the dependent of a lexical item that
the item's meaning triggers and that contributes no negation to the dependent's proposition. They
find the same classes of triggers in English, French, Januubi, Mandarin and Zarma-Sonrai, and
explain the likeness by what a trigger's meaning entails: the negation of its argument, in some
worlds or at some time, which a speaker planning the argument then also produces. An attitude verb
triggers when [it is a negative preference or implies that its complement is
false](##JinKoenig2021.english_triggers), as *fear* and *forget* do and [*hope* and *remember* do
not](##JinKoenig2021.not_english_triggers). *Deny* asserts the negation and [*doubt* only invites
it](##JinKoenig2021.doubt_not_entails), which is why *doubt* wants a negated or questioned matrix.
Where a language has a choice of negator, [its form follows from where the negation
holds](##JinKoenig2021.mandarin_negators): Mandarin uses the prohibitive negator [exactly in the
*fear* class](##JinKoenig2021.ENConcept.imperative_mem_mandarinKinds_iff), where the negation
holds in the holder's desires.

## Implementation notes

* The survey tables, Tables 1 to 4, are counts over a convenience sample that the paper itself
  declines to draw inferences from; they are not encoded, and neither is the production model.
* The paper states the negative inference of each trigger informally. It is proved here for the
  operators the library gives a meaning to. For the attitude verbs it is read off the entry: the
  implicative signature for *forget* and *prevent*, and the valence of the preference for *fear*,
  a label that no semantics of fearing yet backs.
* *Before* is Anscombe's *before ever*, which does not entail that its clause ever holds, so only
  the negative inference of the paper's analysis is derived. The logical triggers have no positive
  inference in the paper either.
* The comparative condition is stated of one individual at two degrees, the table of inferences
  states it of the standard at two degrees, and the text of the individual and the standard at one
  degree. The text's version is the one the library's comparative delivers.
* Under *fear* the paper reports the Januubi prohibitive *laa* without an example, so no row
  records it.

## TODO

* Derive *fear*'s negative inference, that the holder wants the negation of the complement, from a
  semantics of fearing.

## References

* [jin-koenig-2021]
* [heim-1992]
* [dell-1986]
* [anscombe-1964]
-/

@[expose] public section

namespace JinKoenig2021

/-! ### Trigger classes and licensing conditions (Tables 5 and 6, (13)) -/

/-- The four necessary conditions on a trigger, (13a) to (13d). -/
inductive Condition where
  /-- The meaning entails or implies `Operator₁ p` and `Operator₂ ¬p`, the two true in different
  sets of worlds. -/
  | attitude
  /-- The meaning entails or implies two times, at which `p` and `¬p` are true. -/
  | temporal
  /-- The meaning includes a negation. -/
  | logical
  /-- The meaning entails a property of one degree and its negation of another. -/
  | comparative
  deriving DecidableEq, Repr, Fintype

/-- The trigger classes of Table 5, each named by a representative concept, the grouping being
one of convenience. -/
inductive ENTriggerClass where
  | fear
  | regret
  | deny
  | forget
  | temporals
  | impossible
  | without
  | unless
  | comparatives
  deriving DecidableEq, Repr, Fintype

/-- The condition under which the paper analyses a class, by the subsections of Section 6. -/
def ENTriggerClass.condition : ENTriggerClass → Condition
  | .fear | .regret | .deny | .forget => .attitude
  | .temporals => .temporal
  | .impossible | .without | .unless => .logical
  | .comparatives => .comparative

/-- The trigger concepts of Table 6, one representative per subclass. -/
inductive ENConcept where
  | fear
  | avoid
  | regret
  | complain
  | adviseAgainst
  | deny
  | hide
  | despair
  | forget
  | delay
  | refuse
  | stop
  | prevent
  | almost
  | barely
  | before
  | cannotWait
  | since
  | rarely
  | impossible
  | difficult
  | without
  | unless
  | onlyDependsOn
  | moreThan
  | lessThan
  | differentThan
  | tooTo
  deriving DecidableEq, Repr, Fintype

namespace ENConcept

/-- The class of a concept. -/
def cls : ENConcept → ENTriggerClass
  | .fear | .avoid => .fear
  | .regret | .complain | .adviseAgainst => .regret
  | .deny | .hide | .despair => .deny
  | .forget | .delay | .refuse | .stop | .prevent | .almost | .barely => .forget
  | .before | .cannotWait | .since | .rarely => .temporals
  | .impossible | .difficult => .impossible
  | .without => .without
  | .unless | .onlyDependsOn => .unless
  | .moreThan | .lessThan | .differentThan | .tooTo => .comparatives

end ENConcept

/-! ### Negative inferences of the operators (Sections 6.2 to 6.4) -/

open Tense in
-- BEFORE: at a time of the main clause the *before*-clause does not hold, (13b).
example {T : Type*} [LinearOrder T] {A B : Set (NonemptyInterval T)} (h : beforeEver A B) :
    ∃ t ∈ timeTrace A, t ∉ timeTrace B :=
  h.exists_notMem

-- WITHOUT: *q without p* is `q` and not `p`, the negation in the meaning, (13c).
example {W : Type*} (q p : Set W) : q \ p ⊆ pᶜ := fun _ h ↦ h.2

-- UNLESS: *q unless p* supposes `¬p`, the negation in the meaning, (13c).
example {W : Type*} {q p : Set W} {w : W} (h : w ∈ Conditional.materialImp pᶜ q) (hp : w ∉ p) :
    w ∈ q :=
  h hp

-- MORE THAN, TOO…TO: the individual exceeds every degree of the clause, which is therefore false
-- at the individual's own degree, (13d).
example {α : Type*} [Preorder α] {Δ : Set α} {d : α} (h : d ∈ strictUpperBounds Δ) : d ∉ Δ :=
  fun hd ↦ lt_irrefl d (h hd)

/-! ### Denying and doubting (Section 6.1.3) -/

open ModalLogic in
/-- *Deny* asserts the negation of its complement, the necessity of `¬p` along what the holder
says or believes, and *doubt*, the failure of the necessity of `p`, does not entail it: the
holder may believe neither. Its negative inference is an invited one, and not doubting does
entail believing. -/
theorem doubt_not_entails :
    (¬ ∀ (W : Type) (R : SetRel W W) (p : W → Prop) (w : W), ¬ □[R] p w → □[R] pᶜ w) ∧
      ∀ (W : Type) (R : SetRel W W) (p : W → Prop) (w : W), ¬ ¬ □[R] p w → □[R] p w :=
  ⟨fun h ↦ h Bool .univ (· = true) true (fun hb ↦ Bool.false_ne_true (hb false trivial)) true
    trivial rfl, fun _ _ _ _ ↦ not_not.1⟩

/-! ### Verbal triggers (Section 6.1) -/

/-- A verb triggers expletive negation when it is a negative-valence preferential attitude, whose
holder wants the negation of the complement (*fear*, *regret*), or its affirmation implies the
negation of its complement in the real world (*forget*, *prevent*). -/
def IsExpletiveNegationTrigger (v : Verb) : Prop :=
  v.attitude.bind Attitude.valence = some .negative ∨ v.implicative.positive = .some .negative

instance : DecidablePred IsExpletiveNegationTrigger := fun _ ↦
  inferInstanceAs (Decidable (_ ∨ _))

open English
open English.Verbs hiding Verb

/-- *Fear*, *dread*, *worry* and *regret* trigger as negative preferences, and *forget* and
*prevent* as verbs implying that their complement is false. -/
theorem english_triggers :
    IsExpletiveNegationTrigger fear.toVerb ∧ IsExpletiveNegationTrigger dread.toVerb ∧
      IsExpletiveNegationTrigger worry.toVerb ∧ IsExpletiveNegationTrigger regret.toVerb ∧
      IsExpletiveNegationTrigger forget.toVerb ∧ IsExpletiveNegationTrigger prevent.toVerb := by
  decide

/-- The minimal pairs of the definition: *wish* and *hope* beside *fear*, (3), and *remember* and
*manage* beside *forget*, (4), do not trigger. -/
theorem not_english_triggers :
    ¬ IsExpletiveNegationTrigger wish.toVerb ∧ ¬ IsExpletiveNegationTrigger hope.toVerb ∧
      ¬ IsExpletiveNegationTrigger remember.toVerb ∧
      ¬ IsExpletiveNegationTrigger manage.toVerb := by
  decide

/-! ### The examples -/

/-- The five languages of Section 4. -/
inductive Language
  | english
  | french
  | januubi
  | mandarin
  | zarmaSonrai
  deriving DecidableEq, Repr

open Negation in
/-- The standard negators of a language, from its fragment. -/
def Language.standard : Language → List Marker
  | .english => English.Negation.standard
  | .french => French.Negation.standard
  | .januubi => Januubi.Negation.standard
  | .mandarin => Mandarin.Negation.negators.map (·.marker)
  | .zarmaSonrai => ZarmaSonrai.Negation.standard

open Negation in
/-- The negators of a language's fragment, under the forms the rows cite them by. -/
def Language.negators : Language → List (String × Marker)
  | .english => [("not", English.Negation.not)]
  | .french => [("ne pas", French.Negation.nePas), ("ne", French.Negation.ne)]
  | .januubi => [("maa", Januubi.Negation.maa), ("laa", Januubi.Negation.laa)]
  | .mandarin =>
    [("bù", Mandarin.Negation.bu.marker), ("méi", Mandarin.Negation.mei.marker),
      ("bié", Mandarin.Negation.bie), ("bùgāi", Mandarin.Negation.bugai)]
  | .zarmaSonrai =>
    [("si", ZarmaSonrai.Negation.si), ("mana", ZarmaSonrai.Negation.mana),
      ("sinda", ZarmaSonrai.Negation.sinda)]

/-- An example uses the standard negator, a dedicated expletive negator (French *ne* alone), an
imperative negator (Mandarin *bié*), a deontic one (Mandarin *bùgāi*) or a copular one
(Zarma-Sonrai *sinda*). -/
inductive NegatorKind
  | standard
  | dedicated
  | imperative
  | deontic
  | copular
  deriving DecidableEq, Repr

/-- A row records the language, the trigger concept, the negator and its kind. -/
structure Row where
  language : Language
  concept : ENConcept
  negator : Negation.Marker
  kind : NegatorKind
  deriving DecidableEq

def languageOf (l : Glottocode) : Option Language :=
  List.lookup l [(.english, .english), (.french, .french), (.gulfArabic, .januubi),
    (.mandarinChinese, .mandarin), (.zarmaKaado, .zarmaSonrai)]

def conceptOf : String → Option ENConcept
  | "fear" => some .fear
  | "avoid" => some .avoid
  | "regret" => some .regret
  | "complain" => some .complain
  | "deny" => some .deny
  | "hide" => some .hide
  | "forget" => some .forget
  | "delay" => some .delay
  | "barely" => some .barely
  | "before" => some .before
  | "cannotWait" => some .cannotWait
  | "rarely" => some .rarely
  | "onlyDependsOn" => some .onlyDependsOn
  | "differentThan" => some .differentThan
  | "tooTo" => some .tooTo
  | _ => none

def kindOf : String → Option NegatorKind
  | "standard" => some .standard
  | "dedicated" => some .dedicated
  | "imperative" => some .imperative
  | "deontic" => some .deontic
  | "copular" => some .copular
  | _ => none

/-- A row from the paper's features. -/
def Row.ofDatum (e : Datum) : Option Row := do
  let l ← languageOf e.language
  let c ← (e.feature? "concept").bind conceptOf
  let n ← e.parse? "negator" l.negators
  let k ← (e.feature? "negator_kind").bind kindOf
  some ⟨l, c, n, k⟩

/-- The examples of Sections 1, 2 and 6. -/
def rows : List Row := Examples.all.filterMap Row.ofDatum

theorem isSome_ofDatum : ∀ e ∈ Examples.all, (e.feature? "negator").isSome →
    (Row.ofDatum e).isSome := by
  decide

theorem kind_eq_standard_iff :
    ∀ r ∈ rows, r.kind = .standard ↔ r.negator ∈ r.language.standard := by
  decide

theorem januubi_maa : ∀ r ∈ rows, r.language = .januubi → r.negator = Januubi.Negation.maa := by
  decide

/-! ### The form of the negator (Sections 6.1.1 and 6.1.2) -/

/-- Where the negation of the complement holds, for an attitude trigger: in what the holder
desires, in what conforms to the holder's behavioral standards, or in the real world. -/
inductive Evaluation where
  | desires
  | standards
  | actual
  deriving DecidableEq, Repr

/-- The negator Mandarin uses for a negation that holds there: the prohibitive *bié* or *búyào*
for the holder's desires, the deontic *bùgāi* for the holder's standards, and the standard *bù*
or *méi* for the real world. -/
def Evaluation.kind : Evaluation → NegatorKind
  | .desires => .imperative
  | .standards => .deontic
  | .actual => .standard

namespace ENConcept

/-- Where Table 6 has the negative inference of an attitude trigger hold, among the holder's
desires, the holder's standards and the real world. *Advise against* has it in optimal worlds, a
weaker deontic evaluation, and the *deny* class in the holder's beliefs or words. -/
def negative : ENConcept → List Evaluation
  | .fear => [.desires]
  | .avoid => [.desires, .actual]
  | .regret | .complain => [.standards]
  | .despair | .forget | .delay | .refuse | .stop | .prevent | .almost => [.actual]
  | _ => []

/-- The kinds of negator Mandarin admits under a trigger. -/
def mandarinKinds (c : ENConcept) : List NegatorKind := c.negative.map Evaluation.kind

/-- Mandarin admits the prohibitive negator exactly under the *fear* class, whose negation holds
in the holder's desires: under *fear* alone, and beside the standard negators under *avoid*. -/
theorem imperative_mem_mandarinKinds_iff {c : ENConcept} :
    .imperative ∈ c.mandarinKinds ↔ c.cls = .fear := by
  revert c; decide

theorem deontic_mem_mandarinKinds_iff {c : ENConcept} :
    .deontic ∈ c.mandarinKinds ↔ c = .regret ∨ c = .complain := by
  revert c; decide

end ENConcept

/-- Each Mandarin example has a negator of a kind its trigger admits: prohibitive *bié* under
*fear*, (14), standard *bù* and *méi* under *avoid* and *forget*, (15), (4), and deontic *bùgāi*
under *regret* and *complain*, (17), (18). -/
theorem mandarin_negators :
    (∀ r ∈ rows, r.language = .mandarin → r.kind ∈ r.concept.mandarinKinds) ∧
      (rows.filter (·.language = .mandarin)).length = 5 := by
  decide

/-! ### Blocked classes (Sections 6.4 and 7) -/

/-- Why a trigger class fails to license expletive negation in a language, Section 7. -/
inductive ENBlockingReason where
  /-- The language disprefers modal operators in complement clauses. -/
  | modalRestriction
  /-- Comparative complements admit only noun phrases. -/
  | npOnlyComplement
  /-- The concept is expressed analytically with a necessary negation. -/
  | analyticNegation
  /-- The negative inference is invited, not entailed. -/
  | weakInference
  deriving DecidableEq, Repr

/-- A concept can fail to trigger expletive negation in a language for four reasons. Januubi admits
only noun phrases as complements of comparatives and disprefers the modal that the *regret* class
needs; Januubi, Mandarin and Zarma-Sonrai express *too … to* as 'too … so that … not'; Mandarin
and Zarma-Sonrai express *without* as 'q not p', where the negation is part of the meaning; and
*hide*, whose negative inference is only invited, does not trigger in Januubi. -/
def blocking : Language → ENConcept → Option ENBlockingReason
  | .januubi, .moreThan | .januubi, .lessThan => some .npOnlyComplement
  | .januubi, .regret => some .modalRestriction
  | .januubi, .hide => some .weakInference
  | .januubi, .tooTo | .mandarin, .tooTo | .zarmaSonrai, .tooTo => some .analyticNegation
  | .mandarin, .without | .zarmaSonrai, .without => some .analyticNegation
  | _, _ => none

theorem blocking_eq_none_of_mem : ∀ r ∈ rows, blocking r.language r.concept = none := by decide

end JinKoenig2021
