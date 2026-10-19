module

public import Linglib.Syntax.Control.Defs
public import Linglib.Syntax.Control.Head
public import Linglib.Syntax.Category.Verb.Basic
public import Linglib.Fragments.English.Verbs.Inventory
public import Linglib.Semantics.Presupposition.Verb

/-!
# Landau (2015): A Two-Tiered Theory of Control

In Landau's two-tiered theory of control, obligatory control complements divide by the attitude
status of the selecting predicate, non-attitude complements establishing control by predication and
attitude complements by the binding of a projected coordinate of the embedded context, a second tier
built over the first. Landau's earlier predicate classes carry the split, the four classes selecting
untensed complements to the predicative tier and the four selecting tensed ones to the logophoric
tier ((4), (5)); the summary table of contrasts (80) shows the two tiers separated on every row,
with obligatory control into an inflected complement realized as the OC-NC generalization (70) over
the library's clause classes (`inflectedComplement_realizes_ocnc`); and object control under
attitude predicates reads *de se* with psychological verbs and *de te* with communicative ones (36).
The predicate classes are derived from the English fragment's verb entries rather than stored
(`derivedLandauClass`), and the derivation places the book's exhaustive-control verbs on the
predicative tier and its partial-control verbs on the logophoric tier.

## Implementation notes

The book was checked against the author's 2014 manuscript, whose numbering agrees with the
citations here. The tiers are mapped into the library's neutral vocabulary of control
mechanisms, predication sharing a referent and logophoric control composing a binding leg
over predication. Table (80) is recorded as the book states it; its three saturation rows,
control shift, partial control, and split control, are what `Control.IsSaturating` denies of a
predicative dependency, and its inflected-complement row is the one derived here. Obligatory
*de se* is a property of the logophoric tier alone, not a criterion of obligatory control.

## References

* [landau-2015]
* [landau-2000], [landau-2004], [landau-2013]
* [pearson-2016], [heim-2008], [kratzer-2009], [ganenkov-2019]
-/

@[expose] public section

namespace Landau2015

open Control

/-! ### The two tiers -/

/-- Obligatory control has two tiers. Predicative control, selected by non-attitude predicates,
moves PRO to the specifier of Fin and is syntactic predication, which forces exhaustive control.
In logophoric control, selected by attitude predicates, the complementizer projects a
perspectival coordinate that binds PRO, which admits partial control and forces a reading bound
to the attitude holder. -/
inductive Tier where
  | predicative
  | logophoric
  deriving DecidableEq, Repr

/-- In the neutral vocabulary of control mechanisms, predication shares the referent and
logophoric control composes a binding leg over predication. -/
def Tier.mechanism : Tier → Control.Mechanism
  | .predicative => .referent
  | .logophoric  => .composite

/-! ### Predicate classes ((4), (5)) -/

/-- The control predicate classes of [landau-2000], four selecting untensed complements (4) and
four selecting tensed ones (5), [landau-2004]'s correlation. Membership is a property
of predicate–complement pairs, not lexemes, and the evaluative class is the *of*-frame
adjectives; [pearson-2016]'s rival cut is temporal rather than attitudinal. -/
inductive PredicateClass where
  /-- *dare*, *manage*, *remember*, *avoid*, *fail*, *force*, … (4a). -/
  | implicative
  /-- *begin*, *start*, *continue*, *finish*, *stop* (4b). -/
  | aspectual
  /-- *have*, *need*, *may*, *should*, *is able*, *must* (4c). -/
  | modal
  /-- *rude*, *silly*, *smart*, *kind*, *bold*, *crazy* (4d). -/
  | evaluative
  /-- *glad*, *regret*, *hate*, *sorry*, … (5a). -/
  | factive
  /-- *believe*, *think*, *say*, *claim*, *declare*, … (5b). -/
  | propositional
  /-- *want*, *hope*, *agree*, *decide*, *intend*, *promise*, *choose*, … (5c). -/
  | desiderative
  /-- *wonder*, *ask*, *inquire*, *guess*, *know* (5d). -/
  | interrogative
  deriving DecidableEq, Repr

/-- A class selects a tier by tense, untensed complements being predicative and tensed ones
logophoric. -/
def PredicateClass.tier : PredicateClass → Tier
  | .implicative | .aspectual | .modal | .evaluative => .predicative
  | .factive | .propositional | .desiderative | .interrogative => .logophoric

/-! ### The empirical contrasts (table (80)) -/

/-- The six contrasts of table (80). -/
inductive Table80Row where
  /-- Obligatory control into an inflected complement, the OC-NC generalization (70). -/
  | inflectedComplement
  /-- A non-human PRO ((81)) has no logophoric binder, which is the author or addressee
  coordinate and defined only for humans. -/
  | nonhumanPRO
  /-- An implicit controller ((90), (93)) is out under predication, which needs a syntactically
  represented argument, so exhaustive-control verbs resist impersonal passives (98). -/
  | implicitControl
  /-- Control shift (§4.3) is out under predication, which is bi-unique
  (`Control.IsSaturating.eq_of_controllers`), so no other argument can saturate the predicate. -/
  | controlShift
  /-- Partial control (§5) is out under a saturating dependency, which is exhaustive
  (`Control.IsSaturating.not_isPartial`). -/
  | partialControl
  /-- Split control (§5) is out under a saturating dependency, which has a unique controller
  (`Control.IsSaturating.not_isSplit`). -/
  | splitControl
  deriving DecidableEq, Repr

/-- The predicative column of table (80). -/
def availableUnderPredicative : Table80Row → Bool
  | .inflectedComplement => true
  | .nonhumanPRO         => true
  | _                    => false

/-- The logophoric column of table (80). -/
def availableUnderLogophoric : Table80Row → Bool
  | .inflectedComplement => false
  | .nonhumanPRO         => false
  | _                    => true

/-- Table (80) separates the tiers on every row. -/
theorem table80_complementary (r : Table80Row) :
    availableUnderLogophoric r = !availableUnderPredicative r := by
  cases r <;> rfl

/-- The inflected-complement row is the OC-NC generalization (70) over the clause classes:
agreement leaves obligatory control in an untensed complement, the predicative tier, and
destroys it in a tensed one, the logophoric tier, since predication is not contingent on feature
matching while variable binding is ([heim-2008], [kratzer-2009]); its empirical scope is
contested ([ganenkov-2019]). -/
theorem inflectedComplement_realizes_ocnc :
    availableUnderPredicative .inflectedComplement
        = decide (ClauseClass.cSubjunctive.HasOC true) ∧
      availableUnderLogophoric .inflectedComplement
        = decide (ClauseClass.fSubjunctive.HasOC true) :=
  ⟨by decide, by decide⟩

/-! ### Readings of PRO under attitude predicates (table (36)) -/

/-- Logophoric PRO is bound to the author coordinate of the embedded context (*de se*) or to its
addressee coordinate (*de te*). -/
inductive DeSeReading where
  | deSe
  | deTe
  deriving DecidableEq, Repr

/-- The object control verbs by the coordinate they project (36). -/
inductive ObjectControlSubclass where
  /-- *convince*, *persuade*, *dissuade*, *tempt*. -/
  | psychological
  /-- *tell*, *ask*, *urge*, *recommend*. -/
  | communicative
  deriving DecidableEq, Repr

/-- Psychological verbs bind the author coordinate and communicative verbs the addressee
coordinate (36). -/
def objectControlReading : ObjectControlSubclass → DeSeReading
  | .psychological => .deSe
  | .communicative => .deTe

/-! ### Predicate classes from the fragment -/

/-- The predicate class of a fragment verb is read off its semantic fields. A change-of-state type
gives the aspectual class, an implication signature the implicative class, a factive
presupposition the factive class, question embedding without an attitude the interrogative
class, and a doxastic or preferential attitude the propositional or desiderative class; `none`
where the fields decide nothing, as for *try*. -/
def derivedLandauClass (v : Verb) : Option PredicateClass :=
  if v.phasal ≠ none then some .aspectual
  else if v.implicative ≠ ⊥ then some .implicative
  else if v.IsFactive then some .factive
  else if v.TakesQuestion ∧ v.attitude = none then some .interrogative
  else match v.attitude with
    | some (.doxastic _)     => some .propositional
    | some (.preferential _ _) => some .desiderative
    | none                   => none

/-- A fragment control verb is on the tier of its class, or else logophoric exactly when it
selects an attitude complement; a verb without control has no tier. -/
def derivedControlTier (v : Verb) : Option Tier :=
  if ¬ v.HasController then Option.none
  else match derivedLandauClass v with
    | some cls => some cls.tier
    | none =>
      if v.attitude ≠ none ∨ v.IsFactive ∨ v.TakesQuestion then some .logophoric
      else some .predicative

section Verbs

open English
open English.Verbs hiding Verb

/-- The fragment's exhaustive-control verbs, the aspectual and implicative ones. -/
def exhaustiveControlVerbs : List Verb :=
  [stop.toVerb, start.toVerb, begin_.toVerb, continue_.toVerb, manage.toVerb, fail.toVerb,
    remember.toVerb, forget.toVerb, force.toVerb]

/-- The fragment's partial-control verbs, the desiderative, factive, propositional and
interrogative ones. -/
def partialControlVerbs : List Verb :=
  [want.toVerb, hope.toVerb, promise.toVerb, persuade.toVerb, regret.toVerb, know.toVerb,
    believe.toVerb, think.toVerb, wonder.toVerb]

/-- The exhaustive-control verbs derive a class on the predicative tier. -/
theorem exhaustiveControlVerbs_predicative :
    ∀ v ∈ exhaustiveControlVerbs, (derivedLandauClass v).map (·.tier) = some .predicative := by
  decide

/-- The partial-control verbs derive a class on the logophoric tier. -/
theorem partialControlVerbs_logophoric :
    ∀ v ∈ partialControlVerbs, (derivedLandauClass v).map (·.tier) = some .logophoric := by
  decide

/-- *try* carries none of the deciding fields: trying entails no success and reports no
attitude. -/
theorem try_unclassifiable : derivedLandauClass try_.toVerb = none := rfl

end Verbs

end Landau2015
