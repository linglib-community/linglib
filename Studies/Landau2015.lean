module

public import Linglib.Syntax.Control.Basic
public import Mathlib.Data.Fin.VecNotation
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
citations here. A tier is a shape of control dependency (`Tier.Realizes`): predication is
saturating, and logophoric control composes a binding leg over predication. Table (80)'s three
saturation rows, control shift, partial control and split control, are derived from that shape,
since `Control.IsSaturating` denies them of predication and the binding leg admits them; its
inflected-complement row is the OC-NC generalization, and its rows on non-human PRO and implicit
control are recorded as the book states them. In a single dependency, control shift and split
control both show as a dependent with two controllers; the dependency does not record whether
they are alternatives or act jointly. Obligatory
*de se* is a property of the logophoric tier alone, not a criterion of obligatory control.

## References

* [landau-2015]
* [landau-2000], [landau-2004], [landau-2013]
* [pearson-2016], [heim-2008], [kratzer-2009], [ganenkov-2019]
-/

@[expose] public section

namespace Landau2015

open Control SetRel

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

/-- A dependency realizes a tier. Predicative control is predication, a saturating dependency;
logophoric control composes the binding of the projected coordinate *pro* by the controller over
the predication of *pro*. -/
def Tier.Realizes {Pos Ref : Type*} (val : Pos → Ref) : Tier → SetRel Pos Pos → Prop
  | .predicative, d => IsSaturating val d
  | .logophoric, d => ∃ bind pred, d = bind ○ pred ∧ IsSaturating val pred

theorem isPartial_bind_of_logophoric {Pos Ref : Type*} [Preorder Ref] {val : Pos → Ref}
    {bind pred : SetRel Pos Pos} (hp : IsSaturating val pred) (h : IsPartial val (bind ○ pred)) :
    IsPartial val bind :=
  h.of_comp hp.exhaustive

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

/-- The clause class of an inflected complement on each tier, untensed under predication and
tensed under logophoric control ((4), (5)). -/
def Tier.inflectedClass : Tier → ClauseClass
  | .predicative => .cSubjunctive
  | .logophoric => .fSubjunctive

/-- A row of table (80) is available on a tier. The three saturation rows are available when some
dependency realizing the tier shows them, referents measured in `ℕ`; the inflected-complement row
is the OC-NC generalization (70) for the tier's clause class; the other two rows are as the book
states them. -/
def Table80Row.Available : Table80Row → Tier → Prop
  | .inflectedComplement, t => t.inflectedClass.HasOC true
  | .nonhumanPRO, t => t = .predicative
  | .implicitControl, t => t = .logophoric
  | .controlShift, t => ∃ (Pos : Type) (val : Pos → ℕ) (d : SetRel Pos Pos),
      t.Realizes val d ∧ ∃ a b p, a ≠ b ∧ a ~[d] p ∧ b ~[d] p
  | .partialControl, t => ∃ (Pos : Type) (val : Pos → ℕ) (d : SetRel Pos Pos),
      t.Realizes val d ∧ IsPartial val d
  | .splitControl, t => ∃ (Pos : Type) (val : Pos → ℕ) (d : SetRel Pos Pos),
      t.Realizes val d ∧ IsSplit d

private theorem realizes_logophoric_witness :
    Tier.logophoric.Realizes ![1, 1, 2, 2]
      ({(0, 2), (1, 2)} ○ ({(2, 3)} : SetRel (Fin 4) (Fin 4))) := by
  refine ⟨_, _, rfl, ⟨⟨fun a b c ↦ ?_, fun a b c ↦ ?_⟩, fun ⟨a, b⟩ h ↦ ?_⟩⟩ <;> simp_all

theorem available_iff_logophoric {r : Table80Row}
    (hr : r = .controlShift ∨ r = .partialControl ∨ r = .splitControl) (t : Tier) :
    r.Available t ↔ t = .logophoric := by
  have hw := realizes_logophoric_witness
  rcases hr with rfl | rfl | rfl <;> cases t <;> simp only [Table80Row.Available, reduceCtorEq,
    iff_false, not_exists, not_and, iff_true]
  · exact fun _ _ _ h a b p hab ha hb ↦ hab (IsSaturating.eq_of_controllers h ha hb)
  · exact ⟨_, _, _, hw, 0, 1, 3, by decide, ⟨2, by simp⟩, ⟨2, by simp⟩⟩
  · exact fun _ _ _ h ↦ IsSaturating.not_isPartial h
  · exact ⟨_, _, _, hw, 0, 3, ⟨2, by simp⟩, by decide⟩
  · exact fun _ _ _ h ↦ IsSaturating.not_isSplit h
  · exact ⟨_, _, _, hw, fun h ↦
      absurd (h (a := 0) (b := 1) (c := 3) ⟨2, by simp⟩ ⟨2, by simp⟩) (by decide)⟩

-- (80)
theorem table80_complementary (r : Table80Row) :
    r.Available .logophoric ↔ ¬ r.Available .predicative := by
  cases r
  case controlShift | partialControl | splitControl =>
    simp [available_iff_logophoric]
  all_goals simp only [Table80Row.Available, Tier.inflectedClass]; decide

/-- The inflected-complement row is the OC-NC generalization (70), keeping control in predicative
but not logophoric complements ([heim-2008], [kratzer-2009]; contested by [ganenkov-2019]). -/
theorem inflectedComplement_realizes_ocnc :
    Table80Row.inflectedComplement.Available .predicative ∧
      ¬ Table80Row.inflectedComplement.Available .logophoric := by
  simp only [Table80Row.Available, Tier.inflectedClass]; decide

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

theorem exhaustiveControlVerbs_predicative :
    ∀ v ∈ exhaustiveControlVerbs, (derivedLandauClass v).map (·.tier) = some .predicative := by
  decide

theorem partialControlVerbs_logophoric :
    ∀ v ∈ partialControlVerbs, (derivedLandauClass v).map (·.tier) = some .logophoric := by
  decide

theorem try_unclassifiable : derivedLandauClass try_.toVerb = none := rfl

end Verbs

end Landau2015
