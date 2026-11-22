module

public import Linglib.Morphology.DistributedMorphology.Spellout
public import Linglib.Syntax.Minimalist.Feature.Basic
public import Linglib.Phonology.RuleInteraction
public import Linglib.Data.Examples.ArregiNevins2012
public import Linglib.Data.Examples.Gloss

/-!
# Arregi and Nevins (2012): Morphotactics

The Basque finite auxiliary is a word of terminals: T, and clitics that bear a case and person and
number features. Its spellout runs in modules. In the Feature Markedness module, First Singular
Clitic Impoverishment (`firstSingular`) deletes `[+participant]` from a first singular clitic, and
Participant Dissimilation (`ondarru`, `zamudio`) obliterates a first person participant clitic of
a word with a second participant clitic. In the Linear Operations module, which follows, a T at
the left edge of the word violates T-Noninitiality (`TNoninitial`) and is repaired by Ergative
Metathesis (`ergativeMetathesis`), which fronts the ergative clitic across T, or else by L-Support
(`lSupportRepair`), which inserts an epenthetic L before T. The module leaves no T at the left
edge (`tNoninitial_linearOperations`).

The order of the rules shows in their interactions. First Singular Clitic Impoverishment is
paradigmatic and bleeds Participant Dissimilation (`firstSingular_bleeds_ondarru`), whose condition
reads a second clitic. Participant Dissimilation feeds Ergative Metathesis in Ondarru, where it
obliterates the absolutive clitic that stood before T (`ondarru_feeds`), and bleeds it in Zamudio,
where it obliterates the ergative clitic (`zamudio_bleeds`). With the two modules in the other
order T is left at the edge of the word (`not_tNoninitial_linearThenMarkedness`). The auxiliaries
of the examples are acceptable exactly where their morphemes are the terminals the modules give,
in the same order (`predicted_iff_acceptable`).

## Implementation notes

* A terminal is a list of `Minimalist.FeatureVal`s. The book's `[±singular]` is written
  `[±atomic]`, T bears `[±tense]` for `[±past]` and no agreement features, and `[+motion]` is
  dative or ergative case.
* The rules of the Feature Markedness module are stated on the string of terminals. Their
  conditions on a word with two clitics read the whole context of the focus, in either direction
  and at any distance.
* Ergative Metathesis carries the condition common to the three dialects, that no first person
  dative clitic stands between T and the ergative clitic.

## TODO

* Participant Dissimilation is an `ObliterationRule`, to which `ImpoverishmentRule.Syntagmatic`
  does not apply; `not_factorsThrough_ondarru` states it on the condition.
* Plural Clitic Impoverishment and the Impoverishment rules of T, Ergative Doubling, Root
  Reduplication, Lekeitio's condition on Ergative Metathesis, and exponence.

## References

* [K. Arregi and A. Nevins, *Morphotactics*][arregi-nevins-2012]
-/

@[expose] public section

namespace ArregiNevins2012

open Minimalist DistributedMorphology Phonology Neighborhood

/-! ### Terminals -/

/-- A terminal of the auxiliary is a list of features. -/
abbrev Terminal := List FeatureVal

/-- A clitic is a terminal with a case feature. -/
def IsClitic (t : Terminal) : Prop := ∃ f ∈ t, f.1 = FeatureType.case

/-- T is a terminal with a tense feature. -/
def IsT (t : Terminal) : Prop := ∃ f ∈ t, f.1 = FeatureType.tense

/-- The dative and ergative clitics are `[+motion]`, the absolutive is not. -/
def HasMotion (t : Terminal) : Prop := ⟨.case, .dat⟩ ∈ t ∨ ⟨.case, .erg⟩ ∈ t

instance : DecidablePred IsClitic := fun t ↦ inferInstanceAs (Decidable (∃ f ∈ t, _))

instance : DecidablePred IsT := fun t ↦ inferInstanceAs (Decidable (∃ f ∈ t, _))

instance : DecidablePred HasMotion := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- First person, `[+participant, +author]`. -/
def firstφ : Terminal := [⟨.participant, true⟩, ⟨.author, true⟩]

/-- Second person, `[+participant, −author]`. -/
def secondφ : Terminal := [⟨.participant, true⟩, ⟨.author, false⟩]

/-- A clitic bears its case, its person features and `[±singular]`. -/
def clitic (c : Case) (φ : Terminal) (singular : Bool) : Terminal :=
  ⟨.case, c⟩ :: φ ++ [⟨.atomic, singular⟩]

/-- T, in the past tense. -/
def pastT : Terminal := [⟨.tense, true⟩]

/-- The epenthetic L of L-Support is a terminal without features. -/
def lSupport : Terminal := []

/-! ### The Feature Markedness module -/

/-- (58): by First Singular Clitic Impoverishment a clitic specified as
`[+participant, +author, +singular]` loses `[+participant]`. -/
def firstSingular : ImpoverishmentRule Terminal FeatureVal :=
  .ofFocus
    (fun t ↦ IsClitic t ∧ ⟨.participant, true⟩ ∈ t ∧ ⟨.author, true⟩ ∈ t ∧ ⟨.atomic, true⟩ ∈ t)
    ⟨.participant, true⟩

theorem firstSingular_paradigmatic : firstSingular.Paradigmatic :=
  ImpoverishmentRule.paradigmatic_ofFocus _ _

/-- First Singular Clitic Impoverishment applied to each terminal of the word. -/
def firstSingularImpoverishment (d : SpelloutDomain Terminal) : SpelloutDomain Terminal :=
  (along d).map (firstSingular.apply fun t f ↦ t.erase f)

/-- (31): by Participant Dissimilation in Ondarru a clitic that is `[+participant, +author]` is
obliterated in a word with an ergative `[+participant]` clitic. -/
def ondarru : ObliterationRule Terminal :=
  ⟨fun n ↦ IsClitic n.focus ∧ firstφ ⊆ n.focus ∧
    ∃ t ∈ n.leftCtx ++ n.rightCtx, [⟨.case, .erg⟩, ⟨.participant, true⟩] ⊆ t⟩

/-- (33): by Participant Dissimilation in Zamudio a clitic that is
`[+motion, +participant, +author]` is obliterated in a word with a `[+participant]` clitic. -/
def zamudio : ObliterationRule Terminal :=
  ⟨fun n ↦ HasMotion n.focus ∧ firstφ ⊆ n.focus ∧
    ∃ t ∈ n.leftCtx ++ n.rightCtx, IsClitic t ∧ ⟨.participant, true⟩ ∈ t⟩

/-! ### The Linear Operations module -/

/-- (96): T-Noninitiality holds of a word whose leftmost terminal is not T. -/
def TNoninitial (d : SpelloutDomain Terminal) : Prop := ¬ ∃ t ∈ d.head?, IsT t

instance : DecidablePred TNoninitial := fun _ ↦ inferInstanceAs (Decidable (¬ _))

/-- (105): by Ergative Metathesis a word-initial past T and what follows it up to the first
ergative clitic change places with that clitic, when no first person dative clitic stands between
them. The double brackets open before T and close after the clitic, and the angled brackets
stand before the clitic. -/
def ergativeMetathesis (n : Neighborhood Terminal) : Option Reduplication :=
  if n.leftCtx = [] ∧ ⟨.tense, true⟩ ∈ n.focus then
    (n.rightCtx.findIdx? (·.contains ⟨.case, .erg⟩)).bind fun i ↦
      if ∀ t ∈ n.rightCtx.take i, ¬ (⟨.case, .dat⟩ ∈ t ∧ ⟨.author, true⟩ ∈ t) then
        some (.metathesis (i + 1) 1)
      else none
  else none

theorem reduplicateFirst_ergativeMetathesis_perm (d : SpelloutDomain Terminal) :
    (reduplicateFirst ergativeMetathesis d).Perm d :=
  reduplicateFirst_perm (fun n b hb ↦ by
    unfold ergativeMetathesis at hb
    split_ifs at hb
    · obtain ⟨i, -, hi⟩ := Option.bind_eq_some_iff.1 hb
      split_ifs at hi
      cases hi
      rfl
    · cases hb) d

/-- (121): by L-Support an L is inserted before a word-initial T. -/
def lSupportRepair (d : SpelloutDomain Terminal) : SpelloutDomain Terminal :=
  if ∃ t ∈ d.head?, IsT t then lSupport :: d else d

theorem tNoninitial_lSupportRepair (d : SpelloutDomain Terminal) :
    TNoninitial (lSupportRepair d) := by
  unfold lSupportRepair
  split_ifs with h
  · simp [TNoninitial, lSupport, IsT]
  · exact h

/-- The Linear Operations module applies Ergative Metathesis and then L-Support, the more
general of the two repairs. -/
def linearOperations : SpelloutDomain Terminal → SpelloutDomain Terminal :=
  lSupportRepair ∘ reduplicateFirst ergativeMetathesis

/-- The Linear Operations module leaves no T at the left edge of the word. -/
theorem tNoninitial_linearOperations (d : SpelloutDomain Terminal) :
    TNoninitial (linearOperations d) :=
  tNoninitial_lSupportRepair _

/-- Feature Markedness before Linear Operations. -/
def markednessThenLinear (pd : ObliterationRule Terminal) :
    SpelloutDomain Terminal → SpelloutDomain Terminal :=
  linearOperations ∘ pd.apply

/-- Linear Operations before Feature Markedness. -/
def linearThenMarkedness (pd : ObliterationRule Terminal) :
    SpelloutDomain Terminal → SpelloutDomain Terminal :=
  pd.apply ∘ linearOperations

/-! ### Paradigmatic before syntagmatic -/

/-- The first plural absolutive clitic of (16). -/
def absFirstPlural : Terminal := clitic .abs firstφ false

theorem not_factorsThrough_ondarru : ¬ ondarru.condition.FactorsThrough Neighborhood.focus :=
  fun h ↦ absurd
    ((h (a := ⟨absFirstPlural, [], [pastT, clitic .erg secondφ true]⟩) (b := ↑absFirstPlural)
      rfl).to_iff.1 (by decide)) (by decide)

/-- First Singular Clitic Impoverishment bleeds Participant Dissimilation, (58) and (59c): in a
word with a first singular absolutive clitic and a second person ergative clitic, the absolutive
clitic loses the `[+participant]` that Participant Dissimilation requires of it. -/
theorem firstSingular_bleeds_ondarru :
    Bleeds firstSingularImpoverishment ondarru.Fires
      [clitic .abs firstφ true, pastT, clitic .erg secondφ true] := by
  decide

-- (58): the rule does not apply to first plural clitics
theorem not_firstSingular_bleeds_ondarru :
    ¬ Bleeds firstSingularImpoverishment ondarru.Fires
      [absFirstPlural, pastT, clitic .erg secondφ true] := by
  decide

/-! ### Participant Dissimilation and Ergative Metathesis -/

/-- The Ondarru auxiliary of (16), *s-endu-n* 'you saw us': a first plural absolutive clitic,
past T, and a second singular ergative clitic. -/
def auxiliary16 : SpelloutDomain Terminal := [absFirstPlural, pastT, clitic .erg secondφ true]

/-- The Zamudio auxiliary of (20), *y-a-tzu-e-n* 'we accompanied you': past T, a second plural
dative clitic, and a first plural ergative clitic. -/
def auxiliary20 : SpelloutDomain Terminal :=
  [pastT, clitic .dat secondφ false, clitic .erg firstφ false]

/-- The auxiliary of (21): past T, a first plural dative clitic, and a second person ergative
clitic. -/
def auxiliary21 : SpelloutDomain Terminal :=
  [pastT, clitic .dat firstφ false, clitic .erg secondφ true]

-- (15), (16)
theorem ondarru_markednessThenLinear :
    markednessThenLinear ondarru auxiliary16 = [clitic .erg secondφ true, pastT] := by
  decide

-- (17b)
theorem ondarru_linearThenMarkedness :
    linearThenMarkedness ondarru auxiliary16 = [pastT, clitic .erg secondφ true] := by
  decide

/-- In Ondarru, Participant Dissimilation feeds Ergative Metathesis, (15): T is initial only once
the absolutive clitic is obliterated. -/
theorem ondarru_feeds : Feeds ondarru.apply (Fires ergativeMetathesis) auxiliary16 := by
  decide

-- (21), with the first person dative clitic that blocks Ergative Metathesis
theorem ondarru_feeds_dative : Feeds ondarru.apply (Fires ergativeMetathesis) auxiliary21 := by
  decide

-- (19), (20)
theorem zamudio_markednessThenLinear :
    markednessThenLinear zamudio auxiliary20 = [lSupport, pastT, clitic .dat secondφ false] := by
  decide

theorem zamudio_linearThenMarkedness :
    linearThenMarkedness zamudio auxiliary20 = [pastT, clitic .dat secondφ false] := by
  decide

/-- In Zamudio, Participant Dissimilation bleeds Ergative Metathesis, (19): it obliterates the
ergative clitic that would front. -/
theorem zamudio_bleeds : Bleeds zamudio.apply (Fires ergativeMetathesis) auxiliary20 := by
  decide

-- (17b), and the order rejected for (20)
theorem not_tNoninitial_linearThenMarkedness :
    ¬ TNoninitial (linearThenMarkedness ondarru auxiliary16) ∧
      ¬ TNoninitial (linearThenMarkedness zamudio auxiliary20) := by
  decide

/-! ### The examples

A row's auxiliary is read off its gloss line and compared, piece by piece, with the string of
terminals the two modules give for the row's variety and arguments. -/

/-- The pieces of an auxiliary that the two modules order. -/
inductive Piece where
  | absolutive
  | dative
  | ergative
  | tense
  | l
  deriving DecidableEq, Repr

/-- The piece a terminal is: T, a clitic of its case, or L, the terminal without features. -/
def piece (t : Terminal) : Piece :=
  if IsT t then .tense
  else if ⟨.case, .abs⟩ ∈ t then .absolutive
  else if ⟨.case, .dat⟩ ∈ t then .dative
  else if ⟨.case, .erg⟩ ∈ t then .ergative
  else .l

/-- The piece a morpheme of the gloss line is: `PST` is T, `L` is L, and `CL` with a person is
the clitic of its case. The plural exponent of a clitic and the complementizer are not terminals
of the string the modules order. -/
def pieceOfGloss? (g : List Char) : Option Piece :=
  let els := Gloss.elements g
  if "PST".toList ∈ els then some .tense
  else if els = ["L".toList] then some .l
  else if "CL".toList ∈ els ∧ ∃ n ∈ ["1", "2", "3"], n.toList ∈ els then
    if "A".toList ∈ els then some .absolutive
    else if "D".toList ∈ els then some .dative
    else if "E".toList ∈ els then some .ergative
    else none
  else none

/-- The pieces of a row's auxiliary, the word with a tense morpheme. -/
def pieces (e : Datum) : Option (List Piece) :=
  (e.glossedWords.find? fun w ↦ decide (some Piece.tense ∈ w.glosses.map pieceOfGloss?)).map
    (·.glosses.filterMap pieceOfGloss?)

/-- The rule of Participant Dissimilation of a variety. -/
def Examples.Variety.rule : Examples.Variety → ObliterationRule Terminal
  | .ondarru => ArregiNevins2012.ondarru
  | .zamudio => ArregiNevins2012.zamudio

/-- The string of terminals the syntax hands over for the arguments of a row. -/
def Examples.Arguments.auxiliary : Examples.Arguments → SpelloutDomain Terminal
  | .erg2sgAbs1pl => auxiliary16
  | .erg1plDat2pl => auxiliary20

/-- A row is predicted when its auxiliary has the pieces of the string the two modules give for
its variety and arguments, in the same order. -/
def Predicted (x : Examples.Example) : Prop :=
  ∃ v ∈ x.variety, ∃ a ∈ x.arguments,
    pieces x.datum = some ((markednessThenLinear v.rule a.auxiliary).map piece)

instance : DecidablePred Predicted := fun _ ↦ inferInstanceAs (Decidable (∃ v ∈ _, ∃ a ∈ _, _))

/-- The auxiliaries of (16), (17) and (20) are acceptable exactly where they are predicted. -/
theorem predicted_iff_acceptable :
    ∀ x : Examples.Example, Predicted x ↔ x.datum.judgment = .acceptable := by
  decide

-- (17b) is the string that Linear Operations before Feature Markedness gives
theorem pieces_ex17b :
    pieces Examples.ex_17b = some ((linearThenMarkedness ondarru auxiliary16).map piece) := by
  decide

end ArregiNevins2012
