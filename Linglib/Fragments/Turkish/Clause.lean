module

public import Linglib.Data.UD.Features
public import Linglib.Fragments.Turkish.Morphotactics
public import Linglib.Syntax.Clause.Chaining

/-!
# Turkish converbs

Turkish chains clauses with converbs, the non-finite verbs of adverbial clauses, without
switch-reference. Most converbial suffixes stand in place of the tense, aspect or modality
marker and all that follows it, after the voice suffixes, the negative and the markers of
positions 1 and 2 (§8.2, §28.2). *-(y)ken*, which contains the copula, attaches to a
position-3 marker or a nominal, and *-cAsInA* to the aorist or *-mIş* (§8.5.2.2). The converbs
take no person marker, except one before *-cAsInA* and the third-person plural before
*-(y)ken*. Three more converbial subordinators go on two verbs in succession.

## Main definitions

* `Turkish.Converb`: the converbial suffixes on one verb, with their forms, the relations they
  encode and `Converb.follows`, the last slot of the finite verb that may precede them; they
  are a `MedialForm`.
* `Turkish.DoubledConverb`: the converbial subordinators on two verbs.

## Implementation notes

The forms are strings of `Turkish.Suffix`, so that `Turkish.realize` gives a converb on a
stem, and the negative of *-mAdAn* is the finite verb's. `InterclauseRelation` names neither
the proportional and 'whenever' readings of *-DIkçA* nor the 'before' reading of *-mAdAn*.
The clause-chaining typology over the converbs is in `Studies/SarvasyAikhenvald2025.lean`, and
the grammar's examples are checked in `Studies/GokselKerslake2005.lean`.

## TODO

The other converbs built on the subordinators -DIK, -(y)AcAK, -mA and -mAK (§8.5.1), such as
*-mAksIzIn* 'without', and those with a postposition, such as *-mAzdAn önce* and
*-(y)IncAyA kadar* (§8.5.2.2), are not represented.

## References

* [A. Göksel and C. Kerslake, *Turkish: A Comprehensive Grammar* (2005)][goksel-kerslake-2005]
-/

@[expose] public section

namespace Turkish

open Turkish.Phonology

/-- The converbial suffixes on one verb, those of §8.5.2.2 that need no postposition, and
*-DIkçA*. -/
inductive Converb where
  /-- *-(y)Ip* 'and, and then', conjoining clauses. -/
  | ip
  /-- *-(y)ArAk* 'by doing, doing', manner and means, also conjunctive. -/
  | arak
  /-- *-(y)IncA* 'when'. -/
  | inca
  /-- *-(y)ken* 'while, as, when', the copula on a position-3 marker or a nominal. -/
  | ken
  /-- *-(y)AlI* 'since', colloquial. -/
  | ali
  /-- *-mAdAn* 'without doing, before doing', containing the negative. -/
  | madan
  /-- *-cAsInA* 'as if', on the aorist or *-mIş*. -/
  | casina
  /-- *-DIkçA* 'the more, whenever'. -/
  | dikca
  deriving DecidableEq, Repr, Fintype

namespace Converb

/-- The citation form of a converb, the negative of *-mAdAn* being the finite verb's and the `c`
of *-cAsInA* alternating with `ç`, as in *duymamışçasına*. -/
def form : Converb → List Suffix
  | ip => [⟨some y, [I, p]⟩]
  | arak => [⟨some y, [A, r, A, k]⟩]
  | inca => [⟨some y, [I, n, c, A]⟩]
  | ken => [⟨some y, [k, e, n]⟩]
  | ali => [⟨some y, [A, l, I]⟩]
  | madan => [Verb.Exponent.negative.form, ⟨none, [D, A, n]⟩]
  | casina => [⟨none, [C, A, s, I, n, A]⟩]
  | dikca => [⟨none, [D, I, k, ç, A]⟩]

/-- The interclausal relations a converb encodes (§26.3, §28.2). -/
def relations : Converb → Finset InterclauseRelation
  | ip => {.sequential, .additive}
  | arak => {.manner, .simultaneous, .additive}
  | inca | ali => {.sequential}
  | ken => {.simultaneous, .contrastive}
  | madan | casina => {.manner}
  | dikca => ∅

/-- The last slot of the finite verb whose exponent may precede the converb. The converbs on a
non-finite stem follow the markers of position 2 (§8.2), *-(y)ken* a position-3 marker,
*-cAsInA* a person marker, and *-mAdAn*, whose negative fills the negation slot, the
possibility suffix of position 1. -/
def follows : Converb → Verb.Slot
  | ip | arak | inca | ali | dikca => .auxiliary
  | ken => .tam
  | casina => .person
  | madan => .possibility

/-- A position-3 marker of tense, aspect or modality may precede the converb. -/
def Tensed (c : Converb) : Prop := .tam ≤ c.follows

instance : DecidablePred Tensed := fun _ ↦ inferInstanceAs (Decidable (_ ≤ _))

/-- The converb contains the negative or admits it before it. -/
def Negatable (c : Converb) : Prop :=
  Verb.Exponent.negative.form ∈ c.form ∨ .negation ≤ c.follows

instance : DecidablePred Negatable := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- A person marker may precede the converb: any before *-cAsInA*, and the third-person plural
*-lAr* before *-(y)ken* (§8.5.2.2). -/
def PersonMarked (c : Converb) : Prop := .person ≤ c.follows ∨ c = ken

instance : DecidablePred PersonMarked := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- The verb form of a converb. -/
def verbForm (_ : Converb) : UD.VerbForm := .Conv

/-- The converbs as medial forms, neutral to switch-reference. -/
instance : MedialForm Converb where
  sr _ := none
  relations := relations
  IndexesSubject := PersonMarked

end Converb

/-- The converbial subordinators on two verbs in succession (§8.5.2.2). -/
inductive DoubledConverb where
  /-- *-(y)A … -(y)A*, continuous manner, as *baka baka* 'staring'. -/
  | aA
  /-- *-DI … -(y)AlI* 'ever since', the first verb with a person marker, as *duydum duyalı*. -/
  | diAli
  /-- *-(A/I)r … -mAz* 'as soon as', the positive and the negative aorist, as *yer yemez*. -/
  | arMaz
  deriving DecidableEq, Repr, Fintype

/-- The suffixes of the first and of the second verb. -/
def DoubledConverb.forms : DoubledConverb → List Suffix × List Suffix
  | .aA => ([⟨some y, [A]⟩], [⟨some y, [A]⟩])
  | .diAli => ([Verb.Exponent.di.form], Converb.ali.form)
  | .arMaz => ([Verb.Exponent.aorist.form], [Verb.Exponent.negative.form, ⟨none, [z]⟩])

end Turkish
