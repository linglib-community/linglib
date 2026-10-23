module

public import Linglib.Data.UD.UPOS
public import Linglib.Data.UD.Features
public import Linglib.Fragments.English.Nouns
public import Linglib.Morphology.Word.Basic
public import Linglib.Pragmatics.SocialMeaning.Register
public import Linglib.Semantics.Modality.Basic
public import Linglib.Syntax.Agreement.Target
public import Linglib.Syntax.Category.Auxiliary.Basic
public import Linglib.Syntax.Number.Basic
public import Linglib.Syntax.Person.Basic

/-!
# English auxiliaries

This file defines the English auxiliary verbs of the Cambridge grammar: the modals *can*, *may*,
*will*, *shall*, *must*, *ought*, *need* and *dare*, with the preterites *could*, *might*,
*would* and *should*, and the non-modals *be*, *have* and *do*. The entries are primary forms,
present or preterite, neutral or negative. A modal has one present form for every subject;
*have* and *do* tell the third person singular from the plain present; and *be* shows more
agreement than any other verb. The present and the preterite of *be* and the present of *have*
and *do* are agreement targets, so that what each agrees in is read off its forms, and their
entries are its values in cells. The negative forms *can't*, *won't* and the rest are
inflectional forms in their own right. The infinitival marker *to* is also here, apart from the
preposition.

## Main declarations

* `English.Auxiliaries.bePresent`, `bePreterite`, `havePresent`, `doPresent`: the targets.
* `English.Auxiliaries.modals`, `allAuxiliaries`: the auxiliaries.
* `English.Auxiliaries.contractions`, `negative`: each auxiliary paired with its negative form.
* `factorsThrough_havePresent_bePresent`, `not_factorsThrough_bePresent_havePresent`: *be*
  agrees more than *have* and *do*.

## Implementation notes

* A modal's meanings are force–flavor pairs. The grammar's epistemic and deontic modality are
  the flavors of those names and its dynamic modality, ability, volition and circumstantial
  possibility or necessity, is circumstantial; its medium strength, of *should* and *ought*, is
  weak necessity.
* The meanings are those of affirmative contexts, as `Modality.ModalItem` takes them: epistemic
  *can*, confined to non-affirmative contexts, is not among them, nor is the deontic *will* that
  is an implicature. *need* and *dare* occur only in non-affirmative contexts and carry the
  meanings they have there.
* An entry carries the person and the number that every cell it realizes shares: *are*, of the
  second person and the plurals, carries neither, and *was* carries the singular.
* The lexical modals *have to* and *be able to* are not auxiliaries; the dialectal auxiliary
  *use* and the auxiliary preterite *dared* are left out.

## References

* [huddleston-pullum-2002]
* [zwicky-pullum-1983]
-/

@[expose] public section

open Morphology (Word Features)
open _root_.Agreement (Dimension Target)
open Function

namespace English.Auxiliaries

/-- The features of a finite form in a tense, with the person and the number it fixes. -/
def finite (tense : UD.Tense) (person : Option Person := none) (number : Option Number := none) :
    Features :=
  Features.of (person := person) (number := number) (verbForm := some .Fin) (tense := some tense)

/-! ### Agreement

A finite verb agrees with its subject in person and number ([huddleston-pullum-2002] ch. 3
§1.1). -/

/-- The values of a cell of an English finite verb: a person of the tripartition and one of the
two numbers, and a single value in the dimensions no English verb agrees in. -/
abbrev Value : Dimension → Type
  | .person => {p : Person // ¬ p.MarksClusivity}
  | .number => Nouns.numberSystem.values
  | .gender => Unit
  | .case => Unit
  | .definiteness => Unit

/-- A cell of an English finite verb. -/
abbrev Cell := (d : Dimension) → Value d

/-- The cell of a subject of a person and a number. -/
def cell (p : Person) (n : Number) (hp : ¬ p.MarksClusivity := by decide)
    (hn : n ∈ Nouns.numberSystem.values := by decide) : Cell
  | .person => ⟨p, hp⟩
  | .number => ⟨n, hn⟩
  | .gender => ()
  | .case => ()
  | .definiteness => ()

/-- The predicate target whose form is `f` of the subject's person and number, given a person
and the plural that each change the form of the third person singular. -/
def ofForm (f : {p : Person // ¬ p.MarksClusivity} → Nouns.numberSystem.values → String)
    (p : {p : Person // ¬ p.MarksClusivity})
    (hp : f p (Nouns.numberSystem.value .singular) ≠
      f ⟨.third, by decide⟩ (Nouns.numberSystem.value .singular))
    (hn : f ⟨.third, by decide⟩ (Nouns.numberSystem.value .plural) ≠
      f ⟨.third, by decide⟩ (Nouns.numberSystem.value .singular)) :
    Target Value String :=
  .ofDependsOn {.predicate} (fun x ↦ f (x .person) (x .number)) {.person, .number}
    (fun x y h ↦ by simp only [h .person (by simp), h .number (by simp)])
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
      exact ⟨⟨cell .third .singular, p, hp⟩, ⟨cell .third .singular, _, hn⟩⟩)

/-- The present of *be*: *am* in the first person singular, *is* in the third, and *are*
elsewhere ([huddleston-pullum-2002] ch. 3 §1.1). -/
def bePresentForm (p : {p : Person // ¬ p.MarksClusivity}) :
    Nouns.numberSystem.values → String :=
  Nouns.numberSystem.elim (match p.1 with | .first => "am" | .third => "is" | _ => "are") "are"

/-- The preterite of *be*: *was* in the first and the third person singular, and *were*
elsewhere ([huddleston-pullum-2002] ch. 3 §1.1). -/
def bePreteriteForm (p : {p : Person // ¬ p.MarksClusivity}) :
    Nouns.numberSystem.values → String :=
  Nouns.numberSystem.elim (match p.1 with | .second => "were" | _ => "was") "were"

/-- The present of a verb with a third person singular form `third` and a plain present form
`plain`, which serves every other subject ([huddleston-pullum-2002] ch. 3 §1.1). -/
def presentForm (third plain : String) (p : {p : Person // ¬ p.MarksClusivity}) :
    Nouns.numberSystem.values → String :=
  Nouns.numberSystem.elim (match p.1 with | .third => third | _ => plain) plain

/-- The present of *be* inflects for person and number. -/
def bePresent : Target Value String :=
  ofForm bePresentForm ⟨.first, by decide⟩ (by decide) (by decide)

/-- The preterite of *be* inflects for person and number. -/
def bePreterite : Target Value String :=
  ofForm bePreteriteForm ⟨.second, by decide⟩ (by decide) (by decide)

/-- The present of *have* inflects for person and number. -/
def havePresent : Target Value String :=
  ofForm (presentForm "has" "have") ⟨.first, by decide⟩ (by decide) (by decide)

/-- The present of *do* inflects for person and number. -/
def doPresent : Target Value String :=
  ofForm (presentForm "does" "do") ⟨.first, by decide⟩ (by decide) (by decide)

private theorem factorsThrough_ofForm {f g : {p : Person // ¬ p.MarksClusivity} →
      Nouns.numberSystem.values → String}
    (h : ∀ p n q m, f p n = f q m → g p n = g q m) :
    FactorsThrough (fun x : Cell ↦ g (x .person) (x .number))
      (fun x : Cell ↦ f (x .person) (x .number)) :=
  fun _ _ ↦ h _ _ _ _

/-- *be* shows more person–number agreement than other verbs ([huddleston-pullum-2002] ch. 3
§1.1): the present of *have* tells apart only cells that the present of *be* tells apart. -/
theorem factorsThrough_havePresent_bePresent : FactorsThrough havePresent.form bePresent.form :=
  factorsThrough_ofForm (f := bePresentForm) (g := presentForm "has" "have") (by decide)

theorem factorsThrough_doPresent_bePresent : FactorsThrough doPresent.form bePresent.form :=
  factorsThrough_ofForm (f := bePresentForm) (g := presentForm "does" "do") (by decide)

theorem not_factorsThrough_bePresent_havePresent :
    ¬ FactorsThrough bePresent.form havePresent.form :=
  fun h ↦ absurd (h (a := cell .first .singular) (b := cell .second .singular) rfl) (by decide)

theorem factorsThrough_bePreterite_bePresent : FactorsThrough bePreterite.form bePresent.form :=
  factorsThrough_ofForm (f := bePresentForm) (g := bePreteriteForm) (by decide)

/-! ### Modals

A modal has a single present form for every subject and no secondary forms
([huddleston-pullum-2002] ch. 3 §2.4). -/

/-- *can*, weak modality ([huddleston-pullum-2002] ch. 3 §9.3): deontic permission, informal
beside *may*, and dynamic possibility, ability among it. Its epistemic use, *He can't have done
it deliberately*, is confined to non-affirmative contexts. -/
def can : ModalAuxiliary where
  form := "can"
  features := finite .Pres
  meaning := {.possibility} ×ˢ {.deontic, .circumstantial}

/-- *could*, the preterite of *can*: the deontic and dynamic uses of *can* in past time, and the
epistemic possibility that *can* lacks ([huddleston-pullum-2002] ch. 3 §9.8). -/
def could : ModalAuxiliary where
  form := "could"
  features := finite .Past
  meaning := {.possibility} ×ˢ {.epistemic, .deontic, .circumstantial}

/-- *will*, strong modality of low degree ([huddleston-pullum-2002] ch. 3 §9.5): epistemic,
futurity among it, and dynamic volition. Its deontic use, *You will report back for duty*, is an
implicature. -/
def will : ModalAuxiliary where
  form := "will"
  features := finite .Pres
  meaning := {.necessity} ×ˢ {.epistemic, .circumstantial}

/-- *would*, the preterite of *will*: volition and futurity in past time, and the tentative
epistemic use of *He'd be about sixty* ([huddleston-pullum-2002] ch. 3 §9.8). -/
def would : ModalAuxiliary where
  form := "would"
  features := finite .Past
  meaning := {.necessity} ×ˢ {.epistemic, .circumstantial}

/-- *shall*, strong deontic modality in regulations, the speaker's guarantee and direction
questions, and with a first person subject a variant of *will* for futurity and volition,
somewhat more formal ([huddleston-pullum-2002] ch. 3 §9.6). -/
def shall : ModalAuxiliary where
  form := "shall"
  features := finite .Pres
  register := .formal
  meaning := {.necessity} ×ˢ {.deontic, .epistemic, .circumstantial}

/-- *should*, the preterite of *shall*, whose most frequent uses are idiomatic: medium strength
deontic and epistemic modality, interchangeable with *ought* ([huddleston-pullum-2002] ch. 3
§9.4). -/
def should : ModalAuxiliary where
  form := "should"
  features := finite .Past
  meaning := {.weakNecessity} ×ˢ {.deontic, .epistemic}

/-- *may*, weak modality ([huddleston-pullum-2002] ch. 3 §9.3): epistemic possibility, and in
formal style deontic permission and dynamic possibility. -/
def may : ModalAuxiliary where
  form := "may"
  features := finite .Pres
  meaning := {.possibility} ×ˢ {.epistemic, .deontic, .circumstantial}

/-- *might*, the preterite of *may*, or for some speakers a lexeme of its own: tentative
epistemic possibility, and the deontic and dynamic uses of *Might I have a little more sugar?*
and *It might be described as an act of provocation* ([huddleston-pullum-2002] ch. 3 §9.8). -/
def might : ModalAuxiliary where
  form := "might"
  features := finite .Past
  meaning := {.possibility} ×ˢ {.epistemic, .deontic, .circumstantial}

/-- *must*, strong modality with no preterite ([huddleston-pullum-2002] ch. 3 §9.3): epistemic
and deontic necessity, and the fairly rare dynamic necessity of an internal need. -/
def must : ModalAuxiliary where
  form := "must"
  features := finite .Pres
  meaning := {.necessity} ×ˢ {.epistemic, .deontic, .circumstantial}

/-- *need*, strong modality with no preterite, confined to non-affirmative contexts
([huddleston-pullum-2002] ch. 3 §2.5.5, §9.3): epistemic in *He needn't have done it
deliberately* and deontic in *You needn't attend the lectures*. -/
def need : ModalAuxiliary where
  form := "need"
  features := finite .Pres
  meaning := {.necessity} ×ˢ {.epistemic, .deontic}

/-- *dare*, confined to non-affirmative contexts ([huddleston-pullum-2002] ch. 3 §2.5.5): the
dynamic modality of *I daren't tell her*, 'have the courage', which its entailments put with
the weak modals (§9.7). -/
def dare : ModalAuxiliary where
  form := "dare"
  features := finite .Pres
  meaning := {.possibility} ×ˢ {.circumstantial}

/-- *ought*, medium strength deontic and epistemic modality like *should*, with a
*to*-infinitival complement and no preterite ([huddleston-pullum-2002] ch. 3 §2.5.4, §9.4). -/
def ought : ModalAuxiliary where
  form := "ought"
  features := finite .Pres
  meaning := {.weakNecessity} ×ˢ {.deontic, .epistemic}

/-! ### *Be*, *have* and *do* -/

/-- *am*, the present of *be* in the first person singular. -/
def am : Auxiliary where
  form := bePresent.form (cell .first .singular)
  features := finite .Pres (some .first) (some .singular)

/-- *is*, the present of *be* in the third person singular. -/
def is_ : Auxiliary where
  form := bePresent.form (cell .third .singular)
  features := finite .Pres (some .third) (some .singular)

/-- *are*, the present of *be* in the second person and the plurals. -/
def are : Auxiliary where
  form := bePresent.form (cell .second .singular)
  features := finite .Pres

/-- *was*, the preterite of *be* in the first and the third person singular. -/
def was : Auxiliary where
  form := bePreterite.form (cell .third .singular)
  features := finite .Past (number := some .singular)

/-- *were*, the preterite of *be* in the second person and the plurals. -/
def were : Auxiliary where
  form := bePreterite.form (cell .second .singular)
  features := finite .Past

/-- *were*, the irrealis of *be*, a form only in the first and the third person singular, *If I
were you*, where it contrasts with the preterite *was* ([huddleston-pullum-2002] ch. 3 §1.7). -/
def wereIrrealis : Auxiliary where
  form := "were"
  features := Features.of (number := some .singular) (verbForm := some .Fin) (mood := some .Irr)

/-- *have*, the plain present of *have*. -/
def have_ : Auxiliary where
  form := havePresent.form (cell .first .singular)
  features := finite .Pres

/-- *has*, the present of *have* in the third person singular. -/
def has : Auxiliary where
  form := havePresent.form (cell .third .singular)
  features := finite .Pres (some .third) (some .singular)

/-- *had*, the preterite of *have*, for every subject. -/
def had : Auxiliary where
  form := "had"
  features := finite .Past

/-- *do*, the plain present of *do*. -/
def do_ : Auxiliary where
  form := doPresent.form (cell .first .singular)
  features := finite .Pres

/-- *does*, the present of *do* in the third person singular. -/
def does : Auxiliary where
  form := doPresent.form (cell .third .singular)
  features := finite .Pres (some .third) (some .singular)

/-- *did*, the preterite of *do*, for every subject. -/
def did : Auxiliary where
  form := "did"
  features := finite .Past

/-- The forms read off the targets are those of the paradigms. -/
example : [am, is_, are, was, were, have_, has, do_, does].map (·.form) =
    ["am", "is", "are", "was", "were", "have", "has", "do", "does"] := by
  decide

/-- The modal auxiliaries. -/
def modals : List ModalAuxiliary :=
  [can, could, will, would, shall, should, may, might, must, need, dare, ought]

/-- The auxiliaries. -/
def allAuxiliaries : List Auxiliary :=
  modals.map (↑) ++ [am, is_, are, was, were, wereIrrealis, have_, has, had, do_, does, did]

/-! ### Negative forms

The negative forms are inflectional forms of the auxiliaries, the suffix *-n't* on a present or
a preterite ([zwicky-pullum-1983]; [huddleston-pullum-2002] ch. 18 §5.5). *mayn't* has virtually
disappeared and *amn't* is dialectal, so that *may* and *am* have none; *aren't* serves the first
person singular in inversion, *Aren't I?*, but not otherwise. -/

/-- The negative form of an auxiliary, informal as the negative forms are
([huddleston-pullum-2002] ch. 3 §1.9). -/
def contract (a : Auxiliary) (form : String) : Auxiliary :=
  { a with form := form, features := update a.features .polarity (some .Neg),
           register := .informal }

/-- *can't*. -/
def cant : Auxiliary := contract can "can't"
/-- *cannot*, a variant of *can't* with the whole of *not* attached, more formal in style
([huddleston-pullum-2002] ch. 18 §5.5). -/
def cannot : Auxiliary := { contract can "cannot" with register := .neutral }
/-- *couldn't*. -/
def couldnt : Auxiliary := contract could "couldn't"
/-- *won't*. -/
def wont : Auxiliary := contract will "won't"
/-- *wouldn't*. -/
def wouldnt : Auxiliary := contract would "wouldn't"
/-- *shan't*. -/
def shant : Auxiliary := contract shall "shan't"
/-- *shouldn't*. -/
def shouldnt : Auxiliary := contract should "shouldn't"
/-- *mightn't*. -/
def mightnt : Auxiliary := contract might "mightn't"
/-- *mustn't*. -/
def mustnt : Auxiliary := contract must "mustn't"
/-- *needn't*. -/
def neednt : Auxiliary := contract need "needn't"
/-- *daren't*. -/
def darent : Auxiliary := contract dare "daren't"
/-- *oughtn't*. -/
def oughtnt : Auxiliary := contract ought "oughtn't"
/-- *isn't*. -/
def isnt : Auxiliary := contract is_ "isn't"
/-- *aren't*. -/
def arent : Auxiliary := contract are "aren't"
/-- *wasn't*. -/
def wasnt : Auxiliary := contract was "wasn't"
/-- *weren't*. -/
def werent : Auxiliary := contract were "weren't"
/-- *weren't*, the negative of the irrealis. -/
def werentIrrealis : Auxiliary := contract wereIrrealis "weren't"
/-- *haven't*. -/
def havent : Auxiliary := contract have_ "haven't"
/-- *hasn't*. -/
def hasnt : Auxiliary := contract has "hasn't"
/-- *hadn't*. -/
def hadnt : Auxiliary := contract had "hadn't"
/-- *don't*, also the negative of the plain form in the imperative, *Don't eat it*. -/
def dont : Auxiliary := contract do_ "don't"
/-- *doesn't*. -/
def doesnt : Auxiliary := contract does "doesn't"
/-- *didn't*. -/
def didnt : Auxiliary := contract did "didn't"

/-- *ain't*, the negative of any present form of *be* and *have*, *am*, *are*, *is*, *have* and
*has*, informal in American English and nonstandard in British ([huddleston-pullum-2002] ch. 18
§5.5). It has no base of its own and is not among `contractions`. -/
def aint : Auxiliary where
  form := "ain't"
  features := update (finite .Pres) .polarity (some .Neg)
  register := .informal

/-- Each auxiliary paired with its negative forms, *can't* before *cannot*. -/
def contractions : List (Auxiliary × Auxiliary) :=
  [(can, cant), (can, cannot), (could, couldnt), (will, wont), (would, wouldnt), (shall, shant),
    (should, shouldnt), (might, mightnt), (must, mustnt), (need, neednt), (dare, darent),
    (ought, oughtnt), (is_, isnt), (are, arent), (was, wasnt), (were, werent),
    (wereIrrealis, werentIrrealis), (have_, havent), (has, hasnt), (had, hadnt), (do_, dont),
    (does, doesnt), (did, didnt)]

/-- The negative forms. -/
def negatives : List Auxiliary := contractions.map (·.2)

/-- The first negative form of an auxiliary, if it has one. -/
def negative (a : Auxiliary) : Option Auxiliary :=
  (contractions.find? (·.1 == a)).map (·.2)

/-! ### The infinitival marker -/

/-- The infinitival marker *to*, UD `PART`, distinct from the preposition `English.Adpositions.to_`:
*John managed to sleep*. -/
def toInf : Word := Word.mk' "to" .PART

end English.Auxiliaries
