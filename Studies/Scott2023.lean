module

public import Linglib.Fragments.Mayan.Mam.Agreement
public import Linglib.Fragments.Mayan.Mam.Pronouns
public import Studies.Harbour2016
public import Linglib.Morphology.DistributedMorphology.VocabularyInsertion.Basic
public import Linglib.Morphology.DistributedMorphology.Impoverishment
public import Linglib.Syntax.Minimalist.Probe.Basic
public import Linglib.Data.Examples.Scott2023
import all Init.Data.String.Defs  -- for unfolding `String.join`

/-!
# Scott (2023): Pronouns and Agreement in San Juan Atitán Mam

This file formalizes the dissertation's account of agreement and pronoun form in San Juan
Atitán Mam. Agreement is copying under the interaction and satisfaction theory of Agree (54): a
probe copies the features of its interaction condition from the first goal that satisfies it. The
probe on Infl (73) interacts with author and number and is satisfied by φ or by transitive Voice
(`inflProbe`), so in a transitive clause it halts at transitive Voice before reaching either
argument and copies nothing (`inflProbe_transitive`), while in an intransitive clause it reaches
the subject (`inflProbe_intransitive`); the agreeing-object grammar of standard Mam differs in the
one disjunct (`standardInflProbe_transitive`). Which head agrees with which argument is read off
the probes (`agreedBy`).

Vocabulary Insertion realizes the copied features by the Extended Subset Principle (53) over the
Vocabulary of Tables 4.7, 4.8 and 4.10 and of (59), (65) and (66) (`vocabulary`), which derives
the Fragment's Set A and Set B paradigms (`setA_realize`, `setB_realize`) and the default Set B
of a transitive clause, where Infl carries no φ (`setB_transitive`). A pronoun hosts every item
its features license, so first-person pronouns are bimorphemic (§4.4.1, `insertAll`). A probe
that copies a goal's features flags the goal with its category (§4.4.3.2, `Feat.flag`), and the
impoverishment rule (84) deletes number from a flagged first-person pronoun (`rule84`), bleeding
the bases *qin* and *qo*: the reduced subject and possessor series and the full independent series
of Table 4.25 are both derived from one Vocabulary (`form_flagged`, `form_unflagged`), and the
optional rule (93) reduces second-person plural in Set A contexts alone (`form_rule93`). The
dissertation's judgments (`Data/Examples/Scott2023`) instantiate the derivation
(`pronoun_rows`).

## Implementation notes

* Features are Harbour's bivalent person and number features (Table 4.4) with the head a Set A
  or Set B terminal sits on and the flag a copying probe leaves; the person features of a cell
  are Harbour's signs of its referential category (`Harbour2016.signOf`), and the two pronoun
  series the derivation targets are the fragment's `Mam.independent` and `Mam.subjPoss`.
  Contextual specifications of Vocabulary Items are features of the same terminal, so the
  Extended Subset Principle is the substrate's `subsetPrinciple` over sites.
* Multiple insertion (§4.4.1) is read with the Extended Subset Principle: every applicable item
  is inserted unless a more specific applicable item realizes what it realizes, which is what
  keeps the generic plural *qa* out of the second-person plural *q=i*.
* The object is licensed by Voice under pure satisfaction (§4.4.4.1), a probe that copies
  nothing and so flags nothing; only the φ-copying probes are modeled, so the object is unflagged.
* Search domains are the clause spines of (56), (60) and (64): in a transitive clause Infl
  encounters transitive Voice first, then the object, which has moved above the subject (§3.4.1).
* The default Set A of super-extended ergative clauses (§2.6.3, §3.4.3.3) is data here; the
  dissertation leaves its derivation open.

## References

* [scott-2023]
* [deal-2024]
* [harbour-2016]
* [noyer-1992]
-/

@[expose] public section

open Mam DistributedMorphology Minimalist Morphology

namespace Scott2023

/-! ### Features and Vocabulary -/

/-- The loci of agreement are Infl, the Set B locus, and v/n, Voice or Poss, the Set A locus (Tables
4.7, 4.8). -/
inductive Locus
  | infl | vn
  deriving DecidableEq, Repr

/-! ### The cells -/

/-- The seven person–number cells of the pronominal paradigm (Table 4.4), the quadripartition
of persons crossed with number less the impossible first person singular inclusive. -/
inductive PronCell where
  | firstSg | firstPlExcl | firstPlIncl
  | secondSg | secondPl
  | thirdSg | thirdPl
  deriving DecidableEq, Repr

/-- The referential category of a cell. -/
def PronCell.category : PronCell → Person.Category
  | .firstSg => .speaker
  | .firstPlExcl => .speakerOthers
  | .firstPlIncl => .speakerAddressee
  | .secondSg => .addressee
  | .secondPl => .addresseeOthers
  | .thirdSg => .other
  | .thirdPl => .others

/-- The person of a cell as the agreement paradigms see it, first against non-first. -/
def PronCell.person : PronCell → Person
  | .firstSg | .firstPlExcl | .firstPlIncl => .first
  | .secondSg | .secondPl => .second
  | .thirdSg | .thirdPl => .third

/-- The number of a cell. -/
def PronCell.number : PronCell → Number
  | .firstSg | .secondSg | .thirdSg => .singular
  | .firstPlExcl | .firstPlIncl | .secondPl | .thirdPl => .plural

/-- The cell of the fragment's pronoun paradigms, with clusivity on the person. -/
def PronCell.bundle : PronCell → Agreement.Bundle
  | .firstSg => .personNumber .first .singular
  | .firstPlExcl => .personNumber .firstExclusive .plural
  | .firstPlIncl => .personNumber .firstInclusive .plural
  | .secondSg => .personNumber .second .singular
  | .secondPl => .personNumber .second .plural
  | .thirdSg => .personNumber .third .singular
  | .thirdPl => .personNumber .third .plural

/-- The person features of a cell (Table 4.4) are Harbour's sign of its category, [±author] and
[±participant], the latter an addressee feature under which the first person singular and
exclusive are [−participant]. -/
def PronCell.sign (c : PronCell) : Person.Feature → Bool := Harbour2016.signOf c.category

/-- Whether a cell is singular. -/
def PronCell.singular (c : PronCell) : Bool := c.number = .singular

/-- The fragment's independent pronoun of a cell. -/
def independentOf (c : PronCell) : Option PersonalPronoun := Mam.independent.realize c.bundle

/-- The fragment's subject and possessor pronoun of a cell. -/
def subjPossOf (c : PronCell) : Option PersonalPronoun := Mam.subjPoss.realize c.bundle

/-! ### Features and Vocabulary Items -/

/-- A feature of a terminal is one of Harbour's bivalent person and number features (Table 4.4), the
locus a Set A or Set B terminal sits on, or the flag a probe leaves on a goal whose features it has
copied (§4.4.3.2, Table 4.26). -/
inductive Feat
  | author (b : Bool)
  | participant (b : Bool)
  | singular (b : Bool)
  | head (l : Locus)
  | flag (l : Locus)
  deriving DecidableEq, Repr

/-- The features of a pronoun in a paradigm cell (Table 4.4). -/
def cellFeats (c : PronCell) : List Feat :=
  [.author (c.sign .author), .participant (c.sign .participant), .singular c.singular]

/-- A Vocabulary Item, as the dissertation writes them, has the features it realizes, its contextual
specification, and its exponent. -/
structure Item where
  realized : List Feat
  context : List Feat := []
  exponent : Morph
  deriving DecidableEq, Repr

/-- Everything an item requires of its terminal. -/
def Item.site (i : Item) : List Feat := i.realized ++ i.context

/-- The item for the substrate's Subset Principle keeps its site and exponent. -/
def Item.toVI (i : Item) : VocabularyItem Feat Morph := i.site.toFinset ⟷ i.exponent

/-- The Vocabulary lists Set A (Table 4.7), Set B with its context-free first-person plural and its
Elsewhere item (Table 4.8), the pronominal base *qin* (Table 4.10), the plurals *q* and *qa* ((65),
(66)), and the disagreement enclitic at its two disagreeing values (59), listed last as the items
are linearized in Vocabulary order. -/
def vocabulary : List Item :=
  [ ⟨[.author true, .singular true], [.head .vn], .pref "n"⟩,
    ⟨[.author false, .singular true], [.head .vn], .pref "t"⟩,
    ⟨[.author true, .singular false], [.head .vn], .pref "q"⟩,
    ⟨[.author false, .singular false], [.head .vn], .pref "ky"⟩,
    ⟨[.author true, .singular true], [.head .infl], .free "chin"⟩,
    ⟨[], [.head .infl], .procl "tz'"⟩,
    ⟨[.author true, .singular false], [], .free "qo"⟩,
    ⟨[.author false, .singular false], [.head .infl], .free "chi"⟩,
    ⟨[.author true, .singular true], [], .free "qin"⟩,
    ⟨[.singular false], [.author false, .participant true], .free "q"⟩,
    ⟨[.singular false], [], .free "qa"⟩,
    ⟨[.author true, .participant false], [], .encl "i"⟩,
    ⟨[.author false, .participant true], [], .encl "i"⟩ ]

/-- Single insertion at an agreement terminal inserts the most specific applicable item, by the
Extended Subset Principle (53). -/
def insert1 (t : List Feat) : Option Morph :=
  subsetPrinciple (vocabulary.map Item.toVI) (t.toFinset : Finset Feat)

/-- Multiple insertion at a pronoun (§4.4.1) inserts every applicable item, unless a more specific
applicable item realizes what it realizes. -/
def insertAll (t : List Feat) : List Morph :=
  let app := vocabulary.filter fun i ↦ i.site.all (· ∈ t)
  (app.filter fun i ↦ !app.any fun j ↦
      j != i && i.realized.all (· ∈ j.realized) && i.site.all (· ∈ j.site)).map Item.exponent

/-! ### Agreement (§3.4.2, §4.4.2) -/

/-- On its search a probe meets an argument bearing φ, or the transitive Voice head. -/
structure Encounter where
  role : Option ArgumentRole
  phi : Bool
  voiceTR : Bool
  deriving DecidableEq, Repr

/-- The transitive Voice head. -/
def voiceTR : Encounter := ⟨none, false, true⟩

/-- An argument bearing φ. -/
def dp (r : ArgumentRole) : Encounter := ⟨some r, true, false⟩

/-- The probe on Infl (73) interacts with φ and is satisfied by φ or by transitive Voice, so either
halts it, and it agrees with a goal only if the goal bears φ. -/
def inflProbe : Probe Encounter := { int := fun e ↦ e.phi, sat := fun e ↦ e.phi || e.voiceTR }

/-- The probe on Infl of the agreeing-object grammar (56), satisfied by φ alone. -/
def standardInflProbe : Probe Encounter := Probe.relativized (·.phi)

/-- The probe on Voice or Poss, satisfied by the φ of its specifier. -/
def vnProbe : Probe Encounter := Probe.relativized (·.phi)

/-- Infl's search domain in the clause of an argument (60), (64) is transitive Voice, then the
object, which has moved above the subject, then the subject; or the intransitive subject. -/
def inflDomain : ArgumentRole → List Encounter
  | .A | .P => [voiceTR, dp .P, dp .A]
  | .S => [dp .S]
  | .R | .T => []

/-- The search domain of Voice or Poss is its specifier, the transitive subject. -/
def vnDomain : ArgumentRole → List Encounter
  | .A => [dp .A]
  | _ => []

/-- In a transitive clause Infl's probe halts at transitive Voice and agrees with nothing,
whatever lies below (60), (61). -/
theorem inflProbe_transitive (rest : List Encounter) :
    inflProbe.goal (voiceTR :: rest) = none := rfl

/-- In an intransitive clause Infl's probe agrees with the subject (64). -/
theorem inflProbe_intransitive : inflProbe.goal [dp .S] = some (dp .S) := rfl

/-- Under the agreeing-object grammar Infl's probe passes transitive Voice and agrees with the
object (56), (57). -/
theorem standardInflProbe_transitive (rest : List Encounter) :
    standardInflProbe.goal (voiceTR :: dp .P :: rest) = some (dp .P) := rfl

/-- The probe that copies an argument's features sits on Infl for the intransitive subject and on
Voice or Poss for the transitive subject; no probe copies the object's. -/
def agreedBy (r : ArgumentRole) : Option Locus :=
  if (inflProbe.goal (inflDomain r)).bind (·.role) = some r then some .infl
  else if (vnProbe.goal (vnDomain r)).bind (·.role) = some r then some .vn
  else none

theorem agreedBy_S : agreedBy .S = some .infl := rfl
theorem agreedBy_A : agreedBy .A = some .vn := rfl
theorem agreedBy_P : agreedBy .P = none := rfl

/-- A probe copies author and number (73a). -/
def copied (c : PronCell) : List Feat := [.author (c.sign .author), .singular c.singular]

/-- The Set B terminal on Infl in the clause of an argument in a cell carries the copied features if
Infl agreed with the argument, at the Infl locus. -/
def inflTerminal (r : ArgumentRole) (c : PronCell) : List Feat :=
  (if agreedBy r = some .infl then copied c else []) ++ [.head .infl]

/-- The Set A terminal on Voice or Poss agreeing with a cell. -/
def vnTerminal (c : PronCell) : List Feat := copied c ++ [.head .vn]

/-- The Set B paradigm (Table 4.6) is the Vocabulary's spell-out of what Infl copies from an
intransitive subject. -/
theorem setB_realize (c : PronCell) :
    setBExponent.realize (.personNumber c.person c.number) =
      (insert1 (inflTerminal .S c)).map ([·]) := by
  cases c <;> decide

/-- By default Set B (61), with no features copied, inserts the Elsewhere item *tz'=*, whatever the
object's cell. -/
theorem setB_transitive (c : PronCell) : insert1 (inflTerminal .P c) = some (.procl "tz'") := by
  cases c <;> decide

/-- The Fragment's Set A paradigm (Table 4.5, pre-consonantal) is the Vocabulary's spell-out of
what Voice or Poss copies. -/
theorem setA_realize (c : PronCell) :
    (setAExponent .consonant).realize (.personNumber c.person c.number)
      = (insert1 (vnTerminal c)).map ([·]) := by
  cases c <;> decide

-- Table 4.10
theorem chin_beats_qin :
    insert1 (copied .firstSg ++ [.head .infl]) = some (.free "chin") ∧
      insert1 (copied .firstSg) = some (.free "qin") := by
  decide

/-! ### Pronoun form (§4.4) -/

/-- The dimension an impoverishment rule deletes. -/
inductive Dim
  | author | participant | singular
  deriving DecidableEq, Repr

/-- Delete a dimension from a terminal. -/
def delete (t : List Feat) (d : Dim) : List Feat :=
  t.filter fun f ↦ match f, d with
    | .author _, .author | .participant _, .participant | .singular _, .singular => false
    | _, _ => true

/-- Whether a terminal carries the flag of some probe. -/
def flagged (t : List Feat) : Bool := t.any fun f ↦ match f with | .flag _ => true | _ => false

/-- The impoverishment rule (84) deletes number from a first-person pronoun a probe has flagged. -/
def rule84 : ImpoverishmentRule (List Feat) Dim :=
  .ofFocus (fun t ↦ Feat.author true ∈ t ∧ flagged t) .singular

/-- The optional rule (93) deletes number from a second-person pronoun flagged by Voice or Poss. -/
def rule93 : ImpoverishmentRule (List Feat) Dim :=
  .ofFocus (fun t ↦ Feat.participant true ∈ t ∧ Feat.flag .vn ∈ t) .singular

theorem rule84_paradigmatic : rule84.Paradigmatic :=
  ImpoverishmentRule.paradigmatic_ofFocus _ _

/-- A pronoun terminal in a cell, flagged by the probe that copied its features, if any. -/
def pronounTerminal (l : Option Locus) (c : PronCell) : List Feat :=
  cellFeats c ++ (l.map fun l ↦ [Feat.flag l]).getD []

/-- The form of a pronoun in a cell under a grammar with impoverishment rules `rules`, flagged
by `l`, in which the rules apply and every licensed item is inserted. -/
def formWith (rules : List (ImpoverishmentRule (List Feat) Dim)) (l : Option Locus) (c : PronCell) :
    List Morph :=
  insertAll (runChain (ImpoverishmentRule.apply delete) rules ↑(pronounTerminal l c))

/-- The form of a pronoun under the grammar of (84). -/
def form (l : Option Locus) (c : PronCell) : List Morph := formWith [rule84] l c

/-- The morphemes of the Fragment's pronoun entries (Table 4.9) are *qin=i*, *qo'=y*, *qo*, *=i*,
*q=i*, *qa*, and the null third-person singular. -/
def morphemes : Option PersonalPronoun → List Morph
  | some p =>
    if p = qini then [.free "qin", .encl "i"]
    else if p = qoy then [.free "qo", .encl "i"]
    else if p = qo then [.free "qo"]
    else if p = iDisagr then [.encl "i"]
    else if p = qi then [.free "q", .encl "i"]
    else if p = qa then [.free "qa"]
    else []
  | none => []

/-- In the independent series (Table 4.25), an unflagged pronoun, an object or the subject of a
non-verbal predicate, hosts every item its features license. -/
theorem form_unflagged (c : PronCell) : form none c = morphemes (independentOf c) := by
  cases c <;> decide

/-- In the subject and possessor series (Table 4.25), a flagged first-person pronoun loses its
number, bleeding *qin* and *qo*. -/
theorem form_flagged (l : Locus) (c : PronCell) : form (some l) c = morphemes (subjPossOf c) := by
  cases l <;> cases c <;> decide

/-- With the optional rule (93), second-person plural reduces to the enclitic in a Set A context
but not in a Set B context ((89)–(91)). -/
theorem form_rule93 :
    formWith [rule84, rule93] (some .vn) .secondPl = [.encl "i"] ∧
      formWith [rule84, rule93] (some .infl) .secondPl = morphemes (subjPossOf .secondPl) := by
  decide

/-- An argument in a cell takes the form flagged by the probe that agreed with it. -/
def formAt (r : ArgumentRole) (c : PronCell) : List Morph := form (agreedBy r) c

-- (3), (8)
theorem formAt_eq (c : PronCell) :
    formAt .S c = morphemes (subjPossOf c) ∧ formAt .A c = morphemes (subjPossOf c) ∧
      formAt .P c = morphemes (independentOf c) :=
  ⟨form_flagged .infl c, form_flagged .vn c, form_unflagged c⟩

-- §4.3.3 [noyer-1992]
theorem encl_mem_independent_iff (c : PronCell) :
    Morph.encl "i" ∈ morphemes (independentOf c) ↔ c.sign .author ≠ c.sign .participant := by
  cases c <;> decide

-- Table 4.1
theorem reduced_iff_author (c : PronCell) :
    subjPossOf c ≠ independentOf c ↔ c.sign .author = true := by
  cases c <;> decide

/-! ### The judgments -/

/-- A pronoun is spelled as its morphemes with clitic boundaries. -/
def spell (ms : List Morph) : String :=
  String.join (ms.map fun m ↦ match m.kind with
    | .bound .after .clitic => "=" ++ m.form
    | _ => m.form)

/-- A judgment of the pool records the position's flag, the cell, the pronoun, whether the optional
rule (93) is in force, and the judgment. -/
structure Row where
  flag : Option Locus
  cell : PronCell
  pronoun : String
  optional : Bool
  accepted : Bool
  deriving DecidableEq, Repr

def Row.ofDatum (ex : Datum) : Option Row := do
  let fs := ex.paperFeatures
  let flag ← match fs.lookup "position" with
    | some "S" => some (some Locus.infl)
    | some "A" | some "possessor" => some (some Locus.vn)
    | some "object" | some "unagreed" => some none
    | _ => none
  let cell ← match fs.lookup "cell" with
    | some "1sg" => some PronCell.firstSg | some "1plExcl" => some PronCell.firstPlExcl
    | some "1plIncl" => some PronCell.firstPlIncl | some "2sg" => some PronCell.secondSg
    | some "2pl" => some PronCell.secondPl | some "3sg" => some PronCell.thirdSg
    | some "3pl" => some PronCell.thirdPl | _ => none
  let pronoun ← fs.lookup "morphemes"
  pure ⟨flag, cell, pronoun, fs.lookup "optionalReduction" = some "yes",
    ex.judgment = .acceptable⟩

/-- The pronoun judgments of §4.4. -/
def rows : List Row := Examples.all.filterMap Row.ofDatum

/-- A pronoun is accepted exactly when it is the derived form, under (84) or, where the row
invokes it, the optional (93). -/
theorem pronoun_rows :
    ∀ r ∈ rows, (r.accepted = true ↔
      spell (form r.flag r.cell) = r.pronoun ∨
        (r.optional = true ∧ spell (formWith [rule84, rule93] r.flag r.cell) = r.pronoun)) := by
  decide

end Scott2023
