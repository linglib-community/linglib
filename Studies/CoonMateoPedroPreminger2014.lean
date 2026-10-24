module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Syntax.Minimalist.Verbal.Voice
public import Linglib.Fragments.Mayan.Qanjobal.Agreement
public import Linglib.Fragments.Mayan.Qanjobal.Extraction
public import Linglib.Fragments.Mayan.Chol.Agreement
public import Linglib.Fragments.Mayan.Kaqchikel.Agreement
public import Linglib.Fragments.Mayan.Kaqchikel.Extraction
public import Linglib.Fragments.Mayan.Tseltal.Agreement
public import Linglib.Fragments.Mayan.Tsotsil.Agreement
public import Linglib.Fragments.Mayan.Tsotsil.Extraction
public import Linglib.Fragments.Mayan.Chol.Extraction
public import Linglib.Fragments.Mayan.Tseltal.Extraction
public import Linglib.Fragments.Mayan.Mam.Agreement
public import Linglib.Fragments.Mayan.Mam.Extraction
public import Linglib.Fragments.Mayan.Kiche.Agreement
public import Linglib.Fragments.Mayan.Kiche.Extraction
public import Linglib.Fragments.Mayan.Yukatek.Agreement
public import Linglib.Data.Examples.CoonMateoPedroPreminger2014

/-!
# Coon, Mateo Pedro and Preminger (2014): The role of Case in A-bar extraction asymmetries

Many Mayan languages cannot extract the subject of a regular transitive clause and use the Agent
Focus form of the verb instead. Coon, Mateo Pedro and Preminger trace this syntactic ergativity
to the Case of the object rather than to the ergative subject. Following Legate and Aldridge,
every Mayan language licenses the transitive subject low, from v, but the object is licensed
either by Infl, where the absolutive marker sits high on the aspect marker, or by v, where it
sits low on the stem. A transitive verb phrase is a phase with a single escape hatch that
contains the subject, so an object that must reach Infl takes the hatch and traps the subject,
which is Tada's generalization, and in a non-finite clause, which lacks Infl, it has no Case at
all. The Q'anjob'al Agent Focus suffix *-on* is a marked Voice that cases the object itself, so
no ergative is assigned and v is intransitive, non-phasal and spelled out by the intransitive
status suffix; it frees the subject, licenses non-finite transitives (the Crazy Antipassive),
and as a last resort fails with reflexive and bare objects, which need no Case and let the
subject of a regular transitive extract.

## Main statements

* `tada`: a registered language marks the extraction of a core argument from a finite transitive
  exactly when the regular derivation fails, which for the subject is when the absolutive is
  high.
* `converges_iff_verbForm`: in Q'anjob'al the derivation that converges uses the verb form the
  fragment records, Agent Focus in every non-finite transitive and under extraction of a
  third-person subject.
* `formallyTransitive_iff_hasSetA`, `formallyTransitive_iff_statusSuffix`: Agent Focus selects
  intransitive v, so it has no Set A and takes the intransitive status suffix.
* `analysed_rows`: every analysed example is grammatical exactly when its clause converges.

## Implementation notes

* The paper's v sits above the substrate's Voice head and is formally transitive when Voice
  would head a phase by Chomsky's criterion and leaves the object's Case to Infl or v;
  phasehood, Set A and the status suffix are read off that one property.
* Trapping builds in the subject's position inside the phase and the single escape hatch, as
  the paper assumes them.
* The last resort is the paper's later formulation, that the Case-checking Voice merges only
  where the regular derivation would leave the object without Case or trap the extracting
  subject.
* Rows carry the paper's high or low classification of their language, checked against the
  fragment's verbal template; Kaqchikel Agent Focus and the nominal-stem and passive strategies
  for non-finite transitives are recorded as rows without a configuration.

## TODO

- The person restriction on Agent Focus (72), which the paper tentatively derives by
  base-generating first- and second-person agents high, is not modelled, so
  `converges_iff_verbForm` is stated for third-person agents.
- Agent Focus with reflexive objects in non-finite clauses, which the paper's fn. 31 records and
  leaves unexplained, does not converge here either.
- Trapping could be derived from `SyntacticObject.phaseEdge` on the tree (55) once the substrate
  bounds the number of specifiers at a phase edge.
- The extraction of low adverbs and the instrumental voice (§5.3) are not modelled.

## References

* [J. Coon, P. Mateo Pedro and O. Preminger, *The role of Case in A-bar extraction
  asymmetries: Evidence from Mayan* (2014)][coon-mateo-pedro-preminger-2014]
* [J. A. Legate, *Morphological and abstract case* (2008)][legate-2008]
* [E. Aldridge, *Ergativity and word order in Austronesian languages* (2004)][aldridge-2004]
* [H. Tada, *A/A-bar partition in derivation* (1993)][tada-1993]
* [N. Chomsky, *Derivation by Phase* (2001)][chomsky-2001]
* [H. Harley, *External arguments and the Mirror Principle: On the distinctness of Voice and v*
  (2013)][harley-2013]
* [F. Ordóñez, *The antipassive in Jacaltec: A last resort strategy* (1995)][ordonez-1995]
* [D. Massam, *Pseudo noun incorporation in Niuean* (2001)][massam-2001]
* [L. Hou, *Agent focus in Chuj reflexive constructions* (2013)][hou-2013]
-/

@[expose] public section

namespace CoonMateoPedroPreminger2014

open Minimalist Minimalist.Voice Mayan

/-! ### Clauses -/

/-- The heads that assign structural Case (5). -/
inductive Licenser where
  | infl
  | v
  deriving DecidableEq, Repr

/-- The head licensing transitive objects is read off the absolutive's position (24): Infl when
the absolutive is high, so that it is nominative ([legate-2008]'s ABS=NOM), and v when it is
low, so that it is a default (ABS=DEF). -/
def Licenser.ofPosition : ABSPosition → Licenser
  | .high => .infl
  | .low => .v

/-- What a transitive verb takes as its object. -/
inductive Object where
  /-- A full DP, which needs structural Case and satisfies the EPP of v. -/
  | dp
  /-- A reflexive, extended reflexive or bare NP, pseudo-incorporated ([massam-2001]) and
  needing neither (§5.2). -/
  | caseless
  /-- An object licensed inside its own oblique phrase, the demoted patient of an antipassive
  (59) or the relational-noun complement of a Mam infinitive (39a). -/
  | oblique
  deriving DecidableEq, Repr, Fintype

/-- Agent Focus as the marked Voice (66), agentive Voice that also assigns structural Case to
the object. -/
def voiceAF : Head := { agentive with checksCase := true }

/-- The verb phrase of a clause, an intransitive with the marker series of its sole argument or
a transitive with its Voice and its object. -/
inductive Predicate where
  | intransitive (marking : MarkerSet)
  | transitive (voice : Head) (object : Object)
  deriving DecidableEq

/-- A clause, with the head licensing its object, its finiteness, its verb phrase, the argument
extracted and whether an adverb separates the verb from its object. -/
structure Clause where
  /-- The head licensing transitive objects. -/
  licenser : Licenser
  /-- Whether the clause has finite Infl, the preverbal aspect marker. -/
  finite : Bool
  /-- The verb phrase. -/
  predicate : Predicate
  /-- The argument A-bar extracted, if any. -/
  extracted : Option ArgumentRole := none
  /-- Whether adverbial material separates the verb from its object (81). -/
  separated : Bool := false
  deriving DecidableEq

namespace Predicate

/-- The Voice head of a transitive verb phrase. -/
def voice? : Predicate → Option Head
  | .transitive v _ => some v
  | .intransitive _ => none

/-- The object of a transitive verb phrase. -/
def object? : Predicate → Option Object
  | .transitive _ o => some o
  | .intransitive _ => none

/-- The marker series of an intransitive subject. -/
def marking? : Predicate → Option MarkerSet
  | .intransitive m => some m
  | .transitive _ _ => none

/-- The same verb phrase under regular transitive Voice, the derivation Agent Focus competes
with. -/
def regular : Predicate → Predicate
  | .transitive _ o => .transitive agentive o
  | p => p

/-- The verb phrase has formally transitive v, the phase head above Voice that assigns ergative
to the subject and is spelled out by the status suffix ((55), [harley-2013]). It is selected by
a Voice head that would head a phase by [chomsky-2001]'s criterion, unless that head cases the
object itself and so leaves no ergative to assign (§4.2). -/
def FormallyTransitive (p : Predicate) : Prop := ∃ v ∈ p.voice?, v.IsPhasal ∧ ¬ v.ChecksCase

/-- The Voice checks the object's Case, as Agent Focus does. -/
def ChecksCase (p : Predicate) : Prop := ∃ v ∈ p.voice?, v.ChecksCase

/-- The object raises to the edge of the verb phrase: Case is assigned within the phase and
Infl sits outside it, so a full DP object licensed by Infl must reach the edge (51), which the
EPP of eventive v keeps true under Agent Focus (66); an object licensed by v stays in situ
(52). -/
def Raises (p : Predicate) (l : Licenser) : Prop := p.object? = some .dp ∧ l = .infl

/-- The object's Case is available (27): Voice checks it, v assigns it, or finite Infl does; a
caseless or oblique object needs none. The low-abs non-finite cell takes the embedded clause
to contain v, which the paper's fn. 12 leaves open. -/
def ObjectLicensed (p : Predicate) (l : Licenser) (finite : Bool) : Prop :=
  p.object? = some .dp → p.ChecksCase ∨ l = .v ∨ finite = true

/-- The absolutive on an intransitive subject needs finite Infl ((32), (33)); the
ergative/possessive marking of a non-finite one is the nominalization's. -/
def SubjectLicensed (p : Predicate) (finite : Bool) : Prop :=
  p.marking? = some .setB → finite = true

/-- A pseudo-incorporated object stays adjacent to the verb, the Chuj contrast (81) of
[hou-2013]; the paper's fn. 28 notes that the word-order reflex does not hold of Q'anjob'al
extended reflexives. -/
def Adjacent (p : Predicate) (separated : Bool) : Prop :=
  p.object? = some .caseless → separated = false

instance : DecidablePred FormallyTransitive := fun p ↦
  inferInstanceAs (Decidable (∃ v ∈ p.voice?, _))
instance : DecidablePred ChecksCase := fun p ↦ inferInstanceAs (Decidable (∃ v ∈ p.voice?, _))
instance (p : Predicate) (l : Licenser) : Decidable (p.Raises l) :=
  inferInstanceAs (Decidable (_ ∧ _))
instance (p : Predicate) (l : Licenser) (b : Bool) : Decidable (p.ObjectLicensed l b) :=
  inferInstanceAs (Decidable (_ → _))
instance (p : Predicate) (b : Bool) : Decidable (p.SubjectLicensed b) :=
  inferInstanceAs (Decidable (_ → _))
instance (p : Predicate) (b : Bool) : Decidable (p.Adjacent b) :=
  inferInstanceAs (Decidable (_ → _))

end Predicate

/-! ### Trapping -/

/-- The subject is trapped (53): the raised object takes the single escape hatch of the phasal
verb phrase, inside which the subject is generated, the three factors of (89). -/
def Trapped (c : Clause) : Prop :=
  c.predicate.FormallyTransitive ∧ c.predicate.Raises c.licenser

instance : DecidablePred Trapped := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- Where v licenses the object nothing is trapped (52): the object never raises. -/
theorem not_trapped_of_v {c : Clause} (h : c.licenser = .v) : ¬ Trapped c :=
  fun ht ↦ by simpa [Predicate.Raises, h] using ht.2

/-- A language is syntactically ergative when the subject of a finite regular transitive with a
full DP object is trapped when extracted (21c). -/
def SyntacticallyErgative (l : Licenser) : Prop :=
  Trapped ⟨l, true, .transitive agentive .dp, some .A, false⟩

instance : DecidablePred SyntacticallyErgative := fun _ ↦ inferInstanceAs (Decidable (Trapped _))

/-- A language bans subject extraction exactly when Infl licenses the object ((19), (24)). -/
theorem syntacticallyErgative_iff (l : Licenser) : SyntacticallyErgative l ↔ l = .infl := by
  cases l <;> decide

/-! ### Case configurations -/

/-- A clausal Case configuration (3), with the licensers of the transitive subject and of the
object, where Infl licenses at most one of them. -/
structure Configuration where
  /-- The head licensing the transitive subject. -/
  subject : Licenser
  /-- The head licensing the transitive object. -/
  object : Licenser
  /-- Infl licenses at most one argument. -/
  infl_once : subject = .infl → object = .v

/-- A configuration is morphologically ergative when v licenses the transitive subject. -/
def Configuration.MorphologicallyErgative (k : Configuration) : Prop := k.subject = .v

/-- Syntactic ergativity entails morphological ergativity (10), since Infl licensing the object
leaves the subject to v. -/
theorem morphologicallyErgative_of_syntacticallyErgative (k : Configuration)
    (h : SyntacticallyErgative k.object) : k.MorphologicallyErgative := by
  rw [syntacticallyErgative_iff] at h
  cases hs : k.subject
  · exact absurd (k.infl_once hs) (by simp [h])
  · exact hs

/-- The converse fails (10): the default-absolutive configuration is morphologically but not
syntactically ergative. -/
theorem v_not_syntacticallyErgative :
    (⟨.v, .v, nofun⟩ : Configuration).MorphologicallyErgative ∧ ¬ SyntacticallyErgative .v :=
  ⟨rfl, by decide⟩

/-! ### Convergence -/

/-- The same clause under regular transitive Voice. -/
def Clause.regular (c : Clause) : Clause := { c with predicate := c.predicate.regular }

/-- The regular derivation crashes: its object is unlicensed, or its extracting subject is
trapped. -/
def RegularCrashes (c : Clause) : Prop :=
  ¬ c.regular.predicate.ObjectLicensed c.licenser c.finite ∨
    (c.extracted = some .A ∧ Trapped c.regular)

instance : DecidablePred RegularCrashes := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- Agent Focus is a last resort ([ordonez-1995]; §4.2, §5.1): the Case-checking Voice merges
only where the object would otherwise lack a source of Case or trap the extracting subject. -/
def LastResort (c : Clause) : Prop := c.predicate.ChecksCase → RegularCrashes c

instance : DecidablePred LastResort := fun _ ↦ inferInstanceAs (Decidable (_ → _))

/-- A clause converges when its object and intransitive subject are licensed, an extracted
subject is not trapped, a Case-checking Voice is a last resort, and a pseudo-incorporated
object is adjacent to the verb. -/
def Converges (c : Clause) : Prop :=
  c.predicate.ObjectLicensed c.licenser c.finite ∧ c.predicate.SubjectLicensed c.finite ∧
    (c.extracted = some .A → ¬ Trapped c) ∧ LastResort c ∧ c.predicate.Adjacent c.separated

instance : DecidablePred Converges := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- Non-finite licensing (27): a regular transitive object survives without Infl exactly where
v licenses it, and an absolutive intransitive subject only under finite Infl. -/
theorem nonfinite_licensing (l : Licenser) :
    ((Predicate.transitive agentive .dp).ObjectLicensed l false ↔ l = .v) ∧
      ¬ (Predicate.intransitive .setB).SubjectLicensed false := by
  cases l <;> decide

/-- Agent Focus in a high-abs language frees the extracting subject (67) and licenses the object of
a non-finite transitive (70), where the regular derivation crashes. -/
theorem agent_focus :
    Converges ⟨.infl, true, .transitive voiceAF .dp, some .A, false⟩ ∧
    ¬ Converges ⟨.infl, true, .transitive agentive .dp, some .A, false⟩ ∧
    Converges ⟨.infl, false, .transitive voiceAF .dp, none, false⟩ ∧
    ¬ Converges ⟨.infl, false, .transitive agentive .dp, none, false⟩ := by
  decide

/-- Agent Focus is barred without subject extraction in finite clauses, in low-abs languages, and
with a caseless object (75b), where a regular transitive suffices (75a). -/
theorem last_resort :
    ¬ Converges ⟨.infl, true, .transitive voiceAF .dp, none, false⟩ ∧
    ¬ Converges ⟨.v, true, .transitive voiceAF .dp, some .A, false⟩ ∧
    ¬ Converges ⟨.infl, true, .transitive voiceAF .caseless, some .A, false⟩ ∧
    Converges ⟨.infl, true, .transitive agentive .caseless, some .A, false⟩ := by
  decide

/-- The antipassive frees the subject (60) on either count: its v is intransitive, and its
oblique patient never raises to the edge. -/
theorem antipassive_frees (l : Licenser) :
    ¬ (Predicate.transitive antipassive .oblique).FormallyTransitive ∧
      ¬ (Predicate.transitive antipassive .oblique).Raises l ∧
        ¬ Trapped ⟨l, true, .transitive antipassive .oblique, some .A, false⟩ := by
  cases l <;> decide

/-! ### Agent Focus and intransitive v -/

/-- The Voice head of each verb form, regular Voice for the transitive and the marked Voice for
Agent Focus. -/
def voiceOf : VerbForm → Head
  | .transitive => agentive
  | .agentFocus => voiceAF

/-- A form has Set A exactly when its v is formally transitive: the ergative that transitive v
assigns is absent under Agent Focus (§4.1, §4.2). -/
theorem formallyTransitive_iff_hasSetA (f : VerbForm) (o : Object) :
    (Predicate.transitive (voiceOf f) o).FormallyTransitive ↔ f.HasSetA := by
  decide +revert

/-- The Q'anjob'al status suffix spells out v ((55), (65)): transitive *-V'* exactly when v is
formally transitive, intransitive *-i* under Agent Focus. -/
theorem formallyTransitive_iff_statusSuffix (f : VerbForm) (o : Object) :
    (Predicate.transitive (voiceOf f) o).FormallyTransitive ↔
      Qanjobal.StatusSuffix.ofVerbForm f = .tv := by
  decide +revert

/-! ### The Mayan fragments -/

/-- The Mayan languages with registered fragments. -/
inductive Language where
  | chol | qanjobal | kaqchikel | tseltal | tsotsil | mam | kiche | yukatek
  deriving DecidableEq, Repr, Fintype

namespace Language

/-- The Glottolog code of a language, the key the rows carry. -/
def glottocode : Language → String
  | .chol => "chol1282"
  | .qanjobal => "qanj1241"
  | .kaqchikel => "kaqc1270"
  | .tseltal => "tzel1254"
  | .tsotsil => "tzot1259"
  | .mam => "mamm1241"
  | .kiche => "kich1262"
  | .yukatek => "yuca1254"

/-- The verbal complex of a language, from its fragment. -/
def template : Language → Morphology.AffixTemplate VerbSlot
  | .chol => Chol.template
  | .qanjobal => Qanjobal.template
  | .kaqchikel => Kaqchikel.template
  | .tseltal => Tseltal.template
  | .tsotsil => Tsotsil.template
  | .mam => Mam.template
  | .kiche => Kiche.template
  | .yukatek => Yukatek.template

/-- The absolutive's position in a language, read off its verbal complex (16). -/
def absPosition (L : Language) : ABSPosition := Mayan.absPosition L.template

/-- The head licensing a language's transitive objects. -/
def licenser (L : Language) : Licenser := .ofPosition L.absPosition

/-- The Set B exponents of a language, from its fragment. -/
def setB : Language → ExponentTable
  | .chol => Chol.setBExponent
  | .qanjobal => Qanjobal.setBExponent
  | .kaqchikel => Kaqchikel.setBExponent
  | .tseltal => Tseltal.setBExponent
  | .tsotsil => Tsotsil.setBExponent
  | .mam => Mam.setBExponent
  | .kiche => Kiche.setBExponent
  | .yukatek => Yukatek.setBExponent

/-- The marking of a language's perfective clauses by marker set, from its fragment; the
Yucatec perfective is the completive status. -/
def perfectiveMarking : Language → ArgumentRole → Option MarkerSet
  | .chol => Chol.markerSet .Perf
  | .qanjobal => Qanjobal.markerSet .Perf
  | .kaqchikel => Kaqchikel.markerSet .Perf
  | .tseltal => Tseltal.markerSet
  | .tsotsil => Tsotsil.markerSet
  | .mam => Mam.markerSet
  | .kiche => Kiche.markerSet
  | .yukatek => Yukatek.markerSet .completive

/-- The language is ergatively aligned in the perfective (§2.1). -/
def IsErgativePerfective (L : Language) : Prop := Alignment.IsErgative L.perfectiveMarking

instance : DecidablePred IsErgativePerfective := fun _ ↦
  inferInstanceAs (Decidable (Alignment.IsErgative _))

/-- The fragment records a reflex for the extraction of an argument on some verb, with
third-person arguments where the marking depends on their person. The Yukatek fragment records
no extraction reflexes, and its value is a junk `False`. -/
def MarksExtraction : Language → ArgumentRole → Prop
  | .chol, r => ∃ m ∈ Chol.Extraction.realize (.argument r), m.Nonempty
  | .qanjobal, r => ∃ m ∈ Qanjobal.Extraction.realize .third (.argument r), m.Nonempty
  | .kaqchikel, r => ∃ c, (Kaqchikel.Extraction.realize c .third .third (.argument r)).Nonempty
  | .tseltal, r => ∃ m ∈ Tseltal.Extraction.realize (.argument r), m.Nonempty
  | .tsotsil, r => ∃ m ∈ Tsotsil.Extraction.realize (.argument r), m.Nonempty
  | .mam, r => (Mam.Extraction.realize (.argument r)).Nonempty
  | .kiche, r => ∃ c, (Kiche.Extraction.realize c (.argument r)).Nonempty
  | .yukatek, _ => False

instance : ∀ L r, Decidable (MarksExtraction L r)
  | .chol, _ | .qanjobal, _ | .tseltal, _ | .tsotsil, _ => Option.decidableExistsMem _
  | .mam, _ => Finset.decidableNonempty
  | .kaqchikel, _ | .kiche, _ => Fintype.decidableExistsFintype
  | .yukatek, _ => inferInstanceAs (Decidable False)

end Language

/-- Every registered language but San Juan Atitán Mam, which is tripartite, marks its arguments
ergatively in the perfective (§2.1). -/
theorem isErgativePerfective_iff (L : Language) : L.IsErgativePerfective ↔ L ≠ .mam := by
  cases L <;> decide

/-- Third person singular absolutive is null in every registered language ergative in the
perfective (13); Mam's default Set B surfaces there. -/
theorem thirdSgZero_of_isErgativePerfective {L : Language} (h : L.IsErgativePerfective) :
    L.setB.IsThirdSgZero := by
  cases L <;> first | decide | exact absurd h (by decide)

/-- A registered language other than Tsotsil and Yucatec marks extraction of a core argument from a
finite transitive iff the regular derivation fails ((19), Footnote 8). -/
theorem tada (L : Language) (h₁ : L ≠ .tsotsil) (h₂ : L ≠ .yukatek) {r : ArgumentRole}
    (hr : r ∈ ArgumentRole.core) :
    L.MarksExtraction r ↔
      ¬ Converges ⟨L.licenser, true, .transitive agentive .dp, some r, false⟩ := by
  rw [ArgumentRole.mem_core] at hr
  cases L <;> first | exact (h₁ rfl).elim | exact (h₂ rfl).elim |
    rcases hr with rfl | rfl | rfl <;> decide

theorem tsotsil_marks_free_extraction :
    Language.tsotsil.MarksExtraction .A ∧
      Converges ⟨Language.tsotsil.licenser, true, .transitive agentive .dp, some .A, false⟩ := by
  decide

/-- With a third-person agent and a full DP object, a Q'anjob'al clause converges exactly under the
Voice of the verb form the fragment records (§4.2, §5.1). -/
theorem converges_iff_verbForm {agent : Person} (ha : ¬ agent.IsSAP) (finite : Bool)
    (e : Option ArgumentRole) (f : VerbForm) :
    Converges ⟨Language.qanjobal.licenser, finite, .transitive (voiceOf f) .dp, e, false⟩ ↔
      Qanjobal.verbForm finite e agent = f := by
  have h3 : ¬ Person.third.IsSAP := by decide
  rw [show Qanjobal.verbForm finite e agent = Qanjobal.verbForm finite e .third by
    simp [Qanjobal.verbForm, ha, h3]]
  revert finite e f
  decide

/-! ### The paper's examples -/

/-- The paper's labels for the absolutive positions. -/
def absPositions : List (String × ABSPosition) := [("high", .high), ("low", .low)]

/-- The rows' labels for the objects. -/
def objects : List (String × Object) :=
  [("dp", .dp), ("caseless", .caseless), ("oblique", .oblique)]

/-- The verb phrase a row describes. -/
def Predicate.ofRow (row : Datum) : Option Predicate := do
  match ← row.feature? "predicate" with
  | "intransitive" =>
      Predicate.intransitive <$> row.parse? "marking" [("abs", MarkerSet.setB), ("erg", .setA)]
  | "transitive" => Predicate.transitive agentive <$> row.parse? "object" objects
  | "agentFocus" => Predicate.transitive voiceAF <$> row.parse? "object" objects
  | "antipassive" => Predicate.transitive antipassive <$> row.parse? "object" objects
  | _ => none

/-- The clause a row describes, its object's licenser read off the paper's classification of
its language. -/
def Clause.ofRow (row : Datum) : Option Clause := do
  let pos ← row.parse? "absPosition" absPositions
  let finite ← row.parse? "finite" [("yes", true), ("no", false)]
  let predicate ← Predicate.ofRow row
  return ⟨.ofPosition pos, finite, predicate,
    row.parse? "extracted" [("S", ArgumentRole.S), ("A", .A), ("P", .P)],
    decide (row.feature? "separated" = some "yes")⟩

/-- Every analysed example is grammatical exactly when its clause converges. -/
theorem analysed_rows : ∀ row ∈ Examples.all, (row.feature? "predicate").isSome = true →
    ∃ c ∈ Clause.ofRow row, (row.judgment = .acceptable ↔ Converges c) := by
  decide

theorem rows_match_fragments : ∀ row ∈ Examples.all, ∀ L : Language,
    L.glottocode = row.language →
      row.parse? "absPosition" absPositions = some L.absPosition := by
  decide

end CoonMateoPedroPreminger2014
