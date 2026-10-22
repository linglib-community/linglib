module

public import Linglib.Data.Examples.Erlewine2016
public import Linglib.Syntax.Person.Basic
public import Linglib.Fragments.Mayan.Kaqchikel.Extraction
public import Linglib.Phonology.OptimalityTheory.Tableau
public import Linglib.Syntax.Minimalist.Locality.AntiLocality
public import Studies.CoonMateoPedroPreminger2014

/-!
# Erlewine (2016): Anti-locality and Optimality in Kaqchikel Agent Focus

Kaqchikel marks the Ā-extraction of a transitive subject with Agent Focus (AF), a verb form with
an AF suffix and no Set A agreement. Erlewine argues that the trigger is movement that is too
short: Spec-to-Spec Anti-Locality bans a step from the specifier of a phrase that crosses no other
maximal projection, and a subject that T's optional Set A probe has moved to Spec,TP sits one
step below Spec,CP, while an intransitive subject stays in situ. AF is the derivation that skips
Spec,TP at the cost of an argument left un-cross-referenced, chosen by ranked constraints over
competing derivations of the whole clause: anti-locality outranks cross-referencing, so AF
disappears when an adverb or another operator intervenes, and cross-referencing participants
outranks both, so the full transitive returns when both arguments are first or second person, an
exception the paper argues no last-resort account of AF can make. Rerankings give the typology of
Popti', Akatek and Ch'ol.

## Main statements

* `extractionTooClose_iff`: an extraction is too close exactly when the subject moves from Spec,TP
  to the layer immediately above, read off the chain of the clause each derivation builds.
* `rows_optimal`: every example is grammatical exactly when an optimal derivation realizes its
  verb form.
* `af_iff_immediately_preverbal`: with at most one participant argument, Kaqchikel AF is optimal
  exactly when the subject moves to the layer immediately above TP.
* `exists_optimal_agentFocus_iff`: the grammar derives the Kaqchikel fragment's Agent Focus
  reflex for arguments of every person.
* `lastResort_matches_iff`: the last-resort model of Coon, Mateo Pedro and Preminger, run on the
  Kaqchikel examples, judges an example correctly exactly when its subject is not extracted past
  an intervening layer and its arguments are not both participants.

## Implementation notes

* A derivation builds the spine VP, vP, TP and the layers above TP, an adverb's projection after
  Cinque, the CPs of Rizzi's split periphery and the topic projection, with a copy of each argument
  at each position it occupies; anti-locality is read off the chain of the extracted argument
  (`Minimalist.SpecToSpec`). Long-distance extraction is the embedded clause's competition, since
  movement stops at the embedded Spec,CP.
* A candidate is a choice of the optional Set A probe and of the Set B probe's target; the two
  probes cannot share a goal, the Set A probe sees only the subject at the vP edge, and Popti'
  and Akatek restrict Set B to the object. The constraint preferring plural targets is not
  modelled.
* The last-resort model is the one formalized in `Studies/CoonMateoPedroPreminger2014.lean`, run
  on each Kaqchikel example with Infl licensing the object, the Voice of the attested form and
  the extracted argument's role; its authors propose it for Q'anjob'al only, as the paper's
  fn. 46 notes.
* Example and footnote numbers are the published version's; the examples are
  `Data.Examples.Erlewine2016`.

## References

* [erlewine-2016]
* [abels-2003]
* [cinque-1999]
* [rizzi-1997]
* [stiebels-2006]
* [preminger-2011b]
* [coon-mateo-pedro-preminger-2014]
* [prince-smolensky-1993]
-/

@[expose] public section

namespace Erlewine2016

open OptimalityTheory Erlewine2016.Examples
open Minimalist (Cat LexicalItem LinearizedSyntacticObject chainTop links projectionAt SpecToSpec)

/-- The arguments of a verb. -/
inductive Arg
  | subj
  | obj
  deriving DecidableEq, Repr

/-- A layer of the clause above TP, an adverb's projection, a CP of the periphery, or the topic
projection. -/
inductive Layer
  | advP
  | cP
  | topP
  deriving DecidableEq, Repr

/-- A clause and its extraction, with whether it is transitive, the layers above TP from the bottom,
the extracted argument with the index of the layer it lands in, and the person of each
argument. -/
structure Input where
  transitive : Bool
  layers : List Layer
  extracted : Option (Arg × ℕ)
  subj : Person
  obj : Person
  deriving DecidableEq, Repr

/-- The arguments of a transitive or intransitive clause. -/
def argsOf (transitive : Bool) : List Arg := if transitive then [.subj, .obj] else [.subj]

/-- The arguments of the clause. -/
def Input.args (i : Input) : List Arg := argsOf i.transitive

/-- The person of an argument. -/
def Input.person (i : Input) : Arg → Person
  | .subj => i.subj
  | .obj => i.obj

/-! ### The clause and anti-locality -/

/-- The category of a layer's head: an adverb's projection is one of Cinque's modal heads. -/
def Layer.cat : Layer → Cat
  | .advP => .Mod
  | .cP => .C
  | .topP => .Top

/-- The head of the `j`th layer above TP, selecting the category below it. -/
def Layer.head (l : Layer) (j : ℕ) (below : Cat) : LexicalItem.Token := ⟨.of l.cat [below], 10 + j⟩

/-- The verb, selecting the object when it is transitive. -/
def verb (transitive : Bool) : LexicalItem.Token := ⟨.of .V (if transitive then [.D] else []), 0⟩

def littleV : LexicalItem.Token := ⟨.of .v [.V], 1⟩

def tense : LexicalItem.Token := ⟨.of .T [.v], 2⟩

/-- The token of an argument. -/
def Arg.token : Arg → LexicalItem.Token
  | .subj => ⟨.of .D [], 3⟩
  | .obj => ⟨.of .D [], 4⟩

/-! ### Derivations and constraints -/

/-- A derivation of the clause (§5.1), fixing whether T's optional Set A probe is used, moving the
subject to Spec,TP, and the argument its Set B probe targets. -/
structure Candidate where
  aProbe : Bool
  bTarget : Arg
  deriving DecidableEq, Repr

/-- The candidates of a numeration. The Set B target is an argument, the two probes cannot share
a goal, and where Set B is restricted to the object it targets the object. -/
def candidatesOf (transitive objectOnly : Bool) : List Candidate :=
  ([true, false].flatMap fun a ↦ (argsOf transitive).map (⟨a, ·⟩)).filter fun c ↦
    (c.aProbe → c.bTarget ≠ .subj) ∧ (objectOnly → transitive → c.bTarget = .obj)

/-- The candidates of a clause. -/
def candidates (i : Input) (objectOnly : Bool) : Finset Candidate :=
  (candidatesOf i.transitive objectOnly).toFinset

/-- An argument is cross-referenced when the Set A probe targets it, the subject having moved to
Spec,TP, or the Set B probe does, (46). -/
def CrossRef (c : Candidate) (a : Arg) : Prop := (c.aProbe ∧ a = .subj) ∨ c.bTarget = a

instance (c : Candidate) (a : Arg) : Decidable (CrossRef c a) := by unfold CrossRef; infer_instance

/-- The clause a derivation builds (§4.1), with a copy of each argument at each position it
occupies: the subject in Spec,vP and, when the Set A probe attracts it, in Spec,TP; the object as
the complement of V; and an extracted argument in the specifier of the layer it lands in. -/
def Input.clause (i : Input) (c : Candidate) : LinearizedSyntacticObject :=
  let vP : LinearizedSyntacticObject := Arg.subj.token * (littleV *
    (if i.transitive then (verb true * Arg.obj.token : LinearizedSyntacticObject) else verb false))
  let tP : LinearizedSyntacticObject :=
    if c.aProbe then Arg.subj.token * (tense * vP) else tense * vP
  (i.layers.zipIdx.foldl (fun (x : LinearizedSyntacticObject × Cat) (l, j) ↦
    let y := l.head j x.2 * x.1
    (match i.extracted with
      | some (a, k) => if k = j then a.token * y else y
      | none => y, l.cat)) (tP, .T)).1

/-- The step that extracts `a` is too close: the link landing at the top of its chain moves a
specifier across no maximal projection but its own, Spec-to-Spec Anti-Locality (42). -/
def ExtractionTooClose (t : LinearizedSyntacticObject) (a : Arg) : Prop :=
  ∃ p ∈ chainTop t a.token, ∃ x ∈ links t a.token, x.1 = projectionAt t p ∧ SpecToSpec t x

instance (t : LinearizedSyntacticObject) (a : Arg) : Decidable (ExtractionTooClose t a) := by
  unfold ExtractionTooClose; infer_instance

/-- Spec-to-Spec Anti-Locality as a violable constraint: one violation for an extraction that is
too close. -/
def ssal (i : Input) : Constraint Candidate := fun c ↦
  match i.extracted with
  | none => 0
  | some (a, _) => if ExtractionTooClose (i.clause c) a then 1 else 0

/-- XRef assigns one violation per argument not cross-referenced. -/
def xref (i : Input) : Constraint Candidate := fun c ↦ (i.args.filter (¬ CrossRef c ·)).length

/-- XRef-Participant assigns one violation per participant argument not cross-referenced
(§5.2), deriving the Set B agreement of [preminger-2011b] and the salience hierarchy of
[stiebels-2006]. -/
def xrefP (i : Input) : Constraint Candidate := fun c ↦
  (i.args.filter fun a ↦ (i.person a).IsSAP ∧ ¬ CrossRef c a).length

/-- A grammar of §6.1, with a ranking of the constraints and whether Set B is restricted to the
object. -/
structure Grammar where
  ranking : List (Input → Constraint Candidate)
  objectOnly : Bool

/-- The competition of a clause under a grammar. -/
def Grammar.tableau (g : Grammar) (i : Input) :=
  Tableau.ofList (candidates i g.objectOnly) (g.ranking.map (· i))

/-- Kaqchikel ranks XRef-Participant ≫ SSAL ≫ XRef, Set B free to target either argument. -/
def kaqchikel : Grammar := ⟨[xrefP, ssal, xref], false⟩

/-- Popti' has the Kaqchikel ranking with Set B restricted to the object. -/
def popti : Grammar := ⟨[xrefP, ssal, xref], true⟩

/-- Akatek ranks SSAL above both cross-referencing constraints, Set B restricted to the object. -/
def akatek : Grammar := ⟨[ssal, xrefP, xref], true⟩

/-- Ch'ol, a Mayan language without AF, ranks XRef ≫ SSAL. -/
def chol : Grammar := ⟨[xref, ssal], false⟩

/-! ### Realization -/

/-- The AF suffix is realized when some argument is not cross-referenced (48). -/
def Candidate.AFSuffix (args : List Arg) (c : Candidate) : Prop := ∃ a ∈ args, ¬ CrossRef c a

instance (args : List Arg) (c : Candidate) : Decidable (c.AFSuffix args) := by
  unfold Candidate.AFSuffix; infer_instance

/-- The AF suffix marks a violation of XRef. -/
theorem afSuffix_iff_xref_pos (i : Input) (c : Candidate) :
    c.AFSuffix i.args ↔ 0 < xref i c := by
  simp [Candidate.AFSuffix, xref, List.length_pos_iff_exists_mem, List.mem_filter]

/-- The verb form of a derivation, Set A being realized only when the subject moved to
Spec,TP. -/
def Candidate.form (args : List Arg) (c : Candidate) : Mayan.VerbForm :=
  if c.AFSuffix args then .agentFocus else .transitive

/-- Among the candidates of a transitive clause, the AF form is exactly the absence of the Set
A probe: the derivation that skips Spec,TP loses Set A and gains the suffix. -/
theorem form_hasSetA (o : Bool) :
    ∀ c ∈ candidatesOf true o, ((c.form (argsOf true)).HasSetA ↔ c.aProbe = true) := by
  cases o <;> decide

/-! ### The rows -/

/-- The clause types as named in the rows. -/
def clauseTable : List (String × Bool) := [("transitive", true), ("intransitive", false)]

/-- The layers above TP as named in the rows. -/
def layerTable : List (String × List Layer) :=
  [("CP", [.cP]), ("AdvP,CP", [.advP, .cP]), ("CP,CP", [.cP, .cP]), ("CP,TopP", [.cP, .topP])]

/-- The extracted argument as named in the rows. -/
def extractedTable : List (String × Option Arg) :=
  [("none", none), ("subject", some .subj), ("object", some .obj)]

/-- The persons as named in the rows. -/
def personTable : List (String × Person) := [("1", .first), ("2", .second), ("3", .third)]

/-- The verb forms as named in the rows. -/
def verbTable : List (String × Mayan.VerbForm) := [("AF", .agentFocus), ("full", .transitive)]

/-- The grammars by glottocode. -/
def grammarTable : List (String × Grammar) :=
  [("kaqc1270", kaqchikel), ("popt1235", popti), ("west2635", akatek), ("chol1282", chol)]

/-- A row, with the clause, its language's grammar, the attested form and the judgment. -/
structure Row where
  input : Input
  grammar : Grammar
  form : Mayan.VerbForm
  judgment : Judgment

/-- A row from an example; landing layers count from one in the rows. -/
def Row.ofDatum (ex : Datum) : Option Row := do
  let transitive ← ex.parse? "clause" clauseTable
  let layers ← ex.parse? "layers" layerTable
  let extracted ← match ← ex.parse? "extracted" extractedTable with
    | none => pure none
    | some a => do pure (some (a, (← ex.nat? "landing") - 1))
  let subj ← ex.parse? "subject" personTable
  let grammar ← List.lookup ex.language grammarTable
  let form ← ex.parse? "verb" verbTable
  pure ⟨⟨transitive, layers, extracted, subj, (ex.parse? "object" personTable).getD .third⟩,
    grammar, form, ex.judgment⟩

theorem row_ofDatum_isSome : ∀ ex ∈ Examples.all, (Row.ofDatum ex).isSome := by decide

/-- The rows of all four languages. -/
def rows : List Row := Examples.all.filterMap Row.ofDatum

/-- The Kaqchikel rows. -/
def kaqchikelRows : List Row :=
  (Examples.all.filter (·.language = "kaqc1270")).filterMap Row.ofDatum

/-- The configuration of (44): in the clause of every row, an extraction is too close exactly when
the subject moves from Spec,TP to the layer immediately above TP. -/
theorem extractionTooClose_iff :
    ∀ r ∈ rows, ∀ c ∈ candidatesOf r.input.transitive r.grammar.objectOnly,
      ∀ x ∈ r.input.extracted,
        (ExtractionTooClose (r.input.clause c) x.1 ↔ x.1 = .subj ∧ c.aProbe = true ∧ x.2 = 0) := by
  decide

/-- In every row the attested form is grammatical exactly when an optimal derivation realizes
it. -/
theorem rows_optimal :
    ∀ r ∈ rows, r.judgment = .acceptable ↔
      ∃ c ∈ (r.grammar.tableau r.input).optimal, c.form r.input.args = r.form := by
  decide

/-- The generalization of §3. With at most one participant argument, AF is optimal in Kaqchikel
exactly when the subject moves to the layer immediately above TP. -/
theorem af_iff_immediately_preverbal :
    ∀ r ∈ kaqchikelRows, ¬ (r.input.subj.IsSAP ∧ r.input.obj.IsSAP) →
      ((∃ c ∈ (kaqchikel.tableau r.input).optimal, c.AFSuffix r.input.args) ↔
        r.input.extracted = some (.subj, 0)) := by
  decide

/-! ### The competitions of §5 and §6 -/

/-- Subject extraction to Spec,CP in a simple transitive clause. -/
def subjectExtraction (s o : Person) : Input := ⟨true, [.cP], some (.subj, 0), s, o⟩

/-- Without extraction (§5.1), cross-referencing selects the derivation that moves the subject to
Spec,TP; this is also what an evaluation at TP would select before the anti-locality violation
of a later extraction is visible, the argument of §5.3 for evaluation at the clause. -/
theorem no_extraction_full (s o : Person) :
    (kaqchikel.tableau ⟨true, [.cP], none, s, o⟩).optimal = {⟨true, .obj⟩} := by
  cases s <;> cases o <;> decide

/-- Under subject extraction with two third-person arguments (§5.1), both AF derivations beat
the derivation through Spec,TP, and the two constraints do not decide the Set B target. -/
theorem subject_extraction_af :
    (kaqchikel.tableau (subjectExtraction .third .third)).optimal =
      {⟨false, .subj⟩, ⟨false, .obj⟩} := by
  decide

/-- A participant argument breaks the tie, Set B cross-referencing it (§5.2). -/
theorem participant_breaks_tie :
    (kaqchikel.tableau (subjectExtraction .second .third)).optimal = {⟨false, .subj⟩} ∧
      (kaqchikel.tableau (subjectExtraction .third .second)).optimal = {⟨false, .obj⟩} := by
  decide

/-- With two participant arguments the full-agreement transitive is optimal (§5.2), the
anti-locality violation notwithstanding. -/
theorem participant_exception :
    (kaqchikel.tableau (subjectExtraction .first .second)).optimal = {⟨true, .obj⟩} := by
  decide

/-- Subject extraction to Spec,CP has an optimal AF derivation exactly when the arguments are not
both participants, which is when the Kaqchikel fragment records the Agent Focus reflex. -/
theorem exists_optimal_agentFocus_iff (c : Mayan.VerbClass) (s o : Person) :
    (∃ d ∈ (kaqchikel.tableau (subjectExtraction s o)).optimal,
        d.form (argsOf true) = .agentFocus) ↔
      (Kaqchikel.Extraction.realize c s o (.argument .A)).Nonempty := by
  have h :
      (Kaqchikel.Extraction.realize c s o (.argument .A)).Nonempty ↔ ¬ (s.IsSAP ∧ o.IsSAP) := by
    simp only [Kaqchikel.Extraction.realize]
    split_ifs with h <;> simp [h]
  rw [h]
  cases s <;> cases o <;> decide

/-- Object extraction and intransitive subject extraction cross enough structure (§4.2), and no
optimal derivation bears the AF suffix. -/
theorem no_af_without_short_step :
    (kaqchikel.tableau ⟨true, [.cP], some (.obj, 0), .third, .third⟩).optimal =
        {⟨true, .obj⟩} ∧
      ∀ c ∈ (kaqchikel.tableau ⟨false, [.cP], some (.subj, 0), .third, .third⟩).optimal,
        ¬ c.AFSuffix (argsOf false) := by
  decide

/-- The typology of rerankings (§6.1). Popti' keeps the full form when the subject is a
participant and uses AF when it is not; Akatek uses AF for a participant subject; Ch'ol keeps
the full form throughout. -/
theorem typology :
    (popti.tableau (subjectExtraction .second .third)).optimal = {⟨true, .obj⟩} ∧
      (popti.tableau (subjectExtraction .third .second)).optimal = {⟨false, .obj⟩} ∧
      (akatek.tableau (subjectExtraction .first .third)).optimal = {⟨false, .obj⟩} ∧
      (chol.tableau (subjectExtraction .third .second)).optimal = {⟨true, .obj⟩} := by
  decide

/-! ### The last-resort alternative -/

/-- The role of an argument in a transitive or intransitive clause. -/
def Arg.role (transitive : Bool) : Arg → ArgumentRole
  | .subj => if transitive then .A else .S
  | .obj => .P

/-- The clause the last-resort model of Coon, Mateo Pedro and Preminger assigns a Kaqchikel row,
finite, with Infl licensing the object as Kaqchikel's high absolutive has it, the Voice of the
attested form, and the extracted argument by its role. -/
def Row.lastResortClause (r : Row) : CoonMateoPedroPreminger2014.Clause :=
  ⟨CoonMateoPedroPreminger2014.Language.kaqchikel.licenser, true,
    if r.input.transitive then
      .transitive (CoonMateoPedroPreminger2014.voiceOf r.form) .dp
    else .intransitive .setB,
    r.input.extracted.map fun e ↦ e.1.role r.input.transitive, false⟩

/-- The subject is extracted past an intervening layer, an adverb, another operator or a topic
(§3). -/
def Row.DistantSubject (r : Row) : Prop := ∃ e ∈ r.input.extracted, e.1 = .subj ∧ e.2 ≠ 0

/-- Both arguments are participants (§5.2). -/
def Row.TwoParticipants (r : Row) : Prop := r.input.subj.IsSAP ∧ r.input.obj.IsSAP

instance : DecidablePred Row.DistantSubject := fun r ↦
  inferInstanceAs (Decidable (∃ e ∈ r.input.extracted, _))
instance : DecidablePred Row.TwoParticipants := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- The last-resort model merges the Case-assigning AF Voice only where the regular derivation
would crash, so it sees neither person nor what lies between the extracted subject and the verb.
It judges a Kaqchikel example correctly exactly when the subject is not extracted past an
intervening layer, the locality such Case-based accounts miss (fn. 47), and the arguments are not
both participants, the exception for which a last resort would need a last resort of its own
(§5.3, (81)); the optimality grammar fits every example (`rows_optimal`). -/
theorem lastResort_matches_iff : ∀ r ∈ kaqchikelRows,
    ((r.judgment = .acceptable ↔ CoonMateoPedroPreminger2014.Converges r.lastResortClause) ↔
      ¬ r.DistantSubject ∧ ¬ r.TwoParticipants) := by
  decide

end Erlewine2016
