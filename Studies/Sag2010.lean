module

public import Linglib.Syntax.HPSG.Construction
public import Linglib.Data.Examples.Sag2010

/-!
# Sag (2010): English Filler-Gap Constructions

This file formalizes the paper's account of the five English filler-gap clauses, topicalized,
wh-exclamative, nonsubject wh-interrogative, wh-relative and the-clauses, as constructions of
Sign-Based Construction Grammar. The clauses share the filler-head construction, which binds a
nonverbal filler to a gap in a verbal head daughter, and each cross-classifies with a clausal
type that fixes its semantic type; what remains to each is a short list of constraints, from
which the paper's parameters of variation follow: which distinguished element the filler must
contain, which categories the filler and head daughters may have, whether the head may or must
be inverted or infinitival, whether the clause is an island, and whether it must be independent.

A construct is described by the categories of its daughters and the inversion, finiteness and
independence of its head (`Construct`), and a clause licenses the constructs meeting its
constraints (`FGClause.Licenses`), with categories compared in the sort order of the RSRL
construct hierarchy of `Syntax/HPSG/Construction`. Islandhood and semantics are facts of that
hierarchy's grammar. A clause is an absolute island when every construct of its sort, in every
model of the grammar, has a mother with an empty `GAP` list (`FGClause.IsIsland`). Topicalized
clauses, wh-exclamatives and the-clauses are islands, since their constructions give the head
daughter a single gap, which the filler discharges (`isIsland_iff`). A construct is well formed
exactly when its mother has the semantic type of its clause. The distinguished element is
lexical: the wh-word inventory is read off the paper's judgment triples (`occurs`), and no
wh-form of any category occurs in all three wh-constructions (`no_universal_wh_word`).
The rows are the paper's examples, and their judgments follow from the constructions
(`judgments`).

## Implementation notes

The WH, REL, IC and VFORM features of the constructions are not in the RSRL signature, so the
constraints on them are stated over `Construct` rather than checked by the model theory, while
the category, GAP and SEM constraints are the grammar's. Independence is identified with the
absence of embedding, so the embedded topicalizations the paper licenses under predicates that
admit main-clause phenomena are not among the rows. The inventory is derived from the judgment
triples rather than transcribed from the paper's table of wh-words, which prints two cells
differently: bare *what* in exclamatives and determiner *which* in relatives are marked as
accepted by some speakers in the table but starred in the triples. The island rows are checked
in one direction, since the paper attributes the graded degradation of extraction from finite
wh-interrogatives to processing. The-clauses come out as islands because the the-clause
construction gives the head daughter a single gap, as the topicalization and wh-exclamative
constructions do. The text discusses islandhood only for the latter two, and no row tests a
the-clause.

## TODO

* The paper stars its example of a the-clause with a complementizer head although its text
  admits an S or CP head; the row is omitted.

## References

* [sag-2010]
* [ginzburg-sag-2000]
* [bouma-malouf-sag-2001]
* [hofmeister-sag-2010]
-/

@[expose] public section

namespace Sag2010

open HPSG HPSG.RSRL HPSG.Construction

/-! ### The five constructions -/

/-- The five English filler-gap clauses. -/
inductive FGClause where
  | topicalized
  | whExclamative
  | whInterrogative
  | whRelative
  | theClause
  deriving DecidableEq, Repr, Fintype

/-- The construct sort of a clause in the RSRL hierarchy. -/
def FGClause.sort : FGClause → Srt
  | .topicalized => .topCl
  | .whExclamative => .whExclCl
  | .whInterrogative => .nsWhIntCl
  | .whRelative => .whRelCl
  | .theClause => .theCl

/-- The semantic type of a clause is a question, a fact, a modifier, or an austinean object. -/
def FGClause.sem : FGClause → Srt
  | .whInterrogative => .question
  | .whExclamative => .fact
  | .whRelative => .modifier
  | .topicalized | .theClause => .austinean

/-- A single-gap construct of the clause's sort whose mother has semantic type `σ`. -/
abbrev FGClause.construct (c : FGClause) (σ : Srt) : Interpretation sig Ent :=
  singleConstruct c.sort σ singleGapA

/-- A construct of the clause's sort satisfies the grammar exactly when its mother has the
clause's semantic type. -/
theorem models_construct_iff (c : FGClause) (σ : Srt)
    (hσ : σ ∈ [Srt.question, .fact, .modifier, .austinean]) :
    (c.construct σ).Models grammar ↔ σ = c.sem := by
  revert c σ
  decide +kernel

/-- A construct of the clause's sort whose head daughter carries a second, undischarged gap. -/
abbrev FGClause.secondGap (c : FGClause) : Interpretation sig Ent :=
  twoGapConstruct c.sort c.sem .noun

/-- The constructs of each clause are well-typed, so the grammar's verdict on them is a verdict
of its constructions and not of the appropriateness conditions. -/
theorem isWellTyped_constructs (c : FGClause) :
    (c.construct c.sem).IsWellTyped ∧ c.secondGap.IsWellTyped := by
  cases c <;> decide +kernel

/-- A clause is an absolute island when, in every model of the grammar, every construct of its
sort has a mother with an empty `GAP` list, so that no gap inside the clause is bound outside
it. -/
def FGClause.IsIsland (c : FGClause) : Prop :=
  ∀ ⦃U : Type⦄ (I : Interpretation sig U), I.Models grammar → ∀ u, I.S u = c.sort →
    I.Satisfies (fun _ ↦ u) u (.sortAssign (.path [.MTR, .GAP]) .elist)

/-- In a model of the grammar, the head daughter of a topicalized clause, a wh-exclamative or a
the-clause has a single gap. -/
theorem satisfies_gapRest_elist {U : Type*} {I : Interpretation sig U} (hI : I.Models grammar)
    {c : FGClause} (hc : c = .topicalized ∨ c = .whExclamative ∨ c = .theClause) {u : U}
    (hu : I.S u = c.sort) :
    I.Satisfies (fun _ ↦ u) u (.sortAssign (.path [.HDDTR, .GAP, .REST]) .elist) := by
  rcases hc with rfl | rfl | rfl
  · exact (hI.satisfies_body (c := topPrinciple)
      (List.mem_map_of_mem (by simp [constraints])) hu.le).2.2.1
  · exact (hI.satisfies_body (c := whExclPrinciple)
      (List.mem_map_of_mem (by simp [constraints])) hu.le).2
  · exact (hI.satisfies_body (c := thePrinciple)
      (List.mem_map_of_mem (by simp [constraints])) hu.le).2

/-- Exactly topicalized clauses, wh-exclamatives and the-clauses are absolute islands. Their
constructions give the head daughter a single gap, which the filler discharges, while a
wh-interrogative or a wh-relative construct may pass a second gap to its mother. -/
theorem isIsland_iff (c : FGClause) :
    c.IsIsland ↔ c = .topicalized ∨ c = .whExclamative ∨ c = .theClause := by
  refine ⟨fun h ↦ ?_, fun hc U I hI u hu ↦ ?_⟩
  · by_contra hc
    have key : ∀ c : FGClause, ¬ (c = .topicalized ∨ c = .whExclamative ∨ c = .theClause) →
        c.secondGap.Models grammar ∧ ¬ c.secondGap.Satisfies (fun _ ↦ .cxt) .cxt
          (.sortAssign (.path [.MTR, .GAP]) .elist) := by
      decide +kernel
    exact (key c hc).2 (h _ (key c hc).1 .cxt rfl)
  · have hfh : I.S u ≤ .fillerHeadCxt :=
      hu ▸ (by decide +kernel : ∀ c : FGClause, c.sort ≤ .fillerHeadCxt) c
    exact (satisfies_mtrGap_iff hI hfh .elist).2 (satisfies_gapRest_elist hI hc hu)

/-! ### Constructs -/

/-- The syntactic categories of filler and head daughters. -/
inductive Cat where
  | NP
  | PP
  | AP
  | AdvP
  | VP
  | S
  | CP
  deriving DecidableEq, Repr, Fintype

/-- The category sort of the RSRL hierarchy; S and VP are both projections of a verb. -/
def Cat.sort : Cat → Srt
  | .NP => .noun
  | .PP => .prep
  | .AP => .adj
  | .AdvP => .adv
  | .VP | .S => .verb
  | .CP => .comp

/-- The nonverbal categories are NP, PP, AP and AdvP. -/
theorem Cat.sort_le_nonverbal_iff {x : Cat} :
    x.sort ≤ .nonverbal ↔ x = .NP ∨ x = .PP ∨ x = .AP ∨ x = .AdvP := by
  cases x <;> decide

/-- The nominal categories are NP and PP. -/
theorem Cat.sort_le_nominal_iff {x : Cat} : x.sort ≤ .nominal ↔ x = .NP ∨ x = .PP := by
  cases x <;> decide

/-- The projections of a verb are S and VP. -/
theorem Cat.sort_le_verb_iff {x : Cat} : x.sort ≤ .verb ↔ x = .S ∨ x = .VP := by
  cases x <;> decide

/-- The syntactic features of a filler-head construct that the parameters of variation probe:
the categories of its filler and head daughters, and whether its head is inverted, finite and
independent. -/
structure Construct where
  filler : Cat
  head : Cat
  inverted : Bool
  finite : Bool
  independent : Bool
  deriving DecidableEq, Repr

/-- A construct meets the category conditions shared by the five clauses when its filler is
nonverbal and its head verbal. -/
def Construct.FillerHead (k : Construct) : Prop :=
  k.filler.sort ≤ .nonverbal ∧ k.head.sort ≤ .verbal

instance : DecidablePred Construct.FillerHead := fun k ↦ by
  unfold Construct.FillerHead; infer_instance

/-- The relative construction requires a clause that is neither independent nor inverted. -/
def Construct.RelativeCl (k : Construct) : Prop := k.independent = false ∧ k.inverted = false

instance : DecidablePred Construct.RelativeCl := fun k ↦ by
  unfold Construct.RelativeCl; infer_instance

/-- The constructs a clause licenses. A topicalized clause has an uninverted, finite,
independent S head; a wh-exclamative an uninverted, finite S head; a nonsubject
wh-interrogative an S head inverted exactly when the clause is independent; a wh-relative is a
relative clause with a verbal head whose filler is nominal when finite and a PP when
infinitival; and a the-clause has a finite S or CP head. -/
def FGClause.Licenses : FGClause → Construct → Prop
  | .topicalized, k =>
      k.FillerHead ∧ k.head = .S ∧ k.inverted = false ∧ k.finite = true ∧ k.independent = true
  | .whExclamative, k => k.FillerHead ∧ k.head = .S ∧ k.inverted = false ∧ k.finite = true
  | .whInterrogative, k => k.FillerHead ∧ k.head = .S ∧ k.inverted = k.independent
  | .whRelative, k =>
      k.FillerHead ∧ k.RelativeCl ∧ k.head.sort ≤ .verb ∧
        (k.finite = true → k.filler.sort ≤ .nominal) ∧ (k.finite = false → k.filler = .PP)
  | .theClause, k => k.FillerHead ∧ (k.head = .S ∨ k.head = .CP) ∧ k.finite = true

instance (c : FGClause) (k : Construct) : Decidable (c.Licenses k) := by
  cases c <;> unfold FGClause.Licenses <;> infer_instance

/-! ### The parameters of variation -/

/-- The filler daughter is an NP, PP, AP or AdvP; a finite wh-relative's is an NP or PP and an
infinitival wh-relative's a PP. -/
theorem filler_of_licenses {c : FGClause} {k : Construct} (h : c.Licenses k) :
    (k.filler = .NP ∨ k.filler = .PP ∨ k.filler = .AP ∨ k.filler = .AdvP) ∧
      (c = .whRelative →
        (k.finite = true → k.filler = .NP ∨ k.filler = .PP) ∧
          (k.finite = false → k.filler = .PP)) := by
  cases c <;> simp_all [FGClause.Licenses, Construct.FillerHead, Cat.sort_le_nonverbal_iff,
    Cat.sort_le_nominal_iff]

/-- The head daughter is an S, or a CP in a the-clause, or a VP in a wh-relative. -/
theorem head_of_licenses {c : FGClause} {k : Construct} (h : c.Licenses k) :
    k.head = .S ∨ c = .theClause ∧ k.head = .CP ∨ c = .whRelative ∧ k.head = .VP := by
  cases c <;> simp_all [FGClause.Licenses, Cat.sort_le_verb_iff]

/-- An inverted head occurs only in an independent wh-interrogative or in a the-clause. -/
theorem inverted_of_licenses {c : FGClause} {k : Construct} (h : c.Licenses k)
    (hi : k.inverted = true) : c = .whInterrogative ∧ k.independent = true ∨ c = .theClause := by
  cases c <;> simp_all [FGClause.Licenses, Construct.RelativeCl]

/-- Only wh-interrogatives and wh-relatives take an infinitival head. -/
theorem infinitival_of_licenses {c : FGClause} {k : Construct} (h : c.Licenses k)
    (hf : k.finite = false) : c = .whInterrogative ∨ c = .whRelative := by
  cases c <;> simp_all [FGClause.Licenses]

/-- Topicalized clauses are independent and wh-relatives are not. -/
theorem independent_of_licenses {c : FGClause} {k : Construct} (h : c.Licenses k) :
    (c = .topicalized → k.independent = true) ∧ (c = .whRelative → k.independent = false) := by
  cases c <;> simp_all [FGClause.Licenses, Construct.RelativeCl]

/-! ### The distinguished element -/

/-- The distinguished element that a construction requires in its filler daughter. Topicalization
requires none, a the-clause requires the definite degree marker, and the other constructions
require a wh-word of their own kind. -/
inductive Marker where
  | none
  | the
  | interrogative
  | exclamative
  | relative
  deriving DecidableEq, Repr

/-- The marker each construction requires. -/
def FGClause.marker : FGClause → Marker
  | .topicalized => .none
  | .theClause => .the
  | .whInterrogative => .interrogative
  | .whExclamative => .exclamative
  | .whRelative => .relative

/-- The wh-forms of the inventory. -/
inductive WhForm where
  | who
  | whose
  | what
  | whatA
  | which
  | how
  | when
  | «where»
  | why
  deriving DecidableEq, Repr, Fintype

/-- The categories a wh-form bears. -/
inductive WhCategory where
  | np
  | det
  | detSing
  | detPl
  | degree
  | advpManner
  | ap
  | ppTime
  | ppPlace
  | ppReason
  deriving DecidableEq, Repr, Fintype

/-! ### The paper's examples -/

/-- The parameters of variation the rows probe, and the wh-word inventory. -/
inductive Parameter where
  | distinguished
  | inventory
  | fillerCategory
  | headCategory
  | inversion
  | finiteness
  | independence
  | island
  deriving DecidableEq, Repr

def parameters : List (String × Parameter) :=
  [("distinguished", .distinguished), ("inventory", .inventory),
    ("fillerCategory", .fillerCategory), ("headCategory", .headCategory),
    ("inversion", .inversion), ("finiteness", .finiteness),
    ("independence", .independence), ("island", .island)]

def clauses : List (String × FGClause) :=
  [("topicalized", .topicalized), ("whExclamative", .whExclamative),
    ("whInterrogative", .whInterrogative), ("whRelative", .whRelative), ("theClause", .theClause)]

def cats : List (String × Cat) :=
  [("NP", .NP), ("PP", .PP), ("AP", .AP), ("AdvP", .AdvP), ("VP", .VP), ("S", .S), ("CP", .CP)]

def bools : List (String × Bool) := [("true", true), ("false", false)]

def whForms : List (String × WhForm) :=
  [("who", .who), ("whose", .whose), ("what", .what), ("whatA", .whatA), ("which", .which),
    ("how", .how), ("when", .when), ("where", .«where»), ("why", .why)]

def whCategories : List (String × WhCategory) :=
  [("np", .np), ("det", .det), ("detSing", .detSing), ("detPl", .detPl), ("degree", .degree),
    ("advpManner", .advpManner), ("ap", .ap), ("ppTime", .ppTime), ("ppPlace", .ppPlace),
    ("ppReason", .ppReason)]

/-- The rows probing a parameter. -/
def probing (p : Parameter) : List Datum :=
  Examples.all.filter fun x ↦ decide (x.parse? "parameter" parameters = some p)

/-- The clause a row instantiates. -/
def clause? (x : Datum) : Option FGClause := x.parse? "construction" clauses

/-- The construct that a row describes, with its filler and head categories and the inversion,
finiteness and embedding of its head. The filler is an NP and the head an uninverted, finite,
matrix S unless the row records otherwise. -/
def construct (x : Datum) : Construct where
  filler := (x.parse? "filler" cats).getD .NP
  head := (x.parse? "head" cats).getD .S
  inverted := (x.parse? "inverted" bools).getD false
  finite := (x.parse? "finite" bools).getD true
  independent := !(x.parse? "embedded" bools).getD false

/-- The wh-form and category of a row's filler, if it contains a wh-word. -/
def whWord? (x : Datum) : Option (WhForm × WhCategory) :=
  (x.parse? "whForm" whForms).bind fun f ↦ (x.parse? "whCategory" whCategories).map (f, ·)

/-- The judgment the inventory records for a wh-form of a category in a wh-construction. -/
def occurs (f : WhForm) (cat : WhCategory) (c : FGClause) : Option Judgment :=
  ((probing .inventory).find? fun x ↦ decide (whWord? x = some (f, cat) ∧ clause? x = some c)).map
    (·.judgment)

/-- The three wh-constructions. -/
def whClauses : List FGClause := [.whInterrogative, .whExclamative, .whRelative]

/-- No wh-form of any category occurs in all three wh-constructions: there is no unitary
category of English wh-expression. -/
theorem no_universal_wh_word :
    ∀ x ∈ probing .inventory, ∀ w ∈ whWord? x,
      ∃ c ∈ whClauses, occurs w.1 w.2 c ≠ some .acceptable := by
  decide +kernel

/-- The markers a filler containing a wh-form of a category can bear: those of the
wh-constructions in which the inventory records it as acceptable. -/
def markers (f : WhForm) (cat : WhCategory) : List Marker :=
  (whClauses.filter fun c ↦ decide (occurs f cat c = some .acceptable)).map FGClause.marker

/-- The markers that a row's filler can bear. They are those of its wh-word if it contains one,
the definite degree marker if it contains comparative *the*, and none otherwise. -/
def fillerMarkers (x : Datum) : List Marker :=
  match whWord? x with
  | some (f, cat) => markers f cat
  | none => if (x.parse? "the" bools).getD false then [.the] else [.none]

/-- The rows probing the distinguished element are acceptable exactly when the filler can bear
the construction's marker. -/
theorem distinguished :
    ∀ x ∈ probing .distinguished, ∀ c, clause? x = some c →
      (x.judgment = .acceptable ↔ c.marker ∈ fillerMarkers x) := by
  decide +kernel

/-- The rows probing the categories of the daughters and the inversion, finiteness and
independence of the head are acceptable exactly when the clause licenses the construct they
describe. -/
theorem judgments :
    ∀ p ∈ [Parameter.fillerCategory, .headCategory, .inversion, .finiteness, .independence],
      ∀ x ∈ probing p, ∀ c, clause? x = some c →
        (x.judgment = .acceptable ↔ c.Licenses (construct x)) := by
  decide +kernel

/-- The rows extracting a second gap from a clause are acceptable only when the clause is not
an island. -/
theorem island_rows :
    ∀ x ∈ probing .island, ∀ c, clause? x = some c → x.judgment = .acceptable → ¬ c.IsIsland := by
  simp only [isIsland_iff]
  decide +kernel

end Sag2010
