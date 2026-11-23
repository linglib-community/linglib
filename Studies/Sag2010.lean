module

public import Linglib.Syntax.HPSG.Construction
public import Linglib.Syntax.HPSG.RSRL.Satisfiability
public import Linglib.Data.Examples.Sag2010
public import Linglib.Data.Examples.Readers

/-!
# Sag (2010): English Filler-Gap Constructions

English has five kinds of clause in which a phrase at the front is understood in a gap further
in: topicalized clauses, wh-exclamatives, nonsubject wh-interrogatives, wh-relatives and
the-clauses. The paper analyses them as constructions that share the *filler-head* construction
and each add a few constraints of their own.

A row of the paper's examples describes a construct, and the row is acceptable exactly when that
construct is a model of the grammar (`judgments`). A clause is an *absolute island* when the
grammar entails that every construct of its sort has a mother with an empty `GAP` list;
topicalized clauses, wh-exclamatives and the-clauses are islands (`isIsland_iff`). No wh-form
occurs in all three wh-constructions (`no_universal_wh_word`).

## Implementation notes

The features `WH`, `REL` and `VAL` are not in the signature, so the distinguished element is
checked against the wh-word inventory, and S and VP are not told apart. The inventory is read
off the judgment triples; the paper's table of wh-words differs from them in two cells.
Independence is identified with the absence of embedding. The island rows are checked in one
direction, since the paper attributes the degradation of extraction from finite
wh-interrogatives to processing. No row tests a the-clause for islandhood.

## TODO

* The paper stars its example of a the-clause with a complementizer head, while its text admits
  an S or CP head. The row is omitted.

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

/-- The entities of a worked construct are the construct, its mother, head daughter and filler
daughter, their categories, two list cells and the empty list, two gaps with their indices and
the second gap's category, the mother's semantic object, and the values of the head's
features. -/
inductive Ent
  | cxt | mtr | hd | fl | flCat | hdCat | g1 | g2 | nil | gp1 | gp2 | gp2Cat | ix1 | ix2 | sem
  | plus | minus | fin | inf
  deriving DecidableEq, Fintype, Repr

/-- The construct of sort `σ` whose filler and head daughters have the categories `filler` and
`head`, whose head has the inversion, independence and verb-form values `inv`, `ic` and `vform`,
whose mother has the semantic type `semSort`, and whose mother's `GAP` list is `rest`, either
the empty list `nil` or the list `g2` of a second gap. The filler shares its category and index
with the first gap, and the mother its category with the head daughter. As the signature
requires, only a verb has an inversion value and only a verbal category an independence value
and a verb form. -/
@[reducible] def construct (σ : Srt) (filler head : Cat) (inv ic vform : Ent) (semSort : Srt)
    (rest : Ent) : Interpretation sig Ent where
  S
    | .cxt => σ
    | .mtr | .hd | .fl => .overtExpr
    | .flCat => filler.sort
    | .hdCat => head.sort
    | .g1 | .g2 => .nelist
    | .nil => .elist
    | .gp1 | .gp2 => .gap
    | .gp2Cat => .noun
    | .ix1 | .ix2 => .idx
    | .sem => semSort
    | .plus => .plus
    | .minus => .minus
    | .fin => .fin
    | .inf => .inf
  A
    | .MTR, .cxt => some .mtr
    | .HDDTR, .cxt => some .hd
    | .FILLERDTR, .cxt => some .fl
    | .CAT, .fl | .CAT, .gp1 => some .flCat
    | .INDEX, .fl | .INDEX, .gp1 => some .ix1
    | .CAT, .hd | .CAT, .mtr => some .hdCat
    | .INV, .hdCat => if head.sort ≤ .verb then some inv else none
    | .IC, .hdCat => if head.sort ≤ .verbal then some ic else none
    | .VFORM, .hdCat => if head.sort ≤ .verbal then some vform else none
    | .GAP, .hd => some .g1
    | .FIRST, .g1 => some .gp1
    | .REST, .g1 | .GAP, .mtr => some rest
    | .FIRST, .g2 => some .gp2
    | .CAT, .gp2 => some .gp2Cat
    | .INDEX, .gp2 => some .ix2
    | .REST, .g2 | .GAP, .fl | .GAP, .gp1 | .GAP, .gp2 => some .nil
    | .SEM, .mtr => some .sem
    | _, _ => none
  R := noRel

/-- The construct sort of a clause whose head has the verb form `vform`. A wh-relative is finite
or infinitival. -/
def FGClause.cxtSort : FGClause → Ent → Srt
  | .whRelative, .inf => .infWhRelCl
  | .whRelative, _ => .finWhRelCl
  | c, _ => c.sort

/-- A finite construct of the clause with a noun phrase filler and a sentential head, whose
mother has semantic type `semSort` and `GAP` list `rest`. Its head is inverted and independent
in a wh-interrogative, uninverted and embedded in a wh-relative, and uninverted and independent
otherwise. -/
abbrev FGClause.construct (c : FGClause) (semSort : Srt) (rest : Ent) : Interpretation sig Ent :=
  Sag2010.construct (c.cxtSort .fin) .NP .S (if c = .whInterrogative then .plus else .minus)
    (if c = .whRelative then .minus else .plus) .fin semSort rest

theorem models_construct_iff (c : FGClause) (σ : Srt)
    (hσ : σ ∈ [Srt.question, .fact, .modifier, .austinean]) :
    (c.construct σ .nil).Models grammar ↔ σ = c.sem := by
  revert c σ
  decide +kernel

theorem isWellTyped_constructs (c : FGClause) :
    (c.construct c.sem .nil).IsWellTyped ∧ (c.construct c.sem .g2).IsWellTyped := by
  cases c <;> decide +kernel

/-- A filler that differs in category from the gap it fills violates the filler-head
construction. -/
example : ¬ { FGClause.topicalized.construct .austinean .nil with
    A := fun (a : Attr) (v : Ent) ↦ match a, v with
      | .CAT, .gp1 => some .hdCat
      | a, v => (FGClause.topicalized.construct .austinean .nil).A a v }.Models grammar := by
  decide +kernel

/-! ### Islands -/

/-- A clause is an absolute island when the grammar entails that every construct of its sort has
a mother with an empty `GAP` list, so that no gap inside the clause is bound outside it. -/
def FGClause.IsIsland (c : FGClause) : Prop :=
  grammar.Entails (⟨c.sort, [.sort [.MTR, .GAP] .elist]⟩ : Constraint sig).toDescription

variable {U : Type*} {I : Interpretation sig U} {u : U}

theorem sortAt_hdDtr_gap_rest (hI : I.Models grammar) {c : FGClause}
    (hc : c = .topicalized ∨ c = .whExclamative ∨ c = .theClause) (hu : I.S u ≤ c.sort) :
    I.SortAt u [.HDDTR, .GAP, .REST] .elist := by
  rcases hc with rfl | rfl | rfl
  exacts [hI.sortAt topPrinciple hu, hI.sortAt whExclPrinciple hu, hI.sortAt thePrinciple hu]

theorem isIsland_iff (c : FGClause) :
    c.IsIsland ↔ c = .topicalized ∨ c = .whExclamative ∨ c = .theClause := by
  refine ⟨fun h ↦ ?_, fun hc ↦ Grammar.entails_toDescription_iff.2 fun U I _ hI u hu a ha ↦ ?_⟩
  · by_contra hc
    have key : ∀ c : FGClause, ¬ (c = .topicalized ∨ c = .whExclamative ∨ c = .theClause) →
        (c.construct c.sem .g2).Models grammar ∧
          ¬ (c.construct c.sem .g2).SortAt .cxt [.MTR, .GAP] .elist := by
      decide +kernel
    obtain ⟨hM, hn⟩ := key c hc
    exact hn (h.holds (isWellTyped_constructs c).2 hM (r := .cxt)
      ((by decide +kernel : ∀ c : FGClause, c.cxtSort .fin ≤ c.sort) c)
      (List.mem_singleton_self _))
  · obtain rfl := List.mem_singleton.1 ha
    exact (sortAt_mtr_gap_iff hI
      (hu.trans ((by decide +kernel : ∀ c : FGClause, c.sort ≤ .fillerHeadCxt) c)) .elist).2
      (sortAt_hdDtr_gap_rest hI hc hu)

/-! ### The parameters of variation

The constructions fix the parameters of variation (6) in every model of the grammar, not only
in the worked constructs. -/

private theorem le_finWhRelCl_or_le_infWhRelCl (hs : I.IsSortResolved) (hu : I.S u ≤ .whRelCl) :
    I.S u ≤ .finWhRelCl ∨ I.S u ≤ .infWhRelCl :=
  (by decide +kernel : ∀ σ : Srt, σ ≤ .whRelCl → IsSpecies σ →
    σ ≤ .finWhRelCl ∨ σ ≤ .infWhRelCl) _ hu (hs u)

/-- The filler daughter of each of the five clauses is nonverbal (25). -/
theorem sortAt_fillerDtr_cat (hI : I.Models grammar) (hs : I.IsSortResolved)
    (c : FGClause) (hu : I.S u ≤ c.sort) : I.SortAt u [.FILLERDTR, .CAT] .nonverbal := by
  cases c
  · exact hI.sortAt topPrinciple hu
  · exact hI.sortAt whExclPrinciple hu
  · exact hI.sortAt nsWhIntPrinciple hu
  · rcases le_finWhRelCl_or_le_infWhRelCl hs hu with h | h
    · exact (hI.sortAt finWhRelPrinciple h (σ := .nominal)).mono (by decide)
    · exact (hI.sortAt infWhRelPrinciple h (σ := .prep)).mono (by decide)
  · exact hI.sortAt thePrinciple hu

/-- The head daughter of a topicalized clause, wh-exclamative, wh-interrogative or wh-relative is a
projection of a verb (27). -/
theorem sortAt_hdDtr_cat (hI : I.Models grammar) (hw : I.IsWellTyped) {c : FGClause}
    (hc : c ≠ .theClause) (hu : I.S u ≤ c.sort) : I.SortAt u [.HDDTR, .CAT] .verb := by
  cases c
  · exact hI.sortAt topPrinciple hu
  · exact sortAt_of_sortAt_concat hw (p := [.HDDTR, .CAT]) (α := .INV) (by decide)
      (hI.sortAt whExclPrinciple hu (p := [.HDDTR, .CAT, .INV]) (σ := .minus))
  · obtain ⟨v, hv, -⟩ :=
      hI.pathEq nsWhIntPrinciple hu (p := [.HDDTR, .CAT, .INV]) (q := [.HDDTR, .CAT, .IC])
    exact sortAt_of_sortAt_concat hw (p := [.HDDTR, .CAT]) (α := .INV) (by decide)
      ⟨v, hv, le_rfl⟩
  · exact sortAt_of_sortAt_concat hw (p := [.HDDTR, .CAT]) (α := .INV) (by decide)
      ((sortAt_mtr_cat_iff hI (hu.trans (by decide)) [.INV] .minus).1
        (hI.sortAt relativePrinciple (hu.trans (by decide))))
  · exact absurd rfl hc

/-- The head daughter of a topicalized clause, wh-exclamative or wh-relative is uninverted (28).
A wh-relative inherits this from the relative construction on its mother. -/
theorem sortAt_hdDtr_inv (hI : I.Models grammar) {c : FGClause}
    (hc : c = .topicalized ∨ c = .whExclamative ∨ c = .whRelative) (hu : I.S u ≤ c.sort) :
    I.SortAt u [.HDDTR, .CAT, .INV] .minus := by
  rcases hc with rfl | rfl | rfl
  · exact hI.sortAt topPrinciple hu
  · exact hI.sortAt whExclPrinciple hu
  · exact (sortAt_mtr_cat_iff hI (hu.trans (by decide)) [.INV] .minus).1
      (hI.sortAt relativePrinciple (hu.trans (by decide)))

/-- The head daughter of a topicalized clause, wh-exclamative, the-clause or finite wh-relative is
finite (29). -/
theorem sortAt_hdDtr_vform (hI : I.Models grammar)
    (hu : I.S u ≤ .topCl ∨ I.S u ≤ .whExclCl ∨ I.S u ≤ .theCl ∨ I.S u ≤ .finWhRelCl) :
    I.SortAt u [.HDDTR, .CAT, .VFORM] .fin := by
  rcases hu with hu | hu | hu | hu
  · exact hI.sortAt topPrinciple hu
  · exact hI.sortAt whExclPrinciple hu
  · exact hI.sortAt thePrinciple hu
  · exact (sortAt_mtr_cat_iff hI (hu.trans (by decide)) [.VFORM] .fin).1
      (hI.sortAt finWhRelPrinciple hu)

theorem sortAt_hdDtr_ic (hI : I.Models grammar) :
    (I.S u ≤ .topCl → I.SortAt u [.HDDTR, .CAT, .IC] .plus) ∧
      (I.S u ≤ .whRelCl → I.SortAt u [.HDDTR, .CAT, .IC] .minus) :=
  ⟨fun hu ↦ hI.sortAt topPrinciple hu,
    fun hu ↦ (sortAt_mtr_cat_iff hI (hu.trans (by decide)) [.IC] .minus).1
      (hI.sortAt relativePrinciple (hu.trans (by decide)))⟩

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

/-- The inversion values that rows record. -/
def inversions : List (String × Ent) := [("true", .plus), ("false", .minus)]

/-- The independence values of embedded and matrix clauses. -/
def embeddings : List (String × Ent) := [("true", .minus), ("false", .plus)]

/-- The verb forms of finite and infinitival clauses. -/
def verbForms : List (String × Ent) := [("true", .fin), ("false", .inf)]

/-- The construct of the clause `c` that a row describes, with its filler and head categories
and the inversion, embedding and finiteness of its head. The filler is an NP and the head an
uninverted, finite, matrix S unless the row records otherwise. -/
@[reducible] def rowConstruct (c : FGClause) (x : Datum) : Interpretation sig Ent :=
  let vform := (x.parse? "finite" verbForms).getD .fin
  construct (c.cxtSort vform) ((x.parse? "filler" cats).getD .NP) ((x.parse? "head" cats).getD .S)
    ((x.parse? "inverted" inversions).getD .minus) ((x.parse? "embedded" embeddings).getD .plus)
    vform c.sem .nil

/-- The wh-form and category of a row's filler, if it contains a wh-word. -/
def whWord? (x : Datum) : Option (WhForm × WhCategory) :=
  (x.parse? "whForm" whForms).bind fun f ↦ (x.parse? "whCategory" whCategories).map (f, ·)

/-- The judgment the inventory records for a wh-form of a category in a wh-construction. -/
def occurs (f : WhForm) (cat : WhCategory) (c : FGClause) : Option Judgment :=
  ((probing .inventory).find? fun x ↦ decide (whWord? x = some (f, cat) ∧ clause? x = some c)).map
    (·.judgment)

/-- The three wh-constructions. -/
def whClauses : List FGClause := [.whInterrogative, .whExclamative, .whRelative]

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
  | none => if (x.bool? "the").getD false then [.the] else [.none]

theorem distinguished :
    ∀ x ∈ probing .distinguished, ∀ c, clause? x = some c →
      (x.judgment = .acceptable ↔ c.marker ∈ fillerMarkers x) := by
  decide +kernel

/-- The rows probing the categories of the daughters and the inversion, finiteness and
independence of the head are acceptable exactly when the construct they describe is a model of
the grammar. -/
theorem judgments :
    ∀ p ∈ [Parameter.fillerCategory, .headCategory, .inversion, .finiteness, .independence],
      ∀ x ∈ probing p, ∀ c, clause? x = some c →
        (x.judgment = .acceptable ↔ (rowConstruct c x).Models grammar) := by
  decide +kernel

theorem isWellTyped_rowConstruct :
    ∀ p ∈ [Parameter.fillerCategory, .headCategory, .inversion, .finiteness, .independence],
      ∀ x ∈ probing p, ∀ c, clause? x = some c → (rowConstruct c x).IsWellTyped := by
  decide +kernel

theorem island_rows :
    ∀ x ∈ probing .island, ∀ c, clause? x = some c → x.judgment = .acceptable → ¬ c.IsIsland := by
  simp only [isIsland_iff]
  decide +kernel

end Sag2010
