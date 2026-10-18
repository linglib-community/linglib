module

public import Linglib.Syntax.HPSG.Binding
public import Linglib.Syntax.HPSG.Construction
public import Linglib.Data.Examples.SagWasowBender2003

/-!
# Sag, Wasow & Bender (2003): Syntactic Theory: A Formal Introduction

This file formalizes two chapters of the textbook in the RSRL model theory of `Syntax/HPSG`.
The binding theory of Chapter 7 says that an anaphor must be outranked by a coindexed argument
on some argument-structure list and that a nonreflexive pronoun must not be, and the
textbook's judgments on reflexives and pronouns follow from the binding grammar of
`Syntax/HPSG/Binding`, whose outranking is local o-command (`binding_rows`), over a worked
model of a transitive clause such as *Susan likes herself*. The long-distance
dependencies of Chapter 15 rest on the list-valued feature GAP: the GAP Principle sums the
daughters' gaps into the mother and the Head-Filler Rule discharges one, which is the
filler-head construction of `Syntax/HPSG/Construction`. The Coordinate Structure Constraint and
its across-the-board exception are then derived rather than stipulated: conjuncts share their
SYN value, GAP included, so a gap in one conjunct whose filler lies outside is rejected while
gaps in every conjunct paired with one filler pass (`coordinationPrinciple`,
`coordination_rows`), and a conjunct cannot itself be a gap, since a gap is an argument
unrealized in the syntax rather than an empty phrase (`gap_not_conjunct`).

## Implementation notes

The textbook's ranking on argument-structure lists, with a prepositional object of equal rank
to its PP, is the substrate's local o-command relation, given directly on the worked transitive
clause, whose subject is the feminine singular *Susan*; the rows record whether the pronoun's
antecedent is its local o-commander.
Coordination is a binary construct whose conjuncts share their category and GAP list by token
identity, the SYN identity of the textbook's rule; n-ary coordination, the conjunction daughter
and the semantic restriction list are not modelled. The Argument Realization Principle, the
subject-extraction lexical rule and the initial symbol are not formalized.

## References

* [sag-wasow-bender-2003]
* [ross-1967]
* [chomsky-1981]
-/

@[expose] public section

namespace SagWasowBender2003

open HPSG.RSRL HPSG.Construction

/-- The rows on a topic. -/
def probing (t : String) : List Datum :=
  Examples.all.filter fun x ↦ decide (x.feature? "topic" = some t)

/-! ### Binding theory -/

/-- The entities of a worked transitive clause are the verb's sign, its subject and object, two
indices, and the gender and number values. -/
inductive ClauseEnt
  | s | subj | obj | iSubj | iObj | gMasc | gFem | nSing | nPlur
  deriving DecidableEq, Fintype, Repr

/-- The worked transitive clause, whose subject *Susan* is a feminine singular nonpronoun indexed
`iSubj` that locally o-commands the object. The object has the given sort, index, gender and
number. -/
@[reducible] def clause (objSort : Binding.Srt) (objIdx objGend objNum : ClauseEnt) :
    Interpretation Binding.sig ClauseEnt where
  S
    | .s => .sign
    | .subj => .npro
    | .obj => objSort
    | .iSubj | .iObj => .idx
    | .gMasc => .masc
    | .gFem => .fem
    | .nSing => .sing
    | .nPlur => .plur
  A
    | .SUBJ, .s => some .subj
    | .OBJ, .s => some .obj
    | .IDX, .subj => some .iSubj
    | .IDX, .obj => some objIdx
    | .GEND, .subj => some .gFem
    | .GEND, .obj => some objGend
    | .NUM, .subj => some .nSing
    | .NUM, .obj => some objNum
    | _, _ => none
  R _ xs := xs 0 = .subj ∧ xs 1 = .obj

instance (objSort : Binding.Srt) (objIdx objGend objNum : ClauseEnt) (ρ : Binding.sig.Rel) :
    DecidablePred ((clause objSort objIdx objGend objNum).R ρ) :=
  fun xs ↦ inferInstanceAs (Decidable (xs 0 = .subj ∧ xs 1 = .obj))

/-- Every worked clause whose object is a species of nominal object with an index, a gender and
a number is sort-resolved and totally well-typed. -/
theorem clause_isTotallyWellTyped :
    ∀ σ ∈ [Binding.Srt.ana, .ppro, .npro], ∀ i ∈ [ClauseEnt.iSubj, .iObj],
      ∀ γ ∈ [ClauseEnt.gMasc, .gFem], ∀ n ∈ [ClauseEnt.nSing, .nPlur],
        (clause σ i γ n).IsSortResolved ∧ (clause σ i γ n).IsTotallyWellTyped := by
  decide

/-- A clause whose object has the underspecified sort `synsem` is not sort-resolved, and one
whose object has a gender in place of its index is not well-typed. -/
example : ¬ (clause .synsem .iSubj .gFem .nSing).IsSortResolved ∧
    ¬ (clause .ana .gFem .gFem .nSing).IsWellTyped := by decide

def sorts : List (String × Binding.Srt) := [("anaphor", .ana), ("pronoun", .ppro)]

def binders : List (String × ClauseEnt) :=
  [("local", .iSubj), ("nonlocal", .iObj)]

/-- The rows on binding are acceptable exactly when the worked clause with a pronoun of the
row's sort, coindexed with its local o-commander or not as the row records, satisfies the
binding grammar: a reflexive needs a coindexed local o-commander and a nonreflexive pronoun
must lack one. -/
theorem binding_rows :
    ∀ x ∈ probing "binding", ∀ s ∈ x.parse? "sort" sorts, ∀ i ∈ x.parse? "binder" binders,
      (x.judgment = .acceptable ↔
        (clause s i .gFem .nSing).Models Binding.grammar) := by
  decide +kernel

/-- *Susan likes herself* meets the framework-neutral Conditions A and B over local o-command:
the part of its worked clause that the verb's sign generates is rooted at the sign and models
the binding principles. -/
theorem clause_satisfies_conditions :
    let I := (clause .ana .iSubj .gFem .nSing).generated .s
    (Binding.configuration I).Satisfies (Binding.Codependent I) (Binding.configuration I).exempt
      fun x ↦ (I.S x).bindingClass :=
  Binding.satisfies_of_models
    ((show (clause .ana .iSubj .gFem .nSing).Models Binding.grammar by decide).generated .s)
    Interpretation.isRootedAt_generated fun _ h ↦ by cases h.1.symm.trans h.2

/-! ### Long-distance dependencies -/

/-- In the coordination construction the two conjuncts share their category and GAP list, and
the mother carries them. -/
def coordinationPrinciple : Constraint sig where
  sort := .coordCxt
  body :=
    .and (.pathEq (.path [.CONJ1, .CAT]) (.path [.CONJ2, .CAT]))
      (.and (.pathEq (.path [.CONJ1, .GAP]) (.path [.CONJ2, .GAP]))
        (.and (.pathEq (.path [.MTR, .CAT]) (.path [.CONJ1, .CAT]))
          (.pathEq (.path [.MTR, .GAP]) (.path [.CONJ1, .GAP]))))

/-- The filler-gap grammar with the coordination construction. -/
def swbGrammar : Grammar sig := (constraints ++ [coordinationPrinciple]).map Constraint.toDesc

/-- The entities of a worked coordinate construct are the construct, its mother and two
conjuncts, their category, a one-gap list with its NP gap and the gap's index, and the empty
list. -/
inductive CoordEnt where
  | cxt
  | mtr
  | c₁
  | c₂
  | cat
  | np
  | g
  | gp
  | nil
  | ix
  deriving DecidableEq, Fintype, Repr

/-- The GAP list of a conjunct is the shared one-gap list when the conjunct contains a gap, and
the empty list otherwise. -/
def gapList (b : Bool) : CoordEnt := if b then .g else .nil

/-- A coordinate construct of two clausal conjuncts, each containing a gap or not. The gap is one
NP, shared by the conjuncts that have one, and the mother's GAP is the first conjunct's. -/
@[reducible] def coordConstruct (gap₁ gap₂ : Bool) : Interpretation sig CoordEnt where
  S := fun
    | .cxt => .coordCxt
    | .mtr | .c₁ | .c₂ => .overtExpr
    | .cat => .verb
    | .np => .noun
    | .g => .nelist
    | .gp => .gap
    | .nil => .elist
    | .ix => .idx
  A := fun a u ↦ match a, u with
    | .MTR, .cxt => some .mtr
    | .CONJ1, .cxt => some .c₁
    | .CONJ2, .cxt => some .c₂
    | .CAT, .mtr | .CAT, .c₁ | .CAT, .c₂ => some .cat
    | .GAP, .mtr | .GAP, .c₁ => some (gapList gap₁)
    | .GAP, .c₂ => some (gapList gap₂)
    | .FIRST, .g => some .gp
    | .REST, .g => some .nil
    | .CAT, .gp => some .np
    | .INDEX, .gp => some .ix
    | _, _ => none
  R := noRel

/-- The worked coordinate constructs are well-typed. -/
theorem coordConstruct_isWellTyped (g₁ g₂ : Bool) : (coordConstruct g₁ g₂).IsWellTyped := by
  cases g₁ <;> cases g₂ <;> decide

def bools : List (String × Bool) := [("true", true), ("false", false)]

/-- The rows on coordination are acceptable exactly when the coordinate construct with a gap in
the conjuncts the row records satisfies the grammar: a gap in one conjunct alone breaks the
identity of the conjuncts' GAP lists, and gaps in both, paired with one filler, keep it. -/
theorem coordination_rows :
    ∀ x ∈ probing "coordination", ∀ g₁ ∈ x.parse? "gapInFirst" bools,
      ∀ g₂ ∈ x.parse? "gapInSecond" bools,
        (x.judgment = .acceptable ↔ (coordConstruct g₁ g₂).Models swbGrammar) := by
  decide +kernel

/-- A conjunct is an overt expression and a gap a covert one, an argument unrealized in the
syntax, so no well-typed interpretation has a gap for a conjunct. -/
theorem gap_not_conjunct {U : Type*} {I : Interpretation sig U} (hI : I.IsWellTyped) {u v : U}
    (hv : I.A .CONJ1 u = some v) : ¬ I.S v ≤ .gap :=
  fun h ↦ not_le_covertExpr hI (by simp) hv (h.trans (by decide))

end SagWasowBender2003
