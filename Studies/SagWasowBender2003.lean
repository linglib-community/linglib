module

public import Linglib.Syntax.HPSG.Binding
public import Linglib.Syntax.HPSG.Construction
public import Linglib.Data.Examples.SagWasowBender2003
public import Linglib.Data.Examples.Readers
public import Linglib.Fragments.English.Pronouns

/-!
# Sag, Wasow & Bender (2003): Syntactic Theory: A Formal Introduction

This file formalizes two chapters of the textbook in the RSRL model theory of `Syntax/HPSG`.
The binding theory of Chapter 7 says that an anaphor must be outranked by a coindexed argument
on some argument-structure list and that a nonreflexive pronoun must not be, and the
textbook's judgments on reflexives and pronouns follow from the binding grammar of
`Syntax/HPSG/Binding`, whose outranking is local o-command (`binding_rows`), over a worked
model of a transitive clause such as *Susan likes herself*. The binding principles mention no
agreement, and the textbook adds that coindexed elements agree. Here the person, number and
gender are attributes of the index, as in [pollard-sag-1994], so a reflexive whose form differs
from its antecedent's in one of them cannot share its index: over the pronouns of
`Fragments/English/Pronouns`, a reflexive is licensed with a pronoun antecedent exactly when the
indices of their agreement bundles are compatible (`licenses_iff_compat`), which excludes the
textbook's *I enjoy yourself*, *He enjoys themselves* and *She enjoys himself*
(`agreement_rows`). Equal features do not make two nominals coindexed
(`agreement_eq_not_coindexed`). The long-distance
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
The textbook keeps the agreement features in `AGR`, on the head, and states the agreement of
coindexed elements as a principle of its own; with the features on the index it is a
consequence (`HPSG.RSRL.Binding.agreement_eq_of_coindexed`). A form constrains its index only in
the index of its agreement bundle, so its case is not compared.
Coordination is a binary construct whose conjuncts share their category and GAP list by token
identity, the SYN identity of the textbook's rule; n-ary coordination, the conjunction daughter
and the semantic restriction list are not modelled. The Argument Realization Principle, the
subject-extraction lexical rule and the initial symbol are not formalized.

## References

* [sag-wasow-bender-2003]
* [pollard-sag-1994]
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
indices, and the person, number and gender values. -/
inductive ClauseEnt
  | s | subj | obj | iSubj | iObj | p1 | p2 | p3 | nSing | nPlur | gMasc | gFem | gNeut
  deriving DecidableEq, Fintype, Repr

/-- The person, number and gender values of an index. -/
structure Agr where
  /-- The person value. -/
  per : ClauseEnt
  /-- The number value. -/
  num : ClauseEnt
  /-- The gender value. -/
  gend : ClauseEnt
  deriving DecidableEq, Repr

/-- The third person singular feminine, the values of the index of *Susan*. -/
def Agr.susan : Agr := ⟨.p3, .nSing, .gFem⟩

/-- The eighteen resolved choices of person, number and gender. -/
def agrs : List Agr :=
  [ClauseEnt.p1, .p2, .p3].flatMap fun p ↦ [ClauseEnt.nSing, .nPlur].flatMap fun n ↦
    [ClauseEnt.gMasc, .gFem, .gNeut].map fun g ↦ ⟨p, n, g⟩

/-- The worked transitive clause, whose subject is a nonpronoun indexed `iSubj` that locally
o-commands the object. The object has the given sort and index, and the two indices have the
given values. -/
@[reducible] def clause (objSort : Binding.Srt) (objIdx : ClauseEnt) (subjAgr objAgr : Agr) :
    Interpretation Binding.sig ClauseEnt where
  S
    | .s => .sign
    | .subj => .npro
    | .obj => objSort
    | .iSubj | .iObj => .idx
    | .p1 => .first
    | .p2 => .second
    | .p3 => .third
    | .nSing => .sing
    | .nPlur => .plur
    | .gMasc => .masc
    | .gFem => .fem
    | .gNeut => .neut
  A
    | .SUBJ, .s => some .subj
    | .OBJ, .s => some .obj
    | .IDX, .subj => some .iSubj
    | .IDX, .obj => some objIdx
    | .PER, .iSubj => some subjAgr.per
    | .NUM, .iSubj => some subjAgr.num
    | .GEND, .iSubj => some subjAgr.gend
    | .PER, .iObj => some objAgr.per
    | .NUM, .iObj => some objAgr.num
    | .GEND, .iObj => some objAgr.gend
    | _, _ => none
  R _ := {xs | xs 0 = .subj ∧ xs 1 = .obj}

instance (objSort : Binding.Srt) (objIdx : ClauseEnt) (subjAgr objAgr : Agr)
    (ρ : Binding.sig.Rel) : DecidablePred (· ∈ (clause objSort objIdx subjAgr objAgr).R ρ) :=
  fun xs ↦ inferInstanceAs (Decidable (xs 0 = .subj ∧ xs 1 = .obj))

theorem clause_isTotallyWellTyped :
    ∀ σ ∈ [Binding.Srt.ana, .ppro, .npro], ∀ i ∈ [ClauseEnt.iSubj, .iObj], ∀ a ∈ agrs,
      (clause σ i .susan a).IsSortResolved ∧ (clause σ i .susan a).IsTotallyWellTyped := by
  decide

/-- A clause whose object has the underspecified sort `synsem` is not sort-resolved, and one
whose object has a gender in place of its index is not well-typed. -/
example : ¬ (clause .synsem .iSubj .susan .susan).IsSortResolved ∧
    ¬ (clause .ana .gFem .susan .susan).IsWellTyped := by decide

def sorts : List (String × Binding.Srt) := [("anaphor", .ana), ("pronoun", .ppro)]

def binders : List (String × ClauseEnt) :=
  [("local", .iSubj), ("nonlocal", .iObj)]

theorem binding_rows :
    ∀ x ∈ probing "binding", ∀ s ∈ x.parse? "sort" sorts, ∀ i ∈ x.parse? "binder" binders,
      (x.judgment = .acceptable ↔
        (clause s i .susan .susan).Models Binding.grammar) := by
  decide +kernel

theorem clause_satisfies_conditions :
    let I := (clause .ana .iSubj .susan .susan).generated .s
    (Binding.configuration I).Satisfies (Binding.Coindexed I) (Binding.configuration I).exempt
      fun x ↦ (I.S x).bindingClass :=
  Binding.satisfies_of_models
    ((show (clause .ana .iSubj .susan .susan).Models Binding.grammar by decide).generated .s)
    Interpretation.isRootedAt_generated fun _ ⟨h₁, h₂⟩ ↦ by cases h₁.symm.trans h₂

/-! ### Pronominal agreement -/

/-- A subject whose form has the agreement bundle `a` and a reflexive object whose form has the
bundle `r` are licensed when some worked clause is a model of the binding grammar in which the
index of the subject's agreement bundle extends that of `a` and the object's that of `r`. The
index of a bundle is its person, number and gender, the features an HPSG index bears; a form's
case is not among them. -/
def Licenses (a r : Agreement.Bundle) : Prop :=
  ∃ i ∈ [ClauseEnt.iSubj, .iObj], ∃ x ∈ agrs, ∃ y ∈ agrs,
    a.index ≤ (Binding.agreement (clause .ana i x y) .subj).index ∧
      r.index ≤ (Binding.agreement (clause .ana i x y) .obj).index ∧
        (clause .ana i x y).Models Binding.grammar

instance (a r : Agreement.Bundle) : Decidable (Licenses a r) :=
  inferInstanceAs (Decidable (∃ i ∈ [ClauseEnt.iSubj, .iObj], ∃ x ∈ agrs, ∃ y ∈ agrs, _ ∧ _ ∧ _))

/-- The agreement bundle of an index with the values `x`. -/
def Agr.bundle (x : Agr) : Agreement.Bundle :=
  Binding.agreement (clause .ana .iSubj x x) .subj

theorem agreement_subj (i : ClauseEnt) (x y : Agr) :
    Binding.agreement (clause .ana i x y) .subj = x.bundle := by
  funext d; cases d <;> rfl

theorem agreement_obj_iSubj (x y : Agr) :
    Binding.agreement (clause .ana .iSubj x y) .obj = x.bundle := by
  funext d; cases d <;> rfl

/-- A reflexive object whose index is not the subject's violates Principle A, whatever the values
of the two indices. -/
theorem not_models_iObj (x y : Agr) : ¬ (clause .ana .iObj x y).Models Binding.grammar := fun h ↦ by
  obtain ⟨z, hz, v, hv, hv'⟩ := Binding.exists_coindexed_of_models (r := .s) (x := .obj)
    (y := .subj) h (.single ⟨.OBJ, rfl⟩) (.single ⟨.SUBJ, rfl⟩) rfl ⟨rfl, rfl⟩
  obtain rfl : z = .subj := hz.1
  cases Option.mem_def.1 hv
  cases Option.mem_def.1 hv'

theorem models_iSubj : ∀ x ∈ agrs, (clause .ana .iSubj x x).Models Binding.grammar := by
  decide +kernel

/-- A subject and a reflexive object are licensed exactly when one index bears the features of
both forms. -/
theorem licenses_iff {a r : Agreement.Bundle} :
    Licenses a r ↔ ∃ x ∈ agrs, a.index ≤ x.bundle.index ∧ r.index ≤ x.bundle.index := by
  refine ⟨fun ⟨i, hi, x, hx, y, _, ha, hr, hM⟩ ↦ ?_,
    fun ⟨x, hx, ha, hr⟩ ↦ ⟨.iSubj, by simp, x, hx, x, hx, ?_, ?_, models_iSubj x hx⟩⟩
  · obtain rfl | rfl : i = .iSubj ∨ i = .iObj := by simpa using hi
    · exact ⟨x, hx, agreement_subj _ x y ▸ ha, agreement_obj_iSubj x y ▸ hr⟩
    · exact absurd hM (not_models_iObj x y)
  · exact (agreement_subj _ x x).symm ▸ ha
  · exact (agreement_obj_iSubj x x).symm ▸ hr

/-- With no agreement condition in the binding principles, an English reflexive is licensed with
a pronoun antecedent exactly when the indices of their agreement bundles are compatible:
Principle A requires the two to share an index, and an index has one person, number and
gender. -/
theorem licenses_iff_compat :
    ∀ a ∈ English.Pronouns.personal, ∀ r ∈ English.Pronouns.reflexives,
      (Licenses a.agreement r.agreement ↔ Compat a.agreement.index r.agreement.index) := by
  simp only [licenses_iff]
  decide +kernel

-- (17a)–(17c)
theorem agreement_rows :
    ∀ x ∈ probing "pronominal agreement",
      ∀ a ∈ English.Pronouns.personal, x.feature? "antecedent" = some a.form →
        ∀ r ∈ English.Pronouns.reflexives, x.feature? "reflexive" = some r.form →
          (x.judgment = .acceptable ↔ Licenses a.agreement r.agreement) := by
  simp only [licenses_iff]
  decide +kernel

/-- Nominal objects with the same agreement bundle need not be coindexed: in *Susan likes her*
with *her* another woman the two indices have the same values and the clause is a model. -/
theorem agreement_eq_not_coindexed :
    Binding.agreement (clause .ppro .iObj .susan .susan) .subj =
        Binding.agreement (clause .ppro .iObj .susan .susan) .obj ∧
      ¬ Binding.Coindexed (clause .ppro .iObj .susan .susan) .subj .obj ∧
        (clause .ppro .iObj .susan .susan).Models Binding.grammar := by
  decide +kernel

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
abbrev swbGrammar : Grammar sig :=
  .ofList ((constraints ++ [coordinationPrinciple]).map Constraint.toDescription)

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

theorem coordConstruct_isWellTyped (g₁ g₂ : Bool) : (coordConstruct g₁ g₂).IsWellTyped := by
  cases g₁ <;> cases g₂ <;> decide

theorem coordination_rows :
    ∀ x ∈ probing "coordination", ∀ g₁ ∈ x.bool? "gapInFirst",
      ∀ g₂ ∈ x.bool? "gapInSecond",
        (x.judgment = .acceptable ↔ (coordConstruct g₁ g₂).Models swbGrammar) := by
  decide +kernel

theorem gap_not_conjunct {U : Type*} {I : Interpretation sig U} (hI : I.IsWellTyped) {u v : U}
    (hv : I.A .CONJ1 u = some v) : ¬ I.S v ≤ .gap :=
  fun h ↦ not_le_covertExpr hI (by simp) hv (h.trans (by decide))

end SagWasowBender2003
