module

public import Linglib.Data.Examples.BhattTakahashi2011
public import Studies.Lechner2004
public import Linglib.Semantics.Degree.HeimKennedy
public import Linglib.Syntax.Tree.Basic
public import Linglib.Syntax.Command

/-!
# Bhatt and Takahashi (2011): Reduced and unreduced phrasal comparatives

This file formalizes Bhatt and Takahashi's argument that a phrasal comparative is either the
reduction of a clausal source, with the two-place degree head, or genuinely phrasal, with a
three-place head taking an individual standard. Their binding generalization (10), that the
standard is c-commanded by everything that c-commands the associate, holds in English, the
signature of reduction, and fails in Hindi-Urdu, where the standard is an external PP that the
matrix pronoun never c-commands. Their scope generalization of §4, that a quantifier in the
*than*-phrase must scope out exactly when its base position c-commands the degree trace, sorts
the two languages the same way. Japanese realizes both analyses through the subcategorization of
*yori*, and §6 proposes that both degree heads are available crosslinguistically.

## Implementation notes

Generalization (10) is derived from Lechner's Gapped clause, whose remnant inherits the
c-command relations of the correlate. The binding rows code whether the pronoun c-commands the
associate as a feature (`BindingDatum`), and the scope rows are read into the reduced
*than*-clause LFs of (43a) and (43b), where the Heim–Kennedy constraint at the quantifier's base
position decides than-phrase-internal scope. The Single Standard Restriction and the Precedence
Constraint of §3 and the derivation of Japanese's analyses from *yori* are not formalized.

## TODO

Derive the c-command feature of the binding rows from trees of (11)–(13), as
`Lechner2004.PhrasalComparative` does for Lechner's minimal pairs, so that (10) is checked
against the rows rather than presupposed by their coding.

## References

* [bhatt-takahashi-2011]
* [lechner-2004]
* [lechner-2001]
* [merchant-2009]
-/

@[expose] public section

namespace BhattTakahashi2011

open Core.Order Degree PhraseStructure
open PhraseStructure.Tree
open RoseTree (cCommand CCommands)

/-! ### The binding generalization (§2) -/

/-- Under reduction, whatever c-commands the associate in the matrix clause c-commands every
position of the standard, as Generalization (10) states. -/
theorem standard_cCommanded_of_associate (e : Lechner2004.PhrasalComparative) {m : TreePath}
    (hcm : ¬ e.correlate ≤ m) (hmc : ¬ m ≤ e.correlate) (h : CCommands e.matrix m e.correlate)
    (q : List ℕ) : CCommands e.gapped m ⟨e.correlate.toList ++ q⟩ :=
  (e.cCommands_gapped_iff hcm hmc q).2 h

/-- A binding row records whether the matrix pronoun c-commands the associate and whether
coreference between the pronoun and an R-expression inside the standard is attested, with the
row's label. -/
structure BindingDatum where
  citationId : String
  pronCCommandsAssociate : Bool
  corefAttested : Bool
  deriving DecidableEq, Repr

/-- With Condition C, (10) predicts coreference into the standard exactly when the pronoun does
not c-command the associate. -/
def RAPredictsCoref (d : BindingDatum) : Prop :=
  d.pronCCommandsAssociate = false ↔ d.corefAttested = true

instance (d : BindingDatum) : Decidable (RAPredictsCoref d) :=
  inferInstanceAs (Decidable (_ ↔ _))

/-- The direct analysis predicts coreference throughout, since at LF (15) the matrix pronoun does
not c-command the standard. -/
def DAPredictsCoref (d : BindingDatum) : Prop :=
  d.corefAttested = true

instance (d : BindingDatum) : Decidable (DAPredictsCoref d) :=
  inferInstanceAs (Decidable (_ = _))

/-- Binding data realize the reduction analysis when every datum fits its prediction. -/
def realizesReduction (data : List BindingDatum) : Prop :=
  ∀ d ∈ data, RAPredictsCoref d

instance (data : List BindingDatum) : Decidable (realizesReduction data) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))

/-- Binding data realize the direct analysis when every datum attests coreference. -/
def realizesDirect (data : List BindingDatum) : Prop :=
  ∀ d ∈ data, DAPredictsCoref d

instance (data : List BindingDatum) : Decidable (realizesDirect data) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))

/-! ### The rows -/

/-- `bindingOf e` reads a binding row into a `BindingDatum`, recording whether the matrix pronoun
c-commands the associate and whether the coreferential reading the row states is attested. -/
def bindingOf (e : Datum) : Option BindingDatum :=
  (e.feature? "pron_c_commands_associate").bind fun s ↦
    let cc : Option Bool := match s with | "yes" => some true | "no" => some false | _ => none
    cc.map fun b ↦ ⟨e.id, b, decide (.marginal ≤ e.judgment)⟩

/-- `rowsOf g` lists the rows of the language with Glottocode `g`. -/
def rowsOf (glottocode : String) : List Datum :=
  Examples.all.filter (·.language = glottocode)

/-- `englishBindingPairs` holds the English minimal pairs (11)–(13). -/
def englishBindingPairs : List BindingDatum := (rowsOf "stan1293").filterMap bindingOf

/-- `hindiUrduBindingPairs` holds the Hindi-Urdu datum (35). -/
def hindiUrduBindingPairs : List BindingDatum := (rowsOf "hind1269").filterMap bindingOf

/-! ### The binding diagnostic (§2, §3.4) -/

/-- The English data (11)–(13) realize the reduction analysis and rule out the direct analysis. -/
theorem english_binding :
    realizesReduction englishBindingPairs ∧ ¬ realizesDirect englishBindingPairs := by
  decide

/-- The Hindi-Urdu datum (35) realizes the direct analysis and rules out reduction, the pronoun
c-commanding the associate yet coreferring into the standard. -/
theorem hindi_urdu_binding :
    realizesDirect hindiUrduBindingPairs ∧ ¬ realizesReduction hindiUrduBindingPairs := by
  decide

/-! ### The scope diagnostic (§4) -/

/-- A reduced *than*-clause LF is given by its tree, the quantifier's base position and the degree
trace. -/
structure ThanClause where
  tree : Tree Unit String
  qp : TreePath
  trace : TreePath

/-- In the reduced *than*-clause of (43a), *than Craige assigned every second year student d-many
papers*, in a VP shell, the quantifier's base position c-commands the degree trace. -/
def thanClause43a : ThanClause where
  tree := binder 1 (bin (leaf "Craige") (bin (leaf "assigned")
    (bin (leaf "every second year student") (bin (leaf "t") (bin (tr 1) (leaf "many papers"))))))
  qp := ⟨[0, 1, 1, 0]⟩
  trace := ⟨[0, 1, 1, 1, 1, 0]⟩

/-- In the reduced *than*-clause of (43b), *than Craige assigned d-many students every paper by
Klein*, the quantifier's base position does not c-command the degree trace. -/
def thanClause43b : ThanClause where
  tree := binder 1 (bin (leaf "Craige") (bin (leaf "assigned")
    (bin (bin (tr 1) (leaf "many students")) (bin (leaf "t") (leaf "every paper by Klein")))))
  qp := ⟨[0, 1, 1, 1, 1]⟩
  trace := ⟨[0, 1, 1, 0, 0]⟩

/-- A scope row's *than*-clause has the configuration of (43a) when the quantifier's base position
c-commands the degree trace and that of (43b) when it does not. -/
def thanClauseOf (e : Datum) : Option ThanClause :=
  match e.feature? "qp_base_c_commands_degree_trace" with
  | some "yes" => some thanClause43a
  | some "no" => some thanClause43b
  | _ => none

/-- Under reduction, as (43) shows, than-phrase-internal scope is available exactly when the
quantifier in its base position satisfies the Heim–Kennedy constraint against the degree
abstraction at the root of the *than*-clause. -/
def RAPredictsScope (e : Datum) : Prop :=
  ∀ c ∈ thanClauseOf e,
    (IsHeimKennedy (cCommand c.tree) c.qp ⊥ c.trace ↔
      e.feature? "than_internal_scope" = some "available")

instance (e : Datum) : Decidable (RAPredictsScope e) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))

/-- The English scope data (43a–b) follow the reduction generalization. -/
theorem english_scope : ∀ e ∈ rowsOf "stan1293", RAPredictsScope e := by decide

/-- In Hindi-Urdu (40), a quantifier based below the degree trace still scopes out, against the
reduction analysis. -/
theorem hindi_urdu_scope : ∃ e ∈ rowsOf "hind1269", ¬ RAPredictsScope e := by decide

/-! ### The typology (§6) -/

/-- `HeadAvailability` records which analyses a language's phrasal comparatives realize. -/
structure HeadAvailability where
  reductionRealized : Bool
  directRealized : Bool
  deriving DecidableEq, Repr

/-- `headAvailabilityFromBinding data` decides from the two predictions which analyses the binding
data realize. -/
def headAvailabilityFromBinding (data : List BindingDatum) : HeadAvailability where
  reductionRealized := decide (realizesReduction data)
  directRealized := decide (realizesDirect data)

/-- `Language` enumerates the surveyed languages. -/
inductive Language where
  | english
  | hindiUrdu
  | japanese
  deriving DecidableEq, Repr

/-- English and Hindi-Urdu realize the analyses their binding data decide, and Japanese realizes
both, a clausal or multiple-standard complement of *yori* taking the two-place head and a DP
complement the three-place one (§6). -/
def headAvailability : Language → HeadAvailability
  | .english => headAvailabilityFromBinding englishBindingPairs
  | .hindiUrdu => headAvailabilityFromBinding hindiUrduBindingPairs
  | .japanese => ⟨true, true⟩

/-- English realizes reduction alone and Hindi-Urdu the direct analysis alone, so the three
languages occupy three cells of the grid. -/
theorem three_cells :
    headAvailability .english = ⟨true, false⟩ ∧ headAvailability .hindiUrdu = ⟨false, true⟩ ∧
      ∀ l l' : Language, headAvailability l = headAvailability l' → l = l' := by
  refine ⟨by decide, by decide, ?_⟩
  intro l l'; cases l <;> cases l' <;> decide

end BhattTakahashi2011
