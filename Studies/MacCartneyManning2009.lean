module

public import Linglib.Logic.Natural.ImplicationSignature
public import Linglib.Logic.Natural.Projection
public import Linglib.Data.Examples.MacCartneyManning2009
public import Linglib.Data.Examples.Readers
public import Linglib.Fragments.English.Verbs.Implicative
public import Linglib.Fragments.English.Verbs.Causative
public import Linglib.Fragments.English.Verbs.Attitude

/-!
# MacCartney and Manning (2009): implicatives and factives in natural logic

MacCartney and Manning bring the implication signatures of Nairn, Condoravdi and Karttunen into
natural logic through the relation that deleting an operator generates between a sentence and its
complement, and a monotonicity class for each signature. Where the two slots of a signature do not
imply the same polarity, the printed relation is
[the one whose constraints are the signature's implications](##MacCartneyManning2009.deletion_eq),
and inserting the operator generates its converse. The factive and the counterfactive are printed
with [the relation of their positive slot](##MacCartneyManning2009.deletion_factive), since their
full implications settle the complement; this is also why negating a factive sentence and its
complement [does not project](##MacCartneyManning2009.negated_eq) the printed relation through
negation, the negations being [disjoint](##MacCartneyManning2009.negated_factive). Each signature's
monotonicity class is [that of the two-way implicative it
weakens](##MacCartneyManning2009.monotonicity_eq).

## TODO

* The projectivity table for the quantifiers and the inference procedure that chains edits.
* The English Fragment has no entries with the signatures of *permit to* and *refuse to*, and
  records the factivity of *admit* and *pretend* outside their implication signatures.

## References

* [maccartney-manning-2009]
* [nairn-condoravdi-karttunen-2006]
-/

@[expose] public section

namespace MacCartneyManning2009

open NaturalLogic

/-! ### Reading the table -/

/-- The paper's symbol for a slot of a signature. -/
def symbol : Flat Polarity → String
  | ⊥ => "◦"
  | (.positive : Polarity) => "+"
  | (.negative : Polarity) => "−"

/-- The slots of a signature. -/
def slots : List (Flat Polarity) := [⊥, ↑Polarity.positive, ↑Polarity.negative]

/-- The nine signatures under the paper's notation. -/
def signatures : List (String × ImplicationSignature) :=
  slots.flatMap fun p ↦ slots.map fun n ↦ (symbol p ++ "/" ++ symbol n, ⟨p, n⟩)

/-- The relations under the paper's symbols. -/
def relations : List (String × Relation) :=
  [("≡", .equiv), ("⊏", .forward), ("⊐", .reverse), ("^", .negation), ("|", .alternation),
    ("⌣", .cover), ("#", .independent)]

/-- The monotonicity classes, as the projectivity signatures `+`, `−` and `•`. -/
def classes : List (String × ProjectivitySignature) :=
  [("up", .mono), ("down", .anti), ("non", .all)]

/-- A row of the table: a signature, the relations that deleting and inserting an operator of it
generate, and the signature's monotonicity class. -/
structure Row where
  signature : ImplicationSignature
  deletion : Relation
  insertion : Relation
  monotonicity : ProjectivitySignature

/-- A row of the table from the paper's features. -/
def Row.ofDatum (e : Datum) : Option Row := do
  pure ⟨← e.parse? "signature" signatures, ← e.parse? "deletion" relations,
    ← e.parse? "insertion" relations, ← e.parse? "monotonicity" classes⟩

/-- The table. -/
def rows : List Row := Examples.all.filterMap Row.ofDatum

theorem isSome_ofDatum :
    ∀ e ∈ Examples.all, e.feature? "deletion" ≠ none → (Row.ofDatum e).isSome := by
  decide

/-- A negated example: the signature of its operator and the relation between the negated
sentence and the negated complement. -/
structure NegatedRow where
  signature : ImplicationSignature
  relation : Relation

/-- A negated example from the paper's features. -/
def NegatedRow.ofDatum (e : Datum) : Option NegatedRow := do
  pure ⟨← e.parse? "signature" signatures, ← e.parse? "relation" relations⟩

/-- The negated examples. -/
def negatedRows : List NegatedRow := Examples.all.filterMap NegatedRow.ofDatum

theorem isSome_negatedRow_ofDatum :
    ∀ e ∈ Examples.all, e.feature? "relation" ≠ none → (NegatedRow.ofDatum e).isSome := by
  decide

theorem parse_signature_eq_implicative :
    Examples.manage.parse? "signature" signatures = some English.Verbs.manage.implicative ∧
    Examples.force.parse? "signature" signatures = some English.Verbs.force.implicative ∧
    Examples.forget.parse? "signature" signatures = some English.Verbs.forget.implicative ∧
    Examples.hesitate.parse? "signature" signatures = some English.Verbs.hesitate.implicative ∧
    Examples.want.parse? "signature" signatures = some English.Verbs.want.implicative := by
  decide

/-! ### Deletion and insertion -/

/-- Where the two slots of a signature do not imply the same polarity, deleting an operator of the
signature generates the relation whose constraints are the signature's implications, and inserting
it generates the converse. -/
theorem deletion_eq : ∀ r ∈ rows, (∀ q : Polarity, r.signature ≠ ⟨q, q⟩) →
    r.deletion.constraints = r.signature.constraints ∧ r.insertion = r.deletion.converse := by
  decide

/-- The factive and the counterfactive are printed with the relation of their implication in a
positive context, their implications together constraining no relation. -/
theorem deletion_factive : ∀ r ∈ rows, ∀ q : Polarity, r.signature = ⟨q, q⟩ →
    r.deletion.constraints = (⟨r.signature.positive, ⊥⟩ : ImplicationSignature).constraints ∧
      r.insertion = r.deletion.converse := by
  decide

/-! ### Negation -/

/-- Negating a sentence and its complement projects the relation that deleting the operator
generates through negation, an anti-morphism, exactly for the implicatives: *he wasn't permitted to
live* `⊏` *he didn't live*, but *he didn't admit that he knew* `|` *he didn't know*. -/
theorem negated_eq : ∀ n ∈ negatedRows, ∀ r ∈ rows, r.signature = n.signature →
    (ProjectivitySignature.antiAddMult • r.deletion = n.relation ↔
      ∀ q : Polarity, n.signature ≠ ⟨q, q⟩) := by
  decide

theorem negated_factive {α : Type*} [BooleanAlgebra α] {x y : α}
    (h : ∀ a ∈ (⟨↑Polarity.positive, ↑Polarity.positive⟩ : ImplicationSignature).constraints,
      a.Holds x y) :
    ∀ n ∈ negatedRows, n.signature = ⟨↑Polarity.positive, ↑Polarity.positive⟩ →
      n.relation.Holds xᶜ yᶜ := by
  have hy := ImplicationSignature.forall_holds_constraints_factive_iff.1 h
  have : ∀ n ∈ negatedRows, n.signature = ⟨↑Polarity.positive, ↑Polarity.positive⟩ →
      n.relation = .alternation := by decide
  intro n hn hs
  rw [this n hn hs, hy, compl_top]
  exact disjoint_bot_right

/-! ### Monotonicity -/

/-- The monotonicity class of the two-way implicative a signature weakens: monotone below `+/−`,
whose operator is the identity, antitone below `−/+`, whose operator is negation, and none for
`◦/◦` or a signature below neither. -/
def monotonicity (s : ImplicationSignature) : ProjectivitySignature :=
  if s = ⊥ then .all
  else if s ≤ ⟨↑Polarity.positive, ↑Polarity.negative⟩ then .mono
  else if s ≤ ⟨↑Polarity.negative, ↑Polarity.positive⟩ then .anti
  else .all

/-- Each signature's monotonicity class is that of the two-way implicative it weakens. -/
theorem monotonicity_eq : ∀ r ∈ rows, r.monotonicity = monotonicity r.signature := by
  decide

/-- An antitone map between Boolean algebras that projects `^` as `|` projects `⌣` as `|` too. -/
theorem alternation_of_cover {α β : Type*} [BooleanAlgebra α] [BooleanAlgebra β] {f : α → β}
    (hf : Antitone f)
    (h : ∀ x y, Relation.negation.Holds x y → Relation.alternation.Holds (f x) (f y))
    {x y : α} (hxy : Relation.cover.Holds x y) : Relation.alternation.Holds (f x) (f y) :=
  Disjoint.mono_left (hf (codisjoint_iff_compl_le_left.1 hxy)) (h yᶜ y isCompl_compl.symm)

end MacCartneyManning2009
