module

public import Linglib.Syntax.Minimalist.SyntacticObject.Label
public import Linglib.Syntax.Minimalist.SyntacticObject.Build

/-!
# Chomsky (2013): Problems of projection

[chomsky-2013] replaces projection by a labeling algorithm, minimal search for the head of a
syntactic object (`Minimalist.SyntacticObject.label`). A head merged with a phrase labels the
result; two phrases do not, unless one of them raises, its lower copy being invisible to the
search, or their heads share an agreed feature. Raising for labeling reinterprets [moro-2000]'s
dynamic antisymmetry: the small clause of a copular sentence (18) is two phrases and is labeled
only once one of them raises, and the verb phrase with its external argument (17) is labeled
`v` only once that argument raises out of it, which forces the EPP. The intermediate landing
sites of successive-cyclic movement are the most general case: a wh-phrase in the specifier of
an embedded declarative CP leaves it unlabeled, barring (21), and moving on leaves its lower copy,
so the CP is labeled and the verb above selects it.

## Implementation notes

* A clause is represented before its surface subject is merged, `{T, XP}`, labeled `T`: the
  paper argues that the C–T relation is established at that point, before the subject is
  introduced (the discussion of (16)–(17)). The subject and its sister are two phrases, labeled
  by the φ-features they share, which is not formalized.
* The wh-phrase of (21) is an adjunct; its base position is left out.

## TODO

The labeling of the indirect question (22) by the interrogative feature its two phrases share,
and of the case of (17) where the internal argument raises and the external argument stays,
labeled `v` because only the external argument and the raised verb are visible, need Agree and
head movement.

## References

* [chomsky-2013]
* [moro-2000]
-/

@[expose] public section

namespace Chomsky2013

open Minimalist Minimalist.LinearizedSyntacticObject

/-- A token of the examples. -/
def tok (id : ℕ) (cat : Cat) (sel : SelStack := []) (phon : String := "") (wh : Bool := false) :
    LexicalItem.Token :=
  ⟨LexicalItem.of cat sel phon wh false, id⟩

/-! ### Copular small clauses (18) -/

def be := tok 0 .V [.D] "be"
def lightning := tok 1 .D (phon := "lightning")
def the := tok 2 .D [.N] "the"
def cause := tok 3 .N (phon := "cause")

/-- The small clause *[lightning, the cause of the fire]*, two phrases. -/
def smallClause : LinearizedSyntacticObject := lightning * (the * cause)

/-- The small clause after *lightning* has raised out of it, leaving its lower copy. -/
def smallClauseRaised : LinearizedSyntacticObject := .traceOf lightning * (the * cause)

/-- (18): the small clause is unlabeled, so the copula cannot select it. -/
theorem smallClause_label_eq_none :
    (smallClause : SyntacticObject).label = none ∧
      ((be * smallClause : LinearizedSyntacticObject) : SyntacticObject).label = none := by
  decide

/-- (18): once one term raises, the other labels the small clause, and the copula selects it. -/
theorem smallClauseRaised_label :
    (smallClauseRaised : SyntacticObject).label = some the ∧
      ((be * smallClauseRaised : LinearizedSyntacticObject) : SyntacticObject).label = some be := by
  decide

/-! ### The external argument and the EPP (17) -/

def t := tok 4 .T [.v]
def v := tok 5 .v [.V]
def see := tok 6 .V [.D] "see"
def ea := tok 7 .D (phon := "John")
def ia := tok 8 .D (phon := "Bill")

/-- The verb phrase *v [see Bill]*. -/
def vP : LinearizedSyntacticObject := v * (see * ia)

/-- (17): the external argument and the verb phrase are two phrases, so `β` is unlabeled. -/
theorem beta_label_eq_none :
    ((ea * vP : LinearizedSyntacticObject) : SyntacticObject).label = none := by
  decide

/-- (17): once the external argument raises, `β` is labeled `v` and `T` selects it, so the EPP is
forced. -/
theorem beta_label_of_raising :
    ((.traceOf ea * vP : LinearizedSyntacticObject) : SyntacticObject).label = some v ∧
      ((t * (.traceOf ea * vP) : LinearizedSyntacticObject) : SyntacticObject).label = some t := by
  decide

/-! ### Successive-cyclic movement (21) -/

def thought := tok 9 .V [.C] "thought"
def whichCity := tok 10 .P (phon := "in which Texas city") (wh := true)
def c := tok 11 .C [.T]
def was := tok 12 .T [.V] "was"
def assassinated := tok 13 .V [.D] "assassinated"
def jfk := tok 14 .D (phon := "JFK")

/-- The embedded clause *C [was assassinated JFK]*. -/
def cP : LinearizedSyntacticObject := c * (was * (assassinated * jfk))

/-- (21): *in which Texas city* stopping in the specifier of the embedded declarative CP leaves `α`
unlabeled, and *thought* cannot select it. -/
theorem alpha_label_eq_none :
    ((whichCity * cP : LinearizedSyntacticObject) : SyntacticObject).label = none ∧
      ((thought * (whichCity * cP) : LinearizedSyntacticObject) :
        SyntacticObject).label = none := by
  decide

/-- Moving on, the wh-phrase leaves its lower copy, `α` is labeled `C`, and *thought* selects it:
successive-cyclic movement is forced. -/
theorem alpha_label_of_raising :
    ((.traceOf whichCity * cP : LinearizedSyntacticObject) : SyntacticObject).label = some c ∧
      ((thought * (.traceOf whichCity * cP) : LinearizedSyntacticObject) : SyntacticObject).label =
        some thought := by
  decide

end Chomsky2013
