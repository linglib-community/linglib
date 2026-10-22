module

public import Linglib.Syntax.Minimalist.Probe.Label
public import Linglib.Syntax.Minimalist.SyntacticObject.Build

/-!
# Chomsky (2013): Problems of projection

[chomsky-2013] replaces projection by a labeling algorithm, minimal search for the heads of a
syntactic object (`Minimalist.LinearizedSyntacticObject.labels`). A head merged with a phrase
labels the result; two phrases do not, unless one of them moves on, its lower copy being outside
the domain searched, or their heads agree in a feature, which then labels. So a copular small
clause (18), the verb phrase with its external argument (17) and an intermediate landing site of
wh-movement (21) are labeled only once a phrase moves on, while an indirect question (22) and the
subject–predicate phrase (16) are labeled by the interrogative feature and the φ-features their
heads agree in.

## Implementation notes

* Copies are the same tokens at several positions, so a phrase that has moved on has an
  occurrence outside what it moved out of.
* Nominals are a determiner over a nominalizer and a root: the paper takes nouns and pronouns to be
  complex, since a one-word subject would label the clause.
* Agreement is read off the heads' probes: an interrogative C probes for a [wh] head and T for a
  determiner, and two heads agree in a feature when one bears its probe and finds the other. The
  [wh] head of the pied-piped phrase stands in for the Q particle the paper adopts, which the
  category inventory lacks. Mere matching is not agreement: the two determiners of a small clause
  agree in nothing.
* The base position of the wh-phrase of (21) and (22) is an adjunct of the verb phrase, where
  C's probe finds it.

## TODO

The case of (17) where the internal argument raises and the external argument stays, labeled `v`
because only the external argument and the raised verb are visible, needs head movement.

## References

* [chomsky-2013]
* [moro-2000]
-/

@[expose] public section

namespace Chomsky2013

open Minimalist Minimalist.LinearizedSyntacticObject

/-- A token of the examples. -/
def tok (id : ℕ) (cat : Cat) (phon : String := "") (wh : Bool := false) : LexicalItem.Token :=
  ⟨LexicalItem.of cat [] phon wh false, id⟩

/-- A nominal: a determiner over a nominalizer and a root. -/
def nominal (d n r : LexicalItem.Token) : LinearizedSyntacticObject :=
  (d : LinearizedSyntacticObject) * ((n : LinearizedSyntacticObject) * r)

/-! ### Agreement -/

/-- The features that label by agreement. -/
inductive Feature
  | Q | phi
  deriving DecidableEq, Fintype

/-- The probe for a feature on the positions of `t`: for the interrogative feature, [wh] heads; for
φ-features, determiners. -/
def probe (t : LinearizedSyntacticObject) : Feature → Probe t.val.Positions
  | .Q => .relativized fun q ↦ (t.termAt q).token?.any (·.item.wh)
  | .phi => .relativized fun q ↦ decide (SyntacticObject.isLeafOf .D (t.termAt q))

/-- The heads bearing the probe for a feature: interrogative C and T. -/
def Probes : Feature → LexicalItem.Token → Prop
  | .Q, h => h.item.cat = .C ∧ h.item.wh = true
  | .phi, h => h.item.cat = .T

instance : ∀ f, DecidablePred (Probes f)
  | .Q => fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))
  | .phi => fun _ ↦ inferInstanceAs (Decidable (_ = _))

/-- Two heads agree in a feature when one bears its probe and the probe finds the other. -/
def Agreed (t : LinearizedSyntacticObject) (f : Feature) (h h' : LexicalItem.Token) : Prop :=
  (Probes f h ∧ ↑h' ∈ t.goals (probe t f) ↑h) ∨ (Probes f h' ∧ ↑h ∈ t.goals (probe t f) ↑h')

instance (t : LinearizedSyntacticObject) (f : Feature) : DecidableRel (Agreed t f) :=
  fun _ _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-! ### Copular small clauses (18) -/

def be := tok 0 .V "be"
/-- *lightning*. -/
def lightning : LinearizedSyntacticObject :=
  nominal (tok 1 .D) (tok 2 .n) (tok 3 .N "lightning")
def the := tok 4 .D "the"
/-- *the cause* (of the fire). -/
def theCause : LinearizedSyntacticObject := nominal the (tok 5 .n) (tok 6 .N "cause")

/-- The small clause *[lightning, the cause of the fire]*. -/
def smallClause : LinearizedSyntacticObject := lightning * theCause

/-- The copula over the small clause, before either term raises. -/
def copular : LinearizedSyntacticObject := be * smallClause

/-- (18): *lightning* raised over the copula, leaving its lower copy in the small clause. -/
def copularRaised : LinearizedSyntacticObject := lightning * (be * smallClause)

/-- The small clause is two phrases whose determiners agree in nothing, so it is unlabeled. -/
theorem smallClause_not_isLabeled :
    ¬ copular.IsLabeled (Agreed copular) smallClause := by
  decide +kernel

/-- (18): once *lightning* raises, its lower copy is invisible and *the* labels the small clause;
the copula labels its merge with it. -/
theorem smallClause_isLabeledBy_of_raising :
    copularRaised.IsLabeledBy smallClause the ∧
      copularRaised.IsLabeledBy (be * smallClause : LinearizedSyntacticObject) be := by
  decide +kernel

/-! ### The external argument and the EPP (17), the subject (16) -/

def t := tok 7 .T
def v := tok 8 .v
def see := tok 9 .V "see"
def dEA := tok 10 .D
/-- The external argument *John*. -/
def ea : LinearizedSyntacticObject := nominal dEA (tok 11 .n) (tok 12 .N "John")
/-- The internal argument *Bill*. -/
def ia : LinearizedSyntacticObject := nominal (tok 13 .D) (tok 14 .n) (tok 15 .N "Bill")

/-- The verb phrase *v [see Bill]*. -/
def vP : LinearizedSyntacticObject := v * (see * ia)

/-- `β = {EA, vP}`. -/
def beta : LinearizedSyntacticObject := ea * vP

/-- T merged with `β`, before the external argument raises. -/
def tP : LinearizedSyntacticObject := t * beta

/-- The clause with the external argument raised over T. -/
def clause : LinearizedSyntacticObject := ea * (t * beta)

/-- (17): `β` is two phrases, so it is unlabeled; T labels its merge with `β`, which establishes the
C–T relation before the subject is merged. -/
theorem beta_not_isLabeled :
    ¬ tP.IsLabeled (Agreed tP) beta ∧ tP.IsLabeledBy tP t := by
  decide +kernel

/-- (17): once the external argument raises, `β` is labeled `v`, so the EPP is forced. -/
theorem beta_isLabeledBy_of_raising : clause.IsLabeledBy beta v := by
  decide +kernel

/-- (16): the subject and its sister are two phrases whose heads, the subject's determiner and T,
agree in φ-features, which label the clause. -/
theorem clause_isLabeledByFeature_phi : clause.IsLabeledByFeature (Agreed clause) clause .phi := by
  decide +kernel

/-! ### Successive-cyclic movement (21) and indirect questions (22) -/

def thought := tok 16 .V "thought"
def wondered := tok 17 .V "wondered"
def c := tok 18 .C
def cQ := tok 19 .C (wh := true)
def was := tok 20 .T "was"
def assassinated := tok 21 .V "assassinated"
/-- *JFK*. -/
def jfk : LinearizedSyntacticObject := nominal (tok 22 .D) (tok 23 .n) (tok 24 .N "JFK")
def inP := tok 25 .P "in" (wh := true)
/-- *in which Texas city*. -/
def whichCity : LinearizedSyntacticObject :=
  inP * nominal (tok 26 .D "which" (wh := true)) (tok 27 .n) (tok 28 .N "city")

/-- *JFK was assassinated in which Texas city*, the wh-phrase in its base position. -/
def tP' : LinearizedSyntacticObject := was * ((assassinated * jfk) * whichCity)

/-- `α`: the wh-phrase at the edge of the embedded declarative CP. -/
def alpha : LinearizedSyntacticObject := whichCity * (c * tP')

/-- (21): *they thought [α in which Texas city [C [JFK was assassinated]]]*. -/
def thoughtAlpha : LinearizedSyntacticObject := thought * alpha

/-- The wh-phrase moved on from `α`. -/
def movedOn : LinearizedSyntacticObject := whichCity * (thought * alpha)

/-- (21): the wh-phrase and the declarative CP are two phrases whose heads agree in nothing, so `α`
is unlabeled, barring (21). -/
theorem alpha_not_isLabeled : ¬ thoughtAlpha.IsLabeled (Agreed thoughtAlpha) alpha := by
  decide +kernel

/-- Moving on, the wh-phrase leaves `α` to C: successive-cyclic movement is forced. -/
theorem alpha_isLabeledBy_of_raising : movedOn.IsLabeledBy alpha c := by
  decide +kernel

/-- The embedded interrogative of (22). -/
def alphaQ : LinearizedSyntacticObject := whichCity * (cQ * tP')

/-- (22): *they wondered [α in which Texas city [β C [JFK was assassinated]]]*. -/
def wonderedAlpha : LinearizedSyntacticObject := wondered * alphaQ

/-- (22): `α` is two phrases, but their heads agree in the interrogative feature, which labels it:
C's probe finds the wh-phrase's head in its base position. -/
theorem alphaQ_isLabeledByFeature_Q :
    wonderedAlpha.labels alphaQ = {inP, cQ} ∧
      wonderedAlpha.IsLabeledByFeature (Agreed wonderedAlpha) alphaQ .Q := by
  decide +kernel

end Chomsky2013
