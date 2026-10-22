module

public import Linglib.Syntax.Minimalist.Label.MinimalSearch
public import Linglib.Syntax.Minimalist.SyntacticObject.Build
public import Linglib.Data.Examples.Chomsky2013

/-!
# Chomsky (2013): Problems of projection

[chomsky-2013] replaces projection by a labeling algorithm, minimal search for the heads of a
syntactic object (`Minimalist.LinearizedSyntacticObject.labels`). A head merged with a phrase
labels the result, though a root does not qualify as a label; two phrases do not, unless one of
them moves on, its lower copy being outside the domain searched, or their heads agree in a feature,
which then labels. So a copular small clause (18), the verb phrase with its external argument (17)
and an intermediate landing site of wh-movement (21) are labeled only once a phrase moves on, while
an indirect question (22) and the subject–predicate phrase (16) are labeled by the feature their
heads agree in.

## Implementation notes

* Copies are the same tokens at several positions, written out: a derivation with a workspace for
  the specifier would build them.
* Nominals are a determiner over a nominalizer and a root, the paper taking nouns and pronouns to be
  complex. The wh-phrase's [wh] head stands in for the Q particle the paper adopts, which the
  category inventory lacks, and its base position is set-merged with the verb phrase, where the
  paper pair-merges adjuncts.
* Agreement is read off the heads' probes: an interrogative C probes for a [wh] head and T for a
  determiner phrase, and two heads agree in a feature when one bears its probe and finds a goal the
  other heads.

## TODO

* The paper's ⟨valued, unvalued⟩ asymmetry of agreement, which puts the unvalued interrogative
  feature on the wh-phrase rather than a probe on C.
* The split topics of (19), coordination (23), the exceptional case marking of (24), the T–Q
  account of the ECP in (25), and the case of (17) where the internal argument raises and the
  external argument stays, which needs head movement.

## References

* [chomsky-2013]
* [moro-2000]
-/

@[expose] public section

namespace Chomsky2013

open Minimalist Minimalist.LinearizedSyntacticObject

/-- A token of the examples. -/
def tok (id : ℕ) (cat : Cat) (phon : String := "") (wh : Bool := false) (sel : SelStack := []) :
    LexicalItem.Token :=
  ⟨LexicalItem.of cat sel phon wh false, id⟩

/-- A nominal: a determiner over a nominalizer and a root. -/
def nominal (d n r : LexicalItem.Token) : LinearizedSyntacticObject :=
  (d : LinearizedSyntacticObject) * ((n : LinearizedSyntacticObject) * r)

/-! ### Roots and the labeling readout -/

/-- A root, of a category a categorizer determines. -/
def IsRoot (a : LexicalItem.Token) : Prop := a.item.cat = .V ∨ a.item.cat = .N ∨ a.item.cat = .A

instance : DecidablePred IsRoot := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- A categorizer, the head that determines the category of a root. -/
def IsCategorizer (a : LexicalItem.Token) : Prop :=
  a.item.cat = .v ∨ a.item.cat = .n ∨ a.item.cat = .a

instance : DecidablePred IsCategorizer := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- `x` is labeled in `t`, the heads in `Weak` not qualifying as labels: by the one head minimal
search finds, if it qualifies; by a categorizer merged with a root; or by a feature the heads found
agree in. -/
def IsLabeledWith {F : Type*} (Weak : LexicalItem.Token → Prop)
    (Agreed : F → LexicalItem.Token → LexicalItem.Token → Prop) (t : LinearizedSyntacticObject)
    (x : SyntacticObject) : Prop :=
  (∃ a ∈ t.labels x, t.labels x = {a} ∧ ¬ Weak a) ∨
    (∃ k ∈ t.labels x, ∃ r ∈ t.labels x, IsCategorizer k ∧ IsRoot r ∧
      x = ((k : LinearizedSyntacticObject) * r : LinearizedSyntacticObject)) ∨
    ∃ f, t.IsLabeledByFeature Agreed x f

instance {F : Type*} [Fintype F] (Weak : LexicalItem.Token → Prop) [DecidablePred Weak]
    (Agreed : F → LexicalItem.Token → LexicalItem.Token → Prop) [∀ f, DecidableRel (Agreed f)]
    (t : LinearizedSyntacticObject) (x : SyntacticObject) :
    Decidable (IsLabeledWith Weak Agreed t x) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _))

/-! ### Agreement -/

/-- The features that label by agreement. -/
inductive Feature
  | Q | phi
  deriving DecidableEq, Fintype

/-- The probe for a feature on the positions of `t`: for the interrogative feature, [wh] heads; for
φ-features, determiner phrases. -/
def probe (t : LinearizedSyntacticObject) : Feature → Probe t.val.Positions
  | .Q => .relativized fun q ↦ (t.termAt q).token?.any (·.item.wh)
  | .phi => t.phraseProbe .D

/-- The heads bearing the probe for a feature: interrogative C and T. -/
def Probes : Feature → LexicalItem.Token → Prop
  | .Q, a => a.item.cat = .C ∧ a.item.wh = true
  | .phi, a => a.item.cat = .T

instance : ∀ f, DecidablePred (Probes f)
  | .Q => fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))
  | .phi => fun _ ↦ inferInstanceAs (Decidable (_ = _))

/-- Two heads agree in a feature, given the heads bearing probes, when one bears the probe and it
finds a goal the other heads. -/
def AgreedVia (P : Feature → LexicalItem.Token → Prop) (t : LinearizedSyntacticObject)
    (f : Feature) : LexicalItem.Token → LexicalItem.Token → Prop :=
  Relation.SymmGen fun a b ↦ P f a ∧ ∃ g ∈ t.goals (probe t f) ↑a, b ∈ t.labels g

instance (P : Feature → LexicalItem.Token → Prop) [∀ f, DecidablePred (P f)]
    (t : LinearizedSyntacticObject) (f : Feature) : DecidableRel (AgreedVia P t f) :=
  fun _ _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- Agreement in this paper, with interrogative C and T as the probing heads. -/
abbrev Agreed (t : LinearizedSyntacticObject) : Feature → LexicalItem.Token →
    LexicalItem.Token → Prop :=
  AgreedVia Probes t

/-- Labeling in this paper: roots do not qualify as labels. -/
abbrev IsLabeled (t : LinearizedSyntacticObject) (x : SyntacticObject) : Prop :=
  IsLabeledWith IsRoot (Agreed t) t x

/-! ### Copular small clauses (18) -/

def be := tok 0 .V "be"
def d₁ := tok 1 .D
def n₁ := tok 2 .n
def lightningRoot := tok 3 .N "lightning"
/-- *lightning*. -/
def lightning : LinearizedSyntacticObject := nominal d₁ n₁ lightningRoot
def the := tok 4 .D "the"
/-- *the cause* (of the fire). -/
def theCause : LinearizedSyntacticObject := nominal the (tok 5 .n) (tok 6 .N "cause")

/-- The small clause *[lightning, the cause of the fire]*. -/
def smallClause : LinearizedSyntacticObject := lightning * theCause

/-- The copula over the small clause, before either term raises. -/
def copular : LinearizedSyntacticObject := be * smallClause

/-- (18): *lightning* raised over the copula, leaving its lower copy in the small clause. -/
def copularRaised : LinearizedSyntacticObject := lightning * (be * smallClause)

/-- A root does not qualify as a label, so the nominalizer labels its merge with the root. -/
theorem nominalizer_root_isLabeled :
    IsLabeled copular (n₁ * lightningRoot : LinearizedSyntacticObject) := by
  decide +kernel

/-- The small clause is two phrases whose determiners match in category but do not agree, neither
bearing a probe, so it is unlabeled. -/
theorem smallClause_not_isLabeled :
    d₁.item.cat = the.item.cat ∧ ¬ Agreed copular .phi d₁ the ∧
      ¬ IsLabeled copular smallClause := by
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

/-- The clause with the internal argument raised over T instead, the external argument in situ. -/
def objectRaised : LinearizedSyntacticObject := ia * (t * beta)

/-- (17): `β` is two phrases, so it is unlabeled; T labels its merge with `β`, which establishes
the C–T relation before the subject is merged. -/
theorem beta_not_isLabeled : ¬ IsLabeled tP beta ∧ tP.IsLabeledBy tP t := by
  decide +kernel

/-- (17): once the external argument raises, `β` is labeled `v`: in this case the EPP is forced. -/
theorem beta_isLabeledBy_of_raising : clause.IsLabeledBy beta v := by
  decide +kernel

/-- (16): the subject and its sister are two phrases whose heads, the subject's determiner and T,
agree in φ-features, which label the clause. T's probe finds the external argument, the closer
determiner phrase, so the internal argument raised over it labels nothing. -/
theorem clause_isLabeledByFeature_phi :
    clause.IsLabeledByFeature (Agreed clause) clause .phi ∧
      ¬ IsLabeled objectRaised objectRaised := by
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

/-- The embedded declarative CP. -/
def cP : LinearizedSyntacticObject := c * tP'

/-- (20): *they thought JFK was assassinated in which Texas city?*, the wh-phrase in situ. -/
def thoughtInSitu : LinearizedSyntacticObject := thought * cP

/-- `α`: the wh-phrase at the edge of the embedded declarative CP. -/
def alpha : LinearizedSyntacticObject := whichCity * cP

/-- (21): *they thought [α in which Texas city [C [JFK was assassinated]]]*. -/
def thoughtAlpha : LinearizedSyntacticObject := thought * alpha

/-- The wh-phrase moved on from `α`. -/
def movedOn : LinearizedSyntacticObject := whichCity * (thought * alpha)

/-- (20), (21): the declarative CP is labeled with the wh-phrase in situ, but not with the
wh-phrase at its edge, two phrases whose heads agree in nothing. -/
theorem ex20_ex21 :
    (Examples.ex20.judgment = .acceptable ↔ IsLabeled thoughtInSitu cP) ∧
      (Examples.ex21.judgment = .acceptable ↔ IsLabeled thoughtAlpha alpha) := by
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
theorem ex22 :
    wonderedAlpha.labels alphaQ = {inP, cQ} ∧
      wonderedAlpha.IsLabeledByFeature (Agreed wonderedAlpha) alphaQ .Q ∧
      (Examples.ex22.judgment = .acceptable ↔ IsLabeled wonderedAlpha alphaQ) := by
  decide +kernel

end Chomsky2013
