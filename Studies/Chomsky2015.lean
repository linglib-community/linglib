module

public import Studies.Chomsky2013
public import Linglib.Data.Examples.Chomsky2015
public import Linglib.Syntax.Minimalist.Domain.Basic

/-!
# Chomsky (2015): Problems of projection: Extensions

[chomsky-2015] takes T, like a root, to be too weak to label in a language with weak agreement like
English, while Italian T, with rich agreement, labels by itself. T merged with its complement is
then labeled only by agreement with a subject in its specifier, the EPP, and a subject moved on
leaves T alone, unable to label, the ECP. A root merged with the object labels only once the object
raises to its specifier and agrees with the φ-features the root inherits from v*, raising to
object. Labels are computed at the phase level and kept: a deleted complementizer passes its
phasehood to T, and v*, invisible once the root raises to it, passes its phasehood to the root, so
that a subject or object labeled at their edge is free to move on. A wh-phrase raised out of its
criterial position leaves the interrogative C to label the clause by itself, as a yes-no question.

## Implementation notes

* The phase heads are C and v*. An occurrence is labeled in the object built at its phase level
  (`Minimalist.phaseLevel`), and the label stays.
* Transfer seals the complement of a phase head, or of the head inheriting its phasehood, once its
  phase is complete (`Minimalist.Pic1`).
* The matrix clauses of (2′), (3′) and (4) are cut down to the raised wh-phrase over the verb or
  *do*.
* Weakness is fixed by the richness of agreement the paper attributes to a language.
* A root inherits φ-features when minimal search finds it in the sister of v*.

## TODO

* The amalgam a root forms by raising to v*, with v* affixed and invisible, which needs head
  movement; and the crash at the conceptual-intentional interface of (1) read as a yes-no question.
* The free order of operations of (8), evaluated at the phase level, which needs a derivation.

## References

* [chomsky-2015]
* [chomsky-2013]
-/

@[expose] public section

namespace Chomsky2015

open Core.Order Minimalist Minimalist.LinearizedSyntacticObject
open Chomsky2013 (tok nominal Feature IsRoot IsCategorizer IsLabeledWith AgreedVia)

/-! ### Weak heads and agreement -/

/-- The richness of agreement, which decides whether T can label. -/
inductive Agreement
  | weak | rich
  deriving DecidableEq

/-- The richness of agreement the paper attributes to a language: weak in English, rich in
Italian. -/
def agreementOf : String → Option Agreement
  | "stan1293" => some .weak
  | "ital1282" => some .rich
  | _ => none

/-- The paper's examples are English, where agreement is weak. -/
theorem agreementOf_examples : ∀ r ∈ Examples.all, agreementOf r.language = some .weak := by
  decide

/-- A head too weak to label: a root, or T where agreement is weak. -/
def Weak (ag : Agreement) (a : LexicalItem.Token) : Prop :=
  IsRoot a ∨ (ag = .weak ∧ a.item.cat = .T)

instance (ag : Agreement) : DecidablePred (Weak ag) := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

def vStar := tok 100 .v "v*" (sel := [.V])

/-- A root that minimal search finds in the sister of v*, which inherits its φ-features. -/
def InheritsPhi (t : LinearizedSyntacticObject) (r : LexicalItem.Token) : Prop :=
  IsRoot r ∧ ∃ p d : t.val.Positions, t.termAt p = ↑vStar ∧ p ≠ ⊥ ∧ d ≠ ⊥ ∧ p ≠ d ∧
    p.val.parent = d.val.parent ∧ r ∈ t.labelsAt d

instance (t : LinearizedSyntacticObject) : DecidablePred (InheritsPhi t) :=
  fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- The heads bearing the probe for a feature: those of [chomsky-2013], and the roots that inherit
φ-features from v*. -/
def Probes (t : LinearizedSyntacticObject) (f : Feature) (a : LexicalItem.Token) : Prop :=
  Chomsky2013.Probes f a ∨ (f = .phi ∧ InheritsPhi t a)

instance (t : LinearizedSyntacticObject) (f : Feature) : DecidablePred (Probes t f) :=
  fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- Agreement in this paper. -/
abbrev Agreed (t : LinearizedSyntacticObject) : Feature → LexicalItem.Token →
    LexicalItem.Token → Prop :=
  AgreedVia (Probes t) t

/-- Labeling in this paper: weak heads do not qualify as labels. -/
abbrev IsLabeled (ag : Agreement) (t : LinearizedSyntacticObject) (x : SyntacticObject) : Prop :=
  IsLabeledWith (Weak ag) (Agreed t) t x

/-! ### Phases -/

/-- The deleted complementizer, Ø. -/
def cNull := tok 135 .C (sel := [.T])

/-- The phase heads: C and v*. -/
def IsPhaseHead (a : LexicalItem.Token) : Prop := a.item.cat = .C ∨ a = vStar

instance : DecidablePred IsPhaseHead := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- The phase heads that pass their phasehood to the head of their complement: v*, affixed to the
root that raises to it, and the deleted complementizer. -/
def Invisible (a : LexicalItem.Token) : Prop := a = vStar ∨ a = cNull

instance : DecidablePred Invisible := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- The positions of the heads `P` holds of. -/
def headPositions (P : LexicalItem.Token → Prop) [DecidablePred P] (t : LinearizedSyntacticObject) :
    Finset TreePath :=
  ((tokenList t.val).filterMap fun x ↦ if P x.2 then some x.1 else none).toFinset

/-- The object built at the phase level of a position. -/
def stageOf (t : LinearizedSyntacticObject) (n : t.val.Positions) : LinearizedSyntacticObject :=
  t.linearizedTermAt (phaseLevel t (headPositions IsPhaseHead t) n)

/-- Labeling at the phase level: an occurrence of `x` is labeled in the object built at its phase
level, and later movement leaves the label in place. -/
def IsLabeledAtPhase (ag : Agreement) (t : LinearizedSyntacticObject) (x : SyntacticObject) :
    Prop :=
  ∃ n, t.termAt n = x ∧ IsLabeled ag (stageOf t n) x

instance (ag : Agreement) (t : LinearizedSyntacticObject) (x : SyntacticObject) :
    Decidable (IsLabeledAtPhase ag t x) :=
  inferInstanceAs (Decidable (∃ _, _))

/-- A link of the chain of `tok` leaves a transferred complement, that of a phase head or, where
the phase heads `I` holds of are invisible, of the head inheriting its phasehood: the PIC. -/
def ViolatesPic (I : LexicalItem.Token → Prop) [DecidablePred I] (t : LinearizedSyntacticObject)
    (tok : LexicalItem.Token) : Prop :=
  LinkLeaves t tok
    (sealed (headPositions IsPhaseHead t) (complementDomain t (headPositions I t)) (Pic1 t))

instance (I : LexicalItem.Token → Prop) [DecidablePred I] (t : LinearizedSyntacticObject)
    (tok : LexicalItem.Token) : Decidable (ViolatesPic I t tok) :=
  inferInstanceAs (Decidable (LinkLeaves _ _ _))

/-- A nominal of the examples, its determiner selecting the nominalizer, which selects the root. -/
def dp (id : ℕ) (d r : String) : LinearizedSyntacticObject :=
  nominal (tok id .D d (sel := [.n])) (tok (id + 1) .n (sel := [.N])) (tok (id + 2) .N r)

/-! ### Categorizers and roots -/

def n₁ := tok 101 .n (sel := [.N])
def the₁ := tok 102 .D "the" (sel := [.n])
def dogRoot := tok 103 .N "dog"

/-- A categorizer labels its merge with a root, in either language. -/
theorem categorizer_root_isLabeled (ag : Agreement) :
    IsLabeled ag (n₁ * dogRoot) (n₁ * dogRoot : LinearizedSyntacticObject) := by
  cases ag <;> decide +kernel

/-- Other head–head merges are unlabeled, even in the sister of v*: a determiner does not
categorize the root. -/
theorem determiner_root_not_isLabeled (ag : Agreement) :
    ¬ IsLabeled ag (vStar * (the₁ * dogRoot)) (the₁ * dogRoot : LinearizedSyntacticObject) := by
  cases ag <;> decide +kernel

/-! ### Subjects of CP: EPP and ECP (2), (2′), (4) -/

def c := tok 104 .C "that" (sel := [.T])
def t := tok 105 .T (sel := [.v])
def think := tok 106 .V "think" (sel := [.C])
def read := tok 107 .V "read" (sel := [.D])
/-- *Tom*. -/
def tom : LinearizedSyntacticObject := dp 108 "" "Tom"
/-- *a book*. -/
def aBook : LinearizedSyntacticObject := dp 111 "a" "book"

/-- `β`: the verb phrase with its external argument *Tom*. -/
def beta : LinearizedSyntacticObject := tom * (vStar * (read * aBook))

/-- T merged with `β`, before the subject raises. -/
def tBeta : LinearizedSyntacticObject := t * beta

/-- `α` of (2): the subject raised over T. -/
def alpha : LinearizedSyntacticObject := tom * (t * beta)

/-- (2): *Tom read a book*, `[δ C [α Tom T [β t v* …]]]`. -/
def clause : LinearizedSyntacticObject := c * alpha

/-- T alone labels its merge with its complement only where agreement is rich. -/
theorem tBeta_isLabeled_iff (ag : Agreement) : IsLabeled ag tBeta tBeta ↔ ag = .rich := by
  cases ag <;> decide +kernel

/-- (2): with the subject in its specifier, `α` is labeled by the φ-features T and the subject
agree in: the EPP is met. -/
theorem ex2 : ∀ ag ∈ agreementOf Examples.ex2.language,
    (Examples.ex2.judgment = .acceptable ↔ IsLabeledAtPhase ag clause alpha) := by
  decide +kernel

def vSmall := tok 114 .v (sel := [.V])
def arrive := tok 115 .V "arrive" (sel := [.D])
/-- *a dog*. -/
def aDog : LinearizedSyntacticObject := dp 116 "a" "dog"

/-- An unaccusative verb phrase, *arrive a dog*, which has no external argument. -/
def vUnacc : LinearizedSyntacticObject := vSmall * (arrive * aDog)

/-- T merged with the unaccusative verb phrase. -/
def tUnacc : LinearizedSyntacticObject := t * vUnacc

/-- The internal argument raised over T. -/
def unaccRaised : LinearizedSyntacticObject := aDog * (t * vUnacc)

/-- Without an external argument, the crucial case of the EPP: T labels its merge with the verb
phrase only where agreement is rich, and the internal argument raised over it agrees with it in
either language. -/
theorem unaccusative_epp (ag : Agreement) :
    (IsLabeled ag tUnacc tUnacc ↔ ag = .rich) ∧ IsLabeled ag unaccRaised unaccRaised := by
  cases ag <;> decide +kernel

/-- The determiner of *who*. -/
def whoD := tok 119 .D "who" (wh := true) (sel := [.n])
/-- *who*, a wh-nominal. -/
def who : LinearizedSyntacticObject := nominal whoD (tok 120 .n (sel := [.N])) (tok 121 .N "who")

/-- `α` of (2′): *who* in the specifier of T. -/
def alphaWho : LinearizedSyntacticObject := who * (t * (who * (vStar * (read * aBook))))

/-- *who* raised from the specifier of T straight out of the clause of *that*. -/
def whoThinkDirect : LinearizedSyntacticObject := who * (think * (c * alphaWho))

/-- (2′): *who do you think that read the book*, *who* moved on through the specifier of C. -/
def whoThink : LinearizedSyntacticObject := who * (think * (who * (c * alphaWho)))

/-- (2′): the complement of C is transferred, so *who* moves on through the specifier of C, and at
the phase level leaves T alone in `α`, which labels it in Italian but not in English: the ECP, and
its absence where agreement is rich. -/
theorem ex2prime :
    ViolatesPic Invisible whoThinkDirect whoD ∧ ¬ ViolatesPic Invisible whoThink whoD ∧
      (∀ ag ∈ agreementOf Examples.ex2prime.language,
        (Examples.ex2prime.judgment = .acceptable ↔ IsLabeledAtPhase ag whoThink alphaWho)) ∧
      IsLabeledAtPhase .rich whoThink alphaWho := by
  decide +kernel

/-- (4): *who do you think read the book*, the complementizer deleted. -/
def whoThinkNoC : LinearizedSyntacticObject := who * (think * (cNull * alphaWho))

/-- (4): the deleted complementizer passes its phasehood to T, whose complement alone is
transferred, so *who* moves on from the specifier of T, where a visible complementizer would seal
it. `α`, labeled at the phase level by the φ-features T and *who* agree in, stays labeled, though at
the last stage T is alone. -/
theorem ex4 : ¬ ViolatesPic Invisible whoThinkNoC whoD ∧
    ViolatesPic (· = vStar) whoThinkNoC whoD ∧ ¬ IsLabeled .weak whoThinkNoC alphaWho ∧
    ∀ ag ∈ agreementOf Examples.ex4.language,
      (Examples.ex4.judgment = .acceptable ↔ IsLabeledAtPhase ag whoThinkNoC alphaWho) := by
  decide +kernel

/-! ### Raising to object (3), (3′) -/

def toInf := tok 122 .T "to" (sel := [.v])
def vInf := tok 123 .v (sel := [.V])
def win := tok 124 .V "win"
def expect := tok 125 .V "expect" (sel := [.T])
/-- *John*. -/
def john : LinearizedSyntacticObject := dp 126 "" "John"

/-- The embedded infinitive *John to win*, its subject raised from the verb phrase. -/
def infinitive : LinearizedSyntacticObject := john * (toInf * (john * (vInf * win)))

/-- v* over the root *expect* merged with the infinitive, before the object raises. -/
def expectInSitu : LinearizedSyntacticObject := vStar * (expect * infinitive)

/-- `α` of (3): the object raised to the specifier of *expect*. -/
def alphaObject : LinearizedSyntacticObject := john * (expect * infinitive)

/-- (3): *they expected John to win*, `[δ v* [α John R [β t …]]]`. -/
def expectRaised : LinearizedSyntacticObject := vStar * alphaObject

/-- (3): the root merged with its complement is unlabeled in either language, since roots are
weak. -/
theorem expect_not_isLabeled (ag : Agreement) :
    ¬ IsLabeled ag expectInSitu (expect * infinitive : LinearizedSyntacticObject) := by
  cases ag <;> decide +kernel

/-- (3): raised to the specifier of the root, the object agrees with it in the φ-features it
inherits from v*, which label `α`: raising to object is forced. -/
theorem ex3 : ∀ ag ∈ agreementOf Examples.ex3.language,
    (Examples.ex3.judgment = .acceptable ↔ IsLabeledAtPhase ag expectRaised alphaObject) := by
  decide +kernel

def doT := tok 136 .T "do" (sel := [.v])
/-- *you*. -/
def you : LinearizedSyntacticObject := dp 137 "" "you"

/-- `α` of (3′), *who* raised to the specifier of *expect*. -/
def alphaWhoObject : LinearizedSyntacticObject :=
  who * (expect * (who * (toInf * (who * (vInf * win)))))

/-- (3′): *who do you expect to win*, *who* moved on from the specifier of *expect*, with the
external argument *you* in the specifier of v*. -/
def whoExpect : LinearizedSyntacticObject := who * (doT * (you * (vStar * alphaWhoObject)))

/-- (3′): v*, invisible once the root raises to it, passes its phasehood to the root, whose
complement alone is transferred, so *who* moves on from the specifier of *expect*, where a visible
v* would seal it. `α`, labeled at the phase level by the φ-features the root and *who* agree in,
stays labeled, though at the last stage the root is alone: the ECP holds in no language. -/
theorem ex3prime : ¬ ViolatesPic Invisible whoExpect whoD ∧
    ViolatesPic (· = cNull) whoExpect whoD ∧ ¬ IsLabeled .weak whoExpect alphaWhoObject ∧
    ∀ ag ∈ agreementOf Examples.ex3prime.language,
      (Examples.ex3prime.judgment = .acceptable ↔
        IsLabeledAtPhase ag whoExpect alphaWhoObject) := by
  decide +kernel

/-! ### Criterial freezing (1) -/

def cQ := tok 129 .C (wh := true) (sel := [.T])
def wonder := tok 130 .V "wonder" (sel := [.C])
def like := tok 131 .V "like" (sel := [.D])
/-- *which dog*. -/
def whichDog : LinearizedSyntacticObject :=
  nominal (tok 132 .D "which" (wh := true) (sel := [.n])) (tok 133 .n (sel := [.N]))
    (tok 134 .N "dog")

/-- *John likes which dog*, the subject raised from the verb phrase. -/
def likes : LinearizedSyntacticObject := john * (t * (john * (vStar * (like * whichDog))))

/-- `α` of (1): *which dog* in its criterial position, the specifier of the interrogative C. -/
def alphaQ : LinearizedSyntacticObject := whichDog * (cQ * likes)

/-- *you wonder which dog John likes*, *which dog* in its criterial position. -/
def wonderInSitu : LinearizedSyntacticObject := wonder * alphaQ

/-- (1): *which dog do you wonder John likes*, *which dog* raised out of its criterial position. -/
def wonderRaised : LinearizedSyntacticObject := whichDog * (wonder * alphaQ)

/-- In its criterial position, *which dog* and the interrogative C agree in the interrogative
feature, which labels `α`, an indirect question; the embedded clause is labeled by φ-features. -/
theorem alphaQ_isLabeledByFeature :
    wonderInSitu.IsLabeledByFeature (Agreed wonderInSitu) alphaQ .Q ∧
      IsLabeledAtPhase .weak wonderInSitu likes := by
  decide +kernel

/-- (1): `α`, the edge of its phase, is labeled at the next, where *which dog* raised out of its
criterial position leaves the interrogative C to label `α` by itself, which the paper reads as a
yes-no question. -/
theorem ex1 : (∀ n, wonderRaised.termAt n = alphaQ → stageOf wonderRaised n = wonderRaised) ∧
    wonderRaised.IsLabeledBy alphaQ cQ ∧
    (Examples.ex1.judgment = .acceptable ↔
      wonderRaised.IsLabeledByFeature (Agreed wonderRaised) alphaQ .Q) := by
  decide +kernel

end Chomsky2015
