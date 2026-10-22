module

public import Studies.Chomsky2013
public import Linglib.Data.Examples.Chomsky2015

/-!
# Chomsky (2015): Problems of projection: Extensions

[chomsky-2015] takes T, like a root, to be too weak to label in a language with weak agreement like
English, while Italian T, with rich agreement, labels by itself. T merged with its complement is
then labeled only by agreement with a subject in its specifier, the EPP, and a subject moved on
leaves T alone, unable to label, the ECP. A root merged with the object labels only once the object
raises to its specifier and agrees with the φ-features the root inherits from v*, raising to
object. A wh-phrase raised out of its criterial position leaves the interrogative C to label the
clause by itself, as a yes-no question.

## Implementation notes

* Labeling reads the structure at one stage. The paper keeps a label assigned in a lower phase when
  the subject or object moves on, phase-level memory, so that (3′) and (4) are labeled; at one stage
  they are not, and `ex3prime_ex4_unlabeled` records the misprediction.
* Weakness is fixed by the richness of agreement the paper attributes to a language.
* A root inherits φ-features when minimal search finds it in the sister of v*.

## TODO

* Phase-level label memory, which derives (3′), (4) and the halting problem (6).
* The amalgam a root forms by raising to v*, with v* affixed and invisible, which needs head
  movement; and the crash at the conceptual-intentional interface of (1) read as a yes-no question.

## References

* [chomsky-2015]
* [chomsky-2013]
-/

@[expose] public section

namespace Chomsky2015

open Minimalist Minimalist.LinearizedSyntacticObject
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

def vStar := tok 100 .v "v*"

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

/-! ### Categorizers and roots -/

def n₁ := tok 101 .n
def the₁ := tok 102 .D "the"
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

def c := tok 104 .C "that"
def t := tok 105 .T
def think := tok 106 .V "think"
def read := tok 107 .V "read"
/-- *Tom*. -/
def tom : LinearizedSyntacticObject := nominal (tok 108 .D) (tok 109 .n) (tok 110 .N "Tom")
/-- *a book*. -/
def aBook : LinearizedSyntacticObject := nominal (tok 111 .D "a") (tok 112 .n) (tok 113 .N "book")

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
    (Examples.ex2.judgment = .acceptable ↔ IsLabeled ag clause alpha) := by
  decide +kernel

def vSmall := tok 114 .v
def arrive := tok 115 .V "arrive"
/-- *a dog*. -/
def aDog : LinearizedSyntacticObject := nominal (tok 116 .D "a") (tok 117 .n) (tok 118 .N "dog")

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

/-- *who*, a wh-nominal. -/
def who : LinearizedSyntacticObject := nominal (tok 119 .D "who" (wh := true)) (tok 120 .n)
  (tok 121 .N "who")

/-- `α` of (2′): *who* in the specifier of T. -/
def alphaWho : LinearizedSyntacticObject := who * (t * (who * (vStar * (read * aBook))))

/-- (2′): *who do you think that read the book*, *who* moved on from the specifier of T. -/
def whoThink : LinearizedSyntacticObject := who * (think * (c * alphaWho))

/-- (4): *who do you think read the book*, the complementizer deleted. -/
def whoThinkNoC : LinearizedSyntacticObject := who * (think * alphaWho)

/-- (2′): *who* moved on leaves T alone in `α`, which labels it in Italian but not in English: the
ECP, and its absence where agreement is rich. -/
theorem ex2prime :
    (∀ ag ∈ agreementOf Examples.ex2prime.language,
      (Examples.ex2prime.judgment = .acceptable ↔ IsLabeled ag whoThink alphaWho)) ∧
      IsLabeled .rich whoThink alphaWho := by
  decide +kernel

/-! ### Raising to object (3), (3′) -/

def toInf := tok 122 .T "to"
def vInf := tok 123 .v
def win := tok 124 .V "win"
def expect := tok 125 .V "expect"
/-- *John*. -/
def john : LinearizedSyntacticObject := nominal (tok 126 .D) (tok 127 .n) (tok 128 .N "John")

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
    (Examples.ex3.judgment = .acceptable ↔ IsLabeled ag expectRaised alphaObject) := by
  decide +kernel

/-- `α` of (3′), *who* raised to the specifier of *expect*. -/
def alphaWhoObject : LinearizedSyntacticObject :=
  who * (expect * (who * (toInf * (who * (vInf * win)))))

/-- (3′): *who do you expect to win*, *who* moved on from the specifier of *expect*. -/
def whoExpect : LinearizedSyntacticObject := who * (vStar * alphaWhoObject)

/-- (3′) and (4) are acceptable, but at one stage the moved object leaves the weak root, and the
moved subject leaves weak T, alone and unlabeled: the paper keeps the label they received in the
lower phase. -/
theorem ex3prime_ex4_unlabeled :
    Examples.ex3prime.judgment = .acceptable ∧ ¬ IsLabeled .weak whoExpect alphaWhoObject ∧
      Examples.ex4.judgment = .acceptable ∧ ¬ IsLabeled .weak whoThinkNoC alphaWho := by
  decide +kernel

/-! ### Criterial freezing (1) -/

def cQ := tok 129 .C (wh := true)
def wonder := tok 130 .V "wonder"
def like := tok 131 .V "like"
/-- *which dog*. -/
def whichDog : LinearizedSyntacticObject :=
  nominal (tok 132 .D "which" (wh := true)) (tok 133 .n) (tok 134 .N "dog")

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
      IsLabeled .weak wonderInSitu likes := by
  decide +kernel

/-- (1): raised out of its criterial position, *which dog* leaves the interrogative C to label `α`
by itself, which the paper reads as a yes-no question. -/
theorem ex1 : wonderRaised.IsLabeledBy alphaQ cQ ∧
    (Examples.ex1.judgment = .acceptable ↔
      wonderRaised.IsLabeledByFeature (Agreed wonderRaised) alphaQ .Q) := by
  decide +kernel

end Chomsky2015
