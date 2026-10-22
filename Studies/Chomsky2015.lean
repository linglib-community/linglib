module

public import Studies.Chomsky2013

/-!
# Chomsky (2015): Problems of projection: Extensions

[chomsky-2015] adds weak heads to the labeling algorithm of Chomsky 2013: minimal search finds them,
but they cannot label alone. Roots are weak everywhere, so a categorizer labels its merge with a
root, and a root merged with the object labels only once the object raises to its specifier and
agrees with it, raising to object. T is weak in a language with weak agreement like English, so T
merged with its complement is labeled only by agreement with a subject in its specifier: the EPP.
A subject moved on from there leaves T alone, which cannot label, the ECP, while Italian T, with
rich agreement, labels by itself. Criterial freezing follows from copy invisibility: a wh-phrase
raised out of its criterial position leaves the interrogative C to label the clause by itself, as
a yes-no question.

## Implementation notes

* Weakness is a property of heads that a language fixes: roots are weak everywhere, T is weak in
  English and strong in Italian.
* Roots are the tokens of `roots`; the category inventory gives every token a category.
* A root in the domain of v* inherits its φ-features and probes for a determiner as T does.
* Labeling reads the structure at one stage. That-deletion, under which a label assigned in the
  embedded phase is kept when the subject moves on, and the amalgam a root forms by raising to v*,
  with v* affixed and invisible, need the timing of labeling and head movement.

## References

* [chomsky-2015]
* [chomsky-2013]
-/

@[expose] public section

namespace Chomsky2015

open Minimalist Minimalist.LinearizedSyntacticObject
open Chomsky2013 (tok nominal Feature probe)

/-! ### Weak heads and agreement -/

/-- The languages compared. -/
inductive Language
  | english | italian
  deriving DecidableEq

def read := tok 100 .V "read"
def expect := tok 101 .V "expect"
def win := tok 102 .V "win"
def like := tok 103 .V "like"
def tomRoot := tok 104 .N "Tom"
def bookRoot := tok 105 .N "book"
def johnRoot := tok 106 .N "John"
def whoRoot := tok 107 .N "who"
def dogRoot := tok 108 .N "dog"

/-- The roots of the examples, unspecified as to category in the paper. -/
def roots : List LexicalItem.Token :=
  [read, expect, win, like, tomRoot, bookRoot, johnRoot, whoRoot, dogRoot]

/-- A head is weak in a language: a root, or T where agreement is weak. -/
def Weak (l : Language) (h : LexicalItem.Token) : Prop :=
  h ∈ roots ∨ (l = .english ∧ h.item.cat = .T)

instance (l : Language) : DecidablePred (Weak l) := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- The categorizers, the heads that determine the category of a root. -/
def IsCategorizer (h : LexicalItem.Token) : Prop := h.item.cat = .n ∨ h.item.cat = .v

instance : DecidablePred IsCategorizer := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

def vStar := tok 109 .v "v*"

/-- A root in the domain of v*, which inherits its φ-features. -/
def InheritsPhi (t : LinearizedSyntacticObject) (r : LexicalItem.Token) : Prop :=
  r ∈ roots ∧ ∃ a b : t.val.Positions,
    t.termAt a = ↑vStar ∧ t.termAt b = ↑r ∧ t.val.CCommands a b

instance (t : LinearizedSyntacticObject) : DecidablePred (InheritsPhi t) :=
  fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- The heads bearing the probe for a feature: those of Chomsky 2013, and the roots that inherit
φ-features from v*. -/
def Probes (t : LinearizedSyntacticObject) : Feature → LexicalItem.Token → Prop
  | .Q, h => Chomsky2013.Probes .Q h
  | .phi, h => Chomsky2013.Probes .phi h ∨ InheritsPhi t h

instance (t : LinearizedSyntacticObject) : ∀ f, DecidablePred (Probes t f)
  | .Q => fun _ ↦ inferInstanceAs (Decidable (Chomsky2013.Probes .Q _))
  | .phi => fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- Two heads agree in a feature when one bears its probe and the probe finds the other. -/
def Agreed (t : LinearizedSyntacticObject) (f : Feature) (h h' : LexicalItem.Token) : Prop :=
  (Probes t f h ∧ ↑h' ∈ t.goals (probe t f) ↑h) ∨ (Probes t f h' ∧ ↑h ∈ t.goals (probe t f) ↑h')

instance (t : LinearizedSyntacticObject) (f : Feature) : DecidableRel (Agreed t f) :=
  fun _ _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- `x` is labeled in `t` in language `l`: by the one head minimal search finds, if that head is
strong; by a categorizer merged with a root; or by a feature the heads found agree in. -/
def IsLabeled (l : Language) (t : LinearizedSyntacticObject) (x : SyntacticObject) : Prop :=
  (∃ h ∈ t.labels x, t.labels x = {h} ∧ ¬ Weak l h) ∨
    (∃ k ∈ t.labels x, ∃ r ∈ t.labels x, IsCategorizer k ∧ r ∈ roots ∧
      x = ((k : LinearizedSyntacticObject) * r : LinearizedSyntacticObject)) ∨
    ∃ f, t.IsLabeledByFeature (Agreed t) x f

instance (l : Language) (t : LinearizedSyntacticObject) (x : SyntacticObject) :
    Decidable (IsLabeled l t x) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _))

/-! ### Categorizers and roots -/

def n₁ := tok 110 .n
def the₁ := tok 111 .D "the"

/-- A categorizer labels its merge with a root, in every language. -/
theorem categorizer_root_isLabeled (l : Language) :
    IsLabeled l (n₁ * dogRoot) (n₁ * dogRoot : LinearizedSyntacticObject) := by
  cases l <;> decide +kernel

/-- Other head–head merges are unlabeled: minimal search finds both heads, and a determiner does
not categorize the root. -/
theorem determiner_root_not_isLabeled (l : Language) :
    ¬ IsLabeled l (the₁ * dogRoot) (the₁ * dogRoot : LinearizedSyntacticObject) := by
  cases l <;> decide +kernel

/-! ### Subjects of CP: EPP and ECP (2), (2′) -/

def c := tok 112 .C "that"
def t := tok 113 .T
def think := tok 114 .V "think"
/-- *Tom*. -/
def tom : LinearizedSyntacticObject := nominal (tok 115 .D) (tok 116 .n) tomRoot
/-- *a book*. -/
def aBook : LinearizedSyntacticObject := nominal (tok 117 .D "a") (tok 118 .n) bookRoot

/-- `β`: the verb phrase with its external argument *Tom*. -/
def beta : LinearizedSyntacticObject := tom * (vStar * (read * aBook))

/-- T merged with `β`, before the subject raises. -/
def tBeta : LinearizedSyntacticObject := t * beta

/-- (2): *Tom read a book*, `[δ C [α Tom T [β t v* …]]]`. -/
def clause : LinearizedSyntacticObject := c * (tom * (t * beta))

/-- (2): T alone labels its merge with `β` in Italian but not in English, where it is weak. -/
theorem tBeta_isLabeled_iff (l : Language) :
    IsLabeled l tBeta tBeta ↔ l = .italian := by
  cases l <;> decide +kernel

/-- (2): with the subject in its specifier, `α` is labeled by the φ-features T and the subject agree
in, in either language: the EPP is met. -/
theorem alpha_isLabeled (l : Language) :
    IsLabeled l clause (tom * (t * beta) : LinearizedSyntacticObject) := by
  cases l <;> decide +kernel

/-- *who*, a wh-nominal. -/
def who : LinearizedSyntacticObject := nominal (tok 119 .D "who" (wh := true)) (tok 120 .n) whoRoot

/-- `β` with *who* as its external argument. -/
def betaWho : LinearizedSyntacticObject := who * (vStar * (read * aBook))

/-- `α` of (2′): *who* in the specifier of T. -/
def alphaWho : LinearizedSyntacticObject := who * (t * betaWho)

/-- (2′): *who do you think that read the book*, *who* moved on from the specifier of T. -/
def whoThink : LinearizedSyntacticObject := who * (think * (c * alphaWho))

/-- (2′): *who* moved on leaves T alone in `α`, which labels it in Italian but not in English: the
ECP, and its absence in a null subject language. -/
theorem alphaWho_isLabeled_iff (l : Language) :
    IsLabeled l whoThink alphaWho ↔ l = .italian := by
  cases l <;> decide +kernel

/-! ### Raising to object (3) -/

def toInf := tok 121 .T "to"
/-- *John*. -/
def john : LinearizedSyntacticObject := nominal (tok 122 .D) (tok 123 .n) johnRoot

/-- The embedded infinitive *John to win*. -/
def infinitive : LinearizedSyntacticObject := john * (toInf * win)

/-- v* over the root *expect* merged with the infinitive, before the object raises. -/
def expectInSitu : LinearizedSyntacticObject := vStar * (expect * infinitive)

/-- (3): *they expected John to win*, `[δ v* [α John R [β t …]]]`, the object raised. -/
def expectRaised : LinearizedSyntacticObject := vStar * (john * (expect * infinitive))

/-- (3): the root merged with its complement is unlabeled in either language, since roots are
weak. -/
theorem expect_not_isLabeled (l : Language) :
    ¬ IsLabeled l expectInSitu (expect * infinitive : LinearizedSyntacticObject) := by
  cases l <;> decide +kernel

/-- (3): raised to the specifier of the root, the object agrees with it in the φ-features it
inherits from v*, which label `α`: raising to object is forced, in either language. -/
theorem alphaObject_isLabeled (l : Language) :
    IsLabeled l expectRaised (john * (expect * infinitive) : LinearizedSyntacticObject) := by
  cases l <;> decide +kernel

/-! ### Criterial freezing (1) -/

def cQ := tok 124 .C (wh := true)
def wonder := tok 125 .V "wonder"
/-- *which dog*. -/
def whichDog : LinearizedSyntacticObject :=
  nominal (tok 126 .D "which" (wh := true)) (tok 127 .n) dogRoot
/-- *John likes which dog*. -/
def likes : LinearizedSyntacticObject := john * (t * (like * whichDog))

/-- `α` of (1): *which dog* in its criterial position, the specifier of the interrogative C. -/
def alphaQ : LinearizedSyntacticObject := whichDog * (cQ * likes)

/-- *you wonder which dog John likes*, *which dog* in its criterial position. -/
def wonderInSitu : LinearizedSyntacticObject := wonder * alphaQ

/-- (1): *which dog do you wonder John likes*, *which dog* raised out of its criterial position. -/
def wonderRaised : LinearizedSyntacticObject := whichDog * (wonder * alphaQ)

/-- In its criterial position, *which dog* and the interrogative C agree in the interrogative
feature, which labels `α`, an indirect question. -/
theorem alphaQ_isLabeledByFeature :
    wonderInSitu.IsLabeledByFeature (Agreed wonderInSitu) alphaQ .Q := by
  decide +kernel

/-- (1): raised out of its criterial position, *which dog* leaves the interrogative C to label `α`
by itself, as a yes-no question: criterial freezing. -/
theorem alphaQ_isLabeledBy_of_raising : wonderRaised.IsLabeledBy alphaQ cQ := by
  decide +kernel

end Chomsky2015
