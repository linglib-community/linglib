module

public import Linglib.Data.UD.DepRel
public import Linglib.Syntax.DependencyGrammar.Projectivity
public import Linglib.Syntax.DependencyGrammar.Length
public import Linglib.Syntax.DependencyGrammar.Stemma
public import Linglib.Syntax.WordOrder
public import Linglib.Morphology.Word.Basic

/-!
# Gibson (2025): Syntax: A Cognitive Approach

This file formalizes chapter 5 of [gibson-2025], where dependency length minimization is a
constraint on grammars: the head-direction generalization, that a language's head-argument orders
share one direction, which the book draws from the word order correlations of [greenberg-1963] and
[dryer-1992], follows because a disharmonic order stretches the dependencies along a recursive
spine. The measure is the total dependency length of [futrell-mahowald-gibson-2015], illustrated on
the book's (99a) (`totalLength_99a`), and a head-final language reads the same structure in the
mirrored order of its head-argument rules with subjects kept before their verbs (`sov_harmonic`).
The argument is worked through the book's (122) and (123): every regime is one dependency structure
read in a different order (`Graph.linearize`), the harmonic orders are the shortest, and each
mismatch of verb-complement direction with the direction of infinitival, subordinator, adposition,
or relative-clause dependencies costs the lengths the book computes (`totalLength_122`,
`totalLength_123`). The mechanism is an arc to the far end of its own phrase
(`Graph.ncard_yield_le_dist`), which is why the one-word dependents of Table 5.4 need not align
(`single_word_free`), the prediction on which Dryer's branching-direction account parts from a
head-direction one.

## Implementation notes

Arcs follow the book's chapter 3: a subordinator or infinitival marker heads its clause, an
adposition its noun phrase, and a relative clause's verb the clause, with the nearest UD label
on each arc. The book's Tables 5.1 to 5.3, WALS cross-tabulations of verb-object order with
adposition, subordinator, and relative-clause order ([dryer-haspelmath-2013]), are prose here:
raw-count dominance over atlas rows is not a theorem of the theory. The full mirror of (123)
costs the same as the English order (`Graph.totalLength_mirror`); the book's head-final orders
cost more only because they keep subjects before their verbs.

## Errata

* The book credits the head-direction generalization to [dryer-1992] as well as to Greenberg, but
  Dryer states the head-dependent account only to argue against it, and proposes in its place
  that the correlated pairs are a nonphrasal and a phrasal category, which is where
  `single_word_free` points.

## References

* [gibson-2025]
* [futrell-mahowald-gibson-2015]
* [greenberg-1963]
* [dryer-1992]
* [dryer-haspelmath-2013]
* [temperley-2007]
-/

@[expose] public section

namespace Gibson2025

open DependencyGrammar Morphology
open Stemma (node leaf)

variable {n : ℕ}

/-- An order is head-first or head-final, section 5.2, when every head-argument arc, that is
every arc but a subject's, takes that direction. -/
def Harmonic (g : Graph UD.DepRel n) (d : HeadDirection) : Prop :=
  ∀ v w, g.Adj v w → g.label v w ≠ some .nsubj → HeadDirection.ofLT v w = d

instance (g : Graph UD.DepRel n) (d : HeadDirection) : Decidable (Harmonic g d) :=
  inferInstanceAs (Decidable (∀ _ _, _))

/-- An order that is neither head-first nor head-final. -/
def Disharmonic (g : Graph UD.DepRel n) : Prop := ∀ d, ¬ Harmonic g d

instance (g : Graph UD.DepRel n) : Decidable (Disharmonic g) :=
  inferInstanceAs (Decidable (∀ _, ¬ _))

/-! ### Section 5.1: the measure, on (99a) -/

/-- (99a) *Mary threw away the important documents that she brought home yesterday*, whose
total dependency length the book computes as eighteen. -/
def ex99a : Graph UD.DepRel 11 := Stemma.toGraph <|
  node (.mk' "threw" .VERB)
    [(.nsubj, leaf (.mk' "Mary" .PROPN))]
    [(.advmod, leaf (.mk' "away" .ADV)),
     (.obj, node (.mk' "documents" .NOUN)
       [(.det, leaf (.mk' "the" .DET)), (.amod, leaf (.mk' "important" .ADJ))]
       [(.acl, node (.mk' "brought" .VERB)
          [(.mark, leaf (.mk' "that" .PRON)), (.nsubj, leaf (.mk' "she" .PRON))]
          [(.advmod, leaf (.mk' "home" .ADV)), (.advmod, leaf (.mk' "yesterday" .ADV))])])]

theorem totalLength_99a : ex99a.totalLength = 18 := by decide

/-- (99b), the particle after the long object, where the arc to *away* crosses the eight words of
the object. -/
def ex99b : Graph UD.DepRel 11 := ex99a.linearize [0, 1, 3, 4, 5, 6, 7, 8, 9, 10, 2] (by decide)

theorem totalLength_99b : ex99b.totalLength = 25 ∧ ex99a.totalLength < ex99b.totalLength := by
  decide

/-! ### Section 5.2: the mirror rules of a verb-final language, (119) to (121) -/

/-- (119a) *Lana ate pizza*. -/
def svo119 : Graph UD.DepRel 3 := Stemma.toGraph <|
  node (.mk' "ate" .VERB)
    [(.nsubj, leaf (.mk' "Lana" .PROPN))]
    [(.obj, leaf (.mk' "pizza" .NOUN))]

/-- (119b) *Lana pizza ate*. -/
def sov119 : Graph UD.DepRel 3 := svo119.linearize [0, 2, 1] (by decide)

/-- (120a) *Lana gave pizza to Francine*. -/
def svo120 : Graph UD.DepRel 5 := Stemma.toGraph <|
  node (.mk' "gave" .VERB)
    [(.nsubj, leaf (.mk' "Lana" .PROPN))]
    [(.obj, leaf (.mk' "pizza" .NOUN)),
     (.obl, node (.mk' "to" .ADP) [] [(.obj, leaf (.mk' "Francine" .PROPN))])]

/-- (120b) *Lana Francine to pizza gave*. -/
def sov120 : Graph UD.DepRel 5 := svo120.linearize [0, 4, 3, 2, 1] (by decide)

/-- (121a) *Alfred said that Lana gave pizza to Francine*. -/
def svo121 : Graph UD.DepRel 8 := Stemma.toGraph <|
  node (.mk' "said" .VERB)
    [(.nsubj, leaf (.mk' "Alfred" .PROPN))]
    [(.ccomp, node (.mk' "that" .SCONJ)
       []
       [(.ccomp, node (.mk' "gave" .VERB)
          [(.nsubj, leaf (.mk' "Lana" .PROPN))]
          [(.obj, leaf (.mk' "pizza" .NOUN)),
           (.obl, node (.mk' "to" .ADP) [] [(.obj, leaf (.mk' "Francine" .PROPN))])])])]

/-- (121b) *Alfred Lana Francine to pizza gave that said*, where each clause keeps its subject first
and mirrors the rest. -/
def sov121 : Graph UD.DepRel 8 := svo121.linearize [0, 3, 7, 6, 5, 4, 2, 1] (by decide)

theorem sov_harmonic :
    Harmonic svo119 .headInitial ∧ Harmonic sov119 .headFinal ∧
      Harmonic svo120 .headInitial ∧ Harmonic sov120 .headFinal ∧
      Harmonic svo121 .headInitial ∧ Harmonic sov121 .headFinal := by
  decide

/-! ### Section 5.3.1: verb-object and verb-complement direction, (122) -/

/-- (122) *Alfred wanted to eat bananas from Hawaii*, head-first: every arc is adjacent. -/
def hi122 : Graph UD.DepRel 7 := Stemma.toGraph <|
  node (.mk' "wanted" .VERB)
    [(.nsubj, leaf (.mk' "Alfred" .PROPN))]
    [(.xcomp, node (.mk' "to" .PART)
       []
       [(.xcomp, node (.mk' "eat" .VERB)
          []
          [(.obj, node (.mk' "bananas" .NOUN)
             []
             [(.nmod, node (.mk' "from" .ADP) [] [(.obj, leaf (.mk' "Hawaii" .PROPN))])])])])]

/-- The head-final order with the subject next to its verb: *Hawaii from bananas eat to Alfred
wanted*. -/
def hf122 : Graph UD.DepRel 7 := hi122.linearize [6, 5, 4, 3, 2, 0, 1] (by decide)

/-- Verb-object order for *eat* but complement-verb order for *wanted*: *Alfred to eat bananas
from Hawaii wanted*. -/
def voCompV122 : Graph UD.DepRel 7 := hi122.linearize [0, 2, 3, 4, 5, 6, 1] (by decide)

/-- Object-verb order for *eat* but verb-complement order for *wanted*: *Alfred wanted to
bananas from Hawaii eat*. -/
def ovVComp122 : Graph UD.DepRel 7 := hi122.linearize [0, 1, 2, 4, 5, 6, 3] (by decide)

theorem totalLength_122 :
    hi122.totalLength = 6 ∧ hf122.totalLength = 7 ∧
      voCompV122.totalLength = 15 ∧ ovVComp122.totalLength = 11 := by
  decide

theorem harmonic_122 :
    Harmonic hi122 .headInitial ∧ Harmonic hf122 .headFinal ∧
      Disharmonic voCompV122 ∧ Disharmonic ovVComp122 := by
  decide

/-! ### Sections 5.3.2 to 5.3.4: subordinators, adpositions, and relative clauses, (123) -/

/-- (123) *Alfred said that Lana gave pizza to monkeys who wanted bananas* in English order. -/
def en123 : Graph UD.DepRel 11 := Stemma.toGraph <|
  node (.mk' "said" .VERB)
    [(.nsubj, leaf (.mk' "Alfred" .PROPN))]
    [(.ccomp, node (.mk' "that" .SCONJ)
       []
       [(.ccomp, node (.mk' "gave" .VERB)
          [(.nsubj, leaf (.mk' "Lana" .PROPN))]
          [(.obj, leaf (.mk' "pizza" .NOUN)),
           (.obl, node (.mk' "to" .ADP)
             []
             [(.obj, node (.mk' "monkeys" .NOUN)
                []
                [(.acl, node (.mk' "wanted" .VERB)
                   [(.nsubj, leaf (.mk' "who" .PRON))]
                   [(.obj, leaf (.mk' "bananas" .NOUN))])])])])])]

/-- The head-final order with subjects first: *Alfred Lana who bananas wanted monkeys to pizza
gave that said*. -/
def hfSubjFirst123 : Graph UD.DepRel 11 :=
  en123.linearize [0, 3, 8, 10, 9, 7, 6, 5, 4, 2, 1] (by decide)

/-- The head-final order with subjects next to their verbs: *who bananas wanted monkeys to pizza
Lana gave that Alfred said*. -/
def hf123 : Graph UD.DepRel 11 := en123.linearize [8, 10, 9, 7, 6, 5, 3, 4, 2, 0, 1] (by decide)

/-- Verb-initial but subordinator-final: *that* follows the clause it heads. -/
def voSubFinal123 : Graph UD.DepRel 11 :=
  en123.linearize [0, 1, 3, 4, 5, 6, 7, 8, 9, 10, 2] (by decide)

/-- Verb-final but subordinator-initial: *that* precedes the clause it heads. -/
def ovSubInitial123 : Graph UD.DepRel 11 :=
  en123.linearize [2, 8, 10, 9, 7, 6, 5, 3, 4, 0, 1] (by decide)

/-- Verb-initial but postpositional: *to* follows its noun phrase. -/
def voPost123 : Graph UD.DepRel 11 :=
  en123.linearize [0, 1, 2, 3, 4, 5, 7, 8, 9, 10, 6] (by decide)

/-- Verb-final but prepositional: *to* precedes its noun phrase. -/
def ovPre123 : Graph UD.DepRel 11 :=
  en123.linearize [6, 8, 10, 9, 7, 5, 3, 4, 2, 0, 1] (by decide)

/-- Verb-initial but with the relative clause before its noun. -/
def voRelN123 : Graph UD.DepRel 11 :=
  en123.linearize [0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 7] (by decide)

/-- Verb-final but with the relative clause after its noun. -/
def ovNRel123 : Graph UD.DepRel 11 :=
  en123.linearize [7, 8, 10, 9, 6, 5, 3, 4, 2, 0, 1] (by decide)

theorem totalLength_123 :
    en123.totalLength = 13 ∧ hfSubjFirst123.totalLength = 27 ∧ hf123.totalLength = 15 ∧
      voSubFinal123.totalLength = 26 ∧ ovSubInitial123.totalLength = 30 ∧
      voPost123.totalLength = 20 ∧ ovPre123.totalLength = 22 ∧
      voRelN123.totalLength = 16 ∧ ovNRel123.totalLength = 20 := by
  decide

theorem harmonic_123 :
    Harmonic en123 .headInitial ∧ Harmonic hfSubjFirst123 .headFinal ∧
      Harmonic hf123 .headFinal ∧
      Disharmonic voSubFinal123 ∧ Disharmonic ovSubInitial123 ∧ Disharmonic voPost123 ∧
        Disharmonic ovPre123 ∧ Disharmonic voRelN123 ∧ Disharmonic ovNRel123 := by
  decide

theorem totalLength_mirror_123 : en123.mirror.totalLength = 13 :=
  en123.totalLength_mirror.trans totalLength_123.1

theorem subordinator_final_stretches :
    (voSubFinal123.yield 10).ncard ≤ Nat.dist (1 : Fin 11) 10 :=
  voSubFinal123.ncard_yield_le_dist (by decide)
    (fun x hx ↦ Set.mem_uIcc.mpr (by revert x hx; decide))

/-! ### Section 5.3.5: one-word dependents, Table 5.4 -/

/-- *very tall*, an intensifier before its adjective. -/
def intensifierFirst : Graph UD.DepRel 2 := Stemma.toGraph <|
  node (.mk' "tall" .ADJ) [(.advmod, leaf (.mk' "very" .ADV))] []

/-- A one-word dependent costs the same on either side of its head, so Table 5.4's single-word
orders need not align with verb-object order. -/
theorem single_word_free : intensifierFirst.mirror.totalLength = intensifierFirst.totalLength :=
  intensifierFirst.totalLength_mirror

end Gibson2025
