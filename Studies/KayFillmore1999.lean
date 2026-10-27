module

public import Linglib.Syntax.ConstructionGrammar.Licensing

/-!
# Kay and Fillmore (1999): The What's X Doing Y? Construction

This file formalizes the construction of [kay-fillmore-1999], *What's X doing Y?*, whose
interrogative form conventionally conveys that someone judges the scene `Y(X)` incongruous
(their gloss (39)), a meaning the paper argues is neither a conversational implicature of an
innocent question (Section 2.2) nor a proposition that negation could apply to
(Section 4.6). The construction is `wxdyConstruction`, the flat rendering of the paper's
Figure 12: BE and *doing* are fixed heads, *what* is a fixed and left-isolated object that binds
the reference of nothing, *doing* and `Y` share the scene judged incongruous, and *doing* may
not be negated, a stipulation the paper reports being unable to deduce. `X` is not unified with
`Y`: coinstantiation, twice, unifies it with the subject requirements of *doing* and of `Y`, so
that it becomes the subject argument of the predication `Y(X)` (`wxdy_coinstantiation`).

The grammatical evidence for the construction in Section 2.3 is derived by the licensing
recognizer over the paper's minimal pairs: the canonical (3a) and the stative (14a) are
licensed, while the bare-stem *do* of (12a), *doing* as complement of *keep* in (13a),
*what else* in (15f), and the negated *doing* of (17b) are not, negation inside `Y` in (17c)
being fine. The coinstantiation construction of Figure 13 is recorded as a fully abstract form
with one unification index.

## Implementation notes

The paper's semantics, the incongruity-judgment frame of Figure 12 with a contextually
anchored judge, is not represented beyond the construction's pragmatic point; its inheritance
from the left-isolation, subject–auxiliary inversion and wh-interrogative constructions of the
paper's unification grammar is recorded in prose only.

## References

* [kay-fillmore-1999]
* [fillmore-kay-oconnor-1988]
-/

@[expose] public section

namespace KayFillmore1999

open ConstructionGrammar

/-! ### The construction (Figure 12) -/

/-- The WXDY construction, the flat rendering of Figure 12. BE governs the complement *doing*,
which cannot be negated (Section 4.6) and governs the object WXDY-*what*, left-isolated and not
an operator binding the reference of anything, and the complement `Y`, a predicate phrase of any
category. The semantics of *doing* and of `Y` bear #1, the scene judged incongruous, and the
subject requirement of `Y` bears #2, the argument of its frame. `X`, the subject of BE, bears
#2 because coinstantiation unifies it with the subject requirements of *doing* and of `Y`
(Section 4.2, Figure 13). -/
def wxdyConstruction : Construction Unit :=
  { form :=
      [ { filler := .semantic "referential", gf := some .subj, refIdx := some 2 }
      , { filler := .headed "be" .AUX, isHead := true }
      , { filler := .headed "doing" .VERB, gf := some .comp, refIdx := some 1, subjIdx := some 2
        , constraints := [.negMinus] }
      , { filler := .fixed "what", gf := some .obj, constraints := [.locMinus, .refEmpty] }
      , { filler := .phrasal, gf := some .comp, refIdx := some 1, subjIdx := some 2 } ]
  , meaning := ()
  , pragmaticPoint := true }

-- Figure 12
theorem wxdy_refGroupCount : refGroupCount wxdyConstruction.form = 2 := by decide

/-- In WXDY the first constituent `X` bears the index of the subject requirement of the last, `Y`,
not that of `Y` itself (Section 4.2). -/
theorem wxdy_coinstantiation :
    wxdyConstruction.form.head?.bind (·.refIdx) = wxdyConstruction.form.getLast?.bind (·.subjIdx) ∧
      wxdyConstruction.form.head?.bind (·.refIdx) ≠
        wxdyConstruction.form.getLast?.bind (·.refIdx) := by
  decide

theorem wxdy_formal_idiom : wxdyConstruction.IsFormalIdiom := by decide

theorem wxdy_partially_open : wxdyConstruction.specificity = .partiallyOpen := rfl

/-! ### The grammatical evidence (Section 2.3)

The paper's minimal pairs, matched against the form: each is a sequence of daughter trees in the
slot order `X`, BE, *doing*, *what*, `Y`, with lemma-level words tagged for part of speech. -/

open PhraseStructure (Tree)
open Morphology (Word)

/-- *not*, a particle of negative polarity. -/
def negator : Word := { form := "not", cat := .PART, features := .of (polarity := some .Neg) }

/-- (3a) *What's this scratch doing on the table?* -/
def scratchTokens : List (Tree Unit Word) :=
  [ .leaf (.mk' "scratch" .NOUN),
    .node () [.leaf (.mk' "be" .AUX)],
    .node () [.leaf (.mk' "doing" .VERB)],
    .leaf (.mk' "what" .PRON),
    .node () [.leaf (.mk' "on" .ADP), .leaf (.mk' "table" .NOUN)] ]

/-- (14a) *What's he doing knowing the answer?*, a stative complement. -/
def stativeTokens : List (Tree Unit Word) :=
  [ .leaf (.mk' "he" .PRON),
    .node () [.leaf (.mk' "be" .AUX)],
    .node () [.leaf (.mk' "doing" .VERB)],
    .leaf (.mk' "what" .PRON),
    .node () [.leaf (.mk' "knowing" .VERB), .leaf (.mk' "answer" .NOUN)] ]

/-- (12a) *What does this scratch do on the table?*, with bare-stem *do*. -/
def bareStemTokens : List (Tree Unit Word) :=
  [ .leaf (.mk' "scratch" .NOUN),
    .node () [.leaf (.mk' "do" .AUX)],
    .node () [.leaf (.mk' "do" .VERB)],
    .leaf (.mk' "what" .PRON),
    .node () [.leaf (.mk' "on" .ADP), .leaf (.mk' "table" .NOUN)] ]

/-- (13a) *What did he keep doing in the tool shed?*, *doing* as complement of *keep* rather
than of copular BE: a fine sentence, but not an instance of the construction. -/
def nonCopulaTokens : List (Tree Unit Word) :=
  [ .leaf (.mk' "he" .PRON),
    .node () [.leaf (.mk' "keep" .VERB)],
    .node () [.leaf (.mk' "doing" .VERB)],
    .leaf (.mk' "what" .PRON),
    .node () [.leaf (.mk' "in" .ADP), .leaf (.mk' "shed" .NOUN)] ]

/-- (15f) *What else are you doing eating cold pizza?*, with *else* on WXDY-*what*. -/
def whatElseTokens : List (Tree Unit Word) :=
  [ .leaf (.mk' "you" .PRON),
    .node () [.leaf (.mk' "be" .AUX)],
    .node () [.leaf (.mk' "doing" .VERB)],
    .node () [.leaf (.mk' "what" .PRON), .leaf (.mk' "else" .ADV)],
    .node () [.leaf (.mk' "eating" .VERB), .leaf (.mk' "pizza" .NOUN)] ]

/-- (17b) *What are my brushes not doing soaking in water?*, with negated *doing*. -/
def negatedDoingTokens : List (Tree Unit Word) :=
  [ .leaf (.mk' "brushes" .NOUN),
    .node () [.leaf (.mk' "be" .AUX)],
    .node () [.leaf negator, .leaf (.mk' "doing" .VERB)],
    .leaf (.mk' "what" .PRON),
    .node () [.leaf (.mk' "soaking" .VERB), .leaf (.mk' "water" .NOUN)] ]

/-- (17c) *What are my brushes doing not soaking in water?*, negation inside `Y`. -/
def negatedComplementTokens : List (Tree Unit Word) :=
  [ .leaf (.mk' "brushes" .NOUN),
    .node () [.leaf (.mk' "be" .AUX)],
    .node () [.leaf (.mk' "doing" .VERB)],
    .leaf (.mk' "what" .PRON),
    .node () [.leaf negator, .leaf (.mk' "soaking" .VERB), .leaf (.mk' "water" .NOUN)] ]

-- (3a), (14a)
theorem wxdy_matches_canonical :
    FormMatches wxdyConstruction.form scratchTokens ∧
      FormMatches wxdyConstruction.form stativeTokens := by
  decide

-- (12a)
theorem wxdy_rejects_bare_stem :
    ¬ FormMatches wxdyConstruction.form bareStemTokens := by
  decide

-- (13a)
theorem wxdy_rejects_non_copula :
    ¬ FormMatches wxdyConstruction.form nonCopulaTokens := by
  decide

-- (15f)
theorem wxdy_rejects_what_else :
    ¬ FormMatches wxdyConstruction.form whatElseTokens := by
  decide

-- (17b), (17c)
theorem wxdy_negation_contrast :
    ¬ FormMatches wxdyConstruction.form negatedDoingTokens ∧
      FormMatches wxdyConstruction.form negatedComplementTokens := by
  decide

/-! ### Coinstantiation (Figure 13, Section 4.2) -/

/-- The coinstantiation construction, which unifies the intrinsic value of an unfulfilled
valence requirement of a predicator with the subject requirement of its controlled
complement, covering raising and control alike; it figures twice in every WXDY clause. The
flat rendering gives the predicator's subject the index of its complement's subject
requirement. -/
def coinstantiationForm : TypedForm String :=
  [ { filler := .open_ .NOUN, gf := some .subj, refIdx := some 1 }
  , { filler := .open_ .VERB, isHead := true }
  , { filler := .open_ .VERB, gf := some .comp, subjIdx := some 1 } ]

theorem coinstantiation_specificity :
    derivedSpecificity coinstantiationForm = .fullyAbstract := by decide

theorem coinstantiation_coreference : refGroupCount coinstantiationForm = 1 := by decide

end KayFillmore1999
