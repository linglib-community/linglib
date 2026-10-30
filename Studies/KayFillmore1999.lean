module

public import Linglib.Syntax.ConstructionGrammar.Licensing

/-!
# Kay and Fillmore (1999): The What's X Doing Y? Construction

The *What's X doing Y?* construction conventionally conveys that someone judges the scene `Y(X)`
incongruous. Its form (`wxdyConstruction`) fixes BE and *doing* as heads, a left-isolated *what*
that binds the reference of nothing, and a predicate phrase `Y`, and forbids negating *doing*. The
form does not identify `X` with the subject of `Y`; coinstantiation in the valence sets of BE and
of *doing* does, since *what* has no value to offer
([`X` is the subject argument of `Y(X)`](##KayFillmore1999.Construct.ySubj_eq_x)). Read in their
word order, the canonical and stative examples [match the form](##KayFillmore1999.wxdy_matches),
and bare-stem *do*, *doing* under *keep*, *what else* and negated *doing* do not.

## Implementation notes

The rows are main-clause questions, so their daughters come in the order that left isolation and
subject–auxiliary inversion give the construction, *what*, BE, `X`, *doing*, `Y`. The embedded,
uninverted order is not a row. A construct (`Construct`) records the values unification relates:
the intrinsic value of `X`, the scene #1, the subject requirement of the VP headed by *doing*, and
the subject requirement #2 of `Y`. The valence sets are read off the slots (`Slot.requirement`),
so the `[ref ∅]` of WXDY-*what* withholds whatever value the construct puts in its position. The
paper's incongruity-judgment frame with its contextually anchored judge is not represented beyond
the construction's pragmatic point. Its inheritance from the left-isolation, subject–auxiliary
inversion and wh-interrogative constructions of the paper's unification grammar is recorded in
prose only.

## References

* [kay-fillmore-1999]
* [fillmore-kay-oconnor-1988]
-/

@[expose] public section

namespace KayFillmore1999

open ConstructionGrammar

/-! ### The construction (Figure 12) -/

/-- WXDY-*what*, a fixed object occurring left-isolated (`[loc -]`) and binding the reference of
nothing (`[ref ∅]`). -/
def whatSlot : Slot String :=
  { filler := .fixed "what", gf := some .obj, constraints := [.locMinus, .refEmpty] }

/-- BE, the head of the construction. -/
def beSlot : Slot String := { filler := .headed "be" .AUX, isHead := true }

/-- `X`, the subject of BE. -/
def xSlot : Slot String := { filler := .semantic "referential", gf := some .subj }

/-- The complement of BE, a VP headed by *doing*, which cannot be negated (`[neg -]`, Section 4.6).
-/
def doingSlot : Slot String :=
  { filler := .headed "doing" .VERB, gf := some .comp, constraints := [.negMinus] }

/-- `Y`, the complement of *doing*, a predicate phrase of any category. -/
def ySlot : Slot String := { filler := .phrasal, gf := some .comp }

/-- The WXDY construction, the flat rendering of Figure 12 in the order of a main-clause
question: WXDY-*what*, BE, `X`, the VP headed by *doing*, and `Y`. -/
def wxdyConstruction : Construction Unit :=
  { form := [whatSlot, beSlot, xSlot, doingSlot, ySlot]
  , meaning := ()
  , pragmaticPoint := true }

theorem wxdy_formal_idiom : wxdyConstruction.IsFormalIdiom := by decide

theorem wxdy_partially_open : wxdyConstruction.specificity = .partiallyOpen := by decide

/-! ### Coinstantiation (Figure 13, Section 4.2) -/

/-- A construct of the WXDY construction at the granularity of Figure 12: the intrinsic value of
`X`, the value a referential filler of WXDY-*what*'s position would contribute, the scene #1 that
*doing* and `Y` share, the subject requirement of the VP headed by *doing*, and the subject
requirement #2 of `Y`, the argument of the scene. -/
structure Construct (E : Type*) where
  /-- The intrinsic value of `X`. -/
  x : E
  /-- The value a referential filler of WXDY-*what*'s position would contribute. -/
  what : E
  /-- The scene #1 judged incongruous. -/
  scene : E
  /-- The value of the subject requirement of the VP headed by *doing*. -/
  doingSubj : E
  /-- The value #2 of the subject requirement of `Y`. -/
  ySubj : E

namespace Construct

variable {E : Type*} (c : Construct E)

/-- The valence set of BE: the requirements of `X` and of the VP headed by *doing*. -/
def beVal : List (Requirement E) :=
  [xSlot.requirement c.x none, doingSlot.requirement c.scene (some c.doingSubj)]

/-- The valence set of *doing*: its unrealized subject and the requirements of WXDY-*what* and of
`Y`. -/
def doingVal : List (Requirement E) :=
  [⟨some .subj, some c.doingSubj, none⟩, whatSlot.requirement c.what none,
    ySlot.requirement c.scene (some c.ySubj)]

theorem beVal_eq :
    c.beVal = [⟨some .subj, some c.x, none⟩, ⟨some .comp, some c.scene, some c.doingSubj⟩] := by
  simp [beVal, Slot.requirement, xSlot, doingSlot]

/-- WXDY-*what*, marked `[ref ∅]`, contributes no intrinsic value to the valence set of *doing*. -/
theorem doingVal_eq : c.doingVal = [⟨some .subj, some c.doingSubj, none⟩, ⟨some .obj, none, none⟩,
    ⟨some .comp, some c.scene, some c.ySubj⟩] := by
  simp [doingVal, Slot.requirement, whatSlot, ySlot]

variable {c}

/-- In a construct that coinstantiation licenses, in the valence sets of BE and of *doing*, the
argument #2 of the scene judged incongruous is the intrinsic value of `X`: `X` is the subject
argument of the predication `Y(X)` (Section 4.2), though Figure 12 does not identify them. -/
theorem ySubj_eq_x (hbe : Coinstantiates c.beVal) (hdo : Coinstantiates c.doingVal) :
    c.ySubj = c.x := by
  rw [beVal_eq, coinstantiates_subj_comp_iff] at hbe
  have hy : c.ySubj = c.doingSubj := by simpa [Coinstantiates, doingVal_eq, eq_comm] using hdo
  exact hy.trans hbe

end Construct

/-- The entities of (3a): the scratch, the table, and the scene of the scratch being on the
table. -/
inductive Ent
  | scratch
  | table
  | scene
  deriving DecidableEq

/-- The construct of (3a) *What's this scratch doing on the table?*, in which the scratch fills
the subject requirements of *doing* and of *on the table*. -/
def scratchConstruct : Construct Ent := ⟨.scratch, .table, .scene, .scratch, .scratch⟩

example : Coinstantiates scratchConstruct.beVal ∧ Coinstantiates scratchConstruct.doingVal := by
  decide

/-- No construct of (3a) makes the table the subject of *on the table*. -/
example (c : Construct Ent) (hx : c.x = .scratch) (hy : c.ySubj = .table) :
    ¬ (Coinstantiates c.beVal ∧ Coinstantiates c.doingVal) :=
  fun h ↦ absurd ((Construct.ySubj_eq_x h.1 h.2).trans hx) (by rw [hy]; decide)

/-- Were WXDY-*what* referential, coinstantiation could unify the subject of `Y` with the value of
*what* instead of with the subject of *doing*; with `[ref ∅]` it cannot. -/
example :
    Coinstantiates [⟨some .subj, some Ent.scratch, none⟩,
      { whatSlot with constraints := [.locMinus] }.requirement .table none,
      ySlot.requirement .scene (some .table)] ∧
    ¬ Coinstantiates [⟨some .subj, some Ent.scratch, none⟩, whatSlot.requirement .table none,
      ySlot.requirement .scene (some .table)] := by
  decide

/-! ### The grammatical evidence (Section 2.3)

The paper's minimal pairs, matched against the form: each is a sequence of daughter trees in the
order of its words, with lemma-level words tagged for part of speech. -/

open PhraseStructure (Tree)
open Morphology (Word)

/-- *not*, a particle of negative polarity. -/
def negator : Word := { form := "not", cat := .PART, features := .of (polarity := some .Neg) }

/-- (3a) *What is this scratch doing on the table?* -/
def scratchTokens : List (Tree Unit Word) :=
  [ .leaf (.mk' "what" .PRON),
    .node () [.leaf (.mk' "be" .AUX)],
    .leaf (.mk' "scratch" .NOUN),
    .node () [.leaf (.mk' "doing" .VERB)],
    .node () [.leaf (.mk' "on" .ADP), .leaf (.mk' "table" .NOUN)] ]

/-- (14a) *What's he doing knowing the answer?*, a stative complement. -/
def stativeTokens : List (Tree Unit Word) :=
  [ .leaf (.mk' "what" .PRON),
    .node () [.leaf (.mk' "be" .AUX)],
    .leaf (.mk' "he" .PRON),
    .node () [.leaf (.mk' "doing" .VERB)],
    .node () [.leaf (.mk' "knowing" .VERB), .leaf (.mk' "answer" .NOUN)] ]

/-- (12a) *What does this scratch do on the table?*, with bare-stem *do*. -/
def bareStemTokens : List (Tree Unit Word) :=
  [ .leaf (.mk' "what" .PRON),
    .node () [.leaf (.mk' "do" .AUX)],
    .leaf (.mk' "scratch" .NOUN),
    .node () [.leaf (.mk' "do" .VERB)],
    .node () [.leaf (.mk' "on" .ADP), .leaf (.mk' "table" .NOUN)] ]

/-- (13a) *What did he keep doing in the tool shed?*, *doing* as complement of *keep* rather
than of copular BE: a fine sentence, but not an instance of the construction. -/
def nonCopulaTokens : List (Tree Unit Word) :=
  [ .leaf (.mk' "what" .PRON),
    .node () [.leaf (.mk' "do" .AUX)],
    .leaf (.mk' "he" .PRON),
    .node () [.leaf (.mk' "keep" .VERB), .leaf (.mk' "doing" .VERB)],
    .node () [.leaf (.mk' "in" .ADP), .leaf (.mk' "shed" .NOUN)] ]

/-- (15f) *What else are you doing eating cold pizza?*, with *else* on WXDY-*what*. -/
def whatElseTokens : List (Tree Unit Word) :=
  [ .node () [.leaf (.mk' "what" .PRON), .leaf (.mk' "else" .ADV)],
    .node () [.leaf (.mk' "be" .AUX)],
    .leaf (.mk' "you" .PRON),
    .node () [.leaf (.mk' "doing" .VERB)],
    .node () [.leaf (.mk' "eating" .VERB), .leaf (.mk' "pizza" .NOUN)] ]

/-- (17b) *What are my brushes not doing soaking in water?*, with negated *doing*. -/
def negatedDoingTokens : List (Tree Unit Word) :=
  [ .leaf (.mk' "what" .PRON),
    .node () [.leaf (.mk' "be" .AUX)],
    .leaf (.mk' "brushes" .NOUN),
    .node () [.leaf negator, .leaf (.mk' "doing" .VERB)],
    .node () [.leaf (.mk' "soaking" .VERB), .leaf (.mk' "water" .NOUN)] ]

/-- (17c) *What are my brushes doing not soaking in water?*, negation inside `Y`. -/
def negatedComplementTokens : List (Tree Unit Word) :=
  [ .leaf (.mk' "what" .PRON),
    .node () [.leaf (.mk' "be" .AUX)],
    .leaf (.mk' "brushes" .NOUN),
    .node () [.leaf (.mk' "doing" .VERB)],
    .node () [.leaf negator, .leaf (.mk' "soaking" .VERB), .leaf (.mk' "water" .NOUN)] ]

/-- The canonical (3a) and the stative (14a) match the form, and so does (17c), negated inside
`Y`, while the bare-stem *do* of (12a), *doing* as the complement of *keep* in (13a), *what else*
in (15f) and the negated *doing* of (17b) do not. -/
theorem wxdy_matches :
    FormMatches wxdyConstruction.form scratchTokens ∧
      FormMatches wxdyConstruction.form stativeTokens ∧
      FormMatches wxdyConstruction.form negatedComplementTokens ∧
      ¬ FormMatches wxdyConstruction.form bareStemTokens ∧
      ¬ FormMatches wxdyConstruction.form nonCopulaTokens ∧
      ¬ FormMatches wxdyConstruction.form whatElseTokens ∧
      ¬ FormMatches wxdyConstruction.form negatedDoingTokens := by
  decide

end KayFillmore1999
