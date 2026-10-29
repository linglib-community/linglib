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
the reference of nothing, `Y` is a predicate phrase, and *doing* may not be negated, a
stipulation the paper reports being unable to deduce.

Figure 12 does not identify `X` with the subject of `Y`. Its index #1 makes *doing* and `Y` share
the scene judged incongruous, and #2 makes the argument of that scene the value of `Y`'s own
subject requirement. The identity comes from coinstantiation (Figure 13), which satisfies the
subject requirement of a controlled complement by unifying it with another requirement of the
same predicator (`Coinstantiates`). A construct is licensed only if coinstantiation applies twice,
in the valence set of BE and in that of *doing*. Since WXDY-*what* refers to nothing, the only
controller of `Y`'s subject is the subject of *doing*, so [`X` becomes the subject argument of
the predication `Y(X)`](##KayFillmore1999.Construct.ySubj_eq_x).

The grammatical evidence for the construction in Section 2.3 is derived by the licensing
recognizer over the paper's minimal pairs, read in their word order: the canonical (3a) and the
stative (14a) are licensed, while the bare-stem *do* of (12a), *doing* as complement of *keep* in
(13a), *what else* in (15f), and the negated *doing* of (17b) are not, negation inside `Y` in
(17c) being fine.

## Implementation notes

The rows are main-clause questions, so their daughters come in the order that left isolation and
subject–auxiliary inversion give the construction, *what*, BE, `X`, *doing*, `Y`. The embedded,
uninverted order is not a row. A construct (`Construct`) records the four values unification
relates: the intrinsic value of `X`, the scene #1, the subject requirement of the VP headed by
*doing*, and the subject requirement #2 of `Y`. The semantics of WXDY-*what* is `[ref ∅]`, an
intrinsic value of `none`, which gives coinstantiation nothing to unify. The paper's
incongruity-judgment frame with its contextually anchored judge is not represented beyond the
construction's pragmatic point. Its inheritance from the left-isolation, subject–auxiliary
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

/-- The WXDY construction, the flat rendering of Figure 12 in the order of a main-clause
question. WXDY-*what* is left-isolated and not an operator binding the reference of anything, BE
heads the construction, `X` is its subject, and BE governs the complement *doing*, which cannot be
negated (Section 4.6) and governs the complement `Y`, a predicate phrase of any category. -/
def wxdyConstruction : Construction Unit :=
  { form :=
      [ { filler := .fixed "what", gf := some .obj, constraints := [.locMinus, .refEmpty] }
      , { filler := .headed "be" .AUX, isHead := true }
      , { filler := .semantic "referential", gf := some .subj }
      , { filler := .headed "doing" .VERB, gf := some .comp, constraints := [.negMinus] }
      , { filler := .phrasal, gf := some .comp } ]
  , meaning := ()
  , pragmaticPoint := true }

theorem wxdy_formal_idiom : wxdyConstruction.IsFormalIdiom := by decide

theorem wxdy_partially_open : wxdyConstruction.specificity = .partiallyOpen := rfl

/-! ### Coinstantiation (Figure 13, Section 4.2) -/

/-- A valence requirement of a predicator as unification sees it: its grammatical function, its
intrinsic value, `none` for the semantics `[ref ∅]`, and the value of its own subject requirement
when it is a predicate that does not realize its subject. -/
structure Requirement (E : Type*) where
  gf : GrammaticalFunction
  intrinsic : Option E
  subj : Option E
  deriving DecidableEq

variable {E : Type*}

/-- Coinstantiation (Figure 13) satisfies the subject requirement of each complement of a
predicator by unifying it with the intrinsic value of another requirement of the same predicator,
covering raising and control alike. A requirement whose semantics is `[ref ∅]` has no value to
give. -/
def Coinstantiates (val : List (Requirement E)) : Prop :=
  ∀ k ∈ val, k.gf = .comp → ∀ v ∈ k.subj, ∃ c ∈ val, c ≠ k ∧ c.intrinsic = some v

instance [DecidableEq E] (val : List (Requirement E)) : Decidable (Coinstantiates val) := by
  unfold Coinstantiates; infer_instance

/-- A construct of the WXDY construction at the granularity of Figure 12: the intrinsic value of
`X`, the scene #1 that *doing* and `Y` share, the subject requirement of the VP headed by *doing*,
and the subject requirement #2 of `Y`, the argument of the scene. -/
structure Construct (E : Type*) where
  x : E
  scene : E
  doingSubj : E
  ySubj : E

namespace Construct

variable (c : Construct E)

/-- The valence set of BE: its subject `X` and the VP headed by *doing*. -/
def beVal : List (Requirement E) :=
  [⟨.subj, some c.x, none⟩, ⟨.comp, some c.scene, some c.doingSubj⟩]

/-- The valence set of *doing*: its subject, WXDY-*what*, whose semantics is `[ref ∅]`, and `Y`. -/
def doingVal : List (Requirement E) :=
  [⟨.subj, some c.doingSubj, none⟩, ⟨.obj, none, none⟩, ⟨.comp, some c.scene, some c.ySubj⟩]

variable {c}

/-- In a construct that coinstantiation licenses, in the valence sets of BE and of *doing*, the
argument #2 of the scene judged incongruous is the intrinsic value of `X`: `X` is the subject
argument of the predication `Y(X)` (Section 4.2), though Figure 12 does not identify them. -/
theorem ySubj_eq_x (hbe : Coinstantiates c.beVal) (hdo : Coinstantiates c.doingVal) :
    c.ySubj = c.x := by
  have h₁ := hbe ⟨.comp, some c.scene, some c.doingSubj⟩ (by simp [beVal]) rfl c.doingSubj rfl
  have h₂ := hdo ⟨.comp, some c.scene, some c.ySubj⟩ (by simp [doingVal]) rfl c.ySubj rfl
  simp [beVal, doingVal] at h₁ h₂
  grind

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
def scratchConstruct : Construct Ent := ⟨.scratch, .scene, .scratch, .scratch⟩

example : Coinstantiates scratchConstruct.beVal ∧ Coinstantiates scratchConstruct.doingVal := by
  decide

/-- No construct of (3a) makes the table the subject of *on the table*. -/
example (c : Construct Ent) (hx : c.x = .scratch) (hy : c.ySubj = .table) :
    ¬ (Coinstantiates c.beVal ∧ Coinstantiates c.doingVal) :=
  fun h ↦ absurd ((Construct.ySubj_eq_x h.1 h.2).trans hx) (by rw [hy]; decide)

/-- Were WXDY-*what* referential, coinstantiation could unify the subject of `Y` with it instead
of with the subject of *doing*. -/
example : Coinstantiates [⟨.subj, some Ent.scratch, none⟩, ⟨.obj, some .table, none⟩,
    ⟨.comp, some .scene, some .table⟩] := by
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

end KayFillmore1999
