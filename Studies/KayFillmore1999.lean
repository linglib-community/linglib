module

public import Linglib.Syntax.ConstructionGrammar.Composition
public import Linglib.Syntax.ConstructionGrammar.Valence

/-!
# Kay and Fillmore (1999): The What's X Doing Y? Construction

The *What's X doing Y?* construction conventionally conveys that someone judges the scene `Y(X)`
incongruous, which is its meaning pole (`wxdyRule`, `Construct.meaning`). Its form (`wxdyForm`)
fixes BE and *doing* as heads, a left-isolated *what*
that binds the reference of nothing, and a predicate phrase `Y`, and forbids negating *doing*. The
form does not identify `X` with the subject of `Y`; coinstantiation in the valence sets of BE and
of *doing* does, since *what* has no value to offer
([`X` is the subject argument of `Y(X)`](##KayFillmore1999.Construct.ySubj_eq_x)). Read in their
word order, the canonical and stative examples [match the form](##KayFillmore1999.wxdy_matches),
and bare-stem *do*, *doing* under *keep*, *what else* and negated *doing* do not. Interpreted
through the construction, (3a) conveys that the scratch being on the table is judged incongruous
(`interps_scratch`), and its bare-stem counterpart has no reading (`interps_bareStem`).

## Implementation notes

The rows are main-clause questions, so their daughters come in the order that left isolation and
subject–auxiliary inversion give the construction, *what*, BE, `X`, *doing*, `Y`. The embedded,
uninverted order is not a row. A construct (`Construct`) records the values unification relates:
the intrinsic value of `X`, the scene #1, the subject requirement of the VP headed by *doing*, and
the subject requirement #2 of `Y`. The valence sets are read off the slots (`Slot.requirement`),
so the `[ref ∅]` of WXDY-*what* withholds whatever value the construct puts in its position. The
paper's incongruity-judgment frame is a parameter `judged`, the judgment of its contextually
anchored judge, who is not represented separately. The phrases around the construction in (3a) are
a fragment of grammar for that sentence only. Its
inheritance from the left-isolation, subject–auxiliary
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

/-- The form of the WXDY construction, the flat rendering of Figure 12 in the order of a
main-clause question: WXDY-*what*, BE, `X`, the VP headed by *doing*, and `Y`. -/
def wxdyForm : TypedForm String := [whatSlot, beSlot, xSlot, doingSlot, ySlot]

theorem wxdy_partially_open : wxdyForm.specificity = .partiallyOpen := by decide

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

/-! ### The meaning (Figure 12, (39))

The external semantics of the construction is a judgment of incongruity, attributed by a
contextually resolved judge to the state of affairs #1 that `Y` predicates of its subject
requirement #2. WXDY-*what*, BE and *doing* contribute nothing to it. -/

section Meaning

variable {E S : Type} (judged : (S → Prop) → S → Prop)

/-- (39): 'someone, you can figure out who, judges `Y(X)` to be incongruous'. In a construct the
state of affairs judged is `Y` of the value #2 of its subject requirement; `judged p` is the
proposition that the judge finds `p` incongruous. -/
def Construct.meaning (c : Construct E) (y : E → S → Prop) : S → Prop := judged (y c.ySubj)

/-- In a construct that coinstantiation licenses, the state of affairs judged incongruous is
`Y(X)`. -/
theorem Construct.meaning_eq {c : Construct E} (hbe : Coinstantiates c.beVal)
    (hdo : Coinstantiates c.doingVal) (y : E → S → Prop) :
    c.meaning judged y = judged (y c.x) := by
  rw [Construct.meaning, Construct.ySubj_eq_x hbe hdo]

/-- The denotations of the construction's parts: `X` an entity, `Y` a predicate, a preposition a
relation, the sentence a proposition, and WXDY-*what*, BE and *doing* inert. -/
inductive Den (E S : Type) where
  | ent : E → Den E S
  | pred : (E → S → Prop) → Den E S
  | rel : (E → E → S → Prop) → Den E S
  | prop : (S → Prop) → Den E S
  | inert : Den E S

/-- The construction composes `X` and `Y` into the judgment that `Y(X)` is incongruous. -/
def wxdyRule : CompositionRule (Den E S)
  | [.inert, .inert, .ent x, .inert, .pred y] => some (.prop (judged (y x)))
  | _ => none

theorem wxdyRule_eq_meaning {c : Construct E} (hbe : Coinstantiates c.beVal)
    (hdo : Coinstantiates c.doingVal) (y : E → S → Prop) :
    wxdyRule judged [.inert, .inert, .ent c.x, .inert, .pred y] =
      some (.prop (c.meaning judged y)) := by
  rw [Construct.meaning_eq judged hbe hdo]; rfl

/-- The WXDY construction, its form paired with the judgment of incongruity. -/
def wxdyConstruction : Construction (CompositionRule (Den E S)) :=
  { form := wxdyForm, meaning := wxdyRule judged }

theorem wxdy_formal_idiom : (wxdyConstruction (E := E) judged).IsFormalIdiom := by
  change wxdyForm.specificity ≠ _
  decide

/-- The phrases of (3a) around the construction: the phrases headed by BE and by *doing*, which
pass their head's denotation up, and the prepositional phrase. -/
def phrasal : List (Construction (CompositionRule (Den E S))) :=
  [ { form := [{ filler := .open_ .AUX, isHead := true }]
      meaning := fun | [d] => some d | _ => none }
  , { form := [{ filler := .open_ .VERB, isHead := true }]
      meaning := fun | [d] => some d | _ => none }
  , { form := [{ filler := .open_ .ADP, isHead := true }, { filler := .open_ .NOUN }]
      meaning := fun | [.rel r, .ent t] => some (.pred fun x ↦ r x t) | _ => none } ]

end Meaning

/-! ### The grammatical evidence (Section 2.3)

The paper's minimal pairs, matched against the form: each is a sequence of daughter trees in the
order of its words, with lemma-level words tagged for part of speech. -/

open PhraseStructure (Tree)
open Morphology (Word)

/-- *not*, a particle of negative polarity. -/
def negator : Word := { form := "not", cat := .PART, features := .of (polarity := some .Neg) }

/-- The phrase headed by BE. -/
def bePhrase : Tree Unit Word := .node () [.leaf (.mk' "be" .AUX)]

/-- The phrase headed by *doing*. -/
def doingPhrase : Tree Unit Word := .node () [.leaf (.mk' "doing" .VERB)]

/-- *on the table*. -/
def onTheTable : Tree Unit Word := .node () [.leaf (.mk' "on" .ADP), .leaf (.mk' "table" .NOUN)]

/-- (3a) *What is this scratch doing on the table?* -/
def scratchTokens : List (Tree Unit Word) :=
  [.leaf (.mk' "what" .PRON), bePhrase, .leaf (.mk' "scratch" .NOUN), doingPhrase, onTheTable]

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
    FormMatches wxdyForm scratchTokens ∧
      FormMatches wxdyForm stativeTokens ∧
      FormMatches wxdyForm negatedComplementTokens ∧
      ¬ FormMatches wxdyForm bareStemTokens ∧
      ¬ FormMatches wxdyForm nonCopulaTokens ∧
      ¬ FormMatches wxdyForm whatElseTokens ∧
      ¬ FormMatches wxdyForm negatedDoingTokens := by
  decide

/-! ### (3a) through the construction -/

section Example3a

variable {S : Type} (judged : (S → Prop) → S → Prop) (on : Ent → Ent → S → Prop)

/-- The words of (3a) and (12a). -/
def lexicon (w : Word) : Option (Den Ent S) :=
  match w.form with
  | "what" | "be" | "do" | "doing" => some .inert
  | "scratch" => some (.ent .scratch)
  | "table" => some (.ent .table)
  | "on" => some (.rel on)
  | _ => none

/-- (3a) conveys that the scratch being on the table is judged incongruous, the meaning of its
construct. -/
theorem interps_scratch :
    interps (wxdyConstruction judged :: phrasal) (lexicon on) (.node () scratchTokens) =
      [.prop (scratchConstruct.meaning judged fun x ↦ on x .table)] := by
  have hbe : interps (wxdyConstruction judged :: phrasal) (lexicon on) bePhrase = [.inert] := rfl
  have hdoing : interps (wxdyConstruction judged :: phrasal) (lexicon on) doingPhrase =
      [.inert] := rfl
  have hon : interps (wxdyConstruction judged :: phrasal) (lexicon on) onTheTable =
      [.pred fun x ↦ on x .table] := rfl
  rw [scratchTokens, interps_node]
  simp only [interpsList, hbe, hdoing, hon]
  rfl

-- (12a), with bare-stem *do*, has no reading.
theorem interps_bareStem :
    interps (wxdyConstruction judged :: phrasal) (lexicon on) (.node () bareStemTokens) = [] :=
  rfl

end Example3a

end KayFillmore1999
