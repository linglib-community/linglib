module

public import Linglib.Syntax.ConstructionGrammar.Composition
public import Studies.Goldberg1995
public import Studies.FillmoreKayOConnor1988

/-!
# Kay and Michaelis (2019): Constructional Meaning and Compositionality

This file formalizes the two formal claims of Kay and Michaelis's survey chapter. First,
rules of semantic combination are construction-relative: a construction specifies how the
semantics of the daughters combine into the semantics of the mother and what the construction
itself adds (Sections 1 and 4). `CompositionRule` and `interps`
give that architecture content over the licensing layer's local trees, a token's readings being
whatever the syntactically matching constructions' rules produce from its daughters' readings;
the chapter's opening contrast, *purple plum* composed by intersection and *alleged thief* by
operator application under one syntactic configuration, falls out as two constructions sharing
a typed form whose rules accept disjoint daughter denotations, so that each token gets exactly
one reading (`purple_plum_intersective`, `alleged_thief_operator`). Second, the kinds of
meaning a construction contributes, truth-conditional content, argument structure, conventional
implicature, illocutionary force, metalinguistic comment and information flow (Sections 3 and
9), are `MeaningKind`, instantiated on the chapter's own cases already in the library: caused
motion, *let alone* and the incredulity response.

## References

* [kay-michaelis-2019]
* [fillmore-kay-oconnor-1988]
-/

@[expose] public section

namespace KayMichaelis2019

open ConstructionGrammar

/-! ### §3: kinds of constructional meaning

The chapter's classification, offered as "neither definitive nor
exhaustive"; `informationFlow` is §9's strand. -/

/-- A `MeaningKind` is a kind of meaning a construction contributes ([kay-michaelis-2019]
§3, §9). -/
inductive MeaningKind where
  | literal                  -- §3(i), §4: truth-conditional content
  | argumentStructure        -- §3(ii), §5
  | conventionalImplicature  -- §3(iii), §6: incl. pragmatic presupposition
  | illocutionaryForce       -- §3(iv), §7
  | metalinguistic           -- §3(v), §8
  | informationFlow          -- §9: topic/focus presuppositions
  deriving DecidableEq, Repr

/-! ### §4: construction-relative composition

"The construction also specifies how the semantics of the daughters are
combined to produce the semantics of the mother, and what additional
semantics, if any, is contributed by the construction itself" — the
`CompositionRule` architecture of
`ConstructionGrammar.Composition`, instantiated below. -/

/-! ### §1: *purple plum* vs. *alleged thief*

"A purple plum is a member of the set of purple things and a member of
the set of plums. But an alleged thief is not a member of the
intersection of the set of thieves and the set of alleged things." Two
modification constructions share one syntactic form; their rules accept
disjoint daughter shapes, so each token composes exactly one way. -/

/-- A `Den E` is a denotation, either a first-order predicate or a predicate operator. -/
inductive Den (E : Type*) where
  | pred : (E → Prop) → Den E
  | op : ((E → Prop) → (E → Prop)) → Den E

/-- The intersective rule maps two predicate daughters to their intersection (*purple
plum*). -/
def intersectiveRule (E : Type*) : CompositionRule (Den E)
  | [.pred a, .pred n] => some (.pred fun x ↦ a x ∧ n x)
  | _ => none

/-- The operator rule applies the adjective's predicate operator to the head's predicate
(*alleged thief*). -/
def operatorRule (E : Type*) : CompositionRule (Den E)
  | [.op f, .pred n] => some (.pred (f n))
  | _ => none

/-- `modificationForm` is the prenominal-modification form the two constructions share. -/
def modificationForm : TypedForm String :=
  [ { filler := .open_ .ADJ }
  , { filler := .open_ .NOUN, isHead := true } ]

/-- Intersective Adj+N modification has the intersective rule as its meaning. -/
def intersectiveModification (E : Type*) :
    Construction (CompositionRule (Den E)) :=
  { form := modificationForm
  , meaning := intersectiveRule E }

/-- Operator Adj+N modification has the operator rule as its meaning. -/
def operatorModification (E : Type*) :
    Construction (CompositionRule (Den E)) :=
  { form := modificationForm
  , meaning := operatorRule E }

/-- The two constructions share their form, one rule of syntactic formation with two semantic
specifications (§1). -/
theorem same_form (E : Type*) :
    (intersectiveModification E).form = (operatorModification E).form := rfl

/-- `demoCx` is the inventory of the two modification constructions. -/
def demoCx (E : Type*) : List (Construction (CompositionRule (Den E))) :=
  [intersectiveModification E, operatorModification E]

section Demo

variable {E : Type*} (purple plum thief : E → Prop)
  (alleged : (E → Prop) → (E → Prop))

/-- `demoLex` gives *purple*, *plum* and *thief* predicates and *alleged* an operator. -/
def demoLex (w : Morphology.Word) : Option (Den E) :=
  match w.form with
  | "purple" => some (.pred purple)
  | "alleged" => some (.op alleged)
  | "plum" => some (.pred plum)
  | "thief" => some (.pred thief)
  | _ => none

/-- `purplePlum` is *purple plum*, two words tagged for part of speech. -/
def purplePlum : PhraseStructure.Tree Unit Morphology.Word :=
  .node () [.leaf (.mk' "purple" .ADJ), .leaf (.mk' "plum" .NOUN)]

/-- `allegedThief` is *alleged thief*, two words tagged for part of speech. -/
def allegedThief : PhraseStructure.Tree Unit Morphology.Word :=
  .node () [.leaf (.mk' "alleged" .ADJ), .leaf (.mk' "thief" .NOUN)]

theorem purple_plum_intersective :
    interps (demoCx E) (demoLex purple plum thief alleged) purplePlum
      = [.pred fun x ↦ purple x ∧ plum x] := rfl

theorem alleged_thief_operator :
    interps (demoCx E) (demoLex purple plum thief alleged) allegedThief
      = [.pred (alleged thief)] := rfl

theorem alleged_thief_needs_operator_construction :
    interps [intersectiveModification E] (demoLex purple plum thief alleged) allegedThief
      = [] := rfl

end Demo

/-! ### §§5–7 instantiated

The chapter's cases that the library already formalizes, with the kind of
meaning each contributes. -/

/-- `chapterCases` pairs the chapter's example constructions with their kinds of meaning: caused
motion (§5, exx. 19–22, *Frank sneezed the tissue off the table*), *let alone* (§6, ex. 32), and
the incredulity type (§7, ex. 14, *Him get first prize?!*). -/
def chapterCases : List (Construction Unit × MeaningKind) :=
  [ (Goldberg1995.causedMotion.map fun _ ↦ (), .argumentStructure)
  , (_root_.FillmoreKayOConnor1988.letAloneConstruction, .conventionalImplicature)
  , (_root_.FillmoreKayOConnor1988.incredulityResponse, .illocutionaryForce) ]

end KayMichaelis2019
