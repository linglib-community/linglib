module

public import Linglib.Morphology.DistributedMorphology.Allosemy
public import Linglib.Morphology.DistributedMorphology.VocabularyInsertion.Basic
public import Linglib.Data.Examples.Myler2016
public import Linglib.Data.Examples.Readers

/-!
# Myler (2016): Building and Interpreting Possession Sentences

This file formalizes Myler's treatment of *have* and *be* as one meaningless
copula whose meaning is the identity function and whose form is fixed by its syntactic
surroundings: *have* under a transitive Voice, one bearing the specifier feature and
φ-features, and *be* otherwise (`englishItems`, `have_iff_transitive`). The possession
relation comes from inside the noun-phrase complement, and Voice adds a thematic role only
when the complement is a predicate of eventualities, so with a relational complement the
sentence means what its complement means (`expletive_voice_passes_complement`). Icelandic's
two *have* verbs divide the transitive context by what lies below the copula, *hafa* over a
predicative phrase and *eiga* elsewhere (`icelandicItems`, `hafa_iff_predP`), and the two
generalizations about attributive possession follow from the structures
(`eiga_only_if_no_pp`, `hafa_only_if_pp`); the items reproduce the book's Icelandic data,
clausal and attributive.

## Implementation notes

Example numbers are the book's, chapter 1 for the copula and Voice rules and chapter 4 for
*have* and the Icelandic section. The Minimalist Voice flavors are not used for the
insertion context, which is syntactic, the transitive configuration; relational *have* has
an expletive Voice at logical form while still surfacing as *have*.

## References

* [myler-2016]
-/

@[expose] public section

namespace Myler2016

open DistributedMorphology DistributedMorphology.Allosemy

/-! ### The copula's context and form -/

/-- What the insertion of v sees: the specifier feature {D} and the
φ-features on the Voice above, and a PredP complement below. -/
inductive Feature where
  | d | phi | pred
  deriving DecidableEq, Repr

/-- A clause's context for v. -/
structure Context where
  voiceD : Bool
  voicePhi : Bool
  predComplement : Bool
  deriving DecidableEq, Repr, Fintype

/-- The features a context exposes. -/
def Context.features (c : Context) : Finset Feature :=
  (if c.voiceD then {.d} else ∅) ∪ (if c.voicePhi then {.phi} else ∅) ∪
    (if c.predComplement then {.pred} else ∅)

/-- A transitive context: Voice introduces an external argument and bears
φ-features that license v's complement. -/
def Context.Transitive (c : Context) : Prop := c.voiceD = true ∧ c.voicePhi = true

instance (c : Context) : Decidable c.Transitive := inferInstanceAs (Decidable (_ ∧ _))

/-- English ((89) of chapter 1): *have* in a transitive context, *be* elsewhere. -/
def englishItems : List (VocabularyItem Feature String) := [{.d, .phi} ⟷ "have", ∅ ⟷ "be"]

/-- Icelandic ((89) of chapter 4): *hafa* in a transitive context over a PredP,
*eiga* in a transitive context otherwise, and the copula *vera* elsewhere. -/
def icelandicItems : List (VocabularyItem Feature String) :=
  [{.d, .phi, .pred} ⟷ "hafa", {.d, .phi} ⟷ "eiga", ∅ ⟷ "vera"]

/-- The form of v in a context, by the Subset Principle over a language's
items. -/
def spellout (items : List (VocabularyItem Feature String)) (c : Context) : Option String :=
  subsetPrinciple items c.features

theorem have_iff_transitive :
    ∀ c : Context, spellout englishItems c = some "have" ↔ c.Transitive := by
  decide

theorem hafa_iff_predP :
    ∀ c : Context,
      spellout icelandicItems c = some "hafa" ↔ c.Transitive ∧ c.predComplement = true := by
  decide

/-! ### Attributive possession and the two generalizations (§4.3) -/

/-- The two DP-internal possession structures ((93), (94)): the possessor in
a PP under Pred, or in Spec,PossP. -/
inductive Attributive where
  | predP | possP
  deriving DecidableEq, Repr, Fintype

/-- A PP possessor is available exactly under the PredP structure ((92),
column C). -/
def Attributive.AllowsPP : Attributive → Prop
  | .predP => True
  | .possP => False

instance : DecidablePred Attributive.AllowsPP :=
  λ a => by cases a <;> unfold Attributive.AllowsPP <;> infer_instance

/-- Clausal possession embeds the attributive structure under v in a
transitive context. -/
def Attributive.context (a : Attributive) : Context := ⟨true, true, a = .predP⟩

/-- Generalization 1 ((90a)): clausal possession with *eiga* only if
DP-internal possession cannot use a PP. -/
theorem eiga_only_if_no_pp (a : Attributive) (h : spellout icelandicItems a.context = some "eiga") :
    ¬ a.AllowsPP := by
  revert h; cases a <;> decide

/-- Generalization 2 ((90b)): clausal possession with *hafa* only if
DP-internal possession can use a PP. -/
theorem hafa_only_if_pp (a : Attributive) (h : spellout icelandicItems a.context = some "hafa") :
    a.AllowsPP := by
  revert h; cases a <;> decide

/-! ### The Icelandic data pool -/

/-- The possession relations of (91) and (92). -/
inductive Relation where
  | concrete | kinship | bodyPart | abstract
  deriving DecidableEq, Repr, Fintype

def Relation.ofString : String → Option Relation
  | "concrete" => some .concrete | "kinship" => some .kinship | "bodyPart" => some .bodyPart
  | "abstract" => some .abstract | _ => none

/-- The structure each relation is built with: body parts and abstract
relations under Pred with a PP possessor, concrete and kinship relations
under Poss ((92)–(94)). -/
def Relation.attributive : Relation → Attributive
  | .concrete | .kinship => .possP
  | .bodyPart | .abstract => .predP

/-- A clausal row of (91): the relation, the verb, and whether it is
accepted. -/
structure ClausalRow where
  relation : Relation
  verb : String
  accepted : Bool
  deriving DecidableEq, Repr

def ClausalRow.ofDatum (ex : Datum) : Option ClausalRow := do
  guard (ex.paperFeatures.lookup "construction" = some "clausal")
  let relation ← ex.paperFeatures.lookup "relation" >>= Relation.ofString
  let verb ← ex.paperFeatures.lookup "verb"
  pure ⟨relation, verb, ex.judgment = .acceptable⟩

/-- A column-C row of (92): the relation and whether the PP possessor is
accepted. -/
structure PPRow where
  relation : Relation
  accepted : Bool
  deriving DecidableEq, Repr

def PPRow.ofDatum (ex : Datum) : Option PPRow := do
  guard (ex.paperFeatures.lookup "construction" = some "attributiveC")
  let relation ← ex.paperFeatures.lookup "relation" >>= Relation.ofString
  pure ⟨relation, ex.judgment = .acceptable⟩

def clausalRows : List ClausalRow := Examples.all.filterMap ClausalRow.ofDatum

def ppRows : List PPRow := Examples.all.filterMap PPRow.ofDatum

theorem rows_cover :
    ∀ ex ∈ Examples.all,
      (ClausalRow.ofDatum ex).isSome ∨
        ex.paperFeatures.lookup "construction" ≠ some "clausal" := by
  decide

-- (91)
theorem clausal_rows :
    ∀ r ∈ clausalRows,
      (spellout icelandicItems r.relation.attributive.context = some r.verb) = r.accepted := by
  decide

-- (92)
theorem attributive_rows :
    ∀ r ∈ ppRows, decide r.relation.attributive.AllowsPP = r.accepted := by
  decide

/-! ### The meaning of a *have* sentence -/

/-- The Voice alloseme a *have* sentence's complement selects ((62)): the
substrate's competition over `Voice.vocabulary`. -/
def voiceAlloseme (eventiveVoiceP stative : Bool) : Voice.Alloseme :=
  Voice.Alloseme.fromComplement
    ((if eventiveVoiceP then {.cat .v, .eventive} else ∅) ∪ if stative then {.stative} else ∅ :
      Finset Allosemy.Feature)

/-- Over a relational complement Voice is the expletive identity `⟦v⟧ = λx.x` (61), as with the
*have* of (7a) and §4.1.1. -/
theorem expletive_voice_passes_complement : voiceAlloseme false false = .expletive := by decide

-- (7b), §4.1.2
theorem contentful_voice_adds_theta :
    (voiceAlloseme false true).AssignsTheta ∧ (voiceAlloseme true false).AssignsTheta := by
  decide

end Myler2016
