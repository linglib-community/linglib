module

public import Studies.Chierchia1998
public import Linglib.Data.Examples.Longobardi2001
public import Linglib.Data.Examples.Readers
public import Linglib.Data.Examples.Languages

/-!
# Longobardi (2001): How Comparative Is Semantics?

This file formalizes the parametric theory of bare nouns and proper names of
[longobardi-2001]. A nominal argument is either referential, a constant denoting through the
lexical reference of its head, or quantificational, a variable bound by an existential or a
generic operator (`ArgumentType`). A quantificational bare noun has the existential reading
where the predicate is stage-level and the generic reading where the environment is
characterizing, habitual aspect, an adverb of generality, or an eventive individual-level
predicate, the tables (11) and (32), and nothing with a stative individual-level or a
kind-level predicate (`Environment`, `quantReadings`); a referential bare noun is a kind name
and generic everywhere (44). Romance bare nouns are only quantificational, English bare nouns
may also be referential (44), which reduces to whether D carries strong referential features
(`DPParameter`, `bnReadings`): Romance bare nouns read exactly as overt indefinites
(`romance_eq_indefinite`, (5a)), are generic only in characterizing environments
(`romance_gen_iff`, (5c)), and are existential exactly with stage-level predicates
(`ex_iff_stageLevel`, (14a)), while English bare nouns are generic everywhere and the two
languages differ exactly in the non-characterizing environments (`english_gen`,
`contrast_iff`, (48)). Kind anaphora requires a kind-referring antecedent, so only English
bare nouns and Romance definites license the species reading (`species_iff`, (22), (24),
(37)). The syntax of proper names and the semantics of bare nouns are one parameter:
object-referring nouns occur without a filled D exactly when kind-referring nouns can
(`typological_generalization`, (56)), and a strong D whose adjectives are opaque to
N-raising forces an article on every proper name, the Greek prediction (61), (65)
(`pnRequiresArticle_greek`). The rows of `Data/Examples/Longobardi2001` are the paper's
paradigms, and the readings they record are the ones the parameter predicts
(`readings_predicted`, `definite_generic`, `species_rows`, `greek_names`); the parameter also
fixes the nominal mapping [chierchia-1998] gives Romance and English (`toNominalMapping`,
`chierchia_mappings`).

## Implementation notes

The two parameters are Boolean coordinates of the paper's table (61), the Celtic setting of
fn. 35 being the fourth cell. The Greek definite of (64b), ungrammatical on its generic
reading in an episodic sentence, is recorded but not predicted, the paper's claim (40a) about
definite generics in episodic sentences being made for Romance. Reading availability counts
the paper's marginal readings as available.

## References

* [longobardi-2001]
* [chierchia-1998]
* [carlson-1977]
* [gerstner-krifka-1987]
-/

@[expose] public section

namespace Longobardi2001

open Genericity

/-- The semantic type of a nominal argument: a constant denoting through the lexical
reference of its head, or a variable bound by an existential or generic operator. -/
inductive ArgumentType where
  | referential
  | quantificational
  deriving DecidableEq, Repr

/-- The parameters of table (61): whether D carries strong referential features, and whether
the constituent between D and N is transparent to N-raising. -/
structure DPParameter where
  strongD : Bool
  transparentAlpha : Bool
  deriving DecidableEq, Repr

/-- Romance: strong D, transparent α. -/
def romance : DPParameter := ⟨true, true⟩

/-- English: weak D, opaque α. -/
def english : DPParameter := ⟨false, false⟩

/-- Greek: strong D, opaque α, the intermediate case of (61). -/
def greek : DPParameter := ⟨true, false⟩

/-- Celtic: weak D, transparent α, the other intermediate case (fn. 35). -/
def celtic : DPParameter := ⟨false, true⟩

/-- Bare nouns may be referential, kind names, exactly when D is weak (44). -/
def BnCanBeReferential (dp : DPParameter) : Prop := dp.strongD = false

/-- Proper names need a phonetically filled D, by raising or an expletive article, exactly
when D is strong (55). -/
def PnRequiresOvertD (dp : DPParameter) : Prop := dp.strongD = true

/-- Proper names need an overt article when D is strong and N cannot raise to it. -/
def PnRequiresArticle (dp : DPParameter) : Prop :=
  dp.strongD = true ∧ dp.transparentAlpha = false

instance : DecidablePred BnCanBeReferential := λ _ => inferInstanceAs (Decidable (_ = _))
instance : DecidablePred PnRequiresOvertD := λ _ => inferInstanceAs (Decidable (_ = _))
instance : DecidablePred PnRequiresArticle := λ _ => inferInstanceAs (Decidable (_ ∧ _))

/-- The argument types available to a bare noun. -/
def bnArgumentTypes (dp : DPParameter) : Finset ArgumentType :=
  if dp.strongD then {.quantificational} else {.referential, .quantificational}

/-- The typological generalization (56): object-referring nouns occur without a filled D
exactly when kind-referring nouns can. -/
theorem typological_generalization (dp : DPParameter) :
    ¬ PnRequiresOvertD dp ↔ BnCanBeReferential dp := by
  cases h : dp.strongD <;> simp [PnRequiresOvertD, BnCanBeReferential, h]

/-- Strong D with opaque adjectives forces an article on Greek proper names but not on Romance or
English ones (65). -/
theorem pnRequiresArticle_greek :
    PnRequiresArticle greek ∧ ¬ PnRequiresArticle romance ∧ ¬ PnRequiresArticle english := by
  decide

/-! ### Environments and readings -/

/-- The environments of the paper's paradigms: an episodic stage-level predicate, habitual
aspect, an adverb of generality, an eventive (class A) or a stative (class B)
individual-level predicate, and a kind-level predicate. -/
inductive Environment where
  | episodic
  | habitual
  | adverbial
  | iLevelA
  | iLevelB
  | kindLevel
  deriving DecidableEq, Repr

/-- Whether the predicate is stage-level. -/
def Environment.StageLevel : Environment → Prop
  | .episodic | .habitual | .adverbial => True
  | _ => False

/-- Whether the environment is characterizing, (32): habitual aspect, an adverb of
generality, or an eventive individual-level predicate. -/
def Environment.Characterizing : Environment → Prop
  | .habitual | .adverbial | .iLevelA => True
  | _ => False

instance : DecidablePred Environment.StageLevel := λ e => by
  cases e <;> unfold Environment.StageLevel <;> infer_instance

instance : DecidablePred Environment.Characterizing := λ e => by
  cases e <;> unfold Environment.Characterizing <;> infer_instance

/-- The existential and generic readings. -/
inductive Reading where
  | ex
  | gen
  deriving DecidableEq, Repr

/-- The readings of a quantificational nominal, (11), (14) and (46): existential with a
stage-level predicate, generic in a characterizing environment. -/
def quantReadings (e : Environment) : Finset Reading :=
  (if e.StageLevel then {.ex} else ∅) ∪ (if e.Characterizing then {.gen} else ∅)

/-- The readings of a bare noun under a parameter, (45) and (46): those of a variable, and
the generic reading of a kind name wherever the noun may be referential. -/
def bnReadings (dp : DPParameter) (e : Environment) : Finset Reading :=
  quantReadings e ∪ (if BnCanBeReferential dp then {.gen} else ∅)

/-- (5a): Romance bare nouns read exactly as overt indefinites in every environment. -/
theorem romance_eq_indefinite (e : Environment) : bnReadings romance e = quantReadings e := by
  simp [bnReadings, BnCanBeReferential, romance]

/-- (14a): a bare noun is existential exactly with a stage-level predicate, whatever the
parameter. -/
theorem ex_iff_stageLevel (dp : DPParameter) (e : Environment) :
    .ex ∈ bnReadings dp e ↔ e.StageLevel := by
  cases e <;> cases h : dp.strongD <;>
    simp [bnReadings, quantReadings, BnCanBeReferential, h, Environment.StageLevel,
      Environment.Characterizing]

/-- (5c): Romance bare nouns are generic only in characterizing environments. -/
theorem romance_gen_iff (e : Environment) : .gen ∈ bnReadings romance e ↔ e.Characterizing := by
  cases e <;>
    simp [bnReadings, quantReadings, BnCanBeReferential, romance, Environment.StageLevel,
      Environment.Characterizing]

/-- (48): English bare nouns are generic in every environment. -/
theorem english_gen (e : Environment) : .gen ∈ bnReadings english e := by
  cases e <;>
    simp [bnReadings, quantReadings, BnCanBeReferential, english, Environment.StageLevel,
      Environment.Characterizing]

/-- The two languages' bare nouns differ exactly in the non-characterizing environments, the
episodic, stative, and kind-level predicates of (48). -/
theorem contrast_iff (e : Environment) :
    bnReadings romance e ≠ bnReadings english e ↔ ¬ e.Characterizing := by
  cases e <;>
    simp [bnReadings, quantReadings, BnCanBeReferential, romance, english,
      Environment.StageLevel, Environment.Characterizing]
  decide

-- (63)
theorem greek_eq_romance (e : Environment) : bnReadings greek e = bnReadings romance e := rfl

/-- The species reading of an anaphor, (22), (24), (37): available to a bare-noun antecedent
exactly when the noun may be a kind name, and always to a definite. -/
def SpeciesReading (dp : DPParameter) : ArgumentType → Prop
  | .referential => True
  | .quantificational => BnCanBeReferential dp

instance (dp : DPParameter) : DecidablePred (SpeciesReading dp) := λ t => by
  cases t <;> unfold SpeciesReading <;> infer_instance

theorem species_iff (dp : DPParameter) :
    (∃ t ∈ bnArgumentTypes dp, SpeciesReading dp t) ↔ BnCanBeReferential dp := by
  cases h : dp.strongD <;> simp [bnArgumentTypes, SpeciesReading, BnCanBeReferential, h]

/-! ### The paradigms -/

/-- The parameter of a row's language. -/
def paramOf (e : Datum) : Option DPParameter :=
  e.byLanguage [(.italian, romance), (.english, english), (.modernGreek, greek)]

/-- The environment a row records. -/
def environmentOf (e : Datum) : Option Environment :=
  e.parse? "environment"
    [("episodic", .episodic), ("habitual", .habitual), ("adverbial", .adverbial),
     ("iLevelA", .iLevelA), ("iLevelB", .iLevelB), ("kindLevel", .kindLevel)]

/-- A reading the row records as available, the paper's marginal readings included. -/
def Available (e : Datum) (name : String) : Prop :=
  ∃ r ∈ e.readings, r.1 = name ∧ (r.2 = .acceptable ∨ r.2 = .marginal)

instance (e : Datum) (name : String) : Decidable (Available e name) :=
  List.decidableBEx _ _

/-- The predicted readings of a bare-noun or overt-indefinite row. -/
def predictedOf (e : Datum) : Option (Finset Reading) := do
  let dp ← paramOf e
  let env ← environmentOf e
  match e.feature? "nominal" with
  | some "bareNoun" => some (bnReadings dp env)
  | some "overtIndefinite" => some (quantReadings env)
  | _ => none

theorem readings_predicted :
    ∀ e ∈ Examples.all, ∀ p ∈ predictedOf e,
      (Available e "Ex" ↔ .ex ∈ p) ∧ (Available e "Gen" ↔ .gen ∈ p) := by
  decide

/-- (5d), (34) to (36): Italian definites are generic in every environment, kind-level and
episodic included. -/
theorem definite_generic :
    ∀ e ∈ Examples.all, e.language = .italian → e.feature? "nominal" = some "definite" →
      ∀ _ ∈ environmentOf e, Available e "Gen" := by
  decide

/-- The anaphora rows (22), (24), (25) and (37): the species reading goes with a definite or
with a bare noun of a weak-D language. -/
theorem species_rows :
    ∀ e ∈ Examples.all, e.feature? "environment" = some "kindAnaphora" → ∀ dp ∈ paramOf e,
      (Available e "species" ↔
        e.feature? "nominal" = some "definite" ∨
          (e.feature? "nominal" = some "bareNoun" ∧ BnCanBeReferential dp)) := by
  decide

/-- (65): a Greek proper name without its article is ungrammatical. -/
theorem greek_names :
    ∀ e ∈ Examples.all, e.feature? "nominal" = some "properName" →
      e.feature? "article" = some "absent" → e.judgment = .ungrammatical := by
  decide

/-! ### The nominal mapping -/

/-- The nominal mapping of [chierchia-1998] the parameter determines: with strong D nouns are
predicates needing D for argumenthood, with weak D they may be arguments on their own. -/
def toNominalMapping (dp : DPParameter) : NominalMapping :=
  if dp.strongD then .predOnly else .argAndPred

theorem chierchia_mappings :
    toNominalMapping romance = Chierchia1998.Language.nominalMapping .italian ∧
      toNominalMapping english = Chierchia1998.Language.nominalMapping .english := ⟨rfl, rfl⟩

end Longobardi2001
