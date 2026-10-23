module

public import Linglib.Semantics.ArgumentStructure.EntailmentProfile.ThetaRole
public import Linglib.Semantics.ArgumentStructure.Linking
public import Linglib.Semantics.Events.Path
public import Linglib.Semantics.Mereology
public import Linglib.Syntax.Category.Verb.Argument
public import Linglib.Fragments.English.Verbs.Inventory
public import Linglib.Data.Examples.GoldbergJackendoff2004
public import Studies.Goldberg1995

/-!
# Goldberg and Jackendoff (2004): The English Resultative as a Family of Constructions

Goldberg and Jackendoff analyze the English resultative as a family of constructions. A resultative
has a verbal subevent supplied by the verb and a constructional subevent supplied by the
construction, in which a host comes to have the property the result phrase names or traverses the
path it names, caused by the subject in the transitive cases. The constructional subevent controls
the aspect of the sentence: the event measures out the result phrase's path, so an end-bounded
result phrase makes a resultative telic and one that is not leaves an activity atelic. Under the
principle of semantic coherence a verb role unifies with a constructional role only if it can be
construed as an instance of it, so the intransitive path resultative admits more verbs than the
intransitive property resultative.

## Main definitions

* `Subconstruction`, `Subconstruction.link`: the four subconstructions of the family, and their
  argument structures.
* `resultative`: the resultative over a path trace.
* `Row.Coheres`: the coherence of a row's roles with those of its construction.

## Main results

* `qua_resultative`: an end-bounded result phrase makes the resultative telic.
* `cum_resultative`: a result phrase that is not end-bounded leaves an activity atelic.
* `rows_for_adverbial`: the for-adverbial is acceptable exactly on the atelic rows.
* `coheres_noncausative_path`: the intransitive path resultative is the more liberal.
* `rows_coherence`: outside the telicity tests, a row is acceptable exactly when its roles cohere.

## Implementation notes

The verbal and constructional subevents are identified as one event, the paper's cotemporal means
(§4.2). End-boundedness is rendered by quantization and its absence by cumulativity, the reading
Krifka gives the event-path homomorphism that the paper takes from Jackendoff. The path of an event
is its spatial trace `Event.σ`, and its preservation of sums a hypothesis. The paper labels result
phrases only as AP or PP; a row's subconstruction follows the summary (97), where a PP naming a
state (*into pieces*, *to death*) is a property result phrase, and the paper presents the examples
(49) as transitive spatial resultatives. A row's `subjectRole` and `objectRole` are the paper's
construals of the verb's arguments, per verb and referent: whether the argument is something that
acts, an agent, or something to which something happens, a patient. The causative property
resultative is the resultative of [goldberg-1995], and the path resultatives take the frames of its
caused motion and intransitive motion constructions, which (97) names them as; where Goldberg
labels the moving host a theme, the roles here are those of §6.2.

## TODO

- The temporal relations the subevent relation allows (33): a means does not follow the subevent it
  effects, and a result does not precede its cause.
- Full argument realization (37), which excludes (41d) and (43b,c), the Correspondence Principle
  of [goldberg-1995] in another form (fn. 20, `ArgumentStructure.Corresponds`).
- The stative extension readings (25), and the *follow* subconstructions (52), (55) and (56), which
  are transitive but not causative.

## References

* [goldberg-jackendoff-2004]
* [goldberg-1995]
* [jackendoff-1996]
* [krifka-1998]
-/

@[expose] public section

namespace GoldbergJackendoff2004

open ArgumentStructure
open English
open English.Verbs hiding Verb

/-! ### The family -/

/-- Whether the result phrase names a property the host comes to have or a path it traverses. -/
inductive RPType where
  | property
  | path
  deriving DecidableEq, Repr

/-- A `Subconstruction` of the summary (97) records whether the subject causes the host's change,
and what the result phrase names. The causative ones are `X CAUSE [Y BECOME Z]` and
`X CAUSE [Y GO Path]`, the noncausative ones `X BECOME Y` and `X GO Path`. -/
structure Subconstruction where
  /-- Whether the subject causes the change of the host, which is then the object. -/
  causative : Bool
  /-- What the result phrase names. -/
  rp : RPType
  deriving DecidableEq, Repr

/-- How the object of a transitive resultative is selected (§2). By §5 the fake reflexive is not
grammatically special: another object is excluded because it is implausible to make someone
else fall asleep by crying. -/
inductive ObjectSelection where
  /-- The verb selects the object: *The gardener watered the flowers flat*, (7a). -/
  | selected
  /-- Only the construction licenses the object: *They drank the pub dry*, (8a). -/
  | unselected
  /-- An unselected reflexive that alternates with no other object, as in *We yelled ourselves
  hoarse*, (9a). -/
  | fakeReflexive
  deriving DecidableEq, Repr

/-! ### Semantic coherence

The principle of semantic coherence (44): a verb role, given by the roles it can be construed as,
unifies with a constructional role, given by the roles that are instances of it, only if some
construal of the verb role is an instance of the constructional role, that is, only if the two
sets of roles are not disjoint (`ArgumentStructure.Coherent`). -/

/-- The argument structure of a subconstruction (97), whose subject the verb shares (§6.1). The
causative property resultative is the resultative of [goldberg-1995], and the path resultatives
have the frames of its caused motion and intransitive motion constructions (p. 563). A causer is
an agent and a caused host a patient, the host of BECOME is a patient, and the host of an uncaused
GO is an agent or a patient, as the subject of an intransitive motion verb is (§6.2). -/
def Subconstruction.link : Subconstruction → LinkedFrame
  | ⟨true, .property⟩ => Goldberg1995.resultative.meaning.link
  | ⟨true, .path⟩ =>
    { Goldberg1995.causedMotion.meaning.link with
      roles := [(.external, ⟨{.agent}, true⟩), (.complement 0, ⟨{.patient}, false⟩),
        (.complement 1, ⟨{.goal}, false⟩)] }
  | ⟨false, .property⟩ =>
    { frame := .smallClause
      roles := [(.external, ⟨{.patient}, true⟩), (.complement 0, ⟨{.goal}, false⟩)] }
  | ⟨false, .path⟩ =>
    { Goldberg1995.intransitiveMotion.meaning.link with
      roles := [(.external, ⟨{.agent, .patient}, true⟩), (.complement 0, ⟨{.goal}, false⟩)] }

/-- A subject role compatible with the intransitive property resultative is compatible with the
intransitive path resultative (§6.2). -/
theorem coheres_noncausative_path {rV : Finset ThetaRole}
    (h : ¬ Disjoint rV ((⟨false, .property⟩ : Subconstruction).link.admits .external)) :
    ¬ Disjoint rV ((⟨false, .path⟩ : Subconstruction).link.admits .external) :=
  fun hd ↦ h (hd.mono_right (by decide))

/-- An agent subject, as of *yell*, is compatible with GO but not with BECOME. -/
example : ¬ Disjoint {.agent} ((⟨false, .path⟩ : Subconstruction).link.admits .external) ∧
    Disjoint {.agent} ((⟨false, .property⟩ : Subconstruction).link.admits .external) := by
  decide

/-! ### Aspect -/

section Aspect

open Mereology Spatial
open Event (σ)

variable {E Loc : Type*} [SemilatticeSup E] [SemilatticeSup (Path Loc)] [Event.SpatialTrace E Loc]
  {V : E → Prop} {R : Path Loc → Prop}

/-- `resultative V R e` holds when `e` is an event of the verb whose path `σ e`, the path of the
constructional subevent, is one the result phrase describes, the two subevents being
cotemporal. -/
def resultative (V : E → Prop) (R : Path Loc → Prop) (e : E) : Prop :=
  V e ∧ R (σ e)

/-- If paths are additive and injective on events, an end-bounded result phrase makes the
resultative telic (27). -/
theorem qua_resultative (hσ : ∀ e e' : E, σ (e ⊔ e') = σ e ⊔ σ e')
    (hinj : Function.Injective (σ : E → Path Loc)) (hR : QUA R) : QUA (resultative V R) :=
  IsAntichain.subset
    (qua_pullback ((OrderHomClass.monotone (SupHom.mk σ hσ)).strictMono_of_injective hinj) hR)
    fun _ h ↦ h.2

/-- If paths are additive, a non-end-bounded result phrase leaves the resultative of an activity
atelic (27). -/
theorem cum_resultative (hσ : ∀ e e' : E, σ (e ⊔ e') = σ e ⊔ σ e') (hV : CUM V) (hR : CUM R) :
    CUM (resultative V R) :=
  SupClosed.inter hV (hR.preimage (SupHom.mk σ hσ))

end Aspect

/-! ### The examples -/

/-- A `Row` records an example's verb, subconstruction, the relation of its subevents, the object
selection of a transitive, whether the result phrase is end-bounded where the paper tests
telicity, the paper's construals of the verb's subject and object where it discusses them, and
the judgment. -/
structure Row where
  verb : English.Verbs.Verb
  subconstruction : Subconstruction
  relation : SubeventRelation
  selection : Option ObjectSelection
  endBounded : Option Bool
  subjectRole : Option (Finset ThetaRole)
  objectRole : Option (Finset ThetaRole)
  judgment : Judgment

/-- `verbs` lists the paper's verbs by citation form. -/
def verbs : List (String × English.Verbs.Verb) :=
  [("hammer", hammer), ("laugh", laugh), ("freeze", freeze), ("roll", roll), ("water", water),
   ("break", break_), ("drink", drink), ("talk", talk), ("yell", yell), ("heat", heat),
   ("weave", weave), ("float", float), ("push", push), ("cry", cry), ("bleed", bleed),
   ("cough", cough), ("wriggle", wriggle), ("melt", melt), ("wiggle", wiggle), ("wipe", wipe),
   ("rumble", rumble)]

/-- The construals of a verb role the rows record. -/
def construals : List (String × Finset ThetaRole) :=
  [("agent", {.agent}), ("patient", {.patient}), ("agent or patient", {.agent, .patient})]

/-- The row an example encodes, when its features parse. -/
def Row.ofDatum (ex : Datum) : Option Row := do
  let verb ← ex.parse? "verb" verbs
  let subconstruction ← ex.parse? "subconstruction"
    [("causative property", ⟨true, .property⟩), ("causative path", ⟨true, .path⟩),
     ("noncausative property", ⟨false, .property⟩), ("noncausative path", ⟨false, .path⟩)]
  pure { verb, subconstruction
         relation := (ex.parse? "subeventRelation" [("result", .result)]).getD .means
         selection := ex.parse? "selection"
           [("selected", .selected), ("unselected", .unselected),
            ("fake reflexive", .fakeReflexive)]
         endBounded := ex.parse? "endBounded" [("true", true), ("false", false)]
         subjectRole := ex.parse? "subjectRole" construals
         objectRole := ex.parse? "objectRole" construals
         judgment := ex.judgment }

/-- `rows` lists the paper's examples (5)–(9), (23)–(24), (45)–(49), (97c), and *wipe the table
clean*. -/
def rows : List Row := Examples.all.filterMap Row.ofDatum

example : rows.length = Examples.all.length := by decide

-- Object selection is a dimension of the transitive, that is causative, subconstructions.
example : ∀ r ∈ rows, r.selection.isSome → r.subconstruction.causative := by decide

/-- By §4.1, on a nonrepetitive reading the for-adverbial is acceptable exactly when the result
phrase is not end-bounded, that is, when the resultative is atelic. -/
theorem rows_for_adverbial :
    ∀ r ∈ rows, ∀ b ∈ r.endBounded, r.judgment = .acceptable ↔ b = false := by
  decide

/-- The paper's construals of a row's subject and object, in the positions of its
construction. -/
def Row.construal (r : Row) : LinkedFrame :=
  { r.subconstruction.link with
    roles := (r.subjectRole.map fun ρ ↦ (.external, ⟨ρ, true⟩)).toList ++
      (r.objectRole.map fun ρ ↦ (.complement 0, ⟨ρ, true⟩)).toList }

/-- A row coheres when each argument the paper construes coheres with the construction's argument
in its position. -/
def Row.Coheres (r : Row) : Prop :=
  Coherent r.construal r.subconstruction.link (r.construal.roles.map Prod.fst).toFinset.diag

instance (r : Row) : Decidable r.Coheres := inferInstanceAs (Decidable (Coherent ..))

/-- By §6.2, outside the telicity tests an example is acceptable exactly when its roles
cohere. -/
theorem rows_coherence :
    ∀ r ∈ rows, r.endBounded = none → (r.judgment = .acceptable ↔ r.Coheres) := by
  decide +kernel

/-- Where the fragment derives an object role label from the verb's basic frame, the label is among
the paper's construals, though subject labels may differ, as in (48b). -/
theorem rows_thetaLabel :
    ∀ r ∈ rows, ∀ ρs ∈ r.objectRole, ∀ s ∈ r.verb.coreSlots[1]?, ∀ ρ ∈ r.verb.thetaLabel s,
      ρ ∈ ρs := by
  decide +kernel

end GoldbergJackendoff2004
