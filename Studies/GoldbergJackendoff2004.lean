module

public import Linglib.Semantics.ArgumentStructure.EntailmentProfile.ThetaRole
public import Linglib.Semantics.ArgumentStructure.Linking
public import Linglib.Semantics.Mereology.Basic
public import Linglib.Syntax.Category.Verb.Argument
public import Linglib.Languages.English.Verbs.Inventory
public import Linglib.Data.Examples.GoldbergJackendoff2004
public import Studies.Goldberg1995
public import Linglib.Data.Examples.Readers

/-!
# Goldberg and Jackendoff (2004): The English Resultative as a Family of Constructions

A *resultative* is a sentence such as *The gardener watered the flowers flat*, in which a result
phrase says what becomes of one of the participants, the *host*. The result phrase names a
property that the host comes to have or a path that it traverses. The construction is *causative*
if the subject causes the change of the host, which is then the object.

We define the four subconstructions of the family, given by whether the construction is causative
and by what the result phrase names, together with their argument structures. We define a path
resultative from a map `σ` that sends an event to its path: the resultative holds of an event of
the verb if the result phrase describes the path of the event. Suppose that `σ` preserves joins.
We prove that the resultative is quantized if `σ` is injective and the result phrase is
quantized, and that it is cumulative if the verb and the result phrase are cumulative.

The paper's examples are the rows of this file. We prove that a row accepts a for-adverbial if
and only if its result phrase is not end-bounded, and that every other row is acceptable if and
only if its roles cohere with the roles of its construction.

## Implementation notes

The verbal subevent and the constructional subevent are one event, which is the case the paper
calls a cotemporal means. End-boundedness is quantization and its absence is cumulativity, as in
Krifka's reading of the homomorphism from events to paths.

The paper labels result phrases only as AP or PP. A row's subconstruction follows the paper's
summary of the family, where a PP that names a state, such as *into pieces* or *to death*, is a
property result phrase.

A row's `subjectRole` and `objectRole` are the paper's construals of the arguments of the verb:
an argument is something that acts, an agent, or something to which something happens, a patient.

The causative property resultative is the resultative of [goldberg-1995]. The path resultatives
take the frames of its caused motion and intransitive motion constructions. Where Goldberg labels
the moving host a theme, the roles here are the paper's.

## TODO

* The temporal relations that the relation between the subevents allows: a means does not follow
  the subevent it brings about, and a result does not precede its cause.
* Full argument realization, which excludes some of the paper's starred examples and restates the
  Correspondence Principle of [goldberg-1995]. See `ArgumentStructure.Corresponds`.
* The stative extension readings, and the *follow* subconstructions, which are transitive but not
  causative.

## References

* [goldberg-jackendoff-2004]
* [goldberg-1995]
* [jackendoff-1996]
* [krifka-1998]
-/

@[expose] public section

namespace GoldbergJackendoff2004

open Examples (ObjectSelection)

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

open Mereology

variable {E P : Type*} [SemilatticeSup E] [SemilatticeSup P] (σ : SupHom E P)
  {V : E → Prop} {R : P → Prop}

/-- `resultative σ V R e` holds when `e` is an event of the verb whose path `σ e`, the path of the
constructional subevent, is one the result phrase describes, the two subevents being
cotemporal. -/
def resultative (V : E → Prop) (R : P → Prop) (e : E) : Prop :=
  V e ∧ R (σ e)

/-- If the path of an event is injective on events, an end-bounded result phrase makes the
resultative telic (27). -/
theorem qua_resultative (hinj : Function.Injective σ) (hR : QUA {p | R p}) :
    QUA {e | resultative σ V R e} :=
  IsAntichain.subset
    (QUA.preimage ((OrderHomClass.monotone σ).strictMono_of_injective hinj) hR)
    fun _ h ↦ h.2

/-- A non-end-bounded result phrase leaves the resultative of an activity atelic (27). -/
theorem cum_resultative (hV : CUM {e | V e}) (hR : CUM {p | R p}) :
    CUM {e | resultative σ V R e} :=
  SupClosed.inter hV (hR.preimage σ)

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
         selection := (Examples.selection ex)
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

-- (48b)
theorem rows_thetaLabels :
    ∀ r ∈ rows, ∀ ρs ∈ r.objectRole, ∀ s ∈ r.verb.coreSlots[1]?,
      (r.verb.thetaLabels s).Nonempty → ¬ Disjoint ρs (r.verb.thetaLabels s) := by
  decide +kernel

end GoldbergJackendoff2004
