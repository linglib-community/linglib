module

public import Linglib.Semantics.Genericity.Normality
public import Linglib.Semantics.Aspect.Viewpoint
public import Linglib.Semantics.Mereology
public import Linglib.Semantics.Modality.Necessity

/-!
# Boneh and Doron 2013: Hab and Gen in the expression of habituality

Boneh and Doron argue that habituality involves two covert operators. Gen is the familiar
modalized universal. Hab is a modalized existential over sums of events: an iteration in every
world of a gnomic modal base, with only an initiating event that indicates a disposition in the
actual world. The English auxiliaries mark neither; *would* marks mood, a special case of Gen,
and *used to* is the imperfective under a retrospective aspect, which places the reference
interval before the perspective interval. The operators are built on Link's sum closure,
Kratzer's modal base, Klein's imperfective and Pancheva's final-subinterval perfect
(`Aspect.perfect`); Del Prete's Italian Same-Object Effect is the configuration of
`same_object_infelicity`.

## Main statements

* `same_object_infelicity`: an indefinite scoping over Hab makes an unrepeatable event recur.
* `gen_admits_fresh_objects`: Gen's universal lets the object vary.
* `hab_without_actual_iteration`: Hab holds with a single actual initiating event.
* `retro_perfect_forces_point`: the retrospective and the perfect share a reference interval only
  at a degenerate perspective.
* `usedTo_of_persisting_state`: *used to* does not bound the state.

## References

* [boneh-doron-2013]
* [link-1983]
* [kratzer-1981]
* [klein-1994]
* [kamp-reyle-1993]
* [pancheva-2003]
* [del-prete-2013]
-/

@[expose] public section

namespace BonehDoron2013

open Event (τ)

open Aspect (Perfectivity IMPF)
open Modality (Background)

/-! ### Hab against Gen ((4)–(8), (13)–(15))

Gen needs an explicit restrictor; without one only Hab applies, and an
indefinite can only scope over it, as in (8) `∃x [cigarette(x) ∧ Hab e
smoke(e, Mary, x)]`. The contrast between (4a) and (4b) is then a theorem:
smoking is unrepeatable per cigarette, so the wide-scope form is
contradictory while Gen's (5a) is satisfiable with a fresh cigarette per
event. -/

/-! Iteration, (14), a sum of P-events with at least two distinct proper P-parts on Link's
closure, is `Mereology.IsPlural`. -/

/-- With the indefinite over Hab, the reading is contradictory for a predicate unrepeatable per
object, such as smoking a cigarette ((4b), (8)). -/
theorem same_object_infelicity {E C : Type*} [SemilatticeSup E]
    {smoke : E → C → Prop} {cig : C → Prop}
    (hOnce : ∀ c e₁ e₂, smoke e₁ c → smoke e₂ c → e₁ = e₂) :
    ¬ ∃ c, cig c ∧ ∃ e, Mereology.IsPlural (smoke · c) e :=
  fun ⟨c, _, e, hIter⟩ => Mereology.not_isPlural_of_subsingleton (hOnce c) e hIter

/-- Gen holds at the interval `i` and world `w` when every `Q`-individual temporally included in
`i` is a `P`-individual throughout the gnomic modal base of `i` at `w`, (21). It is GEN with
every case normal and its modality in the matrix. -/
def gen {W Z T : Type*} (P Q : Z → W → Prop) (τ : Z → Set T) (mb : Set T → Background W)
    (i : Set T) (w : W) : Prop :=
  (i, w) ∈ (⊤ : Genericity.Normality (Set T × W) Z).gen {z | τ z ⊆ i ∧ Q z w}
    {z | Modality.simpleNecessity (mb i) (P z) w}

/-- Gen's universal lets the indefinite scope below it, so the unrepeatability premise is
satisfiable with a fresh cigarette per event, (4a), (5a). -/
theorem gen_admits_fresh_objects :
    ∃ smoke : Bool → Bool → Prop, (∀ c e₁ e₂, smoke e₁ c → smoke e₂ c → e₁ = e₂) ∧
      gen (W := Unit) (fun e _ ↦ ∃ c, smoke e c) (fun _ _ ↦ True) (fun _ ↦ (∅ : Set Unit))
        (fun _ ↦ ⊥) Set.univ () :=
  ⟨(· = ·), fun _ _ _ h₁ h₂ ↦ h₁.trans h₂.symm, fun e _ _ _ ↦ ⟨e, rfl⟩⟩

/-- Hab holds when an initiating event that indicates a disposition occurs in the actual world
and an iteration occurs in every accessible world of the gnomic modal base, (13), (15). The paper
leaves "indicating a disposition" unanalyzed, so it is a parameter, and the temporal anchoring
`τ(s) ⊆ τ(e)` is dropped with the event times. -/
def hab {W E : Type*} [SemilatticeSup E] (P : E → W → Prop) (mb : Background W)
    (indicatesDisposition : W → Prop) (w : W) : Prop :=
  indicatesDisposition w ∧ ∀ w' ∈ mb.accessibleWorlds w, ∃ e, Mereology.IsPlural (P · w') e

/-- Hab is dispositional, holding on a single actual initiating event with the iteration only in
the accessible worlds, (16)–(17), (42a–b). -/
theorem hab_without_actual_iteration :
    ∃ (P : Finset ℕ → Bool → Prop) (mb : Background Bool),
      hab P mb (· = false) false ∧ ¬ ∃ e, Mereology.IsPlural (P · false) e := by
  refine ⟨fun e w' => match w' with | true => e.Nonempty ∧ e ⊆ {0, 1} | false => e = {0},
    fun _ => {(· = true)}, ⟨rfl, ?_⟩, ?_⟩
  · intro w' hw'
    have hw : w' = true := by
      simpa using hw'
    subst hw
    exact ⟨{0} ⊔ {1}, .sum (.base (by decide)) (.base (by decide)),
      {0}, by decide, {1}, by decide, by decide, by decide, by decide⟩
  · rintro ⟨e, -, e₁, -, e₂, -, h₁, h₂, hne⟩
    exact hne (h₁.trans h₂.symm)

/-! ### used to: the imperfective under a retrospective ((18)–(19), (30)–(35))

The auxiliary is the retrospective over the imperfective. The imperfective (19a) is Klein's,
`IMPF`, and the retrospective (19b) places the reference interval before the perspective
interval, Kamp and Reyle's P, so *used to* is imperfective and retrospective by construction. -/

/-- The retrospective holds at a perspective interval when some reference interval satisfying
the description lies wholly before it, (19b). -/
def retro {W T : Type*} [LinearOrder T] (A : W → Set (NonemptyInterval T)) :
    W → Set (NonemptyInterval T) :=
  fun w ↦ {p | ∃ i ∈ A w, i.IsBefore p}

/-- *Used to* is the retrospective over the imperfective, (18). -/
def usedToOp {W T E : Type*} [LinearOrder T] [Event.TemporalTrace E T] (P : W → E → Prop) :
    W → Set (NonemptyInterval T) :=
  retro (IMPF P)

/-- One reference interval serves both the retrospective and the perfect only for an instantaneous
perspective ((32)–(34); see (31)–(33)). -/
theorem retro_perfect_forces_point {T : Type*} [LinearOrder T]
    {i p : NonemptyInterval T} (hb : i.IsBefore p) (hf : p.FinalSubinterval i) :
    p.IsPoint :=
  le_antisymm p.fst_le_snd (hf.2.trans_le hb)

/-- A state persisting past the perspective still satisfies *used to*, so retrospectivity is
cancellable ((30), (19a)). -/
theorem usedTo_of_persisting_state {W T E : Type*} [LinearOrder T] [Event.TemporalTrace E T]
    {P : W → E → Prop} {w : W} {e : E} (hP : P w e)
    {i p : NonemptyInterval T} (hie : i < τ e) (hip : i.IsBefore p) :
    p ∈ usedToOp P w :=
  ⟨i, ⟨e, hie, hP⟩, hip⟩

/-! ### The three forms and Table (41) -/

/-- A `HabitualForm` is one of the English past-habituality forms of (1). -/
inductive HabitualForm where
  | simpleForm
  | usedTo
  | would
  deriving DecidableEq, Repr

/-- A perspective is internal or retrospective, the second dimension of Table (41). -/
inductive PerspectiveType where
  | internal
  | retrospective
  deriving DecidableEq, Repr

/-- `admitsViewpoint f v` says that the form `f` admits the viewpoint `v`, the viewpoint column
of Table (41). The simple form takes either viewpoint, (26)–(27), and the periphrastic forms
only the imperfective. -/
def admitsViewpoint : HabitualForm → Perfectivity → Prop
  | .simpleForm, _ => True
  | _, .imperfective => True
  | _, .perfective => False

/-- `admitsPerspective f p` says that the form `f` admits the perspective `p`, the perspective
column of Table (41). *Used to* is retrospective, *would* internal and the simple form either,
(35)–(40). -/
def admitsPerspective : HabitualForm → PerspectiveType → Prop
  | .simpleForm, _ => True
  | .usedTo, .retrospective => True
  | .usedTo, .internal => False
  | .would, .internal => True
  | .would, .retrospective => False

/-! ### The chapter's judgments -/

/-- An `EnglishDatum` records an English judgment from the chapter. -/
structure EnglishDatum where
  sentence : String
  form : HabitualForm
  felicitous : Bool
  exNumber : String
  deriving Repr

/-- *Mary smokes a cigarette after dinner*, (4a), is felicitous, since *after dinner* supplies
Gen's restrictor and the indefinite scopes below it, as in (5a). -/
def maryCigaretteAfterDinner : EnglishDatum :=
  { sentence := "Mary smokes a cigarette after dinner"
    form := .simpleForm, felicitous := true, exNumber := "(4a)" }

/-- *Mary smokes a cigarette*, (4b), is infelicitous, since with no explicit restrictor only Hab
applies and the indefinite scopes over it, (8). -/
def maryCigarette : EnglishDatum :=
  { sentence := "#Mary smokes a cigarette"
    form := .simpleForm, felicitous := false, exNumber := "(4b)" }

/-- *A flower grows out behind the old shed*, (6b), survives on its plausible same-object
reading, one flower growing out repeatedly. -/
def flowerGrows : EnglishDatum :=
  { sentence := "A flower grows out behind the old shed"
    form := .simpleForm, felicitous := true, exNumber := "(6b)" }

/-- *Max killed a rabbit repeatedly*, (7b), is infelicitous, since the indefinite scopes over the
adverbial's quantifier and the same rabbit would be killed repeatedly. -/
def maxKilledRabbit : EnglishDatum :=
  { sentence := "#Max killed a rabbit repeatedly"
    form := .simpleForm, felicitous := false, exNumber := "(7b)" }

/-- *In the good old days, people would dress elegantly*, (2c), is infelicitous, since *would*
requires its restricting episodes to be explicit or presupposed and nothing supplies them. -/
def wouldDressNoContext : EnglishDatum :=
  { sentence := "#In the good old days, people would dress elegantly"
    form := .would, felicitous := false, exNumber := "(2c)" }

/-- With a purpose clause, (2d), the restriction is supplied. -/
def wouldDressWithContext : EnglishDatum :=
  { sentence := "In the good old days, people would dress elegantly to go to the opera"
    form := .would, felicitous := true, exNumber := "(2d)" }

/-- *She went to work by bus*, (42a), is true on a single actual episode, read episodically or
with Hab. -/
def sheWentByBus : EnglishDatum :=
  { sentence := "She went to work by bus"
    form := .simpleForm, felicitous := true, exNumber := "(42a)" }

/-- *She would go to work by bus*, (42b), is true on a single episode, since *would* is Gen, about
the accessible worlds rather than an actual iteration. -/
def sheWouldGoByBus : EnglishDatum :=
  { sentence := "She would go to work by bus"
    form := .would, felicitous := true, exNumber := "(42b)" }

/-- *She used to go to work by bus*, (42c), is false on a single episode. The chapter derives the
actualization requirement from the aspect. The retrospective's extended reference interval
characterizes a period, and only actualized episodes can characterize one. -/
def sheUsedToGoByBus : EnglishDatum :=
  { sentence := "She used to go to work by bus"
    form := .usedTo, felicitous := false, exNumber := "(42c)" }

/-- *The London Bridge used to stand on the Thames*, (48a), is felicitous, since *used to* is an
aspectual operator selecting states, individual-level ones included. -/
def usedToStand : EnglishDatum :=
  { sentence := "The London Bridge used to stand on the Thames, now it stands in Arizona"
    form := .usedTo, felicitous := true, exNumber := "(48a)" }

/-- *The London Bridge would stand on the Thames*, (48b), is ungrammatical, since habitual *would*
is Gen, an individual-level predicate is incompatible with an episodic restrictor, and a definite
subject supplies no nominal one. -/
def wouldStand : EnglishDatum :=
  { sentence := "*The London Bridge would stand on the Thames, now it stands in Arizona"
    form := .would, felicitous := false, exNumber := "(48b)" }

/-- In *a French teacher would know Latin*, (3a), (47a), the indefinite singular provides Gen's
restrictor, of objects rather than events, so *would* tolerates the individual-level predicate. -/
def wouldKnowLatin : EnglishDatum :=
  { sentence := "a French teacher would know Latin"
    form := .would, felicitous := true, exNumber := "(3a)/(47a)" }

/-- *A French teacher used to know Latin*, (3b), (47b), is ungrammatical, since *used to* is
aspectual rather than quantificational. The indefinite singular finds no operator below Gen, and
Gen over the whole clause, (50b), gives the wrong truth conditions. A bare plural instead denotes
the kind and combines directly, (50a). -/
def usedToKnowLatin : EnglishDatum :=
  { sentence := "*a French teacher used to know Latin"
    form := .usedTo, felicitous := false, exNumber := "(3b)/(47b)" }

/-- Gen with a restrictor is felicitous and Hab with a wide-scope indefinite is not, (4). -/
theorem restrictor_contrast :
    maryCigaretteAfterDinner.felicitous = true ∧ maryCigarette.felicitous = false :=
  ⟨rfl, rfl⟩

/-- The same-object reading decides felicity, plausible for the flower and absurd for the
rabbit, (6b), (7b). -/
theorem sameObjectParallel :
    flowerGrows.felicitous = true ∧ maxKilledRabbit.felicitous = false :=
  ⟨rfl, rfl⟩

/-- One actual episode verifies the simple form and *would* but not *used to*, (42). -/
theorem actualization_contrast :
    sheWentByBus.felicitous = true ∧ sheWouldGoByBus.felicitous = true ∧
      sheUsedToGoByBus.felicitous = false :=
  ⟨rfl, rfl, rfl⟩

/-- *Used to* selects individual-level states, and habitual *would* cannot restrict Gen with
them, (48). -/
theorem individual_level_contrast :
    usedToStand.felicitous = true ∧ wouldStand.felicitous = false :=
  ⟨rfl, rfl⟩

/-- The indefinite singular restricts Gen under *would* but has no host under aspectual
*used to*, (3), (47). -/
theorem would_vs_usedTo_puzzle :
    wouldKnowLatin.felicitous = true ∧ usedToKnowLatin.felicitous = false :=
  ⟨rfl, rfl⟩

end BonehDoron2013
