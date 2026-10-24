module

public import Linglib.Semantics.ArgumentStructure.LevinClass.Basic
public import Linglib.Semantics.Root.Kinds

/-!
# Root entailments of the Levin classes

The root-entailment signature of [beavers-koontz-garboden-2020] that each class of
[levin-1993] realizes, for the classes the literature has analysed; `none` for the rest.
`LevinClass.RootEntails` reads a single entailment off the signature, and
`LevinClass.RootPredictsCausative` is the root hypothesis for the causative alternation, read
off the signature.

## References

* [beavers-koontz-garboden-2020]
* [levin-1993]
-/

@[expose] public section

namespace ArgumentStructure

open ArgumentStructure.Root.Kinds

/-- The root signature a class realizes, where one has been established: manner roots for the
activity classes, causative-result roots for the externally caused changes of state, pure
result roots for the internally caused ones, property concepts for the statives, the empty
signature for roots with no structural entailment. -/
def LevinClass.rootEntailments : LevinClass → Option Root.Kinds
  -- §9 Putting: template provides CAUSE+BECOME; root content varies
  | .put => none
  | .putDirection => none
  | .funnel => some pureManner          -- manner of channeling
  | .pour => some pureManner            -- manner of pouring
  | .coil => some pureManner            -- manner of arranging
  | .sprayLoad => none
  -- §10 Removing
  | .remove => none
  | .clear => some causativeResult      -- externally caused cleared state
  | .wipeManner | .wipeInstrument => some pureManner            -- manner of surface action
  | .steal => none
  -- §11 Sending and Carrying
  | .send => none
  | .carry => some pureManner           -- manner of transport
  | .drive => some pureManner           -- manner via vehicle
  -- §12 Exerting Force
  | .pushPull => some pureManner        -- manner of force application
  -- §13 Change of Possession
  | .give => some fullSpec              -- (B&KG Ch.3) √HAND: manner + caused possession change
  | .contribute => none
  | .get | .obtain => none
  | .exchange => none
  -- §14–16
  | .learn => none
  | .hold => some propertyConcept       -- state of holding
  | .conceal => some causativeResult    -- externally caused hidden state
  -- §17 Throwing
  | .throw => some fullSpec             -- manner of propulsion + caused arrival
  -- §18 Contact by Impact
  | .hit => some pureManner             -- (B&KG Ch.4) impact manner, no state entailed
  | .swat => some pureManner            -- like hit
  | .spank => some pureManner           -- like hit
  -- §19 Poking
  | .poke => some pureManner            -- manner of contact
  -- §20 Contact: Touch
  | .touch => some ∅              -- (B&KG) no structural entailments
  -- §21 Cutting
  | .cut => some fullSpec               -- (B&KG Ch.4) cutting manner + caused separation
  | .carve => some fullSpec             -- like cut
  -- §22 Combining and Attaching
  | .mix => some causativeResult        -- externally caused combined state
  | .amalgamate => some causativeResult
  -- §23 Separating
  | .separate => some causativeResult   -- externally caused separated state
  | .split => some fullSpec             -- instrument manner + caused separation
  -- §24 Coloring
  | .color => some causativeResult      -- externally caused colored state
  -- §25 Image Creation
  | .imageImpression | .scribble | .illustrate | .transcribe =>
    some fullSpec
  -- §26 Creation and Transformation
  | .build => some causativeResult      -- externally caused creation
  | .grow => some pureResult            -- internally caused growth
  | .create => some causativeResult     -- externally caused creation
  | .knead => some fullSpec             -- kneading manner + caused shape change
  | .turn => some causativeResult       -- externally caused transformation
  | .performance => some pureManner     -- performance manner
  -- §27–28
  | .engender => some causativeResult   -- root entails causation
  | .calve => some pureResult           -- internally caused biological process
  -- §29 Predicative Complements
  | .appoint => some causativeResult    -- externally caused status change
  | .characterize => none
  | .declare => some causativeResult    -- externally caused status change
  -- §30 Perception
  | .see => none
  | .sight => none
  -- §31 Psych-Verbs
  | .amuse => some causativeResult      -- stimulus causes psychological CoS
  | .admire => some propertyConcept     -- psychological state
  | .marvel => some propertyConcept     -- psychological state
  -- §32–34
  | .want => some propertyConcept       -- desiderative state
  | .long => some propertyConcept       -- desiderative state
  | .judgment => none
  | .assessment => none
  -- §35 Searching
  | .hunt | .search | .stalk | .investigate | .rummage | .ferret =>
    some pureManner
  -- §36 Social Interaction
  | .correspond | .marry | .meet => none
  -- §37 Communication
  | .say => none
  | .tell => none
  | .mannerOfSpeaking => some pureManner -- manner of speaking
  | .talk => none
  -- §38 Animal Sounds
  | .animalSound => some pureManner     -- specific sound manner
  -- §39 Ingesting
  | .eat => some causativeResult        -- caused consumption, no specific manner
  | .devour => some fullSpec            -- vigorous manner + caused consumption
  | .dine => some pureManner            -- social activity manner
  -- §40 Body
  | .hiccup | .breathe | .exhale => none
  | .nonverbalExpression => none
  | .flinch => none
  | .hurt => some causativeResult       -- externally caused injury
  -- §41 Grooming
  | .dress => some causativeResult      -- externally caused dressed state
  -- §42 Killing
  | .murder => some causativeResult     -- (B&KG) root entails caused death
  | .poison => some fullSpec            -- (B&KG) poisoning manner + caused death (√DROWN-type)
  -- §43 Emission
  | .lightEmission => some propertyConcept  -- emitting state
  | .soundEmission => some propertyConcept
  | .substanceEmission => some propertyConcept
  -- §44 Destroy
  | .destroy => some causativeResult    -- (B&KG) root entails caused total destruction
  -- §45 Change of State
  | .break_ => some causativeResult     -- (B&KG Ch.2,5) √CRACK: externally caused CoS
  | .bend => some causativeResult       -- externally caused shape change
  | .cooking => some fullSpec           -- (B&KG) cooking manner + caused CoS
  | .otherChangeOfState => some causativeResult   -- √MELT/√FREEZE: externally caused CoS
  | .entitySpecificChangeOfState => some pureResult -- √BLOSSOM/√RUST: internally caused
  | .calibratableChangeOfState => some pureResult -- internally driven scalar change
  -- §46 Lodge
  | .lodge => none
  -- §47 Existence
  | .exist => some ∅              -- (B&KG) pure stative, no root content
  -- §48 Appearance, Disappearance
  | .appear | .reflexiveAppearance => some pureResult          -- internally caused appearance
  | .disappearance => some pureResult   -- internally caused going out of existence
  -- §49 Body-Internal Motion
  | .bodyInternalMotion => some pureManner -- fidgeting manner
  -- §50 Assuming a Position
  | .assumePosition => some pureResult  -- internally caused position change
  -- §51 Motion
  | .inherentlyDirectedMotion => some pureResult -- internally caused directed motion
  | .leave => some pureResult           -- internally caused departure
  | .roll | .run => some pureManner  -- (B&KG) √JOG: motion manner
  | .vehicleName | .nonVehicleName => some pureManner   -- vehicle manner
  | .chase => some pureManner           -- chasing manner
  -- §52 Avoid
  | .avoid => none
  -- §53 Lingering and Rushing
  | .linger => some pureManner          -- temporal manner
  | .rush => some pureManner            -- temporal manner
  -- §54 Measure
  | .register | .cost | .fit | .price | .bill => some propertyConcept    -- measurement state
  -- §55 Aspectual
  | .begin | .complete => none
  -- §57 Weather
  | .weather => none
  | _ => none

/-- The class's root carries the entailment. -/
def LevinClass.RootEntails (c : LevinClass) (k : Root.Kind) : Prop :=
  match c.rootEntailments with
  | some s => k ∈ s
  | none => False

instance (c : LevinClass) (k : Root.Kind) : Decidable (c.RootEntails k) := by
  unfold LevinClass.RootEntails; split <;> infer_instance

theorem LevinClass.rootEntailments_wellFormed (c : LevinClass) (s : Root.Kinds)
    (h : c.rootEntailments = some s) : s.WellFormed := by
  cases c <;> cases h <;> decide

/-! ### The root hypothesis for the causative alternation -/

/-- The classes whose root entails its causer, so that no inchoative variant exists although
the root entails a caused change: the destroy and murder verbs of
[beavers-koontz-garboden-2020]. -/
def LevinClass.causativeExceptions : Finset LevinClass := {.destroy, .murder}

/-- The root hypothesis: a class alternates between causative and inchoative when its root
entails a caused change and no manner, unless the root entails its causer
(`causativeExceptions`). A hypothesis to be measured against Part II of [levin-1993], not
data. -/
def LevinClass.RootPredictsCausative (c : LevinClass) : Prop :=
  (∃ s ∈ c.rootEntailments, Root.Kind.cause ∈ s ∧ Root.Kind.manner ∉ s) ∧
    c ∉ LevinClass.causativeExceptions

instance (c : LevinClass) : Decidable c.RootPredictsCausative :=
  inferInstanceAs (Decidable ((∃ s ∈ _, _ ∧ _) ∧ _))

end ArgumentStructure
