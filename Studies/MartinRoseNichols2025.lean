module

public import Linglib.Pragmatics.Bidirectional
public import Linglib.Semantics.ArgumentStructure.EventStructure.Basic
public import Linglib.Semantics.ArgumentStructure.Unaccusativity
public import Linglib.Fragments.English.Verbs.Inventory
public import Linglib.Data.Examples.MartinRoseNichols2025
public import Linglib.Data.Examples.Readers
public import Linglib.Data.Statistics.MartinRoseNichols2025

/-!
# Martin, Rose and Nichols (2025): Burning facts: thick and thin causatives

A thick causative such as *burn*, *break* or *bury* conveys a way of bringing a change about; a
thin causative such as *kill*, *destroy* or *change* names the result state alone. This file
formalizes the account of why a thick causative, used transitively in its physical sense, rejects
a subject with abstract reference (*the lack of sunscreen burned her skin*) that periphrastic
*cause* and the thin causatives accept.

A model `CauseConcepts State Event` is an event structure with two relations of causation
between its eventualities, after Rose, Sievers and Nichols: production, the transfer of a
conserved physical quantity from cause to effect, and dependence, the counterfactual dependence
of the effect on the cause. Production entails dependence, and only a physical relatum produces.
The operator CAUSE has a `Reading` for each relation, and the readings are ordered by
specificity, `production < dependence`, so that `CauseConcepts.cause` is monotone and every
event-structure decomposition is at least as true under dependence as under production
(`CauseConcepts.denote_mono`). A thin causative is true of an eventuality that causes a change
into a state of its root, `CauseConcepts.thin`, and the causative of a manner root adds the
manner of the causing eventuality, `CauseConcepts.manner`.

A verb is thick when its causative entails a manner of the causing eventuality. There are two
ways. A manner root contributes the manner directly, under either reading. A state root does so
when every productive cause of its state is of the manner, the postulate of Beavers and
Koontz-Garboden for a manner of the cause, taken under production: then the causative entails
the manner under production (`CauseConcepts.thin_production_le`), and need not under dependence
(`scene_not_thin_dependence_le`). The second is the paper's account of *bury*, whose state
reveals the process that produced it.

The transitive forms, lexical and periphrastic, are ordered by markedness, and
`specialization : Form ≃o Reading` pairs the lexical causative with production and *cause* with
dependence. Where the manner information of a thick verb in its physical sense makes production
a salient alternative (`Promoted`), harmony is strictly monotone in both orders, and weak
bidirectional optimality keeps exactly the graph of that isomorphism
(`superoptimalSet_eq_graphOn_specialization`). A statement is `Felicitous` when in some model its
cause brings about a change under a reading its frame allows, a cause that is not physical if
the subject has abstract reference; this fails exactly for the lexical causative under promotion
with an abstract subject (`felicitous_iff`). The anticausative with a *from* phrase is not a
competitor and keeps both readings.

The judged causative statements of the paper are read against this. Among those with an absence,
a fact, a gerund or a degree as subject, the felicitous ones are the accepted ones, apart from six
corpus attestations of *burn*, *lift*, *lock* and *melt* whose subject the paper reads as naming a
productive cause (`rows_abstract`, `rows_reinterpreted`). Every statement that is not accepted is
a lexical causative under promotion (`rows_not_acceptable`). The flat tire of the paper's last
section is a physical relatum on which the axle's cracking depends without being produced by it
(`axle_tire`), in the one `scene` that also holds the absence and the producer of the sunscreen
contrast.

A corpus survey of thirty-seven frequent causative verbs records whether each alternates, is
thick, occurs with an adjectival strong resultative, and occurs with an omission or quality
subject in its concrete sense. The thick verbs are the verbs whose root is a predicate of the
causing event, the result verbs found with strong resultatives, together with *bury*
(`thick_iff`), and the verbs found with an omission or quality subject are the thin verbs other
than *close* and *lower*, together with *burn*, *lift*, *lock* and *melt* (`omission_iff`).

## Implementation notes

* The paper states the competition between the lexical causative and *cause* informally, as a
  division of pragmatic labour. It is formalized as weak bidirectional optimality over the two
  forms and the two readings, under any harmony strictly monotone in markedness and specificity,
  so no ranking of constraints is chosen.
* The paper's representations relate the causing eventuality to the result state directly. Here
  the causing eventuality causes a change that gives rise to the state, as the event-structure
  templates have it, and `CauseConcepts.thin_eq_denote` and `CauseConcepts.manner_eq_denote` give
  the two causatives as template denotations. The eventualities of a model are the causal
  relata, facts and absences among them.
* `Felicitous` tests the causal relation alone, the thin causative of any state; the manner of
  a manner root is a further condition on the cause that the rows do not test.
* Only the competition over production is modelled. Where production is not promoted, with a
  thin verb or in an abstract sense, a frame allows both readings; the weaker notions of
  directness in which the paper lets a thin causative still compete with *cause* are not
  represented.
* The rows are the causative statements of sections 1 to 3, 4.3.1 and 6 and the constructed pair
  of the appendix. A line printed with two verbs is one row for each. Example (78b) is printed
  without a mark and entered as marginal, the text calling it much less acceptable than (78a).
  The examples the paper repeats from Rose, Sievers and Nichols without marks in section 4.3.1
  are not entered again.
* For a subject that is an event or a concrete individual, whether it produces the change is a
  fact of the scenario and not of the sentence, so the rows with such subjects are tested only
  in the direction of `rows_not_acceptable`.
* The proportions the paper reports for the survey are left to the generated table. The
  annotators judged *cool* non-alternating, against the fragment, which gives it an intransitive
  with the patient as subject.
* The verb types the survey takes from Levin's catalogue are sections of it
  (`LevinType.number`), and each is a class of the fragment's entry for the verb
  (`levin_number`), except that the catalogue lists *cut* and *stretch* in other classes.

## TODO

* The resultative examples, the French examples and the aspectual contrasts between *cause* and
  the lexical causative have no rows.
* Wolff's definition of direct causation, of which the paper takes the production constraint to
  be the positive form, is not stated; `axle_tire` shows only that a necessary condition for the
  transference cause fails production.
* The survey's thick verbs are not assigned roots: `thick_iff` reads the position of the root
  off the resultative code, and no theorem joins a verb of the survey to `CauseConcepts.manner`
  or to the postulate of `CauseConcepts.thin_production_le`.
* Strong resultatives are available to a root that does not describe states in the study of Yu,
  Ausensi and Smith; the resultative column is not derived from that.

## References

* [martin-rose-nichols-2025]
* [rose-sievers-nichols-2021]
* [embick-2009]
* [wolff-2003]
* [beavers-koontz-garboden-2020]
* [yu-ausensi-smith-2023]
* [blutner-2000]
* [horn-1984]
-/

@[expose] public section

namespace MartinRoseNichols2025

open BidirectionalOT Set ModalLogic ArgumentStructure.EventStructure
open scoped SetRel

/-! ### Two concepts of causation -/

universe u

/-- The two readings of the operator CAUSE. -/
inductive Reading where
  | production
  | dependence
  deriving DecidableEq, Fintype, Repr

/-- The rank of a reading in specificity, the more specific reading first. -/
def Reading.rank : Reading → ℕ
  | .production => 0
  | .dependence => 1

instance : LinearOrder Reading := LinearOrder.lift' Reading.rank (by decide)

/-- An event structure with the two concepts of causation of [rose-sievers-nichols-2021] between
its eventualities, the causal relata: production entails dependence, and only a physical relatum
produces. -/
structure CauseConcepts (State Event : Type u) where
  /-- An eventuality and a state it gives rise to. -/
  become : SetRel Event State
  /-- The cause produces the effect: it transfers a conserved physical quantity to it. -/
  produces : SetRel Event Event
  /-- The effect counterfactually depends on the cause. -/
  depends : SetRel Event Event
  produces_subset_depends : produces ⊆ depends
  /-- The relatum is a physical, energy-bearing entity. -/
  Physical : Event → Prop
  physical_of_produces {c e : Event} : c ~[produces] e → Physical c

namespace CauseConcepts

variable {Entity : Type*} {State Event : Type u} (C : CauseConcepts State Event) (r : Reading)
  (Q : Event → Prop) (p : State → Prop) {c : Event}

/-- The relation that CAUSE denotes under a reading. -/
def cause : Reading → SetRel Event Event
  | .production => C.produces
  | .dependence => C.depends

theorem cause_mono : Monotone C.cause := fun a b h ↦ by
  cases a <;> cases b
  exacts [le_rfl, C.produces_subset_depends, absurd h (by decide), le_rfl]

/-- The relations of the readings, as a monotone map from the specificity order. -/
def causeHom : Reading →o SetRel Event Event := ⟨C.cause, C.cause_mono⟩

@[simp] theorem coe_causeHom : ⇑C.causeHom = C.cause := rfl

/-- The interpretation of the event-structure primitives under a reading of CAUSE. -/
@[simps]
def interpretation : Interpretation State Event := ⟨C.become, C.cause r⟩

-- every decomposition is at least as true under dependence as under production
theorem denote_mono {σ : Eventuality} (t : Template σ) (θ : Entity → Event → Prop)
    (P : Entity → State → Prop) (y x : Entity) :
    Monotone fun r ↦ t.denote (C.interpretation r) θ P Q y x :=
  fun a b h ↦ Template.denote_mono (M := C.interpretation a) (N := C.interpretation b)
    subset_rfl (C.cause_mono h) t y x

/-- (1b): the thin causative, true of an eventuality that causes a change into a state of
`p`. -/
def thin : Event → Prop := ◇[C.cause r] (◇[C.become] p)

/-- (51b): the causative of a manner root, true of an eventuality of the manner `Q` that causes a
change into a state of `p`, the state of a result phrase or any state. -/
def manner : Event → Prop := Q ⊓ C.thin r p

theorem thin_eq_denote (P : Entity → State → Prop) (x : Entity) :
    C.thin r (P x) =
      (Template.cause .effector .achievement).denote (C.interpretation r) ⊤ P Q x x :=
  funext fun _ ↦ (true_and _).symm

theorem manner_eq_denote (P : Entity → State → Prop) (x : Entity) :
    C.manner r Q (P x) = Template.accomplishment.denote (C.interpretation r) ⊤ P Q x x :=
  funext fun _ ↦ propext ⟨fun h ↦ ⟨⟨trivial, h.1⟩, h.2⟩, fun h ↦ ⟨h.1.2, h.2⟩⟩

theorem thin_mono : Monotone (C.thin · p) :=
  fun _ _ h _ ⟨e, he, hp⟩ ↦ ⟨e, C.cause_mono h he, hp⟩

variable {C r p Q}

theorem physical_of_thin (h : C.thin .production p c) : C.Physical c :=
  let ⟨_, he, _⟩ := h; C.physical_of_produces he

/-! ### Two ways of conveying a manner of causing

A verb is thick when its causative entails a manner of the causing eventuality. A manner root
does so under either reading, and a state root does so under production when the manner is that
of the productive cause of its state, as with *bury*. -/

theorem manner_le : C.manner r Q p ≤ Q := inf_le_left

/-- (70b): a causative of a state whose productive causes are all of the manner `Q` entails the
manner under production, where a state arises from at most one change. -/
theorem thin_production_le
    (h : (C.interpretation .production).EntailsMannerOfCause p Q)
    (hC : ∀ s ⦃e⦄, e ~[C.become] s → ∀ ⦃e'⦄, e' ~[C.become] s → e = e') :
    C.thin .production p ≤ Q :=
  h.diamond_cause_diamond_become_le hC

end CauseConcepts

/-! ### The competition between covert and overt CAUSE -/

/-- The transitive forms of a causative statement: the lexical causative and periphrastic
*cause*. -/
inductive Form where
  | lexical
  | periphrastic
  deriving DecidableEq, Fintype, Repr

/-- The markedness of a form. -/
def Form.markedness : Form → ℕ
  | .lexical => 0
  | .periphrastic => 1

instance : LinearOrder Form := LinearOrder.lift' Form.markedness (by decide)

/-- The pairing of the lexical causative with production and of *cause* with dependence, an
isomorphism of the markedness order with the specificity order. -/
def specialization : Form ≃o Reading where
  toFun | .lexical => .production | .periphrastic => .dependence
  invFun | .production => .lexical | .dependence => .periphrastic
  left_inv a := by cases a <;> rfl
  right_inv r := by cases r <;> rfl
  map_rel_iff' {a b} := by cases a <;> cases b <;> decide

@[simp] theorem specialization_lexical : specialization .lexical = .production := rfl

@[simp] theorem specialization_periphrastic : specialization .periphrastic = .dependence := rfl

/-- The production constraint: under any harmony strictly monotone in markedness and
specificity, weak bidirection pairs the lexical causative with production and *cause* with
dependence. -/
theorem superoptimalSet_eq_graphOn_specialization {α : Type*} [Preorder α]
    {f : Form × Reading → α} (hf : StrictMono f) :
    superoptimalSet univ f = univ.graphOn specialization :=
  superoptimalSet_eq_graphOn _ specialization hf finite_univ.isWF (subset_univ _)

/-- The manner information of a verb promotes production when the verb is thick and used in its
physical sense. -/
def Promoted (thick : Prop) (s : Examples.Sense) : Prop := thick ∧ s = .physical

instance (thick : Prop) [Decidable thick] (s : Examples.Sense) : Decidable (Promoted thick s) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The transitive form of a frame, none for the anticausative with a *from* phrase, which does
not compete. -/
def Examples.Frame.form : Examples.Frame → Option Form
  | .lexical => some .lexical
  | .periphrastic => some .periphrastic
  | .anticausative => none

/-- A frame allows a reading of CAUSE unless production is promoted and the competition of the
frame's form with the other transitive form removes the reading. -/
def Allows (promoted : Prop) (fr : Examples.Frame) (r : Reading) : Prop :=
  promoted → ∀ a ∈ fr.form, (a, r) ∈ superoptimalSet univ (id : Form × Reading → Form × Reading)

variable {promoted abstract : Prop} {fr : Examples.Frame} {r : Reading}

theorem allows_iff : Allows promoted fr r ↔ promoted → ∀ a ∈ fr.form, specialization a = r := by
  simp [Allows, superoptimalSet_eq_graphOn_specialization strictMono_id]

theorem allows_of_not (h : ¬promoted) : Allows promoted fr r := fun hp ↦ absurd hp h

theorem allows_anticausative : Allows promoted .anticausative r := fun _ _ h ↦ nomatch h

theorem allows_lexical_iff : Allows promoted .lexical r ↔ promoted → r = .production := by
  simp [allows_iff, Examples.Frame.form, eq_comm]

theorem allows_periphrastic_iff :
    Allows promoted .periphrastic r ↔ promoted → r = .dependence := by
  simp [allows_iff, Examples.Frame.form, eq_comm]

/-! ### A scene -/

/-- The eventualities of a scene: an absence, a physical condition that is necessary for the
transference cause, the transference cause, and the change. -/
inductive Scene where
  | absence
  | condition
  | producer
  | change
  deriving DecidableEq, Repr

/-- The producer produces the change, which depends on the absence and the condition as well and
gives rise to the one state. The lack of sunscreen and the sun are the absence and the producer
of a burn, and the flat tire and the driving the condition and the producer of a cracked axle. -/
def scene : CauseConcepts Unit Scene where
  become := {x | x.1 = .change}
  produces := {x | x.1 = .producer ∧ x.2 = .change}
  depends := {x | x.1 ≠ .change ∧ x.2 = .change}
  produces_subset_depends := by rintro ⟨_, _⟩ ⟨rfl, rfl⟩; exact ⟨by decide, rfl⟩
  Physical c := c ≠ .absence
  physical_of_produces := by rintro _ _ ⟨rfl, -⟩; decide

theorem scene_thin_production {c : Scene} : scene.thin .production ⊤ c ↔ c = .producer := by
  refine ⟨?_, fun h ↦ ⟨.change, ⟨h, rfl⟩, (), rfl, trivial⟩⟩
  rintro ⟨_, ⟨h, -⟩, -⟩
  exact h

theorem scene_thin_dependence {c : Scene} : scene.thin .dependence ⊤ c ↔ c ≠ .change := by
  refine ⟨?_, fun h ↦ ⟨.change, ⟨h, rfl⟩, (), rfl, trivial⟩⟩
  rintro ⟨_, ⟨h, -⟩, -⟩
  exact h

-- the state of the scene has the producer as the manner of its productive cause, and its
-- causative entails that manner under production and not under dependence
theorem scene_entailsMannerOfCause :
    (scene.interpretation .production).EntailsMannerOfCause ⊤ (· = .producer) :=
  fun _ _ ↦ ⟨.change, rfl,
    ⟨.producer, show (Scene.producer, Scene.change) ∈ scene.produces from ⟨rfl, rfl⟩, trivial⟩,
    by rintro _ ⟨h, -⟩; exact h⟩

theorem scene_not_thin_dependence_le : ¬scene.thin .dependence ⊤ ≤ (· = .producer) :=
  fun h ↦ Scene.noConfusion (h .absence (scene_thin_dependence.2 (by decide)))

-- (78): with a thick verb in its physical sense, the flat tire fails the lexical causative on
-- every reading it allows and satisfies *cause*, though the tire is physical
theorem axle_tire :
    scene.Physical .condition ∧ (∀ r, Allows True .lexical r → ¬scene.thin r ⊤ .condition) ∧
      ∃ r, Allows True .periphrastic r ∧ scene.thin r ⊤ .condition :=
  ⟨Scene.noConfusion, fun r hr ↦ by
      obtain rfl := allows_lexical_iff.1 hr trivial
      exact fun h ↦ Scene.noConfusion (scene_thin_production.1 h),
    .dependence, allows_periphrastic_iff.2 fun _ ↦ rfl, scene_thin_dependence.2 (by decide)⟩

/-! ### Felicity -/

/-- A causative statement in a frame is felicitous if in some model its cause brings about a
change under a reading the frame allows, a cause that is not physical when the subject has
abstract reference. -/
def Felicitous (promoted : Prop) (fr : Examples.Frame) (abstract : Prop) : Prop :=
  ∃ (State Event : Type) (C : CauseConcepts State Event) (c : Event) (r : Reading),
    (abstract → ¬C.Physical c) ∧ Allows promoted fr r ∧ C.thin r ⊤ c

/-- A causative statement is infelicitous exactly when it is a lexical causative, production is
promoted, and its subject has abstract reference. -/
theorem felicitous_iff :
    Felicitous promoted fr abstract ↔ ¬(promoted ∧ abstract ∧ fr = .lexical) := by
  refine ⟨fun ⟨_, _, C, c, r, hc, ha, hr⟩ ⟨hp, habs, hfr⟩ ↦ ?_, fun h ↦ ?_⟩
  · subst hfr
    obtain rfl := allows_lexical_iff.1 ha hp
    exact hc habs (CauseConcepts.physical_of_thin hr)
  · have absence {fr} (ha : Allows promoted fr .dependence) : Felicitous promoted fr abstract :=
      ⟨_, _, scene, .absence, .dependence, fun _ h ↦ h rfl, ha,
        scene_thin_dependence.2 (by decide)⟩
    cases fr
    · by_cases habs : abstract
      · exact absence (allows_of_not fun hp ↦ h ⟨hp, habs, rfl⟩)
      · exact ⟨_, _, scene, .producer, .production, fun h ↦ absurd h habs,
          allows_lexical_iff.2 fun _ ↦ rfl, scene_thin_production.2 rfl⟩
    · exact absence (allows_periphrastic_iff.2 fun _ ↦ rfl)
    · exact absence allows_anticausative

/-! ### The corpus survey -/

/-- The fragment entry of each verb of the survey. -/
def Verb.entry : Verb → English.Verbs.Verb
  | .activate => English.Verbs.activate
  | .affect => English.Verbs.affect
  | .change => English.Verbs.change
  | .close => English.Verbs.close
  | .cool => English.Verbs.cool
  | .damage => English.Verbs.damage
  | .destroy => English.Verbs.destroy
  | .dry => English.Verbs.dry
  | .eliminate => English.Verbs.eliminate
  | .enhance => English.Verbs.enhance
  | .extend => English.Verbs.extend
  | .hurt => English.Verbs.hurt
  | .kill => English.Verbs.kill
  | .lower => English.Verbs.lower
  | .open => English.Verbs.open_
  | .put => English.Verbs.put
  | .restore => English.Verbs.restore
  | .set => English.Verbs.set_
  | .slow => English.Verbs.slow
  | .start => English.Verbs.start
  | .stop => English.Verbs.stop
  | .trigger => English.Verbs.trigger
  | .turn => English.Verbs.turn
  | .wakeUp => English.Verbs.wakeUp
  | .break => English.Verbs.break_
  | .bury => English.Verbs.bury
  | .burn => English.Verbs.burn
  | .cut => English.Verbs.cut
  | .drop => English.Verbs.drop
  | .lift => English.Verbs.lift
  | .lock => English.Verbs.lock
  | .melt => English.Verbs.melt
  | .mix => English.Verbs.mix
  | .shut => English.Verbs.shut
  | .spread => English.Verbs.spread
  | .stretch => English.Verbs.stretch
  | .switch => English.Verbs.switch

/-- The position of a verb's root on the paper's analysis of the resultative codes. The root of a
verb found with a strong resultative is a predicate of the causing event, adjoined to `v`; the
root of a verb not found with one is a predicate of the result state, in the complement of `v`;
and a root that lexicalizes no state and needs the resultative spells out `v` itself. -/
def Resultative.position : Resultative → Option ArgumentStructure.Root.Position
  | .yes => some .adjoined
  | .no => some .complement
  | .only => none

/-- The thick verbs of the survey are the verbs whose root is adjoined to `v`, Embick's
causative manner verbs, and *bury*. -/
theorem thick_iff : ∀ v, (survey v).thick ↔
    (survey v).resultative.position = some .adjoined ∨ v = .bury := by
  decide

theorem omission_iff : ∀ v, (survey v).omission ↔
    (¬(survey v).thick ∧ v ∉ [Verb.close, .lower]) ∨ v ∈ [Verb.burn, .lift, .lock, .melt] := by
  decide

theorem alternating_iff_hasCausativeAlternation : ∀ v, v ≠ .cool →
    ((survey v).alternating ↔ v.entry.valency.HasCausativeAlternation) := by
  decide

/-- The section of Levin's catalogue that a verb type of Table 3 names. -/
def LevinType.number : LevinType → List ℕ
  | .amuse => [31, 1]
  | .turn => [26, 6]
  | .otherChangeOfState => [45, 4]
  | .destroy => [44]
  | .removing => [10]
  | .existence => [47]
  | .hurt => [40, 8, 3]
  | .killing => [42]
  | .putting => [9]
  | .put => [9, 1]
  | .contribute => [13, 2]
  | .aspectual => [55]
  | .break => [45, 1]
  | .calibratableChangeOfState => [45, 6]
  | .tape => [22, 4]
  | .mix => [22, 1]
  | .spatialConfiguration => [47, 6]

-- the verb types of Table 3 are catalogue classes of the fragment's entries
theorem levin_number : ∀ v, v ∉ [Verb.cut, .stretch] →
    (∀ t ∈ (survey v).levin, ∃ c ∈ v.entry.levinClasses, t.number <+: c.number) ∧
      ((survey v).levin.isSome ↔ v.entry.levin.isSome) := by
  decide

/-! ### The judged statements -/

namespace Examples

/-- The verb of the survey that a verb of the examples is, none for a verb outside the sample. -/
def Lexeme.sample : Lexeme → Option Verb
  | .burn => some .burn
  | .melt => some .melt
  | .kill => some .kill
  | .damage => some .damage
  | .trigger => some .trigger
  | .change => some .change
  | .activate => some .activate
  | .bury => some .bury
  | .break => some .break
  | .destroy => some .destroy
  | .lift => some .lift
  | .lock => some .lock
  | .lower => some .lower
  | .drop => some .drop
  | .flood | .die | .crack | .boil | .crash | .heat | .ruin => none

/-- A verb of the examples is thick if the survey codes it so, or if it is one of the verbs
outside the sample that the paper calls thick: *flood*, *crack*, *boil*, *crash* and *heat up*. -/
def Lexeme.Thick (l : Lexeme) : Prop :=
  (∃ v ∈ l.sample, (survey v).thick) ∨ l ∈ [Lexeme.flood, .crack, .boil, .crash, .heat]

instance : DecidablePred Lexeme.Thick := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- The fragment entry of each verb of the examples. -/
def Lexeme.entry : Lexeme → English.Verbs.Verb
  | .burn => English.Verbs.burn
  | .melt => English.Verbs.melt
  | .flood => English.Verbs.flood
  | .kill => English.Verbs.kill
  | .die => English.Verbs.die
  | .damage => English.Verbs.damage
  | .trigger => English.Verbs.trigger
  | .change => English.Verbs.change
  | .activate => English.Verbs.activate
  | .bury => English.Verbs.bury
  | .break => English.Verbs.break_
  | .crack => English.Verbs.crack
  | .destroy => English.Verbs.destroy
  | .boil => English.Verbs.boil
  | .lift => English.Verbs.lift
  | .lock => English.Verbs.lock
  | .crash => English.Verbs.crash
  | .heat => English.Verbs.heat
  | .ruin => English.Verbs.ruin
  | .lower => English.Verbs.lower
  | .drop => English.Verbs.drop

theorem Lexeme.entry_sample (l : Lexeme) : ∀ v ∈ l.sample, v.entry = l.entry := by
  cases l <;> simp [Lexeme.sample, Lexeme.entry, Verb.entry]

/-- A subject with abstract reference: an absence, a fact, a gerund or a degree. -/
def Subject.Abstract (k : Subject) : Prop := k ∈ [Subject.absence, .fact, .gerund, .degree]

instance : DecidablePred Subject.Abstract := fun _ ↦ inferInstanceAs (Decidable (_ ∈ _))

/-- Production is promoted in an example: its verb is thick and used in its physical sense. -/
def Example.Promoted (x : Example) : Prop :=
  ∃ l ∈ x.lexemes .verb, ∃ s ∈ x.sense, MartinRoseNichols2025.Promoted l.Thick s

instance : DecidablePred Example.Promoted := fun _ ↦
  inferInstanceAs (Decidable (∃ l ∈ _, ∃ s ∈ _, _))

/-- An example is felicitous on the account: its frame and the kind of its subject are, under
the promotion its verb and sense give. -/
def Example.Felicitous (x : Example) : Prop :=
  ∃ fr ∈ x.frame, ∃ k ∈ x.subject, MartinRoseNichols2025.Felicitous x.Promoted fr k.Abstract

theorem Example.felicitous_iff (x : Example) : x.Felicitous ↔
    ∃ fr ∈ x.frame, ∃ k ∈ x.subject, ¬(x.Promoted ∧ k.Abstract ∧ fr = .lexical) := by
  simp only [Example.Felicitous, MartinRoseNichols2025.felicitous_iff]

/-- The corpus attestations of a thick verb in its physical sense with an omission or a degree
as subject, which the paper reads as naming a productive cause. -/
def reinterpreted : List Example := [.ex_62a, .ex_62b, .ex_62d, .ex_62e, .ex_66a, .ex_66b]

/-- Among the statements whose subject has abstract reference, the felicitous ones are the
accepted ones, the reinterpreted corpus attestations apart. -/
theorem rows_abstract : ∀ x : Example, x ∉ reinterpreted → (∃ k ∈ x.subject, k.Abstract) →
    (x.Felicitous ↔ x.datum.judgment = .acceptable) := by
  simp only [Example.felicitous_iff]
  decide

theorem rows_reinterpreted : ∀ x ∈ reinterpreted, ¬x.Felicitous ∧
    x.datum.judgment = .acceptable ∧ x.datum.method = some .corpus := by
  simp only [Example.felicitous_iff]
  decide

-- every statement that is not accepted is a lexical causative of a thick verb in its physical
-- sense
theorem rows_not_acceptable : ∀ x : Example, x.datum.judgment ≠ .acceptable →
    x.Promoted ∧ x.frame = some .lexical := by
  decide

/-! ### The verbs of the rows -/

/-- A word is printed as a verb entry if it is a form the entry realizes. -/
def Printed (v : English.Verbs.Verb) (w : List Char) : Prop :=
  ∃ c ∈ [English.Verbs.Verb.Cell.base, .thirdSg, .past, .pastParticiple], w = (v.realize c).toList

instance (v : English.Verbs.Verb) (w : List Char) : Decidable (Printed v w) :=
  inferInstanceAs (Decidable (∃ c ∈ _, _))

-- every span names a lexeme and marks a word printed as a form of its entry
theorem printed : ∀ x : Example, ∀ p ∈ x.datum.spans,
    ∃ l ∈ lexeme? p, ∃ w ∈ (p.words x.datum).head?, Printed l.entry w.word := by
  decide +kernel

end Examples

end MartinRoseNichols2025
