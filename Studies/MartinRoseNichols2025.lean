module

public import Linglib.Pragmatics.Bidirectional
public import Linglib.Semantics.Root.Defs
public import Linglib.Fragments.English.Verbs.Inventory
public import Linglib.Semantics.ArgumentStructure.Unaccusativity

/-!
# Martin, Rose and Nichols (2025): Burning facts: thick and thin causatives

This file formalizes the division of English lexical causatives into thick and thin verbs. A
thick causative such as *burn*, *break* or *bury* conveys a way of bringing the change about;
a thin causative such as *kill*, *destroy* or *change* names the result state alone. Rose,
Sievers and Nichols distinguish two concepts of causation, production, the transfer of a
conserved physical quantity from cause to effect, and dependence, the counterfactual
dependence of the effect on the cause. Production entails dependence, and only a physical
entity produces, so an absence, a fact or a degree is at most a dependence cause. A thick
causative used transitively in its physical sense conveys production and so rejects a subject
with abstract reference (*the lack of sunscreen burned her skin*) that a thin causative
accepts (*the lack of water killed my plants*). Martin, Rose and Nichols derive this
production constraint from the competition between the lexical causative and periphrastic
*cause*: the manner information makes production the salient reading, the lexical form takes
the more specific meaning and leaves dependence to *cause*, the division of pragmatic labour
that weak bidirectional optimality theory yields. The constraint lapses where the competition
does, in the abstract sense and in the anticausative with a causer phrase, and it is the
positive form of Wolff's directness constraint: a subject that is only a necessary condition
for the transference cause (*the flat tire cracked the axle*) fails a thick verb but not a
thin one.

A corpus survey of thirty-seven frequent causative verbs records whether each alternates, is
thick, occurs with an adjectival strong resultative (*break open*), and occurs with an
omission or quality subject in its concrete sense. The thick verbs are, except for *bury*,
Embick's causative manner verbs, the result verbs found with strong resultatives, and the thin
verbs found with strong resultatives (*set*, *trigger*, *turn*) lexicalize no result state of
their own. *Bury* is thick through a result state that reveals the process producing it
rather than through an event predicate.

## Main definitions

* `CauseConcepts` — production and dependence over a domain of causal relata, with the
  postulates that production entails dependence and that only physical relata produce.
* `Reading`, `Reading.holds` — the two readings of CAUSE and their truth conditions.
* `Form`, `tableau` — the competition between the lexical causative, periphrastic *cause* and
  the anticausative with a causer phrase, as a bidirectional optimality tableau.
* `Sample` — the thirty-seven verbs of the survey, `Sample.entry` their fragment entries, and
  the columns `alternating`, `thick`, `strongResultative`, `resultless`, `omissionSubject`.
* `causativeMannerVerbs`, `thickState` — Embick's class and the thick verbs outside it.

## Main results

* `production_constraint` — with production promoted, the lexical form conveys production and
  *cause* dependence; `lexical_dependence_of_not_promoted`, `anticausative_readings` — the
  dependence reading survives where nothing promotes production.
* `not_holds_of_not_physical` — under the production constraint no subject with abstract
  reference satisfies the lexical causative; `sunburn` and `axle` are the paper's contrasts.
* `causativeMannerVerbs_subset_thick`, `thickState_eq`, `strongResultative_sdiff_thick` — the
  correlation between thickness and strong resultatives.
* `thin_without_omission`, `thick_inter_omissionSubject` — omission subjects in the survey.
* `alternating_iff_hasCausativeAlternation` — the alternation column agrees with the fragment's
  diatheses.

## Implementation notes

The proportions the paper reports (twelve of thirteen thick verbs with a strong resultative,
ten of thirteen thick and twelve of twenty-four thin verbs alternating) are left to prose;
the theorems state the correlations with their named exceptions. Table 3 lists *melt* among
the thick verbs found with an omission subject, though the discussion names only *burn*,
*lift* and *lock*; the table is followed. The survey's annotators judged *cool*
non-alternating, against the fragment, which gives it an intransitive with the patient as
subject.

## References

* [martin-rose-nichols-2025]
* [rose-sievers-nichols-2021] — the two concepts of causation and the omission contrasts.
* [embick-2009] — causative manner verbs and strong resultatives, as the paper reports them.
* [wolff-2003] — the directness constraint, as the paper quotes it.
* [blutner-2000], [horn-1984] — weak bidirectional optimality and the division of labour.
-/

@[expose] public section

namespace MartinRoseNichols2025

open BidirectionalOT

/-! ### Two concepts of causation -/

/-- A domain of causal relata with the two concepts of causation of Rose, Sievers and
Nichols. Production is the transfer of a conserved physical quantity from cause to effect,
and dependence the counterfactual dependence of the effect on the cause; production entails
dependence, and only a physical relatum produces. -/
structure CauseConcepts (E : Type*) where
  /-- The relatum is a physical, energy-bearing entity. -/
  Physical : E → Prop
  /-- The cause produces the effect. -/
  Produces : E → E → Prop
  /-- The effect counterfactually depends on the cause. -/
  Depends : E → E → Prop
  depends_of_produces {c e : E} : Produces c e → Depends c e
  physical_of_produces {c e : E} : Produces c e → Physical c

variable {E : Type*} (C : CauseConcepts E) {s o : E}

theorem CauseConcepts.not_produces_of_not_physical (h : ¬C.Physical s) : ¬C.Produces s o :=
  fun hp ↦ h (C.physical_of_produces hp)

/-- The two readings of the operator CAUSE. -/
inductive Reading where
  | production
  | dependence
  deriving DecidableEq, Fintype, Repr

/-- The truth condition of a causative statement with subject `s` and object `o` under a
reading. -/
def Reading.holds : Reading → E → E → Prop
  | .production, s, o => C.Produces s o
  | .dependence, s, o => C.Depends s o

/-- Production is the stronger reading. -/
theorem Reading.holds_dependence_of_production (h : Reading.production.holds C s o) :
    Reading.dependence.holds C s o :=
  C.depends_of_produces h

/-! ### The competition between covert and overt CAUSE -/

/-- The forms of a causative statement are the transitive lexical causative, periphrastic
*cause*, and the anticausative with a causer phrase. -/
inductive Form where
  | lexical
  | periphrastic
  | anticausative
  deriving DecidableEq, Fintype, Repr

/-- The markedness constraint: the periphrastic form is marked. -/
def markedness (p : Form × Reading) : ℕ := if p.1 = .periphrastic then 1 else 0

/-- The production constraint: when the verb's manner information promotes production, the
dependence reading is marked. -/
def production (promotes : Bool) (p : Form × Reading) : ℕ :=
  if promotes ∧ p.2 = .dependence then 1 else 0

/-- The tableau of a form and reading under `markedness ≫ production`. -/
def tableau (promotes : Bool) : Form × Reading → List ℕ :=
  profile [markedness, production promotes]

/-- The transitive forms expressing a causal relation between a subject and an object. -/
def transitivePairs : Finset (Form × Reading) :=
  {(.lexical, .production), (.lexical, .dependence),
    (.periphrastic, .production), (.periphrastic, .dependence)}

/-- The anticausative with a causer phrase competes with no other form. -/
def anticausativePairs : Finset (Form × Reading) :=
  {(.anticausative, .production), (.anticausative, .dependence)}

/-- The production constraint. When a thick causative in its physical sense promotes
production, the lexical form takes it and periphrastic *cause* is left with dependence. -/
theorem production_constraint :
    superoptimal transitivePairs (tableau true) =
      {(.lexical, .production), (.periphrastic, .dependence)} := by
  decide

theorem reading_eq_production_of_lexical :
    ∀ r, (Form.lexical, r) ∈ superoptimal transitivePairs (tableau true) → r = .production := by
  decide

theorem reading_eq_dependence_of_periphrastic :
    ∀ r, (Form.periphrastic, r) ∈ superoptimal transitivePairs (tableau true) →
      r = .dependence := by
  decide

/-- Where nothing promotes production, in the abstract sense or with a thin verb, the lexical
form keeps the dependence reading. -/
theorem lexical_dependence_of_not_promoted :
    (Form.lexical, Reading.dependence) ∈ superoptimal transitivePairs (tableau false) := by
  decide

/-- The anticausative with a causer phrase has both readings. -/
theorem anticausative_readings :
    superoptimal anticausativePairs (tableau false) = anticausativePairs := by
  decide

/-- Under the production constraint a subject with abstract reference falsifies the lexical
causative. -/
theorem not_holds_of_not_physical {r : Reading}
    (hr : (Form.lexical, r) ∈ superoptimal transitivePairs (tableau true))
    (h : ¬C.Physical s) : ¬r.holds C s o := by
  obtain rfl := reading_eq_production_of_lexical r hr
  exact C.not_produces_of_not_physical h

/-! ### Witnesses -/

/-- The relata of the sunscreen contrast are the lack of sunscreen, the sun, and the skin. -/
inductive Sunburn where
  | lackOfSunscreen
  | sun
  | skin
  deriving DecidableEq, Repr

/-- The sun burns the skin, and the lack of sunscreen, an absence, is a dependence cause of
the burn only. -/
def sunburn : CauseConcepts Sunburn where
  Physical x := x ≠ .lackOfSunscreen
  Produces c e := c = .sun ∧ e = .skin
  Depends c e := (c = .sun ∨ c = .lackOfSunscreen) ∧ e = .skin
  depends_of_produces h := ⟨.inl h.1, h.2⟩
  physical_of_produces h := by rintro rfl; cases h.1

theorem sunburn_sun : Reading.production.holds sunburn .sun .skin := ⟨rfl, rfl⟩

theorem sunburn_lexical (r : Reading)
    (hr : (Form.lexical, r) ∈ superoptimal transitivePairs (tableau true)) :
    ¬r.holds sunburn .lackOfSunscreen .skin :=
  not_holds_of_not_physical sunburn hr fun h ↦ h rfl

theorem sunburn_periphrastic (r : Reading)
    (hr : (Form.periphrastic, r) ∈ superoptimal transitivePairs (tableau true)) :
    r.holds sunburn .lackOfSunscreen .skin := by
  obtain rfl := reading_eq_dependence_of_periphrastic r hr
  exact ⟨.inr rfl, rfl⟩

/-- The relata of the flat-tire contrast: the tire, the driving, and the axle. -/
inductive Axle where
  | tire
  | driving
  | axle
  deriving DecidableEq, Repr

/-- Driving on a flat tire cracks the axle. The driving transfers force to the axle, and the
flat tire is a necessary condition for the driving to do so; every relatum is physical. -/
def axle : CauseConcepts Axle where
  Physical _ := True
  Produces c e := c = .driving ∧ e = .axle
  Depends c e := (c = .driving ∨ c = .tire) ∧ e = .axle
  depends_of_produces h := ⟨.inl h.1, h.2⟩
  physical_of_produces _ := trivial

theorem axle_driving : Reading.production.holds axle .driving .axle := ⟨rfl, rfl⟩

theorem axle_tire_dependence : Reading.dependence.holds axle .tire .axle := ⟨.inr rfl, rfl⟩

theorem axle_tire_not_production : ¬Reading.production.holds axle .tire .axle :=
  fun h ↦ Axle.noConfusion h.1

/-! ### The corpus survey -/

/-- The thirty-seven verbs of the survey, in the order of Table 3. -/
inductive Sample where
  | activate | affect | change | close | cool | damage | destroy | dry | eliminate | enhance
  | extend | hurt | kill | lower | open_ | put | restore | set_ | slow | start | stop | trigger
  | turn | wakeUp
  | break_ | bury | burn | cut | drop | lift | lock | melt | mix | shut | spread | stretch
  | switch
  deriving DecidableEq, Fintype, Repr

namespace Sample

/-- The fragment entry of each verb. -/
def entry : Sample → English.Verbs.Verb
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
  | .open_ => English.Verbs.open_
  | .put => English.Verbs.put
  | .restore => English.Verbs.restore
  | .set_ => English.Verbs.set_
  | .slow => English.Verbs.slow
  | .start => English.Verbs.start
  | .stop => English.Verbs.stop
  | .trigger => English.Verbs.trigger
  | .turn => English.Verbs.turn
  | .wakeUp => English.Verbs.wakeUp
  | .break_ => English.Verbs.break_
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

/-- The verbs the survey's annotators judged to enter the causative alternation. -/
def alternating : Finset Sample :=
  {.activate, .change, .close, .dry, .extend, .lower, .open_, .slow, .start, .stop, .turn,
    .wakeUp, .break_, .burn, .drop, .lock, .melt, .mix, .shut, .spread, .stretch, .switch}

/-- The thick verbs, those judged to specify a way of causing, confirmed for all but *lift* and
*mix* by a dictionary's manner specification. -/
def thick : Finset Sample :=
  {.break_, .bury, .burn, .cut, .drop, .lift, .lock, .melt, .mix, .shut, .spread, .stretch,
    .switch}

/-- The verbs found with an adjectival strong resultative. -/
def strongResultative : Finset Sample :=
  {.set_, .trigger, .turn, .break_, .burn, .cut, .drop, .lift, .lock, .melt, .mix, .shut,
    .spread, .stretch, .switch}

/-- The verbs that lexicalize no result state of their own, whose resultative is obligatory
(*set me free*); the table's starred cells. -/
def resultless : Finset Sample := {.set_, .trigger, .turn}

/-- The verbs found with an omission or quality subject in their concrete sense. -/
def omissionSubject : Finset Sample :=
  {.activate, .affect, .change, .cool, .damage, .destroy, .dry, .eliminate, .enhance, .extend,
    .hurt, .kill, .open_, .put, .restore, .set_, .slow, .start, .stop, .trigger, .turn,
    .wakeUp, .burn, .lift, .lock, .melt}

/-- Embick's causative manner verbs, the result verbs found with strong resultatives. -/
def causativeMannerVerbs : Finset Sample := strongResultative \ resultless

/-- The thick verbs that are not causative manner verbs, thick through their result state. -/
def thickState : Finset Sample := thick \ causativeMannerVerbs

/-- Every causative manner verb is thick. -/
theorem causativeMannerVerbs_subset_thick : causativeMannerVerbs ⊆ thick := by decide

/-- *Bury* is the one thick verb that is not a causative manner verb. -/
theorem thickState_eq : thickState = {.bury} := by decide

/-- The thin verbs found with strong resultatives are exactly the resultless ones. -/
theorem strongResultative_sdiff_thick : strongResultative \ thick = resultless := by decide

/-- *Close* and *lower* are the thin verbs not found with an omission or quality subject. -/
theorem thin_without_omission : thickᶜ \ omissionSubject = {.close, .lower} := by decide

/-- The thick verbs found with an omission subject, each under a reinterpretation of the
subject as a productive cause. -/
theorem thick_inter_omissionSubject :
    thick ∩ omissionSubject = {.burn, .lift, .lock, .melt} := by
  decide

/-- The alternation column agrees with the fragment's diatheses except on *cool*. -/
theorem alternating_iff_hasCausativeAlternation :
    ∀ s, s ≠ .cool → (s ∈ alternating ↔ s.entry.valency.HasCausativeAlternation) := by
  decide

/-- The position of a verb's root on the paper's analysis. The root of a causative manner verb
is a predicate of the causing event adjoined to `v`, and any other root is a predicate of the
result state in the complement of `v`. -/
def rootPosition (s : Sample) : ArgumentStructure.Root.Position :=
  if s ∈ causativeMannerVerbs then .adjoined else .complement

theorem mem_thick_of_rootPosition {s : Sample} (h : s.rootPosition = .adjoined) : s ∈ thick := by
  unfold rootPosition at h
  split_ifs at h with hs
  exact causativeMannerVerbs_subset_thick hs

end Sample

end MartinRoseNichols2025
