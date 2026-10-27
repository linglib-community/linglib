module

public import Linglib.Semantics.Events.Basic
public import Studies.KoontzGarboden2009
public import Linglib.Semantics.Presupposition.Again
public import Linglib.Core.Order.UpperLower.Finset
public import Linglib.Core.Order.Concept
public import Mathlib.Tactic.DeriveFintype

/-!
# Krejci (2012): Causativization as Antireflexivization: A Study of Middle and Ingestive Verbs

Krejci explains why middle and ingestive verbs (*wash*, *dress*; *eat*, *learn*) causativize
like intransitives in languages that mark causatives morphologically. The report orders verb
classes on a hierarchy of causativizability, unaccusatives before middles and ingestives before
unergatives before simple transitives, on which no language's causative process skips a tier.
The simple forms of these verbs are lexically reflexive, with an already causative event
structure whose causer and causee are coidentified, and the lexical causative (*feed*, *teach*)
arises by antireflexivization, which delinks the two arguments; this is Koontz-Garboden's
reflexivization read in the opposite direction. On a model of *eat*, *feed* and *make eat*, the
entailments of the simple form split between causer and causee of the lexical causative but
stay with the causee of the periphrastic one.

## Implementation notes

* The model takes the verb's event to be the change of state and closes the causing event
  existentially, as `KoontzGarboden2009.causative` does; *make eat* adds a second causing
  event with its own effector.
* Of the report's three tests of event-structural complexity only *again* is formalized;
  *re-* and *almost* have the same scopal structure. States are times in the model, a change
  giving rise to the state at its end, so that *again* on the result state has earlier states
  to presuppose.
* The Marathi evidence and the twenty surveyed languages outside Table 2.8 are not
  formalized.

## References

* [krejci-2012]
* [koontz-garboden-2009]
* [chierchia-2004]
* [dowty-1979]
-/

@[expose] public section

namespace Krejci2012

open Event (τ)

open KoontzGarboden2009 ArgumentStructure
open scoped SetRel

/-! ### Antireflexivization -/

section Model

variable {Entity State T E : Type*} [LinearOrder T] [Event.TemporalTrace E T]
  (M : ArgumentStructure.EventStructure.Interpretation Entity State E)
  (manip : Entity → E → Prop) (S : Entity → State → Prop)

/-- In the lexical causative (38a) the causer's manipulation of food brings the causee to the
state of potential digestion. -/
abbrev feed : Entity → Entity → E → Prop := causative M manip S

/-- The simple form (37a) is the lexical causative on its diagonal, where the eater manipulates
the food and comes to digest it. Antireflexivization ((96)–(97)) delinks the two arguments. -/
abbrev eat : Entity → E → Prop := reflexivize (feed M manip S)

/-- The periphrastic causative *make eat* adds a further causing event, with its own effector,
of an eating. -/
def makeEat (z x : Entity) (e : E) : Prop :=
  ∃ w, M.effector z w ∧ w ~[M.cause] e ∧ eat M manip S x e

/-- Causativization by causer addition ((94)) is the analysis the report rejects, on which the
simple form is an activity `ingest` with no causing subevent and the causative adds a causer. -/
def causerAddition (ingest : Entity → E → Prop) (y x : Entity) (e : E) : Prop :=
  ∃ w, M.effector y w ∧ w ~[M.cause] e ∧ ingest x e

/-- `earlier` relates an event to the events whose run time is before its own. -/
def earlier : SetRel E E := {(e, e') | (τ e').snd ≤ (τ e).fst}

/-- On the restitutive reading *again* modifies only the result state ((66a)), so the state
predicate holds of a state that an earlier state of it preceded, whether or not a change brought
that earlier state about ((65a)). `R` relates a state to the earlier states. The restitutive
reading of a verb is the verb over this predicate. -/
def againState (R : SetRel State State) (S : Entity → State → Prop) (x : Entity)
    (s : State) : Prop :=
  Presupposition.again R (S x) s = 1

/-- On the repetitive reading *again* modifies the whole predicate ((66b)), so the sentence
presupposes that the whole event happened before. -/
def Repetitive (P : Entity → E → Prop) (x : Entity) (e : E) : Prop :=
  Presupposition.again earlier (P x) e = 1

variable {M manip S} {x y z : Entity} {e : E}

theorem eat_eq_anticausative : eat M manip S = anticausative M manip S := rfl

-- (39a)
theorem exists_manip_of_eat (h : eat M manip S x e) : ∃ w, manip x w ∧ w ~[M.cause] e :=
  exists_cause_of_anticausative h

-- (45)
theorem exists_manip_of_feed (h : feed M manip S y x e) : ∃ w, manip y w ∧ w ~[M.cause] e :=
  let ⟨w, h₁, h₂, _⟩ := h; ⟨w, h₁, h₂⟩

-- (44c)
theorem inchoative_of_feed (h : feed M manip S y x e) : M.vBecome S x e :=
  let ⟨_, _, _, h⟩ := h; h

-- (47a)
theorem exists_manip_of_makeEat (h : makeEat M manip S z x e) :
    ∃ w, manip x w ∧ w ~[M.cause] e :=
  let ⟨_, _, _, h⟩ := h; exists_manip_of_eat h

-- (95)
theorem ingest_of_causerAddition {ingest : Entity → E → Prop}
    (h : causerAddition M ingest y x e) : ingest x e :=
  let ⟨_, _, _, h⟩ := h; h

-- (114a)
theorem licensesBySelf_eat (h : ∀ x w, manip x w → M.effector x w) :
    LicensesBySelf M (eat M manip S) :=
  fun _ _ he ↦ let ⟨w, hm, hc⟩ := exists_manip_of_eat he; ⟨w, hc, h _ _ hm⟩

end Model

/-! ### Mary and John -/

/-- A `Participant` is Mary or John. -/
inductive Participant
  | mary
  | john
  deriving DecidableEq

/-- `ev s t` is the event running from `s` to `t`. -/
def ev (s t : ℤ) (h : s ≤ t := by decide) : NonemptyInterval ℤ := ⟨(s, t), h⟩

/-- `At w s t` says that the event `w` runs from `s` to `t`. -/
def At (w : NonemptyInterval ℤ) (s t : ℤ) : Prop := (τ w).toProd = (s, t)

def w₀ : NonemptyInterval ℤ := ev 0 1
def e₀ : NonemptyInterval ℤ := ev 1 2
def w₁ : NonemptyInterval ℤ := ev 0 2
def w₂ : NonemptyInterval ℤ := ev 3 4
def e₁ : NonemptyInterval ℤ := ev 4 5

/-- The state of potential digestion holds of John after each meal of the scenarios below, the
states at the times 2 and 5. -/
def digesting (x : Participant) (s : ℤ) : Prop := x = .john ∧ (s = 2 ∨ s = 5)

/-- `eating causing eff` is the model in which the events `causing` lists bring John to potential
digestion, with `eff` the effectors of events. States are times, and a change gives rise to the
state at its end. -/
def eating (causing : NonemptyInterval ℤ → NonemptyInterval ℤ → Prop)
    (eff : Participant → NonemptyInterval ℤ → Prop) :
    ArgumentStructure.EventStructure.Interpretation Participant ℤ (NonemptyInterval ℤ) where
  become := {p | (∃ w, causing w p.2) ∧ p.1 = (τ p.2).toProd.2}
  cause := {p | causing p.1 p.2}
  effector := eff

/-- Mary manipulates the food. -/
def spoonManip (y : Participant) (w : NonemptyInterval ℤ) : Prop := y = .mary ∧ At w 0 1

/-- In spoon feeding ((44a)) Mary's manipulation of the food causes John's change. -/
def spoonFeeding :
    ArgumentStructure.EventStructure.Interpretation Participant ℤ (NonemptyInterval ℤ) :=
  eating (fun w e ↦ At w 0 1 ∧ At e 1 2) spoonManip

/-- John manipulates the food. -/
def supManip (y : Participant) (w : NonemptyInterval ℤ) : Prop := y = .john ∧ At w 0 1

/-- Under supervision ((48)) John's manipulation of the food and Mary's supervising action both
cause John's change. -/
def supervising :
    ArgumentStructure.EventStructure.Interpretation Participant ℤ (NonemptyInterval ℤ) :=
  eating (fun w e ↦ (At w 0 1 ∨ At w 0 2) ∧ At e 1 2)
    (fun y w ↦ (y = .john ∧ At w 0 1) ∨ (y = .mary ∧ At w 0 2))

/-- Mary manipulates the food the first time, John the second. -/
def twoManip (y : Participant) (w : NonemptyInterval ℤ) : Prop :=
  (y = .mary ∧ At w 0 1) ∨ (y = .john ∧ At w 3 4)

/-- In the model of two meals Mary feeds John, and later John eats. -/
def twoMeals :
    ArgumentStructure.EventStructure.Interpretation Participant ℤ (NonemptyInterval ℤ) :=
  eating (fun w e ↦ (At w 0 1 ∧ At e 1 2) ∨ (At w 3 4 ∧ At e 4 5)) twoManip

/-- *I didn't eat pie; you fed pie to me* ((92), (106)) is consistent, since John, fed by Mary,
manipulated no food (44a). -/
theorem not_eat_and_feed :
    ¬ eat spoonFeeding spoonManip digesting .john e₀ ∧
      feed spoonFeeding spoonManip digesting .mary .john e₀ :=
  ⟨fun ⟨_, ⟨h, _⟩, _⟩ ↦ Participant.noConfusion h,
    ⟨w₀, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, 2, ⟨⟨w₀, rfl, rfl⟩, rfl⟩, rfl, .inl rfl⟩⟩

/-- Feeding is not making eat, since John, fed, was not made to eat, as whoever is made to eat
manipulates food ((47a)). -/
theorem feed_not_makeEat :
    feed spoonFeeding spoonManip digesting .mary .john e₀ ∧
      ¬ makeEat spoonFeeding spoonManip digesting .mary .john e₀ :=
  ⟨not_eat_and_feed.2, fun ⟨_, _, _, h⟩ ↦ not_eat_and_feed.1 h⟩

-- (48)
theorem makeEat_not_feed :
    makeEat supervising supManip digesting .mary .john e₀ ∧
      ¬ feed supervising supManip digesting .mary .john e₀ :=
  ⟨⟨w₁, Or.inr ⟨rfl, rfl⟩, ⟨Or.inr rfl, rfl⟩, w₀, ⟨rfl, rfl⟩, ⟨Or.inl rfl, rfl⟩, 2,
      ⟨⟨w₀, Or.inl rfl, rfl⟩, rfl⟩, rfl, .inl rfl⟩,
    fun ⟨_, ⟨h, _⟩, _⟩ ↦ Participant.noConfusion h⟩

-- (113d)
theorem not_licensesBySelf_inchoative :
    ¬ LicensesBySelf spoonFeeding (spoonFeeding.vBecome digesting) := fun h ↦
  let ⟨_, _, hw⟩ := h .john e₀ ⟨2, ⟨⟨w₀, rfl, rfl⟩, rfl⟩, rfl, .inl rfl⟩
  Participant.noConfusion hw.1

/-- Said after Mary fed John as in (70), *John ate again* is true on the restitutive reading (66a)
and false on the repetitive one. -/
theorem restitutive_not_repetitive :
    eat twoMeals twoManip (againState {p | p.2 < p.1} digesting) .john e₁ ∧
      ¬ Repetitive (eat twoMeals twoManip digesting) .john e₁ :=
  ⟨⟨w₂, Or.inr ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩, 5, ⟨⟨w₂, Or.inr ⟨rfl, rfl⟩⟩, rfl⟩,
      Presupposition.again_eq_one_iff.2 ⟨⟨2, by decide, rfl, .inl rfl⟩, rfl, .inr rfl⟩⟩,
    fun h ↦ by
      obtain ⟨⟨e', hb, w, hm, hc, _⟩, _⟩ := Presupposition.again_eq_one_iff.1 h
      rcases hm with ⟨h, _⟩ | ⟨_, hw⟩
      · exact Participant.noConfusion h
      rcases hc with ⟨h, _⟩ | ⟨_, he⟩
      · exact absurd (hw.symm.trans h) (by decide)
      · have hb' : (τ e').toProd.2 ≤ 4 := hb
        rw [he] at hb'
        exact absurd hb' (by decide)⟩

/-! ### The hierarchy of causativizability -/

/-- A `Tier` is a tier of the hierarchy (22), from the most readily causativized. -/
inductive Tier
  | unaccusative
  | middleIngestive
  | unergative
  | simpleTransitive
  deriving DecidableEq, Fintype, Repr

/-- `t.rank` is the position of the tier `t` on the hierarchy. -/
def Tier.rank : Tier → ℕ
  | .unaccusative => 0
  | .middleIngestive => 1
  | .unergative => 2
  | .simpleTransitive => 3

instance : LinearOrder Tier := LinearOrder.lift' Tier.rank (by decide)

/-- A causative process of a language is the set of tiers whose verbs it applies to. -/
structure Causative where
  language : String
  morpheme : String
  reach : Finset Tier

namespace Causative

/-- A process respects the hierarchy when it reaches every tier before a tier it reaches. -/
def RespectsHierarchy (c : Causative) : Prop := IsLowerSet (↑c.reach : Set Tier)

instance : DecidablePred RespectsHierarchy := fun _ ↦ inferInstanceAs (Decidable (IsLowerSet _))

/-- The type of a process, (1) to (4) of Table 2.8, is the last tier it reaches. -/
def type (c : Causative) : WithBot Tier := c.reach.max

theorem mem_reach_iff {c : Causative} (h : c.RespectsHierarchy) (t : Tier) :
    t ∈ c.reach ↔ ↑t ≤ c.type :=
  h.mem_iff_le_max

end Causative

/-- `table` lists the surveyed languages of Table 2.8, three of each type. Malayalam reaches
transitives only with an instrumental causee and is listed with the third type. -/
def table : List Causative :=
  [⟨"Slave", "-h-", {.unaccusative}⟩,
   ⟨"Mapudungun", "-ɨm", {.unaccusative}⟩,
   ⟨"Classical Nahuatl", "-tia", {.unaccusative}⟩,
   ⟨"Cora", "-te", {.unaccusative, .middleIngestive}⟩,
   ⟨"Marathi", "-aw", {.unaccusative, .middleIngestive}⟩,
   ⟨"Amharic", "a-", {.unaccusative, .middleIngestive}⟩,
   ⟨"Ahtna", "-ɬ-", {.unaccusative, .middleIngestive, .unergative}⟩,
   ⟨"Tariana", "-i-ta", {.unaccusative, .middleIngestive, .unergative}⟩,
   ⟨"Malayalam", "-icc", {.unaccusative, .middleIngestive, .unergative}⟩,
   ⟨"Basque", "-arazi", {.unaccusative, .middleIngestive, .unergative, .simpleTransitive}⟩,
   ⟨"Dulong/Rawang", "shv-", {.unaccusative, .middleIngestive, .unergative, .simpleTransitive}⟩,
   ⟨"Koyukon", "-ɬ-", {.unaccusative, .middleIngestive, .unergative, .simpleTransitive}⟩]

/-- The survey as a formal context, a surveyed process bearing the tiers it reaches. -/
def Reaches (c : {c // c ∈ table}) (t : Tier) : Prop := t ∈ c.1.reach

/-- The hierarchy is the order of implication among the tiers in the survey, one tier coming
before another exactly when every surveyed process that reaches the second reaches the first. -/
theorem ofAttribute_reaches_le_iff {t t' : Tier} :
    Concept.ofAttribute Reaches t' ≤ Concept.ofAttribute Reaches t ↔ t ≤ t' := by
  rw [Concept.ofAttribute_le_ofAttribute_iff]
  simp only [Reaches, Subtype.forall]
  revert t t'
  decide

/-- No surveyed language skips a tier. -/
theorem table_respectsHierarchy : ∀ c ∈ table, c.RespectsHierarchy := fun c hc ↦
  Concept.antitone_ofAttribute_iff.1 (fun _ _ h ↦ ofAttribute_reaches_le_iff.2 h) ⟨c, hc⟩

end Krejci2012
