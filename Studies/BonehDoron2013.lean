module

public import Linglib.Data.Examples.BonehDoron2013
public import Linglib.Semantics.Genericity.Normality
public import Linglib.Semantics.Mereology
public import Linglib.Semantics.Modality.Necessity
public import Linglib.Semantics.Tense.Perspective
public import Studies.IatridouEtAl2001

/-!
# Boneh and Doron (2013): Hab and Gen in the expression of habituality

[boneh-doron-2013] derive English habituals from two covert modal operators and two auxiliaries
that mark aspect and mood. Hab holds of a state that an event indicating a disposition initiates
and that lies, in every world of a gnomic modal base, within an iteration of events; Gen is a
modalized universal over the restricted individuals within an interval. *Used to* is the
retrospective over the imperfective, placing the reference interval before the perspective
time, and *would* is Gen with a restriction and an interval from the context.

## Implementation notes

* States and events share one event domain with a temporal trace. The modal base `MB_{i,w}` is
  indexed by intervals, and (13) and (21) quantify over all its worlds; the ordering of the worlds
  by closeness to an ideal world is in the chapter's prose, not its formulas.
* Iteration (14) is `Mereology.IsPlural`, its gloss: a sum of `P`-events with at least two proper
  `P`-parts. The chapter leaves "indicating a disposition" unanalyzed, so the events that do are a
  parameter.
* The imperfective (19a) is non-strict containment, `Aspect.UNBOUNDED`. The retrospective (19b)
  is the perspectival past of `Tense.Perspective`, a reference interval strictly preceding the
  perspective time and so disjoint from it, as (34b) says; the internal perspective is the
  perspectival present, overlap.
* Gen (21) ranges over individuals, objects or events, so it takes their temporal extent, an
  event's run time or an object's life span, as an argument.
* The perfect of (32) and (33) is the universal perfect of `IatridouEtAl2001`, *since then*
  setting the left boundary of its span. With *used to* the chapter reads *since then* as a
  reference interval stretching to the perspective time.

## Errata

* The denotations (18) and (19) make (42c) true in its context (`usedTo_hab_of_single_trip`).
  Its falsity rests on an assumption the chapter states only in prose in §6.3.2, that a property
  characterizes an interval only if the interval is extended and the property is actualized at
  both of its ends (`Characterizes`).
* The second disjunct of (22b), `∃Q Gen(P_C, Q, i_C, w)`, holds of every restriction through the
  empty restrictor, since Gen (21) has no existential import, so (22b) does not constrain the
  context.

## TODO

* Telling (2c) from (2d) by (22b) needs Gen to presuppose that its restrictor is nonempty.
* The puzzle of (47)–(50) and the contrast (48): Gen over French teachers by their life spans,
  the kind reading of the bare plural, and the clash of an individual-level predicate with an
  episodic restrictor.
* Table (41): the perfective habitual of the simple form, (26)–(27), and the periphrastic forms'
  selection of the imperfective.

## References

* [boneh-doron-2013]
* [link-1983]
* [kratzer-1981]
* [kamp-reyle-1993]
* [pancheva-2003]
* [iatridou-anagnostopoulou-izvorski-2001]
-/

@[expose] public section

namespace BonehDoron2013

open Event (τ)
open Aspect (UNBOUNDED PERF durative)
open Modality (Background simpleNecessity)
open scoped Denotes

variable {W E T : Type*} [LinearOrder T] [Event.TemporalTrace E T]

/-! ### Hab and Gen, (12)–(22) -/

/-- A state is initiated, (15), when an event that `D` says indicates the disposition precedes
it. -/
def Initiated (D : W → E → Prop) (w : W) (s : E) : Prop :=
  ∃ e, (τ e).Precedes (τ s) ∧ D w e

/-- Hab, (13): a state is a `P`-habit when it is initiated and lies, in every world of the modal
base at its run time, within an iteration of `P`-events (14). -/
def Hab [SemilatticeSup E] (mb : NonemptyInterval T → Background W) (D P : W → E → Prop) (w : W)
    (s : E) : Prop :=
  Initiated D w s ∧
    ∀ w' ∈ (mb (τ s)).accessibleWorlds w, ∃ e, τ s ≤ τ e ∧ Mereology.IsPlural (P w') e

/-- With the indefinite over Hab, (8), a predicate that no object satisfies twice, such as smoking
a given cigarette, has no habit over a consistent modal base, (4b) and (9b). -/
theorem not_hab_of_subsingleton [SemilatticeSup E] {mb : NonemptyInterval T → Background W}
    {D P : W → E → Prop} {w : W} {s : E} (hmb : ((mb (τ s)).accessibleWorlds w).Nonempty)
    (hP : ∀ v a b, P v a → P v b → a = b) : ¬ Hab mb D P w s := fun ⟨_, h⟩ ↦
  let ⟨w', hw'⟩ := hmb
  let ⟨e, _, he⟩ := h w' hw'
  Mereology.not_isPlural_of_subsingleton (hP w') e he

/-- Gen, (21): every `Q`-individual whose temporal extent `ext` lies within the interval `i` is a
`P`-individual throughout the modal base at `i`. It is GEN with every case normal and the
modality in the matrix. -/
def Gen {Z : Type*} (ext : Z → NonemptyInterval T) (mb : NonemptyInterval T → Background W)
    (P Q : W → Z → Prop) (i : NonemptyInterval T) (w : W) : Prop :=
  (i, w) ∈ (⊤ : Genericity.Normality (NonemptyInterval T × W) Z).gen {z | ext z ≤ i ∧ Q w z}
    {z | simpleNecessity (mb i) (P · z) w}

theorem gen_iff {Z : Type*} {ext : Z → NonemptyInterval T} {mb : NonemptyInterval T → Background W}
    {P Q : W → Z → Prop} {i : NonemptyInterval T} {w : W} :
    Gen ext mb P Q i w ↔ ∀ z, ext z ≤ i → Q w z → simpleNecessity (mb i) (P · z) w :=
  ⟨fun h _ hi hQ ↦ h ⟨hi, hQ⟩, fun h z hz ↦ h z hz.1 hz.2⟩

-- The second disjunct of (22b) holds of every restriction, through the empty restrictor.
example (mb : NonemptyInterval T → Background W) (Pc : W → E → Prop) (ic : NonemptyInterval T)
    (w : W) : ∃ Q, Gen τ mb Pc Q ic w :=
  ⟨fun _ _ ↦ False, gen_iff.2 fun _ _ h ↦ h.elim⟩

/-! ### *Used to*, (18)–(19) and (28)–(37) -/

section Retro

variable {A : W → Set (NonemptyInterval T)} {P : W → E → Prop} {w : W} {p : NonemptyInterval T}
  {t t₀ : T}

/-- The retrospective, (19b), holds at a perspective interval that a reference interval of `A`
precedes, the perspectival past. -/
def retro (A : W → Set (NonemptyInterval T)) : W → Set (NonemptyInterval T) :=
  fun w ↦ (Tense.Perspective.toSetRel Allen.precedes).preimage (A w)

/-- *Used to*, (18): the retrospective over the imperfective (19a). -/
def usedTo (P : W → E → Prop) : W → Set (NonemptyInterval T) :=
  retro (UNBOUNDED P)

theorem usedTo_eq_preimage : usedTo P w = (Allen.toSetRel (Allen.inv Allen.precedes)).preimage
    ((Allen.toSetRel Allen.le).preimage (τ '' {e | P w e})) := by
  rw [usedTo, retro, Tense.Perspective.toSetRel_eq_inv, ← Allen.toSetRel_inv,
    Aspect.unbounded_eq_preimage]

/-- The composite of the retrospective and the imperfective: the state began before the
perspective time, and may have ended at any time after that. -/
theorem comp_retro_imperfective :
    Allen.comp (Allen.inv Allen.precedes) Allen.le = Allen.atoms.filter (·.fstFst = .gt) := by
  decide +kernel

/-- *Used to* says only that a state began before the perspective time, which the state may
outlast, so the retrospectivity of (28) is an implicature, cancelled in (30) and (31). -/
theorem mem_usedTo_iff : p ∈ usedTo P w ↔ ∃ e, P w e ∧ (τ e).fst < p.fst := by
  constructor
  · intro h
    rw [usedTo_eq_preimage] at h
    obtain ⟨_, ⟨e, hP, rfl⟩, h⟩ := Allen.preimage_toSetRel_subset_comp _ h
    rw [Allen.mem_toSetRel, comp_retro_imperfective] at h
    exact ⟨e, hP, compare_gt_iff_gt.1 (Finset.mem_filter.1 h).2⟩
  · rintro ⟨e, hP, hlt⟩
    exact ⟨.pure (τ e).fst, ⟨e, NonemptyInterval.le_def.2 ⟨le_rfl, (τ e).fst_le_snd⟩, hP⟩,
      Tense.Perspective.mem_toSetRel.2 (Tense.Perspective.presup_precedes.2 hlt)⟩

/-- *Since then*, (33), *now*, (35), and a simultaneous reading, (36)–(37), need reference
intervals overlapping the perspective time, and none of these serves the retrospective. -/
theorem not_mem_retro_of_overlaps (h : ∀ i ∈ A w, i.Overlaps p) : p ∉ retro A w :=
  fun ⟨i, hi, hp⟩ ↦
    NonemptyInterval.Precedes.not_overlaps
      (Tense.Perspective.presup_precedes.1 (Tense.Perspective.mem_toSetRel.1 hp)) (h i hi)

/-- The universal perfect over a span begun before its time of tense entails *used to*, which
unlike it does not assert the state at that time (`IatridouEtAl2001.universal_at_rb`), so the two
form the scale of (32). -/
theorem usedTo_of_universal (h : (w, t) ∈ PERF ({i | i.fst < t} ∩ durative (UNBOUNDED P) ·)) :
    .pure t ∈ usedTo P w :=
  let ⟨_, ⟨hlt, hd⟩, _⟩ := h
  let ⟨e, hle, hP⟩ := hd (Set.mem_Iic.2 le_rfl)
  mem_usedTo_iff.2 ⟨e, hP, (NonemptyInterval.le_def.1 hle).1.trans_lt hlt⟩

/-- `P` characterizes the interval `i` at `w`, the assumption of §6.3.2, when `i` is extended and
`P` is actualized at both of its ends. -/
def Characterizes (P : W → E → Prop) (w : W) (i : NonemptyInterval T) : Prop :=
  i.fst < i.snd ∧ (∃ e, P w e ∧ i.fst ∈ τ e) ∧ ∃ e, P w e ∧ i.snd ∈ τ e

/-- A state that began before `t₀` and lasts to `t` verifies *used to* together with *still*, (30),
and the perfect with *since then*, (33a), but not *used to* with *since then*, (33b). The simple
past takes *now*, which needs its reference interval to overlap the perspective time, and *used
to* does not, (35). -/
theorem perspective_rows {e : E} (he : P w e) (h₀ : (τ e).fst < t₀) (h₁ : t₀ ≤ t)
    (h₂ : t ≤ (τ e).snd) :
    (.pure t ∈ usedTo P w ∧ .pure t ∈ UNBOUNDED P w ↔ Examples.ex30.judgment = .acceptable) ∧
    ((w, t) ∈ PERF ({i | i.fst = t₀} ∩ durative (UNBOUNDED P) ·) ↔
      Examples.ex33a.judgment = .acceptable) ∧
    (.pure t ∈ retro (fun w ↦ {i | i.fst = t₀ ∧ i.snd = t} ∩ UNBOUNDED P w) w ↔
      Examples.ex33b.judgment = .acceptable) ∧
    ((∃ i ∈ UNBOUNDED P w, i.Overlaps (.pure t)) ↔ Examples.ex35a.judgment = .acceptable) ∧
    (.pure t ∈ retro (fun w ↦ {i | i.Overlaps (.pure t)} ∩ UNBOUNDED P w) w ↔
      Examples.ex35b.judgment = .acceptable) := by
  have ht : .pure t ∈ UNBOUNDED P w :=
    ⟨e, NonemptyInterval.le_def.2 ⟨h₀.le.trans h₁, h₂⟩, he⟩
  refine ⟨iff_of_true ⟨mem_usedTo_iff.2 ⟨e, he, h₀.trans_le h₁⟩, ht⟩ rfl,
    iff_of_true (IatridouEtAl2001.universal_of_covers he h₁ h₀.le h₂) rfl,
    iff_of_false (not_mem_retro_of_overlaps fun i ⟨⟨_, hi⟩, _⟩ ↦
      ⟨i.fst_le_snd.trans hi.le, hi.ge⟩) (by decide),
    iff_of_true ⟨_, ht, NonemptyInterval.overlaps_refl _⟩ rfl,
    iff_of_false (not_mem_retro_of_overlaps fun _ h ↦ h.1) (by decide)⟩

end Retro

/-! ### The chapter's examples

The model has an actual world `false` and one gnomic alternative `true`, accessible at every
time. Events are intervals of natural-number times, their own run times, with the convex hull as
sum, and the event indicating a disposition happens at time `0`. -/

section Model

/-- The gnomic modal base, whose one premise is to be the alternative `true`. -/
def gnomic : NonemptyInterval ℕ → Background Bool := fun _ _ ↦ {(· = true)}

/-- The event indicating a disposition, at time `0`. -/
def indicating : Bool → NonemptyInterval ℕ → Prop := fun _ e ↦ e = .pure 0

/-- An object undergoes the event once, at its own time, as a cigarette is smoked or a rabbit
killed. -/
def onceAt : Bool → NonemptyInterval ℕ → ℕ → Prop := fun _ e x ↦ e = .pure x

/-- The object may undergo the event at any time, as a flower grows out. -/
def repeatable : Bool → NonemptyInterval ℕ → Unit → Prop := fun _ e _ ↦ ∃ t, e = .pure t

/-- Ruti's trips to work: one actual trip at time `1`, and a trip at every time in the
alternative. -/
def toWork : Bool → NonemptyInterval ℕ → Prop
  | true, e => ∃ t, e = .pure t
  | false, e => e = .pure 1

/-- Travelling by bus, as every trip from time `1` on does. -/
def byBus : Bool → NonemptyInterval ℕ → Prop := fun _ e ↦ 1 ≤ e.fst

/-- Going to work by bus. -/
def bus : Bool → NonemptyInterval ℕ → Prop := fun w e ↦ toWork w e ∧ byBus w e

/-- Ruti's habit, from her first trip to her death. -/
def habit : NonemptyInterval ℕ := ⟨(1, 2), by decide⟩

private theorem hab_habit {P : Bool → NonemptyInterval ℕ → Prop} (h₁ : P true (.pure 1))
    (h₂ : P true (.pure 2)) : Hab gnomic indicating P false habit := by
  refine ⟨⟨.pure 0, by decide, rfl⟩, fun w' hw' ↦ ⟨habit, le_rfl, ?_⟩⟩
  obtain rfl : w' = true := by simpa [gnomic] using hw'
  have h : NonemptyInterval.pure 1 ⊔ .pure 2 = habit := rfl
  exact ⟨h ▸ .sum (.base h₁) (.base h₂), .pure 1, by decide, .pure 2, by decide, h₁, h₂,
    by decide⟩

/-- Ruti's habit of going to work by bus holds though she went once, (42a), as a habit initiated
by a single event does, (16)–(17). -/
theorem hab_of_single_trip :
    Hab gnomic indicating bus false habit ∧ ¬ ∃ e, Mereology.IsPlural (bus false) e := by
  refine ⟨hab_habit ⟨⟨1, rfl⟩, le_rfl⟩ ⟨⟨2, rfl⟩, Nat.le_succ 1⟩,
    fun ⟨e, he⟩ ↦ Mereology.not_isPlural_of_subsingleton ?_ e he⟩
  rintro _ _ ⟨rfl, -⟩ ⟨rfl, -⟩
  rfl

-- (18), (19), (42), (42c)
theorem usedTo_hab_of_single_trip : .pure 5 ∈ usedTo (Hab gnomic indicating bus) false :=
  mem_usedTo_iff.2 ⟨habit, hab_of_single_trip.1, by decide⟩

/-- Gen with a restrictor admits a fresh cigarette per after-dinner event, (4a) and (5a); with the
indefinite over Hab or over *repeatedly*, smoking a cigarette and killing a rabbit have no
habit, (4b), and no iteration, (7b), while a flower that grows out again has one, (6b). -/
theorem restrictor_rows :
    ((∀ i, Gen τ gnomic (fun w e ↦ ∃ c, onceAt w e c) (fun _ e ↦ ∃ t, e = .pure t) i false) ↔
      Examples.ex4a.judgment = .acceptable) ∧
    ((∃ c s, Hab gnomic indicating (onceAt · · c) false s) ↔
      Examples.ex4b.judgment = .acceptable) ∧
    ((∃ f s, Hab gnomic indicating (repeatable · · f) false s) ↔
      Examples.ex6b.judgment = .acceptable) ∧
    ((∃ r e, Mereology.IsPlural (onceAt false · r) e) ↔
      Examples.ex7b.judgment = .acceptable) :=
  ⟨iff_of_true (fun _ ↦ gen_iff.2 fun _ _ ⟨t, ht⟩ _ _ ↦ ⟨t, ht⟩) rfl,
    iff_of_false (fun ⟨_, _, h⟩ ↦ not_hab_of_subsingleton ⟨true, by simp [gnomic]⟩
      (fun _ _ _ ha hb ↦ ha.trans hb.symm) h) (by decide),
    iff_of_true ⟨(), habit, hab_habit ⟨1, rfl⟩ ⟨2, rfl⟩⟩ rfl,
    iff_of_false (fun ⟨_, e, h⟩ ↦ Mereology.not_isPlural_of_subsingleton
      (fun _ _ ha hb ↦ ha.trans hb.symm) e h) (by decide)⟩

/-- In the context of (42), the habit makes the simple form true, (42a), and supplies *would*'s
restriction, so that *would*, Gen over the trips by (22), is true, (42b); *used to* is false,
(42c), once its reference interval must be characterized by actual trips. -/
theorem actualization_rows :
    (habit ∈ UNBOUNDED (Hab gnomic indicating bus) false ↔
      Examples.ex42a.feature? "truthValue" = some "true") ∧
    ((∃ s, τ s = habit ∧ Hab gnomic indicating toWork false s) ∧
        Gen τ gnomic byBus toWork habit false ↔
      Examples.ex42b.feature? "truthValue" = some "true") ∧
    (.pure 5 ∈ retro (fun w ↦ {i | Characterizes bus w i} ∩ UNBOUNDED (Hab gnomic indicating bus) w)
        false ↔ Examples.ex42c.feature? "truthValue" = some "true") := by
  refine ⟨iff_of_true ⟨habit, le_rfl, hab_of_single_trip.1⟩ (by decide),
    iff_of_true ⟨⟨habit, rfl, hab_habit ⟨1, rfl⟩ ⟨2, rfl⟩⟩,
      gen_iff.2 fun _ _ h _ _ ↦ h ▸ le_rfl⟩ (by decide), iff_of_false ?_ (by decide)⟩
  rintro ⟨i, ⟨⟨hlt, ⟨_, ⟨rfl, -⟩, h₁⟩, _, ⟨rfl, -⟩, h₂⟩, -⟩, -⟩
  rw [Event.τ_nonemptyInterval, NonemptyInterval.mem_pure] at h₁ h₂
  exact hlt.ne (h₁.trans h₂.symm)

end Model

end BonehDoron2013
