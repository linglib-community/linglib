module

public import Linglib.Semantics.Aspect.Viewpoint
public import Linglib.Semantics.Modality.Necessity
public import Linglib.Semantics.Mereology
public import Linglib.Data.Examples.Ferreira2016

/-!
# Ferreira (2016): The semantic ingredients of imperfectivity

Many languages express progressive and habitual readings with one imperfective form, as the
Italian *Gianni fumava* 'Gianni was smoking / used to smoke'. Ferreira derives both readings from
one operator built from three ingredients. The temporal ingredient is ongoingness: the reference
interval lies within the run time of an event. The modal ingredient is Portner's: the event exists
in every best world of a circumstantial modal base for the event description at the reference
interval, ranked by an ordering source of propositions that the eventuality is not interrupted.
The mereological ingredient is a number parameter: the singular operator keeps the minimal events
of the description, and the plural operator its sums of non-overlapping events, so that the
progressive is about a single ongoing event and the habitual about an ongoing plurality.

So *John was crossing the street* is true when a bus stops him, but *John was crossing the
Atlantic* is false of an ordinary swimmer, and *John plays soccer* is true of a regular player
until an accident leaves him unable to move his legs; these scenarios [decide the paper's
judgments](##truthValue_rows). A singular event of a description is never a plural one
(`sg_disjoint_pl`). Statives have no minimal elements, so their imperfectives [cannot be
progressive](##not_mem_IMP_atomize_of_nonatomic), which is why imperfective statives pattern with
habituals. Over a modal base that admits only the actual world, the operator is [Kratzer's
extensional imperfective](##IMP_eq_unbounded_of_isTotallyRealistic), the reference interval within
the run time of an actual event.

## Implementation notes

* The number parameter is an operator on predicates of events: the singular is
  `Mereology.atomize`, the minimal elements, and the plural is `PL`, (12).
* The modal base and ordering source are `Modality.Background`s projected from the description
  and the reference interval, as in (53), and the progressive's event-relative form is
  `Aspect.InProgress`.
* Ongoingness is inclusion, `i ⊆ τ(e)`, the substrate's `Aspect.UNBOUNDED`, not the strict
  `Aspect.IMPF`.
* The run time of a sum is the convex hull of the run times of its parts, so Ferreira's inclusion
  of an interval in a plural interval (31) is inclusion in the hull, and (33) holds. The habitual
  scenario takes its events to be sets of games ordered by inclusion.

## Errata

* (111) applies `MOD` to its arguments in the order `MOD(w)(i)(…)`, though it defines `MOD` as
  `λ℘.λi.λw`; read in its defined order it computes `BEST` from the composite predicate, where (52)
  and (58) compute it from the description `℘`, which `IMP` follows.

## TODO

* The boundedness presuppositions (105) and (109), adverbs of quantification (§2.4), the
  temporal convexity of statives (96)–(98), and counterfactuals (§3) are not formalized.

## References

* [ferreira-2016]
* [portner-1998]
* [kratzer-1998]
* [kratzer-1991]
-/

@[expose] public section

namespace Ferreira2016

open Modality Event Mereology

/-! ### The mereological ingredients -/

section Number

variable {E : Type*} [SemilatticeSup E] {P : E → Prop} {e : E}

/-- `PL` (12): the sums in `P` of pairwise non-overlapping proper parts that are also in `P`. -/
def PL (P : E → Prop) (e : E) : Prop :=
  P e ∧ ∃ s : Finset E, ∃ hs : s.Nonempty, (∀ x ∈ s, x < e ∧ P x) ∧
    (s : Set E).Pairwise (fun x y ↦ ¬ Overlap x y) ∧ s.sup' hs id = e

/-- No singular event of a description is a plural one. -/
theorem sg_disjoint_pl : Disjoint (atomize P) (PL P) := by
  rw [Pi.disjoint_iff]
  intro e
  rw [Prop.disjoint_iff]
  rintro ⟨hmin, -, s, ⟨x, hx⟩, hs, -⟩
  exact (hs x hx).1.not_ge (hmin.2 (hs x hx).2 (hs x hx).1.le)

end Number

/-! ### The imperfective (111) -/

section Imp

variable {E W T : Type*} [LinearOrder T] [TemporalTrace E T]

/-- `IMP` (111), with Portner's `BEST` (52), (53): in every best world of the circumstantial base
for the description `P` at the reference interval, ranked by the ordering source, the reference
interval lies within the run time of an event of type `N (P v)`. -/
def IMP (N : (E → Prop) → E → Prop)
    (circ ord : (W → E → Prop) → NonemptyInterval T → Background W) (P : W → E → Prop) :
    W → Set (NonemptyInterval T) :=
  fun w ↦ {t | necessity (circ P t) (ord P t) (fun v ↦ t ∈ Aspect.UNBOUNDED (fun v ↦ N (P v)) v) w}

variable {N : (E → Prop) → E → Prop} {circ ord : (W → E → Prop) → NonemptyInterval T → Background W}
  {P : W → E → Prop} {w : W} {t : NonemptyInterval T}

theorem mem_IMP_iff : t ∈ IMP N circ ord P w ↔
    ∀ v ∈ bestWorlds (circ P t) (ord P t) w, ∃ e, t ≤ τ e ∧ N (P v) e :=
  necessity_iff ..

/-- Over a modal base that admits only the world of evaluation, the imperfective is Kratzer's
extensional one: the reference interval lies within the run time of an actual event. -/
theorem IMP_eq_unbounded_of_isTotallyRealistic (h : ∀ P t, (circ P t).IsTotallyRealistic) :
    IMP N circ ord P w = Aspect.UNBOUNDED (fun v ↦ N (P v)) w := by
  ext t
  refine ⟨fun ht ↦ (h P t).necessity_le_id (ord P t) _ w ht, fun ht v hv ↦ ?_⟩
  have hacc : v ∈ (circ P t).accessibleWorlds w := (mem_bestWorlds.1 hv).1
  rw [h P t w, Set.mem_singleton_iff] at hacc
  exact hacc ▸ ht

/-- A non-atomic description, every event of which has a proper part of the same description, as
statives are (94), has no progressive imperfective wherever the modal base has a best world. -/
theorem not_mem_IMP_atomize_of_nonatomic [PartialOrder E] (hP : ∀ v e, P v e → ∃ e' < e, P v e')
    (hne : (bestWorlds (circ P t) (ord P t) w).Nonempty) : t ∉ IMP atomize circ ord P w := by
  intro h
  obtain ⟨v, hv⟩ := hne
  obtain ⟨e, -, hmin⟩ := mem_IMP_iff.1 h v hv
  obtain ⟨e', hlt, he'⟩ := hP v e hmin.1
  exact hlt.not_ge (hmin.2 he' hlt.le)

end Imp

/-! ### Progressives (45), (46)

Events are intervals of natural numbers. John's crossing so far ends at time `1`; a complete
crossing is the interval `[0, 3]`. -/

/-- The complete crossing. -/
def crossing : NonemptyInterval ℕ := ⟨(0, 3), by decide⟩

/-- The reference interval, while John is still crossing. -/
def now : NonemptyInterval ℕ := ⟨(1, 1), le_rfl⟩

theorem now_le_crossing : now ≤ crossing := NonemptyInterval.le_def.2 ⟨by decide, by decide⟩

/-- The worlds of the crossing scenarios: in `crosses` John gets across, in `stopped` he does
not. -/
inductive Crossing
  | crosses
  | stopped
  deriving DecidableEq, Fintype

/-- *John cross the street* (or *the Atlantic*): a complete crossing in the world where he gets
across. -/
def cross (v : Crossing) (e : NonemptyInterval ℕ) : Prop := v = .crosses ∧ e = crossing

theorem atomize_cross : atomize (cross .crosses) crossing :=
  ⟨⟨rfl, rfl⟩, fun _ ⟨_, hy⟩ _ ↦ hy ▸ le_rfl⟩

/-- The street (45): the facts about John and the street exclude neither world, and the ordering
source prefers the world where nothing interrupts him. -/
def streetBase : (Crossing → NonemptyInterval ℕ → Prop) → NonemptyInterval ℕ →
    Background Crossing :=
  fun _ _ _ ↦ ∅

/-- `NI`: John is not interrupted. -/
def notInterrupted : (Crossing → NonemptyInterval ℕ → Prop) → NonemptyInterval ℕ →
    Background Crossing :=
  fun _ _ _ ↦ {(· ≠ .stopped)}

/-- The Atlantic (46): the facts about John and the ocean exclude his getting across. -/
def atlanticBase : (Crossing → NonemptyInterval ℕ → Prop) → NonemptyInterval ℕ →
    Background Crossing :=
  fun _ _ _ ↦ {(· ≠ .crosses)}

theorem mem_IMP_street : now ∈ IMP atomize streetBase notInterrupted cross .stopped := by
  rw [mem_IMP_iff]
  intro v hv
  have hacc : v ∈ Background.accessibleWorlds
      (streetBase cross now ⊔ notInterrupted cross now) .stopped := by
    rw [← bestWorlds_eq_accessibleWorlds_sup ⟨.crosses, by
      simp [Background.accessibleWorlds_sup, streetBase, notInterrupted]⟩]
    exact hv
  obtain rfl : v = .crosses := by
    cases v
    · rfl
    · simp [Background.accessibleWorlds_sup, streetBase, notInterrupted] at hacc
  exact ⟨crossing, now_le_crossing, atomize_cross⟩

theorem not_mem_IMP_atlantic : now ∉ IMP atomize atlanticBase notInterrupted cross .stopped := by
  rw [mem_IMP_iff]
  intro h
  have hbest : Crossing.stopped ∈ bestWorlds (atlanticBase cross now) (notInterrupted cross now)
      .stopped := by
    refine mem_bestWorlds.2 ⟨by simp [atlanticBase], fun v hv _ ↦ ?_⟩
    have : v = .stopped := by cases v <;> simp_all [atlanticBase]
    exact this ▸ (premisePreorder _).le_refl _
  obtain ⟨e, -, he⟩ := h _ hbest
  exact absurd he.1.1 (by decide)

/-! ### Habituals (54)

The events are sets of games, ordered by inclusion, and a set of games runs from its first to its
last game. In `plays` John plays at times `0`, `2`, `4` and `6`; in `accident` he cannot move his
legs after time `2`. The sentence is uttered at time `3`. -/

/-- The run time of a set of games, from its first game to its last. -/
def hull (s : Finset ℕ) : NonemptyInterval ℕ :=
  if h : s.Nonempty then ⟨(s.min' h, s.max' h), Finset.min'_le_max' _ h⟩ else ⟨(0, 0), le_rfl⟩

local instance : TemporalTrace (Finset ℕ) ℕ := ⟨hull⟩

/-- The worlds of the soccer scenario. -/
inductive Soccer
  | plays
  | accident
  deriving DecidableEq, Fintype

/-- The games John plays in a world. -/
def played : Soccer → Finset ℕ
  | .plays => {0, 2, 4, 6}
  | .accident => {0, 2}

/-- *John play soccer*: a nonempty set of the games John plays. -/
def playSoccer (v : Soccer) (e : Finset ℕ) : Prop := e.Nonempty ∧ e ⊆ played v

/-- The utterance time. -/
def utterance : NonemptyInterval ℕ := ⟨(3, 3), le_rfl⟩

/-- The facts of (59), which exclude neither world. -/
def soccerBase : (Soccer → Finset ℕ → Prop) → NonemptyInterval ℕ → Background Soccer :=
  fun _ _ _ ↦ ∅

/-- The facts of (61): John cannot move his legs. -/
def accidentBase : (Soccer → Finset ℕ → Prop) → NonemptyInterval ℕ → Background Soccer :=
  fun _ _ _ ↦ {(· = .accident)}

/-- The ordering source (60): nothing interrupts John's playing. -/
def keepsPlaying : (Soccer → Finset ℕ → Prop) → NonemptyInterval ℕ → Background Soccer :=
  fun _ _ _ ↦ {(· ≠ .accident)}

theorem pl_playSoccer : PL (playSoccer .plays) ({0, 2, 4, 6} : Finset ℕ) := by
  refine ⟨⟨⟨0, by decide⟩, subset_rfl⟩, {({0, 2} : Finset ℕ), ({4, 6} : Finset ℕ)},
    ⟨_, Finset.mem_insert_self _ _⟩, ?_, ?_, by decide⟩
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ⟨Finset.ssubset_iff_subset_ne.2 ⟨by decide, by decide⟩, ⟨0, by decide⟩, by decide⟩
    · exact ⟨Finset.ssubset_iff_subset_ne.2 ⟨by decide, by decide⟩, ⟨4, by decide⟩, by decide⟩
  · have hdisj : ¬ Overlap ({0, 2} : Finset ℕ) {4, 6} := by
      rintro ⟨z, hz, hz₁, hz₂⟩
      refine hz fun y ↦ ?_
      have : z ⊆ ({0, 2} : Finset ℕ) ∩ {4, 6} := Finset.subset_inter hz₁ hz₂
      rw [show ({0, 2} : Finset ℕ) ∩ {4, 6} = ∅ by decide] at this
      exact (Finset.subset_empty.1 this) ▸ Finset.empty_subset _
    simp only [Finset.coe_insert, Finset.coe_singleton]
    refine Set.pairwise_insert.2 ⟨Set.pairwise_singleton _ _, fun y hy _ ↦ ?_⟩
    rw [Set.mem_singleton_iff.1 hy]
    exact ⟨hdisj, fun h ↦ hdisj h.symm⟩

theorem utterance_le_hull : utterance ≤ τ ({0, 2, 4, 6} : Finset ℕ) := by
  change utterance ≤ hull _
  unfold hull
  split_ifs with h
  · exact NonemptyInterval.le_def.2 ⟨by simp, by simp [utterance]⟩
  · exact absurd ⟨0, by decide⟩ h

theorem not_utterance_le_hull {e : Finset ℕ} (he : playSoccer .accident e) :
    ¬ utterance ≤ τ e := by
  intro h
  change utterance ≤ hull e at h
  unfold hull at h
  split_ifs at h with hne
  swap
  · exact hne he.1
  have hmax : e.max' hne ∈ ({0, 2} : Finset ℕ) := he.2 (Finset.max'_mem _ _)
  have h3 : 3 ≤ e.max' hne := (NonemptyInterval.le_def.1 h).2
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmax
  omega

theorem mem_IMP_soccer : utterance ∈ IMP PL soccerBase keepsPlaying playSoccer .plays := by
  rw [mem_IMP_iff]
  intro v hv
  have hacc : v ∈ Background.accessibleWorlds
      (soccerBase playSoccer utterance ⊔ keepsPlaying playSoccer utterance) .plays := by
    rw [← bestWorlds_eq_accessibleWorlds_sup ⟨.plays, by
      simp [Background.accessibleWorlds_sup, soccerBase, keepsPlaying]⟩]
    exact hv
  obtain rfl : v = .plays := by
    cases v
    · rfl
    · simp [Background.accessibleWorlds_sup, soccerBase, keepsPlaying] at hacc
  exact ⟨_, utterance_le_hull, pl_playSoccer⟩

theorem not_mem_IMP_accident :
    utterance ∉ IMP PL accidentBase keepsPlaying playSoccer .plays := by
  rw [mem_IMP_iff]
  intro h
  have hbest : Soccer.accident ∈ bestWorlds (accidentBase playSoccer utterance)
      (keepsPlaying playSoccer utterance) .plays := by
    refine mem_bestWorlds.2 ⟨by simp [accidentBase], fun v hv _ ↦ ?_⟩
    have : v = .accident := by simpa [accidentBase] using hv
    exact this ▸ (premisePreorder _).le_refl _
  obtain ⟨e, he, hpl⟩ := h _ hbest
  exact not_utterance_le_hull hpl.1 he

/-! ### The paper's judgments -/

/-- The imperfective decides the paper's judgments: the street and a regular player's habit are
true, the Atlantic and the habit after the accident false. -/
theorem truthValue_rows :
    (now ∈ IMP atomize streetBase notInterrupted cross .stopped ↔
        Examples.ex45.feature? "truthValue" = some "true") ∧
      (now ∈ IMP atomize atlanticBase notInterrupted cross .stopped ↔
        Examples.ex46.feature? "truthValue" = some "true") ∧
      (utterance ∈ IMP PL soccerBase keepsPlaying playSoccer .plays ↔
        Examples.ex54.feature? "truthValue" = some "true") ∧
      (utterance ∈ IMP PL accidentBase keepsPlaying playSoccer .plays ↔
        Examples.ex54_accident.feature? "truthValue" = some "true") :=
  ⟨iff_of_true mem_IMP_street (by decide), iff_of_false not_mem_IMP_atlantic (by decide),
    iff_of_true mem_IMP_soccer (by decide), iff_of_false not_mem_IMP_accident (by decide)⟩

end Ferreira2016
