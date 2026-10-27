module

public import Linglib.Semantics.Aspect.Viewpoint
public import Linglib.Semantics.Conditionals.SelectionFunction
public import Studies.Dowty1979
public import Linglib.Data.Examples.Landman1992

/-!
# Landman (1992): The progressive

*Mary was drawing a circle* can be true when *Mary drew a circle* is false: she may have been
interrupted. This is the imperfective paradox, and it rules out the extensional analysis of
Bennett and Partee, on which a progressive is true at an interval that a longer interval of the
sentence's truth in the actual world extends into the future. The imperfective of the event
semantics, true at an interval properly inside the run time of an actual event of its type, is
extensional in the same way, so [it makes every progressive entail its
perfective](##prfv_nonempty_of_impf_nonempty). Landman takes the
progressive instead to relate an actual event in progress to a possibly non-actual complete event
of its type, and builds the relation from two operations. Within a world, an event grows into the
events of which it is a stage until it stops. When it stops, a Stalnaker-style selection function
gives the closest world where it does not, and the event is followed there if that world is a
reasonable option for it, one in which it gets no further than it had a reasonable chance to get
on the basis of what is internal to it. The worlds and events reached form its continuation
branch, and *e is in progress toward P* holds when some event on the branch is of type `P`.

So [whatever gets completed was in progress during its development](##prog_of_le), even against
all odds. For a process interrupted `n` times, the progressive holds exactly when [each of the
`n` counterfactual continuations is reasonable](##prog_interrupted_iff). Mary was crossing the
street when one truck hit her, and when the second truck behind it would have, but she was not
wiping out the Roman army when the first soldier killed her; by contrast, the inertia worlds of
Dowty's progressive, where everything takes its normal course, contain the truck, so [it makes
Mary's crossing false](##not_dowtyProg_truck). These scenarios [decide the paper's
judgments](##truthValue_rows), where the imperfective of the event semantics gets the interrupted
drawing wrong.

## Implementation notes

* Events are ordered by stage-of, `e ≤ f` when `e` is a stage of `f`. Part-of, which the paper
  uses only to motivate stages, is not modelled.
* An event occurs in some worlds and not in others, and has the same run time, the temporal trace
  of the event semantics, in each world where it occurs. The paper's trace is relative to a world,
  but none of its definitions compares the intervals of an event across worlds.
* An event stops when it goes on but nothing of which it is a stage goes on at a later-ending
  interval; the paper's restriction to non-final intervals is dropped, since the branch only
  jumps to a world where the event continues, and the paper presupposes that the closest such
  world exists.
* The branch jumps from a maximal event of the world, which then stops (`stops_of_maximal`); it is
  the maximal element of the continuation stretch, since every event of which a branch event is a
  stage is on the branch.
  The paper's constraints on stage-of within a world (§2.2) and its Activity Postulate are not
  imposed; the activity half of the paradox is `activity_of_prog`, under the hypothesis the
  postulate supplies, that a process stage of an event of an activity type is of that type.
* In the interrupted processes, the events are intervals, the event domain of the event
  semantics with the identity trace, so `Aspect.IMPF` and `Aspect.PRFV` apply to the same models.
  World `k` removes the first `k` interruptions, and the closest world is the first one from the
  current world on. Tense is not modelled: a progressive is evaluated at its first stage.
* The swimmer of (17) and the soldier of (20) need five continuations and have a reasonable reach
  of two; only whether the reach covers the interruptions matters (`prog_interrupted_iff`).
* Dowty's progressive is `Dowty1979.prog`, his (25), applied to the run times of the events of a
  type. Landman's statement of it (p. 3) takes the longer interval after the inertia world; the two
  agree when, as for the truck, the actual world is the only inertia world.

## Errata

* The definition of stopping (p. 24) says that `f`, going on at `j`, stops when nothing of which
  it is a stage goes on beyond `i`, the interval of `e`. Since `f` is a stage of itself, `f` would
  then never stop at an interval ending later than `i`, and the continuation branch could not
  leave the world of `e`; `j` is meant, and `Stops` reads it.

## TODO

* The rival proposals of §1, the normality, subjunctive and part-of proposals, are not
  formalized, nor the stage kinds of the Activity Postulate (process, planning and pause), the
  intensionality of the object position in (9) and (10), or the perspectives of the appendix.

## References

* [landman-1992]
* [bennett-partee-1972]
* [dowty-1979]
* [stalnaker-1968]
-/

@[expose] public section

namespace Landman1992

open Conditional

/-! ### Models -/

/-- A model of §2 over events ordered by stage-of: the worlds where each event goes on, the
reasonable options of §2.3, and the closest-world selection of a Stalnaker-style theory of
subjunctives (§2.4). -/
structure Model (E W : Type*) where
  /-- An event goes on in a world. -/
  occurs : E → W → Prop
  /-- `reasonable e w` is `R(e, w)`, the worlds that are reasonable options for `e` in `w`. -/
  reasonable : E → W → Set W
  /-- The closest world to a world in a proposition. -/
  closest : SelectionFunction W

namespace Model

open Event (τ)

variable {E W T : Type*} [PartialOrder E] [LinearOrder T] [Event.TemporalTrace E T]
  (M : Model E W)

/-- An event continues in a world when it goes on there and so does something of which it is a
stage, with a later-ending run time. -/
def Continues (e : E) (w : W) : Prop :=
  M.occurs e w ∧ ∃ f, e ≤ f ∧ M.occurs f w ∧ (τ e).snd < (τ f).snd

/-- An event stops in a world (§2.2) when it goes on there and does not continue. -/
def Stops (e : E) (w : W) : Prop := M.occurs e w ∧ ¬ M.Continues e w

/-- The closest world to `u` where `f` continues. -/
noncomputable def next (f : E) (u : W) : W := M.closest.sel u {v | M.Continues f v}

/-- The continuation branch `C(e, w)` of `e` in `w` (§2.4). It follows `e` through the events of
which it is a stage in `w`; when the last of them stops, it goes to the closest world where that
event continues, if that world is a reasonable option for `e` in `w`, and follows the event
there. -/
inductive Branch (e : E) (w : W) : E → W → Prop
  | self : M.occurs e w → Branch e w e w
  | stretch {f g : E} {u : W} : Branch e w f u → M.occurs g u → f ≤ g → Branch e w g u
  | jump {f : E} {u : W} : Branch e w f u → Maximal (M.occurs · u) f →
      M.next f u ∈ M.reasonable e w → M.Continues f (M.next f u) → Branch e w f (M.next f u)

/-- `PROG(e, P)` (§2.4): some event on the continuation branch of `e` is of type `P` in its
world. -/
def Prog (e : E) (P : W → E → Prop) (w : W) : Prop := ∃ f v, M.Branch e w f v ∧ P v f

/-- The progressive of `P` at a world as a property of intervals, those of the events in progress
toward `P` there. -/
def progAt (P : W → E → Prop) (w : W) : Set (NonemptyInterval T) :=
  τ '' {e | M.occurs e w ∧ M.Prog e P w}

variable {M} {e f : E} {w u v : W} {P : W → E → Prop}

theorem stops_of_maximal (h : Maximal (M.occurs · u) f) : M.Stops f u := by
  refine ⟨h.1, fun ⟨_, g, hfg, hg, hlt⟩ ↦ ?_⟩
  obtain rfl := le_antisymm (h.2 hg hfg) hfg
  exact lt_irrefl _ hlt

theorem Branch.occurs (h : M.Branch e w f v) : M.occurs f v := by
  induction h with
  | self h => exact h
  | stretch _ hg => exact hg
  | jump _ _ _ hc => exact hc.1

theorem Branch.occurs_root (h : M.Branch e w f v) : M.occurs e w := by
  induction h with
  | self h => exact h
  | stretch _ _ _ ih => exact ih
  | jump _ _ _ _ ih => exact ih

-- p. 27
theorem Branch.le (h : M.Branch e w f v) : e ≤ f := by
  induction h with
  | self => exact le_rfl
  | stretch _ _ hfg ih => exact ih.trans hfg
  | jump _ _ _ _ ih => exact ih

/-- Whatever gets completed was in progress during its development, however unlikely its
completion ((15), (16)): a stage of an actual event of type `P` is in progress toward `P`. -/
theorem prog_of_le (he : M.occurs e w) (hf : M.occurs f w) (hef : e ≤ f) (hP : P w f) :
    M.Prog e P w :=
  ⟨f, w, .stretch (.self he) hf hef, hP⟩

theorem Prog.occurs (h : M.Prog e P w) : M.occurs e w :=
  let ⟨_, _, hb, _⟩ := h; hb.occurs_root

-- (1) entails (2): a process stage of an activity event is an event of the activity
theorem activity_of_prog (hP : ∀ f v, P v f → e ≤ f → M.occurs e w → P w e)
    (h : M.Prog e P w) : P w e :=
  let ⟨f, v, hb, hf⟩ := h; hP f v hf hb.le hb.occurs_root

end Model

open Model Event

/-- An event type as a sentence of interval semantics, true at the run times of its events. -/
def sentenceOf {E W T : Type*} [LE T] [TemporalTrace E T] (P : W → E → Prop) :
    Dowty1979.Sentence W T :=
  fun v ↦ τ '' {e | P v e}

/-- The imperfective of the event semantics holds at an interval inside the run time of an actual
event of its type, like Bennett and Partee's progressive, so wherever it holds the perfective
holds too: it validates the inference from (3) to (4) that the imperfective paradox rejects. -/
theorem prfv_nonempty_of_impf_nonempty {E W T : Type*} [LinearOrder T]
    [Event.TemporalTrace E T] {P : W → E → Prop} {w : W} (h : (Aspect.IMPF P w).Nonempty) :
    (Aspect.PRFV (T := T) P w).Nonempty :=
  let ⟨_, e, _, he⟩ := h; ⟨Event.τ e, e, le_rfl, he⟩

/-! ### Interrupted processes -/

/-- The interval `[0, j]`, the run time of the `j`-th stage of a process begun at `0`. -/
def upto (j : ℕ) : NonemptyInterval ℕ := ⟨(0, j), Nat.zero_le j⟩

/-- How far a process interrupted `n` times gets in world `k`: in a world `k < n` it reaches stage
`k` and is interrupted, and from world `n` on it is completed at stage `n + 1`. -/
def reach (n k : ℕ) : ℕ := if k < n then k else n + 1

@[simp] theorem upto_fst (j : ℕ) : (upto j).fst = 0 := rfl

@[simp] theorem upto_snd (j : ℕ) : (upto j).snd = j := rfl

theorem reach_of_lt {n k : ℕ} (h : k < n) : reach n k = k := ite_eq_left h

theorem reach_of_le {n k : ℕ} (h : n ≤ k) : reach n k = n + 1 := ite_eq_right h.not_gt

theorem reach_le (n k : ℕ) : reach n k ≤ n + 1 := by unfold reach; split_ifs <;> omega

theorem le_reach_succ {n k : ℕ} (h : k < n) : k + 1 ≤ reach n (k + 1) := by
  unfold reach; split_ifs <;> omega

open Classical in
/-- Selection of the first world from the current one on that is in the proposition, otherwise of
the first world in it. -/
noncomputable def forward : SelectionFunction ℕ :=
  .ofSel (fun k A ↦ if h : ∃ j ∈ A, k ≤ j then Nat.find h else
      if h' : ∃ j, j ∈ A then Nat.find h' else k)
    (fun k A hA ↦ by
      split_ifs with h h'
      · exact (Nat.find_spec h).1
      · exact Nat.find_spec h'
      · exact absurd hA h')
    (fun k A hk ↦ by
      have h : ∃ j ∈ A, k ≤ j := ⟨k, hk, le_rfl⟩
      rw [dite_eq_left h]
      exact le_antisymm (Nat.find_min' h ⟨hk, le_rfl⟩) (Nat.find_spec h).2)

theorem forward_sel_eq {k j : ℕ} {A : Set ℕ} (hj : j ∈ A) (hkj : k ≤ j)
    (hmin : ∀ m, k ≤ m → m < j → m ∉ A) : forward.sel k A = j := by
  classical
  rw [forward, SelectionFunction.sel_ofSel, dite_eq_left ⟨j, hj, hkj⟩, Nat.find_eq_iff]
  exact ⟨⟨hj, hkj⟩, fun m hm ⟨hmA, hkm⟩ ↦ hmin m hkm hm hmA⟩

/-- A process interrupted `n` times, under reasonable options `R`, as in the picture on p. 27:
its stages are the intervals `[0, j]`, each a stage of the later ones; world `k` removes the first
`k` interruptions; and the closest world where the process continues is the next one. -/
noncomputable def interrupted (n : ℕ) (R : Set ℕ) : Model (NonemptyInterval ℕ) ℕ where
  occurs e k := e.fst = 0 ∧ e.snd ≤ reach n k
  reasonable _ _ := R
  closest := forward

/-- The completed process, its last stage `[0, n + 1]`, which goes on in the worlds from `n`
on. -/
def complete (n : ℕ) (v : ℕ) (e : NonemptyInterval ℕ) : Prop := e = upto (n + 1) ∧ n ≤ v

section Interrupted

variable {n k : ℕ} {R : Set ℕ} {e f : NonemptyInterval ℕ}

theorem occurs_interrupted : (interrupted n R).occurs e k ↔ e.fst = 0 ∧ e.snd ≤ reach n k :=
  Iff.rfl

theorem continues_interrupted :
    (interrupted n R).Continues e k ↔ e.fst = 0 ∧ e.snd < reach n k := by
  simp only [Continues, occurs_interrupted, τ_nonemptyInterval]
  constructor
  · rintro ⟨⟨he, -⟩, g, -, ⟨-, hg⟩, hlt⟩
    exact ⟨he, hlt.trans_le hg⟩
  · rintro ⟨he, hlt⟩
    exact ⟨⟨he, hlt.le⟩, upto (reach n k), NonemptyInterval.le_def.2 ⟨he.ge, hlt.le⟩,
      ⟨rfl, le_rfl⟩, hlt⟩

theorem maximal_interrupted :
    Maximal ((interrupted n R).occurs · k) e ↔ e = upto (reach n k) := by
  have hu : (interrupted n R).occurs (upto (reach n k)) k := occurs_interrupted.2 ⟨rfl, le_rfl⟩
  constructor
  · rintro ⟨he, hmax⟩
    obtain ⟨h0, hr⟩ := occurs_interrupted.1 he
    have := NonemptyInterval.le_def.1 (hmax hu (NonemptyInterval.le_def.2 ⟨h0.ge, hr⟩))
    exact NonemptyInterval.ext (Prod.ext h0 (le_antisymm hr this.2))
  · rintro rfl
    refine ⟨hu, fun g hg _ ↦ NonemptyInterval.le_def.2 ⟨Nat.zero_le _, ?_⟩⟩
    exact (occurs_interrupted.1 hg).2

theorem next_interrupted (h : k < n) : (interrupted n R).next (upto k) k = k + 1 := by
  refine forward_sel_eq ?_ k.le_succ fun m hkm hm hmA ↦ ?_
  · exact continues_interrupted.2 ⟨rfl, (Nat.lt_succ_self k).trans_le (le_reach_succ h)⟩
  · obtain rfl : m = k := by omega
    exact (continues_interrupted.1 hmA).2.ne (reach_of_lt h).symm

theorem branch_interrupted (h : (interrupted n R).Branch (upto 0) 0 f k) :
    k ≤ n ∧ Set.Icc 1 k ⊆ R ∧ f.snd ≤ reach n k := by
  induction h with
  | self => exact ⟨Nat.zero_le n, fun m hm ↦ absurd (hm.1.trans hm.2) (by decide), Nat.zero_le _⟩
  | stretch _ hg _ ih => exact ⟨ih.1, ih.2.1, (occurs_interrupted.1 hg).2⟩
  | @jump g u _ hmax hR hc ih =>
    obtain rfl := maximal_interrupted.1 hmax
    have hu : u < n := by
      by_contra hu
      have := (continues_interrupted.1 hc).2
      rw [upto_snd, reach_of_le (not_lt.1 hu)] at this
      exact (reach_le n _).not_gt this
    rw [reach_of_lt hu, next_interrupted hu] at hR ⊢
    change _ ∈ R at hR
    refine ⟨hu, fun m hm ↦ ?_, (Nat.le_succ u).trans (le_reach_succ hu)⟩
    rcases Nat.lt_or_ge m (u + 1) with hm' | hm'
    · exact ih.2.1 ⟨hm.1, by omega⟩
    · exact (le_antisymm hm.2 hm') ▸ hR

theorem branch_upto (hk : k ≤ n) (hR : Set.Icc 1 k ⊆ R) :
    (interrupted n R).Branch (upto 0) 0 (upto k) k := by
  induction k with
  | zero => exact .self (occurs_interrupted.2 ⟨rfl, Nat.zero_le _⟩)
  | succ k ih =>
    have hkn : k < n := hk
    have hb := ih hkn.le fun m hm ↦ hR ⟨hm.1, hm.2.trans k.le_succ⟩
    have hmax : Maximal ((interrupted n R).occurs · k) (upto k) :=
      maximal_interrupted.2 (by rw [reach_of_lt hkn])
    have hnext := next_interrupted (R := R) hkn
    have hj := Branch.jump hb hmax (by rw [hnext]; exact hR ⟨k.succ_pos, le_rfl⟩)
      (by rw [hnext]; exact continues_interrupted.2 ⟨rfl, (Nat.lt_succ_self k).trans_le
        (le_reach_succ hkn)⟩)
    rw [hnext] at hj
    exact hj.stretch (occurs_interrupted.2 ⟨rfl, le_reach_succ hkn⟩)
      (NonemptyInterval.le_def.2 ⟨le_rfl, k.le_succ⟩)

/-- A process interrupted `n` times is in progress toward its completion exactly when each of
the `n` counterfactual continuations the branch needs is a reasonable option for it. -/
theorem prog_interrupted_iff :
    (interrupted n R).Prog (upto 0) (complete n) 0 ↔ Set.Icc 1 n ⊆ R := by
  constructor
  · rintro ⟨f, v, hb, rfl, hnv⟩
    obtain ⟨hvn, hR, -⟩ := branch_interrupted hb
    exact le_antisymm hvn hnv ▸ hR
  · intro hR
    refine ⟨upto (n + 1), n, (branch_upto le_rfl hR).stretch ?_ ?_, rfl, le_rfl⟩
    · exact occurs_interrupted.2 ⟨rfl, (reach_of_le le_rfl).ge⟩
    · exact NonemptyInterval.le_def.2 ⟨le_rfl, n.le_succ⟩

theorem progAt_interrupted_nonempty_iff (hn : 0 < n) :
    ((interrupted n R).progAt (complete n) 0).Nonempty ↔ Set.Icc 1 n ⊆ R := by
  constructor
  · rintro ⟨_, e, ⟨⟨h0, hr⟩, hp⟩, -⟩
    rw [reach_of_lt hn] at hr
    obtain rfl : e = upto 0 := NonemptyInterval.ext (Prod.ext h0 (by rw [upto_snd]; omega))
    exact prog_interrupted_iff.1 hp
  · intro hR
    exact ⟨upto 0, upto 0, ⟨⟨rfl, Nat.zero_le _⟩, prog_interrupted_iff.2 hR⟩, rfl⟩

theorem progAt_interrupted_zero_nonempty : ((interrupted 0 R).progAt (complete 0) 0).Nonempty :=
  ⟨upto 0, upto 0, ⟨⟨rfl, Nat.zero_le _⟩, prog_of_le (f := upto 1) ⟨rfl, Nat.zero_le _⟩
    ⟨rfl, (reach_of_le le_rfl).ge⟩ (NonemptyInterval.le_def.2 ⟨le_rfl, Nat.zero_le _⟩)
    ⟨rfl, le_rfl⟩⟩, rfl⟩

theorem impf_complete_eq_empty (hn : 0 < n) : Aspect.IMPF (T := ℕ) (complete n) 0 = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ ⟨_, _, _, h⟩ ↦ hn.not_ge h

theorem prfv_complete_eq_empty (hn : 0 < n) : Aspect.PRFV (T := ℕ) (complete n) 0 = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ ⟨_, _, _, h⟩ ↦ hn.not_ge h

/-- Dowty's progressive makes *Mary was crossing the street* false when the truck hits her (13):
the truck's hitting her is the normal course of events, so the actual world is the inertia world,
and there she does not get across. -/
theorem not_dowtyProg_truck :
    upto 0 ∉ Dowty1979.prog (fun _ _ ↦ {0}) (sentenceOf (complete 1)) 0 :=
  fun ⟨_, _, h⟩ ↦ let ⟨_, ⟨_, h1⟩, _⟩ := h 0 rfl; absurd h1 (by decide)

end Interrupted

/-! ### The paper's judgments -/

/-- The interrupted drawing and the crossing hit by a truck (3), (13): one interruption, whose
counterfactual continuation is reasonable. -/
noncomputable abbrev once : Model (NonemptyInterval ℕ) ℕ := interrupted 1 Set.univ

/-- The two trucks (18): two interruptions, each continuation reasonable. -/
noncomputable abbrev twoTrucks : Model (NonemptyInterval ℕ) ℕ := interrupted 2 Set.univ

/-- The sinking swimmer (17) and the Roman army (20): many interruptions, of which only the first
two continuations are reasonable. -/
noncomputable abbrev hopeless : Model (NonemptyInterval ℕ) ℕ := interrupted 5 (Set.Iic 2)

/-- The swimmer carried across by divine intervention (17): no interruption, and no world, not even
the actual one, is a reasonable option. -/
noncomputable abbrev miracle : Model (NonemptyInterval ℕ) ℕ := interrupted 0 ∅

/-- The continuation branch decides the paper's judgments in context, where the imperfective of
the event semantics makes the interrupted drawing (3) false. -/
theorem truthValue_rows :
    ((once.progAt (complete 1) 0).Nonempty ↔
        Examples.ex3.feature? "truthValue" = some "true") ∧
      ((Aspect.PRFV (T := ℕ) (complete 1) 0).Nonempty ↔
        Examples.ex4.feature? "truthValue" = some "true") ∧
      ((once.progAt (complete 1) 0).Nonempty ↔
        Examples.ex13.feature? "truthValue" = some "true") ∧
      ((hopeless.progAt (complete 5) 0).Nonempty ↔
        Examples.ex17_sink.feature? "truthValue" = some "true") ∧
      ((miracle.progAt (complete 0) 0).Nonempty ↔
        Examples.ex17_miracle.feature? "truthValue" = some "true") ∧
      ((twoTrucks.progAt (complete 2) 0).Nonempty ↔
        Examples.ex18.feature? "truthValue" = some "true") ∧
      ((hopeless.progAt (complete 5) 0).Nonempty ↔
        Examples.ex20.feature? "truthValue" = some "true") ∧
      ¬ ((Aspect.IMPF (T := ℕ) (complete 1) 0).Nonempty ↔
        Examples.ex3.feature? "truthValue" = some "true") := by
  have hu (n : ℕ) : Set.Icc 1 n ⊆ (Set.univ : Set ℕ) := Set.subset_univ _
  have hh : ¬ Set.Icc 1 5 ⊆ Set.Iic (2 : ℕ) := fun h ↦ absurd (h ⟨by decide, by decide⟩ :
    (3 : ℕ) ∈ Set.Iic 2) (by decide)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact iff_of_true ((progAt_interrupted_nonempty_iff one_pos).2 (hu 1)) (by decide)
  · rw [prfv_complete_eq_empty one_pos]; exact iff_of_false Set.not_nonempty_empty (by decide)
  · exact iff_of_true ((progAt_interrupted_nonempty_iff one_pos).2 (hu 1)) (by decide)
  · exact iff_of_false (mt (progAt_interrupted_nonempty_iff (by decide)).1 hh) (by decide)
  · exact iff_of_true progAt_interrupted_zero_nonempty (by decide)
  · exact iff_of_true ((progAt_interrupted_nonempty_iff (by decide)).2 (hu 2)) (by decide)
  · exact iff_of_false (mt (progAt_interrupted_nonempty_iff (by decide)).1 hh) (by decide)
  · rw [impf_complete_eq_empty one_pos]
    exact fun h ↦ Set.not_nonempty_empty (h.2 (by decide))

end Landman1992
