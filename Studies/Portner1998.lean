module

public import Linglib.Semantics.Aspect.Progressive
public import Studies.Landman1992
public import Linglib.Data.Examples.Portner1998
public import Linglib.Data.Examples.Readers

/-!
# Portner (1998): The progressive in modal semantics

Portner keeps Dowty's idea that the progressive is a necessity operator over inertia worlds and
explains which worlds those are with Kratzer's ordering semantics. The progressive of an event
`e` under a description `P` quantifies over the best worlds of a circumstantial modal base,
`Circ(e, P)`, the facts relevant to whether `e` is completed as an event of type `P`, ranked by an
ordering source `NI(e)`, the propositions that `e` is not interrupted; it is true when in every
such world some event of type `P` includes `e` as a nonfinal part. This is the progressive of the
event semantics, `Aspect.InProgress`.

Since the modal base is fixed by what is internal to the event, a bus that hits Max halfway across
the street is no part of it, and *Max was crossing the street* (11) comes out true where Dowty's
inertia worlds, which contain the bus, [make it false](##not_dowtyProg_bus). Since the base also
depends on the description, the same walk makes (11) true and *Max was walking into the path of an
oncoming bus* (39) true, the latter under a base that includes the bus; [no single base does
both](##not_prog_crossing_and_walkIntoBus). A Mary of ordinary abilities was not wiping out the
Roman army, whose defeat no world compatible with her abilities contains; a Mary who did wipe it out
has the abilities that put such worlds in the base. These scenarios [decide the paper's
judgments](##truthValue_rows), where the imperfective of the event semantics over the actual world
alone, inside which the progressive over a totally realistic base falls
(`Aspect.PROG_subset_IMPF`), gets (11) wrong.

## Implementation notes

* The scenarios take their events to be intervals of natural numbers, as in `Landman1992`, and
  constant backgrounds over three worlds.
* The interval forms (14) and (32) quantify over inertia worlds before the longer interval, the
  reverse of Dowty's (3); the reversal is a weakening (`Dowty1979.not_branchingProg_subset_prog`).

## TODO

* The activity argument of §4.2 (Max is running, so he has run) needs temporal subevents, and the
  winning race (35) and the context dependence of (4) and (47) are not formalized.

## References

* [portner-1998]
* [dowty-1979]
* [landman-1992]
* [kratzer-1991]
-/

@[expose] public section

namespace Portner1998

open Modality Event Aspect

open Dowty1979 (iv)

theorem nonfinalPart_iv {b d : ℕ} (hb : 0 ≤ b) (hd : 0 ≤ d) (hbd : b < d) :
    NonfinalPart (iv 0 b hb) (iv 0 d hd) :=
  ⟨NonemptyInterval.le_def.2 ⟨le_rfl, hbd.le⟩, le_rfl, hbd⟩

/-! ### The bus (11), (39)

Max's walk so far is the event `[0, 1]`. In world `crosses` he gets across, his crossing being
`[0, 3]`; in world `hit`, the actual one, the bus hits him, his walk into its path being `[0, 2]`;
in world `turnsAround` he turns back. -/

/-- The worlds of the bus scenario. -/
inductive Bus
  | crosses
  | hit
  | turnsAround
  deriving DecidableEq, Fintype

/-- *Max crosses the street.* -/
def crossing (v : Bus) (e : NonemptyInterval ℕ) : Prop := v = .crosses ∧ e = iv 0 3

/-- *Max walks into the path of an oncoming bus.* -/
def walkIntoBus (v : Bus) (e : NonemptyInterval ℕ) : Prop := v = .hit ∧ e = iv 0 2

/-- `NI(e)`: Max is not hit by a bus and does not turn around. -/
def notInterrupted : Background Bus := fun _ ↦ {(· ≠ .hit), (· ≠ .turnsAround)}

/-- The base (42) for the description that mentions the bus: a bus is on a path to hit Max. -/
def withBus : Background Bus := fun _ ↦ {(· = .hit)}

open Classical in
/-- `Circ(e, P)` (41), (42): facts about Max alone, unless the description mentions the bus. -/
noncomputable def circ (_ : NonemptyInterval ℕ) (P : Bus → NonemptyInterval ℕ → Prop) :
    Background Bus :=
  if P = walkIntoBus then withBus else ⊥

theorem crossing_ne_walkIntoBus : crossing ≠ walkIntoBus := fun h ↦ by
  have := congrFun (congrFun h .crosses) (iv 0 3)
  simp [crossing, walkIntoBus] at this

theorem prog_crossing : InProgress circ (fun _ ↦ notInterrupted) (iv 0 1) crossing .hit := by
  have hbest : bestWorlds ⊥ notInterrupted Bus.hit = {.crosses} := by
    have hacc : ((⊥ : Background Bus) ⊔ notInterrupted).accessibleWorlds .hit = {.crosses} := by
      ext v; cases v <;> simp [notInterrupted]
    rw [bestWorlds_eq_accessibleWorlds_sup (by rw [hacc]; exact Set.singleton_nonempty _), hacc]
  rw [InProgress, necessity_iff, circ, ite_eq_right crossing_ne_walkIntoBus, hbest]
  rintro v rfl
  exact ⟨iv 0 3, nonfinalPart_iv _ _ (by decide), rfl, rfl⟩

theorem prog_walkIntoBus : InProgress circ (fun _ ↦ notInterrupted) (iv 0 1) walkIntoBus .hit := by
  rw [InProgress, necessity_iff, circ, ite_eq_left rfl]
  intro v hv
  have hacc : withBus.accessibleWorlds Bus.hit = {.hit} := by ext u; cases u <;> simp [withBus]
  obtain rfl : v = .hit := by simpa [hacc] using (mem_bestWorlds.1 hv).1
  exact ⟨iv 0 2, nonfinalPart_iv _ _ (by decide), rfl, rfl⟩

/-- A modal base fixed by the event alone cannot make both (11) and (39) true, so the base must
depend on the description (p. 779). -/
theorem not_prog_crossing_and_walkIntoBus (f : Background Bus)
    (hne : (bestWorlds f notInterrupted .hit).Nonempty) :
    ¬ (InProgress (fun _ _ ↦ f) (fun _ ↦ notInterrupted) (iv 0 1) crossing .hit ∧
      InProgress (fun _ _ ↦ f) (fun _ ↦ notInterrupted) (iv 0 1) walkIntoBus .hit) := by
  rintro ⟨h₁, h₂⟩
  obtain ⟨u, hu⟩ := hne
  obtain ⟨_, -, rfl, -⟩ := h₁ u hu
  obtain ⟨_, -, h, -⟩ := h₂ _ hu
  exact absurd h (by decide)

/-- Dowty's progressive makes (11) false: the bus's hitting Max is the normal course of events,
so the actual world is the inertia world, and there he does not cross (p. 764). -/
theorem not_dowtyProg_bus :
    iv 0 1 ∉ Dowty1979.prog (fun _ _ ↦ {Bus.hit}) (Landman1992.sentenceOf crossing) .hit :=
  fun ⟨_, _, h⟩ ↦ let ⟨_, ⟨h1, _⟩, _⟩ := h .hit rfl; absurd h1 (by decide)

theorem impf_crossing_eq_empty :
    Aspect.IMPF (T := ℕ) (fun w _ ↦ {w}) crossing Bus.hit = ∅ := by
  rw [Aspect.impf_singleton]
  exact Set.eq_empty_of_forall_notMem fun _ ⟨_, _, h, _⟩ ↦ absurd h (by decide)

/-! ### The Roman army (18)

Mary's fighting so far is the event `[0, 1]`. In world `wipesOut` she destroys the army, her
wiping it out being `[0, 10]`; in `killsDozens` she defeats a few dozen soldiers; in `killedEarly`
she is killed at once. -/

/-- The worlds of the Roman army scenario. -/
inductive Army
  | wipesOut
  | killsDozens
  | killedEarly
  deriving DecidableEq, Fintype

/-- *Mary wipes out the Roman army.* -/
def wipeOut (v : Army) (e : NonemptyInterval ℕ) : Prop := v = .wipesOut ∧ e = iv 0 10

/-- `NI(e)`: Mary defeats the soldiers she fights, a few dozen and then the whole army. -/
def defeatsSoldiers : Background Army := fun _ ↦ {(· ≠ .killedEarly), (· = .wipesOut)}

/-- The circumstances of an ordinary Mary, whose abilities rule out defeating the whole army. -/
def ordinary : Background Army := fun _ ↦ {(· ≠ .wipesOut)}

theorem not_prog_ordinary (w : Army) :
    ¬ InProgress (fun _ _ ↦ ordinary) (fun _ ↦ defeatsSoldiers) (iv 0 1) wipeOut w := by
  rw [InProgress, necessity_iff]
  intro h
  have hbest : Army.killsDozens ∈ bestWorlds ordinary defeatsSoldiers w := by
    refine mem_bestWorlds.2 ⟨by simp [ordinary], fun v hv hle ↦ ?_⟩
    have hv' : v ≠ .wipesOut := by simpa [ordinary] using hv
    cases v
    · exact absurd rfl hv'
    · exact (premisePreorder _).le_refl _
    · exact absurd rfl (hle (· ≠ Army.killedEarly) (by simp [defeatsSoldiers]) (by decide))
  obtain ⟨_, -, h1, -⟩ := h _ hbest
  exact absurd h1 (by decide)

theorem prog_hero :
    InProgress (fun _ _ ↦ ⊥) (fun _ ↦ defeatsSoldiers) (iv 0 1) wipeOut .wipesOut := by
  have hacc : ((⊥ : Background Army) ⊔ defeatsSoldiers).accessibleWorlds .wipesOut =
      {.wipesOut} := by
    ext v; cases v <;> simp [defeatsSoldiers]
  rw [InProgress, necessity_iff, bestWorlds_eq_accessibleWorlds_sup
    (by rw [hacc]; exact Set.singleton_nonempty _), hacc]
  rintro v rfl
  exact ⟨iv 0 10, nonfinalPart_iv _ _ (by decide), rfl, rfl⟩

/-! ### The paper's judgments -/

/-- The progressive decides the paper's judgments, where Dowty's inertia worlds and the
imperfective of the event semantics make (11) false. -/
theorem truthValue_rows :
    (InProgress circ (fun _ ↦ notInterrupted) (iv 0 1) crossing .hit ↔
        Examples.ex11.feature? "truthValue" = some "true") ∧
      (InProgress circ (fun _ ↦ notInterrupted) (iv 0 1) walkIntoBus .hit ↔
        Examples.ex39.feature? "truthValue" = some "true") ∧
      (InProgress (fun _ _ ↦ ordinary) (fun _ ↦ defeatsSoldiers) (iv 0 1) wipeOut .killedEarly ↔
        Examples.ex18_ordinary.feature? "truthValue" = some "true") ∧
      (InProgress (fun _ _ ↦ ⊥) (fun _ ↦ defeatsSoldiers) (iv 0 1) wipeOut .wipesOut ↔
        Examples.ex18_hero.feature? "truthValue" = some "true") ∧
      ¬ (iv 0 1 ∈ Dowty1979.prog (fun _ _ ↦ {Bus.hit}) (Landman1992.sentenceOf crossing) .hit ↔
        Examples.ex11.feature? "truthValue" = some "true") ∧
      ¬ ((Aspect.IMPF (T := ℕ) (fun w _ ↦ {w}) crossing Bus.hit).Nonempty ↔
        Examples.ex11.feature? "truthValue" = some "true") := by
  refine ⟨iff_of_true prog_crossing (by decide), iff_of_true prog_walkIntoBus (by decide),
    iff_of_false (not_prog_ordinary _) (by decide), iff_of_true prog_hero (by decide),
    fun h ↦ not_dowtyProg_bus (h.2 (by decide)), ?_⟩
  rw [impf_crossing_eq_empty]
  exact fun h ↦ Set.not_nonempty_empty (h.2 (by decide))

end Portner1998
