module

public import Linglib.Data.Examples.SpalekMcNally2026
public import Linglib.Fragments.English.Verbs.Inventory
public import Linglib.Fragments.Romance.Spanish.Verbs
public import Linglib.Semantics.ArgumentStructure.Unaccusativity
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Tactic.DeriveFintype

/-!
# Spalek & McNally (2026): The Anatomy of a Verb

English *tear* and Spanish *rasgar* are counterparts in lexical databases and share an event
structure: both are result verbs that [take part in the causative
alternation](##hasCausativeAlternation_tear_rasgar). They differ in root content, which the paper
describes by the patient, the motion that effects the change, its result, the force involved and
the agent's control. Read as conditions on described events, the two contents [exclude each
other](##disjoint_tearContent_rasgarContent), since *tear* implies separation in contrary
directions and *rasgar* linear motion, yet the verbs translate each other where a description
[leaves the motion open](##lenses_verdicts), as tearing soft contact lenses does.

## Implementation notes

* An example is a description, the set of events agreeing with what the paper states about it on
  some dimensions; a verb fits an example when its content meets the description. Each contrast
  is a description that one content meets and the other misses.
* The paper's implications are read as conditions. *Tear*'s "often with some force" is not one;
  outside the literal separation domain *tear* needs contrary motion or considerable force, the
  two sources the paper gives for its figurative uses. *Rasgar*'s slight force is a consequence
  the paper draws from its patient, entered as a condition.
* The paper finds *tear the silence* extremely rare but not impossible and *tear the darkness*
  odd; the darkness of (18b) carries the contrast.
* The translation counts of the paper's Tables 1 and 2 are not encoded.

## References

* [spalek-mcnally-2026]
-/

@[expose] public section

namespace SpalekMcNally2026

open Examples

/-! ### Event structure -/

/-- Both verbs have an intransitive use describing a change and a simple transitive use (§3.1). -/
theorem hasCausativeAlternation_tear_rasgar :
    English.Verbs.tear_.valency.HasCausativeAlternation ∧
      Spanish.Verbs.rasgar.valency.HasCausativeAlternation := by
  decide

/-! ### Described events -/

/-- What a use describes (§3.3): the separation of a patient, the literal domain; the disturbance of
a state, as in (18) and (20); or motion along a path or through a medium, as in (19) and (23). -/
inductive Domain where
  | separation
  | state
  | motion
  deriving DecidableEq, Fintype

/-- The substance of the patient (p. 94): insubstantial, as silence or darkness; flimsy, as a sheet
or soft contact lenses; or a thick solid, as bread. -/
inductive Patient where
  | insubstantial
  | flimsy
  | thickSolid
  deriving DecidableEq, Fintype

/-- How the change is effected (p. 95): by separation in contrary directions or by linear
motion. -/
inductive Motion where
  | contrary
  | linear
  deriving DecidableEq, Fintype

/-- The result (p. 94): a separation of the patient, or a gash on its surface without a hole. -/
inductive Result where
  | separation
  | gash
  deriving DecidableEq, Fintype

/-- The force or energy, typically speed, involved (pp. 98–99). -/
inductive Force where
  | slight
  | considerable
  deriving DecidableEq, Fintype

/-- The agent's control over the change (p. 96): enough to carry the action out carefully, or
less. -/
inductive Control where
  | careful
  | uncontrolled
  deriving DecidableEq, Fintype

/-- A described event, a value on each dimension. -/
structure Event where
  domain : Domain
  patient : Patient
  motion : Motion
  result : Result
  force : Force
  control : Control
  deriving DecidableEq, Fintype

/-! ### Root content -/

/-- The content of *tear*: separation in contrary directions (p. 95) or, outside the separation
domain, considerable force (pp. 98–99). -/
def tearContent : Finset Event :=
  {e | e.motion = .contrary ∨ e.domain ≠ .separation ∧ e.force = .considerable}

/-- The content of *rasgar*: a flimsy or insubstantial patient, or a gash on a thicker one
(p. 94), linear motion (p. 95), no careful control (p. 96), and slight force (p. 99). -/
def rasgarContent : Finset Event :=
  {e | (e.patient ≠ .thickSolid ∨ e.result = .gash) ∧ e.motion = .linear ∧
    e.control = .uncontrolled ∧ e.force = .slight}

/-- No event is both a tearing and a *rasgar* event: the contents disagree on the motion. -/
theorem disjoint_tearContent_rasgarContent : Disjoint tearContent rasgarContent := by
  decide

/-! ### The paper's examples -/

/-- Tearing soft contact lenses with one's nails (16a) separates a flimsy patient. -/
def lenses : Finset Event := {e | e.domain = .separation ∧ e.patient = .flimsy}

/-- Tearing a chunk off a slice of bread (14) separates a thick solid without a gash, which is
why *rasgar* cannot describe it (p. 94). The contrary motion the paper also notes (p. 95) would
rule *rasgar* out on its own and is left open. -/
def bread : Finset Event :=
  {e | e.domain = .separation ∧ e.patient = .thickSolid ∧ e.result = .separation}

/-- An awl engraving cement (16b) leaves a gash on a thick solid, without separation in contrary
directions. -/
def cement : Finset Event :=
  {e | e.domain = .separation ∧ e.patient = .thickSolid ∧ e.result = .gash ∧ e.motion = .linear}

/-- Children carefully tearing tin foil (17) control the separation. -/
def foil : Finset Event := {e | e.domain = .separation ∧ e.control = .careful}

/-- A sudden blaze disturbing the darkness (18b) disturbs a fragile state with little force and
nothing like contrary motion (pp. 97–98). -/
def darkness : Finset Event :=
  {e | e.domain = .state ∧ e.patient = .insubstantial ∧ e.motion ≠ .contrary ∧
    e.force = .slight}

/-- A melody moving through the silence of empty streets (19a) moves linearly through an
insubstantial medium, and not especially fast or violently (p. 97). -/
def melody : Finset Event :=
  {e | e.domain = .motion ∧ e.patient = .insubstantial ∧ e.motion = .linear ∧
    e.force = .slight}

/-- A ball tearing through the rough (23a) moves along a path with considerable energy, without
disrupting the space it moves through (p. 99). -/
def rough : Finset Event :=
  {e | e.domain = .motion ∧ e.motion = .linear ∧ e.force = .considerable}

/-- Both contents meet the description of (16a), which leaves the motion open, so the verbs are
translation equivalents there (p. 95). -/
theorem lenses_verdicts : ¬ Disjoint tearContent lenses ∧
    (¬ Disjoint rasgarContent lenses ↔ ex_16a.judgment = .acceptable) := by
  decide

-- (14), p. 95
theorem bread_verdicts : (¬ Disjoint tearContent bread ↔ ex_14a.judgment = .acceptable) ∧
    (¬ Disjoint rasgarContent bread ↔ ex_14b.judgment = .acceptable) := by
  decide

-- (16b), p. 95
theorem cement_verdicts : Disjoint tearContent cement ∧
    (¬ Disjoint rasgarContent cement ↔ ex_16b.judgment = .acceptable) := by
  decide

-- (17), p. 96
theorem foil_verdicts : (¬ Disjoint tearContent foil ↔ ex_17a.judgment = .acceptable) ∧
    (¬ Disjoint rasgarContent foil ↔ ex_17b.judgment = .acceptable) := by
  decide

-- (18b), pp. 97–98
theorem darkness_verdicts : Disjoint tearContent darkness ∧
    (¬ Disjoint rasgarContent darkness ↔ ex_18b.judgment = .acceptable) := by
  decide

-- (19a), pp. 97, 99
theorem melody_verdicts : Disjoint tearContent melody ∧
    (¬ Disjoint rasgarContent melody ↔ ex_19a.judgment = .acceptable) := by
  decide

-- (23a), p. 99
theorem rough_verdicts : (¬ Disjoint tearContent rough ↔ ex_23a.judgment = .acceptable) ∧
    Disjoint rasgarContent rough := by
  decide

end SpalekMcNally2026
