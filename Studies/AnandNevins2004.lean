module

public import Linglib.Semantics.Reference.Kaplan
public import Linglib.Data.Examples.AnandNevins2004
public import Mathlib.Tactic.DeriveFintype

/-!
# Anand and Nevins (2004): shifty operators in changing contexts

Indexicals shift under *vano* 'say' in Zazaki and under some verbs in Slave, but those of one
speech-context domain shift together (16), the embedding verb decides which shift and whether they
must (39), and a shift in an intermediate report keeps the lowest indexicals from the utterance
context (32). The account: the index has the type of the context, and a verb may take as sister an
operator that overwrites coordinates of the context with those of the index (2).

## Main definitions

* `overwrite S c i`: the context `c` with the coordinates in `S` taken from `i`.
* `op S`: the operator overwriting `S`, Zazaki's `opAll` (25) and Slave's `opAuth` (29).
* `say`: an attitude verb (23b), quantifying over indices of the context type.
* `readings e χ c j`: the values of `χ` under a verb with operator options `e` (39).
* `Bound`: the binding account (19) with the constraint (22), on the context tower.

## Main results

* `op_opAll_iff_holdsAt`: `OP∀` is Stalnaker's diagonal (fn. 7).
* `isMonster_op_of_agent_mem`, `not_isMonster_say`: the operators are monsters, the verbs not.
* `readings_vano_prod`, `rows_mixed`: Shift-Together (16).
* `depth₂_ne_zero`: after a shift in the intermediate report the lowest clause cannot read the
  utterance context (32), which the binding account allows (`bound_origin`).
* `rows_reported`, `rows_utterance`, `rows_double_report`: the rows' judgments.

## Implementation notes

Meanings are `Kaplan.Character`s whose index is a `Kaplan.Context`, and an operator is the set of
coordinates it overwrites, so `overwrite S` is a coordinatewise `Finset.piecewise`. On pp. 25
and 28 the paper cites "(25)" for the restriction on shifting and for the clausemate-binding
condition, which are its (16) and (22).

## TODO

Context blocking (44) of the Mupun addressee logophor (45), and the apparent counterexamples to
Shift-Together from Amharic (46) and English (47)–(50), are rows without theorems.

## References

* [anand-nevins-2004]
* [kaplan-1989]
* [schlenker-2003]
* [stalnaker-1978]
-/

@[expose] public section

namespace AnandNevins2004

open Kaplan (Character Context IsMonster shiftBy isMonster_shiftBy_iff)
open ContextTower (AccessPattern)

variable {W E P T α β : Type*}

/-! ### Overwriting coordinates of the context -/

/-- The coordinates of a context (29): its author, addressee, location, time and world. -/
inductive Coord
  | agent
  | addressee
  | position
  | time
  | world
  deriving DecidableEq, Fintype

/-- The context `c` with the coordinates in `S` overwritten by those of `i`. -/
@[simps]
def overwrite (S : Finset Coord) (c i : Context W E P T) : Context W E P T where
  agent := if .agent ∈ S then i.agent else c.agent
  addressee := if .addressee ∈ S then i.addressee else c.addressee
  world := if .world ∈ S then i.world else c.world
  time := if .time ∈ S then i.time else c.time
  position := if .position ∈ S then i.position else c.position

section overwrite

variable (c i : Context W E P T)

@[simp] theorem overwrite_empty : overwrite ∅ c i = c := by simp [overwrite]

@[simp] theorem overwrite_univ : overwrite .univ c i = i := by simp [overwrite]

end overwrite

/-! ### Operators and attitude verbs -/

/-- The context-shifting operator that overwrites the coordinates `S` of the context with those of
the index (2): `⟦OP α⟧^{c,i} = ⟦α⟧^{overwrite S c i, i}`. -/
def op (S : Finset Coord) :
    Character (Context W E P T) (Context W E P T) α →
      Character (Context W E P T) (Context W E P T) α :=
  shiftBy (overwrite S)

@[simp] theorem op_apply (S : Finset Coord) (χ : Character (Context W E P T) (Context W E P T) α)
    (c i : Context W E P T) : op S χ c i = χ (overwrite S c i) i := rfl

/-- Zazaki's `OP∀` overwrites every coordinate (25). -/
abbrev opAll : Finset Coord := .univ

/-- Slave's `OP_AUTH` overwrites the author (29). -/
abbrev opAuth : Finset Coord := {.agent}

/-- An attitude verb (23b): `⟦say α⟧^{c,i}` is true of `x` iff `α` is true at the context and
every index compatible with what `x` says in `i`. -/
def say (acc : E → Context W E P T → Set (Context W E P T)) (x : E)
    (χ : Character (Context W E P T) (Context W E P T) Prop) :
    Character (Context W E P T) (Context W E P T) Prop :=
  fun c i ↦ ∀ j ∈ acc x i, χ c j

variable (acc : E → Context W E P T → Set (Context W E P T)) (x : E)

/-- `OP∀` is Stalnaker's diagonal operator (fn. 7): a sentence under it holds at a context and an
index iff its character holds at the index taken as its own context. -/
theorem op_opAll_iff_holdsAt (χ : Character (Context W E P T) (Context W E P T) Prop)
    (c i : Context W E P T) : op opAll χ c i ↔ χ.HoldsAt id i := by
  simp [Character.HoldsAt]

/-- (26)–(28): with `OP∀` as sister, *say* evaluates its complement at the reported contexts
alone, so every indexical in it shifts. -/
theorem say_op_opAll (χ : Character (Context W E P T) (Context W E P T) Prop)
    (c i : Context W E P T) : say acc x (op opAll χ) c i ↔ ∀ j ∈ acc x i, χ j j := by
  simp [say]

/-- Within the scope of `OP∀` the utterance context is lost (§3.4): the operator's output does
not depend on it. -/
theorem op_opAll_eq (χ : Character (Context W E P T) (Context W E P T) α)
    (c c' : Context W E P T) : op opAll χ c = op opAll χ c' := by
  ext; simp

/-- An attitude verb leaves the context untouched, so it is no monster (§3.1): indexical shift
comes from the operators, not the verbs. -/
theorem not_isMonster_say : ¬ IsMonster (say acc x) :=
  fun h ↦ h ⟨fun _ f i ↦ ∀ j ∈ acc x i, f j, fun _ _ ↦ rfl⟩

/-- Without an operator the context stays put. -/
theorem not_isMonster_op_empty :
    ¬ IsMonster (op ∅ : Character (Context W E P T) (Context W E P T) α → _) :=
  fun h ↦ h ⟨fun _ f ↦ f, fun _ _ ↦ by ext; simp⟩

/-- An operator overwriting the author, as `OP∀` and `OP_AUTH` do, is a monster once there are
two individuals. -/
theorem isMonster_op_of_agent_mem [Nontrivial α] [Nontrivial E] [Nonempty W] [Nonempty P]
    [Nonempty T] {S : Finset Coord} (hS : .agent ∈ S) :
    IsMonster (op S : Character (Context W E P T) (Context W E P T) α → _) := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne E
  obtain ⟨w⟩ := ‹Nonempty W›; obtain ⟨p⟩ := ‹Nonempty P›; obtain ⟨t⟩ := ‹Nonempty T›
  refine (isMonster_shiftBy_iff _).2 ⟨⟨a, a, w, t, p⟩, ⟨b, a, w, t, p⟩, fun h ↦ hab ?_⟩
  simpa [hS] using (congrArg Context.agent h).symm

/-! ### Indexicals, PRO and logophors -/

/-- The first person reads the author of the context (24a). -/
def I : Character (Context W E P T) (Context W E P T) E := Character.dthat Context.agent

/-- The second person reads the addressee of the context. -/
def you : Character (Context W E P T) (Context W E P T) E := Character.dthat Context.addressee

/-- Subject-controlled PRO (41) and the author logophor (43a) read the author of the index, the
attitude holder's counterpart, so they are read de se. -/
def proSubj : Character (Context W E P T) (Context W E P T) E := fun _ i ↦ i.agent

/-- A first person under `OP∀` is subject PRO: shifted, it is read de se (§5.1). -/
theorem op_opAll_I : op opAll (I : Character (Context W E P T) _ E) = proSubj := by
  ext; simp [I, proSubj]

/-! ### Lexical entries and readings -/

/-- Zazaki *vano* 'say' takes `OP∀` optionally. -/
def vano : Finset (Finset Coord) := {∅, opAll}

/-- The other Zazaki attitude verbs take no operator (fn. 3). -/
def zazakiAttitude : Finset (Finset Coord) := {∅}

/-- Slave TELL takes `OP∀` optionally (39). -/
def slaveTell : Finset (Finset Coord) := {∅, opAll}

/-- Slave WANT takes `OP_AUTH` optionally (39). -/
def slaveWant : Finset (Finset Coord) := {∅, opAuth}

/-- Slave SAY takes `OP_AUTH` obligatorily (39). -/
def slaveSay : Finset (Finset Coord) := {opAuth}

/-- The values `χ` takes under a verb with operator options `e`, at the context `c` and a reported
index `j`. -/
def readings (e : Finset (Finset Coord)) (χ : Character (Context W E P T) (Context W E P T) α)
    (c j : Context W E P T) : Set α :=
  (fun S ↦ op S χ c j) '' e

variable (c j : Context W E P T)

/-- Shift-Together (16), (13), (21): under *vano* any two indexicals read the utterance context or
both read the reported one, never one each. -/
theorem readings_vano_prod (f : Context W E P T → α) (g : Context W E P T → β) :
    readings vano (fun c _ ↦ (f c, g c)) c j = {(f c, g c), (f j, g j)} := by
  simp [readings, vano, Set.image_insert_eq]

/-- (17), (38b): under Slave SAY the first person is the reported author and the second the
utterance addressee, obligatorily. -/
theorem readings_slaveSay :
    readings slaveSay (fun c i ↦ (I c i, you c i)) c j = {(j.agent, c.addressee)} := by
  simp [readings, slaveSay, I, you]

/-- (37), (38a): under Slave WANT the first person shifts optionally and the second never. -/
theorem readings_slaveWant :
    readings slaveWant (fun c i ↦ (I c i, you c i)) c j =
      {(c.agent, c.addressee), (j.agent, c.addressee)} := by
  simp [readings, slaveWant, Set.image_insert_eq, I, you]

/-! ### Multiple embedding -/

/-- The tower of two stacked reports over the utterance context `c`, with the reported contexts
`j₁` and `j₂`. -/
def tower₂ (c j₁ j₂ : Context W E P T) : ContextTower (Context W E P T) :=
  ⟨c, [Function.const _ j₁, Function.const _ j₂]⟩

/-- The depth in `tower₂` of the context from which the lowest of two stacked clauses reads the
coordinate `k`, under options `S₁` of the intermediate verb and `S₂` of the lowest. -/
def depth₂ (S₁ S₂ : Finset Coord) (k : Coord) : ℕ :=
  if k ∈ S₂ then 2 else if k ∈ S₁ then 1 else 0

variable (j₁ j₂ : Context W E P T) (S₁ S₂ : Finset Coord)

/-- Two stacked reports evaluate the lowest complement at the utterance context overwritten by the
intermediate operator from the intermediate reported context, then by the lowest operator from the
lowest one (31). -/
theorem say_op_say_op (acc' : E → Context W E P T → Set (Context W E P T)) (y : E)
    (χ : Character (Context W E P T) (Context W E P T) Prop) (i : Context W E P T) :
    say acc x (op S₁ (say acc' y (op S₂ χ))) c i ↔
      ∀ j₁ ∈ acc x i, ∀ j₂ ∈ acc' y j₁, χ (overwrite S₂ (overwrite S₁ c j₁) j₂) j₂ := by
  simp [say]

/-- The lowest of two stacked clauses reads the author of the context of the tower at the depth
the operators fix. -/
theorem agent_overwrite_overwrite :
    (overwrite S₂ (overwrite S₁ c j₁) j₂).agent =
      ((tower₂ c j₁ j₂).contextAt (depth₂ S₁ S₂ .agent)).agent := by
  unfold depth₂; split_ifs <;> simp_all [tower₂, ContextTower.contextAt, Function.End.mul_def]

variable {c j₁ S₁ S₂}

/-- (32): a shifted second person in the intermediate clause diagnoses `OP∀` there, after which
the lowest clause reads no coordinate from the utterance context. -/
theorem depth₂_ne_zero (h₁ : S₁ ∈ vano) (h₂ : S₂ ∈ vano)
    (hyou : (overwrite S₁ c j₁).addressee = j₁.addressee) (hne : c.addressee ≠ j₁.addressee)
    (k : Coord) : depth₂ S₁ S₂ k ≠ 0 := by
  simp only [vano, Finset.mem_insert, Finset.mem_singleton] at h₁ h₂
  obtain rfl | rfl := h₁
  · exact absurd (by simpa using hyou) hne
  · obtain rfl | rfl := h₂ <;> simp [depth₂]

/-- The binding account of [schlenker-2003] as (19) renders it, with the constraint (22): the
indexicals of a clause are bound by one context, the utterance context or a reported one above it,
the context at some depth of the tower, and `f` takes the value `a` there. -/
def Bound (t : ContextTower (Context W E P T)) (f : Context W E P T → α) (a : α) : Prop :=
  ∃ k ≤ t.depth, (AccessPattern.mk (.relative k) f).resolve t = a

/-- On the binding account a clause can always read the utterance context, whatever the clauses
above it read: binding locally does not prevent binding at a distance, against (32). -/
theorem bound_origin (t : ContextTower (Context W E P T)) (f : Context W E P T → α) :
    Bound t f (f t.origin) :=
  ⟨0, Nat.zero_le _, by simp [AccessPattern.resolve]⟩

/-! ### The rows -/

/-- The operator options of the rows' embedding verbs. -/
def entry? : String → Option (Finset (Finset Coord))
  | "vano" => some vano
  | "zazaki_attitude" => some zazakiAttitude
  | "slave_tell" => some slaveTell
  | "slave_want" => some slaveWant
  | "slave_say" => some slaveSay
  | _ => none

/-- The coordinate each indexical of the rows reads. -/
def coord? : String → Option Coord
  | "I" | "me" => some .agent
  | "you" => some .addressee
  | "here" => some .position
  | "now" | "yesterday" | "in two weeks" => some .time
  | _ => none

/-- The operator options of a row's embedding verb and the coordinates its embedded indexicals
read. -/
def entryCoords? (r : Datum) : Option (Finset (Finset Coord) × List Coord) :=
  ((r.feature? "entry").bind entry?).bind fun e ↦ ((r.features "indexical").mapM coord?).map (e, ·)

/-- `entryCoords?` of a row with a single report, unless the row excludes a reading on pragmatic
grounds, as (7) does. -/
def singleReport? (r : Datum) : Option (Finset (Finset Coord) × List Coord) :=
  if r.feature? "test" ≠ some "multiple_embedding" ∧ r.feature? "pragmatic_clash" = none then
    entryCoords? r
  else none

/-- A judged reading with every embedded indexical at the reported context is acceptable exactly
when an operator option of the verb overwrites all their coordinates. -/
theorem rows_reported :
    ∀ r ∈ Examples.all, ∀ p ∈ (singleReport? r).toList, ∀ x ∈ r.readings,
      x.1 ∈ ["reported context", "both reported"] →
        (x.2 = .acceptable ↔ ∃ S ∈ p.1, ∀ k ∈ p.2, k ∈ S) := by
  decide +kernel

/-- A judged reading with every embedded indexical at the utterance context is acceptable exactly
when an operator option of the verb overwrites none of their coordinates. -/
theorem rows_utterance :
    ∀ r ∈ Examples.all, ∀ p ∈ (singleReport? r).toList, ∀ x ∈ r.readings,
      x.1 ∈ ["utterance context", "both utterance"] →
        (x.2 = .acceptable ↔ ∃ S ∈ p.1, ∀ k ∈ p.2, k ∉ S) := by
  decide +kernel

/-- Shift-Together (16): a judged mixed reading is acceptable exactly when an operator option of
the verb overwrites the coordinate of one embedded indexical but not of another, which no option of
the rows' verbs does. -/
theorem rows_mixed :
    ∀ r ∈ Examples.all, ∀ p ∈ (singleReport? r).toList, ∀ x ∈ r.readings,
      "mixed".toList <+: x.1.toList →
        (x.2 = .acceptable ↔ ∃ S ∈ p.1, ∃ k ∈ p.2, ∃ k' ∈ p.2, k ∈ S ∧ k' ∉ S) := by
  decide +kernel

/-- (32), (33): in the lowest of two reports, a judged reading of the embedded indexicals is
acceptable exactly when options of the intermediate and the lowest verb make them read the
context at its depth, the intermediate option overwriting the addressee where the intermediate
clause has a shifted second person. -/
theorem rows_double_report :
    ∀ r ∈ Examples.all, r.feature? "test" = some "multiple_embedding" →
      ∀ p ∈ (entryCoords? r).toList, ∀ x ∈ r.readings,
        ∀ d ∈ [("utterance context", 0), ("intermediate reported context", 1),
            ("lowest reported context", 2)], x.1 = d.1 →
          (x.2 = .acceptable ↔ ∃ S₁ ∈ p.1, ∃ S₂ ∈ p.1,
            (r.feature? "intermediate_shift" = some "yes" → .addressee ∈ S₁) ∧
              ∀ k ∈ p.2, depth₂ S₁ S₂ k = d.2) := by
  decide +kernel

example : (Examples.all.filter fun r ↦ (singleReport? r).isSome).length = 18 := by decide +kernel

end AnandNevins2004
