module

public import Linglib.Semantics.Reference.Context.Overwrite
public import Studies.Schlenker2003
public import Linglib.Data.Examples.AnandNevins2004

/-!
# Anand and Nevins (2004): shifty operators in changing contexts

Indexicals shift under *vano* 'say' in Zazaki and under some verbs in Slave, but those of one
speech-context domain shift together (16), the embedding verb decides which shift and whether they
must (39), and a shift in an intermediate report keeps the lowest indexicals from the utterance
context (32). The account: the index has the type of the context, and a verb may take as sister an
operator that overwrites coordinates of the context with those of the index (2).

## Main definitions

* `opAll` (25), `opAuth` (29): Zazaki's and Slave's operators, as the coordinates their
  `Kaplan.shiftyOp` overwrites.
* `say`: an attitude verb (23b), quantifying over indices of the context type.
* `readings e χ c j`: the values of `χ` under a verb with operator options `e` (39).
* `Bound`: the binding account (19) with the constraint (22), on the context tower.

## Implementation notes

Meanings are `Kaplan.Character`s whose index is a `Kaplan.Context`, and an operator is the set of
coordinates it overwrites (`Kaplan.Context.overwrite`). On pp. 25
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

open Kaplan (Character Context IsMonster shiftyOp isMonster_shiftBy_iff)
open Kaplan.Context (Coord equivPi localDepth overwrite)
open ContextTower (AccessPattern)

universe u

variable {W E P T : Type u} {α β : Type*}

/-! ### Operators and attitude verbs -/

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

/-- `OP∀` is Stalnaker's diagonal operator, evaluating its prejacent at the index taken as its own
context (fn. 7). -/
theorem shiftyOp_opAll_iff_holdsAt (χ : Character (Context W E P T) (Context W E P T) Prop)
    (c i : Context W E P T) : shiftyOp opAll χ c i ↔ χ.HoldsAt id i := by
  simp [Character.HoldsAt]

-- (26), (28)
theorem say_shiftyOp_opAll (χ : Character (Context W E P T) (Context W E P T) Prop)
    (c i : Context W E P T) : say acc x (shiftyOp opAll χ) c i ↔ ∀ j ∈ acc x i, χ j j := by
  simp [say]

-- §3.4
theorem shiftyOp_opAll_eq (χ : Character (Context W E P T) (Context W E P T) α)
    (c c' : Context W E P T) : shiftyOp opAll χ c = shiftyOp opAll χ c' := by
  ext; simp

/-- An attitude verb leaves the context untouched, so it is no monster (§3.1): indexical shift
comes from the operators, not the verbs. -/
theorem not_isMonster_say : ¬ IsMonster (say acc x) :=
  fun h ↦ h ⟨fun _ f i ↦ ∀ j ∈ acc x i, f j, fun _ _ ↦ rfl⟩

theorem not_isMonster_shiftyOp_empty :
    ¬ IsMonster (shiftyOp ∅ : Character (Context W E P T) (Context W E P T) α → _) :=
  fun h ↦ h ⟨fun _ f ↦ f, fun _ _ ↦ by ext; simp⟩

/-- An operator overwriting the author, as `OP∀` and `OP_AUTH` do, is a monster once there are
two individuals. -/
theorem isMonster_shiftyOp_of_agent_mem [Nontrivial α] [Nontrivial E] [Nonempty W] [Nonempty P]
    [Nonempty T] {S : Finset Coord} (hS : .agent ∈ S) :
    IsMonster (shiftyOp S : Character (Context W E P T) (Context W E P T) α → _) := by
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

-- §5.1
theorem shiftyOp_opAll_I : shiftyOp opAll (I : Character (Context W E P T) _ E) = proSubj := by
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
  (fun S ↦ shiftyOp S χ c j) '' e

variable (c j : Context W E P T)

/-- Shift-Together (16), (13), (21): under *vano* any two indexicals read the utterance context or
both read the reported one, never one each. -/
theorem readings_vano_prod (f : Context W E P T → α) (g : Context W E P T → β) :
    readings vano (fun c _ ↦ (f c, g c)) c j = {(f c, g c), (f j, g j)} := by
  simp [readings, vano, Set.image_insert_eq]

-- (17), (38b)
theorem readings_slaveSay :
    readings slaveSay (fun c i ↦ (I c i, you c i)) c j = {(j.agent, c.addressee)} := by
  simp [readings, slaveSay, I, you]

-- (37), (38a)
theorem readings_slaveWant :
    readings slaveWant (fun c i ↦ (I c i, you c i)) c j =
      {(c.agent, c.addressee), (j.agent, c.addressee)} := by
  simp [readings, slaveWant, Set.image_insert_eq, I, you]

/-! ### Multiple embedding -/

variable (j₁ j₂ : Context W E P T) (S₁ S₂ : Finset Coord)

-- (31)
theorem say_shiftyOp_say_shiftyOp (acc' : E → Context W E P T → Set (Context W E P T)) (y : E)
    (χ : Character (Context W E P T) (Context W E P T) Prop) (i : Context W E P T) :
    say acc x (shiftyOp S₁ (say acc' y (shiftyOp S₂ χ))) c i ↔
      ∀ j₁ ∈ acc x i, ∀ j₂ ∈ acc' y j₁, χ (overwrite S₂ (overwrite S₁ c j₁) j₂) j₂ := by
  simp [say]

theorem apply_foldl_overwrite_eq_contextAt {f : Context W E P T → α} {k : Coord}
    (hf : DependsOn (f ∘ equivPi.symm) {k}) (c : Context W E P T)
    (ops : List (Finset Coord × Context W E P T)) :
    f (ops.foldl (fun c p ↦ overwrite p.1 c p.2) c) =
      f ((⟨c, ops.map Prod.snd⟩ : ContextTower _).contextAt (localDepth (ops.map Prod.fst) k)) :=
  Kaplan.Context.apply_foldl_overwrite hf c ops

variable {c j₁ S₁ S₂}

/-- If the intermediate clause has a shifted second person, the lowest clause reads no coordinate
from the utterance context (32). -/
theorem localDepth_ne_zero (h₁ : S₁ ∈ vano) (h₂ : S₂ ∈ vano)
    (hyou : (overwrite S₁ c j₁).addressee = j₁.addressee) (hne : c.addressee ≠ j₁.addressee)
    (k : Coord) : localDepth [S₁, S₂] k ≠ 0 := by
  simp only [vano, Finset.mem_insert, Finset.mem_singleton] at h₁ h₂
  obtain rfl | rfl := h₁
  · exact absurd (by simpa using hyou) hne
  · obtain rfl | rfl := h₂ <;> simp [localDepth]

/-- The binding account of [schlenker-2003] as (19) renders it, with the constraint (22): the
indexicals of a clause are bound by one context, the utterance context or a reported one above it,
the context at some depth of the tower, and `f` takes the value `a` there. -/
def Bound (t : ContextTower (Context W E P T)) (f : Context W E P T → α) (a : α) : Prop :=
  ∃ k ≤ t.depth, (AccessPattern.mk (.relative k) f).resolve t = a

-- (32)
theorem bound_origin (t : ContextTower (Context W E P T)) (f : Context W E P T → α) :
    Bound t f (f t.origin) :=
  ⟨0, Nat.zero_le _, by simp [AccessPattern.resolve]⟩

-- (19)
theorem bound_I_amharicI (t : ContextTower (Context W E P T)) :
    Bound t Context.agent (Kaplan.I.resolve t) ∧
      Bound t Context.agent (Schlenker2003.amharicI.resolve t) :=
  ⟨by simpa [Kaplan.I] using bound_origin t Context.agent,
    ⟨t.depth, le_rfl, by
      simp [AccessPattern.resolve, AccessPattern.innermost, Schlenker2003.amharicI]⟩⟩

/-- For a single report, *say* with `OP∀` agrees with Schlenker's binding verb (§3.4). -/
theorem say_shiftyOp_opAll_iff_say (compat : E → T → W → Set (Context W E P T))
    (χ : Character (Context W E P T) (Context W E P T) Prop) (c i : Context W E P T) :
    say (fun x i ↦ compat x i.time i.world) x (shiftyOp opAll χ) c i ↔
      Schlenker2003.Say compat x i.time i.world (fun t ↦ χ t.innermost t.innermost) (.root c) := by
  simp [say, Schlenker2003.Say]

/-- Under two reports with Schlenker's verbs the lowest clause can still read the utterance context,
contrary to (32). -/
theorem say_say_bound_origin (compat compat' : E → T → W → Set (Context W E P T)) (y : E)
    (f : Context W E P T → α) (c : Context W E P T) :
    Schlenker2003.Say compat x c.time c.world
      (fun t ↦ Schlenker2003.Say compat' y t.innermost.time t.innermost.world
        (fun t' ↦ Bound t' f (f c)) t) (.root c) :=
  fun _ _ _ _ ↦ bound_origin _ f

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

/-- A judged mixed reading is acceptable iff an operator option of the verb shifts one embedded
indexical but not another, which is Shift-Together (16). -/
theorem rows_mixed :
    ∀ r ∈ Examples.all, ∀ p ∈ (singleReport? r).toList, ∀ x ∈ r.readings,
      "mixed".toList <+: x.1.toList →
        (x.2 = .acceptable ↔ ∃ S ∈ p.1, ∃ k ∈ p.2, ∃ k' ∈ p.2, k ∈ S ∧ k' ∉ S) := by
  decide +kernel

/-- In the lower of two reports, a judged reading is acceptable iff the verbs' operator options make
each embedded indexical read the context at its depth ((32), (33)). -/
theorem rows_double_report :
    ∀ r ∈ Examples.all, r.feature? "test" = some "multiple_embedding" →
      ∀ p ∈ (entryCoords? r).toList, ∀ x ∈ r.readings,
        ∀ d ∈ [("utterance context", 0), ("intermediate reported context", 1),
            ("lowest reported context", 2)], x.1 = d.1 →
          (x.2 = .acceptable ↔ ∃ S₁ ∈ p.1, ∃ S₂ ∈ p.1,
            (r.feature? "intermediate_shift" = some "yes" → .addressee ∈ S₁) ∧
              ∀ k ∈ p.2, localDepth [S₁, S₂] k = d.2) := by
  decide +kernel

example : (Examples.all.filter fun r ↦ (singleReport? r).isSome).length = 18 := by decide +kernel

end AnandNevins2004
