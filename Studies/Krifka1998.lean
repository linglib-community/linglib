module

public import Linglib.Semantics.Aspect.Telicity
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Tactic.FinCases

/-!
# Krifka (1998): The Origins of Telicity

Krifka treats telicity as a property of event predicates: a predicate is telic when no event it
applies to has a proper part it also applies to that starts or ends at a different time
(`Aspect.IsTelic`). For verbs of consumption and creation telicity follows from the transfer of
part structure between object and event that a strictly incremental thematic relation performs,
and for verbs of movement it follows from expansion, adjacency, and the source and goal of the
path. Quantized predicates are telic but not conversely, and cumulative predicates that apply to
two non-contemporaneous events are atelic.

## Main results

* `eat_apples_cum`, `eat_two_apples_qua`: on a model of *eat*, *eat apples* is cumulative and
  *eat two apples* is quantized.
* `isTelic_vp_of_seinc`: expansion with mapping to objects makes the verb phrase of a quantized
  object telic.
* `isTelic_sourceGoal`: a movement with a specified source and goal is telic.
* `Reading.not_isTelic_read`: incrementality does not guarantee telicity, since re-reading the end
  of an article gives a reading with a non-final part that is also a reading.
* `Movement`: the paper's movement diagrams, checked against adjacency on a finite model.

## Implementation notes

* The model of *eat* identifies an event with the apples it consumes, so its verb phrases are the
  object predicates themselves; the transfer from object to verb phrase is the general
  `Aspect.vp_cum` and `Aspect.vp_qua`.
* Temporal precedence is a parameter of the telicity notions. The paper's consequence of
  its event axioms that overlapping events never precede each other enters as
  `NoPartPrecedes`, which is all the proofs use.
* Overlap is `Mereology.Overlap`, relative to a possible null element. The paper's part
  structures have none, so the expansion theorems assume that the thematic relation never
  relates the null object.
* The source and goal conditions quantify the subpath and the subevent separately; the
  formalization ties them through the thematic relation, as the paper's telicity proof does.
* The measure adverbial (55) is formalized only through its part relation `IsTemporalPart`,
  without its presupposed universal clause over the parts of the witness `e′`.
* The strict-movement telicity claim of the paper does not follow from adjacency and
  mapping to objects alone (adjacency may be empty), and the tangentiality condition on
  sums of movements, the derived measure functions for movement and the changes in other
  dimensions are not formalized.
* In the finite model, the diagram's detour consists of the segments `h` and `i`; the
  paper's list of movements calls the second one `j`.

## References

* [krifka-1998]
-/

@[expose] public section

namespace Krifka1998

open Mereology Aspect

variable {α β : Type*}

/-! ### Measure adverbials -/

section MeasureAdverbial

variable {T : Type*} [PartialOrder β] [PartialOrder T] (τ : β → T)

/-- `e'` is a temporal part of `e`, in the part relation of a temporal measure (55), if it is
part of `e` and `e` has a part whose runtime does not overlap the runtime of `e'`. -/
def IsTemporalPart (e' e : β) : Prop := e' ≤ e ∧ ∃ e'' ≤ e, ¬ Overlap (τ e') (τ e'')

variable {τ}

theorem IsTemporalPart.le {e' e : β} (h : IsTemporalPart τ e' e) : e' ≤ e := h.1

theorem IsTemporalPart.ne {e' e : β} (hτ : Monotone τ) (h : IsTemporalPart τ e' e)
    (h₀ : ∀ e'', e'' ≤ e → ¬ IsBot (τ e'')) : e' ≠ e := by
  rintro rfl
  obtain ⟨_, e'', he'', hov⟩ := h
  exact hov ⟨τ e'', h₀ e'' he'', hτ he'', le_rfl⟩

end MeasureAdverbial

/-! ### Eating apples -/

section Eat

/-- In a model of *eat* with three apples, an eating event is identified with the apples it
consumes. -/
def eat (x e : Finset (Fin 3)) : Prop := x = e

theorem eat_sinc : SINC eat where
  ue _ _ h _ hle := ⟨_, ⟨h ▸ hle, rfl⟩, fun _ hz ↦ hz.2.symm⟩
  uo _ _ h _ hle := ⟨_, ⟨h ▸ hle, rfl⟩, fun _ hz ↦ hz.2⟩
  extended := ⟨{0, 1}, {0}, {0, 1}, {0}, by decide, by decide, rfl, rfl⟩

theorem eat_sum : SUM eat := sum_graph (SupHom.id _)

theorem eat_up : UP eat := up_graph id

/-- *eat apples* is cumulative, since the bare plural is cumulative and *eat* is summative. -/
theorem eat_apples_cum : CUM (VP eat Finset.Nonempty) :=
  vp_cum eat_sum fun _ hx _ _ ↦ hx.mono Finset.subset_union_left

/-- *eat two apples* is quantized, since a measure phrase is quantized and *eat* is strictly
incremental. -/
theorem eat_two_apples_qua : QUA (VP eat (Finset.card · = 2)) :=
  vp_qua eat_up eat_sinc.mso
    (qua_pullback (IsExtensiveMeasure.strictMono Finset.card) (singleton_qua 2))

end Eat

theorem qua_vp_eq [SemilatticeSup α] [SemilatticeSup β] {θ : α → β → Prop} (h : SINC θ)
    (y : α) : QUA (VP θ (· = y)) :=
  vp_eq θ y ▸ h.uo.qua_of_mso h.mso y

/-! ### Incrementality without telicity (§3.6)

An article has two paragraphs, read by the events `0`, `1` and `2`, the last two both reading the
second paragraph. A strict reading reads each paragraph of its object once, and *read* is the
closure of strict reading under sums, which is incremental but lets the reader go back. -/

namespace Reading

/-- Event `0` reads the first paragraph, and events `1` and `2` both read the second. -/
def paragraph (i : Fin 3) : Fin 2 := if i = 0 then 0 else 1

/-- An event is a strict reading of some paragraphs if it reads each of them exactly once. -/
def readOnce (x : Finset (Fin 2)) (e : Finset (Fin 3)) : Prop :=
  (∀ p, p ∈ x ↔ ∃ i ∈ e, paragraph i = p) ∧ ∀ i ∈ e, ∀ j ∈ e, paragraph i = paragraph j → i = j

instance : DecidableRel readOnce := fun _ _ ↦ by unfold readOnce; infer_instance

theorem readOnce_sinc : SINC readOnce where
  ue x e h y hy := by
    revert h hy
    unfold ExistsUnique
    fin_cases x <;> fin_cases e <;> fin_cases y <;> decide
  uo e x h e' he' := by
    revert h he'
    unfold ExistsUnique flip
    fin_cases x <;> fin_cases e <;> fin_cases e' <;> decide
  extended := ⟨{0, 1}, {0}, {0, 1}, {0}, by decide, by decide, by decide, by decide⟩

/-- Reading is the closure of strict reading under sums. -/
def read (x : Finset (Fin 2)) (e : Finset (Fin 3)) : Prop :=
  AlgClosure (Function.uncurry readOnce) (x, e)

theorem read_inc : INC read := ⟨readOnce, readOnce_sinc, fun _ _ ↦ Iff.rfl⟩

/-- An event precedes another if all its times are earlier. -/
def precedes (a b : Finset (Fin 3)) : Prop := ∀ i ∈ a, ∀ j ∈ b, i < j

instance : DecidableRel precedes := fun _ _ ↦ by unfold precedes; infer_instance

/-- *Read the article* is not telic, since the strict reading `{0, 1}` is a part of the reading
`{0, 1, 2}` that the re-reading `{2}` follows. -/
theorem not_isTelic_read : ¬ IsTelic precedes (read Finset.univ) := fun h ↦ by
  have hsum : read Finset.univ {0, 1, 2} := by
    have := AlgClosure.sum (P := Function.uncurry readOnce) (x := (Finset.univ, {0, 1}))
      (y := (Finset.univ, {0, 2})) (.base (by decide)) (.base (by decide))
    rwa [show ((Finset.univ, {0, 1}) ⊔ (Finset.univ, {0, 2}) : Finset (Fin 2) × Finset (Fin 3)) =
      (Finset.univ, {0, 1, 2}) from by decide] at this
  exact (h {0, 1, 2} {0, 1} hsum (.base (by decide)) (by decide)).2.2
    ⟨{2}, by decide, by unfold flip; decide⟩

end Reading

/-! ### Telicity by expansion -/

section Expansion

variable [SemilatticeSup α] [SemilatticeSup β] (precedes : β → β → Prop) (θ : α → β → Prop)

/-- A relation is expansive if the objects of temporally ordered events do not overlap. -/
def EXP : Prop := ∀ x y e e', θ x e → θ y e' → precedes e e' → ¬ Overlap x y

/-- A relation is strictly expansive incremental if it is expansive and maps to objects. -/
def SEINC : Prop := EXP precedes θ ∧ MO θ

variable {precedes θ} (h : SEINC precedes θ) (h₀ : ∀ x e, θ x e → ¬ IsBot x) {x : α} {e e' : β}
include h h₀

theorem isInitialPart_of_seinc (hx : θ x e) (hx' : θ x e') (hle : e' ≤ e) :
    IsInitialPart precedes e' e :=
  ⟨hle, fun ⟨e'', h'', hp⟩ ↦
    let ⟨y, hy, hθ⟩ := h.2 hx h''
    h.1 y x e'' e' hθ hx' hp ⟨y, h₀ y e'' hθ, le_rfl, hy⟩⟩

theorem isFinalPart_of_seinc (hx : θ x e) (hx' : θ x e') (hle : e' ≤ e) :
    IsFinalPart precedes e' e :=
  ⟨hle, fun ⟨e'', h'', hp⟩ ↦
    let ⟨y, hy, hθ⟩ := h.2 hx h''
    h.1 x y e' e'' hx' hθ hp ⟨y, h₀ y e'' hθ, hy, le_rfl⟩⟩

theorem isTelic_of_seinc (x : α) : IsTelic precedes (θ x) :=
  fun _ _ hx hx' hle ↦
    ⟨isInitialPart_of_seinc h h₀ hx hx' hle, isFinalPart_of_seinc h h₀ hx hx' hle⟩

/-- The verb phrase of a quantized object under a strictly expansive incremental relation with
unique participants is telic, as *eat two apples* is. -/
theorem isTelic_vp_of_seinc (hUP : UP θ) {OBJ : α → Prop} (hOBJ : QUA OBJ) :
    IsTelic precedes (VP θ OBJ) := by
  rintro e e' ⟨x, hOx, hx⟩ ⟨x', hOx', hx'⟩ hle
  obtain ⟨x'', hx''le, hx''⟩ := h.2 hx hle
  obtain rfl := hUP hx' hx''
  obtain rfl : x' = x := by_contra fun hne ↦ hOBJ hOx' hOx hne hx''le
  exact ⟨isInitialPart_of_seinc h h₀ hx hx' hle, isFinalPart_of_seinc h h₀ hx hx' hle⟩

end Expansion

/-! ### Movement relations -/

section Movement

variable [SemilatticeSup α] [SemilatticeSup β] (adjα : α → α → Prop) (adjβ : β → β → Prop)
  (precedes : β → β → Prop) (isPath : α → Prop) (θ : α → β → Prop)

/-- A relation has the adjacency property if two subevents of a movement are temporally
adjacent iff their paths are spatially adjacent. -/
def ADJ : Prop :=
  ∀ x e y z e' e'', θ x e → e' ≤ e → e'' ≤ e → y ≤ x → z ≤ x → θ y e' → θ z e'' →
    (adjβ e' e'' ↔ adjα y z)

/-- A strict movement relation has the adjacency property, maps to objects, and takes paths as
objects. -/
def SMR : Prop := ADJ adjα adjβ θ ∧ MO θ ∧ ∀ x e, θ x e → isPath x

/-- The closure of a relation under sums of temporally ordered events. -/
inductive PrecedenceClosure (θ' : α → β → Prop) : α → β → Prop where
  | base {x : α} {e : β} : θ' x e → PrecedenceClosure θ' x e
  | sum {x₁ x₂ : α} {e₁ e₂ : β} : PrecedenceClosure θ' x₁ e₁ → PrecedenceClosure θ' x₂ e₂ →
      precedes e₁ e₂ → PrecedenceClosure θ' (x₁ ⊔ x₂) (e₁ ⊔ e₂)

/-- A movement relation (71) is the closure of a strict movement relation under sums of
temporally ordered events. -/
def MR : Prop :=
  ∃ θ', SMR adjα adjβ isPath θ' ∧ ∀ x e, θ x e ↔ PrecedenceClosure precedes θ' x e

/-- The subpaths of a movement adjacent to `y` are the paths of its initial parts. -/
def Source (y x : α) (e : β) : Prop :=
  ∀ x' e', θ x' e' → x' ≤ x → e' ≤ e → (adjα x' y ↔ IsInitialPart precedes e' e)

/-- The subpaths of a movement adjacent to `y` are the paths of its final parts. -/
def Goal (y x : α) (e : β) : Prop :=
  ∀ x' e', θ x' e' → x' ≤ x → e' ≤ e → (adjα x' y ↔ IsFinalPart precedes e' e)

variable {adjα adjβ precedes isPath θ}

theorem mr_of_smr (h : SMR adjα adjβ isPath θ)
    (hClosed : ∀ x₁ x₂ e₁ e₂, θ x₁ e₁ → θ x₂ e₂ → precedes e₁ e₂ → θ (x₁ ⊔ x₂) (e₁ ⊔ e₂)) :
    MR adjα adjβ precedes isPath θ :=
  ⟨θ, h, fun _ _ ↦ ⟨.base, fun hcl ↦ by
    induction hcl with
    | base h => exact h
    | sum _ _ hp ih₁ ih₂ => exact hClosed _ _ _ _ ih₁ ih₂ hp⟩⟩

/-- A movement with a specified source and goal is telic under mapping to objects and
uniqueness of participants, as *walk from the university to the capitol* is. -/
theorem isTelic_sourceGoal (hax : NoPartPrecedes precedes) (hMO : MO θ) (hUP : UP θ)
    (u v : α) :
    IsTelic precedes
      (fun e ↦ ∃ x, θ x e ∧ Source adjα precedes θ u x e ∧ Goal adjα precedes θ v x e) := by
  rintro e e' ⟨x, hx, hS, hG⟩ ⟨x', hx', hS', hG'⟩ hle
  obtain ⟨x'', hx''le, hx''⟩ := hMO hx hle
  obtain rfl := hUP hx' hx''
  exact ⟨(hS x' e' hx' hx''le hle).1 ((hS' x' e' hx' le_rfl le_rfl).2 (isInitialPart_self hax e')),
    (hG x' e' hx' hx''le hle).1 ((hG' x' e' hx' le_rfl le_rfl).2 (isFinalPart_self hax e'))⟩

end Movement

/-! ### The movement diagrams -/

section Diagram

/-- The path segments of the paper's diagram run from `a` to `g` in a line, with `h` and `i` a
detour from `c` to `f`. -/
inductive Seg | a | b | c | d | e | f | g | h | i
  deriving DecidableEq

/-- The adjacent pairs of segments. -/
def Seg.edges : List (Seg × Seg) :=
  [(.a, .b), (.b, .c), (.c, .d), (.d, .e), (.e, .f), (.f, .g), (.c, .h), (.h, .i), (.i, .f)]

/-- Adjacency of segments. -/
def Seg.adj (s t : Seg) : Prop := (s, t) ∈ edges ∨ (t, s) ∈ edges

instance (s t : Seg) : Decidable (s.adj t) := by unfold Seg.adj; infer_instance

/-- Two paths are adjacent if they are disjoint and have an adjacent pair of segments. -/
def pathAdj (x y : Finset Seg) : Prop := Disjoint x y ∧ ∃ s ∈ x, ∃ t ∈ y, s.adj t

/-- Two events are adjacent if they are disjoint and have a consecutive pair of times. -/
def eventAdj (e e' : Finset (Fin 7)) : Prop :=
  Disjoint e e' ∧ ∃ i ∈ e, ∃ j ∈ e', i.val + 1 = j.val ∨ j.val + 1 = i.val

instance (x y : Finset Seg) : Decidable (pathAdj x y) := by unfold pathAdj; infer_instance

instance (e e' : Finset (Fin 7)) : Decidable (eventAdj e e') := by
  unfold eventAdj; infer_instance

/-- A diagram relates its atomic movements and the whole movement. -/
def support (L : List (Seg × Fin 7)) : List (Finset Seg × Finset (Fin 7)) :=
  L.map (fun p ↦ ({p.1}, {p.2})) ++ [((L.map Prod.fst).toFinset, (L.map Prod.snd).toFinset)]

/-- The movement relation a diagram depicts. -/
def Movement (L : List (Seg × Fin 7)) (x : Finset Seg) (e : Finset (Fin 7)) : Prop :=
  (x, e) ∈ support L

instance (L : List (Seg × Fin 7)) (x : Finset Seg) (e : Finset (Fin 7)) :
    Decidable (Movement L x e) := by
  unfold Movement; infer_instance

private theorem adj_movement_iff {L : List (Seg × Fin 7)} :
    ADJ pathAdj eventAdj (Movement L) ↔
      ∀ p ∈ support L, ∀ q ∈ support L, ∀ r ∈ support L,
        q.2 ≤ p.2 → r.2 ≤ p.2 → q.1 ≤ p.1 → r.1 ≤ p.1 → (eventAdj q.2 r.2 ↔ pathAdj q.1 r.1) :=
  ⟨fun h p hp q hq r hr h₁ h₂ h₃ h₄ ↦ h p.1 p.2 q.1 r.1 q.2 r.2 hp h₁ h₂ h₃ h₄ hq hr,
    fun h _ _ _ _ _ _ hp h₁ h₂ h₃ h₄ hq hr ↦ h _ hp _ hq _ hr h₁ h₂ h₃ h₄⟩

/-- A walk along `a` to `f`. -/
def walk : List (Seg × Fin 7) := [(.a, 0), (.b, 1), (.c, 2), (.d, 3), (.e, 4), (.f, 5)]

/-- A stop-and-go movement pauses between `c` and `d`. -/
def stopAndGo : List (Seg × Fin 7) := [(.a, 0), (.b, 1), (.c, 2), (.d, 4), (.e, 5), (.f, 6)]

/-- Telekinesis moves from `b` straight to `e`. -/
def telekinesis : List (Seg × Fin 7) := [(.a, 0), (.b, 1), (.e, 2), (.f, 3)]

/-- An Echternach movement returns along `c` and `b`. -/
def echternach : List (Seg × Fin 7) := [(.a, 0), (.b, 1), (.c, 2), (.c, 3), (.b, 4)]

/-- An Alcatraz movement goes around the circle `c`, `d`, `e`, `f`, `i`, `h`. -/
def alcatraz : List (Seg × Fin 7) := [(.c, 0), (.d, 1), (.e, 2), (.f, 3), (.i, 4), (.h, 5)]

/-- A movement along a disconnected path. -/
def disconnected : List (Seg × Fin 7) := [(.a, 0), (.b, 1), (.e, 4), (.f, 5)]

theorem adj_walk : ADJ pathAdj eventAdj (Movement walk) := adj_movement_iff.2 (by decide)

theorem not_adj_stopAndGo : ¬ ADJ pathAdj eventAdj (Movement stopAndGo) := fun h ↦
  absurd (h {.a, .b, .c, .d, .e, .f} {0, 1, 2, 4, 5, 6} {.c} {.d} {2} {4} (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)

theorem not_adj_telekinesis : ¬ ADJ pathAdj eventAdj (Movement telekinesis) := fun h ↦
  absurd (h {.a, .b, .e, .f} {0, 1, 2, 3} {.b} {.e} {1} {2} (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)) (by decide)

theorem not_adj_echternach : ¬ ADJ pathAdj eventAdj (Movement echternach) := fun h ↦
  absurd (h {.a, .b, .c} {0, 1, 2, 3, 4} {.c} {.c} {2} {3} (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)) (by decide)

theorem not_adj_alcatraz : ¬ ADJ pathAdj eventAdj (Movement alcatraz) := fun h ↦
  absurd (h {.c, .d, .e, .f, .i, .h} {0, 1, 2, 3, 4, 5} {.h} {.c} {5} {0} (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)

/-- A set of segments is connected if no proper nonempty subset is closed under adjacency. -/
def Connected (x : Finset Seg) : Prop :=
  ∀ y ∈ x.powerset, y.Nonempty → y ≠ x → ∃ s ∈ y, ∃ t ∈ x \ y, s.adj t

theorem adj_disconnected :
    ADJ pathAdj eventAdj (Movement disconnected) ∧ ¬ Connected {.a, .b, .e, .f} :=
  ⟨adj_movement_iff.2 (by decide),
    fun h ↦ absurd (h {.a, .b} (by decide) (by decide) (by decide)) (by decide)⟩

end Diagram

end Krifka1998
