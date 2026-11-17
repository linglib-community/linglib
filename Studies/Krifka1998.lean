module

public import Linglib.Semantics.Aspect.Telicity
public import Studies.Krifka1989
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Tactic.FinCases
public import Linglib.Semantics.Mereology.Measure

/-!
# Krifka (1998): The Origins of Telicity

Krifka treats telicity as a property of event predicates: a predicate is telic when no event it
applies to has a proper part it also applies to that starts or ends at a different time
(`Aspect.IsTelic`). For verbs of consumption and creation telicity follows from the transfer of
part structure between object and event that a strictly incremental thematic relation performs,
and for verbs of movement it follows from expansion, adjacency, and the source and goal of the
path. Quantized predicates are telic but not conversely, and cumulative predicates that apply to
two non-contemporaneous events are atelic.

## Implementation notes

* The model of *eat* identifies an event with the apples it consumes, so its verb phrases are the
  object predicates themselves; the transfer from object to verb phrase is the general
  `Aspect.vp_cum` and, for the strictly incremental and summative relation of (54),
  `Aspect.SINC.vp_qua`.
* Temporal precedence is a parameter of the telicity notions. The paper's consequence of
  its event axioms that overlapping events never precede each other enters as
  `NoPartPrecedes`, which is all the proofs use and which [any precedence on a part structure
  of events satisfies](##IsTemporalPrecedence.noPartPrecedes).
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
open scoped SetRel

variable {α β : Type*}

/-! ### Measure adverbials -/

section MeasureAdverbial

variable {T : Type*} [PartialOrder β] [PartialOrder T] (τ : β → T)

/-- `e'` is a temporal part of `e`, in the part relation of a temporal measure (55), if it is
part of `e` and `e` has a part whose runtime does not overlap the runtime of `e'`. -/
structure IsTemporalPart (e' e : β) : Prop where
  le : e' ≤ e
  exists_not_overlap : ∃ e'' ≤ e, ¬ Overlap (τ e') (τ e'')

variable {τ}

theorem IsTemporalPart.ne {e' e : β} (hτ : Monotone τ) (h : IsTemporalPart τ e' e)
    (h₀ : ∀ e'', e'' ≤ e → ¬ IsBot (τ e'')) : e' ≠ e := by
  rintro rfl
  obtain ⟨_, e'', he'', hov⟩ := h
  exact hov ⟨τ e'', h₀ e'' he'', hτ he'', le_rfl⟩

end MeasureAdverbial

/-! ### Telicity without quantization

With events ordered by their participants and run times, the predicate true of the events that run
from three to four is telic under temporal precedence, though it holds of an event and of a proper
part with the same run time; under the same precedence the predicate true of every event is not
telic. -/

section NotQua

open Event

/-- An event of the model is a set of participants with a run time. -/
abbrev Ev : Type := Finset (Fin 2) × NonemptyInterval ℕ

local instance : TemporalTrace Ev ℕ := ⟨Prod.snd⟩

-- A telic predicate need not be quantized.
theorem exists_isTelic_not_qua :
    ∃ P : Ev → Prop, IsTelic (Precedes : Ev → Ev → Prop) P ∧ ¬ QUA P ∧
      ¬ IsTelic (Precedes : Ev → Ev → Prop) fun _ ↦ True := by
  refine ⟨(τ · = ⟨(3, 4), by decide⟩), isTelic_runTime_eq monotone_snd _, fun h ↦ ?_, fun h ↦ ?_⟩
  · exact h (x := ({0}, ⟨(3, 4), by decide⟩)) rfl (y := ({0, 1}, ⟨(3, 4), by decide⟩)) rfl
      (fun hxy ↦ absurd (congrArg Prod.fst hxy) (by decide))
      (Prod.mk_le_mk.2 ⟨(by decide : ({0} : Finset (Fin 2)) ⊆ {0, 1}), le_rfl⟩)
  · have hi := (@h ({0}, ⟨(0, 1), by decide⟩) ({0}, ⟨(1, 1), by decide⟩) trivial trivial
      (Prod.mk_le_mk.2 ⟨le_rfl, NonemptyInterval.le_def.2 ⟨by decide, by decide⟩⟩)).left
    refine hi.not_precedes (e'' := ({0}, ⟨(0, 0), by decide⟩)) ?_ ?_
    · exact Prod.mk_le_mk.2 ⟨le_rfl, NonemptyInterval.le_def.2 ⟨by decide, by decide⟩⟩
    · exact (by decide : (0 : ℕ) < 1)

end NotQua

/-! ### Eating apples -/

section Eat

/-- In a model of *eat* with three apples, an eating event is identified with the apples it
consumes. -/
def eat : SetRel (Finset (Fin 3)) (Finset (Fin 3)) := SetRel.id

theorem eat_sinc : SINC eat where
  ue _ _ h _ hle := ⟨_, ⟨hle.trans_eq h, rfl⟩, fun _ ⟨_, hz⟩ ↦ Eq.symm hz⟩
  uo _ _ h _ hle := ⟨_, ⟨hle.trans_eq (Eq.symm h), rfl⟩, fun _ ⟨_, hz⟩ ↦ hz⟩
  extended := ⟨{0, 1}, {0}, {0, 1}, {0}, by decide, by decide, rfl, rfl⟩

theorem eat_sum : SUM eat := fun ⟨_, _⟩ h₁ ⟨_, _⟩ h₂ ↦ congr_arg₂ (· ⊔ ·) h₁ h₂

/-- *eat apples* is cumulative, since the bare plural is cumulative and *eat* is summative. -/
theorem eat_apples_cum : CUM (VP eat Finset.Nonempty) :=
  vp_cum eat_sum fun _ hx _ _ ↦ hx.mono Finset.subset_union_left

/-- *eat two apples* is quantized, since a measure phrase is quantized and *eat* is strictly
incremental and summative (54). -/
theorem eat_two_apples_qua : QUA (VP eat (Finset.card · = 2)) :=
  eat_sinc.vp_qua eat_sum
    (qua_pullback (IsExtensiveMeasure.strictMono Finset.card) (singleton_qua 2))

end Eat

theorem qua_vp_eq [SemilatticeSup α] [SemilatticeSup β] {θ : SetRel α β} (h : SINC θ)
    (y : α) : QUA (VP θ (· = y)) :=
  vp_eq θ y ▸ h.uo.qua_of_mso h.mso y

-- Uniqueness of events is mapping to events without the iterativity of Krifka (1989).
theorem ue_iff_me_and_forall_not_iter [SemilatticeSup α] [SemilatticeSup β] {θ : SetRel α β} :
    UE θ ↔ ME θ ∧ ∀ e x, ¬ Krifka1989.ITER θ e x :=
  ⟨fun h ↦ ⟨h.me, fun _ _ ⟨hxe, _, _, _, h', h'', hne, hx', hθ', hθ''⟩ ↦
      hne ((h hxe hx').unique ⟨h', hθ'⟩ ⟨h'', hθ''⟩)⟩,
    fun ⟨hm, hi⟩ x e hxe y hy ↦
      let ⟨e', he', hθ⟩ := hm hxe hy
      ⟨e', ⟨he', hθ⟩, fun e'' ⟨he'', hθ''⟩ ↦ by_contra fun hne ↦
        hi e x ⟨hxe, e'', e', y, he'', he', hne, hy, hθ'', hθ⟩⟩⟩

/-! ### Strict incrementality without cumulativity

In `twoThemes` the event `{0}` has two objects: `{0}`, its part of the object `{0, 1}` of the whole
event `{0, 1}`, and `{2}`, outside it. The relation is strictly incremental, but the quantized
object predicate true of `{0, 1}` and of `{2}` gives a verb phrase true of `{0}` and of `{0, 1}`.
It is not cumulative, since `{0}` and `{2}` would sum to a third object of `{0}`. -/

/-- The event `{0}` has the objects `{0}` and `{2}`. -/
def twoThemes : SetRel (Finset (Fin 3)) (Finset (Fin 2)) :=
  {p | p ∈ [(∅, ∅), ({0}, {0}), ({1}, {1}), ({0, 1}, {0, 1}), ({2}, {0})]}

instance : DecidablePred (· ∈ twoThemes) := fun _ ↦ by unfold twoThemes; infer_instance

theorem twoThemes_sinc : SINC twoThemes where
  ue x e h y hy := by
    revert h hy
    unfold ExistsUnique
    fin_cases x <;> fin_cases e <;> fin_cases y <;> decide
  uo e x h e' he' := by
    revert h he'
    simp only [ExistsUnique, SetRel.mem_inv]
    fin_cases x <;> fin_cases e <;> fin_cases e' <;> decide
  extended := ⟨{0, 1}, {0}, {0, 1}, {0}, by decide, by decide, by decide, by decide⟩

-- §3.3, after (54)
theorem not_qua_vp_twoThemes :
    QUA (· ∈ ({{0, 1}, {2}} : Finset (Finset (Fin 3)))) ∧
      ¬ QUA (VP twoThemes (· ∈ ({{0, 1}, {2}} : Finset (Finset (Fin 3))))) := by
  refine ⟨?_, fun h ↦ h (x := {0}) ⟨{2}, by decide, by decide⟩ (y := {0, 1})
    ⟨{0, 1}, by decide, by decide⟩ (by decide) (by decide : ({0} : Finset (Fin 2)) ⊆ {0, 1})⟩
  rintro x hx y hy hne hle
  simp only [Set.mem_ofPred_eq, Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
    first | exact hne rfl | exact absurd hle (by decide)

/-! ### Incrementality without telicity (§3.6)

An article has two paragraphs, read by the events `0`, `1` and `2`, the last two both reading the
second paragraph. A strict reading reads each paragraph of its object once, and *read* is the
closure of strict reading under sums, which is incremental but lets the reader go back. -/

namespace Reading

/-- Event `0` reads the first paragraph, and events `1` and `2` both read the second. -/
def paragraph (i : Fin 3) : Fin 2 := if i = 0 then 0 else 1

/-- An event is a strict reading of some paragraphs if it reads each of them exactly once. -/
def readOnce : SetRel (Finset (Fin 2)) (Finset (Fin 3)) :=
  {(x, e) | (∀ p, p ∈ x ↔ ∃ i ∈ e, paragraph i = p) ∧
    ∀ i ∈ e, ∀ j ∈ e, paragraph i = paragraph j → i = j}

instance : DecidablePred (· ∈ readOnce) := fun (x, e) ↦ by
  change Decidable ((∀ p, p ∈ x ↔ ∃ i ∈ e, paragraph i = p) ∧
    ∀ i ∈ e, ∀ j ∈ e, paragraph i = paragraph j → i = j)
  infer_instance

theorem readOnce_sinc : SINC readOnce where
  ue x e h y hy := by
    revert h hy
    unfold ExistsUnique
    fin_cases x <;> fin_cases e <;> fin_cases y <;> decide
  uo e x h e' he' := by
    revert h he'
    simp only [ExistsUnique, SetRel.mem_inv]
    fin_cases x <;> fin_cases e <;> fin_cases e' <;> decide
  extended := ⟨{0, 1}, {0}, {0, 1}, {0}, by decide, by decide, by decide, by decide⟩

/-- Reading is the closure of strict reading under sums. -/
def read : SetRel (Finset (Fin 2)) (Finset (Fin 3)) := supClosure readOnce

theorem read_inc : INC read := ⟨readOnce, readOnce_sinc, rfl⟩

-- *Read* is summative and the article has two readings, so it is not strictly incremental.
theorem not_sinc_read : ¬ SINC read := fun h ↦
  absurd ((h.gue_of_sum read_inc.sum).eq
    (subset_supClosure (by decide) : Finset.univ ~[read] {0, 1})
    (subset_supClosure (by decide) : Finset.univ ~[read] {0, 2})) (by decide)

/-- An event precedes another if all its times are earlier, neither being empty. -/
def precedes (a b : Finset (Fin 3)) : Prop := a.Nonempty ∧ b.Nonempty ∧ ∀ i ∈ a, ∀ j ∈ b, i < j

instance : DecidableRel precedes := fun _ _ ↦ by unfold precedes; infer_instance

instance : IsStrictOrder (Finset (Fin 3)) precedes where
  irrefl _ := fun ⟨⟨i, hi⟩, _, h⟩ ↦ lt_irrefl i (h i hi i hi)
  trans _ _ _ := fun ⟨ha, ⟨j, hj⟩, h₁⟩ ⟨_, hc, h₂⟩ ↦
    ⟨ha, hc, fun i hi k hk ↦ (h₁ i hi j hj).trans (h₂ j hj k hk)⟩

/-- *Read the article* is not telic, since the strict reading `{0, 1}` is a part of the reading
`{0, 1, 2}` that the re-reading `{2}` follows. -/
theorem not_isTelic_read : ¬ IsTelic precedes (Finset.univ ~[read] ·) := fun h ↦ by
  have h₁ : Finset.univ ~[read] {0, 1} := subset_supClosure (by decide)
  have h₂ : Finset.univ ~[read] {0, 2} := subset_supClosure (by decide)
  have hsum : Finset.univ ~[read] {0, 1, 2} := by
    have := read_inc.sum.sup h₁ h₂
    rwa [show ({0, 1} ⊔ {0, 2} : Finset (Fin 3)) = {0, 1, 2} from by decide, sup_idem] at this
  exact (h.isFinalPart (e' := {0, 1}) hsum h₁ (by decide)).not_precedes
    (e'' := {2}) (by decide) (by decide : precedes {0, 1} {2})

end Reading

/-! ### Telicity by expansion -/

section Expansion

variable [SemilatticeSup α] [SemilatticeSup β] (precedes : β → β → Prop) (θ : SetRel α β)

/-- A relation is expansive if the objects of temporally ordered events do not overlap. -/
def EXP : Prop := ∀ x y e e', x ~[θ] e → y ~[θ] e' → precedes e e' → ¬ Overlap x y

/-- A relation is strictly expansive incremental if it is expansive and maps to objects. -/
structure SEINC : Prop where
  exp : EXP precedes θ
  mo : MO θ

variable {precedes θ} [IsStrictOrder β precedes] (h : SEINC precedes θ)
  (h₀ : ∀ x e, x ~[θ] e → ¬ IsBot x) {x : α} {e e' : β}
include h h₀

theorem isInitialPart_of_seinc (hx : x ~[θ] e) (hx' : x ~[θ] e') (hle : e' ≤ e) :
    IsInitialPart precedes e' e :=
  isInitialPart_iff.mpr ⟨hle, fun e'' h'' hp ↦
    let ⟨y, hy, hθ⟩ := h.mo hx h''
    h.exp y x e'' e' hθ hx' hp ⟨y, h₀ y e'' hθ, le_rfl, hy⟩⟩

theorem isFinalPart_of_seinc (hx : x ~[θ] e) (hx' : x ~[θ] e') (hle : e' ≤ e) :
    IsFinalPart precedes e' e :=
  isInitialPart_iff.mpr ⟨hle, fun e'' h'' hp ↦
    let ⟨y, hy, hθ⟩ := h.mo hx h''
    h.exp x y e' e'' hx' hθ hp ⟨y, h₀ y e'' hθ, hy, le_rfl⟩⟩

theorem isTelic_of_seinc (x : α) : IsTelic precedes (x ~[θ] ·) :=
  fun _ _ hx hx' hle ↦
    ⟨isInitialPart_of_seinc h h₀ hx hx' hle, isFinalPart_of_seinc h h₀ hx hx' hle⟩

/-- The verb phrase of a quantized object under a strictly expansive incremental relation with
unique participants is telic, as *eat two apples* is. -/
theorem isTelic_vp_of_seinc (hUP : UP θ) {OBJ : α → Prop} (hOBJ : QUA OBJ) :
    IsTelic precedes (VP θ OBJ) := by
  rintro e e' ⟨x, hOx, hx⟩ ⟨x', hOx', hx'⟩ hle
  obtain ⟨x'', hx''le, hx''⟩ := h.mo hx hle
  obtain rfl := hUP.eq hx' (SetRel.mem_inv.1 hx'')
  obtain rfl : x' = x := by_contra fun hne ↦ hOBJ hOx' hOx hne hx''le
  exact ⟨isInitialPart_of_seinc h h₀ hx hx' hle, isFinalPart_of_seinc h h₀ hx hx' hle⟩

end Expansion

/-! ### Movement relations -/

section Movement

variable [SemilatticeSup α] [SemilatticeSup β] (adjα : α → α → Prop) (adjβ : β → β → Prop)
  (precedes : β → β → Prop) (isPath : α → Prop) (θ : SetRel α β)

/-- A relation has the adjacency property if two subevents of a movement are temporally
adjacent iff their paths are spatially adjacent. -/
def ADJ : Prop :=
  ∀ x e y z e' e'', x ~[θ] e → e' ≤ e → e'' ≤ e → y ≤ x → z ≤ x → y ~[θ] e' → z ~[θ] e'' →
    (adjβ e' e'' ↔ adjα y z)

/-- A strict movement relation has the adjacency property, maps to objects, and takes paths as
objects. -/
structure SMR : Prop where
  adj : ADJ adjα adjβ θ
  mo : MO θ
  path : ∀ x e, x ~[θ] e → isPath x

/-- The closure of a relation under sums of temporally ordered events. -/
inductive PrecedenceClosure (θ' : SetRel α β) : α → β → Prop where
  | base {x : α} {e : β} : x ~[θ'] e → PrecedenceClosure θ' x e
  | sum {x₁ x₂ : α} {e₁ e₂ : β} : PrecedenceClosure θ' x₁ e₁ → PrecedenceClosure θ' x₂ e₂ →
      precedes e₁ e₂ → PrecedenceClosure θ' (x₁ ⊔ x₂) (e₁ ⊔ e₂)

/-- A movement relation (71) is the closure of a strict movement relation under sums of
temporally ordered events. -/
def MR : Prop :=
  ∃ θ', SMR adjα adjβ isPath θ' ∧ ∀ x e, x ~[θ] e ↔ PrecedenceClosure precedes θ' x e

section

variable {adjα adjβ precedes isPath θ}

theorem mr_of_smr (h : SMR adjα adjβ isPath θ)
    (hClosed : ∀ x₁ x₂ e₁ e₂, x₁ ~[θ] e₁ → x₂ ~[θ] e₂ → precedes e₁ e₂ →
      (x₁ ⊔ x₂) ~[θ] (e₁ ⊔ e₂)) :
    MR adjα adjβ precedes isPath θ :=
  ⟨θ, h, fun _ _ ↦ ⟨.base, fun hcl ↦ by
    induction hcl with
    | base h => exact h
    | sum _ _ hp ih₁ ih₂ => exact hClosed _ _ _ _ ih₁ ih₂ hp⟩⟩

end

variable [IsStrictOrder β precedes]

/-- The subpaths of a movement adjacent to `y` are the paths of its initial parts. -/
def Source (y x : α) (e : β) : Prop :=
  ∀ x' e', x' ~[θ] e' → x' ≤ x → e' ≤ e → (adjα x' y ↔ IsInitialPart precedes e' e)

/-- The subpaths of a movement adjacent to `y` are the paths of its final parts. -/
def Goal (y x : α) (e : β) : Prop :=
  ∀ x' e', x' ~[θ] e' → x' ≤ x → e' ≤ e → (adjα x' y ↔ IsFinalPart precedes e' e)

variable {adjα adjβ precedes isPath θ}

/-- A movement with a specified source and goal is telic under mapping to objects and
uniqueness of participants, as *walk from the university to the capitol* is. -/
theorem isTelic_sourceGoal (hax : NoPartPrecedes precedes) (hMO : MO θ) (hUP : UP θ)
    (u v : α) :
    IsTelic precedes
      (fun e ↦ ∃ x, x ~[θ] e ∧ Source adjα precedes θ u x e ∧ Goal adjα precedes θ v x e) := by
  rintro e e' ⟨x, hx, hS, hG⟩ ⟨x', hx', hS', hG'⟩ hle
  obtain ⟨x'', hx''le, hx''⟩ := hMO hx hle
  obtain rfl := hUP.eq hx' (SetRel.mem_inv.1 hx'')
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
def Movement (L : List (Seg × Fin 7)) : SetRel (Finset Seg) (Finset (Fin 7)) :=
  {p | p ∈ support L}

instance (L : List (Seg × Fin 7)) : DecidablePred (· ∈ Movement L) := fun _ ↦ by
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
