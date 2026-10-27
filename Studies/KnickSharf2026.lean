module

public import Linglib.Semantics.Aspect.Viewpoint
public import Linglib.Semantics.Tense.Quantificational

/-!
# Knick and Sharf (2026): On focus and the perfect aspect

Knick and Sharf compose viewpoint aspect, the perfect and tense: an event predicate becomes an
interval property under the imperfective or perfective, a set of world-time points under the
perfect, and a proposition under a tense. The U-perfect, whose perfect time span has its
left boundary in a domain `tᵣ`, entails its simple present competitor whatever the domain and is
equivalent to it under broad focus, where the domain is unrestricted, which is why competition
rules it out there. Among the focus alternatives, a domain further in the past is stronger.

## Implementation notes

* A left boundary is a time point, where the paper's left boundary is a subinterval of `tᵣ`; the
  paper's `PERF_XN` is the perfect over the spans whose left boundary lies in `tᵣ`.
* `later_lb_stronger_prfv`, the reversed ordering under the perfective, is not drawn in the paper.

## References

* [knick-sharf-2026]
-/

@[expose] public section

namespace KnickSharf2026

open ModalLogic Kaplan
open scoped Denotes

open Aspect
open Event (τ)

variable {W T E : Type*} [LinearOrder T] [Event.TemporalTrace E T]

/-! ### Tense -/

/-- The present tense evaluates a set of world-time points at the speech time `tc` in the world
`w`. -/
def evalPres (p : Set (Index W T)) (tc : T) (w : W) : Prop :=
  ⟨w, tc⟩ ∈ p

/-- The past tense evaluates a set of world-time points at some time before the speech time `tc`,
the quantificational past of `Semantics/Tense/Quantificational.lean`. -/
def evalPast (p : Set (Index W T)) (tc : T) (w : W) : Prop :=
  ◇[Tense.toSetRel ⟦Tense.past⟧] (fun t ↦ (w, t) ∈ p) tc

/-- The future tense evaluates a set of world-time points at some time after the speech time
`tc`. -/
def evalFut (p : Set (Index W T)) (tc : T) (w : W) : Prop :=
  ◇[Tense.toSetRel ⟦Tense.future⟧] (fun t ↦ (w, t) ∈ p) tc

/-! ### Composed forms -/

/-- The simple present is `PRES(atPoint(IMPF(V)))`, so *John runs* holds at speech time when
some event `e` with `[tc, tc] ⊂ τ(e)` satisfies `V`. -/
def simplePresent (V : W → E → Prop) (tc : T) (w : W) : Prop :=
  evalPres (atPoint (IMPF V)) tc w

/-- The simple past is `PAST(atPoint(PRFV(V)))`, so *John ran* holds when some `t < tc` and some
event `e` with `τ(e) ⊆ [t, t]` satisfy `V`. -/
def simplePast (V : W → E → Prop) (tc : T) (w : W) : Prop :=
  evalPast (atPoint (PRFV V)) tc w

/-- The present perfect progressive is `PRES(PERF(IMPF(V)))`, so *John has been running* holds
at `tc` when some perfect time span right-bounded by `tc` satisfies `IMPF(V)`. -/
def presPerfProg (V : W → E → Prop) (tc : T) (w : W) : Prop :=
  evalPres (PERF (IMPF V)) tc w

/-- The present perfect simple is `PRES(PERF(PRFV(V)))`, so *John has run* holds at `tc` when
some perfect time span right-bounded by `tc` satisfies `PRFV(V)`. -/
def presPerfSimple (V : W → E → Prop) (tc : T) (w : W) : Prop :=
  evalPres (PERF (PRFV V)) tc w

/-- The present perfect progressive with Extended Now is `PRES(PERF_XN(IMPF(V), tᵣ))`, the
U-perfect reading of [knick-sharf-2026]; *John has been running since Monday* restricts the left
boundary of the perfect time span to `tᵣ`. -/
def presPerfProgXN (V : W → E → Prop) (tᵣ : Set T) (tc : T) (w : W) : Prop :=
  evalPres (PERF ((·.fst) ⁻¹' tᵣ ∩ IMPF V ·)) tc w

/-- The past perfect progressive is `PAST(PERF(IMPF(V)))`, so *John had been running* holds when
some `t < tc` satisfies `PERF(IMPF(V))`. -/
def pastPerfProg (V : W → E → Prop) (tc : T) (w : W) : Prop :=
  evalPast (PERF (IMPF V)) tc w

/-! ### Unfolding -/

theorem simplePresent_unfold (V : W → E → Prop) (tc : T) (w : W) :
    simplePresent V tc w ↔
    ∃ e : E, NonemptyInterval.pure tc < τ e ∧ V w e := by
  rfl

-- (39b)
theorem presPerfProgXN_iff (V : W → E → Prop) (tᵣ : Set T) (tc : T) (w : W) :
    presPerfProgXN V tᵣ tc w ↔ ∃ pts ∈ IMPF V w, pts.fst ∈ tᵣ ∧ pts.snd = tc :=
  ⟨fun ⟨pts, ⟨h₁, h₂⟩, h₃⟩ ↦ ⟨pts, h₂, h₁, h₃⟩, fun ⟨pts, h₂, h₁, h₃⟩ ↦ ⟨pts, ⟨h₁, h₂⟩, h₃⟩⟩

/-! ### Results -/

/-- The U-perfect (39b) entails its simple present competitor (39a) whatever the domain `tᵣ`. -/
theorem u_perf_entails_simple_present (V : W → E → Prop) (tᵣ : Set T) (tc : T) (w : W) :
    presPerfProgXN V tᵣ tc w → simplePresent V tc w := fun h ↦
  let ⟨pts, ⟨_, e, hlt, hV⟩, hRB⟩ := mem_perf.1 h
  ⟨e, lt_of_le_of_lt (NonemptyInterval.le_def.2 ⟨hRB ▸ pts.fst_le_snd, hRB.ge⟩) hlt, hV⟩

/-- Under broad focus, where the domain `tᵣ` is the whole line, the U-perfect is equivalent to
the simple present, the equivalence by which competition rules it out; the converse direction
takes the point `tc` as the perfect time span. -/
theorem broad_focus_equiv (V : W → E → Prop) (tc : T) (w : W) :
    presPerfProgXN V Set.univ tc w ↔ simplePresent V tc w :=
  ⟨u_perf_entails_simple_present V Set.univ tc w, fun h ↦ ⟨.pure tc, ⟨Set.mem_univ _, h⟩, rfl⟩⟩

/-- Under the imperfective an earlier left boundary is stronger, the ordering of the focus
alternatives in (33) and (35). -/
theorem earlier_lb_stronger_impf (V : W → E → Prop) (tLB₁ tLB₂ : T) (tc : T) (w : W)
    (h : tLB₁ < tLB₂) (htc : tLB₂ ≤ tc) :
    presPerfProgXN V {tLB₁} tc w → presPerfProgXN V {tLB₂} tc w := fun hp ↦
  let ⟨_, ⟨hLB, e, hlt, hV⟩, hRB⟩ := mem_perf.1 hp
  ⟨⟨(tLB₂, tc), htc⟩, ⟨rfl, e, lt_of_le_of_lt
    (NonemptyInterval.le_def.2 ⟨(Set.mem_singleton_iff.1 hLB).le.trans h.le, hRB.ge⟩) hlt, hV⟩, rfl⟩

-- (28)
theorem later_lb_stronger_prfv (V : W → E → Prop) (tLB₁ tLB₂ : T) (tc : T) (w : W)
    (h : tLB₁ < tLB₂) :
    ⟨w, tc⟩ ∈ PERF ({pts | pts.fst = tLB₂} ∩ PRFV V ·) →
      ⟨w, tc⟩ ∈ PERF ({pts | pts.fst = tLB₁} ∩ PRFV V ·) := fun hp ↦
  let ⟨pts, ⟨hLB, e, hle, hV⟩, hRB⟩ := mem_perf.1 hp
  have hLB : pts.fst = tLB₂ := hLB
  ⟨⟨(tLB₁, tc), (h.le.trans hLB.ge).trans (hRB ▸ pts.fst_le_snd)⟩,
    ⟨rfl, e, hle.trans (NonemptyInterval.le_def.2 ⟨h.le.trans hLB.ge, hRB.le⟩), hV⟩, rfl⟩

/-- The imperfective ordering is strict, as the state `s''` of (33) shows. -/
theorem earlier_lb_not_weaker_impf :
    ¬ ∀ (V : Unit → NonemptyInterval ℤ → Prop) (tLB₁ tLB₂ tc : ℤ) (w : Unit),
      tLB₁ < tLB₂ → presPerfProgXN V {tLB₂} tc w → presPerfProgXN V {tLB₁} tc w := fun hall ↦ by
  let e₀ : NonemptyInterval ℤ := ⟨(1, 5), by omega⟩
  have prem : presPerfProgXN (fun _ e ↦ e = e₀) {2} 4 () :=
    ⟨⟨(2, 4), by omega⟩, ⟨rfl, e₀, by dsimp only [e₀]; decide, rfl⟩, rfl⟩
  obtain ⟨pts, ⟨hLB, e, hlt, rfl⟩, -⟩ := mem_perf.1 (hall _ 0 2 4 () (by omega) prem)
  have h₁ := (NonemptyInterval.le_def.1 hlt.le).1
  rw [show pts.fst = 0 from hLB] at h₁
  simp [e₀] at h₁

end KnickSharf2026
