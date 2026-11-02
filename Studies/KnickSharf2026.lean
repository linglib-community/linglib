module

public import Linglib.Data.Examples.KnickSharf2026
public import Linglib.Data.Examples.Readers
public import Linglib.Semantics.Aspect.Viewpoint
public import Mathlib.Order.UpperLower.CompleteLattice
public import Studies.Chierchia2006
public import Studies.KatzirSingh2015

/-!
# Knick and Sharf (2026): On focus and the perfect aspect

Knick and Sharf's perfect time span ends at the speech time and starts in a domain $t_r$. With
the imperfective beneath the perfect, the universal perfect [entails the simple
present](##universalPerfect_subset_simplePresent); with the perfective, the experiential perfect
does not, and only it [admits *but she's not anymore*](##completion_continuation). Focus on the
participle falls on the domain, whose alternatives [form a chain under
entailment](##isChain_range_universalPerfect), and covert *even* [selects the one reaching furthest
back](##evenEnrich_universalPerfect_eq_iff), so that the eventuality has held long. A domain
containing the speech time, as under broad focus, [makes the universal perfect the simple
present](##universalPerfect_eq_simplePresent), which as the simpler form [wins the competition
between them](##exists_goodAnswer_universalPerfect_iff).

## Implementation notes

* A sentence is the set of worlds in which it holds at the speech time, the present tense being
  evaluation there, so that entailment is inclusion; the worlds are the context set, and the
  paper's contextual entailment is inclusion too.
* A left boundary is a time point, where the paper's is an initial subinterval of the perfect
  time span within $t_r$, and a domain is a set of times; the paper's interval domains are
  `Set.Icc`.
* The imperfective properly includes the reference interval in the run time of an actual
  eventuality, `Aspect.ViewpointType.imperfective.denote`, not the modal `Aspect.IMPF`.
* Entailment in every model quantifies over predicates of intervals, the event domain in which
  every interval is a possible run time.
* The paper compares alternatives with disjoint, overlapping and nested domains; the three cases
  come to [one criterion](##universalPerfect_Icc_subset_iff), the latest time of the domain up to
  the speech time, so that the width of a domain plays no part of its own.
* The complexity of a competitor is the number of heads in its logical form, the simple present
  being the universal perfect with `PERF` deleted.

## References

* [knick-sharf-2026]
* [chierchia-2006]
* [katzir-singh-2015]
-/

@[expose] public section

namespace KnickSharf2026

open Aspect Function Set
open Event (τ)

variable {W T E : Type*} [LinearOrder T] [Event.TemporalTrace E T]

/-! ### The simple present and the two perfects -/

/-- The simple present (39a), `PRS IMPF`, holds where an eventuality of `V` runs properly through
the speech time `t`. -/
def simplePresent (V : W → E → Prop) (t : T) : Set W :=
  {w | (w, t) ∈ atPoint (ViewpointType.imperfective.denote V)}

/-- The universal perfect (39b), `PRS PERF IMPF`, holds where a perfect time span ending at the
speech time `t` and starting in the domain `D` lies properly within the run time of an
eventuality of `V`. -/
def universalPerfect (V : W → E → Prop) (D : Set T) (t : T) : Set W :=
  {w | (w, t) ∈ PERF ((·.fst) ⁻¹' D ∩ ViewpointType.imperfective.denote V ·)}

/-- The experiential perfect (29), `PRS PERF PRFV`, holds where such a span contains the run time
of an eventuality of `V`. -/
def experientialPerfect (V : W → E → Prop) (D : Set T) (t : T) : Set W :=
  {w | (w, t) ∈ PERF ((·.fst) ⁻¹' D ∩ PRFV V ·)}

variable {V : W → E → Prop} {D D₁ D₂ : Set T} {t : T} {w : W}

@[simp] theorem mem_simplePresent :
    w ∈ simplePresent V t ↔ ∃ e, NonemptyInterval.pure t < τ e ∧ V w e :=
  Iff.rfl

@[simp] theorem mem_universalPerfect : w ∈ universalPerfect V D t ↔
    ∃ x ∈ D, ∃ h : x ≤ t, ∃ e, (⟨(x, t), h⟩ : NonemptyInterval T) < τ e ∧ V w e :=
  mem_perf_inter_preimage_fst

@[simp] theorem mem_experientialPerfect : w ∈ experientialPerfect V D t ↔
    ∃ x ∈ D, ∃ h : x ≤ t, ∃ e, τ e ≤ (⟨(x, t), h⟩ : NonemptyInterval T) ∧ V w e :=
  mem_perf_inter_preimage_fst

/-- The universal perfect entails its simple present competitor, (39) and (41), whatever its
domain. -/
theorem universalPerfect_subset_simplePresent (V : W → E → Prop) (D : Set T) (t : T) :
    universalPerfect V D t ⊆ simplePresent V t := fun _ hw ↦
  let ⟨_, _, h, e, hlt, hV⟩ := mem_universalPerfect.1 hw
  ⟨e, hlt.trans_le' (NonemptyInterval.le_def.2 ⟨h, le_rfl⟩), hV⟩

-- (41), (42)
theorem universalPerfect_eq_simplePresent (h : t ∈ D) :
    universalPerfect V D t = simplePresent V t :=
  (universalPerfect_subset_simplePresent V D t).antisymm fun _ ⟨e, hlt, hV⟩ ↦
    mem_universalPerfect.2 ⟨t, h, le_rfl, e, hlt, hV⟩

-- (29), (30)
theorem not_experientialPerfect_subset_simplePresent [Nonempty W] {x : T} (hx : x ∈ D)
    (hxt : x < t) :
    ¬ ∀ V : W → NonemptyInterval T → Prop, experientialPerfect V D t ⊆ simplePresent V t :=
  fun h ↦ by
  obtain ⟨w⟩ := ‹Nonempty W›
  obtain ⟨_, hlt, rfl⟩ := h (fun _ e ↦ e = .pure x) <| (mem_experientialPerfect (w := w)).2
    ⟨x, hx, hxt.le, .pure x, NonemptyInterval.le_def.2 ⟨le_rfl, hxt.le⟩, rfl⟩
  exact hxt.not_ge (NonemptyInterval.le_def.1 hlt.le).2

/-! ### The focus alternatives -/

-- a span lies properly within its extension to a later right boundary
private theorem lt_extend {x t t' : T} (hxt : x ≤ t) (ht' : t < t') :
    (⟨(x, t), hxt⟩ : NonemptyInterval T) < ⟨(x, t'), hxt.trans ht'.le⟩ :=
  lt_iff_le_not_ge.2 ⟨NonemptyInterval.le_def.2 ⟨le_rfl, ht'.le⟩,
    fun h ↦ (NonemptyInterval.le_def.1 h).2.not_gt ht'⟩

-- §4.3.1, §4.3.2: an eventuality containing a longer span contains a shorter one
theorem universalPerfect_mono (h : lowerClosure (D₁ ∩ Iic t) ≤ lowerClosure (D₂ ∩ Iic t)) :
    universalPerfect V D₁ t ⊆ universalPerfect V D₂ t := fun _ hw ↦
  let ⟨_, hx, hxt, e, hlt, hV⟩ := mem_universalPerfect.1 hw
  let ⟨y, ⟨hy, hyt⟩, hxy⟩ := h (subset_lowerClosure ⟨hx, hxt⟩)
  mem_universalPerfect.2
    ⟨y, hy, hyt, e, hlt.trans_le' (NonemptyInterval.le_def.2 ⟨hxy, le_rfl⟩), hV⟩

-- §4.3
theorem universalPerfect_subset_iff [NoMaxOrder T] [Nonempty W] :
    (∀ V : W → NonemptyInterval T → Prop, universalPerfect V D₁ t ⊆ universalPerfect V D₂ t) ↔
      lowerClosure (D₁ ∩ Iic t) ≤ lowerClosure (D₂ ∩ Iic t) := by
  refine ⟨fun h ↦ lowerClosure_le.2 fun x ⟨hx, hxt⟩ ↦ ?_, fun h _ ↦ universalPerfect_mono h⟩
  obtain ⟨w⟩ := ‹Nonempty W›
  obtain ⟨t', ht'⟩ := exists_gt t
  obtain ⟨y, hy, hyt, _, hlt, rfl⟩ := mem_universalPerfect.1 <|
    h (fun _ e ↦ e = ⟨(x, t'), hxt.trans ht'.le⟩) <| (mem_universalPerfect (w := w)).2
      ⟨x, hx, hxt, _, lt_extend hxt ht', rfl⟩
  exact ⟨y, ⟨hy, hyt⟩, (NonemptyInterval.le_def.1 hlt.le).1⟩

/-- Any two of the alternatives (32) are equivalent or one entails the other: ordered by
entailment in every model, they form a chain. -/
theorem isChain_range_universalPerfect (t : T) :
    IsChain (· ≤ ·) (range fun (D : Set T) (V : W → E → Prop) ↦ universalPerfect V D t) := by
  rintro _ ⟨D₁, rfl⟩ _ ⟨D₂, rfl⟩ -
  exact (le_total (lowerClosure (D₁ ∩ Iic t)) (lowerClosure (D₂ ∩ Iic t))).imp
    (fun h _ ↦ universalPerfect_mono h) (fun h _ ↦ universalPerfect_mono h)

-- §4.3.1–§4.3.3, footnote 7
theorem universalPerfect_Icc_subset_iff [NoMaxOrder T] [Nonempty W] {a₁ b₁ a₂ b₂ : T}
    (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂) (hb₁ : b₁ ≤ t) (hb₂ : b₂ ≤ t) :
    (∀ V : W → NonemptyInterval T → Prop,
      universalPerfect V (Icc a₁ b₁) t ⊆ universalPerfect V (Icc a₂ b₂) t) ↔ b₁ ≤ b₂ := by
  rw [universalPerfect_subset_iff, lowerClosure_le]
  refine ⟨fun h ↦ ?_, fun h x ⟨⟨_, hx⟩, _⟩ ↦ ⟨b₂, ⟨right_mem_Icc.2 h₂, hb₂⟩, hx.trans h⟩⟩
  obtain ⟨y, ⟨⟨_, hy⟩, _⟩, hby⟩ := h ⟨right_mem_Icc.2 h₁, hb₁⟩
  exact hby.trans hy

-- (40)
theorem simplePresent_subset_universalPerfect_iff [NoMaxOrder T] [Nonempty W] :
    (∀ V : W → NonemptyInterval T → Prop, simplePresent V t ⊆ universalPerfect V D t) ↔
      t ∈ D := by
  simp_rw [← universalPerfect_eq_simplePresent (mem_singleton t), universalPerfect_subset_iff,
    lowerClosure_le, singleton_inter_of_mem self_mem_Iic, singleton_subset_iff]
  exact ⟨fun ⟨y, ⟨hy, hyt⟩, hty⟩ ↦ le_antisymm hyt hty ▸ hy, fun h ↦ ⟨t, ⟨h, le_rfl⟩, le_rfl⟩⟩

/-! ### The length implication -/

open Chierchia2006 in
/-- Covert *even* over the alternatives (38) leaves the universal perfect over `D` intact in every
model exactly when `D` reaches furthest back, every time of it up to the speech time lying at or
before such a time of each alternative domain: the length implication. -/
theorem evenEnrich_universalPerfect_eq_iff [NoMaxOrder T] [Nonempty W] {𝒟 : Set (Set T)} :
    (∀ V : W → NonemptyInterval T → Prop,
      evenEnrich ((universalPerfect V · t) '' 𝒟) (universalPerfect V D t) =
        universalPerfect V D t) ↔
      ∀ D' ∈ 𝒟, lowerClosure (D ∩ Iic t) ≤ lowerClosure (D' ∩ Iic t) := by
  refine ⟨fun h D' hD' ↦ universalPerfect_subset_iff.1 fun V _ hw ↦
    ((h V).ge hw).2 _ ⟨D', hD', rfl⟩ hw, fun h V ↦ Set.ext fun _ ↦ ⟨And.left, fun hw ↦ ⟨hw, ?_⟩⟩⟩
  rintro _ ⟨D', hD', rfl⟩
  exact universalPerfect_mono (h D' hD')

/-! ### Competition with the simple present -/

/-- The competitors of (39) and (41). -/
inductive Competitor
  | simplePresent
  | universalPerfect
  deriving DecidableEq

/-- What a competitor means at the speech time `t`, the universal perfect over `D`. -/
def Competitor.meaning (V : W → E → Prop) (D : Set T) (t : T) : Competitor → Set W
  | .simplePresent => KnickSharf2026.simplePresent V t
  | .universalPerfect => KnickSharf2026.universalPerfect V D t

/-- The heads of the logical form, `PRS IMPF` and `PRS PERF IMPF` (footnote 10). -/
def Competitor.heads : Competitor → ℕ
  | .simplePresent => 2
  | .universalPerfect => 3

/-- The competition (43) between the simple present and the universal perfect over `D`, the
question being the competitors themselves. -/
abbrev competition (V : W → E → Prop) (D : Set T) (t : T) :
    KatzirSingh2015.Scenario W Competitor Competitor where
  meaning := Competitor.meaning V D t
  complexity := Competitor.heads
  context := univ
  question := Competitor.meaning V D t

theorem competition_relevant (c : Competitor) : (competition V D t).Relevant c :=
  fun _ _ _ _ h ↦ h c

-- (43), (44)
theorem goodAnswer_universalPerfect_iff :
    (competition V D t).GoodAnswer .universalPerfect w ↔
      w ∈ universalPerfect V D t ∧ ¬ simplePresent V t ⊆ universalPerfect V D t := by
  refine ⟨fun h ↦ ⟨h.1, fun hs ↦ ?_⟩, fun ⟨hw, hs⟩ ↦ ⟨hw, competition_relevant _, ?_⟩⟩
  · exact (competition V D t).not_goodAnswer_of_simpler (u := .universalPerfect)
      (v := .simplePresent)
      (by decide : Competitor.heads .simplePresent < Competitor.heads .universalPerfect) hs
      (universalPerfect_subset_simplePresent V D t h.1) (competition_relevant _) h
  · rintro ⟨_ | _, hb, -, -⟩
    · exact hs hb.1.2
    · exact (competition V D t).better_irrefl _ hb

/-- The universal perfect survives its competition with the simple present in some model exactly
when its domain has a time before the speech time but not the speech time itself, as under
narrow focus and not under broad focus. -/
theorem exists_goodAnswer_universalPerfect_iff [NoMaxOrder T] [Nontrivial W] :
    (∃ (V : W → NonemptyInterval T → Prop) (w : W),
      (competition V D t).GoodAnswer .universalPerfect w) ↔ t ∉ D ∧ (D ∩ Iic t).Nonempty := by
  simp_rw [goodAnswer_universalPerfect_iff]
  refine ⟨fun ⟨V, w, hw, hs⟩ ↦ ⟨fun ht ↦ hs (universalPerfect_eq_simplePresent ht).ge, ?_⟩, ?_⟩
  · obtain ⟨x, hx, hxt, -⟩ := mem_universalPerfect.1 hw
    exact ⟨x, hx, hxt⟩
  -- a world verifying the universal perfect, beside the simple present's countermodel
  rintro ⟨ht, x, hx, hxt⟩
  classical
  obtain ⟨V, hV⟩ := not_forall.1 (mt (simplePresent_subset_universalPerfect_iff (W := W)).1 ht)
  obtain ⟨w₂, hsp, hu⟩ := not_subset.1 hV
  obtain ⟨w₁, hne⟩ := exists_ne w₂
  obtain ⟨t', ht'⟩ := exists_gt t
  refine ⟨update V w₁ (· = ⟨(x, t'), hxt.trans ht'.le⟩), w₁,
    mem_universalPerfect.2 ⟨x, hx, hxt, _, lt_extend hxt ht', by simp⟩, fun hs ↦ hu ?_⟩
  simpa only [mem_universalPerfect, update_of_ne hne.symm] using
    hs (a := w₂) (by simpa only [mem_simplePresent, update_of_ne hne.symm] using hsp)

/-! ### The completion continuation -/

/-- The universal and the experiential reading of the perfect. -/
inductive Reading
  | universal
  | experiential
  deriving DecidableEq

/-- The perfect under a reading. -/
def Reading.perfect : Reading → (W → E → Prop) → Set T → T → Set W
  | .universal => universalPerfect
  | .experiential => experientialPerfect

/-- A reading entails the simple present when in every model, over every domain, the
eventuality holds at the speech time wherever the perfect does. -/
def Reading.EntailsPresent (W T : Type*) [LinearOrder T] (r : Reading) : Prop :=
  ∀ (V : W → NonemptyInterval T → Prop) D t, r.perfect V D t ⊆ simplePresent V t

theorem Reading.entailsPresent_iff [Nonempty W] [Nontrivial T] {r : Reading} :
    r.EntailsPresent W T ↔ r = .universal := by
  cases r
  · exact iff_of_true (fun V D t ↦ universalPerfect_subset_simplePresent V D t) rfl
  · obtain ⟨x, t, hxt⟩ := exists_pair_lt T
    exact iff_of_false
      (fun h ↦ not_experientialPerfect_subset_simplePresent (W := W) (mem_univ x) hxt (h · univ t))
      Reading.noConfusion

instance [Nonempty W] [Nontrivial T] (r : Reading) : Decidable (r.EntailsPresent W T) :=
  decidable_of_iff _ Reading.entailsPresent_iff.symm

/-- The reading the paper assigns a row. -/
def reading (e : Datum) : Option Reading :=
  e.parse? "reading" [("universal", .universal), ("experiential", .experiential)]

/-- The continuation *but she's not anymore* is felicitous on exactly the rows whose reading does
not entail the simple present: the experiential perfects (6), (8a) and (12), and none of the
universal perfects (5), (8b) and (10). -/
theorem completion_continuation :
    Datum.Checks reading (fun r ↦ .ofProp ¬ r.EntailsPresent Unit ℤ) Examples.all 6 := by
  decide

end KnickSharf2026
