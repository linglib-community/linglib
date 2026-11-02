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
present](##uPerfect_subset_simplePresent); with the perfective, the experiential perfect does not,
and only it [admits *but she's not anymore*](##completion_continuation). Focus on the participle
falls on the domain, whose alternatives [form a chain under entailment](##isChain_range_uPerfect),
and covert *even* [selects the one reaching furthest back](##evenEnrich_uPerfect_eq_iff), so that
the eventuality has held long. A domain containing the speech time, as under broad focus, [makes
the universal perfect the simple present](##uPerfect_eq_simplePresent), which as the simpler form
[wins the competition between them](##exists_goodAnswer_uPerfect_iff).

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
  come to [one criterion](##uPerfect_Icc_subset_iff), the latest time of the domain up to the
  speech time, so that the width of a domain plays no part of its own.
* The complexity of a competitor is the number of heads in its logical form, the simple present
  being the universal perfect with `PERF` deleted.

## References

* [knick-sharf-2026]
* [chierchia-2006]
* [katzir-singh-2015]
-/

@[expose] public section

namespace KnickSharf2026

open Aspect Set
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
def uPerfect (V : W → E → Prop) (D : Set T) (t : T) : Set W :=
  {w | (w, t) ∈ PERF ((·.fst) ⁻¹' D ∩ ViewpointType.imperfective.denote V ·)}

/-- The experiential perfect (29), `PRS PERF PRFV`, holds where such a span contains the run time
of an eventuality of `V`. -/
def ePerfect (V : W → E → Prop) (D : Set T) (t : T) : Set W :=
  {w | (w, t) ∈ PERF ((·.fst) ⁻¹' D ∩ PRFV V ·)}

variable {V : W → E → Prop} {D D₁ D₂ : Set T} {t : T}

/-- The universal perfect entails its simple present competitor, (39) and (41), whatever its
domain. -/
theorem uPerfect_subset_simplePresent (V : W → E → Prop) (D : Set T) (t : T) :
    uPerfect V D t ⊆ simplePresent V t := fun _ ⟨i, ⟨_, e, hlt, hV⟩, hi⟩ ↦
  ⟨e, lt_of_le_of_lt (NonemptyInterval.le_def.2 ⟨i.fst_le_snd.trans hi.le, hi.ge⟩) hlt, hV⟩

-- (41), (42)
theorem uPerfect_eq_simplePresent (h : t ∈ D) : uPerfect V D t = simplePresent V t :=
  (uPerfect_subset_simplePresent V D t).antisymm fun _ hw ↦ ⟨.pure t, ⟨h, hw⟩, rfl⟩

-- (29), (30)
theorem not_ePerfect_subset_simplePresent [Nonempty W] {x : T} (hx : x ∈ D) (hxt : x < t) :
    ¬ ∀ V : W → NonemptyInterval T → Prop, ePerfect V D t ⊆ simplePresent V t := fun h ↦ by
  obtain ⟨w⟩ := ‹Nonempty W›
  obtain ⟨_, hlt, rfl⟩ := h (fun _ e ↦ e = .pure x) (a := w)
    ⟨⟨(x, t), hxt.le⟩, ⟨hx, .pure x, NonemptyInterval.le_def.2 ⟨le_rfl, hxt.le⟩, rfl⟩, rfl⟩
  exact hxt.not_ge (NonemptyInterval.le_def.1 hlt.le).2

/-! ### The focus alternatives -/

-- a span lies properly within its extension to a later right boundary
private theorem lt_extend {x t t' : T} (hxt : x ≤ t) (ht' : t < t') :
    (⟨(x, t), hxt⟩ : NonemptyInterval T) < ⟨(x, t'), hxt.trans ht'.le⟩ :=
  lt_iff_le_not_ge.2 ⟨NonemptyInterval.le_def.2 ⟨le_rfl, ht'.le⟩,
    fun h ↦ (NonemptyInterval.le_def.1 h).2.not_gt ht'⟩

-- §4.3.1, §4.3.2: an eventuality containing a longer span contains a shorter one
theorem uPerfect_mono (h : lowerClosure (D₁ ∩ Iic t) ≤ lowerClosure (D₂ ∩ Iic t)) :
    uPerfect V D₁ t ⊆ uPerfect V D₂ t := fun _ ⟨i, ⟨hD, e, hlt, hV⟩, hi⟩ ↦
  let ⟨y, ⟨hy, hyt⟩, hxy⟩ := h (subset_lowerClosure ⟨hD, i.fst_le_snd.trans hi.le⟩)
  ⟨⟨(y, t), hyt⟩, ⟨hy, e, lt_of_le_of_lt (NonemptyInterval.le_def.2 ⟨hxy, hi.ge⟩) hlt, hV⟩, rfl⟩

-- §4.3
theorem uPerfect_subset_iff [NoMaxOrder T] [Nonempty W] :
    (∀ V : W → NonemptyInterval T → Prop, uPerfect V D₁ t ⊆ uPerfect V D₂ t) ↔
      lowerClosure (D₁ ∩ Iic t) ≤ lowerClosure (D₂ ∩ Iic t) := by
  refine ⟨fun h ↦ lowerClosure_le.2 fun x ⟨hx, hxt⟩ ↦ ?_, fun h _ ↦ uPerfect_mono h⟩
  obtain ⟨w⟩ := ‹Nonempty W›
  obtain ⟨t', ht'⟩ := exists_gt t
  obtain ⟨i, ⟨hy, _, hlt, rfl⟩, hi⟩ := h (fun _ e ↦ e = ⟨(x, t'), hxt.trans ht'.le⟩) (a := w)
    ⟨⟨(x, t), hxt⟩, ⟨hx, _, lt_extend hxt ht', rfl⟩, rfl⟩
  exact ⟨i.fst, ⟨hy, i.fst_le_snd.trans hi.le⟩, (NonemptyInterval.le_def.1 hlt.le).1⟩

/-- Any two of the alternatives (32) are equivalent or one entails the other: ordered by
entailment in every model, they form a chain. -/
theorem isChain_range_uPerfect (t : T) :
    IsChain (· ≤ ·) (range fun (D : Set T) (V : W → E → Prop) ↦ uPerfect V D t) := by
  rintro _ ⟨D₁, rfl⟩ _ ⟨D₂, rfl⟩ -
  exact (le_total (lowerClosure (D₁ ∩ Iic t)) (lowerClosure (D₂ ∩ Iic t))).imp
    (fun h _ ↦ uPerfect_mono h) (fun h _ ↦ uPerfect_mono h)

-- §4.3.1–§4.3.3, footnote 7
theorem uPerfect_Icc_subset_iff [NoMaxOrder T] [Nonempty W] {a₁ b₁ a₂ b₂ : T} (h₁ : a₁ ≤ b₁)
    (h₂ : a₂ ≤ b₂) (hb₁ : b₁ ≤ t) (hb₂ : b₂ ≤ t) :
    (∀ V : W → NonemptyInterval T → Prop, uPerfect V (Icc a₁ b₁) t ⊆ uPerfect V (Icc a₂ b₂) t) ↔
      b₁ ≤ b₂ := by
  rw [uPerfect_subset_iff, lowerClosure_le]
  refine ⟨fun h ↦ ?_, fun h x ⟨⟨_, hx⟩, _⟩ ↦ ⟨b₂, ⟨right_mem_Icc.2 h₂, hb₂⟩, hx.trans h⟩⟩
  obtain ⟨y, ⟨⟨_, hy⟩, _⟩, hby⟩ := h ⟨right_mem_Icc.2 h₁, hb₁⟩
  exact hby.trans hy

-- (40)
theorem simplePresent_subset_uPerfect_iff [NoMaxOrder T] [Nonempty W] :
    (∀ V : W → NonemptyInterval T → Prop, simplePresent V t ⊆ uPerfect V D t) ↔ t ∈ D := by
  simp_rw [← uPerfect_eq_simplePresent (mem_singleton t), uPerfect_subset_iff, lowerClosure_le,
    singleton_inter_of_mem self_mem_Iic, singleton_subset_iff]
  exact ⟨fun ⟨y, ⟨hy, hyt⟩, hty⟩ ↦ le_antisymm hyt hty ▸ hy, fun h ↦ ⟨t, ⟨h, le_rfl⟩, le_rfl⟩⟩

/-! ### The length implication -/

open Chierchia2006 in
/-- Covert *even* over the alternatives (38) leaves the universal perfect over `D` intact in every
model exactly when `D` reaches furthest back, every time of it up to the speech time lying at or
before such a time of each alternative domain: the length implication. -/
theorem evenEnrich_uPerfect_eq_iff [NoMaxOrder T] [Nonempty W] {𝒟 : Set (Set T)} :
    (∀ V : W → NonemptyInterval T → Prop,
      evenEnrich ((uPerfect V · t) '' 𝒟) (uPerfect V D t) = uPerfect V D t) ↔
      ∀ D' ∈ 𝒟, lowerClosure (D ∩ Iic t) ≤ lowerClosure (D' ∩ Iic t) := by
  refine ⟨fun h D' hD' ↦ uPerfect_subset_iff.1 fun V _ hw ↦ ((h V).ge hw).2 _ ⟨D', hD', rfl⟩ hw,
    fun h V ↦ Set.ext fun _ ↦ ⟨And.left, fun hw ↦ ⟨hw, ?_⟩⟩⟩
  rintro _ ⟨D', hD', rfl⟩
  exact uPerfect_mono (h D' hD')

/-! ### Competition with the simple present -/

/-- The competitors of (39) and (41). -/
inductive Competitor
  | simplePresent
  | uPerfect
  deriving DecidableEq

/-- What a competitor means at the speech time `t`, the universal perfect over `D`. -/
def Competitor.meaning (V : W → E → Prop) (D : Set T) (t : T) : Competitor → Set W
  | .simplePresent => KnickSharf2026.simplePresent V t
  | .uPerfect => KnickSharf2026.uPerfect V D t

/-- The heads of the logical form, `PRS IMPF` and `PRS PERF IMPF` (footnote 10). -/
def Competitor.heads : Competitor → ℕ
  | .simplePresent => 2
  | .uPerfect => 3

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
theorem goodAnswer_uPerfect_iff {w : W} :
    (competition V D t).GoodAnswer .uPerfect w ↔
      w ∈ uPerfect V D t ∧ ¬ simplePresent V t ⊆ uPerfect V D t := by
  refine ⟨fun h ↦ ⟨h.1, fun hs ↦ ?_⟩, fun ⟨hw, hs⟩ ↦ ⟨hw, competition_relevant _, ?_⟩⟩
  · exact (competition V D t).not_goodAnswer_of_simpler (u := .uPerfect) (v := .simplePresent)
      (by decide : Competitor.heads .simplePresent < Competitor.heads .uPerfect) hs
      (uPerfect_subset_simplePresent V D t h.1) (competition_relevant _) h
  · rintro ⟨_ | _, hb, -, -⟩
    · exact hs hb.1.2
    · exact (competition V D t).better_irrefl _ hb

/-- The universal perfect survives its competition with the simple present in some model exactly
when its domain has a time before the speech time but not the speech time itself, as under
narrow focus and not under broad focus. -/
theorem exists_goodAnswer_uPerfect_iff [NoMaxOrder T] [Nontrivial W] :
    (∃ (V : W → NonemptyInterval T → Prop) (w : W), (competition V D t).GoodAnswer .uPerfect w) ↔
      t ∉ D ∧ (D ∩ Iic t).Nonempty := by
  simp_rw [goodAnswer_uPerfect_iff]
  refine ⟨fun ⟨V, w, ⟨i, ⟨hD, _⟩, hi⟩, hs⟩ ↦
    ⟨fun ht ↦ hs (uPerfect_eq_simplePresent ht).ge, i.fst, hD, i.fst_le_snd.trans hi.le⟩, ?_⟩
  rintro ⟨ht, x, hx, hxt⟩
  obtain ⟨w₁, w₂, hne⟩ := exists_pair_ne W
  obtain ⟨t', ht'⟩ := exists_gt t
  let e₁ : NonemptyInterval T := ⟨(x, t'), hxt.trans ht'.le⟩
  let e₂ : NonemptyInterval T := ⟨(t, t'), ht'.le⟩
  refine ⟨fun w e ↦ w = w₁ ∧ e = e₁ ∨ w ≠ w₁ ∧ e = e₂, w₁, ?_, fun hs ↦ ?_⟩
  · exact ⟨⟨(x, t), hxt⟩, ⟨hx, e₁, lt_extend hxt ht', .inl ⟨rfl, rfl⟩⟩, rfl⟩
  · obtain ⟨i, ⟨hD, e, hlt, he⟩, hi⟩ :=
      hs (a := w₂) ⟨e₂, lt_extend le_rfl ht', .inr ⟨hne.symm, rfl⟩⟩
    obtain ⟨hw, -⟩ | ⟨-, rfl⟩ := he
    · exact hne.symm hw
    · exact ht ((le_antisymm (i.fst_le_snd.trans hi.le) (NonemptyInterval.le_def.1 hlt.le).1 :
        i.fst = t) ▸ hD)

/-! ### The completion continuation -/

/-- The universal and the experiential reading of the perfect. -/
inductive Reading
  | universal
  | experiential
  deriving DecidableEq

/-- The perfect under a reading. -/
def Reading.perfect : Reading → (W → E → Prop) → Set T → T → Set W
  | .universal => uPerfect
  | .experiential => ePerfect

/-- A reading entails the simple present when in every model, over every domain, the
eventuality holds at the speech time wherever the perfect does. -/
def Reading.EntailsPresent (W T : Type*) [LinearOrder T] (r : Reading) : Prop :=
  ∀ (V : W → NonemptyInterval T → Prop) D t, r.perfect V D t ⊆ simplePresent V t

theorem Reading.entailsPresent_iff [Nonempty W] [Nontrivial T] {r : Reading} :
    r.EntailsPresent W T ↔ r = .universal := by
  cases r
  · exact iff_of_true (fun V D t ↦ uPerfect_subset_simplePresent V D t) rfl
  · obtain ⟨x, t, hxt⟩ := exists_pair_lt T
    exact iff_of_false (fun h ↦ not_ePerfect_subset_simplePresent (mem_univ x) hxt (h · univ t))
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
