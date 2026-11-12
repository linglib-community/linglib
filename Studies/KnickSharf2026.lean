module

public import Linglib.Data.Examples.KnickSharf2026
public import Linglib.Data.Examples.Readers
public import Linglib.Semantics.Aspect.Viewpoint
public import Mathlib.Order.UpperLower.CompleteLattice
public import Studies.Chierchia2006
public import Studies.IatridouEtAl2001
public import Studies.KatzirSingh2015

/-!
# Knick and Sharf (2026): On focus and the perfect aspect

Knick and Sharf's perfect time span ends at the speech time and starts in a domain $t_r$. With
the imperfective beneath the perfect, the universal perfect entails the simple present; with the
perfective, the experiential perfect does not. Focus on the participle falls on the domain, whose
alternatives [form a chain under entailment](##isChain_range_universalPerfect), and covert *even*
[selects the one reaching furthest back](##evenEnrich_universalPerfect_eq_iff), leaving [the speech
time outside it](##not_mem_of_evenEnrich). The universal perfect [survives its competition with
the simple present exactly then](##survives_universalPerfect_iff), as under *ever since* and not
under broad focus, where the domain contains the speech time. How a perfect specifies its left
boundary thus [predicts its reading and whether it admits *but she's not
anymore*](##form_predicts).

## Implementation notes

* A sentence is the set of worlds in which it holds at the speech time, the present tense being
  evaluation there, so that entailment is inclusion; the worlds are the context set, and the
  paper's contextual entailment is inclusion too.
* A left boundary is a time point, where the paper's is an initial subinterval of the perfect
  time span within $t_r$, and a domain is a set of times; the paper's interval domains are
  `Set.Icc`.
* The imperfective properly includes the reference interval in the run time of an actual
  eventuality, `Aspect.ViewpointType.imperfective.denote`, not the modal `Aspect.IMPF`. Iatridou,
  Anagnostopoulou and Izvorski's includes it, so an eventuality running exactly from $t_0$ to the
  speech time [verifies their universal perfect and not this
  one](##exists_iatridou_not_universalPerfect).
* *Ever since* is their durative adverbial, the spans starting at $t_0$ with the aspect holding
  throughout: over the imperfective it is [the universal perfect over
  $\{t_0\}$](##everSince_universal), and over the perfective it [fails of eventualities that take
  time](##not_survives_everSince_experiential).
* A parse is available when it survives the competition in some model whose eventualities take
  time, as those of *be happy*, *cry* and *be sick* do. The focused perfect has the one parse its
  logical form gives it, the imperfective beneath the perfect.
* Entailment in every model quantifies over predicates of intervals, the event domain in which
  every interval is a possible run time.
* The paper compares alternatives with disjoint, overlapping and nested domains; the three cases
  come to [one criterion](##universalPerfect_Icc_subset_iff), the latest time of the domain up to
  the speech time, so that the width of a domain plays no part of its own.
* The complexity of a competitor is the number of heads in its logical form, the simple present
  being the universal perfect with `PERF` deleted.

## TODO

* The permanent states of *be dead*, the predicate classes under focus and the unavailable
  shortening contrast are not yet rows paired with predictions.

## References

* [knick-sharf-2026]
* [iatridou-anagnostopoulou-izvorski-2001]
* [chierchia-2006]
* [rooth-1992]
* [katzir-singh-2015]
-/

@[expose] public section

namespace KnickSharf2026

open Aspect Function Set
open Chierchia2006 (evenEnrich)
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

-- (39), (41): whatever its domain
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

/-- The competitors of (39) and (41), the simple present and a perfect. -/
inductive Competitor
  | simplePresent
  | perfect
  deriving DecidableEq

/-- What a competitor means at the speech time `t`, the perfect meaning `p`. -/
def Competitor.meaning (V : W → E → Prop) (p : Set W) (t : T) : Competitor → Set W
  | .simplePresent => KnickSharf2026.simplePresent V t
  | .perfect => p

/-- The heads of the logical form, `PRS IMPF` against `PRS PERF IMPF` or `PRS PERF PRFV`
(footnote 10). -/
def Competitor.heads : Competitor → ℕ
  | .simplePresent => 2
  | .perfect => 3

/-- The competition (43) between the simple present and the perfect `p`. -/
abbrev competition (V : W → E → Prop) (p : Set W) (t : T) :
    KatzirSingh2015.Scenario W Competitor ℕ where
  meaning := Competitor.meaning V p t
  complexity := Competitor.heads
  context := univ

/-- The question the competitors answer, the competitors themselves. -/
abbrev question (V : W → E → Prop) (p : Set W) (t : T) : Set (Set W) :=
  range (Competitor.meaning V p t)

theorem competition_relevant {p : Set W} (c : Competitor) :
    (competition V p t).Relevant (question V p t) c :=
  KatzirSingh2015.Scenario.relevant_of_mem ⟨c, rfl⟩

-- (43), (44)
theorem goodAnswer_perfect_iff {p : Set W} :
    (competition V p t).GoodAnswer (question V p t) .perfect w ↔
      w ∈ p ∧ ¬ (simplePresent V t ⊆ p ∧ w ∈ simplePresent V t) := by
  refine ⟨fun h ↦ ⟨h.mem, fun ⟨hs, hw⟩ ↦ ?_⟩, fun ⟨hw, hs⟩ ↦ ⟨⟨hw, competition_relevant _⟩, ?_⟩⟩
  · exact KatzirSingh2015.Scenario.not_goodAnswer_of_simpler (u := .perfect) (v := .simplePresent)
      (by decide : Competitor.heads .simplePresent < Competitor.heads .perfect) hs hw
      (competition_relevant _) h
  · rintro (_ | _) ⟨hw', -⟩ hle
    · exact absurd ⟨hle.2, hw'⟩ hs
    · exact le_rfl

theorem goodAnswer_universalPerfect_iff :
    (competition V (universalPerfect V D t) t).GoodAnswer (question V (universalPerfect V D t) t)
        .perfect w ↔
      w ∈ universalPerfect V D t ∧ ¬ simplePresent V t ⊆ universalPerfect V D t := by
  rw [goodAnswer_perfect_iff]
  exact and_congr_right fun hw ↦ not_congr
    ⟨And.left, fun hs ↦ ⟨hs, universalPerfect_subset_simplePresent V D t hw⟩⟩

/-- A perfect, a proposition in each model, survives the competition with the simple present when
it is a good answer in some model whose eventualities take time. -/
def Survives (p : (W → NonemptyInterval T → Prop) → Set W) (t : T) : Prop :=
  ∃ V : W → NonemptyInterval T → Prop, (∀ w e, V w e → e.fst < e.snd) ∧
    ∃ w, (competition V (p V) t).GoodAnswer (question V (p V) t) .perfect w

/-- The universal perfect survives its competition with the simple present exactly when its
domain has a time before the speech time but not the speech time itself, as under narrow focus or
an overt adverbial and not under broad focus. -/
theorem survives_universalPerfect_iff [NoMaxOrder T] [Nontrivial W] :
    Survives (W := W) (universalPerfect · D t) t ↔ t ∉ D ∧ (D ∩ Iic t).Nonempty := by
  simp_rw [Survives, goodAnswer_universalPerfect_iff]
  refine ⟨fun ⟨V, _, w, hw, hs⟩ ↦ ⟨fun ht ↦ hs (universalPerfect_eq_simplePresent ht).ge, ?_⟩, ?_⟩
  · obtain ⟨x, hx, hxt, -⟩ := mem_universalPerfect.1 hw
    exact ⟨x, hx, hxt⟩
  -- an eventuality from `x` through the speech time, and in another world one starting there
  rintro ⟨ht, x, hx, hxt⟩
  classical
  obtain ⟨w₁, w₂, hne⟩ := exists_pair_ne W
  obtain ⟨t', ht'⟩ := exists_gt t
  refine ⟨update (fun _ e ↦ e = ⟨(t, t'), ht'.le⟩) w₁ (· = ⟨(x, t'), hxt.trans ht'.le⟩), ?_, w₁,
    mem_universalPerfect.2 ⟨x, hx, hxt, _, lt_extend hxt ht', by simp⟩, fun hs ↦ ?_⟩
  · intro w e he
    rcases eq_or_ne w w₁ with rfl | hw
    · simp only [update_self] at he
      exact he ▸ hxt.trans_lt ht'
    · rw [update_of_ne hw] at he
      exact he ▸ ht'
  · obtain ⟨y, hy, hyt, e, hlt, he⟩ := mem_universalPerfect.1 <|
      hs (a := w₂) ⟨_, lt_extend le_rfl ht', by simp [update_of_ne hne.symm]⟩
    rw [update_of_ne hne.symm] at he
    subst he
    exact ht (le_antisymm hyt (NonemptyInterval.le_def.1 hlt.le).1 ▸ hy)

-- (29), (30): an eventuality that has ended
theorem survives_experientialPerfect [Nonempty W] {x m : T} (hx : x ∈ D) (hxm : x < m)
    (hmt : m < t) : Survives (W := W) (experientialPerfect · D t) t := by
  obtain ⟨w⟩ := ‹Nonempty W›
  refine ⟨fun _ e ↦ e = ⟨(x, m), hxm.le⟩, fun _ _ he ↦ he ▸ hxm, w, goodAnswer_perfect_iff.2
    ⟨mem_experientialPerfect.2 ⟨x, hx, (hxm.trans hmt).le, ⟨(x, m), hxm.le⟩,
      NonemptyInterval.le_def.2 ⟨le_rfl, hmt.le⟩, rfl⟩, fun ⟨_, e, hlt, he⟩ ↦ ?_⟩⟩
  subst he
  exact hmt.not_ge (NonemptyInterval.le_def.1 hlt.le).2

/-! ### The left boundary specified -/

-- §4.3.4 and §5: a distinct alternative, which the alternatives `C` include [rooth-1992]
theorem not_mem_of_evenEnrich [NoMaxOrder T] [Nonempty W] {𝒟 : Set (Set T)} {D' : Set T}
    (he : ∀ V : W → NonemptyInterval T → Prop,
      evenEnrich ((universalPerfect V · t) '' 𝒟) (universalPerfect V D t) =
        universalPerfect V D t)
    (hD' : D' ∈ 𝒟)
    (hne : ∃ V : W → NonemptyInterval T → Prop, universalPerfect V D' t ≠ universalPerfect V D t) :
    t ∉ D := fun ht ↦ by
  obtain ⟨y, ⟨hy, hyt⟩, hty⟩ :=
    evenEnrich_universalPerfect_eq_iff.1 he D' hD' (subset_lowerClosure ⟨ht, le_rfl⟩)
  obtain ⟨V, hV⟩ := hne
  exact hV (by rw [universalPerfect_eq_simplePresent ht,
    universalPerfect_eq_simplePresent (le_antisymm hyt hty ▸ hy)])

/-- The universal and the experiential reading of the perfect. -/
inductive Reading
  | universal
  | experiential
  deriving DecidableEq

/-- The aspect beneath the perfect, the imperfective (25) for the universal reading and the
perfective (28) for the experiential (§4.2). -/
def Reading.aspect : Reading → (W → E → Prop) → W → Set (NonemptyInterval T)
  | .universal => ViewpointType.imperfective.denote
  | .experiential => PRFV

/-- The perfect under a reading. -/
def Reading.perfect : Reading → (W → E → Prop) → Set T → T → Set W
  | .universal => universalPerfect
  | .experiential => experientialPerfect

/-- The perfect under the durative adverbial *ever since t₀* (4b), (5), (8b): the spans starting
at `t₀`, the aspect holding throughout them, as [iatridou-anagnostopoulou-izvorski-2001] read
durative adverbials. -/
def Reading.everSince (r : Reading) (V : W → E → Prop) (t₀ t : T) : Set W :=
  {w | (w, t) ∈ PERF ({pts | pts.fst = t₀} ∩ durative (r.aspect V) ·)}

theorem everSince_universal (V : W → E → Prop) (t₀ t : T) :
    Reading.universal.everSince V t₀ t = universalPerfect V {t₀} t := by
  have h (w : W) : durative (ViewpointType.imperfective.denote V) w =
      ViewpointType.imperfective.denote V w :=
    durative_eq_of_isLowerSet (isLowerSet_denote_imperfective V w)
  simp only [Reading.everSince, Reading.aspect, h]
  rfl

-- footnote 2: a bounded eventuality that takes time holds throughout no span
theorem not_survives_everSince_experiential {t₀ : T} :
    ¬ Survives (W := W) (Reading.experiential.everSince · t₀ t) t :=
  fun ⟨_, hV, _, hw⟩ ↦ IatridouEtAl2001.no_universal_of_prfv (fun e he ↦ hV _ e he)
    (perf_mono (fun _ ↦ inter_subset_right) hw.mem)

-- the imperfective (25) is strict where Iatridou et al.'s is not (footnote 6)
theorem exists_iatridou_not_universalPerfect [Nonempty W] {t₀ : T} (h : t₀ ≤ t) :
    ∃ (V : W → NonemptyInterval T → Prop) (w : W),
      (w, t) ∈ PERF ({pts | pts.fst = t₀} ∩ durative (UNBOUNDED V) ·) ∧
        w ∉ universalPerfect V {t₀} t := by
  obtain ⟨w⟩ := ‹Nonempty W›
  refine ⟨fun _ e ↦ e = ⟨(t₀, t), h⟩, w,
    IatridouEtAl2001.universal_of_covers rfl h le_rfl le_rfl, fun hw ↦ ?_⟩
  obtain ⟨_, rfl, _, _, hlt, rfl⟩ := mem_universalPerfect.1 hw
  exact hlt.ne rfl

/-- How the left boundary of the perfect time span is specified (p. 585): not at all, as under
broad focus without an adverbial; by an overt durative adverbial; or by narrow focus on the
participle. -/
inductive LeftBoundary
  | unspecified
  | everSince
  | focused
  deriving DecidableEq

/-- The parses of a perfect: universal and experiential, except under focus, whose logical form
(31) has the imperfective beneath the perfect. -/
def LeftBoundary.parses : LeftBoundary → List Reading
  | .unspecified | .everSince => [.universal, .experiential]
  | .focused => [.universal]

/-- A parse is available to a perfect whose left boundary is specified as `b` when, in some
configuration `b` admits, it survives the competition with the simple present: over a domain
containing the speech time when unspecified (p. 587), from an earlier time under *ever since*, and
under focus over a domain on which covert *even* is consistent against alternatives that include a
distinct one. -/
def LeftBoundary.Available (W T : Type*) [LinearOrder T] : LeftBoundary → Reading → Prop
  | .unspecified, r => ∃ (D : Set T) (t : T), t ∈ D ∧ Survives (W := W) (r.perfect · D t) t
  | .everSince, r => ∃ t₀ t : T, t₀ < t ∧ Survives (W := W) (r.everSince · t₀ t) t
  | .focused, r => ∃ (D : Set T) (𝒟 : Set (Set T)) (t : T),
      (∃ D' ∈ 𝒟, ∃ V : W → NonemptyInterval T → Prop, r.perfect V D' t ≠ r.perfect V D t) ∧
      (∀ V : W → NonemptyInterval T → Prop,
        evenEnrich ((r.perfect V · t) '' 𝒟) (r.perfect V D t) = r.perfect V D t) ∧
      Survives (W := W) (r.perfect · D t) t

-- the experiential alternatives are ordered by the earliest time of the domain
theorem experientialPerfect_mono (h : D₁ ∩ Iic t ⊆ upperClosure (D₂ ∩ Iic t)) :
    experientialPerfect V D₁ t ⊆ experientialPerfect V D₂ t := fun _ hw ↦
  let ⟨_, hx, hxt, e, hle, hV⟩ := mem_experientialPerfect.1 hw
  let ⟨y, ⟨hy, hyt⟩, hyx⟩ := h ⟨hx, hxt⟩
  mem_experientialPerfect.2
    ⟨y, hy, hyt, e, hle.trans (NonemptyInterval.le_def.2 ⟨hyx, le_rfl⟩), hV⟩

/-- Were the focused perfect experiential, its parse would be available: covert *even* over its
alternatives selects the domain reaching least far back, and it survives the competition, so the
account itself does not exclude the felicity of the continuation of (10) or of (14d). -/
theorem focused_experiential_available [Nonempty W] :
    LeftBoundary.focused.Available W ℤ .experiential := by
  obtain ⟨w⟩ := ‹Nonempty W›
  let e₀ : NonemptyInterval ℤ := ⟨(0, 2), by norm_num⟩
  simp only [LeftBoundary.Available, Reading.perfect]
  refine ⟨{1}, {{1}, {0}}, 3, ⟨{0}, by simp, fun _ e ↦ e = e₀, fun h ↦ ?_⟩, fun V ↦ ?_,
    survives_experientialPerfect (mem_singleton 1) (by norm_num : (1 : ℤ) < 2) (by norm_num)⟩
  · -- the eventuality from 0 to 2 lies within a span from 0 and within none from 1
    have h₀ : w ∈ experientialPerfect (fun _ e ↦ e = e₀) {0} 3 :=
      mem_experientialPerfect.2 ⟨0, rfl, by norm_num, e₀,
        NonemptyInterval.le_def.2 ⟨le_rfl, by norm_num⟩, rfl⟩
    obtain ⟨x, hx, _, e, hle, he⟩ := mem_experientialPerfect.1 (h ▸ h₀)
    subst he
    have : x ≤ 0 := (NonemptyInterval.le_def.1 hle).1
    simp only [mem_singleton_iff] at hx
    omega
  · refine Set.ext fun _ ↦ ⟨And.left, fun hw ↦ ⟨hw, ?_⟩⟩
    rintro _ ⟨D', hD', rfl⟩
    refine experientialPerfect_mono fun x ⟨hx, hxt⟩ ↦ ?_
    rcases hD' with rfl | rfl
    · exact subset_upperClosure ⟨hx, hxt⟩
    · exact ⟨0, ⟨rfl, by norm_num⟩, by simp only [mem_singleton_iff] at hx; omega⟩

/-! ### The form predicts the reading -/

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

theorem LeftBoundary.available_iff {b : LeftBoundary} {r : Reading} :
    b.Available Bool ℤ r ↔ ¬ (b = .unspecified ∧ r = .universal) ∧
      ¬ (b = .everSince ∧ r = .experiential) := by
  cases b <;> cases r <;> simp only [reduceCtorEq, and_true, and_false, not_true_eq_false,
    not_false_eq_true, and_self, iff_true, iff_false]
  · rintro ⟨D, t, ht, hs⟩
    exact (survives_universalPerfect_iff.1 hs).1 ht
  · exact ⟨univ, 2, trivial, survives_experientialPerfect (x := 0) (m := 1) trivial
      (by norm_num) (by norm_num)⟩
  · refine ⟨0, 1, by norm_num, ?_⟩
    simp only [everSince_universal]
    exact survives_universalPerfect_iff.2 ⟨by simp, 0, rfl, by norm_num⟩
  · rintro ⟨t₀, t, -, hs⟩
    exact not_survives_everSince_experiential hs
  · simp only [LeftBoundary.Available, Reading.perfect]
    let e₀ : NonemptyInterval ℤ := ⟨(1, 3), by norm_num⟩
    refine ⟨{0}, {{0}, {1}}, 2, ⟨{1}, by simp, fun _ e ↦ e = e₀, fun h ↦ ?_⟩,
      evenEnrich_universalPerfect_eq_iff.2 ?_,
      survives_universalPerfect_iff.2 ⟨by simp, 0, rfl, by norm_num⟩⟩
    · -- the eventuality from 1 to 3 runs through a span from 1 and through none from 0
      have h₁ : true ∈ universalPerfect (fun _ e ↦ e = e₀) {1} 2 :=
        mem_universalPerfect.2 ⟨1, rfl, by norm_num, e₀, lt_extend (by norm_num)
          (by norm_num : (2 : ℤ) < 3), rfl⟩
      obtain ⟨x, hx, _, e, hlt, he⟩ := mem_universalPerfect.1 (h ▸ h₁)
      subst he
      have : 1 ≤ x := (NonemptyInterval.le_def.1 hlt.le).1
      simp only [mem_singleton_iff] at hx
      omega
    · rintro _ (rfl | rfl)
      · exact le_rfl
      · exact lowerClosure_le.2 fun x ⟨hx, _⟩ ↦
          ⟨1, ⟨rfl, by norm_num⟩, by simp only [mem_singleton_iff] at hx; omega⟩
  · exact focused_experiential_available

instance (b : LeftBoundary) (r : Reading) : Decidable (b.Available Bool ℤ r) :=
  decidable_of_iff _ LeftBoundary.available_iff.symm

/-- A perfect admits the continuation *but she's not anymore* when one of its parses is available
and leaves the eventuality free to have ended. -/
def LeftBoundary.AdmitsCompletion (b : LeftBoundary) : Prop :=
  ∃ r ∈ b.parses, b.Available Bool ℤ r ∧ ¬ r.EntailsPresent Bool ℤ

instance (b : LeftBoundary) : Decidable b.AdmitsCompletion :=
  inferInstanceAs (Decidable (∃ r ∈ b.parses, _))

/-- How a row's perfect specifies its left boundary: by focus on the participle, by an overt
durative adverbial, or not at all. -/
def leftBoundary (e : Datum) : Option LeftBoundary :=
  match e.feature? "focus", e.feature? "adverbial" with
  | some _, _ => some .focused
  | none, some "durative" => some .everSince
  | none, none => some .unspecified
  | none, some _ => none

/-- The reading the paper assigns a row. -/
def reading (e : Datum) : Option Reading :=
  e.parse? "reading" [("universal", .universal), ("experiential", .experiential)]

/-- The form of each perfect predicts its reading, the one parse available to it, and whether it
admits *but she's not anymore*: the experiential perfects (6), (8a) and (12) do, the universal
perfects (5) and (8b) under *ever since* and (10) under focus do not. -/
theorem form_predicts :
    (∀ e ∈ Examples.all, (leftBoundary e).map (fun b ↦ b.parses.filter (b.Available Bool ℤ ·)) =
      (reading e).map ([·])) ∧
    Datum.Checks leftBoundary (fun b ↦ .ofProp b.AdmitsCompletion) Examples.all 6 := by
  decide

end KnickSharf2026
