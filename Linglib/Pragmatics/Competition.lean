module

public import Mathlib.Data.Set.Lattice.Indexed
public import Mathlib.Order.Minimal

/-!
# Pragmatic competition

An expression is blocked when one of its alternatives is strictly better along a preorder, and
it survives competition at a point where its content holds and no alternative whose content also
holds there is strictly stronger. `Blocked` is the first relation, for any alternative source
`S → Set S` and any map into a preorder, and `unblocked` the set of points of the second, for a
content function `S → Set W`; `sameAssertion` keeps the alternatives with the same at-issue
content. Ordered by entailment, blocking compares contents; ordered by harmony it is the blocking
of bidirectional optimality theory (`BidirectionalOT.blocks_iff_blocked`).

Along at-issue content over the weakly assertable alternatives, blocking is Katzir's
neo-Gricean principle, and along conventional-implicature content it is Lo Guercio's Maximize
Conventional Implicatures. Along presuppositional content over `sameAssertion` it is Heim's
Maximize Presupposition, and its condition at a context, as Schlenker states it, is
`unblocked`: the presupposition less the presuppositions of the strictly stronger alternatives,
whose removal is Percus's anti-presupposition and Sauerland's implicated presupposition. The
relations carry no theory of why competition obtains, so pragmatic and grammatical accounts of
each principle state their disagreement over one definition.

## Main definitions

* `Competition.Blocked`: some alternative is strictly better along a preorder.
* `Competition.unblocked`: the points where no alternative whose content holds is strictly
  stronger.
* `Competition.sameAssertion`: the alternatives with the same at-issue content.

## Main results

* `Competition.not_blocked_iff_minimalFor`: an expression is unblocked when it is minimal among
  itself and its alternatives.
* `Competition.mem_unblocked_iff_minimalFor`: an expression is unblocked where it is a most
  specific competitor whose content holds.
* `Competition.disjoint_unblocked`: competitors with strictly nested contents are never
  unblocked at the same point.
* `Competition.unblocked_anti`: more alternatives, fewer unblocked points.

## References

* [katzir-2007]
* [lo-guercio-2025]
* [heim-1991]
* [schlenker-2012]
* [percus-2006]
* [sauerland-2008a]
-/

@[expose] public section

namespace Competition

variable {S W β : Type*} {alts alts' : S → Set S} {content assertion : S → Set W} {φ φ' ψ : S}
  {w : W}

section Preorder

variable [Preorder β] {f : S → β}

/-- `φ` is blocked when some alternative in `alts φ` is strictly better under `f`. -/
def Blocked (alts : S → Set S) (f : S → β) (φ : S) : Prop :=
  ∃ φ' ∈ alts φ, f φ' < f φ

theorem Blocked.mono (h : alts ≤ alts') (hb : Blocked alts f φ) : Blocked alts' f φ :=
  let ⟨φ', hφ', hlt⟩ := hb; ⟨φ', h φ hφ', hlt⟩

theorem not_blocked_of_forall_le (h : ∀ φ' ∈ alts φ, f φ ≤ f φ') : ¬ Blocked alts f φ :=
  fun ⟨φ', hφ', hlt⟩ ↦ hlt.not_ge (h φ' hφ')

theorem not_blocked_iff_minimalFor :
    ¬ Blocked alts f φ ↔ MinimalFor (· ∈ insert φ (alts φ)) f φ := by
  simp only [Blocked, MinimalFor, Set.mem_insert_iff, true_or, true_and, not_exists, not_and,
    not_lt_iff_le_imp_ge]
  constructor
  · intro h ψ hψ hle
    rcases hψ with rfl | hψ
    exacts [le_rfl, h ψ hψ hle]
  · exact fun h ψ hψ hle ↦ h (.inr hψ) hle

end Preorder

/-- The alternatives of `φ` with the same at-issue content, the competitors Maximize
Presupposition compares. -/
def sameAssertion (alts : S → Set S) (assertion : S → Set W) (φ : S) : Set S :=
  {φ' ∈ alts φ | assertion φ' = assertion φ}

@[simp] theorem mem_sameAssertion :
    φ' ∈ sameAssertion alts assertion φ ↔ φ' ∈ alts φ ∧ assertion φ' = assertion φ :=
  Iff.rfl

theorem sameAssertion_le (alts : S → Set S) (assertion : S → Set W) :
    sameAssertion alts assertion ≤ alts :=
  fun _ _ h ↦ h.1

/-! ### Unblocked points -/

/-- `φ` is unblocked at the points where its content holds and no alternative whose content also
holds there is strictly stronger: its content less the contents of the strictly stronger
alternatives. -/
def unblocked (alts : S → Set S) (content : S → Set W) (φ : S) : Set W :=
  content φ \ ⋃₀ (content '' alts φ ∩ Set.Iio (content φ))

theorem mem_unblocked_iff :
    w ∈ unblocked alts content φ ↔
      w ∈ content φ ∧ ∀ ψ ∈ alts φ, w ∈ content ψ → ¬ content ψ ⊂ content φ := by
  refine ⟨fun ⟨hw, hn⟩ ↦ ⟨hw, fun ψ hψ hwψ hss ↦ hn ⟨_, ⟨⟨ψ, hψ, rfl⟩, hss⟩, hwψ⟩⟩,
    fun ⟨hw, h⟩ ↦ ⟨hw, ?_⟩⟩
  rintro ⟨_, ⟨⟨ψ, hψ, rfl⟩, hss⟩, hwψ⟩
  exact h ψ hψ hwψ hss

theorem unblocked_subset (alts : S → Set S) (content : S → Set W) (φ : S) :
    unblocked alts content φ ⊆ content φ :=
  sdiff_le

theorem mem_unblocked_iff_minimalFor :
    w ∈ unblocked alts content φ ↔
      MinimalFor (fun ψ ↦ ψ ∈ insert φ (alts φ) ∧ w ∈ content ψ) content φ := by
  simp only [mem_unblocked_iff, MinimalFor, Set.mem_insert_iff, true_or, true_and,
    Set.ssubset_iff_subset_ne, not_and, not_not]
  constructor
  · rintro ⟨hw, h⟩
    refine ⟨hw, fun ψ ⟨hψ, hwψ⟩ hle ↦ ?_⟩
    rcases hψ with rfl | hψ
    exacts [le_rfl, (h ψ hψ hwψ hle).ge]
  · rintro ⟨hw, h⟩
    exact ⟨hw, fun ψ hψ hwψ hle ↦ le_antisymm hle (h ⟨Or.inr hψ, hwψ⟩ hle)⟩

theorem unblocked_eq_self (h : ¬ Blocked alts content φ) : unblocked alts content φ = content φ :=
  sdiff_eq_left.2 <| Set.disjoint_left.2 fun _ _ ⟨_, ⟨⟨ψ, hψ, rfl⟩, hss⟩, _⟩ ↦ h ⟨ψ, hψ, hss⟩

/-- With one strictly stronger alternative containing the others, `φ` is unblocked on its content
less that alternative's. -/
theorem unblocked_eq_sdiff (hψ : ψ ∈ alts φ) (hss : content ψ ⊂ content φ)
    (hother : ∀ χ ∈ alts φ, content χ ⊂ content φ → content χ ⊆ content ψ) :
    unblocked alts content φ = content φ \ content ψ := by
  ext w
  rw [mem_unblocked_iff, Set.mem_sdiff]
  exact and_congr_right fun _ ↦
    ⟨fun h hw ↦ h ψ hψ hw hss, fun h χ hχ hw hss' ↦ h (hother χ hχ hss' hw)⟩

/-- Where `φ` is unblocked, no strictly stronger alternative's content holds. -/
theorem disjoint_unblocked_of_ssubset (hψ : ψ ∈ alts φ) (h : content ψ ⊂ content φ) :
    Disjoint (content ψ) (unblocked alts content φ) :=
  disjoint_sdiff_self_right.mono_left
    (le_sSup (s := content '' alts φ ∩ Set.Iio (content φ)) ⟨⟨ψ, hψ, rfl⟩, h⟩)

theorem disjoint_unblocked (hψ : ψ ∈ alts φ) (h : content ψ ⊂ content φ) :
    Disjoint (unblocked alts content ψ) (unblocked alts content φ) :=
  (disjoint_unblocked_of_ssubset hψ h).mono_left (unblocked_subset _ _ _)

/-- An expression is unblocked at fewer points than its content holds exactly when some
alternative with satisfiable content is strictly stronger. -/
theorem unblocked_ssubset_iff :
    unblocked alts content φ ⊂ content φ ↔
      ∃ ψ ∈ alts φ, content ψ ⊂ content φ ∧ (content ψ).Nonempty := by
  refine ⟨fun h ↦ ?_, fun ⟨ψ, hψ, hss, w, hw⟩ ↦ ?_⟩
  · obtain ⟨w, hw, hu⟩ := Set.exists_of_ssubset h
    simp only [mem_unblocked_iff, hw, true_and, not_forall, not_not] at hu
    obtain ⟨ψ, hψ, hwψ, hss⟩ := hu
    exact ⟨ψ, hψ, hss, w, hwψ⟩
  · exact (unblocked_subset _ _ _).ssubset_of_ne fun heq ↦
      Set.disjoint_left.1 (disjoint_unblocked_of_ssubset hψ hss) hw (heq ▸ hss.1 hw)

theorem unblocked_anti (h : alts ≤ alts') :
    unblocked alts' content φ ⊆ unblocked alts content φ :=
  sdiff_le_sdiff_left <| sSup_le_sSup <| Set.inter_subset_inter_left _ (Set.image_mono (h φ))

end Competition
