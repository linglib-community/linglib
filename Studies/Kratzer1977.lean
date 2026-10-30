module

public import Linglib.Semantics.Modality.Necessity

/-!
# Kratzer (1977): What 'must' and 'can' must and can mean

Kratzer reads *must* and *can* in view of a conversational background as consequence from and
compatibility with the premises it supplies, the substrate's `simpleNecessity` and
`simplePossibility`. From an inconsistent premise set everything follows and nothing is
compatible with it, so she revises both to quantify over its consistent subsets: *must φ* holds
when every consistent subset extends to a consistent subset from which φ follows, and *can φ*
when some consistent subset leaves φ compatible with all its consistent extensions. The revision
is [necessity over the empty modal base with the premise set as ordering
source](##mustInView_iff_humanNecessity). It [agrees with the first definitions on a consistent
premise set](##mustInView_iff_of_consistent) and, unlike them, [never makes a proposition and its
negation both necessary](##canInView_of_mustInView). In a New Zealand whose judgments say
that murder is a crime and that deer are, and are not, responsible for damage to young trees,
[murder must be a crime](##must_p) and [deer can be responsible](##can_q), and [whether pupils
must practise flying](##must_q) turns on whether a recommendation to stride and fly is one
premise or two.

## Implementation notes

* The worlds of each example are the four combinations of the two issues it turns on, and its
  premise set is the same at every world.
* The verdicts are proved in the ordering the premises induce on worlds: a premise must hold
  when every world is bettered by one where it holds, and a best world where a proposition fails
  refutes its necessity. A consistent subset containing a proposition makes it possible.
* Definitions 7 and 8 are prose in the article; the set-builder forms quoted with them are those
  of the revised version in [kratzer-2012]. The sentence numbers are the article's; the revision
  numbers each sentence one higher.

## TODO

* Footnote 6 calls the tools for inconsistent premise sets more general than Rescher's. The
  comparison needs Rescher's definitions.

## References

* [kratzer-1977]
* [kratzer-2012] — chapter 1, the revised version of the paper
* [kratzer-1981]
* [lewis-1981]
-/

@[expose] public section

namespace Kratzer1977

open Modality

/-! ### Definitions 7 and 8 -/

section Definitions

variable {W : Type*} {f : Background W} {φ : W → Prop} {i : W} {A B : Set (W → Prop)}

/-- The consistent subsets of a premise set, the set `X` over which Definitions 7 and 8
quantify. -/
def consistentSubsets (A : Set (W → Prop)) : Set (Set (W → Prop)) := {B | B ⊆ A ∧ sInf B ≠ ⊥}

/-- Definition 7: *must φ in view of f* holds at `i` when, `X` being the set of all consistent
subsets of `f i`, "there is for every set in `X` a superset in `X` from which `φ` follows";
in the revised version,
`ν(p, f) = {w ∈ W : ∀A[A ∈ X_f(w) → ∃B[B ∈ X_f(w) & A ⊆ B & ⋂B ⊆ p]]}`. -/
def MustInView (f : Background W) (φ : W → Prop) (i : W) : Prop :=
  ∀ B ∈ consistentSubsets (f i), ∃ C ∈ consistentSubsets (f i), B ⊆ C ∧ sInf C ≤ φ

/-- Definition 8: *can φ in view of f* holds at `i` when "there is a set in `X` such that `φ` is
(logically) compatible with all its supersets in `X`"; in the revised version,
`μ(p, f) = {w ∈ W : ∃A[A ∈ X_f(w) & ∀B[[B ∈ X_f(w) & A ⊆ B] → consistent(B ∪ {p})]]}`. -/
def CanInView (f : Background W) (φ : W → Prop) (i : W) : Prop :=
  ∃ B ∈ consistentSubsets (f i), ∀ C ∈ consistentSubsets (f i), B ⊆ C → ¬ Disjoint (sInf C) φ

private theorem sInf_ne_bot_iff : sInf B ≠ ⊥ ↔ ∃ w, ∀ x ∈ B, x w := by
  simp [Function.ne_iff]

/-- Definition 7 is necessity over the empty modal base with `f` as ordering source: a world
stands for the premises it verifies, and a consistent subset for the worlds verifying it. This is
the modal case of [lewis-1981]'s equivalence of premise and ordering semantics. -/
theorem mustInView_iff_humanNecessity : MustInView f φ i ↔ humanNecessity ⊥ f φ i := by
  rw [humanNecessity, Background.accessibleWorlds_bot,
    OrderingSemantics.mem_necessityFilter_ofCriteria_iff]
  simp [MustInView, consistentSubsets, sInf_ne_bot_iff, Pi.le_def, and_assoc]

theorem canInView_iff_not_mustInView_compl : CanInView f φ i ↔ ¬ MustInView f φᶜ i := by
  simp only [CanInView, MustInView, ← le_compl_iff_disjoint_right, not_forall, not_exists, not_and,
    exists_prop]

theorem mustInView_iff_not_canInView_compl : MustInView f φ i ↔ ¬ CanInView f φᶜ i := by
  rw [canInView_iff_not_mustInView_compl, compl_compl, not_not]

theorem canInView_iff_humanPossibility : CanInView f φ i ↔ humanPossibility ⊥ f φ i :=
  canInView_iff_not_mustInView_compl.trans (not_congr mustInView_iff_humanNecessity)

/-- Whatever must be the case under Definition 7 can be under Definition 8, on every premise set:
unlike Definitions 5 and 6, the revision never makes a proposition and its negation both
necessary. -/
theorem canInView_of_mustInView [Nonempty W] (h : MustInView f φ i) : CanInView f φ i := by
  rw [mustInView_iff_humanNecessity] at h
  rw [canInView_iff_not_mustInView_compl, mustInView_iff_humanNecessity]
  have : (OrderingSemantics.necessityFilter (premisePreorder (f i))
      ((⊥ : Background W).accessibleWorlds i)).NeBot :=
    OrderingSemantics.necessityFilter_neBot_iff.2 (by simp)
  exact fun h' ↦ let ⟨_, hφ, hnφ⟩ := Filter.nonempty_of_mem (Filter.inter_mem h h'); hnφ hφ

-- On a consistent premise set Definition 7 is Definition 5, consequence from the premises
theorem mustInView_iff_of_consistent (h : sInf (f i) ≠ ⊥) :
    MustInView f φ i ↔ simpleNecessity f φ i := by
  rw [mustInView_iff_humanNecessity, humanNecessity_iff_simpleNecessity_sup, bot_sup_eq]
  simpa [bot_sup_eq, Set.Nonempty] using sInf_ne_bot_iff.1 h

-- Definition 8 is Definition 6 on a consistent premise set
theorem canInView_iff_of_consistent (h : sInf (f i) ≠ ⊥) :
    CanInView f φ i ↔ simplePossibility f φ i := by
  simp [canInView_iff_not_mustInView_compl, mustInView_iff_of_consistent h]

-- The relation first tried and rejected as too strict, consequence from every consistent subset,
-- holds only of a tautology, since the empty set is a consistent subset (p. 350)
theorem forall_consistentSubsets_sInf_le_iff [Nonempty W] :
    (∀ B ∈ consistentSubsets A, sInf B ≤ φ) ↔ φ = ⊤ :=
  ⟨fun h ↦ top_le_iff.1 (sInf_empty (α := W → Prop) ▸ h ∅ ⟨A.empty_subset, by simp⟩),
    fun h _ _ ↦ h ▸ le_top⟩

-- Definition 8, as the paper argues (8) and (9)
theorem canInView_of_mem (hB : B ∈ consistentSubsets (f i)) (hφ : φ ∈ B) : CanInView f φ i :=
  ⟨B, hB, fun _ hC hBC hd ↦ hC.2 (hd.eq_bot_of_le (sInf_le (hBC hφ)))⟩

-- A premise must hold when every world is bettered by one where it holds
theorem mustInView_of_forall_exists_le (hφ : φ ∈ f i) (h : ∀ u, ∃ v, (v ≤[f i] u) ∧ φ v) :
    MustInView f φ i :=
  mustInView_iff_humanNecessity.2 fun u _ ↦
    let ⟨v, hvu, hv⟩ := h u
    ⟨v, by simp, hvu, fun _ _ hzv ↦ hzv φ hφ hv⟩

-- A best world where `φ` fails refutes *must φ*
theorem not_mustInView_of_mem_bestWorlds {u : W} (hu : u ∈ bestWorlds ⊥ f i) (hφ : ¬ φ u) :
    ¬ MustInView f φ i :=
  fun h ↦ hφ (necessity_of_humanNecessity (mustInView_iff_humanNecessity.1 h) u hu)

end Definitions

/-! ### The worlds -/

/-- The four worlds: the truth values of the two issues an example turns on. -/
abbrev World := Bool × Bool

/-- The first issue holds. -/
def p : World → Prop := (·.1 = true)

/-- The second issue holds. -/
def q : World → Prop := (·.2 = true)

/-! ### The New Zealand judgments

`p` is that murder is a crime, the judgment (10); `q` that deer are personally responsible for
damage they inflict on young trees, the Auckland judgment (11); and `qᶜ` the Wellington
judgment (12). -/

/-- What the New Zealand judgments provide. -/
def judgments : Set (World → Prop) := {p, q, qᶜ}

theorem judgments_inconsistent : sInf judgments = ⊥ := by
  funext w; simp [judgments]

-- Definition 5 makes (7) true
theorem simpleNecessity_compl_p (w : World) :
    simpleNecessity (Function.const World judgments) pᶜ w := by
  rw [simpleNecessity_iff_sInf_le, Function.const_apply, judgments_inconsistent]; exact bot_le

-- Definition 6 makes (8) false
theorem not_simplePossibility_q (w : World) :
    ¬ simplePossibility (Function.const World judgments) q w := by
  rw [simplePossibility_iff_not_disjoint, Function.const_apply, judgments_inconsistent, not_not]
  exact disjoint_bot_left

-- The rejected relation: `p` does not follow from every consistent subset (p. 350)
example : ¬ ∀ B ∈ consistentSubsets judgments, sInf B ≤ p := by
  rw [forall_consistentSubsets_sInf_le_iff]
  exact fun h ↦ by simpa [p] using congrFun h (false, false)

/-- (6), *murder must be a crime*, is true under Definition 7: making murder a crime leaves every
other judgment as it was. -/
theorem must_p (w : World) : MustInView (Function.const World judgments) p w :=
  mustInView_of_forall_exists_le (by simp [judgments]) fun u ↦
    ⟨(true, u.2), fun x hx _ ↦ by rcases hx with rfl | rfl | rfl <;> simp_all [p, q], rfl⟩

-- (7) is false under Definition 7: no consistent superset of `{p, q}` implies `pᶜ` (p. 351)
theorem not_must_compl_p (w : World) : ¬ MustInView (Function.const World judgments) pᶜ w :=
  canInView_iff_not_mustInView_compl.1 <| canInView_of_mem (B := {p, q})
    ⟨by simp [judgments, Set.insert_subset_iff], sInf_ne_bot_iff.2 ⟨(true, true), by simp [p, q]⟩⟩
    (by simp)

/-- (8), *deer can be personally responsible*, is true under Definition 8: the Auckland judgment
is a consistent subset by itself. -/
theorem can_q (w : World) : CanInView (Function.const World judgments) q w :=
  canInView_of_mem (B := {q})
    ⟨by simp [judgments], sInf_ne_bot_iff.2 ⟨(true, true), by simp [q]⟩⟩ rfl

-- (9) is true under Definition 8, symmetrically
theorem can_compl_q (w : World) : CanInView (Function.const World judgments) qᶜ w :=
  canInView_of_mem (B := {qᶜ})
    ⟨by simp [judgments], sInf_ne_bot_iff.2 ⟨(true, false), by simp [q]⟩⟩ rfl

-- (13) is false under Definition 8, by (6)
theorem not_can_compl_p (w : World) : ¬ CanInView (Function.const World judgments) pᶜ w :=
  mustInView_iff_not_canInView_compl.1 (must_p w)

/-! ### The Whare Wananga recommendations (§2.3)

`p` is that the pupils practise striding and `q` that they practise flying. Te Miti's
recommendation is read once as the single proposition (14), `p ⊓ q`, and once as the two
propositions `p` and `q`; Te Kini's is (15), `pᶜ`. -/

/-- Te Miti's recommendation as one proposition, with Te Kini's. -/
def recommendations : Set (World → Prop) := {p ⊓ q, pᶜ}

/-- Te Miti's recommendation as two propositions, with Te Kini's. -/
def recommendations' : Set (World → Prop) := {p, q, pᶜ}

-- (16) is false on the first reading: a world where the pupils neither stride nor fly is best,
-- the only recommendation it keeps being Te Kini's (p. 353)
theorem not_must_q (w : World) : ¬ MustInView (Function.const World recommendations) q w := by
  refine not_mustInView_of_mem_bestWorlds (u := (false, false)) ⟨by simp, fun v _ hv ↦ ?_⟩
    (by simp [q])
  have hpv : ¬ p v := hv pᶜ (by simp [recommendations]) (by simp [p])
  rintro x (rfl | rfl) hxv
  · exact absurd hxv.1 hpv
  · simp [p]

/-- On the second reading (16), *the pupils must practise flying*, is true: flying is a
recommendation of its own, and practising it leaves every other recommendation as it was. -/
theorem must_q (w : World) : MustInView (Function.const World recommendations') q w :=
  mustInView_of_forall_exists_le (by simp [recommendations']) fun u ↦
    ⟨(u.1, true), fun x hx _ ↦ by rcases hx with rfl | rfl | rfl <;> simp_all [p, q], rfl⟩

end Kratzer1977
