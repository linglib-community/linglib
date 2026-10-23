module

public import Linglib.Semantics.Modality.Necessity
public import Mathlib.Data.Fintype.Prod

/-!
# Kratzer (1977): What 'must' and 'can' must and can mean

Kratzer reads *must* and *can* in view of a premise set as consequence and compatibility
(Definitions 5 and 6, the substrate's `simpleNecessity` and `simplePossibility`), and revises them
for inconsistent premise sets by quantifying over the consistent subsets (Definitions 7 and 8,
`MustInView` and `CanInView`). In a New Zealand whose whole common law is three judgments, that
murder is a crime and that deer are, and are not, personally responsible for the damage they
inflict on young trees, the revised definitions recover the verdicts the paper argues for:
murder must be a crime, while deer can be responsible and can fail to be. The recommendations of
the former principals of a Whare Wananga show that the verdicts depend on how premises are
individuated.

## Main statements

* `must_p`, `can_q`, `can_neg_q`: the revised verdicts on the New Zealand judgments.
* `not_must_q`, `must_q`: flying is required only when Te Miti's recommendation is two premises.
* `canInView_iff_not_mustInView_not`: the revised modals are dual.

## Implementation notes

* Each example's worlds are the four combinations of the two issues it turns on, and its
  premise set is the same at every world.
* Every premise but one looks at a single issue, so a world of a consistent subset can be moved
  along the other issue without leaving it; the verdicts are proved that way rather than by
  enumerating subsets.
* The paper's sentence numbers are those of the original article; the 2012 revision renumbers
  them.

## References

* [kratzer-1977]
* [kratzer-2012] — Chapter 1, the revised version of the paper
-/

@[expose] public section

namespace Kratzer1977

open Modality

/-! ### Definitions 7 and 8: must and can over consistent subsets -/

section Definitions

variable {W : Type*} {f : Background W} {φ : W → Prop} {i : W}

/-- The consistent subsets of a premise set, `X_A = {B ⊆ A : ⋂B ≠ ∅}`, over which the revised
definitions quantify. -/
def consistentSubsets (A : Set (W → Prop)) : Set (Set (W → Prop)) := {B | B ⊆ A ∧ sInf B ≠ ⊥}

/-- Definition 7: *must φ in view of f* holds at `i` when every consistent subset of `f i`
extends to a consistent subset from which `φ` follows,
`ν(φ, f) = {i : ∀B[B ∈ X_{f(i)} → ∃C[C ∈ X_{f(i)} ∧ B ⊆ C ∧ ⋂C ⊆ φ]]}`. -/
def MustInView (f : Background W) (φ : W → Prop) (i : W) : Prop :=
  ∀ B ∈ consistentSubsets (f i), ∃ C ∈ consistentSubsets (f i), B ⊆ C ∧ sInf C ≤ φ

/-- Definition 8: *can φ in view of f* holds at `i` when some consistent subset of `f i` has
`φ` compatible with each of its consistent extensions,
`μ(φ, f) = {i : ∃B[B ∈ X_{f(i)} ∧ ∀C[(C ∈ X_{f(i)} ∧ B ⊆ C) → consistent(C ∪ {φ})]]}`. -/
def CanInView (f : Background W) (φ : W → Prop) (i : W) : Prop :=
  ∃ B ∈ consistentSubsets (f i), ∀ C ∈ consistentSubsets (f i), B ⊆ C → ¬ Disjoint (sInf C) φ

/-- On a consistent premise set the revised necessity is Definition 5: the premise set is
itself the consistent subset that dominates every other. -/
theorem mustInView_iff_of_consistent (h : sInf (f i) ≠ ⊥) :
    MustInView f φ i ↔ simpleNecessity f φ i := by
  rw [simpleNecessity_iff_sInf_le]
  refine ⟨fun hAll ↦ ?_, fun hle B hB ↦ ⟨f i, ⟨subset_rfl, h⟩, hB.1, hle⟩⟩
  obtain ⟨C, hC, -, hle⟩ := hAll (f i) ⟨subset_rfl, h⟩
  exact (sInf_le_sInf hC.1).trans hle

/-- On a consistent premise set the revised possibility is Definition 6. -/
theorem canInView_iff_of_consistent (h : sInf (f i) ≠ ⊥) :
    CanInView f φ i ↔ simplePossibility f φ i := by
  rw [simplePossibility_iff_not_disjoint]
  refine ⟨fun ⟨B, hB, hAll⟩ ↦ hAll (f i) ⟨subset_rfl, h⟩ hB.1,
    fun hc ↦ ⟨f i, ⟨subset_rfl, h⟩, fun C hC _ hd ↦ hc (hd.mono_left (sInf_le_sInf hC.1))⟩⟩

/-- *Can* is the negation of *must not*, since compatibility with a premise set is the failure
of the negation to follow from it. -/
theorem canInView_iff_not_mustInView_not (f : Background W) (φ : W → Prop) (i : W) :
    CanInView f φ i ↔ ¬ MustInView f (fun j ↦ ¬ φ j) i := by
  have h (C : Set (W → Prop)) : (sInf C ≤ fun j ↦ ¬ φ j) ↔ Disjoint (sInf C) φ :=
    le_compl_iff_disjoint_right
  simp only [CanInView, MustInView, h, not_forall, not_exists, not_and, exists_prop]

theorem mustInView_iff_not_canInView_not (f : Background W) (φ : W → Prop) (i : W) :
    MustInView f φ i ↔ ¬ CanInView f (fun j ↦ ¬ φ j) i := by
  rw [canInView_iff_not_mustInView_not, not_not]
  simp only [not_not]

/-- A premise in a consistent subset is possible under Definition 8: every consistent extension
still contains it. -/
theorem canInView_of_mem {B : Set (W → Prop)} (hB : B ∈ consistentSubsets (f i)) (hφ : φ ∈ B) :
    CanInView f φ i :=
  ⟨B, hB, fun _ hC hBC hd ↦ hC.2 (hd.eq_bot_of_le (sInf_le (hBC hφ)))⟩

/-- A premise of `f i` is necessary under Definition 7 when it is compatible with every
consistent subset: each extends by it to a consistent subset that entails it. -/
theorem mustInView_of_forall_not_disjoint (hφ : φ ∈ f i)
    (h : ∀ B ∈ consistentSubsets (f i), ¬ Disjoint (sInf B) φ) : MustInView f φ i := by
  intro B hB
  refine ⟨insert φ B, ⟨Set.insert_subset hφ hB.1, ?_⟩, Set.subset_insert φ B,
    sInf_le (Set.mem_insert φ B)⟩
  rw [sInf_insert, inf_comm]
  exact fun hbot ↦ h B hB (disjoint_iff.2 hbot)

theorem sInf_ne_bot_iff {B : Set (W → Prop)} : sInf B ≠ ⊥ ↔ ∃ w, ∀ x ∈ B, x w := by
  simp [Function.ne_iff]

theorem not_disjoint_sInf_iff {B : Set (W → Prop)} :
    ¬ Disjoint (sInf B) φ ↔ ∃ w, (∀ x ∈ B, x w) ∧ φ w := by
  simp [Pi.disjoint_iff, Prop.disjoint_iff]

end Definitions

/-! ### The worlds -/

/-- The four worlds: the truth values of the two issues an example turns on. -/
abbrev World := Bool × Bool

/-- The first issue holds. -/
def p : World → Prop := (·.1 = true)

/-- The second issue holds. -/
def q : World → Prop := (·.2 = true)

private theorem forall_mem_of_eq {A B : Set (World → Prop)} {r : World → Prop}
    {π : World → Bool} (hA : ∀ x ∈ A, x ≠ r → ∀ u v, π u = π v → (x u ↔ x v)) (hB : B ⊆ A)
    {w₀ v : World} (hw₀ : ∀ x ∈ B, x w₀) (hv : π v = π w₀) (hr : r ∈ B → r v) :
    ∀ x ∈ B, x v := fun x hx ↦ by
  by_cases hxr : x = r
  · exact hxr ▸ hr (hxr ▸ hx)
  · exact (hA x (hB hx) hxr v w₀ hv).2 (hw₀ x hx)

/-! ### The New Zealand judgments (§2.1–§2.2)

`p` is that murder is a crime, the judgment (10); `q` that deer are personally responsible for
damage they inflict on young trees, the Auckland judgment (11); and `qᶜ` the Wellington
judgment (12). -/

/-- What the New Zealand judgments provide. -/
def judgments : Set (World → Prop) := {p, q, qᶜ}

theorem judgments_inconsistent : sInf judgments = ⊥ := by
  funext w; simp [judgments]

/-- Under Definition 5 the inconsistent judgments make (7) true: it must be that murder is
not a crime, by ex falso quodlibet. -/
theorem simpleNecessity_neg_p (w : World) :
    simpleNecessity (Function.const World judgments) pᶜ w := by
  rw [simpleNecessity_iff_sInf_le, Function.const_apply, judgments_inconsistent]; exact bot_le

/-- Under Definition 6 nothing is compatible with the judgments, so (8) is false: deer cannot
be personally responsible. -/
theorem not_simplePossibility_q (w : World) :
    ¬ simplePossibility (Function.const World judgments) q w := by
  rw [simplePossibility_iff_not_disjoint, Function.const_apply, judgments_inconsistent, not_not]
  exact disjoint_bot_left

private theorem judgments_snd : ∀ x ∈ judgments, x ≠ p → ∀ u v : World, u.2 = v.2 →
    (x u ↔ x v) := by
  simp only [judgments, Set.mem_insert_iff, Set.mem_singleton_iff]
  rintro x (rfl | rfl | rfl) h u v huv <;> first | exact absurd rfl h | simp [q, huv]

/-- Definition 7 makes (6) true, murder must be a crime: `p` is compatible with every
consistent subset of the judgments, since making murder a crime at a world of the subset keeps
it there. -/
theorem must_p (w : World) : MustInView (Function.const World judgments) p w := by
  refine mustInView_of_forall_not_disjoint (by simp [judgments]) fun B hB ↦ ?_
  obtain ⟨w₀, hw₀⟩ := sInf_ne_bot_iff.1 hB.2
  exact not_disjoint_sInf_iff.2 ⟨(true, w₀.2),
    forall_mem_of_eq judgments_snd hB.1 hw₀ rfl fun _ ↦ rfl, rfl⟩

/-- Definition 7 makes (7) false: no consistent subset of the judgments entails that murder
is not a crime, since any of its worlds can be moved to one where murder is a crime. -/
theorem not_must_neg_p (w : World) :
    ¬ MustInView (Function.const World judgments) pᶜ w := fun h ↦ by
  obtain ⟨C, hC, -, hle⟩ := h ∅ ⟨Set.empty_subset _, by simp⟩
  obtain ⟨w₀, hw₀⟩ := sInf_ne_bot_iff.1 hC.2
  have hv := forall_mem_of_eq judgments_snd hC.1 hw₀ (v := (true, w₀.2)) rfl fun _ ↦ rfl
  exact hle (true, w₀.2) (by simpa using hv) rfl

/-- Definition 8 makes (8) true: the judgment that deer are responsible is itself a consistent
subset. -/
theorem can_q (w : World) : CanInView (Function.const World judgments) q w :=
  canInView_of_mem (B := {q})
    ⟨by simp [judgments], sInf_ne_bot_iff.2 ⟨(true, true), by simp [q]⟩⟩ rfl

/-- Definition 8 makes (9) true, symmetrically. -/
theorem can_neg_q (w : World) : CanInView (Function.const World judgments) qᶜ w :=
  canInView_of_mem (B := {qᶜ})
    ⟨by simp [judgments], sInf_ne_bot_iff.2 ⟨(true, false), by simp [q]⟩⟩ rfl

/-- Definition 8 makes (13) false, it cannot be that murder is not a crime: the dual of
(6). -/
theorem not_can_neg_p (w : World) :
    ¬ CanInView (Function.const World judgments) pᶜ w :=
  (mustInView_iff_not_canInView_not _ _ _).mp (must_p w)

/-! ### The Whare Wananga recommendations (§2.3)

`p` is that the pupils practise striding and `q` that they practise flying. Te Miti's
recommendation is read once as the single proposition (14), that they do both, and once as
two recommendations; Te Kini's is (15), that they do not stride. -/

/-- Te Miti's recommendation as one proposition, with Te Kini's. -/
def recommendations : Set (World → Prop) := {fun w ↦ p w ∧ q w, pᶜ}

/-- Te Miti's recommendation as two propositions, with Te Kini's. -/
def recommendations' : Set (World → Prop) := {q, p, pᶜ}

/-- On the first reading (16) is false: Te Kini's ban is a consistent subset whose only
consistent extension is itself, and flying does not follow from it. -/
theorem not_must_q (w : World) :
    ¬ MustInView (Function.const World recommendations) q w := fun h ↦ by
  obtain ⟨C, hC, hBC, hle⟩ := h {pᶜ}
    ⟨by simp [recommendations], sInf_ne_bot_iff.2 ⟨(false, false), by simp [p]⟩⟩
  obtain ⟨w₀, hw₀⟩ := sInf_ne_bot_iff.1 hC.2
  have hnp : pᶜ w₀ := hw₀ _ (hBC rfl)
  have hC' : ∀ x ∈ C, x = pᶜ := fun x hx ↦ by
    rcases hC.1 hx with rfl | rfl
    · exact absurd (hw₀ _ hx).1 hnp
    · rfl
  exact absurd (hle (false, false) (by simpa using fun x hx ↦ hC' x hx ▸ by simp [p]))
    (by simp [q])

private theorem recommendations'_fst : ∀ x ∈ recommendations', x ≠ q → ∀ u v : World,
    u.1 = v.1 → (x u ↔ x v) := by
  simp only [recommendations', Set.mem_insert_iff, Set.mem_singleton_iff]
  rintro x (rfl | rfl | rfl) h u v huv <;> first | exact absurd rfl h | simp [p, huv]

/-- On the second reading (16) is true: flying is compatible with every consistent subset. -/
theorem must_q (w : World) : MustInView (Function.const World recommendations') q w := by
  refine mustInView_of_forall_not_disjoint (by simp [recommendations']) fun B hB ↦ ?_
  obtain ⟨w₀, hw₀⟩ := sInf_ne_bot_iff.1 hB.2
  exact not_disjoint_sInf_iff.2 ⟨(w₀.1, true),
    forall_mem_of_eq recommendations'_fst hB.1 hw₀ rfl fun _ ↦ rfl, rfl⟩

end Kratzer1977
