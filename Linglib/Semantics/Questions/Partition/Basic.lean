module

public import Linglib.Core.Data.Setoid.Basic
public import Mathlib.Order.Setoid.Partition

/-!
# Partition questions

This file defines the basic vocabulary of partition questions. A question in the sense of
[groenendijk-stokhof-1984] is a `Setoid W`, its answers the cells; the same object is a subject
matter in the sense of [lewis-1988], and a proposition is entirely about it when the question
decides it, that is, when it is constant on the cells. The polar question whether `p` is the
kernel of the indicator of `p`, a question decides `p` exactly when it refines the polar
question, `Q ≤ polar p`, and the question raised by a family of propositions is the meet of
their polar questions, so a finer question decides more (`le_trans`), the finest question
decides everything (`bot_le`), and a family's question decides each member (`iInf₂_le`). A
question settles the value of a function exactly when it decides each of its fibres
(`le_ker_iff_forall_decides`). Every question is the meet of the polar questions of its cells
(`iInf_polar_cell`), and the nontrivial polar questions are the coatoms of the lattice of
questions (`isCoatom_iff`). A proposition a question decides is [cariani-2013]'s visible,
[phillips-brown-2025]'s considered, and an issue in a subject matter for
[von-fintel-gillies-2010]; the converse relation, a proposition settling a question, is
`Question.Resolves`.

## Main definitions

* `Setoid.cell Q w` — the cell of `w`, an element of `Q.classes`.
* `Setoid.polar p` — the polar question whether `p`.
* `Setoid.Decides Q p` — `Q` decides `p`: `p` is a union of cells.
* `Setoid.ofProps ps` — the question raised by a finite family of propositions.

## References

* [groenendijk-stokhof-1984]
* [lewis-1988]
* [von-fintel-gillies-2010]
* [cariani-2013]
* [phillips-brown-2025]
-/

@[expose] public section

namespace Setoid

variable {W : Type*} (Q : Setoid W) (p q : Set W)

/-! ### Cells -/

/-- The cell of `w` is the set of worlds equivalent to it. -/
def cell (w : W) : Set W := {v | Q v w}

variable {Q p q} {w v : W}

@[simp] theorem mem_cell : v ∈ Q.cell w ↔ Q v w := Iff.rfl

theorem cell_mem_classes (w : W) : Q.cell w ∈ Q.classes := Q.mem_classes w

theorem mem_cell_self (w : W) : w ∈ Q.cell w := Q.refl' w

theorem cell_nonempty (w : W) : (Q.cell w).Nonempty := ⟨w, Q.mem_cell_self w⟩

theorem cell_eq_of_rel (h : Q w v) : Q.cell w = Q.cell v :=
  Set.ext fun _ ↦ ⟨fun h' ↦ Q.trans' h' h, fun h' ↦ Q.trans' h' (Q.symm' h)⟩

variable (Q) in
theorem cell_eq_or_disjoint (w v : W) : Q.cell w = Q.cell v ∨ Disjoint (Q.cell w) (Q.cell v) := by
  by_cases h : Q w v
  · exact Or.inl (cell_eq_of_rel h)
  · exact Or.inr (Set.disjoint_left.2 fun u hw hv ↦ h (Q.trans' (Q.symm' hw) hv))

@[simp] theorem cell_bot (w : W) : (⊥ : Setoid W).cell w = {w} := by
  ext; simp [cell]

theorem cell_inf (Q' : Setoid W) (w : W) : (Q ⊓ Q').cell w = Q.cell w ∩ Q'.cell w :=
  Set.ext fun _ ↦ Setoid.inf_iff_and

instance [DecidableEq W] : DecidableRel (⊥ : Setoid W) :=
  fun v w ↦ decidable_of_iff (v = w) (by rw [Setoid.bot_def])

instance : DecidableRel (⊤ : Setoid W) := fun _ _ ↦ isTrue trivial

instance [DecidableRel Q] : Decidable (v ∈ Q.cell w) := inferInstanceAs (Decidable (Q v w))

instance [Fintype W] [DecidableRel Q] [DecidablePred (· ∈ p)] : Decidable (Q.cell w ⊆ p) :=
  inferInstanceAs (Decidable (∀ v, Q v w → v ∈ p))

/-! ### Polar questions and decided propositions -/

variable (p) in
/-- The polar question whether `p` is the kernel of its indicator. -/
def polar : Setoid W := Setoid.ker (· ∈ p)

theorem polar_iff : polar p w v ↔ (w ∈ p ↔ v ∈ p) := eq_iff_iff

theorem polar_cell_of_mem (hw : w ∈ p) : (polar p).cell w = p := by
  ext v
  simp [hw]

theorem polar_cell_of_notMem (hw : w ∉ p) : (polar p).cell w = pᶜ := by
  ext v
  simp [hw]

@[simp] theorem polar_compl : polar pᶜ = polar p :=
  Setoid.ext fun _ _ ↦ by simp only [polar_iff, Set.mem_compl_iff, not_iff_not]

instance [DecidablePred (· ∈ p)] : DecidableRel (polar p) :=
  fun _ _ ↦ decidable_of_iff _ polar_iff.symm

variable (Q p) in
/-- A question decides `p` when it refines the polar question whether `p`, so that `p` is
constant on its cells and a union of them. -/
def Decides : Prop := Q ≤ polar p

theorem decides_iff : Q.Decides p ↔ ∀ w v, Q w v → (w ∈ p ↔ v ∈ p) :=
  ⟨fun h _ _ hwv ↦ polar_iff.1 (h hwv), fun h _ _ hwv ↦ polar_iff.2 (h _ _ hwv)⟩

/-- Equivalent worlds agree on a decided proposition. -/
theorem Decides.iff (h : Q.Decides p) (hwv : Q w v) : w ∈ p ↔ v ∈ p :=
  decides_iff.1 h w v hwv

theorem decides_iff_forall_cell :
    Q.Decides p ↔ ∀ w, Q.cell w ⊆ p ∨ ∀ v ∈ Q.cell w, v ∉ p := by
  rw [decides_iff]
  refine ⟨fun h w ↦ ?_, fun h w v hwv ↦ ?_⟩
  · by_cases hw : w ∈ p
    · exact Or.inl fun v hv ↦ (h v w hv).2 hw
    · exact Or.inr fun v hv hv' ↦ hw ((h v w hv).1 hv')
  · rcases h v with hall | hnone
    · exact iff_of_true (hall hwv) (hall (Q.refl' v))
    · exact iff_of_false (hnone w hwv) (hnone v (Q.refl' v))

instance [Fintype W] [DecidableRel Q] [DecidablePred (· ∈ p)] : Decidable (Q.Decides p) :=
  decidable_of_iff _ decides_iff.symm

theorem Decides.mono {Q' : Setoid W} (hQ : Q' ≤ Q) (h : Q.Decides p) : Q'.Decides p :=
  hQ.trans h

theorem bot_decides : (⊥ : Setoid W).Decides p := bot_le

theorem polar_decides : (polar p).Decides p := le_rfl

theorem top_decides_iff : (⊤ : Setoid W).Decides p ↔ ∀ w v, (w ∈ p ↔ v ∈ p) := by
  simp [decides_iff, Setoid.top_def]

theorem decides_compl_iff : Q.Decides pᶜ ↔ Q.Decides p := by
  simp only [Decides, polar_compl]

theorem Decides.compl (h : Q.Decides p) : Q.Decides pᶜ := decides_compl_iff.2 h

theorem Decides.inter (hp : Q.Decides p) (hq : Q.Decides q) : Q.Decides (p ∩ q) :=
  decides_iff.2 fun _ _ h ↦ and_congr (decides_iff.1 hp _ _ h) (decides_iff.1 hq _ _ h)

theorem Decides.union (hp : Q.Decides p) (hq : Q.Decides q) : Q.Decides (p ∪ q) :=
  decides_iff.2 fun _ _ h ↦ or_congr (decides_iff.1 hp _ _ h) (decides_iff.1 hq _ _ h)

theorem decides_cell (w : W) : Q.Decides (Q.cell w) :=
  decides_iff.2 fun _ _ hab ↦ ⟨fun h ↦ Q.trans (Q.symm hab) h, fun h ↦ Q.trans hab h⟩

theorem Decides.cell_subset (h : Q.Decides p) (hw : w ∈ p) : Q.cell w ⊆ p :=
  fun _ hv ↦ (decides_iff.1 h _ _ hv).2 hw

theorem le_ker_iff_forall_decides {β : Type*} {f : W → β} :
    Q ≤ ker f ↔ ∀ b, Q.Decides (f ⁻¹' {b}) :=
  ⟨fun h _ ↦ decides_iff.2 fun _ _ hwv ↦ by simp [ker_def.1 (h hwv)],
    fun h w _ hwv ↦ (((h (f w)).iff hwv).1 rfl).symm⟩

/-! ### Polar questions as coatoms -/

variable (Q) in
theorem iInf_polar_cell : ⨅ w, polar (Q.cell w) = Q := by
  ext v u
  simp only [Setoid.iInf_iff, polar_iff, mem_cell]
  exact ⟨fun h ↦ (h u).2 (Q.refl' u), fun h w ↦ ⟨fun hv ↦ Q.trans' (Q.symm' h) hv, Q.trans' h⟩⟩

theorem polar_ne_top (hp : p.Nonempty) (hp' : p ≠ Set.univ) : polar p ≠ ⊤ := fun h ↦ by
  obtain ⟨v, hv⟩ := hp
  obtain ⟨u, hu⟩ := (Set.ne_univ_iff_exists_notMem p).1 hp'
  exact hu ((polar_iff.1 (show polar p v u from h ▸ trivial)).1 hv)

theorem isCoatom_polar (hp : p.Nonempty) (hp' : p ≠ Set.univ) : IsCoatom (polar p) := by
  refine ⟨polar_ne_top hp hp', fun R hR ↦ Setoid.eq_top_iff.2 fun x y ↦ ?_⟩
  obtain ⟨a, b, hab, h⟩ : ∃ a b, R a b ∧ ¬ polar p a b := by
    simpa [Setoid.le_def] using hR.not_ge
  have hle := @hR.le
  simp only [Setoid.le_def, polar_iff] at h hle
  grind [Setoid.trans', Setoid.symm']

theorem isCoatom_iff : IsCoatom Q ↔ ∃ p : Set W, p.Nonempty ∧ p ≠ Set.univ ∧ Q = polar p := by
  refine ⟨fun h ↦ ?_, fun ⟨p, hp, hp', e⟩ ↦ e ▸ isCoatom_polar hp hp'⟩
  obtain ⟨w, hw⟩ : ∃ w, Q.cell w ≠ Set.univ := by
    by_contra hall
    push Not at hall
    exact h.1 (Setoid.eq_top_iff.2 fun x y ↦ show x ∈ Q.cell y from (hall y) ▸ Set.mem_univ x)
  exact ⟨Q.cell w, ⟨w, mem_cell_self w⟩, hw,
    ((h.le_iff.1 (decides_cell w)).resolve_left (polar_ne_top ⟨w, mem_cell_self w⟩ hw)).symm⟩

/-! ### The question raised by a family of propositions -/

variable (ps : Finset (Finset W))

/-- The question raised by a family of propositions is the meet of their polar questions, the
coarsest question deciding each of them. -/
def ofProps : Setoid W := ⨅ p ∈ ps, polar (↑p : Set W)

theorem ofProps_iff : ofProps ps w v ↔ ∀ p ∈ ps, (w ∈ p ↔ v ∈ p) := by
  simp only [Setoid.iInf_iff, polar_iff, Finset.mem_coe]

instance [DecidableEq W] : DecidableRel (ofProps ps) :=
  fun _ _ ↦ decidable_of_iff _ (ofProps_iff ps).symm

theorem ofProps_decides {p : Finset W} (hp : p ∈ ps) : (ofProps ps).Decides ↑p :=
  iInf₂_le p hp

theorem le_ofProps_iff : Q ≤ ofProps ps ↔ ∀ p ∈ ps, Q.Decides ↑p :=
  le_iInf₂_iff

end Setoid
