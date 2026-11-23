module

public import Linglib.Core.Data.Setoid.Basic
public import Mathlib.Order.Setoid.Partition

/-!
# Partition questions

A partition question divides the worlds into cells and asks which cell the actual world is in. We
represent it by an equivalence relation `Q : Setoid W`: two worlds are equivalent when the question
does not distinguish them. The cell `Q.cell w` is the set of worlds equivalent to `w`, and it is the
true answer at `w`. This is the notion of question of [groenendijk-stokhof-1984].

Questions are ordered by refinement: `Q ≤ Q'` means that `Q` distinguishes every pair of worlds that
`Q'` does. The simplest question is the polar question `Setoid.polar p`, which asks only whether the
proposition `p` holds.

A question determines a proposition `p` when learning the answer always settles whether `p` holds,
that is, when `p` is a union of cells. We write this `Q.Determines p`. It is the same as
`Q ≤ Setoid.polar p`.

## References

* [groenendijk-stokhof-1984]
* [lewis-1988]
* [ciardelli-2022]
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

theorem cell_ker {β : Type*} (f : W → β) (w : W) : (ker f).cell w = f ⁻¹' {f w} := rfl

variable (Q) in
theorem cell_eq_or_disjoint (w v : W) : Q.cell w = Q.cell v ∨ Disjoint (Q.cell w) (Q.cell v) := by
  by_cases h : Q w v
  · exact Or.inl (cell_eq_of_rel h)
  · exact Or.inr (Set.disjoint_left.2 fun u hw hv ↦ h (Q.trans' (Q.symm' hw) hv))

/-- The cell of `w` is the fibre of the quotient map through `w`. -/
theorem cell_eq_preimage_mk (w : W) : Q.cell w = Quotient.mk Q ⁻¹' {Quotient.mk Q w} :=
  Set.ext fun _ ↦ Quotient.eq.symm

@[simp] theorem cell_bot (w : W) : (⊥ : Setoid W).cell w = {w} := by
  ext; simp [cell]

@[simp] theorem cell_top (w : W) : (⊤ : Setoid W).cell w = Set.univ := by
  ext; simp [cell, Setoid.top_def]

theorem cell_inf (Q' : Setoid W) (w : W) : (Q ⊓ Q').cell w = Q.cell w ∩ Q'.cell w :=
  Set.ext fun _ ↦ Setoid.inf_iff_and

instance [DecidableEq W] : DecidableRel (⊥ : Setoid W) :=
  fun v w ↦ decidable_of_iff (v = w) (by rw [Setoid.bot_def])

instance : DecidableRel (⊤ : Setoid W) := fun _ _ ↦ isTrue trivial

instance [DecidableRel Q] : Decidable (v ∈ Q.cell w) := inferInstanceAs (Decidable (Q v w))

instance [Fintype W] [DecidableRel Q] [DecidablePred (· ∈ p)] : Decidable (Q.cell w ⊆ p) :=
  inferInstanceAs (Decidable (∀ v, Q v w → v ∈ p))

/-! ### Polar questions and determined propositions -/

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

/-- The cells of a polar question are the proposition and its complement, when nonempty. -/
theorem mem_classes_polar_iff {s : Set W} :
    s ∈ (polar p).classes ↔ s.Nonempty ∧ (s = p ∨ s = pᶜ) := by
  refine ⟨?_, fun ⟨⟨w, hw⟩, h⟩ ↦ ⟨w, ?_⟩⟩
  · rintro ⟨w, rfl⟩
    refine ⟨⟨w, (polar p).refl' w⟩, ?_⟩
    by_cases hw : w ∈ p
    · exact .inl (polar_cell_of_mem hw)
    · exact .inr (polar_cell_of_notMem hw)
  · rcases h with rfl | rfl
    · exact (polar_cell_of_mem hw).symm
    · exact (polar_cell_of_notMem hw).symm

/-- Two propositions raise the same polar question exactly when they are equal or
complementary. -/
theorem polar_eq_polar_iff : polar p = polar q ↔ p = q ∨ p = qᶜ := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · rcases p.eq_empty_or_nonempty with rfl | ⟨w, hw⟩
    · rcases q.eq_empty_or_nonempty with rfl | ⟨w, hw⟩
      · exact .inl rfl
      · have := congrArg (·.cell w) h
        simp only [polar_cell_of_mem hw, polar_cell_of_notMem (Set.notMem_empty w)] at this
        exact .inr (by rw [← this, compl_compl])
    · have := congrArg (·.cell w) h
      by_cases hq : w ∈ q
      · exact .inl (by simpa only [polar_cell_of_mem hw, polar_cell_of_mem hq] using this)
      · exact .inr (by simpa only [polar_cell_of_mem hw, polar_cell_of_notMem hq] using this)
  · rintro (rfl | rfl)
    · rfl
    · exact polar_compl

instance [DecidablePred (· ∈ p)] : DecidableRel (polar p) :=
  fun _ _ ↦ decidable_of_iff _ polar_iff.symm

variable (Q p) in
/-- A question determines `p` when it refines the polar question whether `p`, so that `p` is
constant on its cells and a union of them. -/
def Determines : Prop := Q ≤ polar p

theorem determines_iff : Q.Determines p ↔ ∀ w v, Q w v → (w ∈ p ↔ v ∈ p) :=
  ⟨fun h _ _ hwv ↦ polar_iff.1 (h hwv), fun h _ _ hwv ↦ polar_iff.2 (h _ _ hwv)⟩

/-- Equivalent worlds agree on a determined proposition. -/
theorem Determines.iff (h : Q.Determines p) (hwv : Q w v) : w ∈ p ↔ v ∈ p :=
  determines_iff.1 h w v hwv

theorem determines_iff_forall_cell :
    Q.Determines p ↔ ∀ w, Q.cell w ⊆ p ∨ ∀ v ∈ Q.cell w, v ∉ p := by
  rw [determines_iff]
  refine ⟨fun h w ↦ ?_, fun h w v hwv ↦ ?_⟩
  · by_cases hw : w ∈ p
    · exact Or.inl fun v hv ↦ (h v w hv).2 hw
    · exact Or.inr fun v hv hv' ↦ hw ((h v w hv).1 hv')
  · rcases h v with hall | hnone
    · exact iff_of_true (hall hwv) (hall (Q.refl' v))
    · exact iff_of_false (hnone w hwv) (hnone v (Q.refl' v))

instance [Fintype W] [DecidableRel Q] [DecidablePred (· ∈ p)] : Decidable (Q.Determines p) :=
  decidable_of_iff _ determines_iff.symm

theorem Determines.mono {Q' : Setoid W} (hQ : Q' ≤ Q) (h : Q.Determines p) : Q'.Determines p :=
  hQ.trans h

theorem bot_determines : (⊥ : Setoid W).Determines p := bot_le

theorem polar_determines : (polar p).Determines p := le_rfl

theorem top_determines_iff : (⊤ : Setoid W).Determines p ↔ ∀ w v, (w ∈ p ↔ v ∈ p) := by
  simp [determines_iff, Setoid.top_def]

theorem determines_compl_iff : Q.Determines pᶜ ↔ Q.Determines p := by
  simp only [Determines, polar_compl]

theorem Determines.compl (h : Q.Determines p) : Q.Determines pᶜ := determines_compl_iff.2 h

theorem Determines.inter (hp : Q.Determines p) (hq : Q.Determines q) : Q.Determines (p ∩ q) :=
  determines_iff.2 fun _ _ h ↦ and_congr (determines_iff.1 hp _ _ h) (determines_iff.1 hq _ _ h)

theorem Determines.union (hp : Q.Determines p) (hq : Q.Determines q) : Q.Determines (p ∪ q) :=
  determines_iff.2 fun _ _ h ↦ or_congr (determines_iff.1 hp _ _ h) (determines_iff.1 hq _ _ h)

theorem determines_cell (w : W) : Q.Determines (Q.cell w) :=
  determines_iff.2 fun _ _ hab ↦ ⟨fun h ↦ Q.trans (Q.symm hab) h, fun h ↦ Q.trans hab h⟩

theorem Determines.cell_subset (h : Q.Determines p) (hw : w ∈ p) : Q.cell w ⊆ p :=
  fun _ hv ↦ (determines_iff.1 h _ _ hv).2 hw

/-- The cell of a member of `p` is `p` when `p` lies in that cell and `Q` determines `p`. -/
theorem cell_eq_iff (hw : w ∈ p) : Q.cell w = p ↔ p ⊆ Q.cell w ∧ Q.Determines p :=
  ⟨fun h ↦ ⟨h.ge, h ▸ determines_cell w⟩, fun h ↦ (h.2.cell_subset hw).antisymm h.1⟩

/-- The polar question whether `p` is the coarsest question with `p` as a cell. -/
theorem isGreatest_polar (hw : w ∈ p) : IsGreatest {Q : Setoid W | Q.cell w = p} (polar p) :=
  ⟨polar_cell_of_mem hw, fun _ hQ ↦ hQ ▸ determines_cell w⟩

theorem le_ker_iff_forall_determines {β : Type*} {f : W → β} :
    Q ≤ ker f ↔ ∀ b, Q.Determines (f ⁻¹' {b}) :=
  ⟨fun h _ ↦ determines_iff.2 fun _ _ hwv ↦ by simp [ker_def.1 (h hwv)],
    fun h w _ hwv ↦ (((h (f w)).iff hwv).1 rfl).symm⟩

/-! ### Determination relative to a set of worlds -/

variable (Q p) in
/-- A question determines `p` on `c` when `p` is constant on the part of each cell inside `c`. -/
def DeterminesOn (c : Set W) : Prop := ∀ ⦃w⦄, w ∈ c → ∀ ⦃v⦄, v ∈ c → Q w v → (w ∈ p ↔ v ∈ p)

theorem Determines.determinesOn (h : Q.Determines p) (c : Set W) : Q.DeterminesOn p c :=
  fun _ _ _ _ hwv ↦ h.iff hwv

@[simp] theorem determinesOn_univ : Q.DeterminesOn p Set.univ ↔ Q.Determines p :=
  ⟨fun h ↦ determines_iff.2 fun _ _ hwv ↦ h trivial trivial hwv, fun h ↦ h.determinesOn _⟩

theorem DeterminesOn.mono {c c' : Set W} (h : Q.DeterminesOn p c) (hc : c' ⊆ c) :
    Q.DeterminesOn p c' :=
  fun _ hw _ hv ↦ h (hc hw) (hc hv)

theorem DeterminesOn.mono_left {Q' : Setoid W} {c : Set W} (h : Q.DeterminesOn p c)
    (hQ : Q' ≤ Q) : Q'.DeterminesOn p c :=
  fun _ hw _ hv hwv ↦ h hw hv (hQ hwv)

theorem DeterminesOn.compl {c : Set W} (h : Q.DeterminesOn p c) : Q.DeterminesOn pᶜ c :=
  fun _ hw _ hv hwv ↦ not_congr (h hw hv hwv)

theorem DeterminesOn.inter {c : Set W} (hp : Q.DeterminesOn p c) (hq : Q.DeterminesOn q c) :
    Q.DeterminesOn (p ∩ q) c :=
  fun _ hw _ hv hwv ↦ and_congr (hp hw hv hwv) (hq hw hv hwv)

theorem DeterminesOn.union {c : Set W} (hp : Q.DeterminesOn p c) (hq : Q.DeterminesOn q c) :
    Q.DeterminesOn (p ∪ q) c :=
  fun _ hw _ hv hwv ↦ or_congr (hp hw hv hwv) (hq hw hv hwv)

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
    ((h.le_iff.1 (determines_cell w)).resolve_left (polar_ne_top ⟨w, mem_cell_self w⟩ hw)).symm⟩

end Setoid
