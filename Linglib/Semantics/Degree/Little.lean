module

public import Linglib.Semantics.Degree.Quantifier

/-!
# Degree negation and its scope

The degree word *little* negates a degree property: *`d` little* holds of a set of degrees `P`
when `d ∉ P`, so that abstracting over `d` gives the complement `Pᶜ`. Of the degrees `Set.Iic a`
that an object measuring `a` reaches it leaves `Set.Ioi a`, the degrees it falls short of.

Under a quantifier `Q` the negation applies to each entity's degree property or to the degrees at
which `Q` holds. A comparative says that the than-clause degrees are properly included in the
matrix degrees, and *less* is the comparative of *little*, so for a matrix subject measuring `c`
and a than-clause with the quantifier `Q` and the measure `μ` we define

* `Quantifier.LittleBelow Q μ c`, with the negation below `Q`, as
  `scopeDegrees Q (fun x ↦ (Iic (μ x))ᶜ) ⊂ (Iic c)ᶜ`;
* `Quantifier.LittleAbove Q μ c`, with the negation above `Q`, as
  `(scopeDegrees Q (Iic ∘ μ))ᶜ ⊂ (Iic c)ᶜ`.

A negation below a quantifier is a negation above its dual,
`Quantifier.littleBelow_iff_littleAbove_dual`, so the two coincide under a quantifier that is its
own dual, `Quantifier.littleBelow_iff_littleAbove_of_dual_eq`, as an individual is. Above a
monotone quantifier the comparative says that `Q` holds of the entities measuring at least `e`
for some `e` above `c`, `Quantifier.littleAbove_iff`. On a complete scale that puts `c` below
the supremum of the degrees `Q` reaches, `Quantifier.littleAbove_iff_lt_sSup`, which is the
infimum of the measures for *every* and their supremum for *some*. The comparative is monotone
in `Q`, so under a quantifier that entails its dual the negation above entails the negation
below, `Quantifier.LittleAbove.littleBelow`.

## References

* [heim-2006]
* [rullmann-1995]
* [buring-2007]
-/

@[expose] public section

open Set Quantifier.Det

namespace Quantifier

variable {α D : Type*} [LinearOrder D] {Q : Quantifier α} {μ : α → D} {c m : D} {A : Set α}
  {a : α}

/-- The *less*-comparative of a subject measuring `c` with the degree negation of its than-clause
above the quantifier `Q`. -/
def LittleAbove (Q : Quantifier α) (μ : α → D) (c : D) : Prop :=
  (scopeDegrees Q (Iic ∘ μ))ᶜ ⊂ (Iic c)ᶜ

/-- The *less*-comparative of a subject measuring `c` with the degree negation of its than-clause
below the quantifier `Q`. -/
def LittleBelow (Q : Quantifier α) (μ : α → D) (c : D) : Prop :=
  scopeDegrees Q (fun x ↦ (Iic (μ x))ᶜ) ⊂ (Iic c)ᶜ

/-- A degree negation below a quantifier is a degree negation above its dual. -/
theorem littleBelow_iff_littleAbove_dual : LittleBelow Q μ c ↔ LittleAbove Q.dual μ c := by
  rw [LittleAbove, scopeDegrees_dual, compl_compl]
  rfl

/-- Under a quantifier that is its own dual, an individual or any ultrafilter, the scope of the
degree negation makes no difference. -/
theorem littleBelow_iff_littleAbove_of_dual_eq (h : Q.dual = Q) :
    LittleBelow Q μ c ↔ LittleAbove Q μ c := by
  rw [littleBelow_iff_littleAbove_dual, h]

theorem littleAbove_iff (hQ : Monotone Q) :
    LittleAbove Q μ c ↔ ∃ e, c < e ∧ Q {x | e ≤ μ x} := by
  refine compl_lt_compl_iff_lt.trans ⟨fun h ↦ ?_, fun ⟨e, hce, he⟩ ↦ ⟨fun e' he' ↦ ?_, fun h ↦ ?_⟩⟩
  · obtain ⟨e, he, hec⟩ := exists_of_ssubset h
    exact ⟨e, not_le.mp hec, he⟩
  · exact hQ (fun x hx ↦ (he'.trans hce.le).trans hx) he
  · exact hce.not_ge (h he)

theorem littleBelow_iff (hQ : Monotone Q) :
    LittleBelow Q μ c ↔ ∃ e, c < e ∧ ¬ Q {x | μ x < e} := by
  rw [littleBelow_iff_littleAbove_dual, littleAbove_iff (monotone_dual hQ)]
  simp [Set.compl_ofPred]

theorem LittleAbove.mono {Q' : Quantifier α} (hQ : Monotone Q) (hQ' : Monotone Q') (h : Q ≤ Q')
    (hc : LittleAbove Q μ c) : LittleAbove Q' μ c :=
  let ⟨e, hce, he⟩ := (littleAbove_iff hQ).mp hc
  (littleAbove_iff hQ').mpr ⟨e, hce, h _ he⟩

/-- Under a monotone quantifier that entails its dual, the comparative with the negation above
the quantifier entails the one with the negation below it. -/
theorem LittleAbove.littleBelow (hQ : Monotone Q) (h : Q ≤ Q.dual) (hc : LittleAbove Q μ c) :
    LittleBelow Q μ c :=
  littleBelow_iff_littleAbove_dual.mpr (hc.mono hQ (monotone_dual hQ) h)

/-- Over finitely many entities, the comparative with the negation above a monotone quantifier
says that the quantifier holds of the entities measuring more than the subject. -/
theorem littleAbove_iff_of_finite [Finite α] (hQ : Monotone Q) (hQ₀ : ¬ Q ⊥) :
    LittleAbove Q μ c ↔ Q {x | c < μ x} :=
  (littleAbove_iff hQ).trans
    ⟨fun ⟨_, hce, he⟩ ↦ hQ (fun _ hx ↦ hce.trans_le hx) he, fun h ↦
      let ⟨e, hce, he⟩ := highScope_of_lowScope hQ hQ₀ (IsUpperSet.Ioi c) (lowScope_maxIn.2 h)
      ⟨e, hce, he.1⟩⟩

theorem littleAbove_iff_highScope (hQ : Monotone Q)
    (h : ∃ m, IsGreatest (scopeDegrees Q (Iic ∘ μ)) m) :
    LittleAbove Q μ c ↔ HighScope (MaxIn (Ioi c)) Q (Iic ∘ μ) :=
  let ⟨m, hm⟩ := h
  (littleAbove_iff hQ).trans
    ⟨fun ⟨_, hce, he⟩ ↦ ⟨m, hce.trans_le (hm.2 he), hm⟩, fun ⟨e, hce, he⟩ ↦ ⟨e, hce, he.1⟩⟩

/-! ### Without a quantifier -/

theorem littleAbove_individual : LittleAbove (individual a) μ c ↔ c < μ a :=
  compl_lt_compl_iff_lt.trans Iic_ssubset_Iic

theorem littleBelow_individual : LittleBelow (individual a) μ c ↔ c < μ a :=
  (littleBelow_iff_littleAbove_of_dual_eq (dual_individual a)).trans littleAbove_individual

/-! ### Universal and existential quantifiers -/

theorem littleAbove_every : LittleAbove (every A) μ c ↔ ∃ e, c < e ∧ e ∈ lowerBounds (μ '' A) :=
  (littleAbove_iff (monotone_every A)).trans <|
    exists_congr fun _ ↦ and_congr_right fun _ ↦ (mem_lowerBounds.trans forall_mem_image).symm

theorem littleAbove_some : LittleAbove (Det.some A) μ c ↔ ∃ x ∈ A, c < μ x :=
  (littleAbove_iff (monotone_some A)).trans
    ⟨fun ⟨_, hce, x, hx, he⟩ ↦ ⟨x, hx, hce.trans_le he⟩, fun ⟨x, hx, hc⟩ ↦ ⟨_, hc, x, hx, le_rfl⟩⟩

theorem littleBelow_every : LittleBelow (every A) μ c ↔ ∃ x ∈ A, c < μ x := by
  rw [littleBelow_iff_littleAbove_dual, ← dual_apply', dual_every, littleAbove_some]

theorem littleBelow_some :
    LittleBelow (Det.some A) μ c ↔ ∃ e, c < e ∧ e ∈ lowerBounds (μ '' A) := by
  rw [littleBelow_iff_littleAbove_dual, ← dual_apply', dual_some, littleAbove_every]

theorem littleAbove_every_iff_of_isGLB (h : IsGLB (μ '' A) m) :
    LittleAbove (every A) μ c ↔ c < m :=
  littleAbove_every.trans ⟨fun ⟨_, hce, he⟩ ↦ hce.trans_le (h.2 he), fun hc ↦ ⟨m, hc, h.1⟩⟩

theorem littleAbove_some_iff_of_isLUB (h : IsLUB (μ '' A) m) :
    LittleAbove (Det.some A) μ c ↔ c < m :=
  littleAbove_some.trans <| exists_mem_image.symm.trans (lt_isLUB_iff h).symm

theorem littleBelow_every_iff_of_isLUB (h : IsLUB (μ '' A) m) :
    LittleBelow (every A) μ c ↔ c < m := by
  rw [littleBelow_iff_littleAbove_dual, ← dual_apply', dual_every, littleAbove_some_iff_of_isLUB h]

theorem littleBelow_some_iff_of_isGLB (h : IsGLB (μ '' A) m) :
    LittleBelow (Det.some A) μ c ↔ c < m := by
  rw [littleBelow_iff_littleAbove_dual, ← dual_apply', dual_some, littleAbove_every_iff_of_isGLB h]

/-- Over a nonempty set, the comparative with the negation above *every* entails the one with
the negation above *some*. -/
theorem LittleAbove.some_of_every (hA : A.Nonempty) (h : LittleAbove (every A) μ c) :
    LittleAbove (Det.some A) μ c :=
  h.mono (monotone_every A) (monotone_some A) fun _ hB ↦ let ⟨x, hx⟩ := hA; ⟨x, hx, hB hx⟩

/-! ### On a complete scale

The degrees a monotone quantifier reaches have a supremum, the infimum of the measures for
*every* and their supremum for *some*, and the comparative puts the subject below it. -/

section CompleteLinearOrder

variable {D : Type*} [CompleteLinearOrder D] {Q : Quantifier α} {μ : α → D} {c : D} {A : Set α}

/-- On a complete scale, the comparative with the negation above a monotone quantifier puts the
subject below the supremum of the degrees the quantifier reaches. -/
theorem littleAbove_iff_lt_sSup (hQ : Monotone Q) :
    LittleAbove Q μ c ↔ c < sSup (scopeDegrees Q (Iic ∘ μ)) :=
  (littleAbove_iff hQ).trans
    ⟨fun ⟨e, hce, he⟩ ↦ lt_sSup_iff.mpr ⟨e, he, hce⟩,
      fun h ↦ let ⟨e, he, hce⟩ := lt_sSup_iff.mp h; ⟨e, hce, he⟩⟩

theorem littleBelow_iff_lt_sSup (hQ : Monotone Q) :
    LittleBelow Q μ c ↔ c < sSup (scopeDegrees Q.dual (Iic ∘ μ)) :=
  littleBelow_iff_littleAbove_dual.trans (littleAbove_iff_lt_sSup (monotone_dual hQ))

theorem littleAbove_every_iff_lt_sInf : LittleAbove (every A) μ c ↔ c < sInf (μ '' A) := by
  rw [littleAbove_iff_lt_sSup (monotone_every A), sSup_scopeDegrees_every]

theorem littleAbove_some_iff_lt_sSup : LittleAbove (Det.some A) μ c ↔ c < sSup (μ '' A) := by
  rw [littleAbove_iff_lt_sSup (monotone_some A), sSup_scopeDegrees_some]

end CompleteLinearOrder

end Quantifier
