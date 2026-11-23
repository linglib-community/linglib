module

public import Linglib.Core.Data.List.Infix
public import Linglib.Core.Order.GornAddress
public import Linglib.Syntax.Projection.Basic

/-!
# Projection on Gorn addresses

On the positions of an ordered tree a head relation is given by the index of each position's head
daughter, `hd : GornAddress → Option ℕ`. The head relation, the levels of projection and the
maximal projection of a position are then decidable, and a set of segment positions splits the
head relation into projection and adjunction.

## Main definitions

* `PhraseStructure.headDaughterRel`: the head relation of a head-daughter index.
* `PhraseStructure.maximalProjectionAt`: the maximal projection of a position, computed by walking
  up while the position is its mother's head daughter.
* `PhraseStructure.projectionIndex`, `PhraseStructure.adjunctionIndex`: the head-daughter index
  away from the segment positions, and at them.

## Main results

* `PhraseStructure.isLeast_maximalProjectionAt`: `maximalProjectionAt` computes the maximal
  projection.
* `PhraseStructure.headDaughterRel_eq_sup`: the head relation is the join of projection and
  adjunction.

## References

* [gorn-1967]
* [barker-pullum-1990]
-/

@[expose] public section

namespace PhraseStructure

open scoped SetRel

/-! ### Head daughters at tree positions -/

section Positions


variable (hd : GornAddress → Option ℕ)

/-- `headDaughterRel hd m d` says that `d` is the daughter of `m` at the index `hd m`. -/
def headDaughterRel (m d : GornAddress) : Prop := ∃ i, hd m = some i ∧ d.toList = m.toList ++ [i]

instance : DecidableRel (headDaughterRel hd) := fun m d ↦
  match h : hd m with
  | none => isFalse (by rintro ⟨i, hi, -⟩; rw [h] at hi; cases hi)
  | some i => decidable_of_iff (d.toList = m.toList ++ [i])
      ⟨fun hd' ↦ ⟨i, h, hd'⟩, fun ⟨j, hj, hd'⟩ ↦ by rw [h] at hj; cases hj; exact hd'⟩

theorem headDaughterRel_covBy {m d : GornAddress} (h : headDaughterRel hd m d) : m ⋖ d :=
  GornAddress.covBy_iff.2 ⟨h.choose, GornAddress.ext h.choose_spec.2⟩

theorem headDaughterRel_rightUnique : Relator.RightUnique (headDaughterRel hd) := by
  rintro m d d' ⟨i, hi, hd⟩ ⟨j, hj, hd'⟩
  rw [hi] at hj
  cases hj
  exact GornAddress.ext (hd.trans hd'.symm)

theorem isMinimalProjection_headDaughterRel_iff {p : GornAddress} :
    IsMinimalProjection (headDaughterRel hd) p ↔ hd p = none := by
  constructor
  · intro h
    cases hp : hd p with
    | none => rfl
    | some i => exact absurd ⟨i, hp, rfl⟩ (h (p * .of i))
  · rintro h d ⟨i, hi, -⟩
    rw [h] at hi
    cases hi

instance (p : GornAddress) : Decidable (IsMinimalProjection (headDaughterRel hd) p) :=
  decidable_of_iff _ (isMinimalProjection_headDaughterRel_iff hd).symm

theorem isMaximalProjection_headDaughterRel_iff {p : GornAddress} :
    IsMaximalProjection (headDaughterRel hd) p ↔ ¬ headDaughterRel hd p.parent p := by
  refine ⟨fun h ↦ h _, fun h m hm ↦ h ?_⟩
  obtain rfl : m = p.parent := by
    obtain ⟨i, -, hi⟩ := hm
    exact GornAddress.ext (by simp [hi])
  exact hm

instance (p : GornAddress) : Decidable (IsMaximalProjection (headDaughterRel hd) p) :=
  decidable_of_iff _ (isMaximalProjection_headDaughterRel_iff hd).symm

theorem isProjectionOf_headDaughterRel_iff {h p : GornAddress} :
    IsProjectionOf (headDaughterRel hd) h p ↔
      p ≤ h ∧ ∀ q ∈ h.inits, p < q → headDaughterRel hd q.parent q := by
  have hH : ∀ m d, headDaughterRel hd m d → m ⋖ d := fun _ _ ↦ headDaughterRel_covBy hd
  constructor
  · intro hp
    refine ⟨hp.le hH, fun q hq hpq ↦ ?_⟩
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hq
    have hqh : (⟨l⟩ : GornAddress) ≤ h := GornAddress.le_def.mpr ((List.mem_inits _ _).mp hl)
    obtain ⟨m, hm⟩ := hp.exists_of_lt hH (hp.of_le_of_le hH hpq.le hqh) hpq
    have : m = GornAddress.parent ⟨l⟩ := by
      obtain ⟨i, -, hi⟩ := hm
      have hi' : l = m.toList ++ [i] := hi
      exact GornAddress.ext (by rw [GornAddress.parent_toList, hi', List.dropLast_concat])
    exact this ▸ hm
  · rintro ⟨hph, hall⟩
    obtain ⟨s, hs⟩ := GornAddress.le_def.mp hph
    obtain ⟨p⟩ := p
    obtain ⟨h⟩ := h
    simp only at hs
    subst hs
    suffices key : ∀ s, (∀ q ∈ (p ++ s).inits.map GornAddress.mk, (⟨p⟩ : GornAddress) < q →
        headDaughterRel hd q.parent q) → IsProjectionOf (headDaughterRel hd) ⟨p ++ s⟩ ⟨p⟩ from
      key s hall
    intro s
    induction s using List.reverseRecOn with
    | nil => intro _; simpa using IsProjectionOf.refl (H := headDaughterRel hd) ⟨p⟩
    | append_singleton s i ih =>
      intro hall
      rw [← List.append_assoc] at hall ⊢
      refine Relation.ReflTransGen.tail (ih fun q hq hpq ↦ hall q ?_ hpq) ?_
      · obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hq
        exact List.mem_map.mpr ⟨l, (List.mem_inits _ _).mpr
          (((List.mem_inits _ _).mp hl).trans (List.prefix_append _ _)), rfl⟩
      · have hlt : (⟨p⟩ : GornAddress) < ⟨p ++ s ++ [i]⟩ :=
          lt_of_le_of_ne (GornAddress.le_def.mpr (by simp)) fun e ↦ by
            simpa using congrArg (fun q : GornAddress ↦ q.toList.length) e
        have := hall ⟨p ++ s ++ [i]⟩
          (List.mem_map.mpr ⟨_, (List.mem_inits _ _).mpr List.prefix_rfl, rfl⟩) hlt
        have hpar : (⟨p ++ s ++ [i]⟩ : GornAddress).parent = ⟨p ++ s⟩ := GornAddress.ext (by simp)
        rwa [hpar] at this

instance (h p : GornAddress) : Decidable (IsProjectionOf (headDaughterRel hd) h p) :=
  decidable_of_iff _ (isProjectionOf_headDaughterRel_iff hd).symm

instance (h p : GornAddress) : Decidable (IsLexicalHeadOf (headDaughterRel hd) h p) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The maximal projection of `h` is the lowest maximal projection dominating it. -/
def maximalProjectionAt (h : GornAddress) : GornAddress :=
  h.take (Nat.findGreatest (fun n ↦ IsMaximalProjection (headDaughterRel hd) (h.take n)) h.depth)

theorem maximalProjectionAt_le (h : GornAddress) : maximalProjectionAt hd h ≤ h :=
  GornAddress.take_le _ h

theorem isMaximalProjection_maximalProjectionAt (h : GornAddress) :
    IsMaximalProjection (headDaughterRel hd) (maximalProjectionAt hd h) :=
  Nat.findGreatest_spec (P := fun n ↦ IsMaximalProjection (headDaughterRel hd) (h.take n))
    (Nat.zero_le _) fun _ ⟨_, _, hi⟩ ↦ by simp at hi

/-- `maximalProjectionAt hd h` is the least projection of `h`. -/
theorem isLeast_maximalProjectionAt (h : GornAddress) :
    IsLeast {p | IsProjectionOf (headDaughterRel hd) h p} (maximalProjectionAt hd h) := by
  refine (isLeast_projections_iff fun _ _ ↦ headDaughterRel_covBy hd).2
    ⟨(isProjectionOf_headDaughterRel_iff hd).2 ⟨maximalProjectionAt_le hd h, ?_⟩,
      isMaximalProjection_maximalProjectionAt hd h⟩
  rintro _ hq hlt
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hq
  have hl' := List.prefix_iff_eq_take.1 ((List.mem_inits _ _).1 hl)
  have hfg := Nat.findGreatest_is_greatest (k := l.length)
    (by simpa [maximalProjectionAt, Nat.findGreatest_le, GornAddress.depth] using
      GornAddress.depth_strictMono hlt)
    ((List.mem_inits _ _).1 hl).length_le
  rw [show h.take l.length = ⟨l⟩ from GornAddress.ext hl'.symm] at hfg
  by_contra hne
  exact hfg ((isMaximalProjection_headDaughterRel_iff hd).2 hne)

theorem isProjectionOf_maximalProjectionAt (h : GornAddress) :
    IsProjectionOf (headDaughterRel hd) h (maximalProjectionAt hd h) :=
  (isLeast_maximalProjectionAt hd h).1

/-! #### Projection and adjunction at positions -/

variable (seg : GornAddress → Prop) [DecidablePred seg]

/-- The head daughter of a position that is not a segment, a projection step. -/
def projectionIndex (p : GornAddress) : Option ℕ := if seg p then none else hd p

/-- The head daughter of a segment, its host. -/
def adjunctionIndex (p : GornAddress) : Option ℕ := if seg p then hd p else none

theorem headDaughterRel_eq_sup :
    headDaughterRel hd =
      headDaughterRel (projectionIndex hd seg) ⊔ headDaughterRel (adjunctionIndex hd seg) := by
  ext m d
  simp only [headDaughterRel, projectionIndex, adjunctionIndex, Pi.sup_apply]
  by_cases h : seg m <;> simp [h]

theorem not_projection_of_adjunction {m d : GornAddress}
    (h : headDaughterRel (adjunctionIndex hd seg) m d) :
    ¬ headDaughterRel (projectionIndex hd seg) m d := by
  obtain ⟨i, hi, -⟩ := h
  rintro ⟨j, hj, -⟩
  simp only [adjunctionIndex, projectionIndex] at hi hj
  split at hi <;> simp_all

theorem isMaximalCategory_iff_inits (x : GornAddress) :
    IsMaximalCategory (headDaughterRel (projectionIndex hd seg))
        (headDaughterRel (adjunctionIndex hd seg)) x ↔
      ∀ s ∈ x.inits,
        IsProjectionOf (headDaughterRel (adjunctionIndex hd seg)) x s →
          IsMaximalProjection (headDaughterRel (projectionIndex hd seg)) s := by
  rw [isMaximalCategory_iff_forall_above (fun _ _ ↦ headDaughterRel_covBy _)
    (fun _ _ ↦ headDaughterRel_covBy _) (headDaughterRel_rightUnique _)
    (fun _ _ ↦ not_projection_of_adjunction hd seg)]
  constructor
  · exact fun h s _ hs ↦ h s hs
  · exact fun h s hs ↦ h s (List.mem_map.2 ⟨_, (List.mem_inits _ _).2
      (GornAddress.le_def.1 (IsProjectionOf.le (fun _ _ ↦ headDaughterRel_covBy _) hs)), rfl⟩) hs

/-- A daughter other than the head of a mother that is no segment is a maximal category. -/
theorem isMaximalCategory_append_singleton {m : GornAddress} {i : ℕ} (hm : ¬ seg m)
    (hi : hd m ≠ some i) :
    IsMaximalCategory (headDaughterRel (projectionIndex hd seg))
      (headDaughterRel (adjunctionIndex hd seg)) (m * .of i) := by
  have hmother {c : GornAddress} {j : ℕ} (h : m.toList ++ [i] = c.toList ++ [j]) : c = m ∧ j = i :=
      by
    obtain ⟨h₁, h₂⟩ := List.append_inj' h rfl
    exact ⟨GornAddress.ext h₁.symm, (List.singleton_inj.mp h₂).symm⟩
  rw [isMaximalCategory_iff_forall_above (fun _ _ ↦ headDaughterRel_covBy _)
    (fun _ _ ↦ headDaughterRel_covBy _) (headDaughterRel_rightUnique _)
    (fun _ _ ↦ not_projection_of_adjunction hd seg)]
  intro s hs
  rcases Relation.ReflTransGen.cases_tail hs with rfl | ⟨c, -, j, hj, hc⟩
  · rintro c ⟨j, hj, hc⟩
    obtain ⟨rfl, rfl⟩ := hmother hc
    exact hi (by simpa [projectionIndex, hm] using hj)
  · obtain ⟨rfl, rfl⟩ := hmother hc
    simp [adjunctionIndex, hm] at hj

instance (x : GornAddress) : Decidable (IsMaximalCategory (headDaughterRel (projectionIndex hd seg))
    (headDaughterRel (adjunctionIndex hd seg)) x) :=
  decidable_of_iff _ (isMaximalCategory_iff_inits hd seg x).symm

instance (x : GornAddress) :
    Decidable (x ∈ maximalProjections (headDaughterRel (projectionIndex hd seg))
      (headDaughterRel (adjunctionIndex hd seg))) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem includes_iff_inits (x y : GornAddress) :
    Includes (headDaughterRel (adjunctionIndex hd seg)) x y ↔
      x ≤ y ∧ ∀ q ∈ y.inits,
        IsProjectionOf (headDaughterRel (adjunctionIndex hd seg)) q x →
          ∀ i, adjunctionIndex hd seg q = some i → q * .of i ≤ y := by
  rw [includes_iff_forall_le (fun _ _ ↦ headDaughterRel_covBy _) (headDaughterRel_rightUnique _)]
  refine and_congr_right fun _ ↦ ⟨fun h q hqy hq i hi ↦ h q hq ?_ _ ⟨i, hi, rfl⟩,
    fun h q hq hqy d ⟨i, hi, hd'⟩ ↦ ?_⟩
  · obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hqy
    exact GornAddress.le_def.2 ((List.mem_inits _ _).1 hl)
  · have := h q (List.mem_map.2 ⟨_, (List.mem_inits _ _).2 (GornAddress.le_def.1 hqy), rfl⟩) hq i hi
    exact GornAddress.ext hd' ▸ this

instance (x y : GornAddress) : Decidable (Includes (headDaughterRel (adjunctionIndex hd seg)) x y)
    :=
  decidable_of_iff _ (includes_iff_inits hd seg x y).symm

theorem excludes_iff_inits (x y : GornAddress) :
    Excludes (headDaughterRel (adjunctionIndex hd seg)) x y ↔
      ∀ s ∈ x.inits,
        IsProjectionOf (headDaughterRel (adjunctionIndex hd seg)) x s → ¬ s ≤ y := by
  rw [excludes_iff (fun _ _ ↦ headDaughterRel_covBy _) (headDaughterRel_rightUnique _)]
  exact ⟨fun h s _ hs ↦ h s hs, fun h s hs ↦ h s (List.mem_map.2 ⟨_, (List.mem_inits _ _).2
    (GornAddress.le_def.1 (IsProjectionOf.le (fun _ _ ↦ headDaughterRel_covBy _) hs)), rfl⟩) hs⟩

instance (x y : GornAddress) : Decidable (Excludes (headDaughterRel (adjunctionIndex hd seg)) x y)
    :=
  decidable_of_iff _ (excludes_iff_inits hd seg x y).symm

instance (x y : GornAddress) : Decidable (Contains (headDaughterRel (adjunctionIndex hd seg)) x y)
    :=
  decidable_of_iff _ not_excludes_iff_contains

end Positions

end PhraseStructure
