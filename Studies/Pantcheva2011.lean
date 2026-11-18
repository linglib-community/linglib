module

public import Linglib.Morphology.Paradigm.Contiguity
public import Linglib.Core.Algebra.Order.Interval.Set.Instances
public import Mathlib.Topology.UnitInterval
public import Studies.Zwarts2005

/-!
# Pantcheva (2011): Decomposing Path

Pantcheva classifies paths by their shape relative to a region, crossing direction with
transition (`Spatial.Path.Shape`). The shapes with a transition are those
[Zwarts's closure under concatenation counts as bounded](##Pantcheva2011.cumulative_hasShape_iff).
[A goal path followed by a source path](##Pantcheva2011.isTransitive_of_concat) is a route path,
while the reverse order [yields no shape at all](##Pantcheva2011.not_hasShape_of_concat), which
she takes up as the absence of any preposition for such a path, and which
[reversing a route path](##Pantcheva2011.isTransitive_reverse) cannot derive.

The directional heads Place, Goal, Source and Route form the containment sequence of
`Spatial.Path.Direction`, and a syncretism pattern over the four is a paradigm over that sequence.
Two constraints restrict the patterns: the *ABA generalization of Bobaljik (then circulating in
manuscript), on which a syncretism targets only adjacent heads, the same contiguity that governs
nominal case in Caha's analysis; and *A&¬A, on which Goal and Source never share a marker, because
the Source head reverses the Goal path and
[no path is both](##Spatial.Path.IsCofinal.not_isCoinitial). Together they say exactly that
[no syncretism crosses the seam between Goal and Source](##Pantcheva2011.possible_iff_respectsSeam),
which [cuts the fifteen set-partitions of the four roles to
four](##Pantcheva2011.possible_syncretisms): Place and Goal may merge, Source and Route may merge,
and nothing else.

## Implementation notes

The patterns are restricted-growth strings over the four positions, one representative per
set-partition; the seam characterization is proved for every pattern, and the enumerations
are its corollaries. The attested lexicalization patterns are described in prose.

## TODO

* The Scale head that derives non-transitional paths from transitional ones, and the Bound head
  that derives delimited ones.
* The morphological containment of Goal markers in Source markers as data, rather than the order
  of the heads alone.

## References

* [pantcheva-2011]
* [zwarts-2005]
* [bobaljik-2012]
* [caha-2009]
-/

@[expose] public section

namespace Pantcheva2011

open Morphology
open Spatial Spatial.Path

/-- A syncretism pattern assigns form-class indices to the four path roles, in containment order
Place, Goal, Source, Route, as the four-cell instance of `Morphology.Paradigm`. -/
abbrev Pattern := Paradigm 4 ℕ

/-- The fifteen syncretism patterns up to relabeling are the restricted-growth strings over four
positions, one per set-partition of the four roles. -/
def allPatterns : List Pattern :=
  [![0, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, 1, 0], ![0, 0, 1, 1], ![0, 0, 1, 2],
   ![0, 1, 0, 0], ![0, 1, 0, 1], ![0, 1, 0, 2], ![0, 1, 1, 0], ![0, 1, 1, 1],
   ![0, 1, 1, 2], ![0, 1, 2, 0], ![0, 1, 2, 1], ![0, 1, 2, 2], ![0, 1, 2, 3]]

/-- Goal and Source share a form class, which *A&¬A forbids. -/
def GoalSourceMerged (p : Pattern) : Prop := p Direction.goal.rank = p Direction.source.rank

instance (p : Pattern) : Decidable (GoalSourceMerged p) := inferInstanceAs (Decidable (_ = _))

/-- A pattern is possible iff it is contiguous, *ABA, and keeps Goal distinct from Source,
*A&¬A. -/
def Possible (p : Pattern) : Prop := IsContiguous p ∧ ¬ GoalSourceMerged p

instance (p : Pattern) : Decidable (Possible p) := inferInstanceAs (Decidable (_ ∧ _))

/-- A pattern respects the seam when no form class straddles Goal and Source: cells that share
a form lie on the same side of the seam. -/
def RespectsSeam (p : Pattern) : Prop := ∀ i j, p i = p j → (i ≤ 1 ↔ j ≤ 1)

private theorem ne_of_seam {p : Pattern} (hc : IsContiguous p) (hgs : ¬ GoalSourceMerged p)
    {i j : Fin 4} (hi : i ≤ 1) (hj : 2 ≤ j) : p i ≠ p j := fun h ↦
  hgs ((hc hi (le_trans (by decide) hj) h).symm.trans (hc (le_trans hi (by decide)) hj h))

theorem possible_iff_respectsSeam (p : Pattern) : Possible p ↔ RespectsSeam p := by
  constructor
  · rintro ⟨hc, hgs⟩ i j h
    constructor
    · intro hi; by_contra hj
      exact ne_of_seam hc hgs hi (by omega) h
    · intro hj; by_contra hi
      exact ne_of_seam hc hgs hj (by omega) h.symm
  · intro hs
    refine ⟨fun i j k hij hjk hik ↦ ?_, fun h ↦ by simpa using hs 1 2 h⟩
    rcases eq_or_lt_of_le hij with rfl | hlt
    · rfl
    · have hs' := hs i k hik
      have hjk' : j = k := by
        by_cases hi : i ≤ 1
        · have := hs'.mp hi; omega
        · have : ¬ k ≤ 1 := fun hk ↦ hi (hs'.mpr hk); omega
      subst hjk'; exact hik

/-- Exactly four of the fifteen patterns respect the seam, Types 1 to 4 of Table 9.2. -/
theorem possible_syncretisms :
    allPatterns.filter (fun p ↦ Possible p) =
      [![0, 0, 1, 1], ![0, 0, 1, 2], ![0, 1, 2, 2], ![0, 1, 2, 3]] := by
  decide

-- Table 9.3
theorem aba_excluded :
    allPatterns.filter (fun p ↦ ¬ IsContiguous p) =
      [![0, 0, 1, 0], ![0, 1, 0, 0], ![0, 1, 0, 1], ![0, 1, 0, 2], ![0, 1, 1, 0],
       ![0, 1, 2, 0], ![0, 1, 2, 1]] := by
  decide

-- Table 9.3
theorem ana_excluded :
    allPatterns.filter (fun p ↦ IsContiguous p ∧ GoalSourceMerged p) =
      [![0, 0, 0, 0], ![0, 0, 0, 1], ![0, 1, 1, 1], ![0, 1, 1, 2]] := by
  decide

/-! ### Containment

The Source structure contains the Goal structure, visible where the Source marker contains the
Goal marker, as in Quechua *-man* against *-man-da* (Table 4.2). -/

theorem source_contains_goal :
    Set.Iic Direction.place ⊂ Set.Iic Direction.goal ∧
      Set.Iic Direction.goal ⊂ Set.Iic Direction.source ∧
      Set.Iic Direction.source ⊂ Set.Iic Direction.route :=
  ⟨Set.Iic_ssubset_Iic.2 (by decide), Set.Iic_ssubset_Iic.2 (by decide),
    Set.Iic_ssubset_Iic.2 (by decide)⟩

-- Table 9.1
theorem georgian_loc_goal_possible : Possible ![0, 0, 1, 2] := by decide

/-! ### Paths and their shapes -/

section Shapes

variable {Loc β : Type*} [Preorder β] {R : Set Loc} {d : Loc → β} {p q r : Path Loc} {s : Shape}

/-- A path from outside a place into it is cofinal and not coinitial, and its reverse is
coinitial, the semantic ground of *A&¬A (§5.4). -/
example : let p : Path ℕ := ⟨0, [1]⟩
    IsCofinal {1} p ∧ ¬ IsCoinitial {1} p ∧ IsCoinitial {1} p.reverse := by
  intro p
  have h : IsCofinal {1} p := by
    refine ⟨fun a b hab ha ↦ ?_, by decide, by decide⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at ha ⊢
    revert a b; decide
  exact ⟨h, h.not_isCoinitial,
    (hasShape_reverse p (d := (id : ℕ → ℕ)) (s := .coinitial)).2 h⟩

/-- A goal path followed by a source path is a route path with one positive phase, (10) of
Chapter 2. -/
theorem isTransitive_of_concat (hp : IsCofinal R p) (hq : IsCoinitial R q)
    (h : p.IsConcat q r) : IsTransitive R r := by
  have hl := h.length_steps
  refine ⟨⟨fun a ha b hb c hc ↦ ?_⟩, ⟨⟨p.steps.length, by omega⟩, ?_⟩, ?_, ?_⟩
  · rcases le_total (c : ℕ) p.steps.length with hle | hle
    · have hac := Fin.le_def.1 hc.1
      have key : (⟨a, by omega⟩ : Fin (p.steps.length + 1)) ∈ p ⁻¹' R := by
        rw [Set.mem_preimage, ← h.apply_of_le a (hac.trans hle)]; exact ha
      show r c ∈ R
      rw [h.apply_of_le c hle]
      exact hp.1 (Fin.le_def.2 hac) key
    · have hcb := Fin.le_def.1 hc.2
      have key : (⟨b - p.steps.length, by omega⟩ : Fin (q.steps.length + 1)) ∈ q ⁻¹' R := by
        rw [Set.mem_preimage, ← h.apply_of_ge b (hle.trans hcb)]; exact hb
      show r c ∈ R
      rw [h.apply_of_ge c hle]
      exact hq.1 (Fin.le_def.2 (Nat.sub_le_sub_right hcb _)) key
  · show r _ ∈ R
    rw [h.apply_of_le _ le_rfl]
    exact hp.2.2
  · rw [coe_bot, h.source_eq]; exact hp.2.1
  · rw [coe_top, h.goal_eq, ← coe_top]; exact hq.2.2

/-- A source path followed by a goal path has two positive phases and so no shape, the *tsap of
(11) of Chapter 2, which to her knowledge no language has a preposition for. -/
theorem not_hasShape_of_concat (hp : IsCoinitial R p) (hq : IsCofinal R q)
    (h : p.IsConcat q r) (s : Shape) : ¬ HasShape R r d s :=
  fun hr ↦ h.not_ordConnected (p.coe_top ▸ hp.2.2) hp.2.1 hq.2.2 hr.ordConnected

/-- Such a path can be formed, so what (11) lacks is a shape rather than a concatenation. -/
example : ∃ p q r : Path ℕ, IsCoinitial {1} p ∧ IsCofinal {1} q ∧ p.IsConcat q r := by
  refine ⟨⟨1, [0]⟩, ⟨0, [1]⟩, _, ⟨fun a b hab hb ↦ ?_, by decide, by decide⟩,
    ⟨fun a b hab ha ↦ ?_, by decide, by decide⟩, rfl, rfl⟩
  · simp only [Set.mem_preimage, Set.mem_singleton_iff] at hb ⊢
    revert a b; decide
  · simp only [Set.mem_preimage, Set.mem_singleton_iff] at ha ⊢
    revert a b; decide

-- §5.5
theorem isTransitive_reverse : IsTransitive R p.reverse ↔ IsTransitive R p :=
  hasShape_reverse p (d := fun _ ↦ ()) (s := .transitive)

-- §5.4, §5.5
theorem hasShape_comp_symm {γ : unitInterval → Loc} :
    HasShape R (γ ∘ unitInterval.symm) d s ↔ HasShape R γ d s.reverse := by
  rw [show γ ∘ unitInterval.symm = (γ ∘ OrderDual.ofDual) ∘ Set.Icc.symmOrderIso from rfl,
    hasShape_comp,
    hasShape_comp_ofDual]

/-- A shape is bounded in the table's sense exactly when its paths are not cumulative in the sense
of [zwarts-2005]: the paths of a shape are cumulative just when it has no transition and two of
them concatenate. -/
theorem cumulative_hasShape_iff :
    Zwarts2005.Cumulative IsConcat {p : Path Loc | HasShape R p d s} ↔
      ¬ s.IsBounded ∧ ∃ p q r : Path Loc, HasShape R p d s ∧ HasShape R q d s ∧ IsConcat p q r :=
  ⟨fun ⟨⟨p, hp, q, hq, r, hr⟩, hc⟩ ↦
    ⟨fun hs ↦ HasShape.not_concat hs hp hq hr (hc p hp q hq r hr), p, q, r, hp, hq, hr⟩,
    fun ⟨hs, p, q, r, hp, hq, hr⟩ ↦
      ⟨⟨p, hp, q, hq, r, hr⟩, fun _ hp _ hq _ hr ↦ HasShape.concat hs hp hq hr⟩⟩

-- [zwarts-2005]
theorem mem_towardsPP_of_isApproximative (h : IsApproximative R p d) :
    p ∈ Zwarts2005.towardsPP d := by
  have : d (p ⊤) < d (p ⊥) := h.2.1 (lt_of_le_of_ne bot_le h.2.2)
  rwa [coe_top, coe_bot] at this

-- [zwarts-2005]
theorem mem_awayFromPP_of_isRecessive (h : IsRecessive R p d) :
    p ∈ Zwarts2005.awayFromPP d := by
  have : d (p ⊥) < d (p ⊤) := h.2.1 (lt_of_le_of_ne bot_le h.2.2)
  rwa [coe_top, coe_bot] at this

/-- A stationary path neither approaches a region nor recedes from it. -/
example (l : Loc) : ¬ IsApproximative R (const l) d ∧ ¬ IsRecessive R (const l) d :=
  ⟨fun h ↦ h.2.2 rfl, fun h ↦ h.2.2 rfl⟩

end Shapes

end Pantcheva2011
