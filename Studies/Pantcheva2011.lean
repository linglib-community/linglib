module

public import Linglib.Morphology.Paradigm.Contiguity
public import Linglib.Core.Algebra.Order.Interval.Set.Instances
public import Mathlib.Topology.UnitInterval
public import Linglib.Semantics.Space.Shape
public import Studies.Zwarts2005

/-!
# Pantcheva (2011): Decomposing Path

A directional expression has one of four heads, Place, Goal, Source and Route, and each head
contains the one before it. A *syncretism pattern* says which of the four heads a language marks
with the same form. Two constraints restrict the patterns. By \*ABA, a form shared by two heads
is shared by every head between them. By \*A&¬A, Goal and Source never share a form.

We define a pattern as a function from the four heads to form classes. The main result,
`Pantcheva2011.possible_iff_respectsSeam`, says that a pattern satisfies both constraints if and
only if no form class has heads on both sides of the boundary between Goal and Source. Exactly
four of the fifteen patterns do. They have four distinct forms, or merge Place with Goal, or
merge Source with Route, or do both.

Paths are also classified by their shape relative to a region. We prove that a path into a region
followed by a path out of it crosses the region, and that a path out of a region followed by a
path into it has none of the eight shapes. We also prove that the paths of a shape are cumulative
under concatenation if and only if the shape is not bounded and two of its paths concatenate.

## Implementation notes

A pattern is a restricted-growth string over the four positions, which gives one representative
of each partition of the four heads.

The patterns attested in particular languages are not encoded as data.

## TODO

* The Scale head, which derives non-transitional paths from transitional ones, and the Bound
  head, which derives delimited ones.
* The containment of Goal markers in Source markers as data, and not only the order of the heads.

## References

* [pantcheva-2011]
* [zwarts-2005]
* [bobaljik-2012]
* [caha-2009]
-/

@[expose] public section

namespace Pantcheva2011

open Morphology
open Locative Order Zwarts2005

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

variable {Loc β : Type*} [Preorder β] {R : Set Loc} {d : Loc → β} {p q : Path Loc} {s : Shape}

/-- A path from outside a place into it is cofinal and not coinitial, and its reverse is
coinitial, the semantic ground of *A&¬A (§5.4). -/
example : let p : Path ℕ := Path.ofPoints 0 [1]
    Enters p {1} ∧ ¬ Leaves p {1} ∧ Leaves p.reverse {1} := by
  intro p
  have h : Enters p {1} := by
    refine ⟨fun a b hab ha ↦ ?_, by decide, by decide⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at ha ⊢
    revert a b; decide
  exact ⟨h, h.not_leaves,
    (hasShape_reverse p (d := (id : ℕ → ℕ)) (s := .coinitial)).2 h⟩

/-- A goal path followed by a source path is a route path with one positive phase, (10) of
Chapter 2. -/
theorem crosses_of_concat (hp : Enters p R) (hq : Leaves q R)
    (h : p.last = q.head) : Crosses (p.smash q h) R := by
  have hl : (p.smash q h).length = p.length + q.length := rfl
  refine ⟨⟨fun a ha b hb c hc ↦ ?_⟩, ⟨⟨p.length, by omega⟩, ?_⟩, ?_, ?_⟩
  · rcases le_total (c : ℕ) p.length with hle | hle
    · have hac := Fin.le_def.1 hc.1
      have key : (⟨a, by omega⟩ : Fin (p.length + 1)) ∈ p ⁻¹' R := by
        rw [Set.mem_preimage, ← RelSeries.smash_apply_of_le h a (hac.trans hle)]; exact ha
      show p.smash q h c ∈ R
      rw [RelSeries.smash_apply_of_le h c hle]
      exact hp.1 (Fin.le_def.2 hac) key
    · have hcb := Fin.le_def.1 hc.2
      have key : (⟨b - p.length, by omega⟩ : Fin (q.length + 1)) ∈ q ⁻¹' R := by
        rw [Set.mem_preimage, ← RelSeries.smash_apply_of_ge h b (hle.trans hcb)]; exact hb
      show p.smash q h c ∈ R
      rw [RelSeries.smash_apply_of_ge h c hle]
      exact hq.1 (Fin.le_def.2 (Nat.sub_le_sub_right hcb _)) key
  · show p.smash q h _ ∈ R
    rw [RelSeries.smash_apply_of_le h _ le_rfl]
    exact hp.2.2
  · rw [RelSeries.apply_bot, RelSeries.head_smash]; exact hp.2.1
  · rw [RelSeries.apply_top, RelSeries.last_smash, ← RelSeries.apply_top]; exact hq.2.2

/-- A source path followed by a goal path has two positive phases and so no shape, the *tsap of
(11) of Chapter 2, which to her knowledge no language has a preposition for. -/
theorem not_hasShape_of_concat (hp : Leaves p R) (hq : Enters q R)
    (h : p.last = q.head) (s : Shape) : ¬ HasShape R (p.smash q h) d s :=
  fun hr ↦ by
    have := hr.entries_eq_zero_of_head_mem (by simpa using hp.2.1)
    rw [RelSeries.entries_smash, hp.entries_eq, hq.entries_eq] at this
    exact absurd this (by decide)

/-- Such a path can be formed, so what (11) lacks is a shape rather than a concatenation. -/
example : ∃ p q : Path ℕ, Leaves p {1} ∧ Enters q {1} ∧ p.last = q.head := by
  refine ⟨Path.ofPoints 1 [0], Path.ofPoints 0 [1], ⟨fun a b hab hb ↦ ?_, by decide, by decide⟩,
    ⟨fun a b hab ha ↦ ?_, by decide, by decide⟩, rfl⟩
  · simp only [Set.mem_preimage, Set.mem_singleton_iff] at hb ⊢
    revert a b; decide
  · simp only [Set.mem_preimage, Set.mem_singleton_iff] at ha ⊢
    revert a b; decide

-- §5.5
theorem crosses_reverse : Crosses p.reverse R ↔ Crosses p R :=
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
    Zwarts2005.Cumulative Zwarts2005.Concat {p : Path Loc | HasShape R p d s} ↔
      ¬ s.IsBounded ∧
        ∃ p q : Path Loc, HasShape R p d s ∧ HasShape R q d s ∧ p.last = q.head :=
  ⟨fun ⟨⟨p, hp, q, hq, _, h, rfl⟩, hc⟩ ↦
    ⟨fun hs ↦ HasShape.not_concat hs hp hq h (hc p hp q hq _ ⟨h, rfl⟩), p, q, hp, hq, h⟩,
    fun ⟨hs, p, q, hp, hq, h⟩ ↦
      ⟨⟨p, hp, q, hq, _, h, rfl⟩,
        fun _ hp _ hq _ ⟨h, hr⟩ ↦ hr ▸ HasShape.concat hs hp hq h⟩⟩

-- [zwarts-2005]
theorem mem_towardsPP_of_approaches (h : Approaches p R d) :
    p ∈ Zwarts2005.towardsPP d := by
  have : d (p ⊤) < d (p ⊥) := h.2.1 (lt_of_le_of_ne bot_le h.2.2)
  rwa [RelSeries.apply_top, RelSeries.apply_bot] at this

-- [zwarts-2005]
theorem mem_awayFromPP_of_recedes (h : Recedes p R d) :
    p ∈ Zwarts2005.awayFromPP d := by
  have : d (p ⊥) < d (p ⊤) := h.2.1 (lt_of_le_of_ne bot_le h.2.2)
  rwa [RelSeries.apply_top, RelSeries.apply_bot] at this

/-- A stationary path neither approaches a region nor recedes from it. -/
example (l : Loc) :
    ¬ Approaches (RelSeries.singleton _ l : Path Loc) R d ∧
      ¬ Recedes (RelSeries.singleton _ l : Path Loc) R d :=
  ⟨fun h ↦ h.2.2 rfl, fun h ↦ h.2.2 rfl⟩

end Shapes

end Pantcheva2011
