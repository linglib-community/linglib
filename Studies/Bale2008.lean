module

public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Tactic.NormNum
public import Linglib.Semantics.Degree.Quantifier
public import Linglib.Semantics.Degree.UniversalScale
public import Linglib.Data.Examples.Bale2008

/-!
# Bale (2008): A universal scale of comparison

A gradable adjective orders a comparison class by a quasi-order, such as *has as much beauty as*.
Its classes of equivalent members form the primary scale, and each member is sent to the
universal degree of its class: one plus the number of classes below it, over the number of
classes. The comparative compares universal degrees whatever the two scales, so one
interpretation serves indirect comparisons (*Betty is more beautiful than Heather is
intelligent*) and direct ones (*Seymour is taller than he is wide*). A comparison is direct when
the comparison class contains the measurements in inches up to a bound and everyone is as tall,
or as wide, as exactly one of them: both primary scales are then the measurement system, and
universal degrees compare as measurements do. A for-clause restricts the comparison class to
men and drops the measurements, so Seymour, short and very wide, is taller than he is wide but
not taller for a man than he is wide for a man.

## Implementation notes

* Universal degrees are `Degree.universalDegree`: an adjective's quasi-order is given by a
  measure into a linear order, and a comparison class by a finite set, which restricts the
  quasi-order as Klein's comparison classes do.
* The comparative is Kennedy's, as in the paper: MORE applied to the greatest degree the
  than-clause reaches is `Degree.MaxComparative .gt` over the two measures (`more_iff`), stated as
  the point comparison `μ ⁻¹' Set.Ioi n`.
* Universal degrees are rationals: the paper's universal scale is the rationals from zero to one.
* Measurements are individuals `.inr n` of `n` inches, bounded by the comparison class; heights
  and widths are in inches as printed, and the committee's rankings count from the bottom.

## References

* [bale-2008]
* [kennedy-1999]
* [klein-1980]
-/

@[expose] public section

namespace Bale2008

open Finset Degree

/-! ### The comparative -/

theorem more_iff {E F : Type*} (μ₁ : E → ℚ) (μ₂ : F → ℚ) (x : E) (y : F) :
    MaxComparative .gt (· = .inl x) (· = .inr y) (Sum.elim μ₁ μ₂) ↔
      x ∈ μ₁ ⁻¹' Set.Ioi (μ₂ y) :=
  maxComparative_eq_iff _ _ _

theorem not_more_of_least_of_greatest {D D' E F : Type*} [LinearOrder D] [DecidableEq D]
    [LinearOrder D'] [DecidableEq D'] {μ : E → D} {ν : F → D'} {C : Finset E} {C' : Finset F}
    {x : E} {y : F} (hx : x ∈ C) (hy : y ∈ C') (hmin : ∀ z ∈ C, μ x ≤ μ z)
    (hmax : ∀ z ∈ C', ν z ≤ ν y) :
    x ∉ (universalDegree μ C) ⁻¹' Set.Ioi (universalDegree ν C' y) := by
  simp only [Set.mem_preimage, Set.mem_Ioi, not_lt,
    universalDegree_of_forall_le hy hmax, universalDegree_of_forall_ge hx hmin]
  exact div_le_one_of_le₀ (by exact_mod_cast card_pos.2 ⟨μ x, mem_image_of_mem μ hx⟩)
    (Nat.cast_nonneg _)

/-! ### The committee -/

/-- The committee has ten original members `a`–`j`, among them Betty (`b`), Evelin (`e`) and
Heather (`h`), and the expanded committee adds five members `a'`–`e'`. -/
inductive Member
  | a | b | c | d | e | f | g | h | i | j | a' | b' | c' | d' | e'
  deriving DecidableEq, Fintype, Repr

/-- The original ten members. -/
def original : Finset Member := {.a, .b, .c, .d, .e, .f, .g, .h, .i, .j}

/-- A member's beauty is their position counted from the least beautiful, the original ten
ranking a, b, c, …, j from the most beautiful down; `a'` and `b'` are as beautiful as Betty, `c'`
as `c`, `d'` as `d` and `e'` as Evelin. -/
def beauty : Member → ℕ
  | .a => 10 | .b | .a' | .b' => 9 | .c | .c' => 8 | .d | .d' => 7 | .e | .e' => 6
  | .f => 5 | .g => 4 | .h => 3 | .i => 2 | .j => 1

/-- A member's intelligence is their position counted from the least intelligent, the original
ten ranking i, f, j, g, h, a, d, b, e, c from the most intelligent down; `a'` is as intelligent as
Heather, `b'` and `c'` as Betty, `d'` as `f` and `e'` as Evelin. -/
def intelligence : Member → ℕ
  | .i => 10 | .f | .d' => 9 | .j => 8 | .g => 7 | .h | .a' => 6 | .a => 5 | .d => 4
  | .b | .b' | .c' => 3 | .e | .e' => 2 | .c => 1

/-- Betty, second most beautiful, is more beautiful for a committee member than Heather, fifth
most intelligent, is intelligent; Betty, third least intelligent, is not more intelligent than
Evelin, fifth most beautiful, is beautiful. -/
theorem indirect_comparison :
    .b ∈ (universalDegree beauty original) ⁻¹' Set.Ioi
      (universalDegree intelligence original .h) ∧
    .b ∉ (universalDegree intelligence original) ⁻¹' Set.Ioi
      (universalDegree beauty original .e) := by
  have hb : original.image beauty = Icc 1 10 := by decide
  have hi : original.image intelligence = Icc 1 10 := by decide
  simp only [Set.mem_preimage, Set.mem_Ioi,
    universalDegree_of_image_eq_Icc hb (by decide : Member.b ∈ original),
    universalDegree_of_image_eq_Icc hb (by decide : Member.e ∈ original),
    universalDegree_of_image_eq_Icc hi (by decide : Member.b ∈ original),
    universalDegree_of_image_eq_Icc hi (by decide : Member.h ∈ original)]
  norm_num [beauty, intelligence]

theorem expanded :
    universalDegree beauty univ = universalDegree beauty original ∧
    universalDegree intelligence univ = universalDegree intelligence original :=
  ⟨universalDegree_eq_of_image_eq (by decide), universalDegree_eq_of_image_eq (by decide)⟩

/-! ### Measurements -/

section Measured

variable {E : Type*} {μ ν : E ⊕ ℕ → ℕ} {P : Finset E} {N : ℕ}

/-- The comparison class of the people in `P` and the measurements from one to `N` inches. -/
def withMeasurements (P : Finset E) (N : ℕ) : Finset (E ⊕ ℕ) := P.disjSum (Icc 1 N)

theorem image_withMeasurements (hμ : ∀ n, μ (.inr n) = n) (hP : ∀ x ∈ P, μ (.inl x) ∈ Icc 1 N) :
    (withMeasurements P N).image μ = Icc 1 N := by
  refine Subset.antisymm (fun _ h ↦ ?_) fun n hn ↦ mem_image.2 ⟨.inr n, ?_, hμ n⟩
  · obtain ⟨y | n, hy, rfl⟩ := mem_image.1 h <;> simp_all [withMeasurements]
  · simp_all [withMeasurements]

theorem universalDegree_withMeasurements (hμ : ∀ n, μ (.inr n) = n)
    (hP : ∀ x ∈ P, μ (.inl x) ∈ Icc 1 N) {x : E} (hx : x ∈ P) :
    universalDegree μ (withMeasurements P N) (.inl x) = μ (.inl x) / N :=
  universalDegree_of_image_eq_Icc (image_withMeasurements hμ hP) (by simp [withMeasurements, hx])

/-- When the comparison class keeps the measurements up to a common bound, each measuring itself
on both scales, and everyone measures within the bound, comparing universal degrees is
comparing measurements, as in a direct comparison. -/
theorem direct_comparison (hμ : ∀ n, μ (.inr n) = n) (hν : ∀ n, ν (.inr n) = n)
    (hPμ : ∀ x ∈ P, μ (.inl x) ∈ Icc 1 N) (hPν : ∀ x ∈ P, ν (.inl x) ∈ Icc 1 N)
    {z w : E ⊕ ℕ} (hz : z ∈ withMeasurements P N) (hw : w ∈ withMeasurements P N) :
    z ∈ (universalDegree μ (withMeasurements P N)) ⁻¹' Set.Ioi
      (universalDegree ν (withMeasurements P N) w) ↔ ν w < μ z :=
  universalDegree_lt_iff_of_image_eq
    ((image_withMeasurements hν hPν).trans (image_withMeasurements hμ hPμ).symm) hw hz

end Measured

/-- The seven people of the height and width situation; `s` is Seymour. -/
inductive Person
  | a | b | c | d | e | f | s
  deriving DecidableEq, Fintype, Repr

/-- Heights are in inches. Man a is six foot three, b six foot two, c six foot, d, e and f five foot
ten and Seymour five foot two, and a measurement is as tall as itself. -/
def height : Person ⊕ ℕ → ℕ
  | .inl .a => 75 | .inl .b => 74 | .inl .c => 72 | .inl .d | .inl .e | .inl .f => 70
  | .inl .s => 62 | .inr n => n

/-- Widths are in inches. Seymour is three feet wide, f two foot five, b two foot two and the
rest two foot one, and a measurement is as wide as itself. -/
def width : Person ⊕ ℕ → ℕ
  | .inl .s => 36 | .inl .f => 29 | .inl .b => 26
  | .inl .a | .inl .c | .inl .d | .inl .e => 25 | .inr n => n

/-- The comparison class of the height and width situation holds the seven people and the
measurements up to eighty inches. -/
def measured : Finset (Person ⊕ ℕ) := withMeasurements univ 80

theorem taller_than_wide :
    universalDegree height measured (.inl .s) = 62 / 80 ∧
    universalDegree width measured (.inl .s) = 36 / 80 ∧
    .inl .s ∈ (universalDegree height measured) ⁻¹' Set.Ioi
      (universalDegree width measured (.inl .s)) ∧
    .inl .s ∉ (universalDegree width measured) ⁻¹' Set.Ioi
      (universalDegree height measured (.inl .s)) := by
  have hs : (.inl .s : Person ⊕ ℕ) ∈ measured := by simp [measured, withMeasurements]
  have hh : ∀ x ∈ (univ : Finset Person), height (.inl x) ∈ Icc 1 80 := by decide
  have hw : ∀ x ∈ (univ : Finset Person), width (.inl x) ∈ Icc 1 80 := by decide
  refine ⟨?_, ?_, (direct_comparison (fun _ ↦ rfl) (fun _ ↦ rfl) hh hw hs hs).2 (by decide),
    fun h ↦ absurd ((direct_comparison (fun _ ↦ rfl) (fun _ ↦ rfl) hw hh hs hs).1 h) (by decide)⟩
  · rw [measured, universalDegree_withMeasurements (fun _ ↦ rfl) hh (mem_univ _)]; norm_num [height]
  · rw [measured, universalDegree_withMeasurements (fun _ ↦ rfl) hw (mem_univ _)]; norm_num [width]

/-! ### For a man -/

/-- The nineteen men; `s` is Seymour. -/
inductive Man
  | a | b | c | d | e | f | g | h | i | j | k | l | m | n | o | p | q | r | s
  deriving DecidableEq, Fintype, Repr

/-- A man's height class counts from the shortest. Seymour is alone at the bottom, followed by
o and p; k, l, m and n; q and c; f, g, h and i; d and e; j and r; and a and b. -/
def heightClass : Man → ℕ
  | .s => 1 | .o | .p => 2 | .k | .l | .m | .n => 3 | .q | .c => 4
  | .f | .g | .h | .i => 5 | .d | .e => 6 | .j | .r => 7 | .a | .b => 8

/-- A man's width class counts from the narrowest. Men q, r and a are at the bottom, then p;
n and o; j, k, l and m; f, g and h; b, c, d and e; and Seymour and i at the top. -/
def widthClass : Man → ℕ
  | .q | .r | .a => 1 | .p => 2 | .n | .o => 3 | .j | .k | .l | .m => 4
  | .f | .g | .h => 5 | .b | .c | .d | .e => 6 | .i | .s => 7

/-- The comparison class that *for a man* fixes holds the men and no measurements. -/
def men : Finset (Man ⊕ ℕ) := univ.map .inl

/-- Seymour is five feet tall and three feet wide. Among men ordered as above and measurements up
to eighty inches he is taller than he is wide, but restricted to men his height degree is one
eighth and his width degree one, so he is not taller for a man than he is wide for a man. -/
theorem for_a_man {τ ω : Man ⊕ ℕ → ℕ}
    (hτ : ∀ x y, τ (.inl x) ≤ τ (.inl y) ↔ heightClass x ≤ heightClass y)
    (hω : ∀ x y, ω (.inl x) ≤ ω (.inl y) ↔ widthClass x ≤ widthClass y)
    (hτn : ∀ n, τ (.inr n) = n) (hωn : ∀ n, ω (.inr n) = n)
    (hs : τ (.inl .s) = 60 ∧ ω (.inl .s) = 36)
    (hb : ∀ x, τ (.inl x) ∈ Icc 1 80 ∧ ω (.inl x) ∈ Icc 1 80) :
    .inl .s ∈ (universalDegree τ (withMeasurements univ 80)) ⁻¹' Set.Ioi
      (universalDegree ω (withMeasurements univ 80) (.inl .s)) ∧
    universalDegree τ men (.inl .s) = 1 / 8 ∧ universalDegree ω men (.inl .s) = 1 ∧
    .inl .s ∉ (universalDegree τ men) ⁻¹' Set.Ioi (universalDegree ω men (.inl .s)) := by
  have hs' : (.inl .s : Man ⊕ ℕ) ∈ men := by simp [men]
  have hτC : universalDegree τ men (.inl .s) = 1 / 8 := by
    rw [universalDegree_congr (ν := Sum.elim heightClass fun _ ↦ 0) ?_ hs']
    · decide +kernel
    · simp only [men, mem_map, mem_univ, true_and]
      rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
      exact hτ x y
  have hωC : universalDegree ω men (.inl .s) = 1 := by
    rw [universalDegree_congr (ν := Sum.elim widthClass fun _ ↦ 0) ?_ hs']
    · decide +kernel
    · simp only [men, mem_map, mem_univ, true_and]
      rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
      exact hω x y
  refine ⟨(direct_comparison hτn hωn (fun x _ ↦ (hb x).1) (fun x _ ↦ (hb x).2)
    (by simp [withMeasurements]) (by simp [withMeasurements])).2 (by omega), hτC, hωC, ?_⟩
  simp only [Set.mem_preimage, Set.mem_Ioi, hτC, hωC]
  norm_num

/-- The hypotheses of `for_a_man` are consistent, since some heights and widths in inches induce
the two orders of the men. -/
example : ∃ τ ω : Man ⊕ ℕ → ℕ,
    (∀ x y, τ (.inl x) ≤ τ (.inl y) ↔ heightClass x ≤ heightClass y) ∧
    (∀ x y, ω (.inl x) ≤ ω (.inl y) ↔ widthClass x ≤ widthClass y) ∧
    (∀ n, τ (.inr n) = n) ∧ (∀ n, ω (.inr n) = n) ∧ τ (.inl .s) = 60 ∧ ω (.inl .s) = 36 ∧
    ∀ x, τ (.inl x) ∈ Icc 1 80 ∧ ω (.inl x) ∈ Icc 1 80 :=
  ⟨Sum.elim (heightClass · + 59) id, Sum.elim (widthClass · + 29) id, by simp, by simp,
    fun _ ↦ rfl, fun _ ↦ rfl, rfl, rfl, by decide⟩

/-! ### The rows -/

/-- A committee member by name. -/
def Member.parse? : String → Option Member
  | "a" => some .a | "b" => some .b | "c" => some .c | "d" => some .d | "e" => some .e
  | "f" => some .f | "g" => some .g | "h" => some .h | "i" => some .i | "j" => some .j
  | _ => none

/-- A person of the height and width situation by name. -/
def Person.parse? : String → Option Person
  | "a" => some .a | "b" => some .b | "c" => some .c | "d" => some .d | "e" => some .e
  | "f" => some .f | "s" => some .s | _ => none

/-- A man by name. -/
def Man.parse? : String → Option Man
  | "a" => some .a | "b" => some .b | "c" => some .c | "d" => some .d | "e" => some .e
  | "f" => some .f | "g" => some .g | "h" => some .h | "i" => some .i | "j" => some .j
  | "k" => some .k | "l" => some .l | "m" => some .m | "n" => some .n | "o" => some .o
  | "p" => some .p | "q" => some .q | "r" => some .r | "s" => some .s | _ => none

/-- A row assigns one of its participants a universal degree on one of its scales in the
comparison class of its situation, which is the original committee, the people with the
measurements up to eighty inches, or the men. -/
def degree? (r : Datum) (who scale : String) : Option ℚ := do
  let n ← r.feature? who
  match r.feature? "model", r.feature? scale with
  | some "committee", some "beauty" => (Member.parse? n).map (universalDegree beauty original)
  | some "committee", some "intelligence" =>
    (Member.parse? n).map (universalDegree intelligence original)
  | some "measured", some "height" =>
    (Person.parse? n).map fun p ↦ universalDegree height measured (.inl p)
  | some "measured", some "width" =>
    (Person.parse? n).map fun p ↦ universalDegree width measured (.inl p)
  | some "men", some "height" => (Man.parse? n).map (universalDegree heightClass univ)
  | some "men", some "width" => (Man.parse? n).map (universalDegree widthClass univ)
  | _, _ => none

/-- Every sentence the paper evaluates in one of its situations has the truth value it reports,
since the subject's universal degree exceeds the standard's exactly when the paper says the sentence
is true. -/
theorem rows_truth : ∀ r ∈ Examples.all, (r.feature? "model").isSome →
    ∃ t ∈ r.verdict, ∃ d₁ ∈ degree? r "subject" "subjectScale",
      ∃ d₂ ∈ degree? r "standard" "standardScale", (d₂ < d₁ ↔ t = true) := by
  decide +kernel

end Bale2008
