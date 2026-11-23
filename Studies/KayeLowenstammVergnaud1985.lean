/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Order.SuccPred.Fin
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Phonology.Autosegmental.Map
public import Linglib.Phonology.Autosegmental.TierTree.Flatten
public import Linglib.Phonology.FeatureGeometry.Linking
public import Linglib.Phonology.GovernmentPhonology.ElementTheory.Autosegmental
public import Linglib.Phonology.Segmental.PHOIBLE

/-!
# Kaye, Lowenstamm and Vergnaud (1985): The internal structure of phonological elements

An element is a fully specified feature matrix in which exactly one feature has its marked
value. That feature is the hot feature of the element. The element I is [−BACK], U is [+ROUND]
and A is [−HIGH]. The cold vowel is the matrix with no marked value. Each element lies on a
line named by its hot feature.

Two matrices combine by fusion: the head takes the value of the operator's hot feature and keeps
its other values. We define `fuse` and the matrix `interpret m` of a melodic expression `m`,
its operators fused into its head. The main theorem, `interpret_apply_feature`, says that the
value of an expression on the feature of a line is marked if and only if the expression has the
element of that line, whether as head or as operator. Only a feature that names no line depends
on which element is the head.

The lines are therefore feature tiers. Take the representation of a form in Element Theory, and
the representation of its marked values in a feature geometry. Link each position to every token
it dominates, and keep only the skeleton and the lines. The two results are the same
representation, in any geometry that places the features of the lines.

## Implementation notes

* The paper links elements to positions directly. `ElementTheory.ofForm` has a root node between
  a position and its elements, and a feature geometry has a root node and class nodes.
  `Autosegmental.AR.flatten` links a position to what it dominates through them.
* An expression of the paper has one head. `ElementTheory.MR` allows several, and `headMatrix`
  takes the first in the order of the lines.
* The paper's [BACK] has two classes, the front vowels and all others, so a central vowel is
  [+BACK]. `Phonology.Feature` has [front] and [back], with a central vowel [−front, −back]. The
  paper's [−BACK] is therefore [+front] here and its [+BACK] is [−front], and the matrices say
  nothing about `Feature.back`.

## TODO

* Fused lines, on which two elements cannot combine, and the ATR element.
* Charm, government, and the vowel system of Kpokolo.

## References

* [kaye-lowenstamm-vergnaud-1985]
-/

@[expose] public section

open ElementTheory Phonology Autosegmental

namespace KayeLowenstammVergnaud1985

/-! ### Elements as feature matrices -/

/-- The lines of a vowel system. A line is named by the hot feature of its element (§1.2). -/
inductive Line where
  | back
  | round
  | high
  deriving DecidableEq, Repr, Fintype

namespace Line

/-- The feature of a line. The paper's [BACK] separates the front vowels from all others, so its
[−BACK] is [+front] here. -/
def feature : Line → Feature
  | .back => .front
  | .round => .round
  | .high => .high

/-- The marked value of the feature of a line: [+front], which is the paper's [−BACK], [+round]
and [−high]. -/
def markedValue : Line → Bool
  | .back => true
  | .round => true
  | .high => false

/-- The element on a line: I on the BACK line, U on the ROUND line and A on the HIGH line. -/
def element : Line → Element
  | .back => .I
  | .round => .U
  | .high => .A

theorem feature_injective : Function.Injective feature := by decide

theorem element_injective : Function.Injective element := by decide

/-- (1): The element on a line, as a feature matrix. -/
def matrix : Line → Phonology.Segment
  | .back => [−round, +front, +high, −atr, −low]
  | .round => [+round, −front, +high, −atr, −low]
  | .high => [−round, −front, −high, −atr, +low]

end Line

/-- (4): The cold vowel, the matrix with no marked value. -/
def cold : Phonology.Segment := [−round, −front, +high, −atr, −low]

/-- The lines in order. -/
def lines : List Line := [.back, .round, .high]

theorem mem_lines (l : Line) : l ∈ lines := by cases l <;> decide

-- §1.2: an element has the marked value of its own line and the unmarked value of the others
theorem Line.matrix_apply_feature (l l' : Line) :
    l.matrix l'.feature = some (if l' = l then l'.markedValue else !l'.markedValue) := by
  cases l <;> cases l' <;> decide

-- (4): the cold vowel has the unmarked value of every line
theorem cold_apply_feature (l : Line) : cold l.feature = some (!l.markedValue) := by
  cases l <;> decide

/-! ### Fusion -/

/-- (5): Fusion of the element of the line `l`, as operator, into a head. The head takes the
value of the operator's hot feature and keeps its other values. -/
def fuse (l : Line) (head : Phonology.Segment) : Phonology.Segment :=
  head.setFeature l.feature l.markedValue

variable {l l' : Line} {head : Phonology.Segment} {f : Feature} {ops : List Line} {m : MR}

@[simp] theorem fuse_apply_self : fuse l head l.feature = some l.markedValue :=
  Phonology.Segment.setFeature_apply_self ..

theorem fuse_apply_of_ne (hf : l.feature ≠ f) : fuse l head f = head f :=
  Phonology.Segment.setFeature_apply_of_ne hf ..

theorem foldr_fuse_apply_feature (ops : List Line) (head : Phonology.Segment) (l : Line) :
    ops.foldr fuse head l.feature =
      if l ∈ ops then some l.markedValue else head l.feature := by
  induction ops with
  | nil => simp
  | cons l' r ih =>
    rw [List.foldr_cons]
    by_cases h : l' = l
    · simp [h]
    · rw [fuse_apply_of_ne (fun hf ↦ h (Line.feature_injective hf)), ih]
      simp [Ne.symm h]

theorem foldr_fuse_apply_of_forall_ne (hf : ∀ l : Line, l.feature ≠ f) (ops : List Line)
    (head : Phonology.Segment) : ops.foldr fuse head f = head f := by
  induction ops with
  | nil => rfl
  | cons l r ih => rw [List.foldr_cons, fuse_apply_of_ne (hf l), ih]

-- (9): an element fused into the cold vowel is the element itself, except A, which is [+low]
theorem fuse_cold_eq_matrix_iff (l : Line) : fuse l cold = l.matrix ↔ l ≠ .high := by
  cases l <;> decide

/-! ### The matrix of an expression -/

/-- The lines whose element is in a set of elements. -/
def linesOf (s : Finset Element) : List Line := lines.filter (·.element ∈ s)

@[simp] theorem mem_linesOf {s : Finset Element} : l ∈ linesOf s ↔ l.element ∈ s := by
  simp [linesOf, mem_lines]

/-- The matrix of the head of an expression: that of its head, or the cold vowel if it has no
head. -/
def headMatrix (m : MR) : Phonology.Segment := ((linesOf m.heads).head?.map Line.matrix).getD cold

/-- The matrix of an expression: its operators fused into its head. -/
def interpret (m : MR) : Phonology.Segment :=
  (linesOf (m.elements \ m.heads)).foldr fuse (headMatrix m)

/-- The marked values of an expression, one for each of its elements. -/
def marked (m : MR) : Phonology.Segment := (linesOf m.elements).foldr fuse ⊥

theorem marked_apply_feature (m : MR) (l : Line) :
    marked m l.feature = if l.element ∈ m.elements then some l.markedValue else none := by
  simp [marked, foldr_fuse_apply_feature]

theorem marked_apply_of_forall_ne (hf : ∀ l : Line, l.feature ≠ f) (m : MR) : marked m f = none :=
  foldr_fuse_apply_of_forall_ne hf ..

private theorem linesOf_heads (hm : m.heads.card ≤ 1) (hl : l.element ∈ m.heads) :
    linesOf m.heads = [l] := by
  have h : ∀ l' : Line, l'.element ∈ m.heads ↔ l' = l := fun l' ↦
    ⟨fun h' ↦ Line.element_injective (Finset.card_le_one.1 hm _ h' _ hl), fun h' ↦ h' ▸ hl⟩
  simp only [linesOf, h, lines]
  cases l <;> decide

private theorem headMatrix_apply_feature (hm : m.heads.card ≤ 1) (l : Line) :
    headMatrix m l.feature =
      some (if l.element ∈ m.heads then l.markedValue else !l.markedValue) := by
  rw [headMatrix]
  cases h : (linesOf m.heads).head? with
  | none =>
    have hl : l.element ∉ m.heads := fun hl ↦ by simp [linesOf_heads hm hl] at h
    simp [hl, cold_apply_feature]
  | some l' =>
    have hl' : l'.element ∈ m.heads := mem_linesOf.1 (List.mem_of_mem_head? h)
    have hiff : l.element ∈ m.heads ↔ l = l' :=
      ⟨fun hl ↦ Line.element_injective (Finset.card_le_one.1 hm _ hl _ hl'), fun hl ↦ hl ▸ hl'⟩
    simp [Line.matrix_apply_feature, hiff]

/-- The value of an expression with at most one head on the feature of a line is marked if and
only if the expression has the element of that line, as head or as operator. -/
theorem interpret_apply_feature (hm : m.heads.card ≤ 1) (l : Line) :
    interpret m l.feature =
      some (if l.element ∈ m.elements then l.markedValue else !l.markedValue) := by
  rw [interpret, foldr_fuse_apply_feature, headMatrix_apply_feature hm]
  by_cases he : l.element ∈ m.elements <;> by_cases hh : l.element ∈ m.heads
  · simp [he, hh]
  · simp [he, hh]
  · exact absurd (m.heads_subset hh) he
  · simp [he, hh]

-- on a feature that names no line, the value of an expression is that of its head
theorem interpret_apply_of_forall_ne (hf : ∀ l : Line, l.feature ≠ f) (m : MR) :
    interpret m f = headMatrix m f :=
  foldr_fuse_apply_of_forall_ne hf ..

/-- (3): The matrix of an expression with at most one head is its marked values, with the other
values those of its head. On the lines these are the values of the cold vowel. -/
theorem interpret_eq_marked_or (hm : m.heads.card ≤ 1) :
    interpret m = (marked m).or (headMatrix m) := by
  refine Phonology.Segment.ext' fun f ↦ ?_
  rw [Phonology.Segment.or_apply]
  by_cases hf : ∃ l : Line, l.feature = f
  · obtain ⟨l, rfl⟩ := hf
    rw [interpret_apply_feature hm, marked_apply_feature, headMatrix_apply_feature hm]
    by_cases he : l.element ∈ m.elements
    · simp [he]
    · have hh : l.element ∉ m.heads := fun hh ↦ he (m.heads_subset hh)
      simp [he, hh]
  · rw [not_exists] at hf
    rw [interpret_apply_of_forall_ne hf, marked_apply_of_forall_ne hf]
    rfl

/-! ### The fusions of the paper -/

-- (5): the matrix of a head with one operator is the fusion of the two
theorem interpret_headedSimplex_sup_simplex : ∀ h o : Line, h ≠ o →
    interpret (.headedSimplex h.element ⊔ .simplex o.element) = fuse o h.matrix := by
  decide +kernel

-- (9): an expression with no head has the cold vowel as its head
theorem interpret_simplex : ∀ o : Line, interpret (.simplex o.element) = fuse o cold := by
  decide +kernel

theorem interpret_headedSimplex : ∀ h : Line, interpret (.headedSimplex h.element) = h.matrix := by
  decide +kernel

theorem interpret_bot : interpret ⊥ = cold := by decide +kernel

-- (7), (8): fusion is not symmetric: A fused into I is [−low], and I fused into A is [+low]
theorem fuse_high_back_ne : fuse .high (Line.matrix .back) ≠ fuse .back (Line.matrix .high) := by
  decide +kernel

/-- The features of the matrices of (1). -/
def features : Finset Feature := {.round, .front, .high, .atr, .low}

/-- On the features of (1), each matrix is the chart's vowel that the paper labels it with: the
elements I, U and A are [i], [u] and [a], the fusions of (7), (8) and (9) are [ɛ], [æ] and [ə],
and A fused into U is [ɔ]. -/
theorem eqOn_ofChart :
    Set.EqOn (interpret (.headedSimplex .I)) (Phonology.Segment.ofChart .«i») ↑features ∧
      Set.EqOn (interpret (.headedSimplex .U)) (Phonology.Segment.ofChart .«u») ↑features ∧
      Set.EqOn (interpret (.headedSimplex .A)) (Phonology.Segment.ofChart .«a») ↑features ∧
      Set.EqOn (interpret (.headedSimplex .I ⊔ .simplex .A)) (Phonology.Segment.ofChart .«ɛ»)
        ↑features ∧
      Set.EqOn (interpret (.headedSimplex .A ⊔ .simplex .I)) (Phonology.Segment.ofChart .«æ»)
        ↑features ∧
      Set.EqOn (interpret (.simplex .A)) (Phonology.Segment.ofChart .«ə») ↑features ∧
      Set.EqOn (interpret (.headedSimplex .U ⊔ .simplex .A)) (Phonology.Segment.ofChart .«ɔ»)
        ↑features := by
  decide +kernel

-- the matrices do not separate a central vowel from a back one: A is also the chart's [ɑ], A
-- fused into the cold vowel its [ʌ], and the cold vowel both its [ɨ] and its [ɯ]
theorem eqOn_ofChart_back :
    Set.EqOn (interpret (.headedSimplex .A)) (Phonology.Segment.ofChart .«ɑ») ↑features ∧
      Set.EqOn (interpret (.simplex .A)) (Phonology.Segment.ofChart .«ʌ») ↑features ∧
      Set.EqOn cold (Phonology.Segment.ofChart .«ɨ») ↑features ∧
      Set.EqOn cold (Phonology.Segment.ofChart .«ɯ») ↑features := by
  decide +kernel

/-! ### Lines as feature tiers -/

/-- The tiers of the paper: the skeleton and the lines (§1.2). -/
inductive Tier where
  | skeleton
  | line (l : Line)
  deriving DecidableEq, Fintype

/-- A tier of the paper as a tier of a representation of elements. -/
def toElementTier : Tier → ElementTheory.Tier
  | .skeleton => .skeleton
  | .line l => .line l.element

section FeatureGeometry

open Phonology.FeatureGeometry

variable {N : Type}

/-- A tier of the paper as a tier of a feature geometry: the timing slots, and the feature of a
line. -/
def toFeatureTier : Tier → Option (N ⊕ Feature)
  | .skeleton => none
  | .line l => some (.inr l.feature)

/-- The relabelling of the tiers of the paper: a slot loses its label, and a token of an element
becomes the marked value of its line. -/
def relabel : ∀ c, ElementTheory.Tiers (toElementTier c) →
    FeatureGeometry.Tiers N Feature Bool (toFeatureTier (N := N) c)
  | .skeleton, _ => PUnit.unit
  | .line l, _ => l.markedValue

/-- The marked values of a position: those of its expression, and none if it has no root
node. -/
def spec (p : Position) : Feature → Option Bool := fun f ↦ p.melody.elim none (marked · f)

theorem spec_apply_feature (p : Position) (l : Line) {b : Bool} :
    spec p l.feature = some b ↔ b = l.markedValue ∧ ∃ m ∈ p.melody, l.element ∈ m.elements := by
  cases hp : p.melody with
  | none => simp [spec, hp]
  | some m =>
    simp only [spec, hp, Option.elim_some, marked_apply_feature]
    split_ifs with h <;> simp [h, eq_comm]

variable [PartialOrder N] [OrderBot N] [PredOrder N] [DecidableEq N] [DecidableLE N]
  [IsPredArchimedean N] [Fintype N] (node : Feature → Option N)

private theorem dominates_ofPosition_line_iff (p : Position) (l : Line) (i j : ℕ) :
    (ofPosition p).Dominates ElementTheory.tiers i (.line l.element) j ↔
      i = 0 ∧ j = 0 ∧ ∃ m ∈ p.melody, l.element ∈ m.elements := by
  constructor
  · intro h
    have hi : i < 1 := h.lt_length (by simp)
    have hj := h.lt_length_right hi
    have h1 := p.length_word_le_one (.line l.element)
    rw [word_ofPosition] at hj
    exact ⟨by omega, by omega, Position.word_line_ne_nil_iff.1 (List.ne_nil_of_length_pos
      (by omega))⟩
  · rintro ⟨rfl, rfl, h⟩
    exact dominates_ofPosition (Position.word_line_ne_nil_iff.2 h)

private theorem dominates_ofSpec_feature_iff (hnode : ∀ l : Line, (node l.feature).isSome)
    (p : Position) (l : Line) (i j : ℕ) :
    (ofSpec node (spec p)).Dominates (FeatureGeometry.tiers node) i (some (.inr l.feature)) j ↔
      i = 0 ∧ j = 0 ∧ ∃ m ∈ p.melody, l.element ∈ m.elements := by
  have hword : (ofSpec node (spec p)).word (some (.inr l.feature)) =
      (spec p l.feature).toList := by
    show (if (node l.feature).isSome then (spec p l.feature).toList else []) = _
    simp only [hnode l, ↓reduceIte]
  constructor
  · intro h
    have hi : i < 1 := h.lt_length (by simp [FeatureGeometry.tiers])
    have hj := h.lt_length_right hi
    rw [hword] at hj
    cases hs : spec p l.feature with
    | none => simp [hs] at hj
    | some b =>
      rw [hs] at hj
      exact ⟨by omega, by simpa using hj, ((spec_apply_feature p l).1 hs).2⟩
  · rintro ⟨rfl, rfl, h⟩
    have hs : spec p l.feature = some l.markedValue := (spec_apply_feature p l).2 ⟨rfl, h⟩
    obtain ⟨q, hq, hb⟩ := AR.mem_melody_iff_exists_dominates.1
      (mem_melody_ofSpec_iff.2 ⟨hnode l, hs⟩)
    rw [hword, hs] at hb
    obtain rfl : q = 0 := by
      have := (List.getElem?_eq_some_iff.1 hb).1
      simpa using this
    exact hq

private theorem flatten_comapDomain_ofPosition (hnode : ∀ l : Line, (node l.feature).isSome)
    (p : Position) :
    (((ofPosition p).flatten ElementTheory.tiers).comapDomain toElementTier).mapRange relabel =
      ((ofSpec node (spec p)).flatten (FeatureGeometry.tiers node)).comapDomain
        toFeatureTier := by
  refine AR.ext (funext fun c ↦ ?_) fun c c' i j ↦ ?_
  · rcases c with _ | l
    · rfl
    · show (p.word (.line l.element)).map (fun _ ↦ l.markedValue) =
        if (node l.feature).isSome then (spec p l.feature).toList else []
      simp only [hnode l, ↓reduceIte]
      by_cases h : ∃ m ∈ p.melody, l.element ∈ m.elements
      · obtain ⟨m, hm, he⟩ := h
        rw [(spec_apply_feature p l).2 ⟨rfl, m, hm, he⟩]
        simp [Position.word, Option.mem_def.1 hm, he]
      · have hs : spec p l.feature = none := by
          cases hs : spec p l.feature with
          | none => rfl
          | some b => exact absurd ((spec_apply_feature p l).1 hs).2 h
        have hw : p.word (.line l.element) = [] := by
          by_contra hw
          exact h (Position.word_line_ne_nil_iff.1 hw)
        simp [hs, hw]
  · rw [AR.link_mapRange, AR.link_comapDomain, AR.link_comapDomain, AR.link_flatten_iff,
      AR.link_flatten_iff]
    have hroot : (FeatureGeometry.tiers node).root = none := rfl
    rcases c with _ | l <;> rcases c' with _ | l' <;>
      simp [toElementTier, toFeatureTier, hroot, dominates_ofPosition_line_iff,
        dominates_ofSpec_feature_iff node hnode]

/-- With each position linked to the tokens it dominates, the representation of elements and the
feature geometry of the marked values are the same representation on the skeleton and the lines,
in any geometry that places the features of the lines. -/
theorem flatten_comapDomain_ofForm (hnode : ∀ l : Line, (node l.feature).isSome)
    (w : List Position) :
    (((ElementTheory.ofForm w).flatten ElementTheory.tiers).comapDomain toElementTier).mapRange
        relabel =
      ((ofWord node (w.map spec)).flatten (FeatureGeometry.tiers node)).comapDomain
        toFeatureTier := by
  induction w with
  | nil => simp [ElementTheory.ofForm, ofWord]
  | cons p w ih =>
    have h1 : ElementTheory.ofForm (p :: w) = ofPosition p * ElementTheory.ofForm w := rfl
    have h2 : ofWord node ((p :: w).map spec) = ofSpec node (spec p) * ofWord node (w.map spec) :=
      rfl
    rw [h1, h2, AR.flatten_mul, AR.flatten_mul, AR.comapDomain_mul, AR.comapDomain_mul,
      AR.mapRange_mul, ih, flatten_comapDomain_ofPosition node hnode]

end FeatureGeometry

/-! ### The intermediate tiers -/

/-- A geometry with one class node, from which the features of the lines hang. -/
def classed : Feature → Option (Fin 2) := fun f ↦
  if f ∈ lines.map Line.feature then some 1 else none

/-- (7): the position of [ɛ], with I as head and A as operator. -/
def mid : Position := ⟨.V, some (.headedSimplex .I ⊔ .simplex .A)⟩

/-- [ɛ] followed by a position with no root node, in the geometry with a class node, with each
slot linked to what it dominates and only the tiers of the paper kept. -/
def flattened : AR fun c ↦ FeatureGeometry.Tiers (Fin 2) Feature Bool (toFeatureTier c) :=
  ((Phonology.FeatureGeometry.ofWord classed ([mid, ⟨.V, none⟩].map spec)).flatten
    (Phonology.FeatureGeometry.tiers classed)).comapDomain toFeatureTier

-- the first slot has a line to its token on the BACK line and on the HIGH line and none on the
-- ROUND line, and the slot with no root node has no line
theorem lines_flattened :
    flattened.lines .skeleton (.line .back) = {(0, 0)} ∧
      flattened.lines .skeleton (.line .high) = {(0, 0)} ∧
      flattened.lines .skeleton (.line .round) = ∅ := by
  decide +kernel

-- without the flattening, the restriction to the skeleton and the lines has no line: in both
-- representations the lines run through a tier that the paper does not have
theorem lines_comapDomain_eq_empty :
    (∀ c c', ((ElementTheory.ofForm [mid]).comapDomain toElementTier).lines c c' = ∅) ∧
      ∀ c c', ((Phonology.FeatureGeometry.ofWord classed ([mid].map spec)).comapDomain
        (toFeatureTier (N := Fin 2))).lines c c' = ∅ := by
  decide +kernel

end KayeLowenstammVergnaud1985
