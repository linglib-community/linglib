/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Order.SuccPred.Fin
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Phonology.Autosegmental.Map
public import Linglib.Phonology.FeatureGeometry.Linking
public import Linglib.Phonology.GovernmentPhonology.ElementTheory.Autosegmental
public import Linglib.Phonology.Segmental.PHOIBLE

/-!
# Kaye, Lowenstamm and Vergnaud (1985): The internal structure of phonological elements

An element is a fully specified feature matrix in which exactly one feature has its marked
value. That feature is the hot feature of the element. The element I is [−back], U is [+round]
and A is [−high]. The cold vowel is the matrix with no marked value. Each element lies on a
line named by its hot feature.

Two matrices combine by fusion: the head takes the value of the operator's hot feature and keeps
its other values. We define `fuse` and the matrix `interpret m` of a melodic expression `m`,
its operators fused into its head. The main theorem, `interpret_apply_feature`, says that the
value of an expression on the feature of a line is marked if and only if the expression has the
element of that line, whether as head or as operator. Only a feature that names no line depends
on which element is the head.

The lines are therefore feature tiers. Restricted to the skeleton, the root nodes and the lines,
the representation of a form in Element Theory is the representation in a feature geometry of
its marked values, when the features hang from the root node and every position has a root
node.

## Implementation notes

* The paper links elements to positions directly. `ElementTheory.ofForm` has a root node between
  a position and its elements, and so has `Phonology.FeatureGeometry.ofWord`.
* An expression of the paper has one head. `ElementTheory.MR` allows several, and `headMatrix`
  takes the first in the order of the lines.
* The matrices have one feature of backness. Those that the paper labels [a] and [ə] are
  [+back], as the chart's [ɑ] and [ʌ] are.

## TODO

* Fused lines, on which two elements cannot combine, and the ATR element.
* Charm, government, and the vowel system of Kpokolo.
* With a class node between the root node and a feature, the two representations agree only
  after the class node is contracted.

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

/-- The feature that names a line. -/
def feature : Line → Feature
  | .back => .back
  | .round => .round
  | .high => .high

/-- The marked value of the feature of a line: [−back], [+round] and [−high]. -/
def markedValue : Line → Bool
  | .back => false
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
  | .back => [−round, −back, +high, −atr, −low]
  | .round => [+round, +back, +high, −atr, −low]
  | .high => [−round, +back, −high, −atr, +low]

end Line

/-- (4): The cold vowel, the matrix with no marked value. -/
def cold : Phonology.Segment := [−round, +back, +high, −atr, −low]

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
def features : Finset Feature := {.round, .back, .high, .atr, .low}

/-- On the features of (1), the elements I, U and A are the chart's [i], [u] and [ɑ], the fusions
of (7) and (8) are its [ɛ] and [æ], and A fused into U is its [ɔ]. -/
theorem eqOn_ofChart :
    Set.EqOn (interpret (.headedSimplex .I)) (Phonology.Segment.ofChart .«i») ↑features ∧
      Set.EqOn (interpret (.headedSimplex .U)) (Phonology.Segment.ofChart .«u») ↑features ∧
      Set.EqOn (interpret (.headedSimplex .A)) (Phonology.Segment.ofChart .«ɑ») ↑features ∧
      Set.EqOn (interpret (.headedSimplex .I ⊔ .simplex .A)) (Phonology.Segment.ofChart .«ɛ»)
        ↑features ∧
      Set.EqOn (interpret (.headedSimplex .A ⊔ .simplex .I)) (Phonology.Segment.ofChart .«æ»)
        ↑features ∧
      Set.EqOn (interpret (.headedSimplex .U ⊔ .simplex .A)) (Phonology.Segment.ofChart .«ɔ»)
        ↑features := by
  decide +kernel

-- (9): the matrices labelled [a] and [ə] are the chart's [ɑ] and [ʌ]; they differ from its [a]
-- and [ə] in [back] only
theorem eqOn_ofChart_central :
    Set.EqOn (interpret (.simplex .A)) (Phonology.Segment.ofChart .«ʌ») ↑features ∧
      Set.EqOn (interpret (.headedSimplex .A)) (Phonology.Segment.ofChart .«a»)
        ↑(features.erase .back) ∧
      Set.EqOn (interpret (.simplex .A)) (Phonology.Segment.ofChart .«ə»)
        ↑(features.erase .back) ∧
      interpret (.headedSimplex .A) Feature.back ≠ (Phonology.Segment.ofChart .«a») Feature.back ∧
      interpret (.simplex .A) Feature.back ≠ (Phonology.Segment.ofChart .«ə») Feature.back := by
  decide +kernel

/-! ### Lines as feature tiers -/

/-- The tiers that a representation of elements and a feature geometry share: the skeleton, the
root nodes and the lines. -/
inductive SharedTier where
  | skeleton
  | rootNode
  | line (l : Line)
  deriving DecidableEq, Fintype

/-- A shared tier as a tier of a representation of elements. -/
def toElementTier : SharedTier → ElementTheory.Tier
  | .skeleton => .skeleton
  | .rootNode => .rootNode
  | .line l => .line l.element

theorem toElementTier_injective : Function.Injective toElementTier := by
  rintro (_ | _ | l) (_ | _ | l') h <;> simp_all [toElementTier]
  exact Line.element_injective h

section FeatureGeometry

open Phonology.FeatureGeometry

variable {N : Type} [PartialOrder N] [OrderBot N]

/-- A shared tier as a tier of a feature geometry: the timing slots, the root node, and the
feature of a line. -/
def toFeatureTier : SharedTier → Option (N ⊕ Feature)
  | .skeleton => none
  | .rootNode => some (.inl ⊥)
  | .line l => some (.inr l.feature)

theorem toFeatureTier_injective : Function.Injective (toFeatureTier (N := N)) := by
  rintro (_ | _ | l) (_ | _ | l') h <;> simp_all [toFeatureTier]
  exact Line.feature_injective h

/-- The relabelling of the shared tiers: a slot and a root node lose their labels, and a token of
an element becomes the marked value of its line. -/
def relabel : ∀ c, ElementTheory.Tiers (toElementTier c) →
    FeatureGeometry.Tiers N Feature Bool (toFeatureTier (N := N) c)
  | .skeleton, _ => PUnit.unit
  | .rootNode, _ => PUnit.unit
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

variable [PredOrder N] [DecidableEq N] [DecidableLE N] (node : Feature → Option N)
  {w : List Position} {k : ℕ} {b : Bool}

private theorem mapRange_comapDomain_ofPosition (hnode : ∀ l : Line, node l.feature = some ⊥)
    (p : Position) (hp : p.melody.isSome) :
    ((ofPosition p).comapDomain toElementTier).mapRange relabel =
      (ofSpec node (spec p)).comapDomain toFeatureTier := by
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.1 hp
  rw [ofPosition, ofSpec, AR.comapDomain_fromRel _ toElementTier_injective, AR.mapRange_fromRel,
    AR.comapDomain_fromRel _ toFeatureTier_injective]
  have hw : (fun c ↦ (p.word (toElementTier c)).map (relabel (N := N) c)) =
      fun c ↦ tierWord node (spec p) (toFeatureTier c) := by
    funext c
    rcases c with _ | _ | l
    · rfl
    · simp [toElementTier, toFeatureTier, Position.word, tierWord, hm, relabel]
    · have := spec_apply_feature p l (b := l.markedValue)
      by_cases he : l.element ∈ m.elements
      · have hs : spec p l.feature = some l.markedValue := this.2 ⟨rfl, m, hm, he⟩
        simp [toElementTier, toFeatureTier, Position.word, tierWord, hm, he, hnode, hs, relabel]
      · have hs : spec p l.feature = none := by simp [spec, hm, marked_apply_feature, he]
        simp [toElementTier, toFeatureTier, Position.word, tierWord, hm, he, hnode, hs]
  have hw' : ∀ c, (p.word (toElementTier c)).map (relabel (N := N) c) =
      tierWord node (spec p) (toFeatureTier c) := fun c ↦ congrFun hw c
  refine AR.ext hw fun c c' i j ↦ ?_
  rw [AR.link_fromRel, AR.link_fromRel, hw' c, hw' c']
  refine and_congr_right fun _ ↦ and_congr_right fun _ ↦ and_congr_right fun _ ↦ ?_
  rcases c with _ | _ | l <;> rcases c' with _ | _ | l' <;>
    simp [toElementTier, toFeatureTier, Tier.parent, tierParent, hnode]

/-- When the features of the lines hang from the root node and every position has a root node,
the representation of elements and the feature geometry of the marked values are the same
representation on the shared tiers. -/
theorem mapRange_comapDomain_ofForm (hnode : ∀ l : Line, node l.feature = some ⊥)
    (hw : ∀ p ∈ w, p.melody.isSome) :
    ((ElementTheory.ofForm w).comapDomain toElementTier).mapRange relabel =
      (ofWord node (w.map spec)).comapDomain toFeatureTier := by
  rw [ElementTheory.ofForm, ofWord, ← AR.comapDomainHom_apply, ← AR.mapRangeHom_apply,
    ← AR.comapDomainHom_apply, map_list_prod, map_list_prod, map_list_prod, List.map_map,
    List.map_map, List.map_map, List.map_map]
  exact congrArg List.prod (List.map_congr_left fun p hp ↦
    mapRange_comapDomain_ofPosition node hnode p (hw p hp))

variable [IsPredArchimedean N] [Fintype N]

/-- In any geometry that places the feature of a line, a slot dominates the marked value on the
tier of that feature if and only if it dominates a token on the line in the representation of
elements. -/
theorem mem_melody_ofWord_feature_iff (hl : (node l.feature).isSome) :
    b ∈ (ofWord node (w.map spec)).melody (FeatureGeometry.tiers node) k
        (some (.inr l.feature)) ↔
      b = l.markedValue ∧
        ∃ s, s ∈ (ElementTheory.ofForm w).melody ElementTheory.tiers k (.line l.element) := by
  rw [mem_melody_ofWord_iff, exists_mem_melody_line_ofForm_iff]
  constructor
  · rintro ⟨hk, -, h⟩
    rw [List.length_map] at hk
    rw [List.getElem_map, spec_apply_feature] at h
    exact ⟨h.1, w[k], List.getElem?_eq_getElem hk, h.2⟩
  · rintro ⟨rfl, p, hp, h⟩
    obtain ⟨hk, rfl⟩ := List.getElem?_eq_some_iff.1 hp
    exact ⟨by simpa using hk, hl, by rw [List.getElem_map, spec_apply_feature]; exact ⟨rfl, h⟩⟩

end FeatureGeometry

/-! ### Where the two representations differ -/

/-- The geometry in which the features of the lines hang from the root node. -/
def flat : Feature → Option (Fin 1) := fun f ↦ if f ∈ lines.map Line.feature then some 0 else none

/-- A geometry with one class node, from which the features of the lines hang. -/
def classed : Feature → Option (Fin 2) := fun f ↦
  if f ∈ lines.map Line.feature then some 1 else none

/-- (7): the position of [ɛ], with I as head and A as operator. -/
def mid : Position := ⟨.V, some (.headedSimplex .I ⊔ .simplex .A)⟩

-- a position with no root node has a root node in the feature geometry
theorem comapDomain_ne_of_rootless :
    ((ElementTheory.ofForm [mid, ⟨.V, none⟩]).comapDomain toElementTier).mapRange relabel ≠
      (Phonology.FeatureGeometry.ofWord flat ([mid, ⟨.V, none⟩].map spec)).comapDomain
        toFeatureTier := by
  decide +kernel

-- under a class node the feature tiers hold the same tokens, with no line to the root node
theorem comapDomain_ne_of_classed :
    ((ElementTheory.ofForm [mid]).comapDomain toElementTier).mapRange relabel ≠
        (Phonology.FeatureGeometry.ofWord classed ([mid].map spec)).comapDomain
          toFeatureTier ∧
      ∀ c, (((ElementTheory.ofForm [mid]).comapDomain toElementTier).mapRange
          (relabel (N := Fin 2))).word c =
        ((Phonology.FeatureGeometry.ofWord classed ([mid].map spec)).comapDomain
          toFeatureTier).word c := by
  decide +kernel

end KayeLowenstammVergnaud1985
