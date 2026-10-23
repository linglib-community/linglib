module

public import Mathlib.Data.List.Infix
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Order.Interval.Set.OrdConnected
public import Mathlib.Order.UpperLower.Basic
public import Mathlib.Tactic.DeriveFintype

/-!
# Spatial paths

A path is a finite sequence of locations, the spatial counterpart of a temporal interval. Zwarts
gives paths an algebra: concatenation, defined only when one path ends where the next starts, the
subpath order, and Krifka's adjacency of paths that share an endpoint. Zwarts's own paths are
continuous curves, mathlib's topological `_root_.Path`, but he allows sequences of places as
compatible with the algebra, and they keep every operation computable.

Pantcheva classifies paths by where they are inside a region. On any path parametrized by a
bounded linear order of positions, a sequence of places or a curve, the positions inside the
region form a set, and its order-theoretic shape is the path's: an upper set for a cofinal path
(*to*), a lower set for a coinitial one (*from*), an interval missing both ends for a transitive
one (*past*), the last position alone for a terminative one (*up to*). Reparametrizing keeps the
shape and reversing the order reverses it, so a source path is a reversed goal path. An event
domain's spatial trace sends each event to the path it traverses, as its temporal trace sends it
to its run time.

## Main definitions

* `Spatial.Path`: a directed trajectory, a source with later steps, ending at `Path.goal`.
* `Spatial.Path.IsConcat`, `Subpath`, `adjacent`, `reverse`: the path algebra.
* `Spatial.Path.Direction`: Place, Goal, Source and Route, in containment order.
* `Spatial.Path.Shape`, `Shape.direction`, `Shape.transition`: the eight shapes.
* `Spatial.Path.IsCofinal`, `IsCoinitial`, `IsTransitive`, `IsTerminative`, `IsEgressive`,
  `IsProlative`, `IsApproximative`, `IsRecessive`, `HasShape`: the shapes of a parametrized
  path relative to a region.
* `Spatial.Path.toFun`: a path's places indexed by their positions.
* `Spatial.Localization`: interior, surface or exterior.
* `Event.SpatialTrace`: the spatial trace of an event domain.

## Main results

* `Spatial.Path.Direction.lt_iff_shells_ssubset`: the containment order is strict inclusion of
  head stacks.
* `Spatial.Path.Shape.exists_direction_transition_iff`: a direction and a transition combine
  into a shape exactly when the direction is not Place and a route is not delimited.
* `Spatial.Path.hasShape_comp`, `hasShape_comp_ofDual`: reparametrizing keeps the shape, and
  traversing the other way reverses it.
* `Spatial.Path.hasShape_reverse`: reversing a path reverses its shape.
* `Spatial.Path.IsCofinal.not_isCoinitial`: no path is both cofinal and coinitial.

## References

* [zwarts-2005]
* [krifka-1998]
* [pantcheva-2011]
-/

@[expose] public section

namespace Spatial

/-- A path is a directed trajectory through space, given by the finite sequence of locations it
visits. -/
structure Path (Loc : Type*) where
  /-- The location the path starts from. -/
  source : Loc
  /-- The later locations, which are empty for a constant path. -/
  steps : List Loc
  deriving DecidableEq, Repr

namespace Path

variable {Loc : Type*}

/-- The goal of a path is its last location. -/
def goal (p : Path Loc) : Loc := p.steps.getLastD p.source

/-- The points of a path are its locations from source to goal. -/
def points (p : Path Loc) : List Loc := p.source :: p.steps

/-- The constant path at `l` visits only `l`. -/
def const (l : Loc) : Path Loc := ⟨l, []⟩

@[simp] theorem goal_const (l : Loc) : (const l).goal = l := rfl

theorem points_ne_nil (p : Path Loc) : p.points ≠ [] := List.cons_ne_nil _ _

theorem points_injective : Function.Injective (points : Path Loc → List Loc) := by
  rintro ⟨s, l⟩ ⟨s', l'⟩ h
  simpa [points] using h

private theorem getLastD_append {α : Type*} (l₁ l₂ : List α) (d : α) :
    (l₁ ++ l₂).getLastD d = l₂.getLastD (l₁.getLastD d) := by
  simp only [List.getLastD_eq_getLast?, List.getLast?_append]
  cases l₂.getLast? <;> simp

/-! ### Concatenation and subpaths -/

/-- `IsConcat p q r` says that `r` is the concatenation `p + q`, defined only when `p` ends where
`q` starts. -/
def IsConcat (p q r : Path Loc) : Prop :=
  p.goal = q.source ∧ r = ⟨p.source, p.steps ++ q.steps⟩

theorem IsConcat.source_eq {p q r : Path Loc} (h : IsConcat p q r) :
    r.source = p.source := by rw [h.2]

theorem IsConcat.goal_eq {p q r : Path Loc} (h : IsConcat p q r) :
    r.goal = q.goal := by
  obtain ⟨h1, rfl⟩ := h
  show (p.steps ++ q.steps).getLastD p.source = q.goal
  rw [getLastD_append]
  show q.steps.getLastD p.goal = q.goal
  rw [h1]; rfl

theorem IsConcat.points_eq {p q r : Path Loc} (h : IsConcat p q r) :
    r.points = p.points ++ q.steps := by
  rw [h.2]; simp [points]

theorem isConcat_const (l : Loc) : IsConcat (const l) (const l) (const l) :=
  ⟨rfl, rfl⟩

/-- `p` is a subpath of `q` when concatenating some paths around `p` yields `q`. -/
def Subpath (p q : Path Loc) : Prop :=
  ∃ r r' m, IsConcat r p m ∧ IsConcat m r' q

theorem subpath_iff_infix {p q : Path Loc} :
    Subpath p q ↔ p.points <:+: q.points := by
  constructor
  · rintro ⟨r, r', m, hrp, hmq⟩
    refine ⟨r.points.dropLast, r'.steps, ?_⟩
    have hgoal : r.points.getLast r.points_ne_nil = p.source := by
      have : r.points.getLast r.points_ne_nil = r.goal := by
        cases h : r.steps <;>
          simp [points, goal, h, List.getLast_cons,
            List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast]
      rw [this, hrp.1]
    calc r.points.dropLast ++ p.points ++ r'.steps
        = (r.points.dropLast ++ [p.source]) ++ p.steps ++ r'.steps := by
          simp [points]
      _ = r.points ++ p.steps ++ r'.steps := by
          rw [← hgoal, List.dropLast_append_getLast]
      _ = q.points := by rw [hmq.points_eq, hrp.points_eq]
  · rintro ⟨A, B, hAB⟩
    match A with
    | [] =>
      obtain ⟨hs, hst⟩ : q.source = p.source ∧ q.steps = p.steps ++ B := by
        simpa [points, List.cons.injEq] using hAB.symm
      exact ⟨const p.source, ⟨p.goal, B⟩, p,
        ⟨rfl, by cases p; rfl⟩, ⟨rfl, by cases q; simp_all [points]⟩⟩
    | a :: A' =>
      obtain ⟨hs, hst⟩ : q.source = a ∧ q.steps = A' ++ (p.source :: p.steps) ++ B := by
        simpa [points, List.cons.injEq, List.append_assoc] using hAB.symm
      refine ⟨⟨a, A' ++ [p.source]⟩, ⟨p.goal, B⟩,
        ⟨a, (A' ++ [p.source]) ++ p.steps⟩,
        ⟨by simp [goal], rfl⟩, ⟨?_, ?_⟩⟩
      · show ((A' ++ [p.source]) ++ p.steps).getLastD a = p.goal
        rw [getLastD_append, getLastD_append]
        rfl
      · cases q
        simp_all [points, List.append_assoc]

/-- The subpath order is a scoped instance, since paths are also studied under a rival total
lattice sum (the `SemilatticeSup (Path Loc)` of `Studies/GoldbergJackendoff2004.lean`).
Activate it with `open scoped Spatial.Path`. -/
scoped instance instSubpathOrder : PartialOrder (Path Loc) where
  le := Subpath
  le_refl p := subpath_iff_infix.mpr (List.infix_refl _)
  le_trans _ _ _ hab hbc := subpath_iff_infix.mpr
    ((subpath_iff_infix.mp hab).trans (subpath_iff_infix.mp hbc))
  le_antisymm _ _ hab hba := points_injective
    (List.infix_antisymm (subpath_iff_infix.mp hab) (subpath_iff_infix.mp hba))

theorem const_source_le (p : Path Loc) : const p.source ≤ p :=
  subpath_iff_infix.mpr ⟨[], p.steps, rfl⟩

/-! ### Adjacency -/

/-- Two paths are adjacent when the goal of one is the source of the other, Krifka's spatial
adjacency. -/
def adjacent (p1 p2 : Path Loc) : Prop :=
  p1.goal = p2.source ∨ p2.goal = p1.source

theorem adjacent_comm {p1 p2 : Path Loc} :
    p1.adjacent p2 ↔ p2.adjacent p1 :=
  or_comm

@[simp]
theorem adjacent_self {p : Path Loc} :
    p.adjacent p ↔ p.goal = p.source :=
  or_self_iff

/-- Concatenable paths are adjacent. -/
theorem IsConcat.adjacent {p q r : Path Loc} (h : IsConcat p q r) :
    p.adjacent q :=
  Or.inl h.1

/-! ### Reversal -/

/-- The reverse of a path traverses it from its goal to its source. -/
def reverse (p : Path Loc) : Path Loc := ⟨p.goal, p.points.reverse.tail⟩

@[simp] theorem source_reverse (p : Path Loc) : p.reverse.source = p.goal := rfl

@[simp] theorem points_reverse (p : Path Loc) : p.reverse.points = p.points.reverse := by
  obtain ⟨s, l⟩ := p
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l x _ => simp [reverse, points, goal]

@[simp] theorem goal_reverse (p : Path Loc) : p.reverse.goal = p.source := by
  have h : p.reverse.points.getLast (points_ne_nil _) = p.reverse.goal := by
    obtain ⟨s, l⟩ := p.reverse
    cases l using List.reverseRecOn <;> simp [points, goal]
  rw [← h]
  simp only [points_reverse, List.getLast_reverse]
  rfl

@[simp] theorem reverse_reverse (p : Path Loc) : p.reverse.reverse = p :=
  points_injective (by simp)

/-! ### Directions -/

/-- The direction heads of a path, in containment order, Goal built on Place, Source on Goal,
and Route on Source. -/
inductive Direction where
  /-- Place is static location, the base of the others. -/
  | place
  /-- Goal is motion *to*. -/
  | goal
  /-- Source is motion *from*. -/
  | source
  /-- Route is motion *via* or *past*. -/
  | route
  deriving DecidableEq, Repr, Fintype

namespace Direction

/-- The number of heads below a direction. -/
def rank : Direction → Fin 4
  | place => 0
  | goal => 1
  | source => 2
  | route => 3

/-- The heads a direction contains, a downward-closed stack. -/
def shells (d : Direction) : Finset (Fin 4) := Finset.Iic d.rank

/-- Strict rank is strict inclusion of head stacks. -/
theorem lt_iff_shells_ssubset (d₁ d₂ : Direction) :
    d₁.rank < d₂.rank ↔ d₁.shells ⊂ d₂.shells := by
  simp [shells]

/-- The direction of a path traversed the other way swaps Goal and Source and keeps Place and
Route. -/
def reverse : Direction → Direction
  | goal => source
  | source => goal
  | d => d

@[simp] theorem reverse_reverse (d : Direction) : d.reverse.reverse = d := by cases d <;> rfl

end Direction

/-! ### Shapes -/

/-- How a path relates its run inside the region to its run outside. -/
inductive Transition where
  /-- The path changes its relation to the region, as *to* does. -/
  | transitional
  /-- The path changes it at one point, which bounds the motion, as *up to* does. -/
  | delimited
  /-- The path does not change it, as *towards* does. -/
  | nonTransitional
  deriving DecidableEq, Repr, Fintype

/-- The eight shapes of a path relative to a region. -/
inductive Shape where
  /-- A cofinal path runs outside, then inside, as *to* does. -/
  | cofinal
  /-- A coinitial path runs inside, then outside, as *from* does. -/
  | coinitial
  /-- A transitive path runs outside, inside and outside, as *past* does. -/
  | transitive
  /-- A terminative path runs outside up to its goal, which is inside, as *up to* does. -/
  | terminative
  /-- An egressive path starts inside and runs outside, as *starting from* does. -/
  | egressive
  /-- An approximative path runs outside, nearer at each point, as *towards* does. -/
  | approximative
  /-- A recessive path runs outside, farther at each point, as *away from* does. -/
  | recessive
  /-- A prolative path runs inside throughout, as *along* does. -/
  | prolative
  deriving DecidableEq, Repr, Fintype

namespace Shape

/-- The direction of a shape. -/
def direction : Shape → Direction
  | cofinal | terminative | approximative => .goal
  | coinitial | egressive | recessive => .source
  | transitive | prolative => .route

/-- The transition of a shape. -/
def transition : Shape → Transition
  | cofinal | coinitial | transitive => .transitional
  | terminative | egressive => .delimited
  | approximative | recessive | prolative => .nonTransitional

theorem direction_transition_injective :
    Function.Injective fun s : Shape ↦ (s.direction, s.transition) := by
  intro a b h
  cases a <;> cases b <;> simp_all [direction, transition]

/-- A direction and a transition make a shape exactly when the direction is not Place and a
Route is not delimited. -/
theorem exists_direction_transition_iff (d : Direction) (t : Transition) :
    (∃ s : Shape, s.direction = d ∧ s.transition = t) ↔
      d ≠ .place ∧ (d = .route → t ≠ .delimited) := by
  cases d <;> cases t <;> decide

/-- The shape of a path traversed the other way. -/
def reverse : Shape → Shape
  | cofinal => coinitial
  | coinitial => cofinal
  | terminative => egressive
  | egressive => terminative
  | approximative => recessive
  | recessive => approximative
  | s => s

@[simp] theorem reverse_reverse (s : Shape) : s.reverse.reverse = s := by cases s <;> rfl

@[simp] theorem direction_reverse (s : Shape) : s.reverse.direction = s.direction.reverse := by
  cases s <;> rfl

@[simp] theorem transition_reverse (s : Shape) : s.reverse.transition = s.transition := by
  cases s <;> rfl

/-- A shape is bounded when it has a transition, which makes the motion telic. -/
def IsBounded (s : Shape) : Prop := s.transition ≠ .nonTransitional

instance : DecidablePred IsBounded := fun s ↦ inferInstanceAs (Decidable (s.transition ≠ _))

end Shape

/-! ### Shapes relative to a region

A path parametrized by a bounded linear order of positions, a sequence of places or a curve,
has the shape its positions inside a region give it: a cofinal path's form an upper set, a
coinitial path's a lower set, a transitive path's an interval inside the path. -/

section Shapes

open OrderDual Set

variable {ι κ α β : Type*} [LinearOrder ι] [BoundedOrder ι] [LinearOrder κ] [BoundedOrder κ]
  (R : Set α) (γ : ι → α)

/-- A cofinal path starts outside `R`, ends inside it, and stays inside once in, as a path *to*
`R` does. -/
def IsCofinal : Prop := IsUpperSet (γ ⁻¹' R) ∧ γ ⊥ ∉ R ∧ γ ⊤ ∈ R

/-- A coinitial path starts inside `R`, ends outside it, and stays outside once out, as a path
*from* `R` does. -/
def IsCoinitial : Prop := IsLowerSet (γ ⁻¹' R) ∧ γ ⊥ ∈ R ∧ γ ⊤ ∉ R

/-- A transitive path starts and ends outside `R` and is inside it over one stretch, as a path
*past* `R` is. -/
def IsTransitive : Prop := (γ ⁻¹' R).OrdConnected ∧ (γ ⁻¹' R).Nonempty ∧ γ ⊥ ∉ R ∧ γ ⊤ ∉ R

/-- A terminative path is inside `R` at its end only, as a path *up to* `R` is. -/
def IsTerminative : Prop := γ ⁻¹' R = {⊤} ∧ (⊥ : ι) ≠ ⊤

/-- An egressive path is inside `R` at its start only, as a path *starting from* `R` is. -/
def IsEgressive : Prop := γ ⁻¹' R = {⊥} ∧ (⊥ : ι) ≠ ⊤

/-- A prolative path is inside `R` throughout, as a path *along* `R` is. -/
def IsProlative : Prop := ∀ i, γ i ∈ R

/-- An approximative path is outside `R` throughout and nearer to it by `d` at each later
position, as a path *towards* `R` is. -/
def IsApproximative [Preorder β] (d : α → β) : Prop := (∀ i, γ i ∉ R) ∧ StrictAnti (d ∘ γ)

/-- A recessive path is outside `R` throughout and farther from it by `d` at each later position,
as a path *away from* `R` is. -/
def IsRecessive [Preorder β] (d : α → β) : Prop := (∀ i, γ i ∉ R) ∧ StrictMono (d ∘ γ)

/-- `HasShape d R γ s` says that `γ` has shape `s` relative to `R`, `d` measuring nearness to
it. -/
def HasShape [Preorder β] (d : α → β) : Shape → Prop
  | .cofinal => IsCofinal R γ
  | .coinitial => IsCoinitial R γ
  | .transitive => IsTransitive R γ
  | .terminative => IsTerminative R γ
  | .egressive => IsEgressive R γ
  | .approximative => IsApproximative R γ d
  | .recessive => IsRecessive R γ d
  | .prolative => IsProlative R γ

variable {R γ}

theorem IsTerminative.isCofinal (h : IsTerminative R γ) : IsCofinal R γ := by
  obtain ⟨hS, hne⟩ := h
  refine ⟨?_, fun h ↦ ?_, ?_⟩
  · rw [hS, ← Ici_top]; exact isUpperSet_Ici ⊤
  · have : (⊥ : ι) ∈ γ ⁻¹' R := h
    rw [hS] at this
    exact hne this
  · show ⊤ ∈ γ ⁻¹' R; rw [hS]; rfl

/-- No path is both cofinal and coinitial. -/
theorem IsCofinal.not_isCoinitial (h : IsCofinal R γ) : ¬ IsCoinitial R γ :=
  fun h' ↦ h'.2.2 h.2.2

theorem HasShape.comp [Preorder β] {d : α → β} {s : Shape} (h : HasShape R γ d s)
    (e : κ ≃o ι) : HasShape R (γ ∘ e) d s := by
  have hpre : (γ ∘ e) ⁻¹' R = e ⁻¹' (γ ⁻¹' R) := rfl
  have hne : ((⊥ : κ) ≠ ⊤ ↔ (⊥ : ι) ≠ ⊤) := by
    rw [ne_eq, ne_eq, ← e.injective.eq_iff, map_bot, map_top]
  cases s with
  | cofinal => exact ⟨hpre ▸ h.1.preimage e.monotone, by simpa using h.2.1, by simpa using h.2.2⟩
  | coinitial => exact ⟨hpre ▸ h.1.preimage e.monotone, by simpa using h.2.1, by simpa using h.2.2⟩
  | transitive =>
    obtain ⟨hc, ⟨i, hi⟩, h₀, h₁⟩ := h
    exact ⟨hpre ▸ hc.preimage_mono e.monotone, ⟨e.symm i, by simpa using hi⟩,
      by simpa using h₀, by simpa using h₁⟩
  | terminative =>
    refine ⟨?_, hne.2 h.2⟩
    ext k
    show e k ∈ γ ⁻¹' R ↔ k = ⊤
    rw [h.1, mem_singleton_iff, ← map_top e, e.injective.eq_iff]
  | egressive =>
    refine ⟨?_, hne.2 h.2⟩
    ext k
    show e k ∈ γ ⁻¹' R ↔ k = ⊥
    rw [h.1, mem_singleton_iff, ← map_bot e, e.injective.eq_iff]
  | prolative => exact fun k ↦ h (e k)
  | approximative => exact ⟨fun k ↦ h.1 (e k), h.2.comp_strictMono e.strictMono⟩
  | recessive => exact ⟨fun k ↦ h.1 (e k), h.2.comp e.strictMono⟩

/-- Reparametrizing a path by an order isomorphism keeps its shape. -/
theorem hasShape_comp [Preorder β] {d : α → β} (e : κ ≃o ι) {s : Shape} :
    HasShape R (γ ∘ e) d s ↔ HasShape R γ d s :=
  ⟨fun h ↦ by simpa [Function.comp_def] using h.comp e.symm, fun h ↦ h.comp e⟩

/-- Traversing a path the other way, on the dual order of positions, reverses its shape. -/
theorem hasShape_comp_ofDual [Preorder β] {d : α → β} {s : Shape} :
    HasShape R (γ ∘ ofDual) d s ↔ HasShape R γ d s.reverse := by
  have hpre : (γ ∘ ofDual) ⁻¹' R = ofDual ⁻¹' (γ ⁻¹' R) := rfl
  have hne : ((⊥ : ιᵒᵈ) ≠ ⊤ ↔ (⊥ : ι) ≠ ⊤) := by
    rw [ne_eq, ne_eq, ← toDual_top, ← toDual_bot, toDual_inj, eq_comm]
  cases s with
  | cofinal =>
    simp only [HasShape, Shape.reverse, IsCofinal, IsCoinitial, hpre,
      isUpperSet_preimage_ofDual_iff, Function.comp_apply, ofDual_bot, ofDual_top]
    tauto
  | coinitial =>
    simp only [HasShape, Shape.reverse, IsCofinal, IsCoinitial, hpre,
      isLowerSet_preimage_ofDual_iff, Function.comp_apply, ofDual_bot, ofDual_top]
    tauto
  | transitive =>
    simp only [HasShape, Shape.reverse, IsTransitive, hpre, ordConnected_dual,
      Function.comp_apply, ofDual_bot, ofDual_top, OrderDual.ofDual.surjective.nonempty_preimage]
    tauto
  | terminative =>
    refine and_congr ⟨fun h ↦ ?_, fun h ↦ ?_⟩ hne
    · ext i
      have := congrArg (toDual i ∈ ·) h
      simpa [hpre, ← toDual_bot] using this
    · ext i
      rw [hpre, mem_preimage, h, mem_singleton_iff, mem_singleton_iff, ← toDual_bot]
      exact ⟨fun h' ↦ by rw [← h', toDual_ofDual], fun h' ↦ by rw [h', ofDual_toDual]⟩
  | egressive =>
    refine and_congr ⟨fun h ↦ ?_, fun h ↦ ?_⟩ hne
    · ext i
      have := congrArg (toDual i ∈ ·) h
      simpa [hpre, ← toDual_top] using this
    · ext i
      rw [hpre, mem_preimage, h, mem_singleton_iff, mem_singleton_iff, ← toDual_top]
      exact ⟨fun h' ↦ by rw [← h', toDual_ofDual], fun h' ↦ by rw [h', ofDual_toDual]⟩
  | prolative => exact OrderDual.forall
  | approximative =>
    simp only [HasShape, Shape.reverse, IsApproximative, IsRecessive, OrderDual.forall,
      Function.comp_apply, ofDual_toDual, ← Function.comp_assoc, strictAnti_comp_ofDual_iff]
  | recessive =>
    simp only [HasShape, Shape.reverse, IsApproximative, IsRecessive, OrderDual.forall,
      Function.comp_apply, ofDual_toDual, ← Function.comp_assoc, strictMono_comp_ofDual_iff]

end Shapes

/-! ### Sequences of places as parametrized paths -/

variable {Loc : Type*} (p : Path Loc)

/-- A path's places, indexed by their positions. -/
def toFun : Fin (p.steps.length + 1) → Loc := fun i ↦ p.points.get ⟨i, by simp [points]⟩

instance : CoeFun (Path Loc) fun p ↦ Fin (p.steps.length + 1) → Loc := ⟨toFun⟩

@[simp] theorem coe_bot : p ⊥ = p.source := rfl

@[simp] theorem coe_top : p ⊤ = p.goal := by
  obtain ⟨s, l⟩ := p
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l x _ => simp [toFun, points, goal, List.getElem_append_right]

theorem length_steps_reverse : p.reverse.steps.length = p.steps.length := by
  simpa [points] using congrArg List.length (points_reverse p)

/-- The positions of a reversed path, as an order isomorphism onto the dual of the path's. -/
def revIso : Fin (p.reverse.steps.length + 1) ≃o (Fin (p.steps.length + 1))ᵒᵈ :=
  (Fin.castOrderIso (by rw [length_steps_reverse])).trans Fin.revOrderIso.symm

theorem coe_reverse : ⇑p.reverse = (p ∘ OrderDual.ofDual) ∘ p.revIso := by
  funext i
  have h := points_reverse p
  simp only [Function.comp_apply, revIso, OrderIso.trans_apply, Fin.revOrderIso_symm_apply,
    OrderDual.ofDual_toDual]
  simp only [toFun, List.get_eq_getElem, Fin.val_rev, Fin.castOrderIso_apply, Fin.val_cast]
  simp only [h, List.getElem_reverse]
  congr 1
  simp [points]

/-- Reversing a path reverses its shape. -/
theorem hasShape_reverse {β : Type*} [Preorder β] {d : Loc → β} {R : Set Loc} {s : Shape} :
    HasShape R p.reverse d s ↔ HasShape R p d s.reverse := by
  rw [coe_reverse, hasShape_comp, hasShape_comp_ofDual]

end Path

/-! ### Localization -/

/-- The part of the reference object a spatial expression localizes in, orthogonal to the
direction. -/
inductive Localization where
  /-- The interior, as of *in*, *into* and *out of*. -/
  | interior
  /-- The surface, as of *on*, *onto* and *off*. -/
  | surface
  /-- The exterior, as of *at*, *to* and *from*. -/
  | exterior
  deriving DecidableEq, Repr, Fintype

end Spatial

namespace Event

/-- The spatial trace of an event domain `E`, which sends each event to the path its theme
traverses. -/
class SpatialTrace (E : Type*) (Loc : outParam Type*) where
  /-- The path traversed in an event. -/
  σ : E → Spatial.Path Loc

export SpatialTrace (σ)

end Event
