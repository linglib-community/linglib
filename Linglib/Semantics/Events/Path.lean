module

public import Mathlib.Data.List.Infix
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Hom.Bounded
public import Mathlib.Order.Interval.Set.OrdConnected
public import Mathlib.Order.UpperLower.Basic
public import Mathlib.Tactic.DeriveFintype

/-!
# Spatial paths

A path is a finite sequence of locations, directed from a source to a goal. Paths carry a partial
algebra: concatenation is defined only when one path ends where the next starts, and the
[concatenants are subpaths](##Spatial.Path.IsConcat.le_left) of the result, in an order where
[constant paths are minimal](##Spatial.Path.isMin_const).

Relative to a region, a path parametrized by a bounded linear order of positions, those of a
sequence or the unit interval of a curve, has the shape its positions inside the region give it:
an upper set for a cofinal path (*to*), a lower set for a coinitial one (*from*), an interval
missing both ends for a transitive one (*past*), the last position alone for a terminative one
(*up to*). [A path that meets the region has a shape](##Spatial.Path.exists_hasShape_iff) exactly
when those positions are one stretch. [Reversing a path](##Spatial.Path.hasShape_reverse) reverses
its shape, and [concatenation keeps a shape](##Spatial.Path.HasShape.concat) exactly when
[it has no transition](##Spatial.Path.HasShape.not_concat).

## Implementation notes

Zwarts's own paths are constant-speed curves on the unit interval; he takes sequences of places to
be compatible with the same algebra, and they keep every operation computable. Unlike such a
curve, a sequence can repeat a location, so `⟨l, [l]⟩` assigns one point to every position without
being `const l`, and it has `const l` as a proper subpath.

## References

* [zwarts-2005]
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

theorem dropLast_points_append (p : Path Loc) : p.points.dropLast ++ [p.goal] = p.points := by
  have h : p.points.getLast p.points_ne_nil = p.goal := by
    cases h : p.steps <;>
      simp [points, goal, h, List.getLast_cons, List.getLastD_eq_getLast?,
        List.getLast?_eq_some_getLast]
  rw [← h, List.dropLast_append_getLast]

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

theorem IsConcat.points_eq' {p q r : Path Loc} (h : IsConcat p q r) :
    r.points = p.points.dropLast ++ q.points := by
  rw [h.points_eq, ← dropLast_points_append p, List.dropLast_concat, h.1]
  simp [points]

/-- A constant path is a left identity for concatenation. -/
theorem isConcat_const_left (p : Path Loc) : IsConcat (const p.source) p p := ⟨rfl, rfl⟩

/-- A constant path is a right identity for concatenation. -/
theorem isConcat_const_right (p : Path Loc) : IsConcat p (const p.goal) p := ⟨rfl, by simp [const]⟩

/-- Concatenation is associative. -/
theorem IsConcat.assoc {p q s t u : Path Loc} (hpq : IsConcat p q s) (hst : IsConcat s t u) :
    ∃ v, IsConcat q t v ∧ IsConcat p v u := by
  refine ⟨⟨q.source, q.steps ++ t.steps⟩, ⟨hpq.goal_eq.symm.trans hst.1, rfl⟩, hpq.1, ?_⟩
  rw [hst.2, hpq.2]; simp

/-- `p` is a subpath of `q` when concatenating some paths around `p` yields `q`. -/
def Subpath (p q : Path Loc) : Prop :=
  ∃ r r' m, IsConcat r p m ∧ IsConcat m r' q

theorem subpath_iff_infix {p q : Path Loc} :
    Subpath p q ↔ p.points <:+: q.points := by
  constructor
  · rintro ⟨r, r', m, hrp, hmq⟩
    refine ⟨r.points.dropLast, r'.steps, ?_⟩
    rw [hmq.points_eq, hrp.points_eq']
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

/-- The subpath order is a scoped instance, since a theory that sums paths by a total join instead
of partial concatenation orders the same type differently. Activate it with
`open scoped Spatial.Path`. -/
scoped instance instSubpathOrder : PartialOrder (Path Loc) where
  le := Subpath
  le_refl p := subpath_iff_infix.mpr (List.infix_refl _)
  le_trans _ _ _ hab hbc := subpath_iff_infix.mpr
    ((subpath_iff_infix.mp hab).trans (subpath_iff_infix.mp hbc))
  le_antisymm _ _ hab hba := points_injective
    (List.infix_antisymm (subpath_iff_infix.mp hab) (subpath_iff_infix.mp hba))

theorem const_le_iff {x : Loc} {p : Path Loc} : const x ≤ p ↔ x ∈ p.points :=
  subpath_iff_infix.trans (List.singleton_infix_iff _ _)

/-- A constant path has no proper subpaths. -/
theorem isMin_const (l : Loc) : IsMin (const l) := fun p hp ↦ by
  rcases (List.infix_singleton_iff p.points l).1 (subpath_iff_infix.mp hp) with h | h
  · exact absurd h p.points_ne_nil
  · exact (points_injective h).ge

/-- Concatenants are subpaths of their concatenation. -/
theorem IsConcat.le_left {p q r : Path Loc} (h : IsConcat p q r) : p ≤ r :=
  ⟨const p.source, q, p, isConcat_const_left p, h⟩

/-- Concatenants are subpaths of their concatenation. -/
theorem IsConcat.le_right {p q r : Path Loc} (h : IsConcat p q r) : q ≤ r :=
  ⟨p, const r.goal, r, h, isConcat_const_right r⟩

/-! ### Reversal -/

/-- The reverse of a path runs from its goal to its source. -/
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
  /-- Goal is a path *to* a place. -/
  | goal
  /-- Source is a path *from* a place. -/
  | source
  /-- Route is a path *via* or *past* a place. -/
  | route
  deriving DecidableEq, Repr, Fintype

namespace Direction

/-- The number of heads below a direction. -/
def rank : Direction → Fin 4
  | place => 0
  | goal => 1
  | source => 2
  | route => 3

/-- The containment order: a direction is below those whose structure contains it. -/
instance : LinearOrder Direction := LinearOrder.lift' rank (by decide)

/-- The direction of a reversed path swaps Goal and Source and keeps Place and Route. -/
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
  /-- The path is inside at one extreme point only, which bounds it, as *up to* does. -/
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

/-- The shape of a reversed path. -/
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

/-- A shape is bounded when it has a transition. Concatenating two paths of a bounded shape
[never yields another](##Spatial.Path.HasShape.not_concat), and concatenating two of any other
shape [always does](##Spatial.Path.HasShape.concat). -/
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
position, of which it has more than one, as a path *towards* `R` is. -/
def IsApproximative [Preorder β] (d : α → β) : Prop :=
  (∀ i, γ i ∉ R) ∧ StrictAnti (d ∘ γ) ∧ (⊥ : ι) ≠ ⊤

/-- A recessive path is outside `R` throughout and farther from it by `d` at each later position,
of which it has more than one, as a path *away from* `R` is. -/
def IsRecessive [Preorder β] (d : α → β) : Prop :=
  (∀ i, γ i ∉ R) ∧ StrictMono (d ∘ γ) ∧ (⊥ : ι) ≠ ⊤

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

theorem IsEgressive.isCoinitial (h : IsEgressive R γ) : IsCoinitial R γ := by
  obtain ⟨hS, hne⟩ := h
  refine ⟨?_, ?_, fun h ↦ ?_⟩
  · rw [hS, ← Iic_bot]; exact isLowerSet_Iic ⊥
  · show ⊥ ∈ γ ⁻¹' R; rw [hS]; rfl
  · have : (⊤ : ι) ∈ γ ⁻¹' R := h
    rw [hS] at this
    exact hne this.symm

/-- No path is both cofinal and coinitial. -/
theorem IsCofinal.not_isCoinitial (h : IsCofinal R γ) : ¬ IsCoinitial R γ :=
  fun h' ↦ h'.2.2 h.2.2

/-- A cofinal path's positions inside `R` are an interval that includes the last position and not
the first. -/
theorem isCofinal_iff_ordConnected :
    IsCofinal R γ ↔ (γ ⁻¹' R).OrdConnected ∧ γ ⊥ ∉ R ∧ γ ⊤ ∈ R :=
  ⟨fun h ↦ ⟨h.1.ordConnected, h.2⟩, fun ⟨h, h₀, h₁⟩ ↦
    ⟨fun _ _ hab ha ↦ h.out ha h₁ ⟨hab, le_top⟩, h₀, h₁⟩⟩

/-- A coinitial path's positions inside `R` are an interval that includes the first position and
not the last. -/
theorem isCoinitial_iff_ordConnected :
    IsCoinitial R γ ↔ (γ ⁻¹' R).OrdConnected ∧ γ ⊥ ∈ R ∧ γ ⊤ ∉ R :=
  ⟨fun h ↦ ⟨h.1.ordConnected, h.2⟩, fun ⟨h, h₀, h₁⟩ ↦
    ⟨fun _ _ hab hb ↦ h.out h₀ hb ⟨bot_le, hab⟩, h₀, h₁⟩⟩

theorem HasShape.ordConnected [Preorder β] {d : α → β} {s : Shape} (h : HasShape R γ d s) :
    (γ ⁻¹' R).OrdConnected := by
  cases s with
  | cofinal | coinitial => exact h.1.ordConnected
  | transitive => exact h.1
  | terminative | egressive => rw [h.1]; exact ordConnected_singleton
  | prolative => rw [show γ ⁻¹' R = univ from eq_univ_of_forall h]; exact ordConnected_univ
  | approximative | recessive =>
    rw [show γ ⁻¹' R = ∅ from eq_empty_of_forall_notMem h.1]; exact ordConnected_empty

/-- A path that meets `R` has a shape exactly when its positions inside `R` are one stretch. -/
theorem exists_hasShape_iff [Preorder β] {d : α → β} (hne : (γ ⁻¹' R).Nonempty) :
    (∃ s, HasShape R γ d s) ↔ (γ ⁻¹' R).OrdConnected := by
  refine ⟨fun ⟨_, h⟩ ↦ h.ordConnected, fun h ↦ ?_⟩
  by_cases h₀ : γ ⊥ ∈ R <;> by_cases h₁ : γ ⊤ ∈ R
  · exact ⟨.prolative, fun _ ↦ h.out h₀ h₁ ⟨bot_le, le_top⟩⟩
  · exact ⟨.coinitial, isCoinitial_iff_ordConnected.2 ⟨h, h₀, h₁⟩⟩
  · exact ⟨.cofinal, isCofinal_iff_ordConnected.2 ⟨h, h₀, h₁⟩⟩
  · exact ⟨.transitive, h, hne, h₀, h₁⟩

private theorem HasShape.ends [Preorder β] {d : α → β} {s : Shape} (h : HasShape R γ d s) :
    (γ ⊥ ∈ R ↔ s ∈ [Shape.coinitial, .egressive, .prolative]) ∧
      (γ ⊤ ∈ R ↔ s ∈ [Shape.cofinal, .terminative, .prolative]) := by
  cases s with
  | cofinal | coinitial => simp [h.2.1, h.2.2]
  | terminative => have h := IsTerminative.isCofinal h; simp [h.2.1, h.2.2]
  | egressive => have h := IsEgressive.isCoinitial h; simp [h.2.1, h.2.2]
  | transitive => simp [h.2.2.1, h.2.2.2]
  | prolative => simp [h ⊥, h ⊤]
  | approximative | recessive => simp [h.1 ⊥, h.1 ⊤]

/-- Two shapes of one path agree in direction and in being bounded, so they differ at most in
delimitation. -/
theorem HasShape.direction_eq [Preorder β] {d : α → β} {s t : Shape} (hs : HasShape R γ d s)
    (ht : HasShape R γ d t) : s.direction = t.direction ∧ (s.IsBounded ↔ t.IsBounded) := by
  have h₀ := hs.ends.1.symm.trans ht.ends.1
  have h₁ := hs.ends.2.symm.trans ht.ends.2
  have outside (hs : IsTransitive R γ) (ht : ∀ i, γ i ∉ R) : False :=
    hs.2.1.elim fun i hi ↦ ht i hi
  have opposite (ha : IsApproximative R γ d) (hr : IsRecessive R γ d) : False :=
    have hlt := lt_of_le_of_ne (bot_le (a := (⊤ : ι))) ha.2.2
    lt_asymm (ha.2.1 hlt) (hr.2.1 hlt)
  cases s <;> cases t <;> first
    | decide
    | (exfalso; revert h₀ h₁; decide)
    | exact (outside hs ht.1).elim
    | exact (outside ht hs.1).elim
    | exact (opposite hs ht).elim
    | exact (opposite ht hs).elim

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
  | approximative => exact ⟨fun k ↦ h.1 (e k), h.2.1.comp_strictMono e.strictMono, hne.2 h.2.2⟩
  | recessive => exact ⟨fun k ↦ h.1 (e k), h.2.1.comp e.strictMono, hne.2 h.2.2⟩

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
      Function.comp_apply, ofDual_toDual, ← Function.comp_assoc, strictAnti_comp_ofDual_iff, hne]
  | recessive =>
    simp only [HasShape, Shape.reverse, IsApproximative, IsRecessive, OrderDual.forall,
      Function.comp_apply, ofDual_toDual, ← Function.comp_assoc, strictMono_comp_ofDual_iff, hne]

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

/-! ### Positions of a concatenation -/

section Concat

variable {p} {q r : Path Loc} {R : Set Loc} {β : Type*} [Preorder β] {d : Loc → β} {s : Shape}

theorem IsConcat.length_steps (h : IsConcat p q r) :
    r.steps.length = p.steps.length + q.steps.length := by
  rw [h.2]; simp

/-- The positions of a concatenation up to the junction are those of its first path. -/
theorem IsConcat.apply_of_le (h : IsConcat p q r) (k : Fin (r.steps.length + 1))
    (hk : (k : ℕ) ≤ p.steps.length) : r k = p ⟨k, by omega⟩ := by
  simp only [toFun, List.get_eq_getElem, h.points_eq]
  exact List.getElem_append_left (by simp [points]; omega)

/-- The positions of a concatenation from the junction on are those of its second path. -/
theorem IsConcat.apply_of_ge (h : IsConcat p q r) (k : Fin (r.steps.length + 1))
    (hk : p.steps.length ≤ (k : ℕ)) :
    r k = q ⟨k - p.steps.length, by have := h.length_steps; omega⟩ := by
  simp only [toFun, List.get_eq_getElem, h.points_eq']
  rw [List.getElem_append_right (by simpa [points] using hk)]
  simp [points]

theorem IsConcat.forall_apply (h : IsConcat p q r) {P : Loc → Prop} :
    (∀ k, P (r k)) ↔ (∀ i, P (p i)) ∧ ∀ j, P (q j) := by
  have hl := h.length_steps
  refine ⟨fun hr ↦ ⟨fun i ↦ ?_, fun j ↦ ?_⟩, fun ⟨hp, hq⟩ k ↦ ?_⟩
  · simpa [h.apply_of_le ⟨i, by omega⟩ (by have := i.2; simp; omega)] using hr ⟨i, by omega⟩
  · simpa [h.apply_of_ge ⟨p.steps.length + j, by omega⟩ (by simp)] using
      hr ⟨p.steps.length + j, by omega⟩
  · rcases le_total (k : ℕ) p.steps.length with hk | hk
    · rw [h.apply_of_le k hk]; exact hp _
    · rw [h.apply_of_ge k hk]; exact hq _

theorem IsConcat.strictMono_comp (h : IsConcat p q r) (hp : StrictMono (d ∘ p))
    (hq : StrictMono (d ∘ q)) : StrictMono (d ∘ r) := by
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  simp only [Function.comp_apply]
  rcases lt_or_ge (i : ℕ) p.steps.length with hi | hi
  · rw [h.apply_of_le _ (by simpa using hi.le), h.apply_of_le _ (by simp; omega)]
    exact hp (by simp [Fin.lt_def])
  · rw [h.apply_of_ge _ (by simpa using hi), h.apply_of_ge _ (by simp; omega)]
    exact hq (by simp [Fin.lt_def]; omega)

theorem IsConcat.strictAnti_comp (h : IsConcat p q r) (hp : StrictAnti (d ∘ p))
    (hq : StrictAnti (d ∘ q)) : StrictAnti (d ∘ r) :=
  h.strictMono_comp (d := OrderDual.toDual ∘ d) hp hq

/-- A path's positions inside `R` are not one stretch if its concatenants both meet `R` and their
junction is outside it. -/
theorem IsConcat.not_ordConnected (h : IsConcat p q r) (hgoal : p.goal ∉ R) {i j}
    (hi : p i ∈ R) (hj : q j ∈ R) : ¬ (r ⁻¹' R).OrdConnected := fun hc ↦ by
  have hl := h.length_steps
  have hn : p.steps.length < r.steps.length + 1 := by omega
  have ha := h.apply_of_le ⟨i, by omega⟩ (by have := i.2; simp; omega)
  have hb := h.apply_of_le ⟨p.steps.length, hn⟩ le_rfl
  have hc' := h.apply_of_ge ⟨p.steps.length + j, by omega⟩ (by simp)
  have hmem := hc.out (x := ⟨i, by omega⟩) (y := ⟨p.steps.length + j, by omega⟩)
    (by simpa [ha] using hi) (by simpa [hc'] using hj)
    (a := ⟨p.steps.length, hn⟩) ⟨by have := i.2; simp [Fin.le_def]; omega, by simp [Fin.le_def]⟩
  have htop : p ⟨p.steps.length, by omega⟩ = p.goal := p.coe_top
  simp only [Set.mem_preimage, hb, htop] at hmem
  exact hgoal hmem

/-- Concatenation keeps a shape without a transition. -/
theorem HasShape.concat (hs : ¬ s.IsBounded) (hp : HasShape R p d s) (hq : HasShape R q d s)
    (h : IsConcat p q r) : HasShape R r d s := by
  have hne (hne : (⊥ : Fin (p.steps.length + 1)) ≠ ⊤) : (⊥ : Fin (r.steps.length + 1)) ≠ ⊤ := by
    have := h.length_steps
    simp only [ne_eq, Fin.ext_iff, bot_eq_zero, Fin.top_eq_last, Fin.val_zero, Fin.val_last]
      at hne ⊢
    omega
  cases s with
  | prolative => exact h.forall_apply.2 ⟨hp, hq⟩
  | approximative =>
    exact ⟨(h.forall_apply (P := (· ∉ R))).2 ⟨hp.1, hq.1⟩, h.strictAnti_comp hp.2.1 hq.2.1,
      hne hp.2.2⟩
  | recessive =>
    exact ⟨(h.forall_apply (P := (· ∉ R))).2 ⟨hp.1, hq.1⟩, h.strictMono_comp hp.2.1 hq.2.1,
      hne hp.2.2⟩
  | _ => exact absurd (by decide) hs

/-- Concatenation never keeps a shape with a transition: the ends of a cofinal or a coinitial path
lie on opposite sides of `R`, so no two of them concatenate, and two transitive paths concatenate
into more than one stretch inside `R`. -/
theorem HasShape.not_concat (hs : s.IsBounded) (hp : HasShape R p d s) (hq : HasShape R q d s)
    (h : IsConcat p q r) : ¬ HasShape R r d s := by
  have cofinal (hp : IsCofinal R p) (hq : IsCofinal R q) : False :=
    hq.2.1 (by rw [coe_bot, ← h.1, ← coe_top]; exact hp.2.2)
  have coinitial (hp : IsCoinitial R p) (hq : IsCoinitial R q) : False :=
    hp.2.2 (by rw [coe_top, h.1, ← coe_bot]; exact hq.2.1)
  cases s with
  | cofinal => exact (cofinal hp hq).elim
  | terminative => exact (cofinal (IsTerminative.isCofinal hp) (IsTerminative.isCofinal hq)).elim
  | coinitial => exact (coinitial hp hq).elim
  | egressive => exact (coinitial (IsEgressive.isCoinitial hp) (IsEgressive.isCoinitial hq)).elim
  | transitive =>
    obtain ⟨_, ⟨i, hi⟩, -, hg⟩ := id hp
    obtain ⟨_, ⟨j, hj⟩, -, -⟩ := id hq
    exact fun hr ↦ h.not_ordConnected (by rwa [coe_top] at hg) hi hj hr.1
  | _ => exact absurd hs (by decide)

end Concat

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

/-- The spatial trace of an event domain `E`, which sends each event to the path its theme
traverses. -/
class SpatialTrace (E : Type*) (Loc : outParam Type*) where
  /-- The path traversed in an event. -/
  σ : E → Spatial.Path Loc

namespace Event

export SpatialTrace (σ)

end Event
