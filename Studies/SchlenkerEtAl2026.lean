module

public import Linglib.Data.Examples.SchlenkerEtAl2026
public import Linglib.Semantics.Reference.Monster
public import Studies.Kaplan1989
public import Mathlib.Algebra.Torsor.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Set.Defs

/-!
# Schlenker, Lamberton & Lamberton (2026): Traveling Shots in Language

This file formalizes the analysis of traveling shots in ASL by Schlenker, Lamberton and Lamberton.
A classifier predicate is a sign whose position and movement in signing space are interpreted
iconically: it holds of an object that projects, from a viewpoint, to the position of the
classifier. A classifier that moves is compared moment by moment with the positions to which the
object projects over a stretch of time. A traveling shot is a classifier for an object that does
not move, such as a tree, which moves past the signer to show the object passing a character who
moves.

A viewpoint is here a bijection between positions in the world and positions in signing space, one
for each time and world. A viewpoint is static if the bijection is the same at every time and
world. The object `d` projects from a viewpoint, at a time and a world, to the image of the
position of `d` under the bijection there. An object is still in a world if its position there is
the same at every time.

For example, Ann jogs toward a tree and the signer moves the tree classifier toward his forehead.
The tree is still, so it projects to two different positions of the classifier from two different
bijections: the viewpoint is Ann's, and it moves with her.

The file proves that from a static viewpoint a still object projects only to a classifier that
does not move, so a traveling shot needs a viewpoint that moves. It also proves that if a still
object projects to a classifier that moves, the viewpoint differs between the times that two
different positions of the classifier depict. A classifier that is held still for an object that
moves shows a moving viewpoint in the same way, since each viewpoint is a bijection.

The paper leaves two analyses open. On the first, any viewpoint variable may denote a viewpoint
that moves. On the second, only the context-bound variable may. This variable denotes the
viewpoint of the agent of the context. Role Shift evaluates its clause at the context of a
character, at the time and world of evaluation. Under Role Shift, a classifier with the
context-bound variable projects from the viewpoint of the character, and a classifier with a free
variable is unchanged. Role Shift is a shift of the context, and it is a monster when it replaces
the agent. If free variables denote static viewpoints only, a traveling shot needs Role Shift.

## Implementation notes

* The static viewpoint of the paper is a Cartesian frame of reference with a spatial scaling
  factor. An object projects to a classifier if its coordinates in that frame are the scaled
  coordinates of the classifier in the frame of the signer. Here a static viewpoint is any
  bijection between positions in the world and positions in signing space, and a position stands
  for a center together with an orientation. The proofs use no geometry beyond injectivity.
* A classifier that moves is a function from the real numbers to positions in signing space, which
  is read on the interval of its duration. Durations are real numbers, and times form a torsor
  over the real numbers.
* A meaning is a character whose index is a pair of a time and a world. The assignment is fixed,
  so a free viewpoint variable is a constant character. Role Shift abstracts over an individual, a
  time and a world. The time and the world are the index of the shifted character. Role Shift
  replaces the agent, the time and the world of the context and keeps its addressee and position,
  which the contexts of the paper do not have.

## TODO

* The inferences about the path of the character, from the side on which the classifier passes
  the signer, need the geometry of frames of reference. So do the degraded examples in which a
  verb displays a path that conflicts with the side of the classifier. The elicited paradigms in
  `Data/Examples/SchlenkerEtAl2026` record the side and the mean judgments. No theorem in this
  file reads them.
* The paper leaves open how viewpoints that move enter the demonstrational analysis of Role Shift,
  which has no viewpoints.

## References

* [schlenker-lamberton-lamberton-2026]
* [schlenker-lamberton-2024]
* [davidson-2015]
-/

@[expose] public section

namespace SchlenkerEtAl2026

open SpeechAct Character Set

variable {W E P T X S α : Type*} [AddTorsor ℝ T]

/-! ### Projection from a viewpoint -/

/-- A **viewpoint** consists of a bijection between positions in the world and positions in
signing space for each time and world, and a temporal scaling factor. -/
structure Viewpoint (X S T W : Type*) where
  /-- The **frame** of a viewpoint at a time and a world is its bijection between positions in the
  world and positions in signing space there. -/
  frame : T × W → X ≃ S
  /-- The **temporal scaling factor** of a viewpoint is the length of time that one unit of the
  movement of a classifier depicts. -/
  timeScale : ℝ

variable {pos : E → T × W → X} {π : Viewpoint X S T W} {d : E} {t : T} {w : W} {δ δ₁ δ₂ : ℝ}
  {cl : ℝ → S}

/-- (29): The **projection** of an object `d` from a viewpoint `π`, at a time and a world, is the
image of the position of `d` there under the frame of `π` there. The function `pos d` gives the
position of `d` at each time and world. -/
def proj (pos : E → T × W → X) (π : Viewpoint X S T W) (d : E) (i : T × W) : S :=
  π.frame i (pos d i)

/-- (27), (32): An object `d` **projects to a dynamic classifier** `cl` of duration `δ` from a
viewpoint `π`, at a time `t` and a world, if for every moment `δ'` between `0` and `δ` the
projection of `d` at the time `δ'` times the temporal scaling factor after `t` is the position
`cl δ'` of the classifier. -/
def DynProj (pos : E → T × W → X) (π : Viewpoint X S T W) (d : E) (i : T × W) (δ : ℝ)
    (cl : ℝ → S) : Prop :=
  ∀ δ' ∈ Icc 0 δ, proj pos π d ((π.timeScale * δ') +ᵥ i.1, i.2) = cl δ'

/-- An object is **still** in a world if its position in that world is the same at every time. -/
def IsStill (pos : E → T × W → X) (d : E) (w : W) : Prop :=
  ∀ t t' : T, pos d (t, w) = pos d (t', w)

/-- (32): If a still object projects to a dynamic classifier that has different positions at two
moments, the frames of the viewpoint differ at the times that the two moments depict. -/
theorem DynProj.frame_ne (h : DynProj pos π d (t, w) δ cl) (hd : IsStill pos d w)
    (h₁ : δ₁ ∈ Icc 0 δ) (h₂ : δ₂ ∈ Icc 0 δ) (hne : cl δ₁ ≠ cl δ₂) :
    π.frame ((π.timeScale * δ₁) +ᵥ t, w) ≠ π.frame ((π.timeScale * δ₂) +ᵥ t, w) :=
  fun heq ↦ hne <| by rw [← h δ₁ h₁, ← h δ₂ h₂, proj, proj, heq, hd]

/-- If a still object projects to a dynamic classifier from a static viewpoint, the classifier has
the same position at every moment. -/
theorem DynProj.eq_of_isConst (h : DynProj pos π d (t, w) δ cl) (hd : IsStill pos d w)
    (hπ : Function.IsConst π.frame) (h₁ : δ₁ ∈ Icc 0 δ) (h₂ : δ₂ ∈ Icc 0 δ) : cl δ₁ = cl δ₂ :=
  not_not.1 fun hne ↦ h.frame_ne hd h₁ h₂ hne (hπ _ _)

-- §7, on two classifiers: a classifier held still for an object that moves
theorem DynProj.frame_ne_of_pos_ne (h : DynProj pos π d (t, w) δ cl) (h₁ : δ₁ ∈ Icc 0 δ)
    (h₂ : δ₂ ∈ Icc 0 δ) (hcl : cl δ₁ = cl δ₂)
    (hne : pos d ((π.timeScale * δ₁) +ᵥ t, w) ≠ pos d ((π.timeScale * δ₂) +ᵥ t, w)) :
    π.frame ((π.timeScale * δ₁) +ᵥ t, w) ≠ π.frame ((π.timeScale * δ₂) +ᵥ t, w) :=
  fun heq ↦ hne <| (π.frame _).injective <| by
    have := (h δ₁ h₁).trans (hcl.trans (h δ₂ h₂).symm)
    rwa [proj, proj, heq] at this

/-! ### Viewpoint variables and classifiers -/

/-- (33b): The **context-bound viewpoint variable** `π*` denotes, at a context `c`, the viewpoint
`vp c.agent` of the agent of `c`. A free viewpoint variable (33a) denotes its value under the
assignment at every context, so it is a constant character. -/
def piStar (vp : E → Viewpoint X S T W) :
    Character (Context W E P T) (T × W) (Viewpoint X S T W) :=
  dthat fun c ↦ vp c.agent

/-- (25a), (31): A **classifier predicate** with lexical component `lex` and viewpoint term `π`
holds of an object `x` if `x` satisfies `lex` and `x` projects to the dynamic classifier `cl` from
the viewpoint that `π` denotes. -/
def classifier (pos : E → T × W → X) (lex : T × W → E → Prop)
    (π : Character (Context W E P T) (T × W) (Viewpoint X S T W)) (δ : ℝ) (cl : ℝ → S) :
    Character (Context W E P T) (T × W) (E → Prop) :=
  fun c i x ↦ lex i x ∧ DynProj pos (π c i) x i δ cl

/-! ### Role Shift -/

/-- (34): **Role Shift** to an individual `x` is the shift that replaces the agent of the context
by `x` and its time and world by the time and world of evaluation. -/
def roleShift (x : E) :
    Character (Context W E P T) (T × W) α → Character (Context W E P T) (T × W) α :=
  shiftBy fun i c ↦ { c with agent := x, time := i.1, world := i.2 }

variable {x : E} {c : Context W E P T} {i : T × W} {lex : T × W → E → Prop}
  {vp : E → Viewpoint X S T W}

omit [AddTorsor ℝ T] in
-- (35): under Role Shift the first person denotes the character
theorem roleShift_I (Q : T × W → E → Prop) :
    roleShift x (fun c i ↦ Q i (Kaplan1989.I c i)) c i = Q i x := rfl

omit [AddTorsor ℝ T] in
/-- Role Shift to `x` is a monster if some context has an agent other than `x`. -/
theorem isMonster_roleShift [Nontrivial α] (h : c.agent ≠ x) :
    IsMonster (roleShift x : Character (Context W E P T) (T × W) α → _) :=
  isMonster_shiftBy_of_ne (v := (c.time, c.world)) (c := c)
    fun e ↦ h (congrArg Context.agent e).symm

/-- (36b): Under Role Shift to `x`, a classifier predicate with the context-bound viewpoint
variable holds of an object if the object satisfies the lexical component and projects to the
classifier from the viewpoint of `x`. -/
theorem roleShift_classifier_piStar :
    roleShift x (classifier pos lex (piStar vp) δ cl) c i d ↔
      lex i d ∧ DynProj pos (vp x) d i δ cl := .rfl

-- a classifier with a free viewpoint variable is unaffected by Role Shift
theorem roleShift_classifier_const :
    roleShift x (classifier pos lex (.const π) δ cl) c i d ↔ lex i d ∧ DynProj pos π d i δ cl :=
  .rfl

-- §8.1, the restrictive theory: with a static free variable a still object's classifier is still
theorem classifier_const_eq_of_isConst (hπ : Function.IsConst π.frame)
    (h : classifier pos lex (.const π) δ cl c (t, w) d) (hd : IsStill pos d w)
    (h₁ : δ₁ ∈ Icc 0 δ) (h₂ : δ₂ ∈ Icc 0 δ) : cl δ₁ = cl δ₂ :=
  h.2.eq_of_isConst hd hπ h₁ h₂

-- (37d): under Role Shift the movement of a still object's classifier is the character's
theorem roleShift_frame_ne (h : roleShift x (classifier pos lex (piStar vp) δ cl) c (t, w) d)
    (hd : IsStill pos d w) (h₁ : δ₁ ∈ Icc 0 δ) (h₂ : δ₂ ∈ Icc 0 δ) (hne : cl δ₁ ≠ cl δ₂) :
    (vp x).frame (((vp x).timeScale * δ₁) +ᵥ t, w) ≠
      (vp x).frame (((vp x).timeScale * δ₂) +ᵥ t, w) :=
  (roleShift_classifier_piStar.1 h).2.frame_ne hd h₁ h₂ hne

/-- The illustration of (32) in the paper: the tree classifier of (30) moves from the front of
signing space to the forehead of the signer in one second. If the tree is still and the temporal
scaling factor is 100, the frame of Ann's viewpoint a hundred seconds after the time of evaluation
differs from its frame at that time. -/
example {tree ann : E} {front back : S} (hne : front ≠ back) (h₀ : cl 0 = front)
    (h₁ : cl 1 = back) (hτ : (vp ann).timeScale = 100) (hd : IsStill pos tree w)
    (h : roleShift ann (classifier pos lex (piStar vp) 1 cl) c (t, w) tree) :
    (vp ann).frame (t, w) ≠ (vp ann).frame ((100 : ℝ) +ᵥ t, w) := by
  have := roleShift_frame_ne h hd (δ₁ := 0) (δ₂ := 1) (by simp) (by simp) (h₀ ▸ h₁ ▸ hne)
  simpa [hτ] using this

/-- A traveling shot has a model. On the real line, let the frame of the viewpoint of a character
at a time `t` be translation by `t`. Under Role Shift to that character, a still object projects
to a classifier that moves. -/
example : roleShift () (classifier (fun _ _ ↦ (0 : ℝ)) (fun _ _ ↦ True)
    (piStar fun _ ↦ ⟨fun i ↦ Equiv.addRight i.1, 1⟩) 1 id)
    (⟨(), (), (), (0 : ℝ), ()⟩ : Context Unit Unit Unit ℝ) (0, ()) () :=
  ⟨trivial, fun δ' _ ↦ by simp [proj, piStar]⟩

end SchlenkerEtAl2026
