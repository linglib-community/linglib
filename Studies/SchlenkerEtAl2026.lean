module

public import Linglib.Data.Examples.SchlenkerEtAl2026
public import Linglib.Semantics.Reference.Monster
public import Studies.Kaplan1989
public import Mathlib.Algebra.Torsor.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Set.Defs

/-!
# Schlenker, Lamberton & Lamberton (2026): Traveling Shots in Language

In Iconological Semantics a classifier predicate has an iconic component: its argument must
project, from a viewpoint, to the position the classifier has in signing space, and a classifier
that moves is matched moment by moment against the positions its argument projects to over a
stretch of time. Schlenker, Lamberton and Lamberton study ASL classifiers for objects that do not
move, a tree or a pole, moving past the signer to show the object passing a moving character, the
traveling shot of film.

A viewpoint is here a correspondence between positions in the world and positions in signing
space at each time and world, and it is static when the correspondence is the same throughout.
From a static viewpoint an object that stays where it is projects to a classifier that does not
move, so the readings need viewpoints that move, and from a moving viewpoint the movement of the
classifier is information about the movement of the viewpoint. Because a viewpoint is a
correspondence, a classifier held still for an object that moves carries the same information, as
when the viewpoint follows a vehicle.

The paper leaves two analyses open. On the first, any viewpoint variable may denote a moving
viewpoint. On the second, only the variable bound by the context may: it denotes the viewpoint of
the context's agent, and Role Shift, which evaluates its clause at the context of a character at
the time and world of evaluation, makes a classifier carrying that variable project from the
character's viewpoint, while a classifier with a free variable is unaffected. Role Shift is a shift
of the context, a monster wherever it replaces the agent, and the context-bound variable is an
indexical. If free variables denote static viewpoints only, a traveling shot needs Role Shift.

## Implementation notes

* The paper's static viewpoint is a Cartesian frame of reference with a spatial scaling factor,
  and an object projects to a classifier when its coordinates in that frame are the scaled
  coordinates of the classifier in the signer's frame. Here it is any bijection between positions
  in the world and positions in signing space, and a position stands for a center with an
  orientation. Nothing below uses the geometry beyond injectivity.
* A dynamic classifier is a function from the reals to positions in signing space, read on the
  interval of its duration. Durations are real numbers and times are a torsor over them.
* Meanings are characters whose index is a time and a world, and the assignment is fixed, so a
  free viewpoint variable is a constant character. Role Shift abstracts over an individual, a time
  and a world; the time and the world are the index of the shifted character. It replaces the
  agent, time and world of the context and keeps its addressee and position, which the paper's
  contexts do not have.

## TODO

* The inferences about the character's path, from the side on which the classifier passes the
  signer, need the geometry of frames of reference. So do the degraded examples in which a verb
  displays a path the classifier's side conflicts with. The elicited paradigms of
  `Data/Examples/SchlenkerEtAl2026` record the side and the mean judgments; no theorem here reads
  them.
* How dynamic viewpoints enter the demonstrational analysis of Role Shift, which has no viewpoints,
  is left open by the paper.

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

/-- A viewpoint gives, at each time and world, a correspondence between positions in the world
and positions in signing space, together with a temporal scaling factor. -/
structure Viewpoint (X S T W : Type*) where
  /-- The correspondence between positions at a time and a world. -/
  frame : T × W → X ≃ S
  /-- The factor from the time of the classifier's movement to the time of what it depicts. -/
  timeScale : ℝ

variable {pos : E → T × W → X} {π : Viewpoint X S T W} {d : E} {t : T} {w : W} {δ δ₁ δ₂ : ℝ}
  {cl : ℝ → S}

/-- (29): the position in signing space to which the object `d` projects from the viewpoint `π`
at a time and a world, where `pos d` gives the position of `d` in the world. -/
def proj (pos : E → T × W → X) (π : Viewpoint X S T W) (d : E) (i : T × W) : S :=
  π.frame i (pos d i)

/-- (27), (32): an object projects to a dynamic classifier `cl` of duration `δ` when at each
moment `δ'` of the classifier's movement the object projects to the classifier's position, at the
time `δ'` scaled by the viewpoint's factor after the time of evaluation. -/
def DynProj (pos : E → T × W → X) (π : Viewpoint X S T W) (d : E) (i : T × W) (δ : ℝ)
    (cl : ℝ → S) : Prop :=
  ∀ δ' ∈ Icc 0 δ, proj pos π d ((π.timeScale * δ') +ᵥ i.1, i.2) = cl δ'

/-- An object is still in a world when its position there does not change over time. -/
def IsStill (pos : E → T × W → X) (d : E) (w : W) : Prop :=
  ∀ t t' : T, pos d (t, w) = pos d (t', w)

/-- (32): if a still object projects to a classifier that moves, the viewpoint differs between the
times the two positions of the classifier depict. -/
theorem DynProj.frame_ne (h : DynProj pos π d (t, w) δ cl) (hd : IsStill pos d w)
    (h₁ : δ₁ ∈ Icc 0 δ) (h₂ : δ₂ ∈ Icc 0 δ) (hne : cl δ₁ ≠ cl δ₂) :
    π.frame ((π.timeScale * δ₁) +ᵥ t, w) ≠ π.frame ((π.timeScale * δ₂) +ᵥ t, w) :=
  fun heq ↦ hne <| by rw [← h δ₁ h₁, ← h δ₂ h₂, proj, proj, heq, hd]

/-- From a static viewpoint a still object projects to a classifier that does not move. -/
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

/-- (33b): the context-bound viewpoint variable `π*` denotes the viewpoint of the agent of the
context, where `vp x` is the viewpoint of the individual `x`. A free viewpoint variable (33a)
denotes its value under the assignment at every context, a constant character. -/
def piStar (vp : E → Viewpoint X S T W) :
    Character (Context W E P T) (T × W) (Viewpoint X S T W) :=
  dthat fun c ↦ vp c.agent

/-- (25a), (31): a dynamic classifier with lexical component `lex` and viewpoint term `π` holds of
an object that satisfies `lex` and projects to the classifier from the viewpoint `π` denotes. -/
def classifier (pos : E → T × W → X) (lex : T × W → E → Prop)
    (π : Character (Context W E P T) (T × W) (Viewpoint X S T W)) (δ : ℝ) (cl : ℝ → S) :
    Character (Context W E P T) (T × W) (E → Prop) :=
  fun c i x ↦ lex i x ∧ DynProj pos (π c i) x i δ cl

/-! ### Role Shift -/

/-- (34): Role Shift evaluates its clause at the context of the individual `x` at the time and
world of evaluation. -/
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
/-- Role Shift is a monster where it replaces the agent of the context. -/
theorem isMonster_roleShift [Nontrivial α] (h : c.agent ≠ x) :
    IsMonster (roleShift x : Character (Context W E P T) (T × W) α → _) :=
  isMonster_shiftBy_of_ne (v := (c.time, c.world)) (c := c)
    fun e ↦ h (congrArg Context.agent e).symm

/-- (36b): under Role Shift a classifier with the context-bound viewpoint variable projects from
the viewpoint of the character. -/
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

/-- The paper's illustration of (32): the tree classifier of (30) moves from the front of signing
space to the signer's forehead in one second, so if the tree does not move and the temporal
scaling factor is 100, Ann's viewpoint a hundred seconds after the time of evaluation differs from
her viewpoint then. -/
example {tree ann : E} {front back : S} (hne : front ≠ back) (h₀ : cl 0 = front)
    (h₁ : cl 1 = back) (hτ : (vp ann).timeScale = 100) (hd : IsStill pos tree w)
    (h : roleShift ann (classifier pos lex (piStar vp) 1 cl) c (t, w) tree) :
    (vp ann).frame (t, w) ≠ (vp ann).frame ((100 : ℝ) +ᵥ t, w) := by
  have := roleShift_frame_ne h hd (δ₁ := 0) (δ₂ := 1) (by simp) (by simp) (h₀ ▸ h₁ ▸ hne)
  simpa [hτ] using this

/-- A traveling shot has a model: on the real line a still object projects, under Role Shift, to a
classifier that moves, from the viewpoint of a character whose frame is translated as time
passes. -/
example : roleShift () (classifier (fun _ _ ↦ (0 : ℝ)) (fun _ _ ↦ True)
    (piStar fun _ ↦ ⟨fun i ↦ Equiv.addRight i.1, 1⟩) 1 id)
    (⟨(), (), (), (0 : ℝ), ()⟩ : Context Unit Unit Unit ℝ) (0, ()) () :=
  ⟨trivial, fun δ' _ ↦ by simp [proj, piStar]⟩

end SchlenkerEtAl2026
