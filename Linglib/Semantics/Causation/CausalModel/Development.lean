module

public import Linglib.Semantics.Causation.CausalModel.Basic

/-!
# Developing an observation through a causal model

An observation `s : ∀ v, Flat (α v)` settles some variables and leaves the context unknown. Two
local procedures propagate what it settles through the equations, each deciding a variable from
what has been decided about its parents alone.

* In the strict development of Schulz and of Nadathur, a variable is settled once all its parents
  are, and its equation then gives the same value in every context (`CausalModel.CausallyEntails`).
* In the Kleene development used by Baglini and Bar-Asher Siegal, a variable is forced to a value
  when every completion of what is known about its parents gives that value in every context,
  so a turned handle on an unlocked door forces the door open while other inputs are unknown
  (`CausalModel.Forced`).

Both are fixed points of maps that compute each variable from its parents
(`WellFounded.fixedPoint`). The strict development settles less than the Kleene one
(`CausalModel.Forced.of_causallyEntails`), and the Kleene one is sound: what it forces holds in
every context when the observation is imposed as an intervention
(`CausalModel.Forced.solve_eq_of_intervene`), and in every context where the observation holds
(`CausalModel.Forced.solve_bot_eq`).

## Main definitions

* `CausalModel.Forced`: the Kleene development of an observation
* `CausalModel.CausallyEntails`: the strict development of an observation

## Main results

* `CausalModel.forced_iff`, `CausalModel.causallyEntails_iff`: the defining equations
* `CausalModel.Forced.of_causallyEntails`: the strict development settles less
* `CausalModel.Forced.solve_eq_of_intervene`, `CausalModel.Forced.solve_bot_eq`: soundness for
  the observation imposed as an intervention and for the observation holding
* `CausalModel.causallyEntails_congr`: the strict development of a variable reads the
  observation only at its ancestors
* `CausalModel.CausallyEntails.parent_eq`: a settled variable settles each parent to the value
  its equation needs
* `CausalModel.causallyEntails_solve_bot`: when only the roots read the context, an observation
  whose development settles every root develops to the actual world of its contexts
* `CausalModel.causallyEntails_iff_develop`: the strict development computed one value per
  variable (`CausalModel.develop`), so that `decide` evaluates it in a finite model

## Implementation notes

Uncertainty about exogenous variables is uncertainty about the context, so a variable whose
equation reads the context is settled only when the equation gives the same value in every
context. A model whose root variables read the context therefore leaves them unsettled unless the
observation settles them, as the strict development of Schulz leaves undetermined background
variables. Both developments are families of predicates `∀ v, α v → Prop`, which spares choosing
the value a variable is settled to.

Soundness has no converse. With `b := ¬ a` and `v := a ∧ b`, `v` is false in every context, but
neither development settles it while `a` is unknown, since each looks only at what is settled
about `v`'s parents.

## References

* [schulz-2011]
* [nadathur-2023-implicatives]
* [baglini-bar-asher-siegal-2025]
* [bar-asher-siegal-2026]
-/

@[expose] public section

namespace CausalModel

variable {U V : Type*} {α : V → Type*} (M : CausalModel U V α)

/-- `M.forcedStep s P` is one round of Kleene development from the observation `s`, given what
`P` has settled. A variable is settled to `x` when `s` settles it so, or when `s` leaves it open
and its equation gives `x` in every context and on every assignment agreeing with what `P`
settles about its parents. -/
def forcedStep (s : ∀ v, Flat (α v)) (P : ∀ v, α v → Prop) : ∀ v, α v → Prop := fun v x ↦
  s v = ↑x ∨ s v = ⊥ ∧
    ∀ u y, (∀ w, M.graph.Adj w v → ∀ z, P w z → y w = z) → M.eqn v u y = x

/-- `M.entailsStep s P` is one round of strict development from the observation `s`. It is
`forcedStep`, except that a variable `s` leaves open is settled only once all its parents are. -/
def entailsStep (s : ∀ v, Flat (α v)) (P : ∀ v, α v → Prop) : ∀ v, α v → Prop := fun v x ↦
  s v = ↑x ∨ s v = ⊥ ∧ (∀ w, M.graph.Adj w v → ∃ z, P w z) ∧
    ∀ u y, (∀ w, M.graph.Adj w v → ∀ z, P w z → y w = z) → M.eqn v u y = x

variable {M}

theorem dependsOn_forcedStep (s : ∀ v, Flat (α v)) (v : V) :
    DependsOn (M.forcedStep s · v) {w | M.graph.Adj w v} := fun P Q h ↦ by
  funext x
  refine propext (or_congr_right (and_congr_right fun _ ↦ forall₂_congr fun u y ↦
    imp_congr_left (forall₂_congr fun w hw ↦ ?_)))
  rw [h w hw]

theorem dependsOn_entailsStep (s : ∀ v, Flat (α v)) (v : V) :
    DependsOn (M.entailsStep s · v) {w | M.graph.Adj w v} := fun P Q h ↦ by
  funext x
  refine propext (or_congr_right (and_congr_right fun _ ↦ and_congr
    (forall₂_congr fun w hw ↦ by rw [h w hw]) (forall₂_congr fun u y ↦
      imp_congr_left (forall₂_congr fun w hw ↦ ?_))))
  rw [h w hw]

theorem entailsStep_le_forcedStep (s : ∀ v, Flat (α v)) {P Q : ∀ v, α v → Prop} (h : P ≤ Q) :
    M.entailsStep s P ≤ M.forcedStep s Q := by
  rintro v x (hx | ⟨hs, -, hx⟩)
  · exact .inl hx
  · exact .inr ⟨hs, fun u y hy ↦ hx u y fun w hw z hz ↦ hy w hw z (h w z hz)⟩

variable (M) [hM : M.IsAcyclic]

/-- `M.Forced s v x` says that the Kleene development of the observation `s` forces `v` to `x`. -/
def Forced (s : ∀ v, Flat (α v)) (v : V) (x : α v) : Prop :=
  hM.fixedPoint (M.forcedStep s) v x

/-- `M.CausallyEntails s v x` says that the strict development of `s` settles `v` to `x`. -/
def CausallyEntails (s : ∀ v, Flat (α v)) (v : V) (x : α v) : Prop :=
  hM.fixedPoint (M.entailsStep s) v x

variable {M} {s : ∀ v, Flat (α v)} {v : V} {x : α v}

theorem forced_iff : M.Forced s v x ↔ s v = ↑x ∨ s v = ⊥ ∧
    ∀ u y, (∀ w, M.graph.Adj w v → ∀ z, M.Forced s w z → y w = z) → M.eqn v u y = x :=
  Iff.of_eq (congrFun (WellFounded.fixedPoint_apply (dependsOn_forcedStep s) v) x)

theorem causallyEntails_iff : M.CausallyEntails s v x ↔ s v = ↑x ∨ s v = ⊥ ∧
    (∀ w, M.graph.Adj w v → ∃ z, M.CausallyEntails s w z) ∧
    ∀ u y, (∀ w, M.graph.Adj w v → ∀ z, M.CausallyEntails s w z → y w = z) →
      M.eqn v u y = x :=
  Iff.of_eq (congrFun (WellFounded.fixedPoint_apply (dependsOn_entailsStep s) v) x)

theorem causallyEntails_root_iff {t : ∀ v, Flat (α v)} {v : V} {x : α v}
    (hroot : ∀ w, ¬ M.graph.Adj w v) (hv : t v = ⊥) :
    M.CausallyEntails t v x ↔ ∀ u y, M.eqn v u y = x := by
  rw [causallyEntails_iff, hv]
  refine ⟨?_, fun h ↦ .inr ⟨rfl, fun w hw ↦ absurd hw (hroot w), fun u y _ ↦ h u y⟩⟩
  rintro (h | ⟨-, -, h⟩)
  · exact absurd h Flat.bot_ne_coe
  · exact fun u y ↦ h u y fun w hw ↦ absurd hw (hroot w)

/-- The strict development settles less than the Kleene one. -/
theorem Forced.of_causallyEntails (h : M.CausallyEntails s v x) : M.Forced s v x :=
  WellFounded.fixedPoint_le_fixedPoint (dependsOn_entailsStep s) (dependsOn_forcedStep s)
    (fun _ _ ↦ entailsStep_le_forcedStep s) v x h

theorem CausallyEntails.parent_settled (h : M.CausallyEntails s v x) (hv : s v = ⊥) {w : V}
    (hw : M.graph.Adj w v) : ∃ z, M.CausallyEntails s w z := by
  rcases causallyEntails_iff.1 h with h | ⟨-, hpar, -⟩
  · rw [hv] at h; exact absurd h Flat.bot_ne_coe
  · exact hpar w hw

/-- Observations that agree on a variable and all its ancestors settle it alike. -/
theorem causallyEntails_congr {t : ∀ v, Flat (α v)}
    (h : ∀ w, Relation.ReflTransGen M.graph.Adj w v → s w = t w) :
    M.CausallyEntails s v x ↔ M.CausallyEntails t v x := by
  induction v using hM.induction with
  | _ v ih =>
    have hpar : ∀ w, M.graph.Adj w v → ∀ z, M.CausallyEntails s w z ↔ M.CausallyEntails t w z :=
      fun w hw _ ↦ ih w hw fun w' hw' ↦ h w' (hw'.tail hw)
    rw [causallyEntails_iff, causallyEntails_iff, h v .refl]
    exact or_congr_right (and_congr_right fun _ ↦ and_congr
      (forall₂_congr fun w hw ↦ exists_congr (hpar w hw))
      (forall₂_congr fun _ _ ↦ imp_congr_left (forall₂_congr fun w hw ↦
        forall_congr' fun z ↦ imp_congr_left (hpar w hw z))))

theorem causallyEntails_update_of_not_reflTransGen [DecidableEq V] {c : V}
    (h : ¬ Relation.ReflTransGen M.graph.Adj c v) (y : Flat (α c)) :
    M.CausallyEntails (Function.update s c y) v x ↔ M.CausallyEntails s v x :=
  causallyEntails_congr fun w hw ↦ Function.update_of_ne (fun hwc : w = c ↦ h (hwc ▸ hw)) y s

theorem forced_iff_iterate_card [Fintype V] :
    M.Forced s v x ↔ (M.forcedStep s)^[Fintype.card V] ⊥ v x :=
  Iff.of_eq (congrFun (congrFun (WellFounded.fixedPoint_eq_iterate_card
    (dependsOn_forcedStep s) ⊥) v) x)

theorem causallyEntails_iff_iterate_card [Fintype V] :
    M.CausallyEntails s v x ↔ (M.entailsStep s)^[Fintype.card V] ⊥ v x :=
  Iff.of_eq (congrFun (congrFun (WellFounded.fixedPoint_eq_iterate_card
    (dependsOn_entailsStep s) ⊥) v) x)

variable [∀ v, Nonempty (α v)]

/-- The Kleene development is sound. What it forces from `s` holds in every context when `s` is
imposed as an intervention. -/
theorem Forced.solve_eq_of_intervene (h : M.Forced s v x) (u : U) : M.solve s u v = x := by
  induction v using hM.induction with
  | _ v ih =>
    rcases forced_iff.1 h with hs | ⟨hs, h⟩
    · exact solve_of_eq_coe hs u
    · rw [solve_of_eq_bot hs u]
      exact h u _ fun w hw _ hz ↦ ih w hw hz

/-- The strict development is sound for the interventional reading. -/
theorem CausallyEntails.solve_eq_of_intervene (h : M.CausallyEntails s v x) (u : U) :
    M.solve s u v = x :=
  (Forced.of_causallyEntails h).solve_eq_of_intervene u

/-- The Kleene development is sound for the observational reading. What it forces from `s` holds
in every context where `s` holds. -/
theorem Forced.solve_bot_eq (h : M.Forced s v x) {u : U} (hu : u ∈ M.contexts s) :
    M.solve ⊥ u v = x := by
  rw [← solve_eq_solve_bot_of_mem_contexts hu]; exact h.solve_eq_of_intervene u

/-- The strict development is sound for the observational reading. -/
theorem CausallyEntails.solve_bot_eq (h : M.CausallyEntails s v x) {u : U}
    (hu : u ∈ M.contexts s) : M.solve ⊥ u v = x :=
  (Forced.of_causallyEntails h).solve_bot_eq hu

/-- When the context reaches the model only at its roots, an observation whose development settles
every root develops, in a context where it holds, to that context's actual world. -/
theorem causallyEntails_solve_bot [M.ContextAtRoots] {u : U}
    (hs : ∀ v, (∀ w, ¬ M.graph.Adj w v) → ∃ z, M.CausallyEntails s v z)
    (hu : u ∈ M.contexts s) : ∀ v, M.CausallyEntails s v (M.solve ⊥ u v) := by
  intro v
  induction v using hM.induction with
  | _ v ih =>
    by_cases hpar : ∃ w, M.graph.Adj w v
    · rcases eq_or_ne (s v) ⊥ with hsv | hsv
      · refine causallyEntails_iff.2 (.inr ⟨hsv, fun w hw ↦ ⟨_, ih w hw⟩, fun u' y hy ↦ ?_⟩)
        obtain ⟨w, hw⟩ := hpar
        rw [M.dependsOn_eqn v u' fun w (hw : M.graph.Adj w v) ↦ hy w hw _ (ih w hw),
          ContextAtRoots.eqn_eq_of_adj hw u' u]
        exact (solve_of_eq_bot rfl u).symm
      · obtain ⟨a, ha⟩ := Flat.ne_bot_iff_exists.1 hsv
        exact (causallyEntails_iff.2 (.inl ha)).solve_bot_eq hu ▸ causallyEntails_iff.2 (.inl ha)
    · obtain ⟨z, hz⟩ := hs v (not_exists.1 hpar)
      exact hz.solve_bot_eq hu ▸ hz

theorem CausallyEntails.unique [Nonempty U] {y : α v} (hx : M.CausallyEntails s v x)
    (hy : M.CausallyEntails s v y) : x = y := by
  classical
  induction v using hM.induction with
  | _ v ih =>
    rcases causallyEntails_iff.1 hx with hx | ⟨hv, hpar, hx⟩
    · rcases causallyEntails_iff.1 hy with hy | ⟨hv, -, -⟩
      · exact Flat.coe_injective (hx.symm.trans hy)
      · rw [hv] at hx; exact absurd hx Flat.bot_ne_coe
    · rcases causallyEntails_iff.1 hy with hy | ⟨-, -, hy⟩
      · rw [hv] at hy; exact absurd hy Flat.bot_ne_coe
      · choose y₀ hy₀ using hpar
        let z : ∀ w, α w := fun w ↦ if h : M.graph.Adj w v then y₀ w h else Classical.arbitrary _
        have hz : ∀ w, M.graph.Adj w v → ∀ z', M.CausallyEntails s w z' → z w = z' :=
          fun w hw z' hz' ↦ by simp only [z, hw, ↓reduceDIte]; exact ih w hw (hy₀ w hw) hz'
        exact (hx (Classical.arbitrary U) z hz).symm.trans (hy _ z hz)

theorem CausallyEntails.eqn_eq [Nonempty U] (h : M.CausallyEntails s v x) (hv : s v = ⊥)
    {y : ∀ w, α w} (hy : ∀ w, M.graph.Adj w v → M.CausallyEntails s w (y w)) (u : U) :
    M.eqn v u y = x := by
  rcases causallyEntails_iff.1 h with h | ⟨-, -, h⟩
  · rw [hv] at h; exact absurd h Flat.bot_ne_coe
  · exact h u y fun w hw _ hz ↦ (hy w hw).unique hz

/-- A variable the strict development settles, unobserved, settles each parent to the value its
equation needs for the result. -/
theorem CausallyEntails.parent_eq [Nonempty U] (h : M.CausallyEntails s v x) (hv : s v = ⊥)
    {w : V} (hw : M.graph.Adj w v) {z : α w}
    (hz : ∀ u (y : ∀ w, α w), M.eqn v u y = x → y w = z) : M.CausallyEntails s w z := by
  classical
  choose y₀ hy₀ using fun w (hw : M.graph.Adj w v) ↦ h.parent_settled hv hw
  let y : ∀ w, α w := fun w ↦ if h : M.graph.Adj w v then y₀ w h else Classical.arbitrary _
  have hy : ∀ w (hw : M.graph.Adj w v), M.CausallyEntails s w (y w) := fun w hw ↦ by
    simp only [y, hw, ↓reduceDIte]; exact hy₀ w hw
  rw [← hz (Classical.arbitrary U) y (h.eqn_eq hv hy _)]
  exact hy w hw

section Develop

/-! ### Computing the strict development

A variable the strict development settles has settled parents, so its value is its equation at
their values, the same in every context. `develop` computes the development this way, one value
per variable, and in a finite model `decide` evaluates it by iteration. -/

variable (M) [Fintype U] [Inhabited U] [∀ v, Inhabited (α v)] [∀ v, DecidableEq (α v)]
  [Fintype V] [DecidableRel M.graph.Adj]

/-- `M.developStep s p` is one round of the strict development as values. A variable `s` settles
keeps its value; one `s` leaves open is settled once `p` settles all its parents and its equation,
at their values, gives the same value in every context. -/
def developStep (s p : ∀ v, Flat (α v)) : ∀ v, Flat (α v) := fun v ↦
  if s v = ⊥ then
    if ∀ w, M.graph.Adj w v → p w ≠ ⊥ then
      if ∀ u, M.eqn v u (fun w ↦ (p w).unbotD default) =
          M.eqn v default (fun w ↦ (p w).unbotD default) then
        ↑(M.eqn v default fun w ↦ (p w).unbotD default)
      else ⊥
    else ⊥
  else s v

variable {M}

omit hM [∀ v, Nonempty (α v)] in
theorem dependsOn_developStep (s : ∀ v, Flat (α v)) (v : V) :
    DependsOn (M.developStep s · v) {w | M.graph.Adj w v} := fun p q h ↦ by
  have heqn : ∀ u, M.eqn v u (fun w ↦ (p w).unbotD default) =
      M.eqn v u (fun w ↦ (q w).unbotD default) := fun u ↦
    M.dependsOn_eqn v u fun w hw ↦ by simp only [h w hw]
  have hpar : (∀ w, M.graph.Adj w v → p w ≠ ⊥) ↔ ∀ w, M.graph.Adj w v → q w ≠ ⊥ :=
    forall₂_congr fun w hw ↦ by rw [h w hw]
  simp only [developStep, heqn, hpar]

variable (M) in
/-- The strict development of the observation `s`, as values. -/
noncomputable def develop (s : ∀ v, Flat (α v)) : ∀ v, Flat (α v) :=
  hM.fixedPoint (M.developStep s)

omit [∀ v, Nonempty (α v)] in
theorem develop_apply (s : ∀ v, Flat (α v)) (v : V) :
    M.develop s v = M.developStep s (M.develop s) v :=
  WellFounded.fixedPoint_apply (dependsOn_developStep s) v

omit [∀ v, Nonempty (α v)] in
/-- The strict development settles `v` to `x` exactly when its computation does. -/
theorem causallyEntails_iff_develop {s : ∀ v, Flat (α v)} {v : V} {x : α v} :
    M.CausallyEntails s v x ↔ M.develop s v = ↑x := by
  induction v using hM.induction with
  | _ v ih =>
    have hpar : (∀ w, M.graph.Adj w v → ∃ z, M.CausallyEntails s w z) ↔
        ∀ w, M.graph.Adj w v → M.develop s w ≠ ⊥ :=
      forall₂_congr fun w hw ↦ by
        simp only [ih w hw, Flat.ne_bot_iff_exists]
    have hcons : ∀ y : ∀ w, α w,
        (∀ w, M.graph.Adj w v → ∀ z, M.CausallyEntails s w z → y w = z) ↔
          ∀ w, M.graph.Adj w v → ∀ z : α w, M.develop s w = ↑z → y w = z :=
      fun y ↦ forall₂_congr fun w hw ↦ forall_congr' fun z ↦ by rw [ih w hw]
    rw [causallyEntails_iff, develop_apply, developStep]
    simp only [hcons]
    cases hs : s v with
    | coe a => simp [Flat.coe_inj]
    | bot =>
      simp only [Flat.bot_ne_coe, false_or, true_and, ↓reduceIte]
      set y₀ : ∀ w, α w := fun w ↦ (M.develop s w).unbotD default
      have hy₀ : ∀ w, M.graph.Adj w v → ∀ z : α w, M.develop s w = ↑z → y₀ w = z :=
        fun w _ z hz ↦ by simp [y₀, hz]
      rw [hpar]
      by_cases hp : ∀ w, M.graph.Adj w v → M.develop s w ≠ ⊥
      · have hagree : ∀ u (y : ∀ w, α w),
            (∀ w, M.graph.Adj w v → ∀ z : α w, M.develop s w = ↑z → y w = z) →
              M.eqn v u y = M.eqn v u y₀ := fun u y hy ↦
          M.dependsOn_eqn v u fun w (hw : M.graph.Adj w v) ↦ by
            obtain ⟨z, hz⟩ := Flat.ne_bot_iff_exists.1 (hp w hw)
            rw [hy w hw z hz, hy₀ w hw z hz]
        rw [ite_eq_left_of_eq_true (h := eq_true hp), and_iff_right hp]
        constructor
        · intro h
          have hx : ∀ u, M.eqn v u y₀ = x := fun u ↦ h u y₀ hy₀
          have hc : ∀ u, M.eqn v u y₀ = M.eqn v default y₀ := fun u ↦ (hx u).trans (hx default).symm
          rw [ite_eq_left_of_eq_true (h := eq_true hc), hx default]
        · intro h u y hy
          split_ifs at h with hc
          · rw [hagree u y hy, hc u]
            exact Flat.coe_inj.1 h
          · exact absurd h Flat.bot_ne_coe
      · simp [hp]

section Decidable

variable {s : ∀ v, Flat (α v)} {v : V} {x : α v}

omit [∀ v, Nonempty (α v)] in
theorem causallyEntails_iff_iterate :
    M.CausallyEntails s v x ↔ (M.developStep s)^[Fintype.card V] ⊥ v = ↑x := by
  rw [causallyEntails_iff_develop, develop,
    WellFounded.fixedPoint_eq_iterate_card (dependsOn_developStep s) ⊥]

/-- In a finite model, causal entailment is decided by computing the strict development. -/
instance : Decidable (M.CausallyEntails s v x) :=
  decidable_of_iff _ causallyEntails_iff_iterate.symm

end Decidable

end Develop

section DevelopKleene

/-! ### Computing the Kleene development

A variable the Kleene development forces takes the value its equation gives at any completion of
what is known about its parents, in any context. `developKleene` computes it by testing the value
at one completion against every completion and context, one value per variable. -/

variable (M) [Fintype U] [Inhabited U] [∀ v, Inhabited (α v)] [∀ v, DecidableEq (α v)]
  [∀ v, Fintype (α v)] [Fintype V] [DecidableEq V] [DecidableRel M.graph.Adj]

/-- `M.developKleeneStep s p` is one round of the Kleene development as values. A variable `s`
settles keeps its value; one `s` leaves open is settled when its equation gives the same value in
every context on every assignment extending what `p` settles about its parents. -/
def developKleeneStep (s p : ∀ v, Flat (α v)) : ∀ v, Flat (α v) := fun v ↦
  if s v = ⊥ then
    if ∀ u (y : ∀ w, α w), (∀ w, M.graph.Adj w v → p w ≤ ↑(y w)) →
        M.eqn v u y = M.eqn v default fun w ↦ (p w).unbotD default then
      ↑(M.eqn v default fun w ↦ (p w).unbotD default)
    else ⊥
  else s v

variable {M}

omit hM [∀ v, Nonempty (α v)] in
theorem dependsOn_developKleeneStep (s : ∀ v, Flat (α v)) (v : V) :
    DependsOn (M.developKleeneStep s · v) {w | M.graph.Adj w v} := fun p q h ↦ by
  have heqn : ∀ u, M.eqn v u (fun w ↦ (p w).unbotD default) =
      M.eqn v u (fun w ↦ (q w).unbotD default) := fun u ↦
    M.dependsOn_eqn v u fun w hw ↦ by simp only [h w hw]
  have hcond : ∀ y : ∀ w, α w, (∀ w, M.graph.Adj w v → p w ≤ ↑(y w)) ↔
      ∀ w, M.graph.Adj w v → q w ≤ ↑(y w) :=
    fun _ ↦ forall₂_congr fun w hw ↦ by rw [h w hw]
  simp only [developKleeneStep, heqn, hcond]

variable (M) in
/-- The Kleene development of the observation `s`, as values. -/
noncomputable def developKleene (s : ∀ v, Flat (α v)) : ∀ v, Flat (α v) :=
  hM.fixedPoint (M.developKleeneStep s)

omit [∀ v, Nonempty (α v)] in
theorem developKleene_apply (s : ∀ v, Flat (α v)) (v : V) :
    M.developKleene s v = M.developKleeneStep s (M.developKleene s) v :=
  WellFounded.fixedPoint_apply (dependsOn_developKleeneStep s) v

omit [∀ v, Nonempty (α v)] in
theorem forced_iff_developKleene {s : ∀ v, Flat (α v)} {v : V} {x : α v} :
    M.Forced s v x ↔ M.developKleene s v = ↑x := by
  induction v using hM.induction with
  | _ v ih =>
    have hcons : ∀ y : ∀ w, α w, (∀ w, M.graph.Adj w v → ∀ z, M.Forced s w z → y w = z) ↔
        ∀ w, M.graph.Adj w v → M.developKleene s w ≤ ↑(y w) := fun y ↦
      forall₂_congr fun w hw ↦ by
        simp only [ih w hw]
        cases M.developKleene s w with
        | bot => simp
        | coe a => simp [Flat.coe_le_coe, eq_comm]
    rw [forced_iff, developKleene_apply, developKleeneStep]
    simp only [hcons]
    set y₀ : ∀ w, α w := fun w ↦ (M.developKleene s w).unbotD default
    have hy₀ : ∀ w, M.graph.Adj w v → M.developKleene s w ≤ ↑(y₀ w) := fun w _ ↦ by
      simp only [y₀]; cases M.developKleene s w with
      | bot => exact bot_le
      | coe a => exact le_rfl
    cases hs : s v with
    | coe a => simp [Flat.coe_inj]
    | bot =>
      simp only [Flat.bot_ne_coe, false_or, true_and, ↓reduceIte]
      constructor
      · intro h
        have hx : ∀ u, M.eqn v u y₀ = x := fun u ↦ h u y₀ hy₀
        rw [ite_eq_left_of_eq_true (h := eq_true fun u y hy ↦ (h u y hy).trans (hx default).symm),
          hx default]
      · intro h u y hy
        split_ifs at h with hc
        · exact (hc u y hy).trans (Flat.coe_inj.1 h)
        · exact absurd h Flat.bot_ne_coe

omit [∀ v, Nonempty (α v)] in
theorem forced_iff_iterate {s : ∀ v, Flat (α v)} {v : V} {x : α v} :
    M.Forced s v x ↔ (M.developKleeneStep s)^[Fintype.card V] ⊥ v = ↑x := by
  rw [forced_iff_developKleene, developKleene,
    WellFounded.fixedPoint_eq_iterate_card (dependsOn_developKleeneStep s) ⊥]

/-- In a finite model, being forced is decided by computing the Kleene development. -/
instance (s : ∀ v, Flat (α v)) (v : V) (x : α v) : Decidable (M.Forced s v x) :=
  decidable_of_iff _ forced_iff_iterate.symm

end DevelopKleene

end CausalModel
