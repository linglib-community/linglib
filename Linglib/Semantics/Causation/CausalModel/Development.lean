module

public import Linglib.Semantics.Causation.CausalModel.Basic

/-!
# Developing an observation through a causal model

An observation `s : ∀ v, Part (α v)` settles some variables and leaves the context unknown. Two
local procedures propagate what it settles through the equations, each deciding a variable from
what has been decided about its parents alone.

* In the strict development of Schulz and of Nadathur, a variable is settled once all its parents
  are, and its equation then gives the same value in every context (`CausalModel.CausallyEntails`).
* In the Kleene development used by Baglini and Bar-Asher Siegal, a variable is forced to a value
  when every completion of what is known about its parents gives that value in every context
  (`CausalModel.ForcedBy`), so a turned handle on an unlocked door forces the door open while
  other inputs are unknown (`CausalModel.Forced`).

Both are fixed points of maps that compute each variable from its parents
(`WellFounded.fixedPoint`). The strict development settles less than the Kleene one
(`CausalModel.Forced.of_causallyEntails`), and the Kleene one is sound: what it forces holds in
every context where the observation holds (`CausalModel.Forced.solve_eq`), and, from the situation
an intervention settles, in every context under that intervention
(`CausalModel.Forced.solve_intervene_eq`).

## Main definitions

* `CausalModel.ForcedBy`: the value of an equation in Kleene's strong three-valued reading
* `CausalModel.Forced`: the Kleene development of an observation
* `CausalModel.CausallyEntails`: the strict development of an observation

## Main results

* `CausalModel.forced_iff`, `CausalModel.causallyEntails_iff`: the defining equations
* `CausalModel.Forced.of_causallyEntails`: the strict development settles less
* `CausalModel.Forced.solve_eq`, `CausalModel.Forced.solve_intervene_eq`: soundness for the
  observation holding and for an intervention, from the situation it settles
* `CausalModel.causallyEntails_congr`: the strict development of a variable reads the
  observation only at its ancestors
* `CausalModel.CausallyEntails.parent_eq`: a settled variable settles each parent to the value
  its equation needs
* `CausalModel.causallyEntails_solve`: when only the roots read the context, an observation
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

/-- `M.ForcedBy P v x` says that what `P` settles about the parents of `v` forces `v` to `x`: the
equation of `v` gives `x` in every context and on every assignment agreeing with it. This is the
three-valued value of the equation that every completion agrees on, which for an equation reading
each parent once is its value in Kleene's strong logic. -/
def ForcedBy (P : ∀ v, α v → Prop) (v : V) (x : α v) : Prop :=
  ∀ u y, (∀ w, M.graph.Adj w v → ∀ z, P w z → y w = z) → M.eqn v u y = x

/-- `M.forcedStep s P` is one round of Kleene development from the observation `s`, given what
`P` has settled. A variable is settled to `x` when `s` settles it so, or when `s` leaves it open
and `P` forces it to `x`. -/
def forcedStep (s : ∀ v, Part (α v)) (P : ∀ v, α v → Prop) : ∀ v, α v → Prop := fun v x ↦
  s v = Part.some x ∨ s v = ⊥ ∧ M.ForcedBy P v x

/-- `M.entailsStep s P` is one round of strict development from the observation `s`. It is
`forcedStep`, except that a variable `s` leaves open is settled only once all its parents are. -/
def entailsStep (s : ∀ v, Part (α v)) (P : ∀ v, α v → Prop) : ∀ v, α v → Prop := fun v x ↦
  s v = Part.some x ∨ s v = ⊥ ∧ (∀ w, M.graph.Adj w v → ∃ z, P w z) ∧ M.ForcedBy P v x

variable {M}

/-- Settling more about the parents forces no less. -/
theorem ForcedBy.mono {P Q : ∀ v, α v → Prop} {v : V} {x : α v}
    (hPQ : ∀ w, M.graph.Adj w v → ∀ z, P w z → Q w z) (h : M.ForcedBy P v x) :
    M.ForcedBy Q v x :=
  fun u y hy ↦ h u y fun w hw z hz ↦ hy w hw z (hPQ w hw z hz)

theorem forcedBy_congr {P Q : ∀ v, α v → Prop} {v : V} {x : α v}
    (h : ∀ w, M.graph.Adj w v → P w = Q w) : M.ForcedBy P v x ↔ M.ForcedBy Q v x :=
  ⟨.mono fun w hw _ ↦ (h w hw ▸ ·), .mono fun w hw _ ↦ ((h w hw).symm ▸ ·)⟩

section Parents

variable [DecidableRel M.graph.Adj] [∀ v, Inhabited (α v)]

/-- Being forced reads only the parents: it is enough to complete what is settled about them,
the other variables taking their default values. -/
theorem forcedBy_iff_parents {P : ∀ v, α v → Prop} {v : V} {x : α v} :
    M.ForcedBy P v x ↔ ∀ u (p : ∀ w : {w // M.graph.Adj w v}, α w),
      (∀ (w : {w // M.graph.Adj w v}) z, P w z → p w = z) →
        M.eqn v u (fun w ↦ if h : M.graph.Adj w v then p ⟨w, h⟩ else default) = x := by
  refine ⟨fun h u p hp ↦ h u _ fun w hw z hz ↦ ?_, fun h u y hy ↦ ?_⟩
  · simpa [hw] using hp ⟨w, hw⟩ z hz
  · have heq : M.eqn v u y = M.eqn v u fun w ↦ if h : M.graph.Adj w v then y w else default :=
      M.dependsOn_eqn v u fun w (hw : M.graph.Adj w v) ↦ by simp [hw]
    exact heq.trans (h u (fun w ↦ y w) fun w z hz ↦ hy w w.2 z hz)

/-- In a finite model, being forced is decided over the assignments to the parents alone. -/
instance [Fintype U] [Fintype V] [DecidableEq V] [∀ v, Fintype (α v)] [∀ v, DecidableEq (α v)]
    (P : ∀ v, α v → Prop) [∀ w z, Decidable (P w z)] (v : V) (x : α v) :
    Decidable (M.ForcedBy P v x) :=
  decidable_of_iff _ forcedBy_iff_parents.symm

end Parents

theorem dependsOn_forcedStep (s : ∀ v, Part (α v)) (v : V) :
    DependsOn (M.forcedStep s · v) {w | M.graph.Adj w v} := fun _ _ h ↦
  funext fun _ ↦ propext <| or_congr_right <| and_congr_right fun _ ↦ forcedBy_congr h

theorem dependsOn_entailsStep (s : ∀ v, Part (α v)) (v : V) :
    DependsOn (M.entailsStep s · v) {w | M.graph.Adj w v} := fun _ _ h ↦
  funext fun _ ↦ propext <| or_congr_right <| and_congr_right fun _ ↦
    and_congr (forall₂_congr fun w hw ↦ by rw [h w hw]) (forcedBy_congr h)

theorem entailsStep_le_forcedStep (s : ∀ v, Part (α v)) {P Q : ∀ v, α v → Prop} (h : P ≤ Q) :
    M.entailsStep s P ≤ M.forcedStep s Q := by
  rintro v x (hx | ⟨hs, -, hx⟩)
  · exact .inl hx
  · exact .inr ⟨hs, hx.mono fun w _ z ↦ h w z⟩

variable (M) [hM : M.IsAcyclic]

/-- `M.Forced s v x` says that the Kleene development of the observation `s` forces `v` to `x`. -/
def Forced (s : ∀ v, Part (α v)) (v : V) (x : α v) : Prop :=
  hM.fixedPoint (M.forcedStep s) v x

/-- `M.CausallyEntails s v x` says that the strict development of `s` settles `v` to `x`. -/
def CausallyEntails (s : ∀ v, Part (α v)) (v : V) (x : α v) : Prop :=
  hM.fixedPoint (M.entailsStep s) v x

variable {M} {s : ∀ v, Part (α v)} {v : V} {x : α v}

theorem forced_iff : M.Forced s v x ↔ s v = Part.some x ∨ s v = ⊥ ∧ M.ForcedBy (M.Forced s) v x :=
  Iff.of_eq (congrFun (WellFounded.fixedPoint_apply (dependsOn_forcedStep s) v) x)

theorem causallyEntails_iff : M.CausallyEntails s v x ↔ s v = Part.some x ∨ s v = ⊥ ∧
    (∀ w, M.graph.Adj w v → ∃ z, M.CausallyEntails s w z) ∧
      M.ForcedBy (M.CausallyEntails s) v x :=
  Iff.of_eq (congrFun (WellFounded.fixedPoint_apply (dependsOn_entailsStep s) v) x)

theorem causallyEntails_root_iff {t : ∀ v, Part (α v)} {v : V} {x : α v}
    (hroot : ∀ w, ¬ M.graph.Adj w v) (hv : t v = ⊥) :
    M.CausallyEntails t v x ↔ ∀ u y, M.eqn v u y = x := by
  rw [causallyEntails_iff, hv]
  refine ⟨?_, fun h ↦ .inr ⟨rfl, fun w hw ↦ absurd hw (hroot w), fun u y _ ↦ h u y⟩⟩
  rintro (h | ⟨-, -, h⟩)
  · exact absurd h Part.bot_ne_some
  · exact fun u y ↦ h u y fun w hw ↦ absurd hw (hroot w)

/-- The strict development settles less than the Kleene one. -/
theorem Forced.of_causallyEntails (h : M.CausallyEntails s v x) : M.Forced s v x :=
  WellFounded.fixedPoint_le_fixedPoint (dependsOn_entailsStep s) (dependsOn_forcedStep s)
    (fun _ _ ↦ entailsStep_le_forcedStep s) v x h

theorem CausallyEntails.parent_settled (h : M.CausallyEntails s v x) (hv : s v = ⊥) {w : V}
    (hw : M.graph.Adj w v) : ∃ z, M.CausallyEntails s w z := by
  rcases causallyEntails_iff.1 h with h | ⟨-, hpar, -⟩
  · rw [hv] at h; exact absurd h Part.bot_ne_some
  · exact hpar w hw

/-- Observations that agree on a variable and all its ancestors settle it alike. -/
theorem causallyEntails_congr {t : ∀ v, Part (α v)}
    (h : ∀ w, Relation.ReflTransGen M.graph.Adj w v → s w = t w) :
    M.CausallyEntails s v x ↔ M.CausallyEntails t v x :=
  Iff.of_eq <| congrFun (WellFounded.fixedPoint_congr (dependsOn_entailsStep s)
    (dependsOn_entailsStep t) fun w hw _ ↦ by unfold entailsStep; rw [h w hw]) x

theorem causallyEntails_update_of_not_reflTransGen [DecidableEq V] {c : V}
    (h : ¬ Relation.ReflTransGen M.graph.Adj c v) (y : Part (α c)) :
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

/-- The Kleene development is sound for the observational reading. What it forces from `s` holds
in every context where `s` holds. -/
theorem Forced.solve_eq (h : M.Forced s v x) {u : U} (hu : u ∈ M.contexts s) :
    M.solve u v = x := by
  induction v using hM.induction with
  | _ v ih =>
    rcases forced_iff.1 h with hs | ⟨-, h⟩
    · exact (Part.some_le_some.1 (hs ▸ hu v)).symm
    · rw [solve_apply]
      exact h u _ fun w hw _ hz ↦ ih w hw hz

/-- The strict development is sound for the observational reading. -/
theorem CausallyEntails.solve_eq (h : M.CausallyEntails s v x) {u : U}
    (hu : u ∈ M.contexts s) : M.solve u v = x :=
  (Forced.of_causallyEntails h).solve_eq hu

section Intervention

variable [DecidableEq V] {X : Finset V} {ξ : ∀ v : X, α v}

/-- The Kleene development is sound for the interventional reading. What it forces from the
situation an intervention settles holds in every context under that intervention. -/
theorem Forced.solve_intervene_eq
    (h : M.Forced (Function.updateFinset ⊥ X fun w ↦ Part.some (ξ w)) v x) (u : U) :
    (M.intervene X ξ).solve u v = x := by
  induction v using hM.induction with
  | _ v ih =>
    rcases forced_iff.1 h with hs | ⟨hs, h⟩
    · by_cases hv : v ∈ X
      · simp only [Function.updateFinset, hv, dite_true, Part.some_inj] at hs
        exact (solve_intervene_of_mem hv).trans hs
      · simp [Function.updateFinset, hv] at hs
    · have hv : v ∉ X := fun hv ↦ by simp [Function.updateFinset, hv] at hs
      rw [solve_intervene_of_notMem hv]
      exact h u _ fun w hw _ hz ↦ ih w hw hz

/-- The strict development is sound for the interventional reading. -/
theorem CausallyEntails.solve_intervene_eq
    (h : M.CausallyEntails (Function.updateFinset ⊥ X fun w ↦ Part.some (ξ w)) v x) (u : U) :
    (M.intervene X ξ).solve u v = x :=
  (Forced.of_causallyEntails h).solve_intervene_eq u

/-- For one variable the situation of the intervention is `[c ← a]`. -/
theorem CausallyEntails.solve_intervene_singleton_eq {c : V} {a : α c}
    (h : M.CausallyEntails [c ← a] v x) (u : U) : M[c ← a].solve u v = x := by
  have : ([c ← a] : ∀ v, Part (α v)) =
      Function.updateFinset ⊥ {c}
        fun w ↦ Part.some ((uniqueElim a : ∀ w : ({c} : Finset V), α w) w) := by
    rw [show ([c ← a] : ∀ v, Part (α v)) = Function.update ⊥ c (Part.some a) from rfl,
      Function.update_eq_updateFinset]
    congr 1
    funext ⟨w, hw⟩
    obtain rfl := Finset.mem_singleton.1 hw
    rfl
  exact CausallyEntails.solve_intervene_eq (this ▸ h) u

end Intervention

/-- When the context reaches the model only at its roots, an observation whose development settles
every root develops, in a context where it holds, to that context's actual world. -/
theorem causallyEntails_solve [M.ContextAtRoots] {u : U}
    (hs : ∀ v, (∀ w, ¬ M.graph.Adj w v) → ∃ z, M.CausallyEntails s v z)
    (hu : u ∈ M.contexts s) : ∀ v, M.CausallyEntails s v (M.solve u v) := by
  intro v
  induction v using hM.induction with
  | _ v ih =>
    by_cases hpar : ∃ w, M.graph.Adj w v
    · rcases eq_or_ne (s v) ⊥ with hsv | hsv
      · refine causallyEntails_iff.2 (.inr ⟨hsv, fun w hw ↦ ⟨_, ih w hw⟩, fun u' y hy ↦ ?_⟩)
        obtain ⟨w, hw⟩ := hpar
        rw [M.dependsOn_eqn v u' fun w (hw : M.graph.Adj w v) ↦ hy w hw _ (ih w hw),
          ContextAtRoots.eqn_eq_of_adj hw u' u]
        exact (solve_apply u _).symm
      · obtain ⟨a, ha⟩ := Part.ne_bot_iff_exists.1 hsv
        exact (causallyEntails_iff.2 (.inl ha)).solve_eq hu ▸ causallyEntails_iff.2 (.inl ha)
    · obtain ⟨z, hz⟩ := hs v (not_exists.1 hpar)
      exact hz.solve_eq hu ▸ hz

theorem CausallyEntails.unique [Nonempty U] {y : α v} (hx : M.CausallyEntails s v x)
    (hy : M.CausallyEntails s v y) : x = y := by
  classical
  induction v using hM.induction with
  | _ v ih =>
    rcases causallyEntails_iff.1 hx with hx | ⟨hv, hpar, hx⟩
    · rcases causallyEntails_iff.1 hy with hy | ⟨hv, -, -⟩
      · exact Part.some_injective (hx.symm.trans hy)
      · rw [hv] at hx; exact absurd hx Part.bot_ne_some
    · rcases causallyEntails_iff.1 hy with hy | ⟨-, -, hy⟩
      · rw [hv] at hy; exact absurd hy Part.bot_ne_some
      · choose y₀ hy₀ using hpar
        let z : ∀ w, α w := fun w ↦ if h : M.graph.Adj w v then y₀ w h else Classical.arbitrary _
        have hz : ∀ w, M.graph.Adj w v → ∀ z', M.CausallyEntails s w z' → z w = z' :=
          fun w hw z' hz' ↦ by simp only [z, hw, ↓reduceDIte]; exact ih w hw (hy₀ w hw) hz'
        exact (hx (Classical.arbitrary U) z hz).symm.trans (hy _ z hz)

theorem CausallyEntails.eqn_eq [Nonempty U] (h : M.CausallyEntails s v x) (hv : s v = ⊥)
    {y : ∀ w, α w} (hy : ∀ w, M.graph.Adj w v → M.CausallyEntails s w (y w)) (u : U) :
    M.eqn v u y = x := by
  rcases causallyEntails_iff.1 h with h | ⟨-, -, h⟩
  · rw [hv] at h; exact absurd h Part.bot_ne_some
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
their values, the same in every context. `develop` computes the development of an observation given
as options, one value per variable, and in a finite model `decide` evaluates it by iteration; a
situation whose domains are decidable is computed through its options (`Part.toOption`). -/

variable (M) [Fintype U] [Inhabited U] [∀ v, Inhabited (α v)] [∀ v, DecidableEq (α v)]
  [Fintype V] [DecidableRel M.graph.Adj]

/-- `M.developStep s p` is one round of the strict development as options. A variable `s` settles
keeps its value; one `s` leaves open is settled once `p` settles all its parents and its equation,
at their values, gives the same value in every context. -/
def developStep (s p : ∀ v, Option (α v)) : ∀ v, Option (α v) := fun v ↦
  if s v = none then
    if ∀ w, M.graph.Adj w v → p w ≠ none then
      if ∀ u, M.eqn v u (fun w ↦ (p w).getD default) =
          M.eqn v default (fun w ↦ (p w).getD default) then
        some (M.eqn v default fun w ↦ (p w).getD default)
      else none
    else none
  else s v

variable {M}

omit hM [∀ v, Nonempty (α v)] in
theorem dependsOn_developStep (s : ∀ v, Option (α v)) (v : V) :
    DependsOn (M.developStep s · v) {w | M.graph.Adj w v} := fun p q h ↦ by
  have heqn : ∀ u, M.eqn v u (fun w ↦ (p w).getD default) =
      M.eqn v u (fun w ↦ (q w).getD default) := fun u ↦
    M.dependsOn_eqn v u fun w hw ↦ by simp only [h w hw]
  have hpar : (∀ w, M.graph.Adj w v → p w ≠ none) ↔ ∀ w, M.graph.Adj w v → q w ≠ none :=
    forall₂_congr fun w hw ↦ by rw [h w hw]
  simp only [developStep, heqn, hpar]

variable (M) in
/-- The strict development of the observation `s`, given as options. -/
noncomputable def develop (s : ∀ v, Option (α v)) : ∀ v, Option (α v) :=
  hM.fixedPoint (M.developStep s)

theorem develop_apply (s : ∀ v, Option (α v)) (v : V) :
    M.develop s v = M.developStep s (M.develop s) v :=
  WellFounded.fixedPoint_apply (dependsOn_developStep s) v

/-- The strict development settles `v` to `x` exactly when its computation does. -/
theorem causallyEntails_iff_develop {s : ∀ v, Option (α v)} {v : V} {x : α v} :
    M.CausallyEntails (fun v ↦ ↑(s v)) v x ↔ M.develop s v = some x := by
  induction v using hM.induction with
  | _ v ih =>
    have hpar : (∀ w, M.graph.Adj w v → ∃ z, M.CausallyEntails (fun v ↦ ↑(s v)) w z) ↔
        ∀ w, M.graph.Adj w v → M.develop s w ≠ none :=
      forall₂_congr fun w hw ↦ by
        simp only [ih w hw, Option.ne_none_iff_exists']
    have hcons : ∀ y : ∀ w, α w,
        (∀ w, M.graph.Adj w v → ∀ z, M.CausallyEntails (fun v ↦ ↑(s v)) w z → y w = z) ↔
          ∀ w, M.graph.Adj w v → ∀ z : α w, M.develop s w = some z → y w = z :=
      fun y ↦ forall₂_congr fun w hw ↦ forall_congr' fun z ↦ by rw [ih w hw]
    rw [causallyEntails_iff, develop_apply, developStep]
    simp only [ForcedBy, hcons]
    cases hs : s v with
    | some a => simp [Part.some_inj]
    | none =>
      simp only [Part.coe_none, ← Part.bot_eq_none, Part.bot_ne_some, false_or, true_and,
        ↓reduceIte]
      set y₀ : ∀ w, α w := fun w ↦ (M.develop s w).getD default
      have hy₀ : ∀ w, M.graph.Adj w v → ∀ z : α w, M.develop s w = some z → y₀ w = z :=
        fun w _ z hz ↦ by simp [y₀, hz]
      rw [hpar]
      by_cases hp : ∀ w, M.graph.Adj w v → M.develop s w ≠ none
      · have hagree : ∀ u (y : ∀ w, α w),
            (∀ w, M.graph.Adj w v → ∀ z : α w, M.develop s w = some z → y w = z) →
              M.eqn v u y = M.eqn v u y₀ := fun u y hy ↦
          M.dependsOn_eqn v u fun w (hw : M.graph.Adj w v) ↦ by
            obtain ⟨z, hz⟩ := Option.ne_none_iff_exists'.1 (hp w hw)
            rw [hy w hw z hz, hy₀ w hw z hz]
        rw [ite_eq_left_of_eq_true (h := eq_true hp), and_iff_right hp]
        constructor
        · intro h
          have hx : ∀ u, M.eqn v u y₀ = x := fun u ↦ h u y₀ hy₀
          have hc : ∀ u, M.eqn v u y₀ = M.eqn v default y₀ := fun u ↦ (hx u).trans (hx default).symm
          rw [ite_eq_left_of_eq_true (h := eq_true hc), hx default]
        · intro h u y hy
          split_ifs at h with hc
          rw [hagree u y hy, hc u]
          exact Option.some_inj.1 h
      · simp [hp]

section Decidable

variable {v : V} {x : α v}

theorem causallyEntails_iff_iterate {s : ∀ v, Option (α v)} :
    M.CausallyEntails (fun v ↦ ↑(s v)) v x ↔
      (M.developStep s)^[Fintype.card V] (fun _ ↦ none) v = some x := by
  rw [causallyEntails_iff_develop, develop,
    WellFounded.fixedPoint_eq_iterate_card (dependsOn_developStep s) fun _ ↦ none]

/-- In a finite model, causal entailment from a situation with decidable domains is decided by
computing the strict development of its options. -/
instance (s : ∀ v, Part (α v)) [∀ v, Decidable (s v).Dom] :
    Decidable (M.CausallyEntails s v x) :=
  decidable_of_iff ((M.developStep fun v ↦ (s v).toOption)^[Fintype.card V] (fun _ ↦ none) v =
    some x) <| by rw [← causallyEntails_iff_iterate]; simp only [Part.of_toOption]

end Decidable

end Develop

section DevelopKleene

/-! ### Computing the Kleene development

A variable the Kleene development forces takes the value its equation gives at any completion of
what is known about its parents, in any context. `developKleene` computes it by testing the value
at one completion against every completion and context, one value per variable. -/

variable (M) [Fintype U] [Inhabited U] [∀ v, Inhabited (α v)] [∀ v, DecidableEq (α v)]
  [∀ v, Fintype (α v)] [Fintype V] [DecidableEq V] [DecidableRel M.graph.Adj]

/-- `M.developKleeneStep s p` is one round of the Kleene development as options. A variable `s`
settles keeps its value; one `s` leaves open is settled when its equation gives the same value in
every context on every assignment extending what `p` settles about its parents. -/
def developKleeneStep (s p : ∀ v, Option (α v)) : ∀ v, Option (α v) := fun v ↦
  if s v = none then
    if ∀ u (y : ∀ w, α w), (∀ w, M.graph.Adj w v → p w = none ∨ p w = some (y w)) →
        M.eqn v u y = M.eqn v default fun w ↦ (p w).getD default then
      some (M.eqn v default fun w ↦ (p w).getD default)
    else none
  else s v

variable {M}

omit hM [∀ v, Nonempty (α v)] in
theorem dependsOn_developKleeneStep (s : ∀ v, Option (α v)) (v : V) :
    DependsOn (M.developKleeneStep s · v) {w | M.graph.Adj w v} := fun p q h ↦ by
  have heqn : ∀ u, M.eqn v u (fun w ↦ (p w).getD default) =
      M.eqn v u (fun w ↦ (q w).getD default) := fun u ↦
    M.dependsOn_eqn v u fun w hw ↦ by simp only [h w hw]
  have hcond : ∀ y : ∀ w, α w, (∀ w, M.graph.Adj w v → p w = none ∨ p w = some (y w)) ↔
      ∀ w, M.graph.Adj w v → q w = none ∨ q w = some (y w) :=
    fun _ ↦ forall₂_congr fun w hw ↦ by rw [h w hw]
  simp only [developKleeneStep, heqn, hcond]

variable (M) in
/-- The Kleene development of the observation `s`, given as options. -/
noncomputable def developKleene (s : ∀ v, Option (α v)) : ∀ v, Option (α v) :=
  hM.fixedPoint (M.developKleeneStep s)

theorem developKleene_apply (s : ∀ v, Option (α v)) (v : V) :
    M.developKleene s v = M.developKleeneStep s (M.developKleene s) v :=
  WellFounded.fixedPoint_apply (dependsOn_developKleeneStep s) v

theorem forced_iff_developKleene {s : ∀ v, Option (α v)} {v : V} {x : α v} :
    M.Forced (fun v ↦ ↑(s v)) v x ↔ M.developKleene s v = some x := by
  induction v using hM.induction with
  | _ v ih =>
    have hcons : ∀ y : ∀ w, α w,
        (∀ w, M.graph.Adj w v → ∀ z, M.Forced (fun v ↦ ↑(s v)) w z → y w = z) ↔
          ∀ w, M.graph.Adj w v → M.developKleene s w = none ∨
            M.developKleene s w = some (y w) := fun y ↦
      forall₂_congr fun w hw ↦ by
        simp only [ih w hw]
        cases M.developKleene s w with
        | none => simp
        | some a => simp [eq_comm]
    rw [forced_iff, developKleene_apply, developKleeneStep]
    simp only [ForcedBy, hcons]
    set y₀ : ∀ w, α w := fun w ↦ (M.developKleene s w).getD default
    have hy₀ : ∀ w, M.graph.Adj w v → M.developKleene s w = none ∨
        M.developKleene s w = some (y₀ w) := fun w _ ↦ by
      simp only [y₀]; cases M.developKleene s w with
      | none => exact .inl rfl
      | some a => exact .inr rfl
    cases hs : s v with
    | some a => simp [Part.some_inj]
    | none =>
      simp only [Part.coe_none, ← Part.bot_eq_none, Part.bot_ne_some, false_or, true_and,
        ↓reduceIte]
      constructor
      · intro h
        have hx : ∀ u, M.eqn v u y₀ = x := fun u ↦ h u y₀ hy₀
        rw [ite_eq_left_of_eq_true (h := eq_true fun u y hy ↦ (h u y hy).trans (hx default).symm),
          hx default]
      · intro h u y hy
        split_ifs at h with hc
        exact (hc u y hy).trans (Option.some_inj.1 h)

theorem forced_iff_iterate {s : ∀ v, Option (α v)} {v : V} {x : α v} :
    M.Forced (fun v ↦ ↑(s v)) v x ↔
      (M.developKleeneStep s)^[Fintype.card V] (fun _ ↦ none) v = some x := by
  rw [forced_iff_developKleene, developKleene,
    WellFounded.fixedPoint_eq_iterate_card (dependsOn_developKleeneStep s) fun _ ↦ none]

/-- In a finite model, being forced from a situation with decidable domains is decided by
computing the Kleene development of its options. -/
instance (s : ∀ v, Part (α v)) [∀ v, Decidable (s v).Dom] (v : V) (x : α v) :
    Decidable (M.Forced s v x) :=
  decidable_of_iff ((M.developKleeneStep fun v ↦ (s v).toOption)^[Fintype.card V]
    (fun _ ↦ none) v = some x) <| by rw [← forced_iff_iterate]; simp only [Part.of_toOption]

end DevelopKleene

end CausalModel
