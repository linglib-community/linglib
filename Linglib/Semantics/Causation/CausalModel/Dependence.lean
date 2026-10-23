module

public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Pi
public import Linglib.Semantics.Causation.CausalModel.Development

/-!
# Causal sufficiency and causal necessity

Nadathur and Lauer draw on two relations of causal dependence for the meanings of periphrastic
causatives, both over the strict development of an observation (`CausalModel.CausallyEntails`). A
fact is causally sufficient for another relative to a background when the background does not
settle the effect but, with the cause added, does. A fact is causally necessary for another when
the background does not settle the effect, some supersituation of the background with the cause
settles the effect, and every supersituation of the background that settles the effect settles
the cause.

## Main definitions

* `CausalModel.CausallySufficient`: Nadathur and Lauer's causal sufficiency
* `CausalModel.CausallyNecessary`: Nadathur and Lauer's causal necessity, over a given relation of
  supersituation
* `CausalModel.IsExogenousSettlement`: an extension of an observation at exogenous variables

## Main results

* `CausalModel.CausallySufficient.reflTransGen`: a cause sufficient for an effect is its ancestor
* `CausalModel.CausallySufficient.solve_eq`, `CausalModel.CausallyNecessary.solve_eq`: in every
  context where the background holds, a sufficient cause brings its effect about, and an effect
  needs its necessary cause
* `CausalModel.CausallyEntails.of_isExogenousSettlement`: settling exogenous variables settles
  no less
* `CausalModel.isExogenousSettlement_update`, `CausalModel.IsExogenousSettlement.trans`

## Implementation notes

Necessity takes the supersituations it quantifies over as a parameter: every supersituation,
`(· ≤ ·)`, for Nadathur and Lauer, and for the worked examples of [nadathur-2023-implicatives] the
exogenous settlements, the extensions at the variables with no parents that the background leaves
open. Over every supersituation, one settling a variable between cause and effect reaches the
effect around the cause. In a finite model each relation is decided through the computed strict
development (`CausalModel.causallyEntails_iff_develop`).

## References

* [nadathur-lauer-2020]
* [nadathur-2023-implicatives]
-/

@[expose] public section

namespace CausalModel

variable {U V : Type*} {α : V → Type*} (M : CausalModel U V α) [M.IsAcyclic] [DecidableEq V]

/-- `M.CausallySufficient s c x e y` says that `c = x` is causally sufficient for `e = y` relative
to the background `s`. The background does not settle the effect, and the background together with
the cause does. -/
def CausallySufficient (s : ∀ v, Flat (α v)) (c : V) (x : α c) (e : V) (y : α e) : Prop :=
  ¬ M.CausallyEntails s e y ∧ M.CausallyEntails (Function.update s c ↑x) e y

/-- `M.CausallyNecessary r s c x e y` says that `c = x` is causally necessary for `e = y` relative
to the background `s`, where `r s s'` says that `s'` is a supersituation of `s`. The background
does not settle the effect; some supersituation of the background with the cause added, leaving the
effect open, settles the effect; and every supersituation of the background leaving the effect open
that settles the effect settles the cause. -/
def CausallyNecessary (r : (∀ v, Flat (α v)) → (∀ v, Flat (α v)) → Prop) (s : ∀ v, Flat (α v))
    (c : V) (x : α c) (e : V) (y : α e) : Prop :=
  ¬ M.CausallyEntails s e y ∧
  (∃ s', r (Function.update s c ↑x) s' ∧ s' e = ⊥ ∧ M.CausallyEntails s' e y) ∧
  ∀ s', r s s' → s' e = ⊥ → M.CausallyEntails s' e y → M.CausallyEntails s' c x

/-- `s'` settles the observation `s` further at exogenous variables only, those with no parents
that the strict development of `s` leaves open. -/
def IsExogenousSettlement (s s' : ∀ v, Flat (α v)) : Prop :=
  s ≤ s' ∧ ∀ v, s v = ⊥ → s' v ≠ ⊥ → (∀ w, ¬ M.graph.Adj w v) ∧ ∀ x, ¬ M.CausallyEntails s v x

variable {M}

theorem CausallySufficient.reflTransGen {s : ∀ v, Flat (α v)} {c : V} {x : α c} {e : V}
    {y : α e} (h : M.CausallySufficient s c x e y) : Relation.ReflTransGen M.graph.Adj c e :=
  Classical.byContradiction fun hce ↦ h.1 ((causallyEntails_update_of_not_reflTransGen hce _).1 h.2)

omit [DecidableEq V] in
theorem CausallyEntails.of_isExogenousSettlement {s s' : ∀ v, Flat (α v)}
    (hs : M.IsExogenousSettlement s s') {v : V} {x : α v} (h : M.CausallyEntails s v x) :
    M.CausallyEntails s' v x := by
  induction v using ‹M.IsAcyclic›.induction with
  | _ v ih =>
    rcases causallyEntails_iff.1 h with hv | ⟨hv, hpar, heq⟩
    · exact causallyEntails_iff.2 (.inl (Flat.coe_le_iff.1 (hv ▸ hs.1 v)))
    · have hv' : s' v = ⊥ := by
        by_contra hne
        exact (hs.2 v hv hne).2 x h
      refine causallyEntails_iff.2 (.inr ⟨hv', fun w hw ↦ ?_, fun u y hy ↦ ?_⟩)
      · obtain ⟨z, hz⟩ := hpar w hw
        exact ⟨z, ih w hw hz⟩
      · exact heq u y fun w hw z hz ↦ hy w hw z (ih w hw hz)

theorem isExogenousSettlement_update {s : ∀ v, Flat (α v)} {p : V}
    (hroot : ∀ w, ¬ M.graph.Adj w p) (hopen : ∀ x, ¬ M.CausallyEntails s p x) (x : α p) :
    M.IsExogenousSettlement s (Function.update s p ↑x) := by
  have hsp : s p = ⊥ := by
    by_contra h
    obtain ⟨y, hy⟩ := Flat.ne_bot_iff_exists.1 h
    exact hopen y (causallyEntails_iff.2 (.inl hy))
  refine ⟨fun v ↦ ?_, fun v hv hne ↦ ?_⟩
  · by_cases hvp : v = p
    · subst hvp; rw [hsp]; exact bot_le
    · rw [Function.update_of_ne hvp]
  · by_cases hvp : v = p
    · subst hvp; exact ⟨hroot, hopen⟩
    · rw [Function.update_of_ne hvp] at hne; exact absurd hv hne

omit [DecidableEq V] in
/-- Every observation is an exogenous settlement of itself. -/
theorem IsExogenousSettlement.refl (s : ∀ v, Flat (α v)) : M.IsExogenousSettlement s s :=
  ⟨le_rfl, fun _ hv hne ↦ absurd hv hne⟩

omit [DecidableEq V] in
theorem IsExogenousSettlement.eq_bot {s s' : ∀ v, Flat (α v)} (h : M.IsExogenousSettlement s s')
    {v : V} (hv : s v = ⊥) (hpar : ∃ w, M.graph.Adj w v) : s' v = ⊥ := by
  by_contra hne
  obtain ⟨w, hw⟩ := hpar
  exact (h.2 v hv hne).1 w hw

omit [DecidableEq V] in
/-- Exogenous settlements compose. -/
theorem IsExogenousSettlement.trans {s s' s'' : ∀ v, Flat (α v)}
    (h₁ : M.IsExogenousSettlement s s') (h₂ : M.IsExogenousSettlement s' s'') :
    M.IsExogenousSettlement s s'' := by
  refine ⟨h₁.1.trans h₂.1, fun v hv hne ↦ ?_⟩
  by_cases hv' : s' v = ⊥
  · exact ⟨(h₂.2 v hv' hne).1, fun x hx ↦ (h₂.2 v hv' hne).2 x (hx.of_isExogenousSettlement h₁)⟩
  · exact h₁.2 v hv hv'

section Contexts

/-! ### Truth in the contexts of a background

A relation of causal dependence relative to a background constrains the actual world of every
context where the background holds. -/

variable [∀ v, Nonempty (α v)] {s : ∀ v, Flat (α v)} {c : V} {x : α c} {e : V} {y : α e}
  {u : U}

theorem CausallySufficient.solve_eq (h : M.CausallySufficient s c x e y) (hu : u ∈ M.contexts s)
    (hc : M.solve ⊥ u c = x) : M.solve ⊥ u e = y :=
  h.2.solve_bot_eq (mem_contexts_update hu hc)

theorem CausallyNecessary.solve_eq [M.ContextAtRoots]
    (h : M.CausallyNecessary M.IsExogenousSettlement s c x e y) (hu : u ∈ M.contexts s)
    (he : M.solve ⊥ u e = y) : M.solve ⊥ u c = x := by
  classical
  obtain ⟨hne, ⟨s', -, hs'e, hent'⟩, hall⟩ := h
  -- settle every open and unsettled root at its value in `u`
  set t : ∀ v, Flat (α v) := fun v ↦
    if s v = ⊥ ∧ (∀ w, ¬ M.graph.Adj w v) ∧ ∀ z, ¬ M.CausallyEntails s v z then
      ↑(M.solve ⊥ u v) else s v with ht
  have hset : M.IsExogenousSettlement s t := by
    refine ⟨fun v ↦ ?_, fun v hv hne ↦ ?_⟩
    · simp only [ht]; split_ifs with hcond
      · rw [hcond.1]; exact bot_le
      · exact le_rfl
    · simp only [ht] at hne; split_ifs at hne with hcond
      · exact hcond.2
      · exact absurd hv hne
  have hut : u ∈ M.contexts t := fun v ↦ by
    simp only [ht]; split_ifs
    · exact le_rfl
    · exact hu v
  have hte : t e = ⊥ := by
    simp only [ht]; split_ifs with hcond
    · exact absurd ((causallyEntails_root_iff hcond.2.1 hcond.1).2
        ((causallyEntails_root_iff hcond.2.1 hs'e).1 hent')) hne
    · by_contra hse
      obtain ⟨z, hz⟩ := Flat.ne_bot_iff_exists.1 hse
      have hzy : z = y := (Flat.coe_le_coe.1 (hz ▸ hu e)).trans he
      exact hne (causallyEntails_iff.2 (.inl (by rw [hz, hzy])))
  have hroot : ∀ v, (∀ w, ¬ M.graph.Adj w v) → ∃ z, M.CausallyEntails t v z := by
    intro v hv
    by_cases hcond : s v = ⊥ ∧ (∀ w, ¬ M.graph.Adj w v) ∧ ∀ z, ¬ M.CausallyEntails s v z
    · refine ⟨M.solve ⊥ u v, causallyEntails_iff.2 (.inl ?_)⟩
      simp only [ht]; split_ifs
      · rfl
    · rcases eq_or_ne (s v) ⊥ with hsv | hsv
      · obtain ⟨z, hz⟩ : ∃ z, M.CausallyEntails s v z := by
          by_contra hz; exact hcond ⟨hsv, hv, not_exists.1 hz⟩
        exact ⟨z, hz.of_isExogenousSettlement hset⟩
      · obtain ⟨z, hz⟩ := Flat.ne_bot_iff_exists.1 hsv
        exact ⟨z, (causallyEntails_iff.2 (.inl hz)).of_isExogenousSettlement hset⟩
  exact (hall t hset hte (he ▸ causallyEntails_solve_bot hroot hut e)).solve_bot_eq hut

end Contexts

section Decidable

variable [Fintype U] [Inhabited U] [∀ v, Inhabited (α v)] [∀ v, DecidableEq (α v)] [Fintype V]
  [DecidableRel M.graph.Adj]

instance (s : ∀ v, Flat (α v)) (c : V) (x : α c) (e : V) (y : α e) :
    Decidable (M.CausallySufficient s c x e y) :=
  inferInstanceAs (Decidable (_ ∧ _))

variable [∀ v, Fintype (α v)]

instance (s s' : ∀ v, Flat (α v)) : Decidable (M.IsExogenousSettlement s s') :=
  haveI : ∀ v, Decidable (s v = ⊥ → s' v ≠ ⊥ →
      (∀ w, ¬ M.graph.Adj w v) ∧ ∀ x, ¬ M.CausallyEntails s v x) := fun _ ↦ inferInstance
  inferInstanceAs (Decidable (_ ∧ _))

/-- Partial assignments over finitely many variables of finite types are finitely many. Not an
instance: a `Fintype` instance on `Flat` would change how `decide` evaluates flat-valued
functions, so necessity installs this one locally. -/
@[reducible] def fintypePartialAssignment : Fintype (∀ v, Flat (α v)) :=
  inferInstanceAs (Fintype (∀ v, Option (α v)))

instance (r : (∀ v, Flat (α v)) → (∀ v, Flat (α v)) → Prop) [∀ s s', Decidable (r s s')]
    (s : ∀ v, Flat (α v)) (c : V) (x : α c) (e : V) (y : α e) :
    Decidable (M.CausallyNecessary r s c x e y) :=
  letI := fintypePartialAssignment (α := α)
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

end Decidable

end CausalModel
