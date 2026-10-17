module

public import Linglib.Semantics.Presupposition.Context
public import Linglib.Core.Logic.Function.DependsOn

/-!
# Transparency and local contexts

Schlenker defines transparency and local contexts on syntactic environments. A syntactic
environment is represented by the set of functions from the denotation of its gap to the
sentence's truth set, one for each continuation of the string that the theory consults. A
restriction `x` on the gap is transparent in a context set `C` when restricting any denotation of
the gap by `x` changes the sentence's truth value at no world of `C`, for every such function
(`Transparent`). The local context is the least transparent restriction (`IsLocalContext`), and a
presupposition is satisfied when it is entailed by the local context (`Satisfied`).

A restriction is transparent iff at each world of the context, under each continuation, the
sentence's truth value factors through restricting the gap by it (`transparent_iff_factorsThrough`).
When the gap denotes a set of indices, worlds for a clause or world–individual pairs for a
predicate, this is dependence: the truth value depends only on the gap's denotation within the
restriction (`transparent_iff_dependsOn`). The local context is then the set of indices on which the
truth value depends at some world of the context under some continuation, and it exists whenever
each of these truth values depends on finitely many indices (`isLocalContext_of_dependsOn`). In the
propositional case every environment is truth-functional, the truth value at a world depending only
on the gap's value there (`IsTruthFunctional`), so the local context is the set of worlds of the
context at which the truth value depends on the gap for some continuation
(`isLocalContext_of_isTruthFunctional`).

A restriction is transparent at an assertion when it is transparent for the denotations of the gap
that agree with that assertion on it (`TransparentAt`), the resolutions of a trigger that
presupposes the restriction and asserts the assertion. Transparency at the trigger's own assertion
is the trigger's definedness by supervaluation, every resolution giving the sentence the same truth
value (`transparentAt_iff`), and transparency is transparency at every assertion
(`transparent_iff_forall_transparentAt`).

A restriction is stably transparent when it never settles the truth value across a set of
continuations unless the unrestricted gap settles it the same way (`StablyTransparent`), the
condition Kalomoiros's Limited Symmetry imposes at each parsing point after a trigger. It is weaker
than transparency, and the two coincide for a single continuation, so that transparency is stable
transparency for each continuation alone (`transparent_iff_forall_stablyTransparent_singleton`).
Transparency, unlike stability, is unchanged when the gap is negated
(`transparent_image_compl_iff`).

## Main definitions

* `Presupposition.Transparent`: a transparent restriction of a gap.
* `Presupposition.IsLocalContext`: the least transparent restriction.
* `Presupposition.Satisfied`: satisfaction of a presupposition in the local context.
* `Presupposition.TransparentAt`: transparency for the resolutions of a trigger.
* `Presupposition.StablyTransparent`: a restriction that settles no truth value the gap leaves
  open.

## Main results

* `Presupposition.transparent_iff_forall_transparentAt`, `Presupposition.transparentAt_iff`:
  transparency is definedness by supervaluation at every assertion.
* `Presupposition.transparent_iff_factorsThrough`: the truth value factors through the
  restriction.
* `Presupposition.transparent_iff_dependsOn`: transparency is dependence.
* `Presupposition.transparent_iff_forall_stablyTransparent_singleton`: transparency is stable
  transparency for each continuation alone.
* `Presupposition.isLocalContext_of_dependsOn`: the local context is the set of indices the truth
  value depends on.
* `Presupposition.IsLocalContext.satisfied_iff_transparent`: where the local context exists,
  satisfaction is transparency.

## Implementation notes

The paper states transparency for strings, quantifying over the expressions that may fill the
gap; here the gap's denotation ranges over the whole type, which is the paper's Expressivity
assumption and the reading that its existence proofs require. The local context is restricted to
the context set, so a world outside it constrains nothing.

## References

* [schlenker-2009]
* [kalomoiros-2023]
-/

@[expose] public section

namespace Presupposition

variable {W α : Type*} [SemilatticeInf α]

/-- A restriction `x` on the gap of the environment `env` is transparent in the context `C` when
restricting any denotation `d` of the gap by `x` changes the truth value at no world of `C`, for
every continuation in `env`. -/
def Transparent (C : Set W) (env : Set (α → Set W)) (x : α) : Prop :=
  ∀ f ∈ env, ∀ d : α, ∀ w ∈ C, w ∈ f (x ⊓ d) ↔ w ∈ f d

/-- The local context of the gap of `env` in `C` is its least transparent restriction. -/
def IsLocalContext (C : Set W) (env : Set (α → Set W)) (x : α) : Prop :=
  IsLeast {x | Transparent C env x} x

theorem Transparent.anti {C : Set W} {env env' : Set (α → Set W)} {x : α} (h : env' ⊆ env)
    (hx : Transparent C env x) : Transparent C env' x :=
  fun f hf ↦ hx f (h hf)

/-- Transparency holds in a context iff it holds at each of its worlds. -/
theorem transparent_iff_forall_singleton {C : Set W} {env : Set (α → Set W)} {x : α} :
    Transparent C env x ↔ ∀ w ∈ C, Transparent {w} env x :=
  ⟨fun h w hw f hf d _ hv ↦ hv ▸ h f hf d w hw, fun h f hf d w hw ↦ h w hw f hf d w rfl⟩

theorem IsLocalContext.unique {C : Set W} {env : Set (α → Set W)} {x y : α}
    (hx : IsLocalContext C env x) (hy : IsLocalContext C env y) : x = y :=
  IsLeast.unique hx hy

/-- A presupposition `P` on the gap of `env` is satisfied in `C` when the local context exists
and entails it. -/
def Satisfied (C : Set W) (env : Set (α → Set W)) (P : α) : Prop :=
  ∃ x, IsLocalContext C env x ∧ x ≤ P

theorem satisfied_iff {C : Set W} {env : Set (α → Set W)} {x : α} (h : IsLocalContext C env x)
    (P : α) : Satisfied C env P ↔ x ≤ P :=
  ⟨fun ⟨_, hy, hP⟩ ↦ h.unique hy ▸ hP, fun hP ↦ ⟨x, h, hP⟩⟩

section Lattice

variable {C : Set W} {env : Set (α → Set W)} {x y : α}

/-- A restriction is transparent iff at each world of the context, under each continuation, the
sentence's truth value factors through restricting the gap by it. -/
theorem transparent_iff_factorsThrough : Transparent C env x ↔
    ∀ f ∈ env, ∀ w ∈ C, Function.FactorsThrough (fun d ↦ w ∈ f d) (x ⊓ ·) := by
  refine ⟨fun h f hf w hw d d' hd ↦ ?_, fun h f hf d w hw ↦ Iff.of_eq (h f hf w hw ?_)⟩
  · change x ⊓ d = x ⊓ d' at hd
    exact propext ((h f hf d w hw).symm.trans (by rw [hd]; exact h f hf d' w hw))
  · exact (inf_assoc x x d).symm.trans (congrArg (· ⊓ d) (inf_idem x))

/-- A restriction weaker than a transparent one is transparent. -/
theorem Transparent.mono (hx : Transparent C env x) (hxy : x ≤ y) : Transparent C env y :=
  fun f hf d w hw ↦ by
    rw [← hx f hf (y ⊓ d) w hw, ← inf_assoc, inf_eq_left.2 hxy]
    exact hx f hf d w hw

/-- Transparent restrictions are closed under conjunction (C.13). -/
theorem Transparent.inf (hx : Transparent C env x) (hy : Transparent C env y) :
    Transparent C env (x ⊓ y) := fun f hf d w hw ↦ by
  rw [inf_assoc, hx f hf (y ⊓ d) w hw]
  exact hy f hf d w hw

/-- Where the local context exists, a presupposition is satisfied iff it is transparent. -/
theorem IsLocalContext.satisfied_iff_transparent (h : IsLocalContext C env x) (P : α) :
    Satisfied C env P ↔ Transparent C env P := by
  rw [satisfied_iff h]
  exact ⟨h.1.mono, fun hP ↦ h.2 hP⟩

/-- A satisfied presupposition is transparent. -/
theorem Satisfied.transparent (h : Satisfied C env x) : Transparent C env x :=
  let ⟨_, hy, hyx⟩ := h
  hy.1.mono hyx

end Lattice

/-! ### Transparency at an assertion -/

/-- A restriction `x` on the gap of `env` is transparent in `C` at the assertion `a` when it is
transparent for the denotations of the gap that agree with `a` on `x`. These are the resolutions of
a trigger presupposing `x` and asserting `a`, which resolve its presupposition failure either way,
so that transparency at `a` is the definedness of the trigger by supervaluation: every resolution
gives the sentence the same truth value at each world of `C` (`transparentAt_iff`). -/
def TransparentAt (C : Set W) (env : Set (α → Set W)) (x a : α) : Prop :=
  ∀ f ∈ env, ∀ d, x ⊓ d = x ⊓ a → ∀ w ∈ C, w ∈ f (x ⊓ d) ↔ w ∈ f d

section At

variable {C : Set W} {env : Set (α → Set W)} {x a : α}

theorem Transparent.transparentAt (h : Transparent C env x) (a : α) : TransparentAt C env x a :=
  fun f hf d _ ↦ h f hf d

/-- Transparency is transparency at every assertion: it quantifies over the assertion that
supervaluation holds fixed. -/
theorem transparent_iff_forall_transparentAt : Transparent C env x ↔ ∀ a, TransparentAt C env x a :=
  ⟨Transparent.transparentAt, fun h f hf d ↦ h d f hf d rfl⟩

/-- Transparency at `a` says that the resolutions of the trigger give the sentence one truth value
at each world of the context. -/
theorem transparentAt_iff : TransparentAt C env x a ↔
    ∀ f ∈ env, ∀ d d', x ⊓ d = x ⊓ a → x ⊓ d' = x ⊓ a → ∀ w ∈ C, (w ∈ f d ↔ w ∈ f d') := by
  refine ⟨fun h f hf d d' hd hd' w hw ↦ ?_, fun h f hf d hd w hw ↦ h f hf _ _ ?_ hd w hw⟩
  · rw [← h f hf d hd w hw, ← h f hf d' hd' w hw, hd, hd']
  · rw [← inf_assoc, inf_idem, hd]

end At

/-! ### Transparency is dependence -/

section Dependence

variable {ι : Type*} {C : Set W} {env : Set (Set ι → Set W)} {x : Set ι}

/-- A restriction is transparent iff at each world of the context, under each continuation, the
sentence's truth value depends only on the gap's denotation within the restriction. -/
theorem transparent_iff_dependsOn :
    Transparent C env x ↔ ∀ f ∈ env, ∀ w ∈ C, DependsOn (fun d : Set ι ↦ w ∈ f d) x := by
  have h (d d' : Set ι) : x ⊓ d = x ⊓ d' ↔ ∀ i ∈ x, d i = d' i :=
    ⟨fun h i hi ↦ propext ⟨fun hd ↦ (h ▸ ⟨hi, hd⟩ : i ∈ x ⊓ d').2,
      fun hd ↦ (h ▸ ⟨hi, hd⟩ : i ∈ x ⊓ d).2⟩,
      fun h ↦ Set.ext fun i ↦ and_congr_right fun hi ↦ Iff.of_eq (h i hi)⟩
  rw [transparent_iff_factorsThrough]
  exact forall₂_congr fun f _ ↦ forall₂_congr fun w _ ↦
    ⟨fun hf d d' hd ↦ hf ((h d d').2 hd), fun hf d d' hd ↦ hf ((h d d').1 hd)⟩

/-- If the truth value at each world of the context, under each continuation, depends on finitely
many indices, the local context exists: it is the set of indices on which the truth value depends
at some world of the context under some continuation. -/
theorem isLocalContext_of_dependsOn
    (h : ∀ f ∈ env, ∀ w ∈ C, ∃ s : Set ι, s.Finite ∧ DependsOn (fun d : Set ι ↦ w ∈ f d) s) :
    IsLocalContext C env
      {i | ∃ f ∈ env, ∃ w ∈ C, ¬ DependsOn (fun d : Set ι ↦ w ∈ f d) {i}ᶜ} := by
  refine ⟨transparent_iff_dependsOn.2 fun f hf w hw ↦ ?_, fun y hy i ⟨f, hf, w, hw, hi⟩ ↦ ?_⟩
  · obtain ⟨s, hs, hd⟩ := h f hf w hw
    exact (isLeast_dependsOn hs hd).1.mono fun i hi ↦ ⟨f, hf, w, hw, hi⟩
  · exact by_contra fun hiy ↦ hi ((transparent_iff_dependsOn.1 hy f hf w hw).mono
      (Set.subset_compl_singleton_iff.2 hiy))

end Dependence

/-! ### Negating the gap -/

section Compl

variable {β : Type*} [BooleanAlgebra β]

private theorem forall_inf_compl_iff {P : β → Prop} {x : β} :
    (∀ d, P (x ⊓ d)ᶜ ↔ P dᶜ) ↔ ∀ d, P (x ⊓ d) ↔ P d := by
  have hY : (∀ d, P (x ⊓ d)ᶜ ↔ P dᶜ) ↔ ∀ y, P (xᶜ ⊔ y) ↔ P y :=
    ⟨fun h y ↦ by simpa [compl_inf] using h yᶜ, fun h d ↦ by simpa [compl_inf] using h dᶜ⟩
  rw [hY]
  refine ⟨fun h d ↦ ?_, fun h y ↦ ?_⟩
  · rw [← h (x ⊓ d), sup_inf_left, compl_sup_eq_top, top_inf_eq, h d]
  · rw [← h (xᶜ ⊔ y), inf_sup_left, inf_compl_eq_bot, bot_sup_eq, h y]

/-- Transparency is invariant under negating the gap. A restriction is transparent for a set of
continuations iff it is transparent for the same continuations applied to the gap's negation. -/
theorem transparent_image_compl_iff {C : Set W} {env : Set (β → Set W)} {x : β} :
    Transparent C ((fun f d ↦ f dᶜ) '' env) x ↔ Transparent C env x := by
  simp only [Transparent, Set.forall_mem_image]
  refine forall₂_congr fun f _ ↦ ⟨fun h d w hw ↦ ?_, fun h d w hw ↦ ?_⟩
  · exact (forall_inf_compl_iff (P := (w ∈ f ·))).1 (fun d ↦ h d w hw) d
  · exact (forall_inf_compl_iff (P := (w ∈ f ·))).2 (fun d ↦ h d w hw) d

end Compl

/-! ### Stable transparency -/

/-- A restriction `x` on the gap is stably transparent in `C` for a set of continuations when
restricting a denotation `d` by `x` settles the truth value at a world of `C` across all of them
only where `d` settles it the same way: wherever every continuation makes the sentence true
(false) with `x ⊓ d`, every continuation makes it true (false) with `d`. -/
def StablyTransparent (C : Set W) (env : Set (α → Set W)) (x : α) : Prop :=
  ∀ d, ∀ w ∈ C, ((∀ f ∈ env, w ∈ f (x ⊓ d)) → ∀ f ∈ env, w ∈ f d) ∧
    ((∀ f ∈ env, w ∉ f (x ⊓ d)) → ∀ f ∈ env, w ∉ f d)

section Stable

variable {C : Set W} {env : Set (α → Set W)} {x : α}

theorem Transparent.stablyTransparent (h : Transparent C env x) : StablyTransparent C env x :=
  fun d w hw ↦ ⟨fun ht f hf ↦ (h f hf d w hw).1 (ht f hf),
    fun hn f hf hd ↦ hn f hf ((h f hf d w hw).2 hd)⟩

/-- For a single continuation, stable transparency is transparency. -/
theorem stablyTransparent_singleton_iff {f : α → Set W} :
    StablyTransparent C {f} x ↔ Transparent C {f} x := by
  refine ⟨fun h g hg d w hw ↦ ?_, Transparent.stablyTransparent⟩
  obtain rfl := Set.mem_singleton_iff.1 hg
  have h' := h d w hw
  simp only [Set.mem_singleton_iff, forall_eq] at h'
  exact ⟨h'.1, fun hd ↦ by_contra fun hn ↦ h'.2 hn hd⟩

/-- Transparency is stable transparency for each continuation alone. -/
theorem transparent_iff_forall_stablyTransparent_singleton :
    Transparent C env x ↔ ∀ f ∈ env, StablyTransparent C {f} x := by
  simp only [stablyTransparent_singleton_iff, Transparent, Set.mem_singleton_iff, forall_eq]

end Stable

/-! ### Truth-functional environments -/

/-- A continuation is truth-functional when the sentence's truth value at a world depends only on
the gap's truth value there. -/
def IsTruthFunctional (f : Set W → Set W) : Prop :=
  ∀ w d d', (w ∈ d ↔ w ∈ d') → (w ∈ f d ↔ w ∈ f d')

/-- The sentence's truth value at `w` depends on the gap of a continuation. -/
def DependsAt (f : Set W → Set W) (w : W) : Prop := ¬ (w ∈ f Set.univ ↔ w ∈ f ∅)

section TruthFunctional

variable {C x : Set W} {env : Set (Set W → Set W)}

theorem IsTruthFunctional.mem_iff_of_mem {f : Set W → Set W} (hf : IsTruthFunctional f)
    {w : W} {d : Set W} (h : w ∈ d) : w ∈ f d ↔ w ∈ f Set.univ :=
  hf w _ _ (by simp [h])

theorem IsTruthFunctional.mem_iff_of_notMem {f : Set W → Set W} (hf : IsTruthFunctional f)
    {w : W} {d : Set W} (h : w ∉ d) : w ∈ f d ↔ w ∈ f ∅ :=
  hf w _ _ (by simp [h])

/-- A restriction is transparent for truth-functional continuations iff it contains every world of
the context at which the truth value depends on the gap for some continuation. -/
theorem transparent_iff_subset (henv : ∀ f ∈ env, IsTruthFunctional f) :
    Transparent C env x ↔ C ∩ {w | ∃ f ∈ env, DependsAt f w} ⊆ x := by
  refine ⟨fun h w ⟨hw, f, hf, hdep⟩ ↦ by_contra fun hx ↦ hdep ?_, fun h f hf d w hw ↦ ?_⟩
  · exact ((h f hf Set.univ w hw).symm.trans
      ((henv f hf).mem_iff_of_notMem (by simpa using hx)))
  · by_cases hx : w ∈ x
    · exact henv f hf w _ _ (by simp [hx])
    · have hind : w ∈ f Set.univ ↔ w ∈ f ∅ := by
        by_contra hdep; exact hx (h ⟨hw, f, hf, hdep⟩)
      rw [(henv f hf).mem_iff_of_notMem (by simp [hx] : w ∉ x ⊓ d)]
      by_cases hd : w ∈ d
      · rw [(henv f hf).mem_iff_of_mem hd, hind]
      · rw [(henv f hf).mem_iff_of_notMem hd]

/-- The local context of truth-functional continuations exists: it is the set of worlds of the
context at which the truth value depends on the gap for some continuation. -/
theorem isLocalContext_of_isTruthFunctional (henv : ∀ f ∈ env, IsTruthFunctional f) :
    IsLocalContext C env (C ∩ {w | ∃ f ∈ env, DependsAt f w}) :=
  ⟨(transparent_iff_subset henv).2 le_rfl, fun _ hy ↦ (transparent_iff_subset henv).1 hy⟩

/-- For truth-functional continuations, a presupposition is satisfied in its local context iff it
is a transparent restriction. -/
theorem satisfied_iff_transparent (henv : ∀ f ∈ env, IsTruthFunctional f) (P : Set W) :
    Satisfied C env P ↔ Transparent C env P :=
  (isLocalContext_of_isTruthFunctional henv).satisfied_iff_transparent P

/-- A restriction is stably transparent for truth-functional continuations iff at each world of the
context outside it, whenever the continuations agree on the truth value with a false gap, they
agree on it with a true gap. -/
theorem stablyTransparent_iff (henv : ∀ f ∈ env, IsTruthFunctional f) :
    StablyTransparent C env x ↔ ∀ w ∈ C, w ∉ x →
      ((∀ f ∈ env, w ∈ f ∅) → ∀ f ∈ env, w ∈ f Set.univ) ∧
        ((∀ f ∈ env, w ∉ f ∅) → ∀ f ∈ env, w ∉ f Set.univ) := by
  refine ⟨fun h w hw hx ↦ ?_, fun h d w hw ↦ ?_⟩
  · have e {f} (hf : f ∈ env) : w ∈ f (x ⊓ Set.univ) ↔ w ∈ f ∅ :=
      (henv f hf).mem_iff_of_notMem (by simpa using hx)
    exact ⟨fun h₀ f hf ↦ (h Set.univ w hw).1 (fun g hg ↦ (e hg).2 (h₀ g hg)) f hf,
      fun h₀ f hf ↦ (h Set.univ w hw).2 (fun g hg hm ↦ h₀ g hg ((e hg).1 hm)) f hf⟩
  by_cases hx : w ∈ x
  · have e {f} (hf : f ∈ env) : w ∈ f (x ⊓ d) ↔ w ∈ f d := henv f hf w _ _ (by simp [hx])
    exact ⟨fun h' f hf ↦ (e hf).1 (h' f hf), fun h' f hf hd ↦ h' f hf ((e hf).2 hd)⟩
  have e {f} (hf : f ∈ env) : w ∈ f (x ⊓ d) ↔ w ∈ f ∅ :=
    (henv f hf).mem_iff_of_notMem (by simp [hx])
  by_cases hd : w ∈ d
  · have e' {f} (hf : f ∈ env) : w ∈ f d ↔ w ∈ f Set.univ := (henv f hf).mem_iff_of_mem hd
    exact ⟨fun h' f hf ↦ (e' hf).2 ((h w hw hx).1 (fun g hg ↦ (e hg).1 (h' g hg)) f hf),
      fun h' f hf hm ↦ (h w hw hx).2 (fun g hg hm' ↦ h' g hg ((e hg).2 hm')) f hf ((e' hf).1 hm)⟩
  · have e' {f} (hf : f ∈ env) : w ∈ f d ↔ w ∈ f ∅ := (henv f hf).mem_iff_of_notMem hd
    exact ⟨fun h' f hf ↦ (e' hf).2 ((e hf).1 (h' f hf)),
      fun h' f hf hm ↦ h' f hf ((e hf).2 ((e' hf).1 hm))⟩

end TruthFunctional

end Presupposition
