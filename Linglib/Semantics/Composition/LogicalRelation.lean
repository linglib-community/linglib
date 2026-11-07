module

public import Linglib.Core.Data.Set.Functor
public import Linglib.Semantics.Composition.Term

/-!
# Logical relations on the semantic types

Relations on the entities, worlds, degrees and eventualities of two models, and a relator between
their computations, [lift to every semantic type](##Ty.LiftRel): functions are related when they
send related arguments to related computations, propositions when they are equivalent, and sets of
alternatives when each alternative in either has a related alternative in the other.
[Every mode preserves the lifted relation](##Mode.rel_evalKleisli) at every relator that respects
`pure`, `bind` and the flattening of alternatives. Between values this is
[the fundamental lemma for the modes](##Mode.rel_eval), so
[terms with related constants and assignments have related values](##Term.rel_eval), and at type
$t$ a sentence holds in one model exactly when it holds in the other. Between values and partial
values it is the preservation of definedness in `Composition/Partial.lean`. Abstraction under the
set effect [does not preserve the relation](##Term.not_liftRel_distribute).

## Implementation notes

A relator of `Eff` quantifying over its result types would have its recursion motive in a higher
universe than that of `Ty`, and Lean would then compile the mutual definition by well-founded
recursion, which does not reduce. So the recursion through `Eff` is confined to the environment of
a reader (`Eff.EnvRel`), `Ty.LiftRel` is reducible, and at a function type it is mathlib's
`Relator.LiftFun`.

## References

* [statman-1985]
* [quigley-2026]
-/

@[expose] public section

namespace Montague

open Relator (LiftFun)

variable {M M' : Type → Type} {E E' W W' : Type} {S S' : Sorts}

/-- Relations on the base types that a model supplies. Truth values and cardinalities are the same
in every model. -/
structure Ty.BaseRel (E E' W W' : Type) (S S' : Sorts) where
  /-- The relation on entities. -/
  e : E → E' → Prop
  /-- The relation on worlds. -/
  s : W → W' → Prop
  /-- The relation on degrees. -/
  d : S.degree → S'.degree → Prop
  /-- The relation on eventualities. -/
  v : S.eventuality → S'.eventuality → Prop

/-- Equality on every base type of one model. -/
def Ty.BaseRel.eq : Ty.BaseRel E E W W S S := ⟨Eq, Eq, Eq, Eq⟩

/-- The environment of an effect: the reader reads a value of its type, and indeterminacy reads
nothing. -/
abbrev Eff.Env (M : Type → Type) (E W : Type) (f : Eff) (S : Sorts := {}) : Type :=
  match f with
  | .reader ι => Ty.DomainM M E W ι S
  | .set => PUnit

/-- The lifting of a relation on computations to an effect's carrier, given a relation on its
environments. Readers are related when related environments give related computations. Sets of
alternatives lift by `Set.LiftRel`. -/
abbrev Eff.LiftRel {α β : Type} : (f : Eff) →
    (Eff.Env M E W f S → Eff.Env M' E' W' f S' → Prop) → (M α → M' β → Prop) →
    Eff.FM M E W f S α → Eff.FM M' E' W' f S' β → Prop
  | .reader _, ρ, R => LiftFun ρ R
  | .set, _, R => Set.LiftRel R

variable (ρ : ∀ {α β : Type}, (α → β → Prop) → M α → M' β → Prop)

mutual

/-- The logical relation at each semantic type, given a relator `ρ` between computations;
[quigley-2026]'s induced relation when the base relations are the graphs of maps and computations
are values. A predicate and a set of alternatives share a carrier but lift differently: along the
graph of a map, a predicate is related to those it is the preimage of, and a set of alternatives to
its image. -/
abbrev Ty.LiftRel (r : Ty.BaseRel E E' W W' S S') :
    (ty : Ty) → Ty.DomainM M E W ty S → Ty.DomainM M' E' W' ty S' → Prop
  | .e => r.e
  | .t => Iff
  | .d => r.d
  | .n => Eq
  | .v => r.v
  | .s => r.s
  | .fn a b => LiftFun (Ty.LiftRel r a) (ρ (Ty.LiftRel r b))
  | .comp f a => Eff.LiftRel f (Eff.EnvRel r f) (ρ (Ty.LiftRel r a))

/-- The logical relation on the environment of an effect. -/
abbrev Eff.EnvRel (r : Ty.BaseRel E E' W W' S S') :
    (f : Eff) → Eff.Env M E W f S → Eff.Env M' E' W' f S' → Prop
  | .reader ι => Ty.LiftRel r ι
  | .set => fun _ _ ↦ True

end

variable [Monad M] [Monad M'] [FlattenAlternatives M] [FlattenAlternatives M'] {ρ}

/-- A relator between two type constructors of computations respects their units, binds and
flattenings of alternatives. -/
structure KleisliRelator (ρ : ∀ {α β : Type}, (α → β → Prop) → M α → M' β → Prop) : Prop where
  pure {α β : Type} {R : α → β → Prop} {a : α} {b : β} : R a b → ρ R (Pure.pure a) (Pure.pure b)
  bind {α β γ δ : Type} {R : α → β → Prop} {Q : γ → δ → Prop} {x : M α} {y : M' β}
    {f : α → M γ} {g : β → M' δ} : ρ R x y → LiftFun R (ρ Q) f g → ρ Q (x >>= f) (y >>= g)
  flatten {α β : Type} {R : α → β → Prop} {x : M (Set (M α))} {y : M' (Set (M' β))} :
    ρ (Set.LiftRel (ρ R)) x y →
      Set.LiftRel (ρ R) (FlattenAlternatives.flatten x) (FlattenAlternatives.flatten y)

namespace Eff.LiftRel

variable {f : Eff} {env : Eff.Env M E W f S → Eff.Env M' E' W' f S' → Prop} {α β γ δ ε ζ : Type}

omit [Monad M] [Monad M'] [FlattenAlternatives M] [FlattenAlternatives M'] in
protected theorem map {R : M α → M' β → Prop} {Q : M γ → M' δ → Prop} {g : M α → M γ}
    {g' : M' β → M' δ} {x : Eff.FM M E W f S α} {y : Eff.FM M' E' W' f S' β} (hg : LiftFun R Q g g')
    (h : Eff.LiftRel f env R x y) : Eff.LiftRel f env Q (Eff.map f g x) (Eff.map f g' y) := by
  cases f with
  | reader _ => exact fun _ _ hi ↦ hg (h hi)
  | set => exact Set.LiftRel.image h hg

omit [Monad M] [Monad M'] [FlattenAlternatives M] [FlattenAlternatives M'] in
protected theorem pure {Q : M α → M' β → Prop} {a : M α} {b : M' β} (h : Q a b) :
    Eff.LiftRel f env Q (Eff.pure f a) (Eff.pure f b) := by
  cases f with
  | reader _ => exact fun _ _ _ ↦ h
  | set => exact Set.liftRel_singleton.2 h

omit [Monad M] [Monad M'] [FlattenAlternatives M] [FlattenAlternatives M'] in
protected theorem zip {R : M α → M' β → Prop} {Q : M γ → M' δ → Prop} {T : M ε → M' ζ → Prop}
    {g : M α → M γ → M ε} {g' : M' β → M' δ → M' ζ} {x : Eff.FM M E W f S α}
    {y : Eff.FM M' E' W' f S' β} {u : Eff.FM M E W f S γ} {v : Eff.FM M' E' W' f S' δ}
    (hg : LiftFun R (LiftFun Q T) g g') (hx : Eff.LiftRel f env R x y)
    (hu : Eff.LiftRel f env Q u v) : Eff.LiftRel f env T (Eff.zip f g x u) (Eff.zip f g' y v) := by
  cases f with
  | reader _ => exact fun _ _ hi ↦ hg (hx hi) (hu hi)
  | set =>
    refine ⟨?_, ?_⟩
    · rintro _ ⟨a, ha, c, hc, rfl⟩
      obtain ⟨b, hb, hab⟩ := hx.1 a ha
      obtain ⟨d, hd, hcd⟩ := hu.1 c hc
      exact ⟨_, ⟨b, hb, d, hd, rfl⟩, hg hab hcd⟩
    · rintro _ ⟨b, hb, d, hd, rfl⟩
      obtain ⟨a, ha, hab⟩ := hx.2 b hb
      obtain ⟨c, hc, hcd⟩ := hu.2 d hd
      exact ⟨_, ⟨a, ha, c, hc, rfl⟩, hg hab hcd⟩

protected theorem join (hρ : KleisliRelator ρ) {R : α → β → Prop}
    {x : Eff.FM M E W f S (Eff.FM M E W f S α)} {y : Eff.FM M' E' W' f S' (Eff.FM M' E' W' f S' β)}
    (h : Eff.LiftRel f env (ρ (Eff.LiftRel f env (ρ R))) x y) :
    Eff.LiftRel f env (ρ R) (Eff.joinKleisli f x) (Eff.joinKleisli f y) := by
  cases f with
  | reader _ => exact fun _ _ hi ↦ hρ.bind (h hi) fun _ _ hy ↦ hy hi
  | set =>
    refine ⟨?_, ?_⟩
    · rintro z ⟨a, ha, hz⟩
      obtain ⟨b, hb, hab⟩ := h.1 a ha
      obtain ⟨w, hw, hzw⟩ := (hρ.flatten hab).1 z hz
      exact ⟨w, ⟨b, hb, hw⟩, hzw⟩
    · rintro w ⟨b, hb, hw⟩
      obtain ⟨a, ha, hab⟩ := h.2 b hb
      obtain ⟨z, hz, hzw⟩ := (hρ.flatten hab).2 w hw
      exact ⟨z, ⟨a, ha, hz⟩, hzw⟩

end Eff.LiftRel

variable {r : Ty.BaseRel E E' W W' S S'}

/-- Every mode preserves the logical relation at every relator: the engine's ways of composing two
daughters depend on nothing about a model, or about how a computation runs, beyond what the relator
relates. -/
theorem Mode.rel_evalKleisli (hρ : KleisliRelator ρ) : ∀ {σ₁ σ₂ τ : Ty} (m : Mode σ₁ σ₂ τ),
    LiftFun (ρ (Ty.LiftRel ρ r σ₁)) (LiftFun (ρ (Ty.LiftRel ρ r σ₂)) (ρ (Ty.LiftRel ρ r τ)))
      (Mode.evalKleisli (M := M) (E := E) (W := W) (S := S) m)
      (Mode.evalKleisli (M := M') (E := E') (W := W') (S := S') m)
  | _, _, _, .functionalLeft => fun _ _ hf _ _ ha ↦ hρ.bind hf fun _ _ hv ↦ hρ.bind ha hv
  | _, _, _, .functionalRight => fun _ _ ha _ _ hf ↦ hρ.bind hf fun _ _ hv ↦ hρ.bind ha hv
  | _, _, _, .predicateModification _ => fun _ _ hp _ _ hq ↦
      hρ.bind hp fun _ _ hP ↦ hρ.bind hq fun _ _ hQ ↦ hρ.pure fun _ _ hx ↦
        hρ.bind (hP hx) fun _ _ ha ↦ hρ.bind (hQ hx) fun _ _ hb ↦ hρ.pure (and_congr ha hb)
  | _, _, _, .eventIdentificationLeft => fun _ _ hf _ _ hp ↦
      hρ.bind hf fun _ _ hF ↦ hρ.bind hp fun _ _ hP ↦ hρ.pure fun _ _ hx ↦
        hρ.bind (hF hx) fun _ _ hFx ↦ hρ.pure fun _ _ he ↦
          hρ.bind (hFx he) fun _ _ ha ↦ hρ.bind (hP he) fun _ _ hb ↦ hρ.pure (and_congr ha hb)
  | _, _, _, .eventIdentificationRight => fun _ _ hp _ _ hf ↦
      hρ.bind hp fun _ _ hP ↦ hρ.bind hf fun _ _ hF ↦ hρ.pure fun _ _ hx ↦
        hρ.bind (hF hx) fun _ _ hFx ↦ hρ.pure fun _ _ he ↦
          hρ.bind (hFx he) fun _ _ ha ↦ hρ.bind (hP he) fun _ _ hb ↦ hρ.pure (and_congr ha hb)
  | _, _, _, .mapRight m => fun _ _ ha _ _ hb ↦
      hρ.bind ha fun _ _ hav ↦ hρ.bind hb fun _ _ hbv ↦
        hρ.pure (Eff.LiftRel.map (Mode.rel_evalKleisli hρ m (hρ.pure hav)) hbv)
  | _, _, _, .mapLeft m => fun _ _ ha _ _ hb ↦
      hρ.bind ha fun _ _ hav ↦ hρ.bind hb fun _ _ hbv ↦
        hρ.pure (Eff.LiftRel.map (fun _ _ hx ↦ Mode.rel_evalKleisli hρ m hx (hρ.pure hbv)) hav)
  | _, _, _, .ap m => fun _ _ ha _ _ hb ↦
      hρ.bind ha fun _ _ hav ↦ hρ.bind hb fun _ _ hbv ↦
        hρ.pure (Eff.LiftRel.zip (Mode.rel_evalKleisli hρ m) hav hbv)
  | _, _, _, .unitRight m => fun _ _ ha _ _ hb ↦
      Mode.rel_evalKleisli hρ m (hρ.bind ha fun _ _ hav ↦ hρ.pure fun _ _ hx ↦
        hav (Eff.LiftRel.pure (hρ.pure hx))) hb
  | _, _, _, .unitLeft m => fun _ _ ha _ _ hb ↦
      Mode.rel_evalKleisli hρ m ha (hρ.bind hb fun _ _ hbv ↦ hρ.pure fun _ _ hx ↦
        hbv (Eff.LiftRel.pure (hρ.pure hx)))
  | _, _, _, .join m => fun _ _ ha _ _ hb ↦
      hρ.bind (Mode.rel_evalKleisli hρ m ha hb) fun _ _ hx ↦ hρ.pure (Eff.LiftRel.join hρ hx)

/-- Values are related by the relation itself. -/
theorem KleisliRelator.pure_pure :
    letI := pureMonad; letI := pureFlatten
    KleisliRelator (M := fun α ↦ α) (M' := fun α ↦ α) fun R ↦ R :=
  let _ := pureMonad
  let _ := pureFlatten
  ⟨id, fun h hf ↦ hf h, id⟩

/-- Every mode preserves the logical relation between values. -/
theorem Mode.rel_eval {σ₁ σ₂ τ : Ty} (m : Mode σ₁ σ₂ τ) :
    LiftFun (Ty.LiftRel (fun R ↦ R) r σ₁)
      (LiftFun (Ty.LiftRel (fun R ↦ R) r σ₂) (Ty.LiftRel (fun R ↦ R) r τ)) m.eval m.eval :=
  fun _ _ ha _ _ hb ↦ by
    let _ := pureMonad
    let _ := pureFlatten
    rw [← evalKleisli_pure, ← evalKleisli_pure]
    exact Mode.rel_evalKleisli KleisliRelator.pure_pure m ha hb

/-- The fundamental lemma of logical relations ([statman-1985]): a term has related values in two
models when its constants and the assignments are related. Which relations qualify is up to the
lexicon, since the engine preserves them all. -/
theorem Term.rel_eval {Γ : ℕ → Ty} {K : Ty → Type*}
    {I : ∀ {ty : Ty}, K ty → Ty.Domain E W ty S} {I' : ∀ {ty : Ty}, K ty → Ty.Domain E' W' ty S'}
    (hc : ∀ {ty : Ty} (c : K ty), Ty.LiftRel (fun R ↦ R) r ty (I c) (I' c))
    {g : ∀ n, Ty.Domain E W (Γ n) S} {g' : ∀ n, Ty.Domain E' W' (Γ n) S'}
    (hg : ∀ n, Ty.LiftRel (fun R ↦ R) r (Γ n) (g n) (g' n)) {ty : Ty} (t : Term Γ K ty) :
    Ty.LiftRel (fun R ↦ R) r ty (t.eval I g) (t.eval I' g') :=
  Term.rel_realize (A := .total I) (B := .total I') (fun ty ↦ Ty.LiftRel (fun R ↦ R) r ty)
    (fun ty ↦ Ty.LiftRel (fun R ↦ R) r ty)
    hc (fun _ _ h ↦ h) (fun _ _ h _ _ hx ↦ h _ _ hx) (fun m _ _ _ _ ha hb ↦ Mode.rel_eval m ha hb) t
    hg

/-- Abstraction under the set effect does not preserve the lifting. Along the map from `Bool` to a
point, the two families below are pointwise equal, yet the identity function, a choice from the
first, is related to no function from the point. So `Term.Rel.realize` takes preservation under
abstraction as a hypothesis, and the fundamental lemma above is for the total interpretation. -/
theorem Term.not_liftRel_distribute :
    ¬ Set.LiftRel (LiftFun (fun (_ : Bool) (_ : Unit) ↦ True) (· = ·))
      (distribute (M := SetM) fun _ : Bool ↦ (Set.univ : Set Bool)).run
      (distribute (M := SetM) fun _ : Unit ↦ (Set.univ : Set Bool)).run := by
  rintro ⟨h, -⟩
  obtain ⟨g, -, hg⟩ := h id (SetM.mem_run_distribute.2 fun _ ↦ Set.mem_univ _)
  exact Bool.noConfusion
    ((hg (a := true) (b := ()) trivial).trans (hg (a := false) (b := ()) trivial).symm)

end Montague
