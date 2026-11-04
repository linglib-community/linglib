module

public import Linglib.Core.Data.Set.Functor
public import Linglib.Semantics.Composition.Term

/-!
# Logical relations on the semantic types

Relations on the entities, worlds, degrees and eventualities of two models [lift to every semantic
type](##Ty.LiftRel): functions are related when they send related arguments to related values,
propositions when they are equivalent, and sets of alternatives when each alternative in either
has a related alternative in the other. [Every mode preserves the lifted relation](##Mode.rel_eval),
so [terms with related constants and assignments have related values](##Term.rel_eval), and at type
$t$ a sentence holds in one model exactly when it holds in the other. Abstraction under the set
effect [does not preserve the relation](##Term.not_liftRel_distribute).

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

variable {E E' W W' : Type} {S S' : Sorts}

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

/-- The environment of an effect: the reader reads a value of its type, and indeterminacy reads
nothing. -/
abbrev Eff.Env (E W : Type) (f : Eff) (S : Sorts := {}) : Type :=
  match f with
  | .reader ι => Ty.Domain E W ι S
  | .set => PUnit

/-- The lifting of a relation on results to an effect's carrier, given a relation on its
environments. Readers are related when related environments give related results. Sets of
alternatives lift by `Set.LiftRel`. -/
abbrev Eff.LiftRel {α β : Type} : (f : Eff) → (Eff.Env E W f S → Eff.Env E' W' f S' → Prop) →
    (α → β → Prop) → Eff.F E W f S α → Eff.F E' W' f S' β → Prop
  | .reader _, ρ, R => LiftFun ρ R
  | .set, _, R => Set.LiftRel R

mutual

/-- The logical relation at each semantic type, [quigley-2026]'s induced relation when the base
relations are the graphs of maps. A predicate and a set of alternatives share a carrier but
lift differently: along the graph of a map, a predicate is related to those it is the preimage of,
and a set of alternatives to its image. -/
abbrev Ty.LiftRel (r : Ty.BaseRel E E' W W' S S') :
    (ty : Ty) → Ty.Domain E W ty S → Ty.Domain E' W' ty S' → Prop
  | .e => r.e
  | .t => Iff
  | .d => r.d
  | .n => Eq
  | .v => r.v
  | .s => r.s
  | .fn a b => LiftFun (Ty.LiftRel r a) (Ty.LiftRel r b)
  | .comp f a => Eff.LiftRel f (Eff.EnvRel r f) (Ty.LiftRel r a)

/-- The logical relation on the environment of an effect. -/
abbrev Eff.EnvRel (r : Ty.BaseRel E E' W W' S S') :
    (f : Eff) → Eff.Env E W f S → Eff.Env E' W' f S' → Prop
  | .reader ι => Ty.LiftRel r ι
  | .set => fun _ _ ↦ True

end

namespace Eff.LiftRel

variable {f : Eff} {ρ : Eff.Env E W f S → Eff.Env E' W' f S' → Prop} {α β γ δ : Type}
  {R : α → β → Prop} {Q : γ → δ → Prop} {x : Eff.F E W f S α} {x' : Eff.F E' W' f S' β}

protected theorem map {g : α → γ} {g' : β → δ} (hg : LiftFun R Q g g')
    (h : Eff.LiftRel f ρ R x x') : Eff.LiftRel f ρ Q (Eff.map f g x) (Eff.map f g' x') := by
  cases f with
  | reader _ => exact fun _ _ hi ↦ hg (h hi)
  | set => exact Set.LiftRel.image h hg

protected theorem pure {a : α} {b : β} (h : R a b) :
    Eff.LiftRel f ρ R (Eff.pure f a) (Eff.pure f b) := by
  cases f with
  | reader _ => exact fun _ _ _ ↦ h
  | set => exact Set.liftRel_singleton.2 h

protected theorem seq {g : Eff.F E W f S (α → γ)} {g' : Eff.F E' W' f S' (β → δ)}
    (hg : Eff.LiftRel f ρ (LiftFun R Q) g g') (h : Eff.LiftRel f ρ R x x') :
    Eff.LiftRel f ρ Q (Eff.seq f g x) (Eff.seq f g' x') := by
  cases f with
  | reader _ => exact fun _ _ hi ↦ hg hi (h hi)
  | set => exact Set.LiftRel.seq hg h

protected theorem join {y : Eff.F E W f S (Eff.F E W f S α)}
    {y' : Eff.F E' W' f S' (Eff.F E' W' f S' β)}
    (h : Eff.LiftRel f ρ (Eff.LiftRel f ρ R) y y') :
    Eff.LiftRel f ρ R (Eff.join f y) (Eff.join f y') := by
  cases f with
  | reader _ => exact fun _ _ hi ↦ h hi hi
  | set => exact Set.LiftRel.sUnion h

end Eff.LiftRel

variable {r : Ty.BaseRel E E' W W' S S'}

/-- Every mode preserves the logical relation: the engine's ways of composing two daughters depend
on nothing about a model beyond their values. -/
theorem Mode.rel_eval : ∀ {σ₁ σ₂ τ : Ty} (m : Mode σ₁ σ₂ τ),
    LiftFun (σ₁.LiftRel r) (LiftFun (σ₂.LiftRel r) (τ.LiftRel r)) m.eval m.eval
  | _, _, _, .functionalLeft => fun _ _ hf _ _ ha ↦ hf ha
  | _, _, _, .functionalRight => fun _ _ ha _ _ hf ↦ hf ha
  | _, _, _, .predicateModification => fun _ _ hp _ _ hq _ _ hx ↦ and_congr (hp hx) (hq hx)
  | _, _, _, .eventIdentificationLeft => fun _ _ hf _ _ hp _ _ hx _ _ he ↦
      and_congr (hf hx he) (hp he)
  | _, _, _, .eventIdentificationRight => fun _ _ hp _ _ hf _ _ hx _ _ he ↦
      and_congr (hf hx he) (hp he)
  | _, _, _, .mapRight m => fun _ _ ha _ _ hb ↦ Eff.LiftRel.map (Mode.rel_eval m ha) hb
  | _, _, _, .mapLeft m => fun _ _ ha _ _ hb ↦
      Eff.LiftRel.map (fun _ _ hx ↦ Mode.rel_eval m hx hb) ha
  | _, _, _, .ap m => fun _ _ ha _ _ hb ↦ Eff.LiftRel.seq (Eff.LiftRel.map (Mode.rel_eval m) ha) hb
  | _, _, _, .unitRight m => fun _ _ ha _ _ hb ↦
      Mode.rel_eval m (fun _ _ hx ↦ ha (Eff.LiftRel.pure hx)) hb
  | _, _, _, .unitLeft m => fun _ _ ha _ _ hb ↦
      Mode.rel_eval m ha fun _ _ hy ↦ hb (Eff.LiftRel.pure hy)
  | _, _, _, .join m => fun _ _ ha _ _ hb ↦ Eff.LiftRel.join (Mode.rel_eval m ha hb)

/-- The fundamental lemma of logical relations ([statman-1985]): a term has related values in two
models when its constants and the assignments are related. Which relations qualify is up to the
lexicon, since the engine preserves them all. -/
theorem Term.rel_eval {Γ : ℕ → Ty} {K : Ty → Type*}
    {I : ∀ {ty : Ty}, K ty → Ty.Domain E W ty S} {I' : ∀ {ty : Ty}, K ty → Ty.Domain E' W' ty S'}
    (hc : ∀ {ty : Ty} (c : K ty), ty.LiftRel r (I c) (I' c))
    {g : ∀ n, Ty.Domain E W (Γ n) S} {g' : ∀ n, Ty.Domain E' W' (Γ n) S'}
    (hg : ∀ n, (Γ n).LiftRel r (g n) (g' n)) {ty : Ty} (t : Term Γ K ty) :
    ty.LiftRel r (t.eval I g) (t.eval I' g') :=
  Term.rel_realize (A := .total I) (B := .total I') (fun ty ↦ ty.LiftRel r) (fun ty ↦ ty.LiftRel r)
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
