module

public import Linglib.Core.ModelTheory.ManySorted.Semantics

/-!
# Simulation between many-sorted structures

One structure simulates another over the same domains when each function of the second is the
value of a term of the first over the argument places, a term operation. Then [every term of the
second has a term of the first with its
value](##MSFirstOrder.Language.Structure.Simulates.exists_term): the clone of term operations of
the second is included in that of the first.

## Main definitions

* `MSFirstOrder.Language.Structure.Simulates`: every function of one structure is a term operation
  of another.
-/

@[expose] public section

universe u v w x

namespace MSFirstOrder.Language.Structure

variable {S : Type u} {L L' L'' : Language.{u, v} S} {α : S → Type w} {D : S → Type x}

/-- `M'` simulates `M` when every function of `M` is the value in `M'` of a term over its
argument places. -/
structure Simulates (M' : L'.Structure D) (M : L.Structure D) : Prop where
  /-- Each function is a term operation. -/
  funMap {σ : Signature S} {t : S} (f : L.Functions σ t) :
    ∃ u : L'.Term σ.Place (.of t), ∀ args, u.realize M' (fun p ↦ p.val args) = M.funMap f args

namespace Simulates

variable {M : L.Structure D} {M' : L'.Structure D}

/-- A structure simulates itself. -/
protected theorem refl (M : L.Structure D) : Simulates M M where
  funMap {σ _} f := ⟨.func f (.places σ), fun args ↦
    congrArg (M.funMap f) (Term.realize_places M σ args)⟩

/-- Whatever term the simulated language has, the simulating one has a term with its value,
whatever the values of the variables. -/
theorem exists_term (h : Simulates M' M) {σ : Signature S} (t : L.Term α σ) :
    ∃ t' : L'.Term α σ, ∀ ρ : ∀ {s : S}, α s → D s, t'.realize M' ρ = t.realize M ρ := by
  induction t with
  | var x => exact ⟨.var x, fun _ ↦ rfl⟩
  | nil => exact ⟨.nil, fun _ ↦ rfl⟩
  | prod a b iha ihb =>
    obtain ⟨a', ha'⟩ := iha
    obtain ⟨b', hb'⟩ := ihb
    exact ⟨.prod a' b', fun ρ ↦ Prod.ext (ha' ρ) (hb' ρ)⟩
  | func f r ih =>
    obtain ⟨r', hr'⟩ := ih
    obtain ⟨u, hu⟩ := h.funMap f
    refine ⟨u.bind fun p ↦ Term.proj p r', fun ρ ↦ ?_⟩
    rw [Term.realize_bind, Term.realize, ← hr' ρ, ← hu]
    congr 1
    funext s p
    exact Term.realize_proj M' ρ r' p

/-- Simulation is transitive. -/
protected theorem trans {M'' : L''.Structure D} (h' : Simulates M'' M') (h : Simulates M' M) :
    Simulates M'' M where
  funMap f := by
    obtain ⟨t, ht⟩ := h.funMap f
    obtain ⟨t', ht'⟩ := h'.exists_term t
    exact ⟨t', fun args ↦ (ht' _).trans (ht args)⟩

end Simulates

end MSFirstOrder.Language.Structure
