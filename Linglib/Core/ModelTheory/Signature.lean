module

public import Mathlib.Logic.Function.Basic
public import Mathlib.Data.List.Basic

/-!
# Many-sorted signatures

A many-sorted signature has operation symbols typed by the sorts of their arguments and the sort
of their result. Its terms over sorted variables are the well-sorted trees of operations, a
structure gives each symbol an operation on a family of domains, and a term then has a value. One
structure simulates another over the same domains when each operation of the second is the value
of a term of the first, and then [every term of the second has a term of the first with its
value](##Signature.Structure.Simulates.exists_term): the clone of the second is included in that
of the first.

## Main definitions

* `Signature`: operation symbols by the sorts of their arguments and result.
* `Signature.Term`: the terms over sorted variables.
* `Signature.Structure`: an operation for each symbol, over a family of domains.
* `Signature.Term.realize`: the value of a term.
* `Signature.Structure.Simulates`: every operation of one structure is a term operation of
  another.

## Implementation notes

The definitions follow `FirstOrder.Language`, its terms and its structures, with a sort for each
argument place and for the result where a first-order language has an arity. The domains are a
parameter of a structure, as the carrier is there. A term operation is a term whose variables are
the argument places, `Signature.Place`; it may use a place more than once or not at all.
-/

@[expose] public section

universe u v w

/-- A many-sorted signature over sorts `S`: the operation symbols with arguments of given sorts
and a result of a given sort. -/
structure Signature (S : Type u) where
  /-- The operation symbols with arguments of sorts `ss` and result of sort `s`. -/
  Op : List S → S → Type v

namespace Signature

variable {S : Type u} {σ σ' : Signature.{u, v} S} {X Y : S → Type w} {D : S → Type w}

/-- The terms over variables `X`. -/
inductive Term (σ : Signature.{u, v} S) (X : S → Type w) : S → Type (max u v w)
  /-- A variable. -/
  | var {s : S} (x : X s) : Term σ X s
  /-- An operation applied to terms of its argument sorts. -/
  | op {ss : List S} {s : S} (f : σ.Op ss s) (args : ∀ i : Fin ss.length, Term σ X (ss.get i)) :
      Term σ X s

namespace Term

/-- Substitution of terms for the variables. -/
def bind : {s : S} → Term σ X s → (∀ {r : S}, X r → Term σ Y r) → Term σ Y s
  | _, var x, θ => θ x
  | _, op f args, θ => op f fun i ↦ (args i).bind θ

end Term

/-- A structure for a signature over the domains `D`: an operation for each symbol. -/
structure Structure (σ : Signature.{u, v} S) (D : S → Type w) where
  /-- The operation of a symbol. -/
  op {ss : List S} {s : S} : σ.Op ss s → (∀ i : Fin ss.length, D (ss.get i)) → D s

namespace Term

/-- The value of a term in a structure, given the values of its variables. -/
def realize (M : Structure σ D) (ρ : ∀ {s : S}, X s → D s) : {s : S} → Term σ X s → D s
  | _, var x => ρ x
  | _, op f args => M.op f fun i ↦ (args i).realize M ρ

theorem realize_bind (M : Structure σ D) (ρ : ∀ {s : S}, Y s → D s) {s : S} (t : Term σ X s)
    (θ : ∀ {r : S}, X r → Term σ Y r) :
    (t.bind θ).realize M ρ = t.realize M fun x ↦ (θ x).realize M ρ := by
  induction t with
  | var x => rfl
  | op f args ih => simp only [bind, realize, ih]

end Term

/-- The argument places of sort `s` among arguments of sorts `ss`. -/
def Place (ss : List S) (s : S) : Type := {i : Fin ss.length // ss.get i = s}

/-- The values of the argument places, from the arguments. -/
def Place.val {ss : List S} (args : ∀ i : Fin ss.length, D (ss.get i)) {s : S} (p : Place ss s) :
    D s :=
  p.2 ▸ args p.1

namespace Structure

/-- `M'` simulates `M` when every operation of `M` is the value in `M'` of a term over its
argument places. -/
structure Simulates (M' : Structure σ' D) (M : Structure σ D) : Prop where
  /-- Each operation is a term operation. -/
  op {ss : List S} {s : S} (f : σ.Op ss s) :
    ∃ t : Term σ' (fun r ↦ ULift.{w} (Place ss r)) s,
      ∀ args, t.realize M' (fun p ↦ p.down.val args) = M.op f args

namespace Simulates

variable {M : Structure σ D} {M' : Structure σ' D}

/-- A structure simulates itself. -/
protected theorem refl (M : Structure σ D) : Simulates M M where
  op f := ⟨.op f fun i ↦ .var ⟨⟨i, rfl⟩⟩, fun _ ↦ rfl⟩

/-- Whatever term the simulated signature has, the simulating one has a term with its value,
whatever the values of the variables. -/
theorem exists_term (h : Simulates M' M) {s : S} (t : Term σ X s) :
    ∃ t' : Term σ' X s, ∀ ρ : ∀ {s : S}, X s → D s, t'.realize M' ρ = t.realize M ρ := by
  induction t with
  | var x => exact ⟨.var x, fun _ ↦ rfl⟩
  | @op ss s f args ih =>
    choose args' hargs' using ih
    obtain ⟨u, hu⟩ := h.op f
    refine ⟨u.bind fun p ↦ p.down.2 ▸ args' p.down.1, fun ρ ↦ ?_⟩
    rw [Term.realize_bind, Term.realize, ← hu]
    congr 1
    funext r p
    obtain ⟨⟨i, rfl⟩⟩ := p
    exact hargs' i ρ

/-- Simulation is transitive. -/
protected theorem trans {σ'' : Signature.{u, v} S} {M'' : Structure σ'' D}
    (h' : Simulates M'' M') (h : Simulates M' M) : Simulates M'' M where
  op f := by
    obtain ⟨t, ht⟩ := h.op f
    obtain ⟨t', ht'⟩ := h'.exists_term t
    exact ⟨t', fun args ↦ (ht' _).trans (ht args)⟩

end Simulates

end Structure

end Signature
