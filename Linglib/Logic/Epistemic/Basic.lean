module

public import Linglib.Logic.Modal.Basic
public import Mathlib.Data.Fintype.Option

/-!
# The language of knowledge and belief

This file defines the propositional language of knowledge and belief, with operators for what each
agent knows and believes and their duals, and its possible-worlds semantics. A model has, for each
agent, an epistemic and a doxastic alternativeness relation, the doxastic alternatives among the
epistemic ones, and knowing and believing are necessity along them, the box `ModalLogic.Box` of
the attitude semantics in `Semantics/Attitudes/Doxastic.lean`.

## Main definitions

* `EpistemicLogic.Formula`: the formulas in atoms `V` with agents `A`.
* `EpistemicLogic.Model`: a model with reflexive epistemic and serial doxastic alternativeness.
* `EpistemicLogic.Model.Sat`: satisfaction of a formula at a world.
* `EpistemicLogic.Model.withPredecessor`: a model with a new world placed before a given one.

## Main results

* `EpistemicLogic.Model.sat_withPredecessor`: the old worlds satisfy what they satisfied.

## Implementation notes

The frame conditions every model shares are fields. Transitivity, the condition Hintikka trades
for his (C.KK*) and (C.BB*), is left to `SetRel.IsTrans` instances, so that a result which does
not need it is stated without it.

## References

* [hintikka-1962]
* [blackburn-derijke-venema-2001] — generated submodels
-/

@[expose] public section

namespace EpistemicLogic

open ModalLogic SetRel

/-- The formulas of the language of knowledge and belief: atomic sentences, negation,
conjunction, disjunction and the epistemic operators `K a` ("a knows that"), `P a` ("it is
possible, for all that a knows, that"), `B a` ("a believes that") and `C a` ("it is compatible
with everything a believes that"). -/
inductive Formula (V A : Type*)
  | atom : V → Formula V A
  | neg : Formula V A → Formula V A
  | and : Formula V A → Formula V A → Formula V A
  | or : Formula V A → Formula V A → Formula V A
  | K : A → Formula V A → Formula V A
  | P : A → Formula V A → Formula V A
  | B : A → Formula V A → Formula V A
  | C : A → Formula V A → Formula V A
  deriving DecidableEq

namespace Formula

variable {V A : Type*}

/-- Negation. -/
scoped notation:max "∼" p:66 => Formula.neg p
/-- Conjunction. -/
scoped infixl:65 " ⋏ " => Formula.and
/-- Disjunction. -/
scoped infixl:60 " ⋎ " => Formula.or

/-- Material implication, eliminated in terms of the other connectives. -/
def imp (p q : Formula V A) : Formula V A := ∼(p ⋏ ∼q)

@[inherit_doc] scoped infixr:55 " ⟹ " => Formula.imp

/-- *a knows whether p*: `a` knows that `p` or knows that not `p`. -/
def knowsWhether (a : A) (p : Formula V A) : Formula V A := K a p ⋎ K a ∼p

/-- *a does not know whether p*: `a` knows neither that `p` nor that not `p`. -/
def notKnowsWhether (a : A) (p : Formula V A) : Formula V A := ∼K a p ⋏ ∼K a ∼p

end Formula

open Formula

variable {V A : Type*}

/-- A possible-worlds model of the epistemic language. -/
structure Model (V A W : Type*) where
  /-- Epistemic alternativeness. -/
  epi : A → SetRel W W
  /-- Doxastic alternativeness. -/
  dox : A → SetRel W W
  /-- Valuation of the atomic sentences. -/
  val : V → W → Prop
  /-- Whatever is known is true. -/
  epi_refl : ∀ a, (epi a).IsRefl
  /-- Some state of affairs is compatible with what each agent believes. -/
  dox_serial : ∀ a, IsSerial (dox a)
  /-- Doxastic alternatives are epistemic alternatives: what is known is believed. -/
  dox_le_epi : ∀ a, dox a ⊆ epi a

namespace Model

variable {W : Type*} (M : Model V A W)

/-- Satisfaction: the epistemic operators are `box` and `diamond` over the agent's
alternativeness. -/
def Sat : Formula V A → W → Prop
  | .atom v, w => M.val v w
  | .neg p, w => ¬ Sat p w
  | .and p q, w => Sat p w ∧ Sat q w
  | .or p q, w => Sat p w ∨ Sat q w
  | .K a p, w => □[M.epi a] (Sat p) w
  | .P a p, w => ◇[M.epi a] (Sat p) w
  | .B a p, w => □[M.dox a] (Sat p) w
  | .C a p, w => ◇[M.dox a] (Sat p) w

/-- The formulas true at a world. -/
def truthSet (w : W) : Set (Formula V A) := {p | M.Sat p w}

/-! ### Decidability over finitely many worlds -/

section Decidable

variable [Fintype W] [∀ a w v, Decidable (w ~[M.epi a] v)] [∀ a w v, Decidable (w ~[M.dox a] v)]
  [∀ v, DecidablePred (M.val v)]

/-- Satisfaction is decidable over finitely many worlds. -/
def decSat : ∀ (p : Formula V A) (w : W), Decidable (M.Sat p w)
  | .atom v, w => inferInstanceAs (Decidable (M.val v w))
  | .neg p, w => @instDecidableNot _ (decSat p w)
  | .and p q, w => @instDecidableAnd _ _ (decSat p w) (decSat q w)
  | .or p q, w => @instDecidableOr _ _ (decSat p w) (decSat q w)
  | .K a p, w => haveI := decSat p; inferInstanceAs (Decidable (□[M.epi a] (M.Sat p) w))
  | .P a p, w => haveI := decSat p; inferInstanceAs (Decidable (◇[M.epi a] (M.Sat p) w))
  | .B a p, w => haveI := decSat p; inferInstanceAs (Decidable (□[M.dox a] (M.Sat p) w))
  | .C a p, w => haveI := decSat p; inferInstanceAs (Decidable (◇[M.dox a] (M.Sat p) w))

instance (p : Formula V A) (w : W) : Decidable (M.Sat p w) := M.decSat p w

instance (p : Formula V A) (w : W) : Decidable (p ∈ M.truthSet w) := M.decSat p w

end Decidable

/-! ### A world before a world

A model with a new world whose alternatives are those of a given world `w₀` together with `w₀`
itself evaluates every formula at the old worlds as before, since no old world sees the new one;
the new world does not believe what fails at `w₀`. -/

/-- `M` with a new world placed before `w₀`: its epistemic alternatives are itself and those of
`w₀`, and its doxastic alternatives `w₀` and those of `w₀`. -/
def withPredecessor (w₀ : W) : Model V A (Option W) where
  epi a := {(x, y) | match x, y with
    | some w, some v => w ~[M.epi a] v
    | none, some v => w₀ ~[M.epi a] v
    | none, none => True
    | some _, none => False}
  dox a := {(x, y) | match x, y with
    | some w, some v => w ~[M.dox a] v
    | none, some v => v = w₀ ∨ w₀ ~[M.dox a] v
    | _, none => False}
  val v x := x.elim False (M.val v)
  epi_refl a := ⟨fun
    | none => trivial
    | some w => (M.epi_refl a).refl w⟩
  dox_serial a := ⟨fun
    | none => ⟨some w₀, Or.inl rfl⟩
    | some w => let ⟨v, hv⟩ := (M.dox_serial a).serial w; ⟨some v, hv⟩⟩
  dox_le_epi a := by
    rintro ⟨_ | w, _ | v⟩ h
    · exact False.elim h
    · exact Or.elim h (fun h ↦ h ▸ (M.epi_refl a).refl w₀) fun h ↦ M.dox_le_epi a h
    · exact False.elim h
    · exact M.dox_le_epi a h

variable (w₀ : W)

instance [∀ a, (M.epi a).IsTrans] (a : A) : ((M.withPredecessor w₀).epi a).IsTrans := ⟨by
  rintro (_ | x) (_ | y) (_ | z) hxy hyz
  exacts [trivial, hyz, False.elim hyz, (M.epi a).trans hxy hyz, False.elim hxy, False.elim hxy,
    False.elim hyz, (M.epi a).trans hxy hyz]⟩

instance [∀ a, (M.dox a).IsTrans] (a : A) : ((M.withPredecessor w₀).dox a).IsTrans := ⟨by
  rintro (_ | x) (_ | y) (_ | z) hxy hyz
  exacts [False.elim hxy, False.elim hxy, False.elim hyz,
    Or.inr (Or.elim hxy (fun h ↦ h ▸ hyz) fun h ↦ (M.dox a).trans h hyz), False.elim hxy,
    False.elim hxy, False.elim hyz, (M.dox a).trans hxy hyz]⟩

theorem sat_withPredecessor (p : Formula V A) (w : W) :
    (M.withPredecessor w₀).Sat p (some w) ↔ M.Sat p w := by
  induction p generalizing w with
  | atom v => rfl
  | neg p ih => exact not_congr (ih w)
  | and p q ihp ihq => exact and_congr (ihp w) (ihq w)
  | or p q ihp ihq => exact or_congr (ihp w) (ihq w)
  | K a p ih | B a p ih =>
    exact ⟨fun h v hv ↦ (ih v).1 (h (some v) hv), fun h ↦ fun
      | some v, hv => (ih v).2 (h v hv)
      | none, hv => False.elim hv⟩
  | P a p ih | C a p ih =>
    exact ⟨fun
      | ⟨some v, hv, hp⟩ => ⟨v, hv, (ih v).1 hp⟩
      | ⟨none, hv, _⟩ => False.elim hv, fun ⟨v, hv, hp⟩ ↦ ⟨some v, hv, (ih v).2 hp⟩⟩

theorem sat_withPredecessor_none_neg_B {a : A} {p : Formula V A} (h : ¬ M.Sat p w₀) :
    (M.withPredecessor w₀).Sat (∼B a p) none :=
  fun hB ↦ h ((M.sat_withPredecessor w₀ p w₀).1 (hB (some w₀) (Or.inl rfl)))

end Model

end EpistemicLogic
