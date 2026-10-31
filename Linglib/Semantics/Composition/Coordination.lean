module

public import Linglib.Semantics.Composition.Coordinator
public import Linglib.Semantics.Composition.Mode

/-!
# Coordination in the composition engine

A coordinator is a word of every conjoinable type, a type that ends in $t$: at such a type
$\tau$ it denotes $\lambda q\,\lambda p.\ c\{p, q\}$, of type
$\langle\tau,\langle\tau,\tau\rangle\rangle$, in the pointwise Boolean algebra of $\tau$, so that
*and* conjoins truth values, predicates and quantifiers alike. Coordination therefore needs no
composition mode of its own: [functional application composes $[X\ [c\ Y]]$ to
$c\{X, Y\}$](##combine?_reading), and predicate modification [is the conjunctive reading at
$\langle e,t\rangle$](##combine?_predicateModification_eq_reading).

## Main definitions

* `Coordinator.reading`: a coordinator's denotation at a conjoinable type.
* `Coordinator.readings`: its denotations at every conjoinable type.

## References

* [heim-kratzer-1998]
* [partee-rooth-1983]
-/

@[expose] public section

namespace Coordinator

open Montague

variable {E W : Type} {M : Type → Type} [Applicative M]

/-- A coordinator at a conjoinable type $\tau$ denotes $\lambda q\,\lambda p.\ c\{p, q\}$, of type
$\langle\tau,\langle\tau,\tau\rangle\rangle$, taking its right coordinand first, as in
$[X\ [c\ Y]]$. -/
def reading (c : Coordinator) (τ : Ty) (h : τ.Conjoinable) : Denotation E W M :=
  ⟨τ ⇒ τ ⇒ τ, pure fun q p ↦ letI := Ty.Domain.completeBooleanAlgebra E W τ h; c.denote {p, q}⟩

/-- A coordinator's readings are its denotations at every conjoinable type. -/
def readings (c : Coordinator) : Set (Denotation E W M) :=
  Set.range fun τ : {τ : Ty // τ.Conjoinable} ↦ c.reading τ τ.2

/-- A conjunctive coordinator's reading is the meet of its coordinands. -/
theorem reading_of_conjunctive {c : Coordinator} (hc : c.role = .conjunctive) {τ : Ty}
    (h : τ.Conjoinable) : (c.reading τ h : Denotation E W M) =
      ⟨τ ⇒ τ ⇒ τ, pure fun q p ↦ letI := Ty.Domain.completeBooleanAlgebra E W τ h; p ⊓ q⟩ := by
  unfold reading
  congr 2
  funext q p
  let := Ty.Domain.completeBooleanAlgebra E W τ h
  exact (denote_of_conjunctive hc _).trans sInf_pair

/-- A disjunctive coordinator's reading is the join of its coordinands. -/
theorem reading_of_disjunctive {c : Coordinator} (hc : c.role = .disjunctive) {τ : Ty}
    (h : τ.Conjoinable) : (c.reading τ h : Denotation E W M) =
      ⟨τ ⇒ τ ⇒ τ, pure fun q p ↦ letI := Ty.Domain.completeBooleanAlgebra E W τ h; p ⊔ q⟩ := by
  unfold reading
  congr 2
  funext q p
  let := Ty.Domain.completeBooleanAlgebra E W τ h
  exact (denote_of_disjunctive hc _).trans sSup_pair

variable [LawfulApplicative M]

/-- Functional application composes `[X [c Y]]` to the coordination of `X` and `Y`. -/
theorem combine?_reading (c : Coordinator) {τ : Ty} (h : τ.Conjoinable)
    (x y : M (Ty.Domain E W τ)) :
    ((Mode.combine? Mode.evalM (c.reading τ h) ⟨τ, y⟩).bind fun d ↦
        Mode.combine? Mode.evalM ⟨τ, x⟩ d) =
      some ⟨τ, (fun p q ↦ letI := Ty.Domain.completeBooleanAlgebra E W τ h; c.denote {p, q}) <$>
        x <*> y⟩ := by
  simp only [reading, Mode.combine?_fn_left, Option.bind_some, Mode.combine?_fn_right,
    Mode.evalM, map_pure, pure_seq, seq_map_assoc, Functor.map_map]
  rfl

/-- Predicate modification is the conjunctive reading at `⟨e,t⟩`. -/
theorem combine?_predicateModification_eq_reading {c : Coordinator} (hc : c.role = .conjunctive)
    (x y : M (Ty.Domain E W (.e ⇒ .t))) :
    Mode.combine? Mode.evalM ⟨.e ⇒ .t, x⟩ ⟨.e ⇒ .t, y⟩ =
      (Mode.combine? Mode.evalM (c.reading (.e ⇒ .t) trivial) ⟨.e ⇒ .t, y⟩).bind fun d ↦
        Mode.combine? Mode.evalM ⟨.e ⇒ .t, x⟩ d := by
  rw [combine?_reading, Mode.combine?_predicateModification]
  have h : (Modifier.intersective : Ty.Domain E W (.e ⇒ .t) → _) = fun p q ↦
      letI := Ty.Domain.completeBooleanAlgebra E W (.e ⇒ .t) trivial; c.denote {p, q} := by
    funext p q; simp [Modifier.intersective, Coordinator.denote_of_conjunctive hc]
  exact congrArg (fun F ↦ some (⟨.e ⇒ .t, F <$> x <*> y⟩ : Denotation E W M)) h

end Coordinator
