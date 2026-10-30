module

public import Mathlib.Data.Set.Functor
public import Mathlib.Data.Set.Card
public import Linglib.Core.Data.Set.Monad
public import Linglib.Semantics.Composition.WithAlternatives
public import Linglib.Semantics.Focus.Particles
public import Mathlib.Control.Monad.Cont
public import Linglib.Semantics.Reference.ChoiceFunction
public import Linglib.Data.Examples.Charlow2014

/-!
# Charlow (2014): On the semantics of exceptional scope

A dynamic program is a computation in `StateT (Stack E) Set`, from an input stack of discourse
referents to a set of values paired with output stacks. A scope-taker is a continuation over such
programs, with Lift `monadLift`, Lower `lower` and Reset `reset`. A scope island is a constituent
that must be evaluated, and Reset discharges quantifiers but keeps nondeterminism and discourse
referents, so indefinites, disjunctions, the referents of proper names and the maximal referents
of dynamic quantifiers take scope out of islands and bind pronouns outside them, while *every*
and *no* do not.

## Main definitions

* `combine`: monadic application.
* `StateSet`: the State.Set monad.
* `Tower`: a scope-taker over State.Set programs.
* `lower`, `reset`: Lower and Reset.

## Implementation notes

* A pronoun on the empty stack has no value in the thesis; here `pro` has no output there. A
  negation over an unbound pronoun is then true, and Facts 3.3 and 4.7 (`neg_pro`,
  `reset_every_pro`) need a nonempty stack.
* The thesis excludes the empty plurality and treats an empty reference set as a presupposition
  failure; `Set A` admits it. The stack holds pluralities `Set A` and quantifiers range over
  atoms, where the thesis identifies an atom with its singleton.
* The choice-function theorems assume that distinct values of the bound variable give distinct
  restrictors, which the thesis states for (4.37) and leaves implicit for (4.35) and (4.38).

## TODO

* Relative-clause islands (`Examples.ex4_2a`), the layered Binder Roof datum (`Examples.ex4_6`),
  donkey disjunction (`Examples.ex4_25b`), the restrictor referents of dynamic quantifiers
  (`Examples.ex5_22`), and selective association with focus across islands.
* Tripartite towers for determiners, and a polymorphic Bind for sloppy readings.
* Evaluation enforced at islands by the grammar, which makes an island the sister of `fin`; here
  `reset` is placed by hand.
* The comparison with Independence-Friendly Logic (§4.7.2).

## References

* [charlow-2014]
* [dekker-1994]
* [liang-hudak-jones-1995]
* [wadler-1994]
* [danvy-filinski-1990]
* [rooth-partee-1982]
* [rooth-1985]
* [brasoveanu-farkas-2011]
* [schwarz-2001]
* [geurts-2000]
* [shan-2002]
* [shan-2004]
* [kratzer-shimoyama-2002]
* [barker-shan-2014]
-/

@[expose] public section

attribute [local instance] Set.monad

namespace Charlow2014

universe u

/-! ### Monadic application and Rebracket -/

section Monadic

variable {M : Type u → Type u} [Monad M] [LawfulMonad M] {α β γ δ : Type u}

/-- `combine f m n` runs `m`, then `n`, and combines their values by `f`, the thesis's `A`, with
forward application `combine (· ·)` and backward `combine (fun x f ↦ f x)`. -/
def combine (f : α → β → γ) (m : M α) (n : M β) : M γ :=
  m >>= fun x ↦ n >>= fun y ↦ pure (f x y)

theorem combine_eq_seq (f : α → β → γ) (m : M α) (n : M β) :
    combine f m n = f <$> m <*> n := by
  simp only [combine, seq_eq_bind_map, ← bind_pure_comp, bind_assoc, pure_bind]

theorem combine_bind (f : α → β → γ) (m : M α) (n : M β) (k : γ → M δ) :
    combine f m n >>= k = m >>= fun x ↦ n >>= fun y ↦ k (f x y) := by
  simp [combine, bind_assoc]

theorem combine_pure_left (f : α → β → γ) (a : α) (n : M β) :
    combine f (pure a) n = f a <$> n := by
  simp [combine, ← bind_pure_comp]

theorem combine_pure_right (f : α → β → γ) (m : M α) (b : β) :
    combine f m (pure b) = (f · b) <$> m := by
  simp [combine, ← bind_pure_comp]

end Monadic

/-! ### Lower and Reset -/

section Lower

variable {M : Type u → Type u} {ρ ρ' : Type u}

/-- Monadic Lower runs a tower at `pure`, the trivial continuation of the underlying monad
(Def. 3.13). -/
def lower [Pure M] (c : ContT ρ M ρ) : M ρ := c.run pure

/-- Reset is Lower followed by Lift (Def. 3.14), the reset of Danvy and Filinski. -/
def reset [Monad M] (c : ContT ρ M ρ) : ContT ρ' M ρ := monadLift (lower c)

/-- `liftValue a` lifts the trivial program `pure a` (Def. 2.9 with Lift), which makes it the
Montague lift `pure a` of the tower (3.20, `liftValue_eq_pure`). -/
def liftValue [Monad M] {α : Type u} (a : α) : ContT ρ M α := monadLift (pure a : M α)

@[simp] theorem run_liftValue [Monad M] [LawfulMonad M] {α : Type u} (a : α) (k : α → M ρ) :
    (liftValue a : ContT ρ M α).run k = k a := by
  simp [liftValue]

theorem liftValue_eq_pure [Monad M] [LawfulMonad M] {α : Type u} (a : α) :
    (liftValue a : ContT ρ M α) = pure a := by
  ext k; simp

end Lower

/-! ### Truth values as propositions -/

section TruthValues

theorem forall_iff_imp {q : Prop} {P : Prop → Prop} : (∀ p, (p ↔ q) → P p) ↔ P q :=
  ⟨fun h ↦ h q Iff.rfl, fun h _ hp ↦ (propext hp).symm ▸ h⟩

theorem exists_iff_and {q : Prop} {P : Prop → Prop} : (∃ p, (p ↔ q) ∧ P p) ↔ P q :=
  ⟨fun ⟨_, hp, h⟩ ↦ propext hp ▸ h, fun h ↦ ⟨q, Iff.rfl, h⟩⟩

end TruthValues

attribute [local simp] forall_iff_imp exists_iff_and

/-! ### The monads of Chapter 2

Application in each monad (Facts 2.2–2.5, 2.8, 2.11): functional application,
state-sensitive (`SSA`), nondeterministic (`NA`), state-sensitive
nondeterministic (`SSNA`, the rule of [kratzer-shimoyama-2002]), stateful, and
stateful nondeterministic application. -/

section Instances

variable {σ α β : Type}

theorem combine_id (f : α → β → σ) (m : Id α) (n : Id β) : combine f m n = f m n := rfl

theorem combine_readerT (f : α → β → σ) (m : ReaderT σ Id α) (n : ReaderT σ Id β) :
    combine f m n = fun s ↦ f (m s) (n s) := rfl

theorem combine_set (f : α → β → σ) (m : Set α) (n : Set β) :
    combine f m n = {c | ∃ x ∈ m, ∃ y ∈ n, c = f x y} := by
  ext; simp [combine, Set.bind_def]

theorem combine_readerT_set (f : α → β → σ) (m : ReaderT σ Set α) (n : ReaderT σ Set β) :
    combine f m n = fun s ↦ {c | ∃ x ∈ m s, ∃ y ∈ n s, c = f x y} := by
  funext s; ext; simp [combine]

theorem combine_stateT (f : α → β → σ) (m : StateT σ Id α) (n : StateT σ Id β) :
    combine f m n = fun s ↦ ((f (m s).1 (n (m s).2).1), (n (m s).2).2) := rfl

theorem combine_stateT_set (f : α → β → σ) (m : StateT σ Set α) (n : StateT σ Set β) :
    combine f m n = fun s ↦ {c | ∃ x ∈ m s, ∃ y ∈ n x.2, c = (f x.1 y.1, y.2)} := by
  funext s; ext; simp [combine]

end Instances

/-! ### Stacks and the State.Set monad (Facts 2.12, 2.13)

Discourse referents live on a stack; pronouns retrieve the most recent one
(`List.getLast?`). A sentence denotes a `StateSet E Prop`: from an input stack
to a set of value–output-stack pairs. -/

/-- The reference stack lists drefs in order of introduction. -/
abbrev Stack (E : Type) := List E

/-- The State.Set monad is `StateT` over the `Set` monad. -/
abbrev StateSet (E : Type) := StateT (Stack E) Set

variable {E α β : Type}

/-- `indef P` is an indefinite, a nondeterministic individual satisfying `P`, with the stack
unchanged. -/
def indef (P : E → Prop) : StateSet E E := fun s ↦ {q | P q.1 ∧ q.2 = s}

/-- `pro` is a pronoun, the topical (most recent) dref, with the stack unchanged. -/
def pro : StateSet E E := fun s ↦ {q | s.getLast? = some q.1 ∧ q.2 = s}

/-- `dref m` introduces a dref, running `m` and pushing its value onto the stack. -/
def dref (m : StateSet E E) : StateSet E E := m >>= fun a s ↦ {(a, s ++ [a])}

/-- A dynamic proposition holds at `s` when some output carries a true value. -/
def holds (m : StateSet E Prop) (s : Stack E) : Prop := ∃ q ∈ m s, q.1

/-- `neg m` is dynamic negation, a test on the input stack that returns it unchanged. -/
def neg (m : StateSet E Prop) : StateSet E Prop := fun s ↦ {(¬ holds m s, s)}

/-- The conditional, from negation via `p → q ↔ ¬(p ∧ ¬q)`. -/
def cond (m n : StateSet E Prop) : StateSet E Prop :=
  neg (m >>= fun p ↦ neg n >>= fun q ↦ pure (p ∧ q))

/-- `det c` is the indefinite determiner, the individuals whose restrictor holds, with the
restrictor's output stacks. -/
def det (c : E → StateSet E Prop) : StateSet E E :=
  fun s ↦ {q | ∃ p, (p, q.2) ∈ c q.1 s ∧ p}

/-- `every c k` is the universal, a scope-taker over dynamic properties defined by
`∀x. P x ⇒ Q x ↔ ¬∃x. P x ∧ ¬Q x`. -/
def every (c : E → StateSet E Prop) (k : E → StateSet E Prop) : StateSet E Prop :=
  neg (det c >>= fun x ↦ neg (k x))

/-- `no c k` is `every` without the inner negation. -/
def no (c : E → StateSet E Prop) (k : E → StateSet E Prop) : StateSet E Prop :=
  neg (det c >>= k)

@[simp] theorem pure_apply (a : α) (s : Stack E) : (pure a : StateSet E α) s = {(a, s)} := rfl

@[simp] theorem mem_indef (P : E → Prop) (s : Stack E) (q : E × Stack E) :
    q ∈ indef P s ↔ P q.1 ∧ q.2 = s := Iff.rfl

@[simp] theorem mem_pro (s : Stack E) (q : E × Stack E) :
    q ∈ pro s ↔ s.getLast? = some q.1 ∧ q.2 = s := Iff.rfl

@[simp] theorem mem_dref (m : StateSet E E) (s : Stack E) (q : E × Stack E) :
    q ∈ dref m s ↔ ∃ r ∈ m s, q = (r.1, r.2 ++ [r.1]) := by simp [dref]

@[simp] theorem neg_apply (m : StateSet E Prop) (s : Stack E) :
    neg m s = {(¬ holds m s, s)} := rfl

@[simp] theorem mem_det (c : E → StateSet E Prop) (s : Stack E) (q : E × Stack E) :
    q ∈ det c s ↔ ∃ p, (p, q.2) ∈ c q.1 s ∧ p := Iff.rfl

@[simp] theorem holds_pure (p : Prop) (s : Stack E) : holds (pure p) s ↔ p := by simp [holds]

@[simp] theorem holds_singleton (p : Prop) (f : Stack E → Stack E) (s : Stack E) :
    holds (fun s ↦ {(p, f s)}) s ↔ p := by simp [holds]

@[simp] theorem holds_bind (m : StateSet E α) (k : α → StateSet E Prop) (s : Stack E) :
    holds (m >>= k) s ↔ ∃ q ∈ m s, holds (k q.1) q.2 := by
  simp only [holds, Set.mem_stateT_bind]
  exact ⟨fun ⟨r, ⟨q, hq, hr⟩, h⟩ ↦ ⟨q, hq, r, hr, h⟩, fun ⟨q, hq, r, hr, h⟩ ↦ ⟨r, ⟨q, hq, hr⟩, h⟩⟩

@[simp] theorem holds_map (f : α → Prop) (m : StateSet E α) (s : Stack E) :
    holds (f <$> m) s ↔ ∃ q ∈ m s, f q.1 := by
  simp only [holds, Set.mem_stateT_map]
  exact ⟨fun ⟨_, ⟨q, hq, rfl⟩, h⟩ ↦ ⟨q, hq, h⟩, fun ⟨q, hq, h⟩ ↦ ⟨_, ⟨q, hq, rfl⟩, h⟩⟩

@[simp] theorem holds_neg (m : StateSet E Prop) (s : Stack E) : holds (neg m) s ↔ ¬ holds m s := by
  simp [holds]

@[simp] theorem det_pure (P : E → Prop) : det (fun x ↦ pure (P x)) = indef P := by
  funext s; ext ⟨x, s'⟩
  exact ⟨fun ⟨_, hp, h⟩ ↦ by cases hp; exact ⟨h, rfl⟩,
    fun ⟨h, hs⟩ ↦ ⟨_, by rw [Set.mem_stateT_pure, hs], h⟩⟩

theorem dref_bind (m : StateSet E E) (π : E → StateSet E α) :
    dref m >>= π = m >>= fun a s ↦ π a (s ++ [a]) := by
  funext s; ext q; simp

theorem bind_pro (m : StateSet E E) (π : E → E → StateSet E α) :
    (dref m >>= fun ν ↦ pro >>= fun u ↦ π ν u) = dref m >>= fun ν ↦ π ν ν := by
  funext s; ext q; simp

theorem indef_met_name (man : E → Prop) (met : E → E → Prop) (p : E) :
    combine (fun x f ↦ f x) (dref (indef man)) (combine (· ·) (pure met) (pure p)) =
      fun s ↦ {q | ∃ x, man x ∧ q = (met p x, s ++ [x])} := by
  funext s; ext q; simp [combine]

theorem indef_left_pro_tired (man left tired : E → Prop) :
    combine (fun x f ↦ f x) (combine (fun x f ↦ f x) (dref (indef man)) (pure left))
      (combine (· ·) (pure fun q p ↦ p ∧ q) (combine (fun x f ↦ f x) pro (pure tired))) =
      dref (indef man) >>= fun x ↦ pure (left x ∧ tired x) := by
  funext s; ext q; simp [combine]

/-! ### Dynamically closed operators (Facts 3.2–3.6) -/

theorem neg_dref_indef (ling left : E → Prop) :
    neg (dref (indef ling) >>= fun x ↦ pure (left x)) = pure (¬ ∃ x, ling x ∧ left x) := by
  funext s; simp

theorem neg_pro (m : E → StateSet E Prop) {s : Stack E} (h : s ≠ []) :
    neg (pro >>= m) s = (pro >>= fun x ↦ neg (m x)) s := by
  have := List.getLast?_eq_some_getLast h
  ext q; simp [this]

theorem cond_dref_indef (P w r : E → Prop) :
    cond (dref (indef P) >>= fun x ↦ pure (w x)) (pro >>= fun y ↦ pure (r y)) =
      pure (∀ x, P x → w x → r x) := by
  funext s; simp [cond]

theorem every_dref_indef (ling hist : E → Prop) (met : E → E → Prop) :
    every (fun x ↦ pure (ling x)) (fun x ↦ dref (indef hist) >>= fun y ↦ pure (met y x)) =
      pure (∀ x, ling x → ∃ y, hist y ∧ met y x) := by
  funext s; simp [every]

theorem every_dref_pro (ling : E → Prop) (rubbed : E → E → Prop) (head : E → E) :
    every (fun x ↦ pure (ling x))
        (fun x ↦ dref (pure x) >>= fun ν ↦ pro >>= fun y ↦ pure (rubbed (head y) ν)) =
      pure (∀ x, ling x → rubbed (head x) x) := by
  funext s; simp [every]

/-! ### Continuations over the State.Set monad (Fact 3.7, (3.23), (3.24))

A tower `ContT β (StateSet E) α` returns an `α` in a computation of type
`StateSet E β`. `monadLift` is monadic Lift (`m ↑ = (m >>= ·)`), `lower`
Lower (application to `pure`), scopal application is `combine` in `ContT`. -/

/-- A tower is a scope-taker over State.Set programs. -/
abbrev Tower (E β α : Type) := ContT β (StateSet E) α

theorem combine_contT {ρ : Type} {M : Type → Type} [Monad M] {α β γ : Type} (f : α → β → γ)
    (m : ContT ρ M α) (n : ContT ρ M β) :
    combine f m n = fun k ↦ m.run fun x ↦ n.run fun y ↦ k (f x y) := rfl

theorem monadLift_id {ρ α : Type} (a : Id α) : (monadLift a : ContT ρ Id α) = fun k ↦ k a := rfl

theorem static_every {ling : E → Prop} (saw : E → E → Prop) (p : E) :
    lower (combine (fun x f ↦ f x) (pure p : ContT Prop Id E)
      (combine (· ·) (pure saw) (fun k ↦ ∀ x, ling x → k x))) =
      ∀ x, ling x → saw x p := rfl

/-- Lowering a combination of lifted programs is their combination in the underlying monad
(Fact 3.14). -/
theorem lower_combine_monadLift {M : Type u → Type u} [Monad M]
    {α β γ : Type u} (f : α → β → γ) (m : M α) (n : M β) :
    lower (combine f (monadLift m : ContT γ M α) (monadLift n)) = combine f m n :=
  rfl

/-- Resetting a lifted program changes nothing (Fact 4.1). -/
theorem reset_map_monadLift {M : Type u → Type u} [Monad M] [LawfulMonad M]
    {α γ ρ : Type u} (f : α → γ) (m : M α) :
    reset (f <$> (monadLift m : ContT γ M α)) = (f <$> monadLift m : ContT ρ M γ) := by
  ext k
  simp [reset, lower, Function.comp_def]

theorem reset_combine_monadLift {M : Type u → Type u} [Monad M]
    {α β γ ρ : Type u} (f : α → β → γ) (m : M α) (n : M β) :
    reset (combine f (monadLift m : ContT γ M α) (monadLift n)) =
      (monadLift (combine f m n) : ContT ρ M γ) :=
  rfl

/-- Universal DPs as scope-takers (Table 3.1). -/
def everyDP (P : E → Prop) : Tower E Prop E := every fun x ↦ (pure (P x) : StateSet E Prop)

/-- Negative DPs as scope-takers (Table 3.1). -/
def noDP (P : E → Prop) : Tower E Prop E := no fun x ↦ (pure (P x) : StateSet E Prop)

@[simp] theorem run_everyDP (P : E → Prop) (k : E → StateSet E Prop) :
    (everyDP P).run k = neg (indef P >>= fun x ↦ neg (k x)) := by
  simp [everyDP, every, ContT.run]

@[simp] theorem run_noDP (P : E → Prop) (k : E → StateSet E Prop) :
    (noDP P).run k = neg (indef P >>= k) := by
  simp [noDP, no, ContT.run]

theorem name_saw_indef (j : E) (saw : E → E → Prop) (ling : E → Prop) :
    lower (combine (fun x f ↦ f x) (liftValue j : Tower E Prop E)
      (combine (· ·) (liftValue saw) (monadLift (indef ling)))) =
      indef ling >>= fun x ↦ pure (saw x j) := by
  funext s; ext q; simp [combine, lower]

theorem indef_saw_every (man ling : E → Prop) (saw : E → E → Prop) :
    lower (combine (fun x f ↦ f x) (monadLift (indef man) : Tower E Prop E)
      (combine (· ·) (liftValue saw) (everyDP ling))) =
      indef man >>= fun x ↦ pure (∀ y, ling y → saw y x) := by
  funext s; ext q; simp [combine, lower]

/-! ### Bind (Facts 3.15, 3.17, 3.18, (3.25), (3.26)) -/

/-- `bindShift m` is the Bind type-shifter (Def. 3.16), which pushes the tower's value onto the
stack before continuing. -/
def bindShift (m : Tower E β E) : Tower E β E := fun k ↦ m.run fun a s ↦ k a (s ++ [a])

@[simp] theorem run_bindShift (m : Tower E β E) (k : E → StateSet E β) :
    (bindShift m).run k = m.run fun a s ↦ k a (s ++ [a]) := rfl

theorem run_bindShift_eq_dref (m : Tower E β E) (k : E → StateSet E β) :
    (bindShift m).run k = m.run fun a ↦ dref (pure a) >>= k := by
  simp only [run_bindShift, dref_bind, pure_bind]

@[simp] theorem bindShift_monadLift (m : StateSet E E) :
    bindShift (monadLift m : Tower E β E) = monadLift (dref m) := by
  funext k
  show (monadLift m : Tower E β E).run _ = (monadLift (dref m) : Tower E β E).run k
  rw [ContT.run_monadLift, ContT.run_monadLift, dref_bind]

@[simp] theorem bindShift_liftValue (a : E) :
    bindShift (liftValue a : Tower E β E) = monadLift (dref (pure a)) :=
  bindShift_monadLift _

theorem run_bindShift_monadLift_indef (P : E → Prop) (k : E → StateSet E β) :
    (bindShift (monadLift (indef P) : Tower E β E)).run k =
      fun s ↦ ⋃ x, ⋃ (_ : P x), k x (s ++ [x]) := by
  funext s; ext q; simp

theorem run_monadLift_pro (k : E → StateSet E β) :
    (monadLift pro : Tower E β E).run k = fun s ↦ ⋃ x ∈ s.getLast?, k x s := by
  funext s; ext q; simp

theorem name_rubbed_pro_head (j : E) (rubbed : E → E → Prop) (head : E → E) :
    lower (combine (fun x f ↦ f x) (bindShift (liftValue j) : Tower E Prop E)
      (combine (· ·) (liftValue rubbed)
        (combine (fun x f ↦ f x) (monadLift pro) (liftValue head)))) =
      fun s ↦ {(rubbed (head j) j, s ++ [j])} := by
  funext s; ext q; simp [combine, lower]

theorem name_mom_saw_pro (j : E) (saw : E → E → Prop) (mom : E → E) :
    lower (combine (fun x f ↦ f x)
      (combine (fun x f ↦ f x) (bindShift (liftValue j) : Tower E Prop E) (liftValue mom))
      (combine (· ·) (liftValue saw) (monadLift pro))) =
      fun s ↦ {(saw j (mom j), s ++ [j])} := by
  funext s; ext q; simp [combine, lower]

/-! ### Inverse scope ((3.28), (3.30))

External Lift of a tower is `pure` one level up (Fact 3.19), internal Lift is
`Functor.map pure` (Def. 3.17), three-level combination is `combine` over
`combine` (Def. 3.18), and one-fell-swoop Lower runs the outer tower at
`lower`. -/

/-- Three-level Lower (Def. 3.19). -/
def lower₂ (m : Tower E β (Tower E β β)) : StateSet E β := m.run lower

@[simp] theorem lower₂_def (m : Tower E β (Tower E β β)) : lower₂ m = m.run lower := rfl

theorem every_over_indef (man ling : E → Prop) (saw : E → E → Prop) :
    lower₂ (combine (combine (fun x f ↦ f x))
      (pure (bindShift (monadLift (indef man))) : Tower E Prop (Tower E Prop E))
      (combine (combine (· ·)) (pure (liftValue saw)) (pure <$> everyDP ling))) =
      pure (∀ y, ling y → ∃ x, man x ∧ saw y x) := by
  funext s; ext q; simp [combine, lower, Function.comp_def]

theorem every_owl_that_saw (owl : E → Prop) (saw : E → E → Prop) (a : E)
    (k : E → StateSet E Prop) :
    every (fun x ↦ dref (pure x) >>= fun ν ↦ pro >>= fun y ↦ pure (owl ν ∧ saw y a)) k =
      fun s ↦ {(∀ ν, owl ν ∧ saw ν a → holds (k ν) (s ++ [ν]), s)} := by
  funext s; simp [every, and_assoc]

/-! ### Scope islands and exceptional scope (Facts 4.2–4.7, (4.7)–(4.12))

A scope island is a constituent that must be evaluated (Def. 4.2); evaluating
and re-lifting is `reset`, and `reset_map_monadLift` is Fact 4.1: Reset
is invisible to a lifted program, so whatever survives evaluation keeps taking
scope. A tower whose value is itself a program is finished by lifting the value
and lowering in one fell swoop, `lower (m >>= monadLift)`. `Examples.ex4_1a` is derived by
`reset_indef_left` and `exceptional_cond`, `Examples.ex4_1b` and `Examples.ex4_1c` by
`reset_every` and `island_cond_every`, and `Examples.ex4_4` by `brc_derivation`. -/

theorem reset_indef_left (ling left : E → Prop) :
    reset (combine (fun x f ↦ f x) (monadLift (indef ling) : Tower E Prop E)
      (liftValue left)) =
      (monadLift (indef ling >>= fun x ↦ pure (left x)) : Tower E Prop Prop) := by
  rw [liftValue, reset_combine_monadLift]; simp [combine]

/-- Resetting *every linguist left* discharges the universal (Fact 4.4). -/
theorem reset_every (ling left : E → Prop) :
    reset (combine (fun x f ↦ f x) (everyDP ling : Tower E Prop E) (liftValue left)) =
      (liftValue (∀ x, ling x → left x) : Tower E Prop Prop) := by
  unfold reset liftValue; congr 1; funext s; ext q; simp [combine, lower]

theorem reset_indef_every (man ling : E → Prop) (met : E → E → Prop) :
    reset (combine (fun x f ↦ f x) (bindShift (monadLift (indef man)) : Tower E Prop E)
      (combine (· ·) (liftValue met) (everyDP ling))) =
      (monadLift (dref (indef man) >>= fun x ↦ pure (∀ y, ling y → met y x)) :
        Tower E Prop Prop) := by
  unfold reset; congr 1; funext s; ext q; simp [combine, lower]

theorem reset_every_indef (man ling : E → Prop) (met : E → E → Prop) :
    (monadLift (lower₂ (combine (combine (fun x f ↦ f x))
      (pure (bindShift (monadLift (indef man))) : Tower E Prop (Tower E Prop E))
      (combine (combine (· ·)) (pure (liftValue met)) (pure <$> everyDP ling)))) :
        Tower E Prop Prop) =
      liftValue (∀ y, ling y → ∃ x, man x ∧ met y x) := by
  rw [every_over_indef]; rfl

theorem reset_every_pro (ling : E → Prop) (met : E → E → Prop) (k : Prop → StateSet E α)
    {s : Stack E} (h : s ≠ []) :
    (reset (combine (fun x f ↦ f x) (everyDP ling : Tower E Prop E)
      (combine (· ·) (liftValue met) (monadLift pro)))).run k s =
      (monadLift (pro >>= fun y ↦ pure (∀ x, ling x → met y x)) : Tower E α Prop).run k s := by
  have := List.getLast?_eq_some_getLast h
  ext q; simp [reset, combine, lower, this]

/-- In *a man met every linguist, and he left* both sentences are Reset and the indefinite binds
across them (4.7). -/
theorem exceptional_binding (man ling left : E → Prop) (met : E → E → Prop) :
    lower (combine (fun x f ↦ f x)
      (reset (combine (fun x f ↦ f x) (bindShift (monadLift (indef man)) : Tower E Prop E)
        (combine (· ·) (liftValue met) (everyDP ling))))
      (combine (· ·) (liftValue fun q p ↦ p ∧ q)
        (reset (combine (fun x f ↦ f x) (monadLift pro : Tower E Prop E)
          (liftValue left))))) =
      dref (indef man) >>= fun x ↦ pure ((∀ y, ling y → met y x) ∧ left x) := by
  funext s; ext q; simp [combine, lower, reset]

theorem exceptional_neg (rel ling : E → Prop) (met : E → E → Prop) :
    lower ((combine (· ·) (liftValue neg : Tower E Prop (StateSet E Prop → StateSet E Prop))
      (pure <$> reset (combine (fun x f ↦ f x) (monadLift (indef rel) : Tower E Prop E)
        (combine (· ·) (liftValue met) (everyDP ling))))) >>= monadLift) =
      indef rel >>= fun x ↦ pure (¬ ∀ y, ling y → met y x) := by
  funext s; ext q; simp [combine, lower, reset]

theorem exceptional_cond (rel dies : E → Prop) (rich : Prop) :
    lower ((combine (· ·)
      (combine (· ·) (liftValue (cond (E := E)) : Tower E Prop _)
        (pure <$> reset (combine (fun x f ↦ f x) (monadLift (indef rel) : Tower E Prop E)
          (liftValue dies))))
      (pure <$> liftValue rich)) >>= monadLift) =
      indef rel >>= fun x ↦ pure (dies x → rich) := by
  funext s; ext q; simp [combine, lower, reset, cond]

theorem island_cond_every (rel dies : E → Prop) (rich : Prop) :
    lower ((combine (· ·)
      (combine (· ·) (liftValue (cond (E := E)) : Tower E Prop _)
        (pure <$> reset (combine (fun x f ↦ f x) (everyDP rel : Tower E Prop E)
          (liftValue dies))))
      (pure <$> liftValue rich)) >>= monadLift) =
      pure ((∀ x, rel x → dies x) → rich) := by
  funext s; ext q; simp [combine, lower, reset, cond]

theorem exceptional_feeds_binding (rel dies steelMagnate : E → Prop) (rich : Prop) :
    lower (combine (fun x f ↦ f x)
      (monadLift (lower ((combine (· ·)
        (combine (· ·) (liftValue (cond (E := E)) : Tower E Prop _)
          (pure <$> reset (combine (fun x f ↦ f x)
            (bindShift (monadLift (indef rel)) : Tower E Prop E) (liftValue dies))))
        (pure <$> liftValue rich)) >>= monadLift)) : Tower E Prop Prop)
      (combine (· ·) (liftValue fun q p ↦ p ∧ q)
        (reset (combine (fun x f ↦ f x) (monadLift pro : Tower E Prop E)
          (liftValue steelMagnate))))) =
      dref (indef rel) >>= fun x ↦ pure ((dies x → rich) ∧ steelMagnate x) := by
  funext s; ext q; simp [combine, lower, reset, cond]

theorem brc_derivation (cand : E → Prop) (paperBy submitted : E → E → Prop) :
    lower₂ (combine (combine (fun x f ↦ f x))
      (pure (bindShift (noDP cand)) : Tower E Prop (Tower E Prop E))
      (combine (combine (· ·)) (pure (liftValue submitted))
        (pure <$> monadLift (pro >>= fun z ↦ indef (paperBy z))))) =
      pro >>= fun z ↦ indef (paperBy z) >>= fun y ↦ pure (¬ ∃ x, cand x ∧ submitted y x) := by
  funext s; ext q; simp [combine, lower, Function.comp_def]

/-! ### Choice functions (§4.7.1, (4.34)–(4.38))

The choice-functional theory interprets an indefinite as a choice function applied to its
restrictor and closes the function existentially wherever it likes, so the indefinite takes
apparent scope without moving. When the restrictor varies with a bound variable, closing the
function above the binder yields readings that no scope-taking derivation gives
(`Examples.ex4_4`, and `Examples.ex4_6` by `cf_layered_iff`). -/

section ChoiceFunction

open Quantifier

-- *Some* at a predicate restrictor and scope, as the choice-function lemmas supply them.
private theorem some_iff_exists {A B : E → Prop} : Det.some A B ↔ ∃ x, A x ∧ B x := .rfl

theorem cf_exceptional_cond (rel dies : E → Prop) (rich : Prop) (hrel : ∃ x, rel x)
    (s : Stack E) :
    (∃ f : ChoiceFunction E, dies (f rel) → rich) ↔
      holds (indef rel >>= fun x ↦ pure (dies x → rich)) s := by
  refine (ChoiceFunction.exists_apply_iff_some hrel fun x ↦ dies x → rich).trans ?_
  simp only [holds, indef, Det.some, Set.mem_stateT_bind, Set.mem_stateT_pure, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x, hx, h⟩
    exact ⟨_, ⟨(x, s), ⟨hx, rfl⟩, rfl⟩, h⟩
  · rintro ⟨_, ⟨q, ⟨hq, -⟩, rfl⟩, h⟩
    exact ⟨q.1, hq, h⟩

/-- Closing the choice function above *no candidate* gives the [schwarz-2001] reading that no
candidate submitted every paper he wrote (4.35, `Examples.ex4_4`) ((4.35)). -/
theorem cf_no_candidate_iff [Nonempty E] (cand : E → Prop) (paperBy submitted : E → E → Prop)
    (hwrote : ∀ x, cand x → ∃ y, paperBy x y) (hinj : Set.InjOn paperBy {x | cand x}) :
    (∃ f : ChoiceFunction E, ¬ ∃ x, cand x ∧ submitted (f (paperBy x)) x) ↔
      ¬ ∃ x, cand x ∧ ∀ y, paperBy x y → submitted y x := by
  have h := ChoiceFunction.exists_forall_apply_iff_of_injective (ι := {x | cand x})
    (Set.injOn_iff_injective.1 hinj) (fun x ↦ hwrote x x.2) fun x y ↦ ¬ submitted y x
  simp only [Set.domRestrict_apply, Subtype.forall, Set.mem_ofPred_eq, some_iff_exists] at h
  push Not
  simpa using h

theorem cf_same_restrictor_iff (girl : E → Prop) (boysFancied gave : E → E → Prop) {B : E → Prop}
    (hB : ∃ y, B y) (hsame : ∀ x, girl x → boysFancied x = B) :
    (∃ f : ChoiceFunction E, ∀ x, girl x → gave (f (boysFancied x)) x) ↔
      ∃ y, B y ∧ ∀ x, girl x → gave y x := by
  rw [← some_iff_exists, ← ChoiceFunction.exists_apply_iff_some hB]
  exact exists_congr fun f ↦ forall₂_congr fun x hx ↦ by rw [hsame x hx]

theorem cf_layered_iff [Nonempty E] (linguist : E → Prop) (bookBy : E → E → Prop)
    (read : E → Prop) (hling : ∃ x, linguist x) (hbook : ∀ x, linguist x → ∃ y, bookBy x y)
    (hinj : Set.InjOn bookBy {x | linguist x}) :
    (∃ f : ChoiceFunction E, ¬ ∃ g : ChoiceFunction E, read (f (bookBy (g linguist)))) ↔
      ∀ x, linguist x → ∃ y, bookBy x y ∧ ¬ read y := by
  have hneg (f : ChoiceFunction E) : (¬ ∃ g : ChoiceFunction E, read (f (bookBy (g linguist)))) ↔
      ∀ x, linguist x → ¬ read (f (bookBy x)) := by
    rw [not_exists]
    exact ChoiceFunction.forall_apply_iff_every hling fun z ↦ ¬ read (f (bookBy z))
  have h := ChoiceFunction.exists_forall_apply_iff_of_injective (ι := {x | linguist x})
    (Set.injOn_iff_injective.1 hinj) (fun x ↦ hbook x x.2) fun _ y ↦ ¬ read y
  simp only [Set.domRestrict_apply, Subtype.forall, Set.mem_ofPred_eq, some_iff_exists] at h
  simpa only [hneg] using h

theorem cf_disjunction_iff [Nonempty E] (cand : E → Prop) (vita portfolio : E → E)
    (submit : E → E → Prop)
    (hinj : Set.InjOn (fun x y ↦ y = vita x ∨ y = portfolio x) {x | cand x}) :
    (∃ f : ChoiceFunction E, ¬ ∃ x, cand x ∧ submit (f fun y ↦ y = vita x ∨ y = portfolio x) x) ↔
      ¬ ∃ x, cand x ∧ submit (vita x) x ∧ submit (portfolio x) x := by
  have h := ChoiceFunction.exists_forall_apply_iff_of_injective (ι := {x | cand x})
    (Set.injOn_iff_injective.1 hinj) (fun x ↦ ⟨vita x, .inl rfl⟩) fun x y ↦ ¬ submit y x.1
  simp only [Set.domRestrict_apply, Subtype.forall, Set.mem_ofPred_eq, some_iff_exists] at h
  push Not
  simpa [or_imp, forall_and, imp_iff_not_or] using h

end ChoiceFunction

/-! ### Selective exceptional scope (§4.5.2)

Two indefinites on one island yield three fully evaluated programs: one
`StateSet E Prop` with the nondeterminism agglomerated, and two
`StateSet E (StateSet E Prop)` layerings. A layered program unfolds back into a
three-level tower after evaluation, so the indefinites scope separately
(`Examples.ex4_18b`, by `indef_visits_indef_layered`). -/

theorem indef_visits_indef (law rel : E → Prop) (visits : E → E → Prop) :
    lower (combine (fun x f ↦ f x) (monadLift (indef law) : Tower E Prop E)
      (combine (· ·) (liftValue visits) (monadLift (indef rel)))) =
      indef law >>= fun x ↦ indef rel >>= fun y ↦ pure (visits y x) := by
  funext s; ext q; simp [combine, lower]

theorem indef_visits_indef_layered (law rel : E → Prop) (visits : E → E → Prop) :
    lower (lower <$> combine (combine (fun x f ↦ f x))
      (pure (monadLift (indef law)) : Tower E (StateSet E Prop) (Tower E Prop E))
      (combine (combine (· ·)) (pure (liftValue visits)) (pure <$> monadLift (indef rel)))) =
      indef rel >>= fun y ↦ pure (indef law >>= fun x ↦ pure (visits y x)) := by
  funext s; ext q; simp [combine, lower, Function.comp_def]

theorem monadLift_layered {M : Type u → Type u} [Monad M] [LawfulMonad M] {ρ α β : Type u}
    (m : M α) (f : α → M β) :
    (monadLift <$> (monadLift (m >>= fun y ↦ pure (f y)) : ContT ρ M (M β)) :
      ContT ρ M (ContT ρ M β)) = fun c ↦ m >>= fun y ↦ c (monadLift (f y)) := by
  funext c
  show ContT.run _ c = _
  simp [ContT.run_map, ContT.run_monadLift, Function.comp_def]

/-! ### Plural indefinites and distributivity ((4.17))

Plural individuals are sets of atoms (Def. 4.3), atoms identified with
singletons. Plural indefinites are nondeterministic like singular ones, so their
existential scope escapes islands, while the distributivity operator is a
scope-taker discharged on evaluation. -/

section Plural

variable {A : Type}

/-- `distr R X` is the distributivity operator (Def. 4.5), a tower quantifying over the atoms of
its plural argument. -/
def distr (R : Set A → α) (X : Set A) : Tower (Set A) Prop α :=
  fun k s ↦ {(∀ x ∈ X, holds (k (R {x})) s, s)}

@[simp] theorem run_distr (R : Set A → α) (X : Set A) (k : α → StateSet (Set A) Prop) :
    (distr R X).run k = fun s ↦ {(∀ x ∈ X, holds (k (R {x})) s, s)} := rfl

theorem indef_fronts_two_distr (guard bldgs : Set A → Prop) (fronts : Set A → Set A → Prop) :
    (combine (combine (combine (fun x f ↦ f x)))
      (pure (pure (monadLift (indef guard))) :
        Tower (Set A) Prop (Tower (Set A) Prop (Tower (Set A) Prop (Set A))))
      ((pure <$> ·) <$> (distr fronts <$>
        monadLift (indef fun X ↦ bldgs X ∧ X.ncard = 2)))).run (·.run lower) =
      indef (fun X ↦ bldgs X ∧ X.ncard = 2) >>= fun Y ↦
        pure (∀ y ∈ Y, ∃ x, guard x ∧ fronts {y} x) := by
  funext s; ext q; simp [combine, lower, Function.comp_def]

end Plural

/-! ### Disjunction ((4.27)–(4.31))

Program disjunction is `<|>` in `StateT _ Set` (Def. 4.6, the union of outputs);
`or` disjoins two scope-takers' results (Def. 4.7). Disjunctions are therefore
nondeterministic programs that survive Reset, bind donkey pronouns, and, being
polymorphic, scope over an operator that scopes over their disjuncts (`Examples.ex4_24b`, by
`or_over_every`). -/

/-- Disjunction of scope-takers (Def. 4.7). -/
def or (m n : Tower E β α) : Tower E β α := fun k ↦ m.run k <|> n.run k

@[simp] theorem run_or (m n : Tower E β α) (k : α → StateSet E β) :
    (or m n).run k = (m.run k <|> n.run k) := rfl

theorem or_names_left (c m : E) (left : E → Prop) :
    lower (combine (fun x f ↦ f x) (or (bindShift (liftValue c)) (bindShift (liftValue m)))
      (liftValue left : Tower E Prop (E → Prop))) =
      (dref (pure c) <|> dref (pure m)) >>= fun x ↦ pure (left x) := by
  funext s; ext q; simp [combine, lower]

theorem or_subparts (me a c : E) (see hear : E → E → Prop) :
    lower (combine (fun x f ↦ f x) (liftValue me : Tower E Prop E)
      (or (combine (fun x f ↦ f x) (bindShift (liftValue a)) (liftValue see))
        (combine (fun x f ↦ f x) (bindShift (liftValue c)) (liftValue hear)))) =
      ((dref (pure a) >>= fun x ↦ pure (see x me)) <|>
        dref (pure c) >>= fun x ↦ pure (hear x me)) := by
  funext s; ext q; simp [combine, lower]

theorem or_pure_pure (steak burger : E → Prop) :
    or (pure (monadLift (indef steak)) : Tower E Prop (Tower E Prop E))
      (pure (monadLift (indef burger))) =
      fun c ↦ c (monadLift (indef steak)) <|> c (monadLift (indef burger)) := rfl

theorem or_over_every (person steak burger : E → Prop) (ate : E → E → Prop) :
    lower₂ (combine (combine (fun x f ↦ f x))
      (pure (everyDP person) : Tower E Prop (Tower E Prop E))
      (combine (combine (· ·)) (pure (liftValue ate))
        (or (pure (monadLift (indef steak))) (pure (monadLift (indef burger)))))) =
      (pure (∀ y, person y → ∃ x, steak x ∧ ate x y) <|>
        pure (∀ y, person y → ∃ x, burger x ∧ ate x y)) := by
  funext s; ext q; simp [combine, lower, Function.comp_def]

theorem or_map_pure_every (steak burger : E → Prop) :
    or (pure <$> everyDP steak : Tower E Prop (Tower E Prop E)) (pure <$> everyDP burger) =
      fun c ↦ (everyDP steak).run (fun x ↦ c (pure x)) <|>
        (everyDP burger).run (fun x ↦ c (pure x)) := rfl

theorem or_or_names (m j b : E) :
    lower (lower <$>
      or (pure (or (liftValue m) (liftValue j)) : Tower E (StateSet E E) (Tower E E E))
        (pure (liftValue b))) =
      (pure (pure m <|> pure j) <|> pure (pure b)) := by
  funext s; ext q; simp [lower]

/-! ### Drefs of proper names take exceptional scope ((5.8))

Anything Bind-shifted survives evaluation (Fact 1.4, Ch. 5.2), so a proper name
inside an island binds a sloppy pro-form outside it (`Examples.ex5_7a`, by
`name_dref_inverse`). -/

theorem name_dref_inverse (person : E → Prop) (thinks : Prop → E → Prop) (come : E → Prop)
    (b : E) :
    lower₂ (combine (combine (fun x f ↦ f x))
      (pure (everyDP person) : Tower E Prop (Tower E Prop E))
      (combine (combine (· ·)) (pure (liftValue thinks))
        (pure <$> combine (fun x f ↦ f x) (bindShift (liftValue b)) (liftValue come)))) =
      dref (pure b) >>= fun y ↦ pure (∀ x, person x → thinks (come y) x) := by
  funext s; ext q; simp [combine, lower, Function.comp_def]

theorem name_dref_cond (person : E → Prop) (thinks : Prop → E → Prop) (come invite : E → Prop)
    (b : E) :
    cond (dref (pure b) >>= fun y ↦ pure (∀ x, person x → thinks (come y) x))
      (pro >>= fun z ↦ pure (¬ invite z)) =
      pure ((∀ x, person x → thinks (come b) x) → ¬ invite b) := by
  funext s; simp [cond]

/-! ### Maximal drefs and dynamic generalized quantifiers (§5.3.2, (5.19), (5.24))

A dynamic GQ (Def. 5.3) returns its truth condition and pushes the refset — the
restrictor individuals satisfying the scope — as a plural dref. The stack holds
pluralities; the quantifier ranges over atoms (`Examples.ex5_23`, by `dynGQ_neg`). -/

section DynamicGQ

variable {A : Type}

/-- Dynamic GQ with a maximal refset dref (Def. 5.3). -/
def dynGQ (DET : Set A → Set A → Prop) (M : Set A) : Tower (Set A) Prop A :=
  fun k s ↦ {(DET M {x | x ∈ M ∧ holds (k x) s}, s ++ [{x | x ∈ M ∧ holds (k x) s}])}

@[simp] theorem run_dynGQ (DET : Set A → Set A → Prop) (M : Set A) (k : A → StateSet (Set A) Prop) :
    (dynGQ DET M).run k =
      fun s ↦ {(DET M {x | x ∈ M ∧ holds (k x) s}, s ++ [{x | x ∈ M ∧ holds (k x) s}])} := rfl

theorem dynGQ_left (ling left : Set A) :
    lower (combine (fun x f ↦ f x) (dynGQ (fun _ N ↦ N.ncard = 1) ling)
      (liftValue (· ∈ left))) =
      dref (pure (ling ∩ left)) >>= fun N ↦ pure (N.ncard = 1) := by
  funext s; ext q; simp [combine, lower]

theorem dynGQ_pro (ling left : Set A) (tired : Set A → Prop) :
    lower (combine (fun x f ↦ f x)
      (monadLift (dref (pure (ling ∩ left)) >>= fun N ↦ pure (N.ncard = 1)) :
        Tower (Set A) Prop Prop)
      (combine (· ·) (liftValue fun q p ↦ p ∧ q)
        (combine (fun x f ↦ f x) (monadLift pro) (liftValue tired)))) =
      dref (pure (ling ∩ left)) >>= fun N ↦ pure (N.ncard = 1 ∧ tired N) := by
  funext s; ext q; simp [combine, lower]

theorem dynGQ_neg (sen admire : Set A) :
    lower ((combine (· ·) (liftValue (neg (E := Set A)) : Tower (Set A) Prop _)
      (pure <$> reset (combine (fun x f ↦ f x) (dynGQ (fun _ N ↦ N = ∅) sen)
        (liftValue (· ∈ admire))))) >>= monadLift) =
      dref (pure (sen ∩ admire)) >>= fun N ↦ pure (¬ N = ∅) := by
  funext s; ext q; simp [combine, lower, reset]

end DynamicGQ

/-! ### The Focus monad (Fact 5.4, §5.4.3–§5.4.5, (5.30))

Rooth's two-dimensional focus semantics is the pointed-powerset monad
([shan-2002]): a value paired with its alternatives, sequencing the Identity
monad on the first coordinate and the Set monad on the second (Def. 5.6). It is the
library's `WithAlternatives`, whose monad laws are the thesis's Appendix B.9.
F-marking injects a value with its alternatives; `only`/`also` quantify over the
alternatives of a monadic VP (Def. 5.10). Focus effects are managed by scope like
any other, so they survive Reset and can be layered for selective association
across islands (`Examples.ex5_27b`, by `only_focus_layered` and
`also_only_focus_layered`). -/

namespace Focus

theorem combine_eq_map₂ {α β γ : Type u} (f : α → β → γ) (m : WithAlternatives α)
    (n : WithAlternatives β) : combine f m n = WithAlternatives.map₂ f m n :=
  (combine_eq_seq f m n).trans (WithAlternatives.map₂_eq_seq f m n).symm

variable {E W : Type}

/-- `fmark alt a` is F-marking (Def. 5.7), a value with its contextual alternatives. -/
def fmark (alt : E → Set E) (a : E) : WithAlternatives E := ⟨a, alt a⟩

/-- A VP meaning as the set of subject–world pairs it holds of. -/
def toSet (Q : E → W → Prop) : Set (E × W) := {xw | Q xw.1 xw.2}

@[simp] theorem mem_toSet {Q : E → W → Prop} {x : E} {w : W} : (x, w) ∈ toSet Q ↔ Q x w :=
  Iff.rfl

theorem toSet_injective : Function.Injective (toSet : (E → W → Prop) → Set (E × W)) :=
  Function.uncurry_injective

/-- `only P` holds of `x` at `w` when the VP's value is among its alternatives and *only* on the
identity scale is true at `(x, w)`. -/
def only (P : WithAlternatives (E → W → Prop)) : E → W → Prop := fun x w ↦
  P.ordinary ∈ P.alternatives ∧
    _root_.Focus.Particles.only (· = ·) (toSet '' P.alternatives) (toSet P.ordinary) (x, w) = 1

/-- `also P` holds of `x` at `w` when the VP's value is among its alternatives and the additive on
the identity scale is true at `(x, w)`. -/
def also (P : WithAlternatives (E → W → Prop)) : E → W → Prop := fun x w ↦
  P.ordinary ∈ P.alternatives ∧
    _root_.Focus.Particles.additive (· = ·) (toSet '' P.alternatives) (toSet P.ordinary) (x, w) = 1

theorem only_iff (P : WithAlternatives (E → W → Prop)) (x : E) (w : W) :
    only P x w ↔ {Q | Q ∈ P.alternatives ∧ Q x w} = {P.ordinary} := by
  simp only [only, _root_.Focus.Particles.only_eq_one_iff, _root_.Focus.Particles.mem_atLeast,
    _root_.Focus.Particles.mem_atMost, Set.forall_mem_image, Set.exists_mem_image, mem_toSet,
    toSet_injective.eq_iff, Set.eq_singleton_iff_unique_mem, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨ho, ⟨_, -, hw, rfl⟩, hmax⟩
    exact ⟨⟨ho, hw⟩, fun Q ⟨hQ, hQw⟩ ↦ (hmax hQ hQw).symm⟩
  · rintro ⟨⟨ho, hw⟩, hu⟩
    exact ⟨ho, ⟨_, ho, hw, rfl⟩, fun Q hQ hQw ↦ (hu Q ⟨hQ, hQw⟩).symm⟩

theorem also_iff (P : WithAlternatives (E → W → Prop)) (x : E) (w : W) :
    also P x w ↔ {P.ordinary} ⊂ {Q | Q ∈ P.alternatives ∧ Q x w} := by
  simp only [also, _root_.Focus.Particles.additive_eq_one_iff,
    _root_.Focus.Particles.mem_additivePresup, Set.exists_mem_image, mem_toSet,
    toSet_injective.eq_iff]
  constructor
  · rintro ⟨ho, ⟨Q, hQ, hQw, hne⟩, hw⟩
    have hsub : {P.ordinary} ⊆ {Q | Q ∈ P.alternatives ∧ Q x w} :=
      Set.singleton_subset_iff.2 ⟨ho, hw⟩
    exact (Set.ssubset_iff_of_subset hsub).2
      ⟨Q, ⟨hQ, hQw⟩, fun h ↦ hne (Set.mem_singleton_iff.1 h).symm⟩
  · intro h
    obtain ⟨ho, hw⟩ := Set.singleton_subset_iff.1 h.subset
    obtain ⟨Q, ⟨hQ, hQw⟩, hne⟩ := (Set.ssubset_iff_of_subset h.subset).1 h
    exact ⟨ho, ⟨Q, hQ, hQw, fun h' ↦ hne (Set.mem_singleton_iff.2 h'.symm)⟩, hw⟩

theorem fmark_left (alt : E → Set E) (j : E) (left : E → Prop) :
    lower (combine (fun x f ↦ f x) (monadLift (fmark alt j) : ContT Prop WithAlternatives E)
      (liftValue left)) =
      ⟨left j, {p | ∃ x ∈ alt j, p = left x}⟩ := by
  rw [liftValue, lower_combine_monadLift, combine_eq_map₂]
  exact WithAlternatives.ext rfl (by ext; simp [fmark, WithAlternatives.alternatives_pure, eq_comm])

theorem only_met_fmark (alt : E → Set E) (j : E) (met : E → E → W → Prop) :
    only (lower (combine (· ·) (liftValue met :
        ContT (E → W → Prop) WithAlternatives _)
      (monadLift (fmark alt j)))) =
      fun x w ↦ {Q | (∃ y ∈ alt j, Q = met y) ∧ Q x w} = {met j} := by
  funext x w
  rw [liftValue, lower_combine_monadLift, combine_eq_map₂, only_iff]
  simp [fmark, WithAlternatives.alternatives_pure, eq_comm]

theorem only_fmark_fmark (alt : E → Set E) (b s : E) (intro : E → E → E → W → Prop) :
    only (lower (combine (· ·)
      (combine (· ·) (liftValue intro : ContT (E → W → Prop) WithAlternatives _)
        (monadLift (fmark alt b)))
      (monadLift (fmark alt s)))) =
      fun z w ↦ {Q | (∃ x ∈ alt b, ∃ y ∈ alt s, Q = intro x y) ∧ Q z w} = {intro b s} := by
  funext z w
  rw [only_iff]
  simp [combine, lower, fmark, WithAlternatives.alternatives_bind,
    WithAlternatives.alternatives_pure, eq_comm]

theorem only_focus_layered (alt : E → Set E) (b s : E) (intro : E → E → E → W → Prop) :
    lower (combine (· ·)
      (liftValue only : ContT (E → W → Prop) WithAlternatives _)
      (lower <$> combine (combine (· ·))
        (combine (combine (· ·))
          (pure (liftValue intro) :
            ContT (E → W → Prop) WithAlternatives (ContT (E → W → Prop) WithAlternatives _))
          (pure (monadLift (fmark alt b))))
        (pure <$> monadLift (fmark alt s)))) =
      ⟨only (combine (· ·) (combine (· ·) (pure intro) (fmark alt b)) (pure s)),
        {P | ∃ y ∈ alt s,
          P = only (combine (· ·) (combine (· ·) (pure intro) (fmark alt b)) (pure y))}⟩ := by
  refine WithAlternatives.ext ?_ ?_
  · simp [combine, lower, fmark, Function.comp_def]
  · ext P
    simp [combine, lower, fmark, Function.comp_def, eq_comm]

theorem also_only_focus_layered (alt : E → Set E) (b s : E) (intro : E → E → E → W → Prop) :
    also (lower (combine (· ·)
      (liftValue only : ContT (E → W → Prop) WithAlternatives _)
      (lower <$> combine (combine (· ·))
        (combine (combine (· ·))
          (pure (liftValue intro) :
            ContT (E → W → Prop) WithAlternatives (ContT (E → W → Prop) WithAlternatives _))
          (pure (monadLift (fmark alt b))))
        (pure <$> monadLift (fmark alt s))))) =
      fun z w ↦ {only (combine (· ·) (combine (· ·) (pure intro) (fmark alt b)) (pure s))} ⊂
        {Q | (∃ y ∈ alt s, Q =
          only (combine (· ·) (combine (· ·) (pure intro) (fmark alt b)) (pure y))) ∧ Q z w} := by
  rw [only_focus_layered]
  funext z w
  exact propext (also_iff _ z w)

theorem reset_fmark (alt : E → Set E) (j : E) (left : E → Prop) :
    reset (combine (fun x f ↦ f x) (monadLift (fmark alt j) : ContT Prop WithAlternatives E)
      (liftValue left)) =
      (monadLift (fmark alt j >>= fun x ↦ pure (left x)) : ContT Prop WithAlternatives Prop) := by
  rw [liftValue, reset_combine_monadLift]; simp [combine]

end Focus

theorem focus_over_stateSet (alt : E → Set E) (p : E) (ling : E → Prop) (met : E → E → Prop) :
    lower (lower <$> combine (combine (fun x f ↦ f x))
      (pure (monadLift (indef ling)) : ContT (StateSet E Prop) WithAlternatives (Tower E Prop E))
      (combine (combine (· ·)) (pure (liftValue met))
        (pure <$> monadLift (Focus.fmark alt p)))) =
      (⟨indef ling >>= fun x ↦ pure (met p x),
        {π | ∃ y ∈ alt p, π = indef ling >>= fun x ↦ pure (met y x)}⟩ : WithAlternatives _) := by
  refine WithAlternatives.ext ?_ ?_
  · simp [combine, lower, Focus.fmark, Function.comp_def]
  · ext π
    simp [combine, lower, Focus.fmark, Function.comp_def, eq_comm]

/-! ### Alternative semantics: the Reader.Set monad (Facts 5.7–5.9, 5.12, §5.5.4)

Swapping `StateT` for `ReaderT` over `Set` gives [kratzer-shimoyama-2002]-style
alternative semantics with scope-managed side effects: indefinites still take
selective exceptional scope, and Bind (Def. 5.21) handles in-scope binding
without the abstraction rule [shan-2004] criticised. But `pure` discards the
stack, so nothing binds out of an island: the account of exceptional scope lives
in the Set monad both share, the account of exceptional binding in State. -/

/-- The Reader.Set monad is `ReaderT` over the `Set` monad. -/
abbrev ReaderSet (E : Type) := ReaderT (Stack E) Set

namespace ReaderSet

variable {E α β : Type}

/-- `indef P` is an indefinite, a nondeterministic individual insensitive to the stack. -/
def indef (P : E → Prop) : ReaderSet E E := fun _ ↦ {x | P x}

/-- `pro` is a pronoun, the topical dref. -/
def pro : ReaderSet E E := fun s ↦ {x | s.getLast? = some x}

/-- Some output is true. -/
def holds (m : ReaderSet E Prop) (s : Stack E) : Prop := ∃ p ∈ m s, p

/-- Negation (Def. 5.18). -/
def neg (m : ReaderSet E Prop) : ReaderSet E Prop := fun s ↦ {¬ holds m s}

/-- The universal (Def. 5.19). -/
def everyDP (P : E → Prop) : ContT Prop (ReaderSet E) E :=
  fun k ↦ neg (indef P >>= fun x ↦ neg (k x))

/-- The negative quantifier. -/
def noDP (P : E → Prop) : ContT Prop (ReaderSet E) E := fun k ↦ neg (indef P >>= k)

/-- `bindShift m` is Bind for Reader.Set towers (Def. 5.21), whose continuation reads the
extended stack. -/
def bindShift (m : ContT β (ReaderSet E) E) : ContT β (ReaderSet E) E :=
  fun k ↦ m.run fun a s ↦ k a (s ++ [a])

@[simp] theorem mem_indef (P : E → Prop) (s : Stack E) (x : E) : x ∈ indef P s ↔ P x := Iff.rfl

@[simp] theorem mem_pro (s : Stack E) (x : E) : x ∈ pro s ↔ s.getLast? = some x := Iff.rfl

@[simp] theorem neg_apply (m : ReaderSet E Prop) (s : Stack E) : neg m s = {¬ holds m s} := rfl

@[simp] theorem holds_pure (p : Prop) (s : Stack E) : holds (pure p) s ↔ p := by simp [holds]

@[simp] theorem holds_bind (m : ReaderSet E α) (k : α → ReaderSet E Prop) (s : Stack E) :
    holds (m >>= k) s ↔ ∃ x ∈ m s, holds (k x) s := by
  simp only [holds, Set.mem_readerT_bind]
  exact ⟨fun ⟨p, ⟨x, hx, hp⟩, h⟩ ↦ ⟨x, hx, p, hp, h⟩, fun ⟨x, hx, p, hp, h⟩ ↦ ⟨p, ⟨x, hx, hp⟩, h⟩⟩

@[simp] theorem holds_map (f : α → Prop) (m : ReaderSet E α) (s : Stack E) :
    holds (f <$> m) s ↔ ∃ x ∈ m s, f x := by
  simp only [holds, Set.mem_readerT_map]
  exact ⟨fun ⟨_, ⟨x, hx, rfl⟩, h⟩ ↦ ⟨x, hx, h⟩, fun ⟨x, hx, h⟩ ↦ ⟨_, ⟨x, hx, rfl⟩, h⟩⟩

@[simp] theorem holds_neg (m : ReaderSet E Prop) (s : Stack E) : holds (neg m) s ↔ ¬ holds m s := by
  simp [holds]

@[simp] theorem run_everyDP (P : E → Prop) (k : E → ReaderSet E Prop) :
    (everyDP P).run k = neg (indef P >>= fun x ↦ neg (k x)) := rfl

@[simp] theorem run_noDP (P : E → Prop) (k : E → ReaderSet E Prop) :
    (noDP P).run k = neg (indef P >>= k) := rfl

@[simp] theorem run_bindShift (m : ContT β (ReaderSet E) E) (k : E → ReaderSet E β) :
    (bindShift m).run k = m.run fun a s ↦ k a (s ++ [a]) := rfl

theorem reset_indef_left (ling left : E → Prop) :
    reset (combine (fun x f ↦ f x) (monadLift (indef ling) : ContT Prop (ReaderSet E) E)
      (liftValue left)) =
      (monadLift (indef ling >>= fun x ↦ pure (left x)) : ContT Prop (ReaderSet E) Prop) := by
  rw [liftValue, reset_combine_monadLift]; simp [combine]

theorem reset_every (ling left : E → Prop) :
    reset (combine (fun x f ↦ f x) (everyDP ling)
      (liftValue left)) =
      (liftValue (∀ x, ling x → left x) : ContT Prop (ReaderSet E) Prop) := by
  unfold reset liftValue; congr 1; funext s; ext; simp [combine, lower]

theorem indef_met_indef_layered (sem phon : E → Prop) (met : E → E → Prop) :
    lower (lower (M := ReaderSet E) <$> combine (combine (fun x f ↦ f x))
      (pure (monadLift (indef sem)) :
        ContT (ReaderSet E Prop) (ReaderSet E) (ContT Prop (ReaderSet E) E))
      (combine (combine (· ·)) (pure (liftValue met))
        (pure <$> monadLift (indef phon)))) =
      indef phon >>= fun y ↦ pure (indef sem >>= fun x ↦ pure (met y x)) := by
  funext s; ext; simp [combine, lower, Function.comp_def]

theorem bind_pro_append (π : E → ReaderSet E α) (s : Stack E) (a : E) :
    (pro >>= π) (s ++ [a]) = π a (s ++ [a]) := by
  ext; simp

theorem indef_rubbed_pro_head (ling : E → Prop) (rubbed : E → E → Prop) (head : E → E) :
    lower (combine (fun x f ↦ f x)
      (bindShift (monadLift (indef ling)) : ContT Prop (ReaderSet E) E)
      (combine (· ·) (liftValue rubbed)
        (combine (fun x f ↦ f x) (monadLift pro) (liftValue head)))) =
      indef ling >>= fun x ↦ pure (rubbed (head x) x) := by
  funext s; ext; simp [combine, lower]

theorem indef_told_no_indef_pro (man person : E → Prop) (bookBy : E → E → Prop)
    (told : E → E → E → Prop) :
    (combine (combine (fun x f ↦ f x))
      (pure <$> bindShift (monadLift (indef man)) :
        ContT Prop (ReaderSet E) (ContT Prop (ReaderSet E) E))
      (combine (combine (· ·))
        (pure (combine (· ·) (liftValue told)
          (noDP person)) : ContT Prop (ReaderSet E) (ContT Prop (ReaderSet E) (E → E → Prop)))
        (pure <$> monadLift (pro >>= fun u ↦ indef (bookBy u))))).run lower =
      indef man >>= fun x ↦ indef (bookBy x) >>= fun z ↦
        pure (¬ ∃ y, person y ∧ told y z x) := by
  funext s; ext; simp [combine, lower, Function.comp_def]

theorem no_exceptional_binding (man left tired : E → Prop) :
    lower (combine (fun x f ↦ f x)
      (reset (combine (fun x f ↦ f x)
        (bindShift (monadLift (indef man)) : ContT Prop (ReaderSet E) E)
        (liftValue left)))
      (combine (· ·) (liftValue fun q p ↦ p ∧ q)
        (reset (combine (fun x f ↦ f x) (monadLift pro : ContT Prop (ReaderSet E) E)
          (liftValue tired))))) =
      indef man >>= fun x ↦ pro >>= fun u ↦ pure (left x ∧ tired u) := by
  funext s; ext; simp [combine, lower, reset]

theorem run_monadLift (m : ReaderSet E α) (k : α → ReaderSet E β) :
    (monadLift m : ContT β (ReaderSet E) α).run k = fun s ↦ ⋃ x ∈ m s, k x s := by
  funext s; ext; simp

end ReaderSet

theorem run_monadLift (m : StateSet E α) (k : α → StateSet E β) :
    (monadLift m : Tower E β α).run k = fun s ↦ ⋃ q ∈ m s, k q.1 q.2 := by
  funext s; ext; simp

end Charlow2014
