module

public import Linglib.Data.Examples.Grove2022
public import Mathlib.Data.Option.Basic
public import Mathlib.Tactic.SplitIfs

/-!
# Grove (2022): Presupposition Projection as a Scope Phenomenon

This file formalizes Grove's scope theory of presupposition projection, on which a presupposition
trigger denotes a value of a maybe type, undefined on presupposition failure, and its presupposition
projects to the constituent over which it takes scope. The maybe types are `Option`, whose unit and
bind are the type shifts of (15); the intensional monad of section 4.1 is the reader transformer
over it, as the paper's footnote says (`Iₚ`); the connective of (16) is the middle Kleene material
conditional (`materialCond`); the presuppositional universal of (27) is undefined wherever its scope
is; and *believe* is the Hintikka quantifier (28) over them. The proviso problem of section 2.1 then
dissolves into a scope ambiguity. For *If Theo has a brother, he'll bring his wetsuit*, the trigger
in situ yields the conditional presupposition of the satisfaction theory
(`localReading_isSome_iff`), the consequent pied-piped over the conditional yields the unconditional
one (`globalReading_isSome_iff`), and the two readings agree wherever the global one is defined. For
*Theo believes he lost his wetsuit*, section 4.2, the clause in situ presupposes a wetsuit at every
doxastic alternative and the clause scoped above the verb a wetsuit at the evaluation index, with
the at-issue content reconstructing by Left Identity (`believeGlobal_eq_some_true_iff`).

## Implementation notes

The truth-value type is `Bool`, so the possibly undefined truth values are `Option Bool`, the
library's `SignType` in monadic form, and the predicates of the models are decidable
propositions turned into truth values by `decide`. The universal of (27) quantifies over a whole
type and is defined classically. The readings are stated for arbitrary index and entity types,
the trigger *his wetsuit* being an `Iₚ I E` value, so the presupposition theorems are general
rather than checked on a finite model. The monad laws of Figure 7 are Lean's lawful-monad
instance for the reader transformer. The paper's judged sentences are rows of
`Data.Examples.Grove2022`.

## References

* [grove-2022]
* [heim-1983]
* [heim-1992]
* [charlow-2020]
* [beaver-krahmer-2001]

## TODO

The syntax of roll-up pied-piping in Figures 2 and 6 and the sketched *also* of (29) are not
represented; the readings are the meanings the derivations deliver.
-/

@[expose] public section

namespace Grove2022

variable {I E : Type}

/-- The intensional presuppositional monad `I#` of section 4.1, a reader over the maybe monad. -/
abbrev Iₚ (I : Type) := ReaderT I Option

/-- The monad laws of Figure 7 hold for `I#`. Left Identity is semantic reconstruction, and
Associativity is what licenses cyclic scope. -/
theorem monad_laws {α β γ : Type} (v : α) (m : Iₚ I α) (k : α → Iₚ I β) (n : β → Iₚ I γ) :
    (pure v >>= k) = k v ∧ (m >>= pure) = m ∧ (m >>= k >>= n) = (m >>= fun x ↦ k x >>= n) :=
  ⟨pure_bind v k, bind_pure m, bind_assoc m k n⟩

/-- The material conditional of (16) has middle Kleene semantics, in which an undefined antecedent
absorbs and a false one makes the conditional true whatever the consequent. -/
def materialCond : Option Bool → Option Bool → Option Bool
  | none, _ => none
  | some false, _ => some true
  | some true, ψ => ψ

theorem materialCond_decide (P : Prop) [Decidable P] (ψ : Option Bool) :
    materialCond (some (decide P)) ψ = if P then ψ else some true := by
  by_cases h : P <;> simp [h, materialCond]

open Classical in
/-- The presuppositional universal of (27) is true if its scope is true everywhere, undefined if
its scope is undefined somewhere, and false otherwise. -/
noncomputable def forallP {α : Type*} (φ : α → Option Bool) : Option Bool :=
  if ∃ x, φ x = none then none else if ∀ x, φ x = some true then some true else some false

theorem forallP_eq_none_iff {α : Type*} (φ : α → Option Bool) :
    forallP φ = none ↔ ∃ x, φ x = none := by
  unfold forallP
  split_ifs with h₁ h₂ <;> simp [h₁]

theorem forallP_eq_some_true_iff {α : Type*} (φ : α → Option Bool) :
    forallP φ = some true ↔ ∀ x, φ x = some true := by
  unfold forallP
  split_ifs with h₁ h₂
  · obtain ⟨x, hx⟩ := h₁
    simp only [false_iff, not_forall]
    exact ⟨x, by simp [hx]⟩
  · simp [h₂]
  · simp [h₂]

theorem forallP_isSome_iff {α : Type*} (φ : α → Option Bool) :
    (forallP φ).isSome ↔ ∀ x, (φ x).isSome := by
  simp only [Option.isSome_iff_ne_none, ne_eq, forallP_eq_none_iff, not_exists]

/-- The evaluation of (20) identifies the index an `I# (i → t)` value reads with the index of
the intension it returns. -/
def evalI (φ : Iₚ I (I → Bool)) : Iₚ I Bool := fun i ↦ (φ i).map (· i)

/-- The *believe* of (28) is the Hintikka quantifier over doxastic alternatives, the conditional
filtering the inaccessible indices. -/
noncomputable def believe (dox : E → I → I → Prop) [∀ x i j, Decidable (dox x i j)]
    (φ : Iₚ I Bool) (x : E) : Iₚ I Bool :=
  fun i ↦ forallP fun j ↦ materialCond (some (decide (dox x i j))) (φ j)

/-! ### The conditional, section 3

*If Theo has a brother, he'll bring his wetsuit*, (1): `bro` is the antecedent, `wetsuit` the
trigger *his wetsuit*, Theo's unique wetsuit at an index if he has one, and `bring` the
predicate. -/

section Conditional

variable (bro : I → Prop) [DecidablePred bro] (wetsuit : Iₚ I E) (bring : E → I → Prop)
  [∀ x i, Decidable (bring x i)]

/-- The consequent with the trigger scoped to its edge, as in Figure 5, is the lifted trigger over
the abstracted clause, of type `t#`. -/
def consequent : Iₚ I Bool := fun i ↦ wetsuit i >>= fun x ↦ pure (decide (bring x i))

/-- The local reading of (1), in Figure 5, applies the conditional to the consequent. -/
def localReading : Iₚ I Bool :=
  fun i ↦ materialCond (some (decide (bro i))) (consequent wetsuit bring i)

/-- In the global reading of (1), Figure 6, the consequent, of type `t##` after two units in the
trigger's scope, takes scope over the conditional. -/
def globalReading : Iₚ I Bool := fun i ↦
  (wetsuit i >>= fun x ↦ pure (pure (decide (bring x i)))) >>= fun ψ ↦
    materialCond (some (decide (bro i))) ψ

/-- The local reading is undefined exactly when Theo has a brother but no wetsuit, the
conditional presupposition of the satisfaction theory in Figure 3. -/
theorem localReading_eq_none_iff (i : I) :
    localReading bro wetsuit bring i = none ↔ bro i ∧ wetsuit i = none := by
  simp only [localReading, consequent, materialCond_decide]
  cases wetsuit i <;> split_ifs <;> simp_all

theorem localReading_eq_some_true_iff (i : I) :
    localReading bro wetsuit bring i = some true ↔
      (bro i → ∃ x, wetsuit i = some x ∧ bring x i) := by
  simp only [localReading, consequent, materialCond_decide]
  cases wetsuit i <;> split_ifs <;> simp_all

theorem localReading_isSome_iff (i : I) :
    (localReading bro wetsuit bring i).isSome ↔ (bro i → (wetsuit i).isSome) := by
  simp only [Option.isSome_iff_ne_none, ne_eq, localReading_eq_none_iff, not_and]

/-- The global reading is undefined exactly when Theo has no wetsuit, the unconditional
presupposition of Figure 4, available without pragmatic strengthening. -/
theorem globalReading_eq_none_iff (i : I) :
    globalReading bro wetsuit bring i = none ↔ wetsuit i = none := by
  simp only [globalReading, materialCond_decide]
  cases wetsuit i <;> split_ifs <;> simp_all

theorem globalReading_eq_some_true_iff (i : I) :
    globalReading bro wetsuit bring i = some true ↔
      ∃ x, wetsuit i = some x ∧ (bro i → bring x i) := by
  simp only [globalReading, materialCond_decide]
  cases wetsuit i <;> split_ifs <;> simp_all

theorem globalReading_isSome_iff (i : I) :
    (globalReading bro wetsuit bring i).isSome ↔ (wetsuit i).isSome := by
  simp only [Option.isSome_iff_ne_none, ne_eq, globalReading_eq_none_iff]

theorem globalReading_eq_localReading_of_isSome (i : I) (h : (wetsuit i).isSome) :
    globalReading bro wetsuit bring i = localReading bro wetsuit bring i := by
  simp only [globalReading, localReading, consequent, materialCond_decide]
  cases hw : wetsuit i <;> split_ifs <;> simp_all

/-- By Left Identity, a unit applied outside the trigger's scope gives the local reading (footnote
on Figure 6). -/
theorem reconstruct (i : I) :
    (pure (consequent wetsuit bring i) >>= fun ψ ↦ materialCond (some (decide (bro i))) ψ) =
      localReading bro wetsuit bring i :=
  pure_bind _ _

end Conditional

/-! ### Propositional attitudes, section 4.2

*Theo believes he lost his wetsuit*, (22): the complement is derived with intensions, Figure 8,
and either evaluated in situ under the verb, Figure 9, or scoped above it, Figure 10. -/

section Attitude

variable (dox : E → I → I → Prop) [∀ x i j, Decidable (dox x i j)] (wetsuit : Iₚ I E)
  (lose : E → I → Prop) [∀ x i, Decidable (lose x i)] (theo : E)

/-- *he lost his wetsuit* with the trigger scoped over the clause, an `I# (i → t)` value. -/
def lostClause : Iₚ I (I → Bool) := fun j ↦ wetsuit j >>= fun x ↦ pure fun i ↦ decide (lose x i)

/-- The local reading of (22), in Figure 9, evaluates the complement under *believe*. -/
noncomputable def believeLocal : Iₚ I Bool := believe dox (evalI (lostClause wetsuit lose)) theo

/-- In the global reading of (22), Figure 10, the clause scopes above the verb through the reader
bind, its trigger read at the evaluation index. -/
noncomputable def believeGlobal : Iₚ I Bool :=
  lostClause wetsuit lose >>= fun φ ↦ believe dox (fun j ↦ pure (φ j)) theo

/-- Evaluating the clause as in (21) makes the trigger and the predicate read the same index. -/
theorem evalI_lostClause (j : I) :
    evalI (lostClause wetsuit lose) j = wetsuit j >>= fun x ↦ pure (decide (lose x j)) := by
  simp only [evalI, lostClause]
  cases wetsuit j <;> rfl

/-- In situ, the presupposition is that Theo has a wetsuit at every doxastic alternative, the
prediction of [heim-1992] for (22). -/
theorem believeLocal_isSome_iff (i : I) :
    (believeLocal dox wetsuit lose theo i).isSome ↔
      ∀ j, dox theo i j → (wetsuit j).isSome := by
  simp only [believeLocal, believe, forallP_isSome_iff, evalI_lostClause, materialCond_decide]
  refine forall_congr' fun j ↦ ?_
  cases wetsuit j <;> split_ifs <;> simp_all

theorem believeLocal_eq_some_true_iff (i : I) :
    believeLocal dox wetsuit lose theo i = some true ↔
      ∀ j, dox theo i j → ∃ x, wetsuit j = some x ∧ lose x j := by
  simp only [believeLocal, believe, forallP_eq_some_true_iff, evalI_lostClause,
    materialCond_decide]
  refine forall_congr' fun j ↦ ?_
  cases wetsuit j <;> split_ifs <;> simp_all

theorem believeGlobal_isSome_iff (i : I) :
    (believeGlobal dox wetsuit lose theo i).isSome ↔ (wetsuit i).isSome := by
  show (lostClause wetsuit lose i >>= fun φ ↦ believe dox (fun j ↦ pure (φ j)) theo i).isSome ↔ _
  simp only [lostClause, believe, materialCond_decide]
  cases wetsuit i
  · rfl
  · simp only [Option.pure_def, Option.bind_eq_bind, Option.bind, Option.isSome_some,
      forallP_isSome_iff, iff_true]
    intro j
    split_ifs <;> rfl

theorem believeGlobal_eq_some_true_iff (i : I) :
    believeGlobal dox wetsuit lose theo i = some true ↔
      ∃ x, wetsuit i = some x ∧ ∀ j, dox theo i j → lose x j := by
  show (lostClause wetsuit lose i >>= fun φ ↦ believe dox (fun j ↦ pure (φ j)) theo i) =
    some true ↔ _
  simp only [lostClause, believe, materialCond_decide]
  cases wetsuit i
  · simp
  · simp only [Option.pure_def, Option.bind_eq_bind, Option.bind, Option.some.injEq,
      exists_eq_left', forallP_eq_some_true_iff]
    refine forall_congr' fun j ↦ ?_
    split_ifs <;> simp_all

end Attitude

end Grove2022
