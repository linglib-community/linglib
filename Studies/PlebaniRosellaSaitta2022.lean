module

public import Linglib.Logic.Truthmaker.Exclusion
public import Mathlib.Tactic.FinCases

/-!
# Plebani, Rosella and Saitta (2022): Truthmakers, incompatibility, and modality

Plebani, Rosella and Saitta build truthmaker semantics on a primitive, symmetric relation of exact
incompatibility between states in place of Fine's primitive set of possible states. Two states are
inexactly incompatible when a part of one is exactly incompatible with a part of the other
(`Truthmaker.Conflict`) and compatible otherwise, and a state is possible when it is compatible
with itself (`Truthmaker.possible`). Compatibility passes to parts (Claim 1,
`Truthmaker.Conflict.mono`), and a state is possible exactly when its parts are pairwise
compatible (Claim 2, `Truthmaker.mem_possible_iff_forall`). In the canonical model a literal is
exactly incompatible with its mirror image, and the possible states are the consistent sets of
literals (`Truthmaker.Canonical.possible_excl`).

A state is maximal with respect to compatibility when it contains every state compatible with it
(`MaximalCompat`), and maximal with respect to parthood when no possible state properly contains
it. The first implies the second (`maximal_of_maximalCompat`, Claim 3) but not conversely
(`maximal_counterExcl`, `not_maximalCompat_counterExcl`). Fine's condition that compatible states
have a possible fusion restores the converse (`maximalCompat_of_maximal`, Claim 4), but it makes
the null state incompatible with every impossible state (`conflict_bot_of_not_mem_possible`).
Possible Fusion instead equates maximality with respect to parthood with a weaker maximality with
respect to compatibility (`maximal_iff_weakMaximalCompat`, Claim 5).

The falsifiers of an atomic formula are the states exactly incompatible with all its verifiers,
and the connectives follow Fine's bilateral clauses (`denote`). Every verifier of a formula is
then inexactly incompatible with every falsifier (`conflict_of_mem_ver_of_mem_fal`, Theorem 1), so
no possible state verifies a contradiction (`not_mem_possible_of_mem_ver_conj_neg`, Corollary 1).

## Implementation notes

States form a complete lattice. Maximality with respect to parthood is mathlib's `Maximal` among
the possible states, which is the paper's definition for possible states, the only ones its claims
about it concern. The applications to first-degree entailment, the Routley star and Kripke frames
(§§4–5) are not formalized.

## References

* [M. Plebani, G. Rosella and V. Saitta, *Truthmakers, Incompatibility, and Modality*
  (2022)][plebani-rosella-saitta-2022]
* [K. Fine, *A Theory of Truthmaker Content I: Conjunction, Disjunction and Negation*
  (2017)][fine-2017a]
-/

@[expose] public section

open SetFamily Truthmaker

namespace PlebaniRosellaSaitta2022

variable {S A : Type*} [CompleteLattice S] {excl : S → S → Prop} {s t : S}

/-! ### Possible worlds -/

variable (excl) in
/-- A state is maximal with respect to compatibility when every state compatible with it is part
of it (def. 10). -/
def MaximalCompat (s : S) : Prop :=
  ∀ ⦃u⦄, ¬ Conflict excl u s → u ≤ s

variable (excl) in
/-- A state is weakly maximal with respect to compatibility when every possible state compatible
with it is part of it (def. 13). -/
def WeakMaximalCompat (s : S) : Prop :=
  ∀ ⦃u⦄, u ∈ possible excl → ¬ Conflict excl u s → u ≤ s

/-- A possible state that is maximal with respect to compatibility is maximal with respect to
parthood (Claim 3). -/
theorem maximal_of_maximalCompat (hs : s ∈ possible excl) (h : MaximalCompat excl s) :
    Maximal (· ∈ possible excl) s :=
  ⟨hs, fun _ hu hsu ↦ h fun hc ↦ hu (hc.mono le_rfl hsu)⟩

/-- If compatible states have a possible fusion, a state that is maximal with respect to parthood
is maximal with respect to compatibility (Claim 4). -/
theorem maximalCompat_of_maximal
    (hF : ∀ ⦃s t : S⦄, ¬ Conflict excl s t → s ⊔ t ∈ possible excl)
    (hs : Maximal (· ∈ possible excl) s) : MaximalCompat excl s :=
  fun _ hu ↦ le_sup_left.trans (hs.le_of_ge (hF hu) le_sup_right)

theorem conflict_bot_of_not_mem_possible
    (hF : ∀ ⦃s t : S⦄, ¬ Conflict excl s t → s ⊔ t ∈ possible excl) (ht : t ∉ possible excl) :
    Conflict excl ⊥ t :=
  by_contra fun hc ↦ ht (by simpa using hF hc)

/-- Under Possible Fusion, a possible state is maximal with respect to parthood exactly when it is
weakly maximal with respect to compatibility (Claim 5). -/
theorem maximal_iff_weakMaximalCompat (hR : PossibleFusion excl) (hs : s ∈ possible excl) :
    Maximal (· ∈ possible excl) s ↔ WeakMaximalCompat excl s :=
  ⟨fun h _ hu hc ↦ le_sup_left.trans (h.le_of_ge (hR hu hs hc) le_sup_right),
    fun h ↦ ⟨hs, fun _ hu hsu ↦ h hu fun hc ↦ hu (hc.mono le_rfl hsu)⟩⟩

/-! ### Maximality with respect to parthood without compatibility -/

/-- The exact incompatibility of the paper's counterexample on the subsets of `{0, 1}`, under which
only `{1}` is incompatible, and only with itself. -/
def counterExcl (a b : Set (Fin 2)) : Prop :=
  a = {1} ∧ b = {1}

instance : Std.Symm counterExcl :=
  ⟨fun _ _ h ↦ h.symm⟩

theorem conflict_counterExcl_iff {a b : Set (Fin 2)} :
    Conflict counterExcl a b ↔ 1 ∈ a ∧ 1 ∈ b := by
  constructor
  · rintro ⟨_, ha, _, hb, rfl, rfl⟩
    exact ⟨ha rfl, hb rfl⟩
  · rintro ⟨ha, hb⟩
    exact ⟨{1}, Set.singleton_subset_iff.2 ha, {1}, Set.singleton_subset_iff.2 hb, rfl, rfl⟩

theorem maximal_counterExcl : Maximal (· ∈ possible counterExcl) {0} := by
  refine ⟨by simp [mem_possible, conflict_counterExcl_iff], fun u hu h0u x hx ↦ ?_⟩
  simp only [mem_possible, conflict_counterExcl_iff, and_self] at hu
  fin_cases x
  · rfl
  · exact absurd hx hu

theorem not_maximalCompat_counterExcl : ¬ MaximalCompat counterExcl {0} := fun h ↦ by
  have := h (u := {1}) (by simp [conflict_counterExcl_iff])
  simp at this

/-! ### Formulas -/

/-- The formulas of a propositional language over atoms `A`. -/
inductive Formula (A : Type*)
  | atom (a : A)
  | neg (φ : Formula A)
  | conj (φ ψ : Formula A)
  | disj (φ ψ : Formula A)

variable (excl) in
/-- The bilateral proposition a formula expresses when `V` assigns verifiers to the atoms. An atom
is falsified by the states exactly incompatible with all its verifiers, and the connectives follow
Fine's bilateral clauses (def. 8). -/
def denote (V : A → Set S) : Formula A → BilProp S
  | .atom a => ⟨V a, {s | ∀ t ∈ V a, excl s t}⟩
  | .neg φ => -denote V φ
  | .conj φ ψ => (denote V φ).conj (denote V ψ)
  | .disj φ ψ => (denote V φ).disj (denote V ψ)

/-- Every verifier of a formula is inexactly incompatible with every falsifier of it
(Theorem 1). -/
theorem conflict_of_mem_ver_of_mem_fal [Std.Symm excl] (V : A → Set S) (φ : Formula A)
    (hs : s ∈ (denote excl V φ).ver) (ht : t ∈ (denote excl V φ).fal) : Conflict excl s t := by
  induction φ generalizing s t with
  | atom a => exact (Conflict.of_excl (ht s hs)).symm
  | neg φ ih => exact (ih ht hs).symm
  | conj φ ψ ihφ ihψ =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hs
    rcases ht with ht | ht
    · exact (ihφ ha ht).mono le_sup_left le_rfl
    · exact (ihψ hb ht).mono le_sup_right le_rfl
  | disj φ ψ ihφ ihψ =>
    obtain ⟨a, ha, b, hb, rfl⟩ := ht
    rcases hs with hs | hs
    · exact (ihφ hs ha).mono le_rfl le_sup_left
    · exact (ihψ hs hb).mono le_rfl le_sup_right

/-- No possible state verifies a contradiction (Corollary 1). -/
theorem not_mem_possible_of_mem_ver_conj_neg [Std.Symm excl] (V : A → Set S) (φ : Formula A)
    (hs : s ∈ (denote excl V (.conj φ (.neg φ))).ver) : s ∉ possible excl := by
  obtain ⟨a, ha, b, hb, rfl⟩ := hs
  exact fun hp ↦ hp ((conflict_of_mem_ver_of_mem_fal V φ ha hb).mono le_sup_left le_sup_right)

end PlebaniRosellaSaitta2022
