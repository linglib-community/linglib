module

public import Linglib.Semantics.Quantifier.Exceptive
public import Linglib.Semantics.Quantifier.Global
public import Linglib.Data.Examples.VonFintel1993
public import Linglib.Languages.English.Determiners
public import Mathlib.Tactic.FinCases
public import Linglib.Data.Examples.Readers

/-!
# von Fintel (1993): Exceptive Constructions

An exceptive subtracts a set `C` from the restrictor `A` of a quantification `Q A B`. A free
exceptive, as in *except for John, every student attended*, asserts that the quantification holds
of `A \ C` and fails of `A`. A *but*-phrase, as in *every student but John attended*, asserts
further that `C` is the exception set of the quantification, the least set whose subtraction makes
it true. With *every* the exception set is `A \ B` and with *no* it is `A ∩ B`.

A determiner guarantees an exception set when every false quantification with it has one. Among
the eight determiner symbols of the library only *every* and *no* do, and a *but*-phrase is
acceptable with exactly the determiners that do. A free exceptive carries no uniqueness condition
and is contradictory only with *some*, which is upward monotone in its restrictor.

## Implementation notes

* Restrictor, scope and exception set are sets, and the five-student and two-student models are
  `Fin 5` and `Fin 2` with the restrictor `Set.univ`.
* The guarantee is conditional on a false quantification, "if there is any at all". A true
  quantification with *every* or *no* also has an exception set, the empty one.
* An exception set that is empty is not restrictive, so the uniqueness condition yields
  restrictiveness only for a nonempty exception set.
* *Both* and *neither* assert that the restrictor has two members, so a false quantification
  with a restrictor of another size has no exception set and they do not guarantee one.
* The determiner of an example is matched by its form against the English determiners. The
  indefinite pronouns of the paradigm from Horn (*everyone*, *nobody*, *somebody*), *any*, the
  definite of *except for Jane, my relatives* and the numeral of the *besides* example match no
  determiner with a reading and are not predicted.
* The examples include no unacceptable free exceptive, so the second prediction is tested only
  on acceptable examples.
* The strengthening of a free exceptive to the *but* reading takes as hypothesis that the
  exception set contains only exceptions, which pragmatics supplies.
* Not formalized: the two curryings of the *but*-phrase, the exclusion of a noun-phrase modifier
  semantics, the Cooper variable, and the rhetorical reading of *who but*.

## References

* [von-fintel-1993]
* [keenan-stavi-1986]
* [hoeksema-1987]
* [horn-1989]
-/

@[expose] public section

namespace VonFintel1993

open Quantifier Quantifier.Det Quantifier.Exceptive
open scoped Denotes

variable {α : Type*} {Q : Det α} {A C B S T : Set α}

/-! ### Consequences of uniqueness (§1.5, §1.7) -/

-- (24)
theorem not_isExceptionSet_of_ssubset (h : IsExceptionSet Q A C B) {C' : Set α} (hlt : C ⊂ C') :
    ¬ IsExceptionSet Q A C' B :=
  fun h' ↦ hlt.ne (h.unique h')

-- (28)
theorem eq_of_isExceptionSet_singleton {j m : α} (hj : IsExceptionSet Q A {j} B)
    (hm : IsExceptionSet Q A {m} B) : j = m :=
  Set.singleton_injective (hj.unique hm)

/-- A false quantification that two disjoint subtractions each make true has no exception set:
there is a choice of what to exclude (§1.6). -/
theorem not_isExceptionSet_of_disjoint (h : ¬ Q A B) (hS : Q (A \ S) B) (hT : Q (A \ T) B)
    (hd : Disjoint S T) : ¬ IsExceptionSet Q A C B := fun hC ↦
  h <| by simpa [(hd.mono (hC.2 hS) (hC.2 hT)).eq_bot_of_self] using hC.1

/-! ### The co-occurrence restrictions (§1.6) -/

/-- A determiner guarantees an exception set when every false quantification has one. -/
def GuaranteesException (Q : Det α) : Prop :=
  ∀ A B : Set α, ¬ Q A B → ∃ C, IsExceptionSet Q A C B

theorem guaranteesException_every : GuaranteesException (every : Det α) :=
  fun A B _ ↦ ⟨A \ B, isExceptionSet_every A B⟩

theorem guaranteesException_no : GuaranteesException (no : Det α) :=
  fun A B _ ↦ ⟨A ∩ B, isExceptionSet_no A B⟩

theorem not_guaranteesException_some [Nonempty α] : ¬ GuaranteesException (Det.some : Det α) :=
  fun h ↦
    let ⟨_, ⟨_, _, hx⟩, _⟩ := h Set.univ ∅ fun ⟨_, _, hx⟩ ↦ hx
    hx

/-- The five students of (25) are Tom, John, Harry, Bill and Mary in order; only the last two
attended (`Examples.ex_25a`). -/
abbrev attended : Set (Fin 5) := {x | 3 ≤ x}

-- (25)
theorem not_isExceptionSet_most (C : Set (Fin 5)) :
    ¬ IsExceptionSet most Set.univ C attended := by
  rintro ⟨h1, h2⟩
  have hTJ : most (Set.univ \ {0, 1}) attended := by decide
  have hTH : most (Set.univ \ {0, 2}) attended := by decide
  have hJH : most (Set.univ \ {1, 2}) attended := by decide
  have hC : C = ∅ := Set.eq_empty_of_forall_notMem fun x hx ↦ by
    have h01 : x = 0 ∨ x = 1 := h2 hTJ hx
    have h02 : x = 0 ∨ x = 2 := h2 hTH hx
    have h12 : x = 1 ∨ x = 2 := h2 hJH hx
    omega
  subst hC
  have h1' : most (Set.univ \ ∅) attended := h1
  rw [Set.sdiff_empty] at h1'
  exact absurd h1' (by decide)

theorem not_guaranteesException_most : ¬ GuaranteesException (most : Det (Fin 5)) := fun h ↦
  let ⟨C, hC⟩ := h Set.univ attended fun hm ↦ absurd hm (by decide)
  not_isExceptionSet_most C hC

-- §1.6
theorem isExceptionSet_most_two :
    IsExceptionSet most Set.univ {(0 : Fin 2)} {(1 : Fin 2)} := by
  refine ⟨by decide, fun S hS x hx ↦ ?_⟩
  obtain rfl : x = 0 := hx
  have hS' : most (Set.univ \ S) {(1 : Fin 2)} := hS
  by_contra h0
  by_cases h1 : 1 ∈ S
  · have e : Set.univ \ S = {(0 : Fin 2)} :=
      Set.ext fun x ↦ by fin_cases x <;> simp [h0, h1]
    rw [e] at hS'
    exact absurd hS' (by decide)
  · have e : Set.univ \ S = Set.univ := Set.ext fun x ↦ by fin_cases x <;> simp [h0, h1]
    rw [e] at hS'
    exact absurd hS' (by decide)

theorem not_guaranteesException_few : ¬ GuaranteesException (few : Det (Fin 1)) := fun h ↦
  let ⟨C, hC⟩ := h Set.univ Set.univ (by decide)
  absurd hC.1 (by simp [few_apply])

theorem not_guaranteesException_half : ¬ GuaranteesException (half : Det (Fin 3)) := fun h ↦
  let ⟨_, hC⟩ := h Set.univ {0, 1} (by decide)
  not_isExceptionSet_of_disjoint (S := {0}) (T := {1}) (by decide) (by decide) (by decide)
    (by simp) hC

private theorem ncard_ne_two (S : Set (Fin 1)) : S.ncard ≠ 2 := fun h ↦ by
  have := Set.ncard_le_ncard (Set.subset_univ S)
  rw [h, Set.ncard_univ, Nat.card_fin] at this
  omega

theorem not_guaranteesException_both : ¬ GuaranteesException (both : Det (Fin 1)) := fun h ↦
  let ⟨_, hC⟩ := h Set.univ Set.univ fun hb ↦ ncard_ne_two _ hb.2
  ncard_ne_two _ hC.1.2

theorem not_guaranteesException_neither : ¬ GuaranteesException (neither : Det (Fin 1)) :=
  fun h ↦
    let ⟨_, hC⟩ := h Set.univ ∅ fun hb ↦ ncard_ne_two _ hb.1
    ncard_ne_two _ hC.1.1

/-- Among the determiner symbols, those that guarantee an exception set on every finite universe
are *every* and *no*. -/
theorem guaranteesException_denote_iff (s : Det.Symbol) :
    (∀ (β : Type) [Finite β], GuaranteesException ((s.denote : Det.Family.{0}) β)) ↔
      s = .every ∨ s = .no := by
  cases s
  · exact iff_of_true (fun _ _ ↦ guaranteesException_every) (.inl rfl)
  · exact iff_of_false (fun h ↦ not_guaranteesException_some (h (Fin 1))) (by decide)
  · exact iff_of_true (fun _ _ ↦ guaranteesException_no) (.inr rfl)
  · exact iff_of_false (fun h ↦ not_guaranteesException_most (h (Fin 5))) (by decide)
  · exact iff_of_false (fun h ↦ not_guaranteesException_few (h (Fin 1))) (by decide)
  · exact iff_of_false (fun h ↦ not_guaranteesException_half (h (Fin 3))) (by decide)
  · exact iff_of_false (fun h ↦ not_guaranteesException_both (h (Fin 1))) (by decide)
  · exact iff_of_false (fun h ↦ not_guaranteesException_neither (h (Fin 1))) (by decide)

/-! ### What *but* operates on (§1.8) -/

-- §1.8
theorem not_exists_nounModifier (hC : C ≠ ∅) :
    ¬ ∃ f : Set α → Set α, ∀ A B, every (f A) B ↔ IsExceptionSet every A C B :=
  fun ⟨_, hf⟩ ↦ hC ((isExceptionSet_every_iff.1 ((hf ∅ Set.univ).1 (Set.subset_univ _))).symm.trans
    (Set.empty_sdiff _))

/-! ### Free exceptives (§2) -/

-- (25), (34c)
theorem restrictive_most :
    Restrictive most Set.univ {0, 1} attended :=
  ⟨by decide, fun h ↦ absurd h (by decide)⟩

/-- Among the determiner symbols, those that admit a restrictive subtraction on some finite
universe are all but *some*, which is upward monotone in its restrictor (§1.4). -/
theorem exists_restrictive_denote_iff (s : Det.Symbol) :
    (∃ (β : Type) (_ : Finite β) (A C B : Set β),
        Restrictive ((s.denote : Det.Family.{0}) β) A C B) ↔ s ≠ .some := by
  cases s
  · exact iff_of_true ⟨Fin 1, inferInstance, Set.univ, Set.univ, ∅,
      fun _ hx ↦ hx.2 trivial, fun h ↦ h (Set.mem_univ (0 : Fin 1))⟩ (by decide)
  · exact iff_of_false (fun ⟨_, _, _, _, _, h⟩ ↦ h.not_of_restrictorMonotone
      restrictorMonotone_some) (by decide)
  · exact iff_of_true ⟨Fin 1, inferInstance, Set.univ, Set.univ, Set.univ,
      fun _ hx _ ↦ hx.2 trivial, fun h ↦ h (Set.mem_univ (0 : Fin 1)) trivial⟩ (by decide)
  · exact iff_of_true ⟨Fin 5, inferInstance, Set.univ, {0, 1}, attended, restrictive_most⟩
      (by decide)
  · exact iff_of_true ⟨Fin 2, inferInstance, Set.univ, {0}, {0},
      show Restrictive (few : Det (Fin 2)) _ _ _ from ⟨by decide, by decide⟩⟩
      (by decide)
  · exact iff_of_true ⟨Fin 3, inferInstance, Set.univ, {0}, {0, 1},
      show Restrictive (half : Det (Fin 3)) _ _ _ from ⟨by decide, by decide⟩⟩
      (by decide)
  · exact iff_of_true ⟨Fin 3, inferInstance, Set.univ, {0}, Set.univ,
      show Restrictive (both : Det (Fin 3)) _ _ _ from ⟨by decide, by decide⟩⟩
      (by decide)
  · exact iff_of_true ⟨Fin 3, inferInstance, Set.univ, {0}, ∅,
      show Restrictive (neither : Det (Fin 3)) _ _ _ from ⟨by decide, by decide⟩⟩
      (by decide)

-- §2.3
theorem isExceptionSet_every_of_restrictive (h : Restrictive every A C B) (hC : C ⊆ A \ B) :
    IsExceptionSet every A C B :=
  isExceptionSet_every_iff.2 (le_antisymm (restrictive_every_iff.1 h).1 hC)

-- §2.3
theorem isExceptionSet_no_of_restrictive (h : Restrictive no A C B) (hC : C ⊆ A ∩ B) :
    IsExceptionSet no A C B :=
  isExceptionSet_no_iff.2 (le_antisymm (restrictive_no_iff.1 h).1 hC)

/-! ### The paper's examples -/

/-- A *but*-phrase is acceptable with an English determiner if and only if every reading of the
determiner guarantees an exception set on every finite universe ((1a), (2b), (10), (22),
(25b)). -/
theorem but_predicted :
    ∀ e ∈ Examples.all, Examples.exceptive e = some .but →
      ∀ d ∈ English.Determiners.allQuantifiers, d.readings.Nonempty →
        e.feature? "determiner" = some d.form →
          (e.judgment = .acceptable ↔
            ∀ q ∈ (⟦d⟧ : Set Det.Family.{0}), ∀ (β : Type) [Finite β],
              GuaranteesException (q β)) := by
  have key (d : QuantificationalDeterminer) :
      (∀ q ∈ (⟦d⟧ : Set Det.Family.{0}), ∀ (β : Type) [Finite β], GuaranteesException (q β)) ↔
        ∀ s ∈ d.readings, s = .every ∨ s = .no := by
    simp only [QuantificationalDeterminer.mem_denote_iff, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, guaranteesException_denote_iff]
  simp only [key]
  decide

/-- A free exceptive is acceptable with an English determiner if and only if every reading of the
determiner admits a restrictive subtraction on some finite universe ((1b), (33a), (34a),
(34c)). -/
theorem exceptFor_predicted :
    ∀ e ∈ Examples.all, Examples.exceptive e = some .exceptFor →
      ∀ d ∈ English.Determiners.allQuantifiers, d.readings.Nonempty →
        e.feature? "determiner" = some d.form →
          (e.judgment = .acceptable ↔
            ∀ q ∈ (⟦d⟧ : Set Det.Family.{0}), ∃ (β : Type) (_ : Finite β) (A C B : Set β),
              Restrictive (q β) A C B) := by
  have key (d : QuantificationalDeterminer) :
      (∀ q ∈ (⟦d⟧ : Set Det.Family.{0}), ∃ (β : Type) (_ : Finite β) (A C B : Set β),
        Restrictive (q β) A C B) ↔ ∀ s ∈ d.readings, s ≠ .some := by
    simp only [QuantificationalDeterminer.mem_denote_iff, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, exists_restrictive_denote_iff]
  simp only [key]
  decide

end VonFintel1993
