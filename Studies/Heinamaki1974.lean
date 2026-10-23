module

public import Studies.Anscombe1964

/-!
# Heinämäki (1974): Semantics of English Temporal Connectives

Heinämäki gives the truth conditions of the English temporal connectives in terms of the times at
which the two clauses hold. On run-time denotations they are relations between the clauses' time
traces: *A when B* asserts that the two hold at a common time (`when_`), *A while B* that every
time of `A` is a time of `B` (`while_`), *A whenever B* the converse containment (`whenever`),
*A since B* that some time of `B` lies at or before every time of `A` (`since`), and *A by B* that
some time of `A` lies at or before every time of `B` (`by_`). *Since* and *by* are the non-strict
counterparts of Anscombe's quantificational *before*, with the roles of the clauses exchanged, so
*before ever* entails *by* but not conversely (`before_by`, `by_not_before`). At a single time of
the main clause *before* is the negation of *when* and *after*, and *by* the negation of *after*
(`beforeEver_iff_exists_not_when_not_after`, `by_iff_exists_not_after`), so the two hold of a
temporal clause that never happens. The existential connectives commit the speaker to both
clauses; the universal ones do so only given the clause they quantify over, and are not symmetric
(`while_not_symm`).

## References

* [heinamaki-1974]
* [anscombe-1964]
-/

@[expose] public section

namespace Heinamaki1974

open Tense Anscombe1964 NonemptyInterval

variable {T : Type*} [LinearOrder T] (A B : Set (NonemptyInterval T))

/-- *A when B* holds when `A` and `B` hold at a common time. -/
def when_ : Prop := ∃ t, t ∈ timeTrace A ∧ t ∈ timeTrace B

/-- *A while B* holds when every time of `A` is a time of `B`. -/
def while_ : Prop := ∀ t ∈ timeTrace A, t ∈ timeTrace B

/-- *A whenever B* holds when every time of `B` is a time of `A`. -/
def whenever : Prop := ∀ t ∈ timeTrace B, t ∈ timeTrace A

/-- *A since B* holds when some time of `B` is at or before every time of `A`. -/
def since : Prop := ∃ t ∈ timeTrace B, ∀ t' ∈ timeTrace A, t ≤ t'

/-- *A by B* holds when some time of `A` is at or before every time of `B`. -/
def by_ : Prop := ∃ t ∈ timeTrace A, ∀ t' ∈ timeTrace B, t ≤ t'

theorem when_comm : when_ A B ↔ when_ B A :=
  ⟨fun ⟨t, h₁, h₂⟩ ↦ ⟨t, h₂, h₁⟩, fun ⟨t, h₁, h₂⟩ ↦ ⟨t, h₂, h₁⟩⟩

theorem when_veridical_complement : when_ A B → ∃ t, t ∈ timeTrace B :=
  fun ⟨t, _, ht⟩ ↦ ⟨t, ht⟩

theorem when_veridical_main : when_ A B → ∃ t, t ∈ timeTrace A := fun ⟨t, ht, _⟩ ↦ ⟨t, ht⟩

theorem while_veridical_complement (hne : ∃ t, t ∈ timeTrace A) :
    while_ A B → ∃ t, t ∈ timeTrace B :=
  fun hw ↦ hne.imp fun _ ht ↦ hw _ ht

theorem when_of_while (hne : ∃ t, t ∈ timeTrace A) : while_ A B → when_ A B :=
  fun hw ↦ hne.imp fun _ ht ↦ ⟨ht, hw _ ht⟩

theorem when_of_whenever (hne : ∃ t, t ∈ timeTrace B) : whenever A B → when_ A B :=
  fun hw ↦ hne.imp fun _ ht ↦ ⟨hw _ ht, ht⟩

theorem since_veridical_complement : since A B → ∃ t, t ∈ timeTrace B :=
  fun ⟨t, ht, _⟩ ↦ ⟨t, ht⟩

theorem by_veridical_main : by_ A B → ∃ t, t ∈ timeTrace A := fun ⟨t, ht, _⟩ ↦ ⟨t, ht⟩

theorem before_by : Tense.beforeEver A B → by_ A B :=
  fun ⟨t, ht, h⟩ ↦ ⟨t, ht, fun t' ht' ↦ (h t' ht').le⟩

/-! ### Before and by as negations of when and after -/

theorem beforeEver_iff_exists_not_when_not_after :
    Tense.beforeEver A B ↔ ∃ t ∈ timeTrace A, ¬ when_ {pure t} B ∧ ¬ Anscombe.after {pure t} B := by
  rw [beforeEver_iff_not_subset_upperClosure, Set.not_subset]
  simp only [SetLike.mem_coe, mem_upperClosure, when_, Anscombe.after, timeTrace_singleton,
    mem_pure, exists_eq_left, not_exists, not_and, not_le, not_lt]
  refine exists_congr fun t ↦ and_congr_right fun _ ↦ ?_
  exact ⟨fun h ↦ ⟨fun ht ↦ lt_irrefl t (h t ht), fun x hx ↦ (h x hx).le⟩,
    fun ⟨h₁, h₂⟩ x hx ↦ (h₂ x hx).lt_of_ne fun e ↦ h₁ (e ▸ hx)⟩

theorem by_iff_exists_not_after : by_ A B ↔ ∃ t ∈ timeTrace A, ¬ Anscombe.after {pure t} B := by
  simp only [by_, Anscombe.after, timeTrace_singleton, SetLike.mem_coe, mem_pure, exists_eq_left,
    not_exists, not_and, not_lt]

/-- *A before B* by the reference point holds when some time of `A` precedes `B`'s first time `lb`.
-/
def before (A : Set (NonemptyInterval T)) (lb : T) : Prop := ∃ t ∈ timeTrace A, t < lb

/-- *A after B* by the reference point holds when some time of `A` follows `B`'s first time `lb`. -/
def after (A : Set (NonemptyInterval T)) (lb : T) : Prop := ∃ t ∈ timeTrace A, lb < t

theorem before_iff_anscombe {lb : T} (hlb : IsLeast (timeTrace B) lb) :
    before A lb ↔ Tense.beforeEver A B := (beforeEver_iff_lt_least hlb).symm

theorem after_iff_anscombe {lb : T} (hlb : IsLeast (timeTrace B) lb) :
    after A lb ↔ Anscombe.after A B := (after_iff_least_lt hlb).symm

theorem while_not_symm :
    ¬∀ A B : Set (NonemptyInterval ℤ), while_ A B → while_ B A := by
  intro h
  let i₁₀ : NonemptyInterval ℤ := ⟨⟨1, 10⟩, by decide⟩
  have h5 : (pure 5 : NonemptyInterval ℤ).fst = 5 ∧ (pure 5 : NonemptyInterval ℤ).snd = 5 :=
    ⟨rfl, rfl⟩
  have h₁₀ : i₁₀.fst = 1 ∧ i₁₀.snd = 10 := ⟨rfl, rfl⟩
  have hw : while_ ({pure 5} : Set (NonemptyInterval ℤ)) (Set.Iic i₁₀) := by
    rintro t ⟨i, hi, hts, htf⟩
    rw [Set.mem_singleton_iff] at hi; subst hi
    rw [timeTrace_Iic]
    exact ⟨by omega, by omega⟩
  obtain ⟨i, hi, h1, _⟩ :=
    h _ _ hw 1 (by rw [timeTrace_Iic]; exact ⟨le_rfl, by decide⟩)
  rw [Set.mem_singleton_iff] at hi; subst hi
  omega

theorem by_not_before :
    ¬∀ A B : Set (NonemptyInterval ℤ), by_ A B → Tense.beforeEver A B := by
  intro h
  have h5 : (pure 5 : NonemptyInterval ℤ).fst = 5 ∧ (pure 5 : NonemptyInterval ℤ).snd = 5 :=
    ⟨rfl, rfl⟩
  obtain ⟨t, ⟨i, hi, h1, h2⟩, hall⟩ := h {pure 5} {pure 5}
    ⟨5, ⟨pure 5, rfl, le_rfl, le_rfl⟩, fun _ ⟨j, hj, hts, _⟩ ↦ by
      rw [Set.mem_singleton_iff] at hj; subst hj; exact hts⟩
  rw [Set.mem_singleton_iff] at hi; subst hi
  have := hall 5 ⟨pure 5, rfl, le_rfl, le_rfl⟩
  omega

end Heinamaki1974
