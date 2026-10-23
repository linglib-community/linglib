module

public import Linglib.Semantics.Quantification.Exceptive
public import Linglib.Data.Examples.VonFintel1993
public import Linglib.Fragments.English.Determiners
public import Linglib.Core.Order.Prop
public import Mathlib.Tactic.FinCases

/-!
# von Fintel (1993): Exceptive Constructions

von Fintel gives the English *but*-phrase of *every student but John* a least-exception
semantics. Plain domain subtraction, reading *students but John* as the students minus John,
neither explains why *but* occurs only with *every* and *no* nor blocks the inference to
*every student but John and Jill*, and adding the requirement that the quantification fail
without the subtraction still admits *most*. On the least-exception semantics the *but*-phrase
instead names the exception set, the least set whose subtraction makes the quantification true
(`Exceptive.IsExceptionSet`), which with *every* is the restrictor minus the scope and with
*no* their intersection. Free exceptives like *except for John* carry subtraction with
restrictiveness only (`Exceptive.Restrictive`), which is why they also occur with *most*.

## Main statements

* `GuaranteesException`: a determiner guarantees an exception set when every false
  quantification has one. *Every* and *no* guarantee one, *some* never has one, and *most* has
  none in the paper's five-student situation though it has one in a two-student limiting case;
  the paper reads the co-occurrence restriction as a grammaticization of this contrast.
* `not_isExceptionSet_of_lt`, `eq_of_isExceptionSet_ident`: the unique least exception blocks
  the enlargement inference and the conjunction of two *but*-phrases.
* `not_exists_nounModifier`: no operation on the restrictor alone yields the *but*-phrase's
  truth conditions.
* `isExceptionSet_every_of_restrictive`: with a universal determiner the free exceptive
  pragmatically strengthens to the *but* reading.
* `but_predicted`, `exceptFor_predicted`: the paper's exceptive examples, read through the
  English fragment's determiner denotations, are judged acceptable exactly as the two
  semantics predict.

## Implementation notes

* Restrictor, scope and exception set are predicates ordered pointwise, so the truth
  conditions are lattice equations and the five-student and two-student models use `⊤` and
  `Fin` restrictors.
* The guarantee of an exception set is conditional on a false quantification, the paper's "if
  there is any at all"; the unconditional version also holds for *every* and *no*, whose
  exception set is then empty (`Exceptive.isExceptionSet_every`).
* The strengthening of a free exceptive to the *but* reading takes as hypothesis that the
  exception set contains only exceptions, the paper's gloss of the uniqueness condition, which
  pragmatics supplies.
* The determiner *any* of Horn's paradigm has no reading in the paper or the fragment, so its
  rows are not predicted; likewise the definite of *except for Jane, my relatives* and the
  minimality-based *besides*, which the paper leaves to further research.
* Not formalized: the two curryings of the *but*-phrase and the impossibility of an
  NP-modifier semantics, which is not derivable from *every* and *no* alone; the Cooper
  variable; the rhetorical reading of *who but*.

## TODO

* The paper's footnote on *both* and *neither* presumes they "give rise to unique exception
  sets"; under the library's cardinality-asserting `both` a false *both*-quantification has no
  exception set at all, so which semantics the footnote intends is undetermined and neither
  claim is stated.

## References

* [von-fintel-1993]
* [keenan-stavi-1986]
* [hoeksema-1987]
* [horn-1989]
-/

@[expose] public section

namespace VonFintel1993

open Quantifier Quantifier.GQ Quantifier.NP Quantifier.Exceptive Semantics
open English.Determiners (QuantityWord)

variable {α : Type*} {Q : GQ α} {A C B : α → Prop}

/-! ### Truth conditions (§1.1, §1.5) -/

/-- *Every student but John attended* says that the students who did not attend are John
alone, (9) of the paper and the reading of `Examples.ex_1a`. -/
theorem isExceptionSet_every_ident_iff {j : α} :
    IsExceptionSet every A (ident j) B ↔ A \ B = ident j :=
  isExceptionSet_every_iff

/-- *No student but John attended* says that the students who attended are John alone, (9) of
the paper and the reading of `Examples.ex_2b`. -/
theorem isExceptionSet_no_ident_iff {j : α} :
    IsExceptionSet no A (ident j) B ↔ A ⊓ B = ident j :=
  isExceptionSet_no_iff

/-! ### Consequences of uniqueness (§1.5, §1.7) -/

/-- The inference to a *but*-phrase with a larger exception set (24), `Examples.ex_14`, is
blocked. -/
theorem not_isExceptionSet_of_lt (h : IsExceptionSet Q A C B) {C' : α → Prop} (hlt : C < C') :
    ¬ IsExceptionSet Q A C' B :=
  fun h' ↦ hlt.ne (h.unique h')

/-- Two *but*-phrases on one quantifier (28), `Examples.ex_28a`, name the same exception. -/
theorem eq_of_isExceptionSet_ident {j m : α} (hj : IsExceptionSet Q A (ident j) B)
    (hm : IsExceptionSet Q A (ident m) B) : j = m :=
  ident_injective (hj.unique hm)

/-! ### The co-occurrence restrictions (§1.6) -/

/-- A determiner guarantees an exception set when every false quantification has one, the
property von Fintel finds the universal determiners alone to have. -/
def GuaranteesException (Q : GQ α) : Prop :=
  ∀ A B : α → Prop, ¬ Q A B → ∃ C, IsExceptionSet Q A C B

theorem guaranteesException_every : GuaranteesException (every : GQ α) :=
  fun A B _ ↦ ⟨A \ B, isExceptionSet_every A B⟩

theorem guaranteesException_no : GuaranteesException (no : GQ α) :=
  fun A B _ ↦ ⟨A ⊓ B, isExceptionSet_no A B⟩

theorem not_guaranteesException_some : ¬ GuaranteesException (GQ.some : GQ α) := fun h ↦
  let ⟨_, ⟨_, _, hx⟩, _⟩ := h ⊤ ⊥ fun ⟨_, _, hx⟩ ↦ hx
  hx

/-- The five students of (25) are Tom, John, Harry, Bill and Mary in order; only the last two
attended (`Examples.ex_25a`). -/
abbrev attended : Fin 5 → Prop := (3 ≤ ·)

/-- No set of students is the exception set of *most students attended* in situation (25)
(`Examples.ex_25b`), since excluding any two of the three nonattenders makes it true, so only
the empty set lies below every rescuer, and without any exclusion it is false. -/
theorem not_isExceptionSet_most (C : Fin 5 → Prop) : ¬ IsExceptionSet most ⊤ C attended := by
  rintro ⟨h1, h2⟩
  have hTJ : most (⊤ \ fun x : Fin 5 ↦ x = 0 ∨ x = 1) attended := by decide
  have hTH : most (⊤ \ fun x : Fin 5 ↦ x = 0 ∨ x = 2) attended := by decide
  have hJH : most (⊤ \ fun x : Fin 5 ↦ x = 1 ∨ x = 2) attended := by decide
  have hC : C = ⊥ := le_bot_iff.1 fun x hx ↦ by
    have h01 := h2 hTJ x hx
    have h02 := h2 hTH x hx
    have h12 := h2 hJH x hx
    show False
    omega
  subst hC
  have h1' : most (⊤ \ (⊥ : Fin 5 → Prop)) attended := h1
  rw [sdiff_bot] at h1'
  exact absurd h1' (by decide)

theorem not_guaranteesException_most : ¬ GuaranteesException (most : GQ (Fin 5)) := fun h ↦
  let ⟨C, hC⟩ := h ⊤ attended fun hm ↦ absurd hm (by decide)
  not_isExceptionSet_most C hC

theorem isExceptionSet_most_two :
    IsExceptionSet most ⊤ (· = (0 : Fin 2)) (· = (1 : Fin 2)) := by
  refine ⟨by decide, fun S hS x hx ↦ ?_⟩
  obtain rfl : x = 0 := hx
  have hS' : most (fun x : Fin 2 ↦ True ∧ ¬ S x) (· = 1) := hS
  by_contra h0
  by_cases h1 : S 1
  · have e : (fun x : Fin 2 ↦ True ∧ ¬ S x) = (· = 0) :=
      funext fun x ↦ propext (by fin_cases x <;> simp [h0, h1])
    rw [e] at hS'
    exact absurd hS' (by decide)
  · have e : (fun x : Fin 2 ↦ True ∧ ¬ S x) = fun _ ↦ True :=
      funext fun x ↦ propext (by fin_cases x <;> simp [h0, h1])
    rw [e] at hS'
    exact absurd hS' (by decide)

/-! ### What *but* operates on (§1.8) -/

/-- The *but*-phrase cannot be a noun modifier (§1.8). No operation on the restrictor alone
yields the exception-set truth conditions with *every*, since with the whole domain as scope
the modified quantification is true while a nonempty `C` is not the exception set. -/
theorem not_exists_nounModifier (hC : C ≠ ⊥) :
    ¬ ∃ f : (α → Prop) → α → Prop, ∀ A B, every (f A) B ↔ IsExceptionSet every A C B :=
  fun ⟨_, hf⟩ ↦
    hC ((isExceptionSet_every_iff.1 ((hf ⊥ ⊤).1 (every_iff_le.2 le_top))).symm.trans bot_sdiff)

/-! ### Free exceptives (§2) -/

/-- In the situation of (25), *except for Tom and John, most students attended* holds where no
*but*-phrase does, so the free exceptive occurs with *most* (34c). -/
theorem restrictive_most :
    Restrictive most ⊤ (fun x : Fin 5 ↦ x = 0 ∨ x = 1) attended :=
  ⟨by decide, fun h ↦ absurd h (by decide)⟩

/-- With *every* the *but* reading is the pragmatic strengthening of the free exceptive to an
exception set that contains only exceptions (§2.3). -/
theorem isExceptionSet_every_of_restrictive (h : Restrictive every A C B) (hC : C ≤ A \ B) :
    IsExceptionSet every A C B :=
  isExceptionSet_every_iff.2 (le_antisymm (restrictive_every_iff.1 h).1 hC)

/-- With *no* the *but* reading is likewise the strengthening of the free exceptive (§2.3). -/
theorem isExceptionSet_no_of_restrictive (h : Restrictive no A C B) (hC : C ≤ A ⊓ B) :
    IsExceptionSet no A C B :=
  isExceptionSet_no_iff.2 (le_antisymm (restrictive_no_iff.1 h).1 hC)

/-! ### The paper's examples -/

/-- The paper opposes two exceptive markers, the *but*-phrase and free *except for*. -/
inductive Marker
  | but
  | exceptFor
  deriving DecidableEq, Repr

/-- These determiners of the paper's exceptive examples have a reading in the English fragment
or the quantification substrate; *any*, the definite and *besides*'s numeral have none. -/
inductive Determiner
  | every
  | no
  | some
  | most
  deriving DecidableEq, Repr

/-- A determiner reads as the English fragment's denotations for the words the fragment has
and as the quantification substrate's `no` for *no*. -/
noncomputable def Determiner.readings : Determiner → Set GQ.Family.{0}
  | .every => ⟦QuantityWord.every⟧
  | .no => {GQ.Family.no}
  | .some => ⟦QuantityWord.some_⟧
  | .most => ⟦QuantityWord.most⟧

/-- A row records an exceptive example of the paper by its marker, its determiner and its
printed judgment. -/
structure Row where
  marker : Marker
  det : Determiner
  judgment : Judgment
  deriving DecidableEq, Repr

/-- `ofDatum` reads the marker, the determiner and the judgment off an exceptive example with
a tabled determiner. -/
def Row.ofDatum (ex : Datum) : Option Row := do
  let m ← ex.parse? "exceptive" [("but", Marker.but), ("except for", .exceptFor)]
  let d ← ex.parse? "determiner"
    [("every", Determiner.every), ("all", .every), ("no", .no), ("some", .some), ("most", .most)]
  pure ⟨m, d, ex.judgment⟩

/-- `rows` collects the exceptive rows of the paper's examples. -/
def rows : List Row := Examples.all.filterMap Row.ofDatum

private theorem rows_eq : rows =
    [⟨.but, .every, .acceptable⟩, ⟨.exceptFor, .every, .acceptable⟩, ⟨.but, .no, .acceptable⟩,
     ⟨.but, .every, .acceptable⟩, ⟨.but, .no, .acceptable⟩, ⟨.but, .some, .ungrammatical⟩,
     ⟨.but, .some, .ungrammatical⟩, ⟨.but, .every, .acceptable⟩, ⟨.but, .most, .ungrammatical⟩,
     ⟨.but, .every, .acceptable⟩, ⟨.but, .no, .acceptable⟩, ⟨.but, .every, .acceptable⟩,
     ⟨.but, .most, .ungrammatical⟩, ⟨.exceptFor, .most, .acceptable⟩,
     ⟨.exceptFor, .no, .acceptable⟩, ⟨.exceptFor, .most, .acceptable⟩] := by
  decide

/-- In Horn's paradigm (10) and the *but*-sentences (1a), (2b), (22) and (25b), a *but*-phrase
is acceptable with a determiner exactly when its readings guarantee an exception set on every
finite domain, the semantic fact the paper takes the co-occurrence restriction to
grammaticize. -/
theorem but_predicted :
    ∀ r ∈ rows, r.marker = .but →
      (r.judgment = .acceptable ↔
        ∀ q ∈ r.det.readings, ∀ (β : Type) [Fintype β], GuaranteesException (q β)) := by
  have hevery : ∀ q ∈ Determiner.every.readings, ∀ (β : Type) [Fintype β],
      GuaranteesException (q β) := fun q hq β _ ↦ by
    obtain rfl : q = GQ.Family.every := hq
    exact guaranteesException_every
  have hno : ∀ q ∈ Determiner.no.readings, ∀ (β : Type) [Fintype β],
      GuaranteesException (q β) := fun q hq β _ ↦ by
    obtain rfl : q = GQ.Family.no := hq
    exact guaranteesException_no
  have hsome : ¬ ∀ q ∈ Determiner.some.readings, ∀ (β : Type) [Fintype β],
      GuaranteesException (q β) :=
    fun h ↦ not_guaranteesException_some (h GQ.Family.some rfl (Fin 1))
  have hmost : ¬ ∀ q ∈ Determiner.most.readings, ∀ (β : Type) [Fintype β],
      GuaranteesException (q β) :=
    fun h ↦ not_guaranteesException_most (h GQ.Family.most rfl (Fin 5))
  rw [rows_eq]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl)
  · exact fun _ ↦ iff_of_true rfl hevery
  · exact fun h ↦ nomatch h
  · exact fun _ ↦ iff_of_true rfl hno
  · exact fun _ ↦ iff_of_true rfl hevery
  · exact fun _ ↦ iff_of_true rfl hno
  · exact fun _ ↦ iff_of_false (by decide) hsome
  · exact fun _ ↦ iff_of_false (by decide) hsome
  · exact fun _ ↦ iff_of_true rfl hevery
  · exact fun _ ↦ iff_of_false (by decide) hmost
  · exact fun _ ↦ iff_of_true rfl hevery
  · exact fun _ ↦ iff_of_true rfl hno
  · exact fun _ ↦ iff_of_true rfl hevery
  · exact fun _ ↦ iff_of_false (by decide) hmost
  · exact fun h ↦ nomatch h
  · exact fun h ↦ nomatch h
  · exact fun h ↦ nomatch h

/-- The free exceptives of (1b), (33a), (34a) and (34c) are acceptable with every tabled
determiner, each of which admits a restrictive exceptive on some finite domain, as the
semantics without the uniqueness condition predicts. -/
theorem exceptFor_predicted :
    ∀ r ∈ rows, r.marker = .exceptFor →
      (r.judgment = .acceptable ↔
        ∀ q ∈ r.det.readings, ∃ (β : Type) (_ : Fintype β) (A C B : β → Prop),
          Restrictive (q β) A C B) := by
  have hevery : ∀ q ∈ Determiner.every.readings, ∃ (β : Type) (_ : Fintype β)
      (A C B : β → Prop), Restrictive (q β) A C B := fun q hq ↦ by
    obtain rfl : q = GQ.Family.every := hq
    exact ⟨Fin 1, inferInstance, ⊤, ⊤, ⊥,
      fun x hx ↦ absurd trivial hx.2, fun h ↦ h 0 trivial⟩
  have hno : ∀ q ∈ Determiner.no.readings, ∃ (β : Type) (_ : Fintype β)
      (A C B : β → Prop), Restrictive (q β) A C B := fun q hq ↦ by
    obtain rfl : q = GQ.Family.no := hq
    exact ⟨Fin 1, inferInstance, ⊤, ⊤, ⊤,
      fun x hx _ ↦ hx.2 trivial, fun h ↦ h 0 trivial trivial⟩
  have hmost : ∀ q ∈ Determiner.most.readings, ∃ (β : Type) (_ : Fintype β)
      (A C B : β → Prop), Restrictive (q β) A C B := fun q hq ↦ by
    obtain rfl : q = GQ.Family.most := hq
    exact ⟨Fin 5, inferInstance, ⊤, fun x ↦ x = 0 ∨ x = 1, attended, restrictive_most⟩
  rw [rows_eq]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl)
  · exact fun h ↦ nomatch h
  · exact fun _ ↦ iff_of_true rfl hevery
  · exact fun h ↦ nomatch h
  · exact fun h ↦ nomatch h
  · exact fun h ↦ nomatch h
  · exact fun h ↦ nomatch h
  · exact fun h ↦ nomatch h
  · exact fun h ↦ nomatch h
  · exact fun h ↦ nomatch h
  · exact fun h ↦ nomatch h
  · exact fun h ↦ nomatch h
  · exact fun h ↦ nomatch h
  · exact fun h ↦ nomatch h
  · exact fun _ ↦ iff_of_true rfl hmost
  · exact fun _ ↦ iff_of_true rfl hno
  · exact fun _ ↦ iff_of_true rfl hmost

end VonFintel1993
