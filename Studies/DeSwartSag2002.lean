module

public import Linglib.Semantics.Quantification.Polyadic
public import Linglib.Logic.Natural.Additivity
public import Linglib.Fragments.Romance.French.Determiners

/-!
# de Swart and Sag (2002): Negation and Negative Concord in Romance

De Swart and Sag take the French n-words *personne*, *rien* and *aucun N* to be negative
quantifiers and derive the two readings of a clause with two of them from two ways of composing
quantifiers. Iteration, ordinary function application, puts one in the scope of the other and
gives the double negation reading; resumption absorbs both into one quantifier over pairs and
gives the concord reading. Only anti-additive quantifiers resume, which *no* is and *few* is
not. Sentential negation is anti-additive too, a quantifier of type 0 that binds no variable,
so it can join a resumption and is then semantically empty; standard French keeps *pas* out of
resumption, so *pas* with an n-word reads only as a double negation.

## Main results

* `reading_iteration_iff`, `reading_resumption_iff`: the double negation reading of two n-words
  is *every*·*some* and the concord reading is *no*·*some*.
* `reading_resumption_and_not_iteration`: the two readings differ.
* `isAntiAdditive_no`, `not_isAntiAdditive_few`: *no* is anti-additive and *few* is not.
* `mem_aucun_and_isAntiAdditive_iff`: of the readings of *aucun*, the anti-additive one is *no*.
* `negReading_iteration_iff`: negation iterated over an n-word gives the existential.

## Implementation notes

* Resumption is binary, `Quantifier.Polyadic.resume`; the ternary and quaternary chains of the
  paper's (15) and (16) are not formalized.
* The HPSG retrieval of §4 is represented by its outcome, the `Mode` in which the stored
  quantifiers compose.

## References

* [de-swart-sag-2002]
* [peters-westerstahl-2006]
* [vanderwouden-1997]
-/

@[expose] public section

namespace DeSwartSag2002

open Quantifier Quantifier.GQ Quantifier.Polyadic NaturalLogic
open scoped Denotes

universe u

/-- Retrieval composes two n-words by iteration, function application, or by resumption into a
single quantifier over pairs ((29)). -/
inductive Mode where
  | iteration
  | resumption
  deriving DecidableEq, Repr, Fintype

section Readings

variable {α : Type u} [Fintype α] {A B : α → Prop} {R : α → α → Prop}

/-- The reading of a clause whose two arguments are n-words with restrictors `A` and `B` and
whose verb denotes `R`, as *Personne n'aime personne* ((13), (14)). -/
def reading : Mode → (α → Prop) → (α → Prop) → (α → α → Prop) → Prop
  | .iteration, A, B, R => iterate no no A B R
  | .resumption, A, B, R => resume GQ.Family.no A B R

/-- The double negation reading, `¬∃x¬∃y R(x, y)` ((13)), is *every*·*some*, as the gloss of
(33b) has it: everyone loves the son of someone. -/
theorem reading_iteration_iff : reading .iteration A B R ↔ iterate every GQ.some A B R :=
  iterate_no_no_iff

/-- The concord reading, `¬∃x∃y R(x, y)` ((14)), is *no*·*some* ((17)). -/
theorem reading_resumption_iff : reading .resumption A B R ↔ iterate no GQ.some A B R :=
  resume_no_iff

/-- The two readings differ: of one individual who loves no one, *Personne n'aime personne* is
true on its concord reading and false on its double negation reading. -/
theorem reading_resumption_and_not_iteration :
    reading .resumption (fun _ : Fin 1 ↦ True) (fun _ ↦ True) (fun _ _ ↦ False) ∧
      ¬ reading .iteration (fun _ : Fin 1 ↦ True) (fun _ ↦ True) (fun _ _ ↦ False) := by
  rw [reading_resumption_iff, reading_iteration_iff]
  simp [iterate, no, every, GQ.some]

end Readings

/-! ### Anti-additivity

Concord is restricted to anti-additive quantifiers such as *personne* 'no one', to the exclusion
of the merely downward-entailing *peu* 'few'. Negation is anti-additive as well
(`NaturalLogic.isAntiAdditive_compl`). -/

section AntiAdditive

variable {α : Type u}

/-- *No* is anti-additive in its scope: none of `A` is in `S ∪ S'` iff none is in `S` and none
in `S'`. -/
theorem isAntiAdditive_no (A : α → Prop) : IsAntiAdditive (no A) := fun S S' ↦ by
  simp only [no, Pi.sup_apply, sup_Prop_eq, inf_Prop_eq, not_or]
  exact propext ⟨fun h ↦ ⟨fun x hx ↦ (h x hx).1, fun x hx ↦ (h x hx).2⟩,
    fun h x hx ↦ ⟨h.1 x hx, h.2 x hx⟩⟩

/-- *Few* is downward-entailing (`Quantifier.GQ.scopeAntitone_few`) but not anti-additive: of
three individuals, few are `0` and few are `1`, but not few are `0` or `1`. -/
theorem not_isAntiAdditive_few : ¬ IsAntiAdditive (few fun _ : Fin 3 ↦ True) := fun h ↦ by
  have : few (fun _ : Fin 3 ↦ True) (fun x ↦ x = 0 ∨ x = 1) ↔
      few (fun _ : Fin 3 ↦ True) (· = 0) ∧ few (fun _ : Fin 3 ↦ True) (· = 1) :=
    eq_iff_iff.mp (h (· = 0) (· = 1))
  revert this; decide

theorem not_isAntiAdditive_some : ¬ IsAntiAdditive (GQ.some fun _ : PUnit.{u + 1} ↦ True) :=
  fun h ↦ by simpa [GQ.some] using eq_iff_iff.mp (h ⊤ ⊥)

/-- Of the readings of *aucun*, the one that is anti-additive on every finite domain, as a
concord item must be, is the negative quantifier. -/
theorem mem_aucun_and_isAntiAdditive_iff {d : GQ.Family.{u}} :
    (d ∈ ⟦French.Determiners.QuantityWord.aucun⟧ ∧
      ∀ (β : Type u) [Fintype β] (A : β → Prop), IsAntiAdditive (d β A)) ↔
      d = GQ.Family.no := by
  refine ⟨fun ⟨hd, h⟩ ↦ hd.resolve_right fun hs ↦ ?_,
    fun h ↦ h ▸ ⟨.inl rfl, fun _ _ ↦ isAntiAdditive_no⟩⟩
  subst hs; exact not_isAntiAdditive_some (h PUnit _)

end AntiAdditive

/-! ### Negation as a quantifier of type 0

A negator binds no variable, so when it joins the resumption of n-words it leaves the resumptive
quantifier unchanged: in concord, negation is semantically empty (§6.1). The same holds of
*sans* 'without' (§6.2). -/

section TypeZero

variable {α : Type u} {A S : α → Prop}

/-- The reading of a negator with one n-word: negation iterated over the n-word, or absorbed
into its resumption. -/
def negReading : Mode → (α → Prop) → (α → Prop) → Prop
  | .iteration, A, S => ¬ no A S
  | .resumption, A, S => no A S

/-- Negation iterated over an n-word gives the existential reading of *Il ne va pas nulle part*
((36a)), since (40) keeps *pas* out of resumption. -/
theorem negReading_iteration_iff : negReading .iteration A S ↔ GQ.some A S := by
  simp [negReading, no, GQ.some]

/-- Absorbed into the n-word's resumption, the negator adds nothing, as *sans* in *Anne est
partie sans rien dire* 'Anne left without saying anything' ((56)). -/
theorem negReading_resumption_iff : negReading .resumption A S ↔ no A S := Iff.rfl

end TypeZero

end DeSwartSag2002
