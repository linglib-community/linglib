module

public import Studies.DeSwartSag2002
public import Linglib.Fragments.Slavic.Czech.Determiners
public import Linglib.Fragments.Romance.Italian.Determiners

/-!
# Zeijlstra (2004): Sentential Negation and Negative Concord

Zeijlstra derives negative concord from syntactic agreement. Each negative element carries a
negative feature, interpretable `[iNEG]` or uninterpretable `[uNEG]`, and an element carrying
`[uNEG]` must be checked by a c-commanding element carrying `[iNEG]`. In concord languages the
n-words carry `[uNEG]` and are non-negative indefinites; the operator that checks them is
negation with existential closure, which binds their variables. A clause whose highest negative
element carries `[uNEG]` has a covert operator above it. Languages differ in the feature of the
negative marker: `[uNEG]` in strict concord languages such as Czech and `[iNEG]` in non-strict
ones such as Italian, while in double negation languages such as Standard Dutch every negative
element carries `[iNEG]` and n-words are negative quantifiers.

In Czech the n-word means the same before and after the negated verb, while an Italian n-word
before *non* yields double negation. The concord reading of two n-words is de Swart and Sag's
resumption of *no*, which Zeijlstra reduces to an iteration; the two analyses differ not on
the truth conditions of concord but on whether a concord language has the double negation
reading as well.

## Main results

* `meaning_of_forall_u`: in a strict concord language every negative clause has one negation,
  wherever its marker and n-words stand.
* `meaning_marker_nword`, `meaning_nword_marker`: Italian *non* before an n-word gives concord
  and after it double negation.
* `meaning_concord_iff_resumption`, `meaning_dn_iff_iteration`: concord is de Swart and Sag's
  resumption and double negation their iteration.
* `mem_nessuno_and_scopeMonotone_iff`: of the readings of an n-word, Zeijlstra's is the
  non-negative one.

## Implementation notes

* A clause is its negative elements in c-command order over a nucleus that takes the individuals
  its n-words introduce; movement, Multiple Agree and phases are represented by that order. An
  n-word's variable is closed by the nearest `[iNEG]` element above it, and since only n-words
  and `[uNEG]` markers intervene, closing it in place is equivalent.
* Example numbers are those of chapter 8 unless marked.
* The summary of §8.1.4 assigns the markers of strict and non-strict concord the opposite
  features; the derivations of §§8.1.1–8.1.2 fix them as here.

## References

* [zeijlstra-2004]
* [de-swart-sag-2002]
-/

@[expose] public section

namespace Zeijlstra2004

open Quantifier Quantifier.GQ Quantifier.Polyadic
open scoped Denotes

universe u

/-- A negative feature is interpretable, `[iNEG]`, or uninterpretable, `[uNEG]`. -/
inductive Feature where
  | i
  | u
  deriving DecidableEq, Repr

/-- A negative element of a clause is a negative marker or an n-word with its restrictor, each
carrying a negative feature. -/
inductive NegElement (α : Type u) where
  | marker (f : Feature)
  | nword (f : Feature) (A : α → Prop)

variable {α : Type u}

namespace NegElement

/-- The negative feature of an element. -/
def feature : NegElement α → Feature
  | .marker f | .nword f _ => f

/-- Whether an element is an n-word. -/
def isNword : NegElement α → Bool
  | .marker _ => false
  | .nword _ _ => true

end NegElement

/-- The interpretation of negative elements in c-command order over a nucleus that takes the
individuals the n-words introduce. A marker carrying `[iNEG]` is negation and one carrying
`[uNEG]` is empty; an n-word carrying `[uNEG]` is an indefinite, existentially closed, and one
carrying `[iNEG]` a negative quantifier. -/
def interp : List (NegElement α) → (List α → Prop) → Prop
  | [], P => P []
  | .marker .i :: es, P => ¬ interp es P
  | .marker .u :: es, P => interp es P
  | .nword .u A :: es, P => GQ.some A fun x ↦ interp es fun xs ↦ P (x :: xs)
  | .nword .i A :: es, P => no A fun x ↦ interp es fun xs ↦ P (x :: xs)

/-- The meaning of a clause. When its highest negative element carries `[uNEG]`, a covert
operator above it checks the feature and contributes negation. -/
def meaning (es : List (NegElement α)) (P : List α → Prop) : Prop :=
  if es.head?.map NegElement.feature = some .u then ¬ interp es P else interp es P

/-! ### Strict concord -/

theorem interp_filter_isNword {es : List (NegElement α)} (hu : ∀ e ∈ es, e.feature = .u)
    (P : List α → Prop) : interp es P ↔ interp (es.filter NegElement.isNword) P := by
  induction es generalizing P with
  | nil => rfl
  | cons e es ih =>
    have hes : ∀ e ∈ es, e.feature = .u := fun e he ↦ hu e (List.mem_cons_of_mem _ he)
    rcases e with f | ⟨f, A⟩ <;> obtain rfl : f = .u := hu _ List.mem_cons_self
    · exact ih hes P
    · simp only [interp, List.filter_cons, NegElement.isNword, ite_true]
      exact exists_congr fun x ↦ and_congr_right' (ih hes _)

/-- In a strict concord language every negative clause expresses one negation wherever the marker
stands, as Czech *Nevolá nikdo* ((20)) and *Nikdo nevolá* ((23)). -/
theorem meaning_of_forall_u {es : List (NegElement α)} (hne : es ≠ [])
    (hu : ∀ e ∈ es, e.feature = .u) (P : List α → Prop) :
    meaning es P ↔ ¬ interp (es.filter NegElement.isNword) P := by
  obtain ⟨e, es, rfl⟩ := List.exists_cons_of_ne_nil hne
  simp only [meaning, List.head?_cons, Option.map_some, hu e List.mem_cons_self, ite_true]
  exact not_congr (interp_filter_isNword hu P)

/-! ### Non-strict concord and double negation -/

section Examples

variable {A : α → Prop} {P : List α → Prop}

/-- Italian *Non ha telefonato nessuno* 'nobody called' ((63)): *non* carries `[iNEG]` and
checks the n-word below it. -/
theorem meaning_marker_nword : meaning [.marker .i, .nword .u A] P ↔ no A fun x ↦ P [x] := by
  simp [meaning, interp, NegElement.feature, no, GQ.some]

/-- In Italian *Nessuno non ha telefonato* ((36b) of chapter 7), *non* negates again, so the concord
reading is out ((66)). -/
theorem meaning_nword_marker : meaning [.nword .u A, .marker .i] P ↔ every A fun x ↦ P [x] := by
  simp [meaning, interp, NegElement.feature, every, GQ.some]

-- (84)
theorem meaning_dn_nword_marker : meaning [.nword .i A, .marker .i] P ↔ every A fun x ↦ P [x] := by
  simp [meaning, interp, NegElement.feature, every, no]

end Examples

/-! ### Comparison with de Swart and Sag -/

section Comparison

variable [Fintype α] {A B : α → Prop} {P : List α → Prop}

/-- Two n-words under the covert operator mean de Swart and Sag's resumption of *no* ((68)), itself
an iteration ((29) of chapter 7). -/
theorem meaning_concord_iff_resumption :
    meaning [.nword .u A, .nword .u B] P ↔
      DeSwartSag2002.reading .resumption A B fun x y ↦ P [x, y] := by
  rw [DeSwartSag2002.reading_resumption_iff]
  simp [meaning, interp, NegElement.feature, iterate, no, GQ.some]

/-- Two n-words carrying `[iNEG]` in a double negation language give de Swart and Sag's
iteration of *no*. -/
theorem meaning_dn_iff_iteration :
    meaning [.nword .i A, .nword .i B] P ↔
      DeSwartSag2002.reading .iteration A B fun x y ↦ P [x, y] := by
  simp [meaning, interp, NegElement.feature, DeSwartSag2002.reading, iterate]

theorem meaning_concord_and_not_iteration :
    meaning [.nword .u (fun _ : Fin 1 ↦ True), .nword .u fun _ ↦ True] (fun _ ↦ False) ∧
      ¬ DeSwartSag2002.reading .iteration (fun _ : Fin 1 ↦ True) (fun _ ↦ True)
        fun _ _ ↦ False :=
  ⟨meaning_concord_iff_resumption.mpr DeSwartSag2002.reading_resumption_and_not_iteration.1,
    DeSwartSag2002.reading_resumption_and_not_iteration.2⟩

end Comparison

/-! ### The readings of n-words

N-words are non-negative indefinites, so of the readings the fragments list for an n-word,
Zeijlstra's is the one that is upward monotone in its scope. -/

section Readings

theorem not_scopeMonotone_no : ¬ ScopeMonotone (no : GQ PUnit.{u + 1}) := fun h ↦ by
  simpa [no] using h (fun _ ↦ True) (bot_le (a := fun _ ↦ True))

/-- Of the readings of Italian *nessuno*, the one upward monotone in its scope on every finite
domain is the indefinite. -/
theorem mem_nessuno_and_scopeMonotone_iff {d : GQ.Family.{u}} :
    (d ∈ ⟦Italian.Determiners.QuantityWord.nessuno⟧ ∧
      ∀ (β : Type u) [Fintype β], ScopeMonotone (d β)) ↔ d = GQ.Family.some := by
  refine ⟨fun ⟨hd, h⟩ ↦ hd.resolve_left fun hn ↦ ?_,
    fun h ↦ h ▸ ⟨.inr rfl, fun _ _ ↦ scopeMonotone_some⟩⟩
  subst hn; exact not_scopeMonotone_no (h PUnit)

theorem mem_zadny_and_scopeMonotone_iff {d : GQ.Family.{u}} :
    (d ∈ ⟦Czech.Determiners.QuantityWord.zadny⟧ ∧
      ∀ (β : Type u) [Fintype β], ScopeMonotone (d β)) ↔ d = GQ.Family.some := by
  refine ⟨fun ⟨hd, h⟩ ↦ hd.resolve_left fun hn ↦ ?_,
    fun h ↦ h ▸ ⟨.inr rfl, fun _ _ ↦ scopeMonotone_some⟩⟩
  subst hn; exact not_scopeMonotone_no (h PUnit)

end Readings

end Zeijlstra2004
