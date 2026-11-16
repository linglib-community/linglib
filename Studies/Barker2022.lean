module

public import Linglib.Logic.Modal.Defs
public import Linglib.Semantics.Composition.Continuized
public import Linglib.Semantics.Composition.Rules
public import Linglib.Semantics.Composition.Sorts
public import Linglib.Semantics.Modality.DomainSemantics
public import Linglib.Semantics.Presupposition.LocalContext

/-!
# Barker (2022): Composing local contexts

A logical form is a derivation by functional application, and its meaning is its value in the
structure of application on continuized values (`LF.value`), where a constituent is a function of
its local context. A presupposition is satisfied when the `Presupposition.commitments` of the
propositions the context may still express entail it. A right conjunct's context [entails the
left conjunct](##commitments_right_conjunct), a left conjunct's has [the commitments of the
initial context](##commitments_left_conjunct), and a logical form without triggers [denotes what
it did before](##lower_realize_continuized). Set against transparency, the commitments [include
the local context](##isLocalContext_subset_commitments) of a truth-functional environment.

## Implementation notes

* The entry of a presupposition trigger is a partial function whose domain condition mentions the
  commitments of its local context. Partial functions are not formalized: a trigger is an arbitrary
  continuized item, a derivation theorem identifies the context it is applied to, and satisfaction
  is entailment by the commitments of that context. The domain condition of bounded *might* is the
  set `bounded`.
* The initial context of a context set `c` is `initial c`, which conjoins `c`.
* *Might* as a test is the *might* of domain semantics at the commitments of its local context.

## TODO

* For a gap that is not sentence-final the inclusion of the transparency local context in the
  commitments is strict, as after a conjunct that a disjunct follows (`isLocalContext_and_or`,
  `commitments_and_or`); the paper's comparison of the two is for the propositional case without
  this restriction.
* Presuppositions in the scope of quantifiers, and logical forms with predicate abstraction, which
  `Continuized.realize_applicative_lift` covers as it does any language of rules.

## References

* [barker-2022]
* [schlenker-2009]
* [mandelkern-2019]
* [veltman-1996]
* [yalcin-2007]
* [heim-1992]
-/

@[expose] public section

namespace Barker2022

open Interpreter ManySorted ManySorted.Language Continuized Presupposition DomainSemantics Set
open scoped ModalLogic

variable {E W : Type} {ι : Type}

/-- The type of propositions. -/
local notation "st" => Ty.intens Ty.t

/-! ### Logical forms -/

/-- A logical form of type `a`: a derivation by functional application whose lexical items are
continuized. -/
abbrev LF (E W : Type) (a : Ty Base) : Type 1 :=
  Deriv application (fun a ↦ Continuized (Set W) (a.Domain E W)) a

/-- The structure of functional application on the domains of the types. -/
abbrev direct (E W : Type) : application.Structure (Ty.Dom (Base.Dom E W)) := inferInstance

namespace LF

variable {a b : Ty Base}

/-- A lexical item without a presupposition, which gives its value to its context. -/
abbrev lex (x : a.Domain E W) : LF E W a := .leaf (lift x)

/-- A functor applied to the argument on its right. -/
abbrev fa (f : LF E W (a ⇒ b)) (x : LF E W a) : LF E W b := .binary Application.fa f x

/-- A functor applied to the argument on its left. -/
abbrev ba (x : LF E W a) (f : LF E W (a ⇒ b)) : LF E W b := .binary Application.ba x f

/-- The meaning of a logical form, evaluated from left to right. -/
def value (d : LF E W a) : Continuized (Set W) (a.Domain E W) :=
  d.realize ((direct E W).applicative (Continuized (Set W))) fun x ↦ x

/-- The meaning of a logical form, each constituent evaluated in the context of the others. -/
def symValue (d : LF E W a) : Continuized (Set W) (a.Domain E W) :=
  d.realize (@Structure.applicative _ _ _ (Continuized (Set W)) symmetric (direct E W)) fun x ↦ x

end LF

open LF

/-- Simulation: a derivation over ordinary items has, continuized and in the empty context, the
proposition it has in the structure of application. -/
theorem lower_realize_continuized (d : Deriv application (fun a ↦ a.Domain E W) st) :
    lower (d.realize ((direct E W).applicative (Continuized (Set W))) fun x ↦ lift x) =
      d.realize (direct E W) fun x ↦ x := by
  rw [realize_applicative_lift (direct E W) fun x ↦ x]
  rfl

/-! ### Commitments of a context -/

/-- The initial context of a context set, which conjoins it with the sentence. -/
def initial (c : Set W) : Set W → Unit → Set W := fun p _ ↦ c ∩ p

section Commitments

variable {α δ : Type} {κ : α → ι → Set W} {w : W}

theorem mem_commitments_saturations :
    w ∈ commitments (saturations κ) ↔ (∃ a i, w ∈ κ a i) ∧ ∃ a i, w ∉ κ a i := by
  simp [mem_commitments, saturations]

theorem mem_commitments_range {g : δ → Set W} :
    w ∈ commitments (range g) ↔ (∃ d, w ∈ g d) ∧ ∃ d, w ∉ g d := by
  simp [mem_commitments]

variable (p : Set W)

-- The row of *and*, and the initial context: it is safe to suppose `p`.
theorem commitments_and : commitments (range fun q ↦ p ∩ q) = p := by
  ext w
  rw [mem_commitments_range]
  exact ⟨fun ⟨⟨_, h⟩, _⟩ ↦ h.1, fun h ↦ ⟨⟨univ, h, trivial⟩, ∅, fun h' ↦ h'.2⟩⟩

-- The row of *or*: it is safe to suppose that `p` is false.
theorem commitments_or : commitments (range fun q ↦ p ∪ q) = pᶜ := by
  ext w
  rw [mem_commitments_range]
  exact ⟨fun ⟨_, _, h⟩ hp ↦ h (Or.inl hp),
    fun h ↦ ⟨⟨univ, Or.inr trivial⟩, ∅, fun h' ↦ h'.elim h fun h ↦ h⟩⟩

-- The row of the material conditional: it is safe to suppose the antecedent.
theorem commitments_imp : commitments (range fun q ↦ p ⇨ q) = p := by
  simpa [himp_eq, union_comm] using commitments_or pᶜ

-- The row of negation, which adds nothing.
theorem commitments_not : commitments (range fun q : Set W ↦ qᶜ) = univ := by
  ext w
  rw [mem_commitments_range]
  exact ⟨fun _ ↦ trivial, fun _ ↦ ⟨⟨∅, fun h ↦ h⟩, univ, fun h ↦ h trivial⟩⟩

theorem commitments_initial (c : Set W) : commitments (saturations (initial c)) = c := by
  ext w
  rw [mem_commitments_saturations]
  exact ⟨fun ⟨⟨_, _, h⟩, _⟩ ↦ h.1, fun h ↦ ⟨⟨univ, ⟨⟩, h, trivial⟩, ∅, ⟨⟩, fun h' ↦ h'.2⟩⟩

end Commitments

/-! ### Commitments and transparency -/

section Transparency

variable {κ : Set W → ι → Set W} {x : Set W}

private theorem iUnion_range_eq_saturations :
    ⋃ f ∈ range fun i q ↦ κ q i, range f = saturations κ := by
  ext p
  simp only [mem_iUnion, mem_range, exists_prop, exists_exists_eq_and, mem_saturations]
  exact ⟨fun ⟨i, q, h⟩ ↦ ⟨q, i, h⟩, fun ⟨q, i, h⟩ ↦ ⟨i, q, h⟩⟩

/-- The local context of transparency, for a truth-functional gap, is included in the
commitments of the context of the gap. -/
theorem isLocalContext_subset_commitments (hκ : ∀ i, IsTruthFunctional (κ · i))
    (hx : IsLocalContext univ (range fun i q ↦ κ q i) x) : x ⊆ commitments (saturations κ) := by
  rw [← iUnion_range_eq_saturations]
  exact fun w hw ↦ (hx.subset_commitments (by rintro _ ⟨i, rfl⟩; exact hκ i) hw).2

-- A sentence-final gap: the commitments are the local context of transparency.
theorem isLocalContext_commitments {κ : Set W → Unit → Set W}
    (hκ : IsTruthFunctional (κ · ⟨⟩)) :
    IsLocalContext univ {(κ · ⟨⟩)} (commitments (saturations κ)) := by
  convert isLocalContext_singleton_of_isTruthFunctional (C := univ) hκ using 1
  rw [univ_inter]
  congr 1
  ext p
  exact ⟨fun h ↦ let ⟨q, _, h⟩ := mem_saturations.1 h; ⟨q, h⟩,
    fun ⟨q, h⟩ ↦ mem_saturations.2 ⟨q, ⟨⟩, h⟩⟩

-- In *(p and _) or c*, the local context of transparency is `p`.
theorem isLocalContext_and_or (p : Set W) :
    IsLocalContext univ (range fun (c q : Set W) ↦ p ∩ q ∪ c) p := by
  convert isLocalContext_of_isTruthFunctional (C := univ)
    (env := range fun (c q : Set W) ↦ p ∩ q ∪ c) ?_ using 1
  · ext w
    simp only [univ_inter, mem_range, exists_exists_eq_and, DependsAt, mem_ofPred_eq, mem_union,
      mem_inter_iff, mem_univ, and_true, mem_empty_iff_false, and_false, false_or]
    exact ⟨fun h ↦ ⟨∅, by simp [h]⟩, fun ⟨c, h⟩ ↦ by_contra fun hp ↦ h (by simp [hp])⟩
  · rintro _ ⟨c, rfl⟩ w d d' h
    simp [h]

-- In *(p and _) or c*, the commitments of the context of the gap are trivial.
theorem commitments_and_or (p : Set W) :
    commitments (saturations fun q c : Set W ↦ p ∩ q ∪ c) = univ := by
  ext w
  rw [mem_commitments_saturations]
  exact ⟨fun _ ↦ trivial, fun _ ↦ ⟨⟨∅, univ, Or.inr trivial⟩, ∅, ∅, fun h ↦ h.elim (·.2) id⟩⟩

end Transparency

/-! ### Conjunction -/

/-- Conjunction, taking the right conjunct first. -/
def conj : (st ⇒ st ⇒ st).Domain E W := fun q p w ↦ p w ∧ q w

section Conjunction

variable (rain : Set W) (ann : E) (t : Continuized (Set W) ((Ty.e ⇒ st).Domain E W))
  (κ : Set W → ι → Set W)

-- In *it rained and Ann [knows it rained]*, the context of the verb phrase contains the left
-- conjunct.
theorem value_right_conjunct :
    (ba (lex (a := st) rain) (fa (lex conj) (ba (lex ann) (.leaf t)))).value ι κ =
      t ι fun v ↦ κ (rain ∩ v ann) := rfl

/-- The commitments of the context of a verb phrase in a right conjunct, in the initial context
of `c`, entail the left conjunct. -/
theorem commitments_right_conjunct (c : Set W) :
    commitments (saturations fun v : E → Set W ↦ initial c (rain ∩ v ann)) = c ∩ rain := by
  ext w
  rw [mem_commitments_saturations]
  exact ⟨fun ⟨⟨_, _, hc, hr, _⟩, _⟩ ↦ ⟨hc, hr⟩, fun ⟨hc, hr⟩ ↦
    ⟨⟨fun _ ↦ univ, ⟨⟩, hc, hr, trivial⟩, fun _ ↦ ∅, ⟨⟩, fun h ↦ h.2.2⟩⟩

-- In *Ann [knows it rained] and it rained*, the context of the verb phrase awaits the right
-- conjunct.
theorem value_left_conjunct (i : ι) :
    (ba (ba (lex ann) (.leaf t)) (fa (lex conj) (lex (a := st) rain))).value ι κ i =
      t ((Set W → Set W) × ι) (fun v p ↦ κ (p.1 (v ann)) p.2) (conj (E := E) rain, i) := rfl

/-- The context of a verb phrase in a left conjunct has the commitments of the initial
context. -/
theorem commitments_left_conjunct :
    commitments (saturations fun (v : E → Set W) (p : (Set W → Set W) × ι) ↦
      κ (p.1 (v ann)) p.2) = commitments (saturations κ) :=
  congrArg commitments <| Subset.antisymm
    (saturations_subset fun v p ↦ ⟨p.1 (v ann), p.2, rfl⟩)
    (saturations_subset fun q i ↦ ⟨fun _ ↦ q, (id, i), rfl⟩)

-- Evaluated symmetrically, the context of a verb phrase in a left conjunct contains the right
-- conjunct.
theorem symValue_left_conjunct :
    (ba (ba (lex ann) (.leaf t)) (fa (lex conj) (lex (a := st) rain))).symValue ι κ =
      t ι fun v ↦ κ (v ann ∩ rain) := rfl

end Conjunction

/-! ### Epistemic modality -/

section Might

variable (c rain : Set W)

/-- *Might* as a test: the *might* of domain semantics at the commitments of the local
context. -/
def mightTest : Continuized (Set W) ((st ⇒ st).Domain E W) :=
  fun _ κ ↦ κ fun p ↦ (Sentence.ofProp p).might (commitments (saturations κ))

-- In *not rain and [might] rain*, the context of the modal contains the left conjunct.
theorem value_modal_right_conjunct (t : Continuized (Set W) ((st ⇒ st).Domain E W))
    (κ : Set W → ι → Set W) (i : ι) :
    (ba (lex (a := st) rainᶜ) (fa (lex conj) (fa (E := E) (.leaf t) (lex (a := st) rain)))).value
        ι κ i =
      t (Set W × ι) (fun f p ↦ κ (rainᶜ ∩ f p.1) p.2) (rain, i) := rfl

private theorem commitments_modal_right_conjunct :
    commitments (saturations fun (f : Set W → Set W) (p : Set W × Unit) ↦
      initial c (rainᶜ ∩ f p.1) p.2) = c ∩ rainᶜ := by
  ext w
  rw [mem_commitments_saturations]
  exact ⟨fun ⟨⟨_, _, hc, hr, _⟩, _⟩ ↦ ⟨hc, hr⟩, fun ⟨hc, hr⟩ ↦
    ⟨⟨fun _ ↦ univ, (∅, ⟨⟩), hc, hr, trivial⟩, fun _ ↦ ∅, (∅, ⟨⟩), fun h ↦ h.2.2⟩⟩

/-- *It isn't raining, but it might be raining* is a contradiction in every initial context. -/
theorem not_rain_and_mightTest_rain :
    (ba (lex (a := st) rainᶜ) (fa (lex conj) (fa (E := E) (.leaf mightTest)
      (lex (a := st) rain)))).value Unit (initial c) ⟨⟩ = ∅ := by
  refine eq_empty_iff_forall_notMem.2 fun w hw ↦ ?_
  obtain ⟨-, -, w', hw', hr⟩ : w ∈ c ∩ (rainᶜ ∩ {_w | ∃ w' ∈ commitments (saturations
    fun (f : Set W → Set W) (p : Set W × Unit) ↦ initial c (rainᶜ ∩ f p.1) p.2), w' ∈ rain}) := hw
  exact ((commitments_modal_right_conjunct c rain).subset hw').2 hr

-- *It might be raining, but it isn't raining* is true at the worlds of the initial context
-- without rain, if the initial context is consistent with rain.
theorem mightTest_rain_and_not_rain (h : (c ∩ rain).Nonempty) :
    (ba (fa (E := E) (.leaf mightTest) (lex (a := st) rain))
      (fa (lex conj) (lex (a := st) rainᶜ))).value Unit (initial c) ⟨⟩ = c \ rain := by
  have hc : commitments (saturations fun (f : Set W → Set W)
      (p : Set W × (Set W → Set W) × Unit) ↦ initial c (p.2.1 (f p.1)) p.2.2) = c := by
    ext w
    rw [mem_commitments_saturations]
    exact ⟨fun ⟨⟨_, _, h, _⟩, _⟩ ↦ h, fun h ↦
      ⟨⟨id, (univ, id, ⟨⟩), h, trivial⟩, id, (∅, id, ⟨⟩), fun h' ↦ h'.2⟩⟩
  change c ∩ ({_w | ∃ w' ∈ commitments (saturations fun (f : Set W → Set W)
    (p : Set W × (Set W → Set W) × Unit) ↦ initial c (p.2.1 (f p.1)) p.2.2), w' ∈ rain} ∩ rainᶜ) =
      c \ rain
  rw [hc]
  ext w
  exact ⟨fun ⟨hw, _, hr⟩ ↦ ⟨hw, hr⟩, fun ⟨hw, hr⟩ ↦ ⟨hw, h.imp fun _ h ↦ h, hr⟩⟩

/-- The domain condition of bounded *might* in a context with commitments `s`: if the evaluation
world is in `s`, so are its epistemic alternatives. -/
def bounded (R : SetRel W W) (s : Set W) : Set W := {w | w ∈ s → □[R] (· ∈ s) w}

-- With bounded *might*, *it isn't raining, but it might be raining* is false wherever the modal
-- is defined.
theorem not_rain_and_might_rain_of_bounded (R : SetRel W W) {w : W}
    (hw : w ∈ bounded R (commitments (saturations fun (f : Set W → Set W) (p : Set W × Unit) ↦
      initial c (rainᶜ ∩ f p.1) p.2))) :
    w ∉ c ∩ (rainᶜ ∩ {w | ◇[R] (· ∈ rain) w}) := by
  rintro ⟨hc, hr, w', hd, hw'⟩
  rw [commitments_modal_right_conjunct] at hw
  exact (hw ⟨hc, hr⟩ w' hd).2 hw'

end Might

/-! ### Attitude verbs -/

section Attitudes

variable (want : Set W → E → Set W) (dox : E → Set W)

/-- *Wants* applies its continuized complement to the context of the subject's beliefs. -/
def wants (p : Continuized (Set W) (Set W)) : Continuized (Set W) (E → Set W) :=
  fun _ κ ↦ κ fun x ↦ want (p Unit (fun q _ ↦ q ∩ dox x) ⟨⟩) x

-- In *wants Bill [to stop smoking]*, the context of the embedded verb phrase is that of the
-- subject's beliefs.
theorem wants_ba (bill : E) (t : Continuized (Set W) ((Ty.e ⇒ st).Domain E W))
    (κ : (E → Set W) → ι → Set W) :
    wants want dox (ba (lex bill) (.leaf t)).value ι κ =
      κ fun x ↦ want (t Unit (fun v _ ↦ v bill ∩ dox x) ⟨⟩) x := rfl

-- The commitments of the context of the verb phrase under *wants* are the subject's beliefs.
theorem commitments_wants (bill x : E) :
    commitments (saturations fun (v : E → Set W) (_ : Unit) ↦ v bill ∩ dox x) = dox x := by
  ext w
  rw [mem_commitments_saturations]
  exact ⟨fun ⟨⟨_, _, h⟩, _⟩ ↦ h.2, fun h ↦
    ⟨⟨fun _ ↦ univ, ⟨⟩, trivial, h⟩, fun _ ↦ ∅, ⟨⟩, fun h' ↦ h'.1⟩⟩

end Attitudes

/-! ### A trigger evaluated before its arguments -/

section Both

variable {a b c : Ty Base} (κ : c.Domain E W → ι → Set W)

-- In *[both] eyes opened*, the context of the determiner contains neither of its arguments.
theorem value_fa_fa (t : Continuized (Set W) ((a ⇒ b ⇒ c).Domain E W)) (x : a.Domain E W)
    (y : b.Domain E W) (i : ι) :
    (fa (fa (.leaf t) (lex x)) (lex y)).value ι κ i =
      t (a.Domain E W × b.Domain E W × ι) (fun f p ↦ κ (f p.1 p.2.1) p.2.2) (x, y, i) := rfl

-- The context of a functor both of whose arguments are still to come has the commitments of the
-- context of the whole.
theorem commitments_fa_fa [Nonempty (a.Domain E W)] [Nonempty (b.Domain E W)] :
    commitments (saturations fun (f : (a ⇒ b ⇒ c).Domain E W)
      (p : a.Domain E W × b.Domain E W × ι) ↦ κ (f p.1 p.2.1) p.2.2) =
      commitments (saturations κ) :=
  congrArg commitments <| Subset.antisymm
    (saturations_subset fun f p ↦ ⟨f p.1 p.2.1, p.2.2, rfl⟩)
    (saturations_subset fun z i ↦
      ⟨fun _ _ ↦ z, (Classical.arbitrary _, Classical.arbitrary _, i), rfl⟩)

end Both

end Barker2022
