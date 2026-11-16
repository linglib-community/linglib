module

public import Linglib.Logic.Modal.Defs
public import Linglib.Semantics.Composition.Continuized
public import Linglib.Semantics.Composition.Sorts
public import Linglib.Semantics.Modality.DomainSemantics
public import Linglib.Semantics.Presupposition.LocalContext

/-!
# Barker (2022): Composing local contexts

A logical form is a derivation by functional application, and its meaning is the value of the
derivation continuized in order (`LF.value`), a computation at the effect of continuations whose
continuation is its local context. A presupposition is satisfied when the
`Presupposition.commitments` of the propositions the context may still express entail it. A
right conjunct's context [entails the left conjunct](##commitments_right_conjunct), a left
conjunct's has [the commitments of the initial context](##commitments_left_conjunct), and a
logical form without triggers [denotes what it did before](##lower_value_lex). Set against
transparency, the commitments [include the local
context](##isLocalContext_subset_commitments) of a truth-functional environment.

## Implementation notes

* A lexical item is a continuized meaning at every answer type that ends in a proposition, since
  an item is continuized at the answer its position gives it. The entry of a presupposition
  trigger is a partial function whose domain condition mentions the commitments of its local
  context. Partial functions are not formalized: a trigger is an arbitrary item, a derivation
  theorem identifies the context it is applied to, and satisfaction is entailment by the
  commitments of that context. The domain condition of bounded *might* is the set `bounded`.
* Propositions are predicates of worlds, the domain of the type of propositions, and the initial
  context of a context set `c` conjoins `c`.
* *Might* as a test is the *might* of domain semantics at the commitments of its local context.

## TODO

* For a gap that is not sentence-final the inclusion of the transparency local context in the
  commitments is strict, as after a conjunct that a disjunct follows (`isLocalContext_and_or`,
  `commitments_and_or`); the paper's comparison of the two is for the propositional case without
  this restriction.
* Presuppositions in the scope of quantifiers, and logical forms with predicate abstraction.

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

open Interpreter ManySorted ManySorted.Language Presupposition DomainSemantics Set
open scoped ModalLogic

variable {E W : Type}

/-- The type of propositions. -/
local notation "st" => Ty.intens Ty.t

/-! ### Logical forms -/

/-- A lexical item of type `a`: a continuized meaning at each answer that awaits arguments of
given types before a proposition. -/
abbrev Item (E W : Type) (a : Ty Base) : Type :=
  ∀ l : List (Ty Base), Cont ((Ty.arrows l st).Domain E W) (a.Domain E W)

/-- A logical form of type `a`: a derivation by functional application. -/
abbrev LF (E W : Type) (a : Ty Base) : Type := Deriv application (Item E W) a

namespace LF

variable {a b : Ty Base}

/-- A lexical item without a presupposition, which gives its value to its context. -/
abbrev lex (x : a.Domain E W) : LF E W a := .leaf fun _ κ ↦ κ x

/-- A functor applied to the argument on its right. -/
abbrev fa (f : LF E W (a ⇒ b)) (x : LF E W a) : LF E W b := .binary Application.fa f x

/-- A functor applied to the argument on its left. -/
abbrev ba (x : LF E W a) (f : LF E W (a ⇒ b)) : LF E W b := .binary Application.ba x f

/-- The meaning of a logical form at an answer that awaits arguments of the types `l`: the
value of the derivation continuized in order. -/
def value (d : LF E W a) (l : List (Ty Base)) :
    Cont ((Ty.arrows l st).Domain E W) (a.Domain E W) :=
  (d.continuize st l).realize (inferInstance : (continuized application).Structure
    (Ty.Dom (Base.Dom E W))) fun | .at x l => x l

end LF

open LF

/-- An ordinary item at each answer type, which gives its value to its context. -/
def ret : {a : Ty Base} → Continuized.Item st (fun a ↦ a.Domain E W) a → a.Domain E W
  | _, .at x _ => fun κ ↦ κ x

/-- Simulation: a derivation over ordinary items has, continuized and in the empty context, the
proposition it has in the structure of application. -/
theorem lower_value_lex (d : Deriv application (fun a ↦ a.Domain E W) st) :
    ((d.continuize st []).realize (inferInstance : (continuized application).Structure
      (Ty.Dom (Base.Dom E W))) ret) id =
      d.realize (inferInstance : application.Structure (Ty.Dom (Base.Dom E W))) fun x ↦ x :=
  congrFun (realize_continuize (p := st) (fun x ↦ x) ret (fun _ _ ↦ rfl) d []) id

/-! ### Commitments of a context -/

/-- The commitments of a context: those of the propositions it gives, over its value and the
arguments its answer awaits. -/
abbrev contextCommitments (E : Type) {W : Type} (l : List (Ty Base))
    (κ : (Ty.arrows l st).Domain E W) : W → Prop :=
  commitments (saturations (Base.Dom E W) st l κ)

section Commitments

variable {a b c : Ty Base} {w : W}

theorem contextCommitments₁ {κ : a.Domain E W → W → Prop} :
    contextCommitments E [a] κ w ↔ (∃ x, κ x w) ∧ ∃ x, ¬ κ x w := by
  simp only [commitments_apply, saturations, mem_iUnion, mem_singleton_iff]
  exact ⟨fun ⟨⟨_, ⟨x, rfl⟩, h⟩, _, ⟨y, rfl⟩, h'⟩ ↦ ⟨⟨x, h⟩, y, h'⟩,
    fun ⟨⟨x, h⟩, y, h'⟩ ↦ ⟨⟨_, ⟨x, rfl⟩, h⟩, _, ⟨y, rfl⟩, h'⟩⟩

theorem contextCommitments₂ {κ : a.Domain E W → b.Domain E W → W → Prop} :
    contextCommitments E [a, b] κ w ↔ (∃ x y, κ x y w) ∧ ∃ x y, ¬ κ x y w := by
  simp only [commitments_apply, saturations, mem_iUnion, mem_singleton_iff]
  exact ⟨fun ⟨⟨_, ⟨x, y, rfl⟩, h⟩, _, ⟨x', y', rfl⟩, h'⟩ ↦ ⟨⟨x, y, h⟩, x', y', h'⟩,
    fun ⟨⟨x, y, h⟩, x', y', h'⟩ ↦ ⟨⟨_, ⟨x, y, rfl⟩, h⟩, _, ⟨x', y', rfl⟩, h'⟩⟩

theorem contextCommitments₃ {κ : a.Domain E W → b.Domain E W → c.Domain E W → W → Prop} :
    contextCommitments E [a, b, c] κ w ↔ (∃ x y z, κ x y z w) ∧ ∃ x y z, ¬ κ x y z w := by
  simp only [commitments_apply, saturations, mem_iUnion, mem_singleton_iff]
  exact ⟨fun ⟨⟨_, ⟨x, y, z, rfl⟩, h⟩, _, ⟨x', y', z', rfl⟩, h'⟩ ↦ ⟨⟨x, y, z, h⟩, x', y', z', h'⟩,
    fun ⟨⟨x, y, z, h⟩, x', y', z', h'⟩ ↦
      ⟨⟨_, ⟨x, y, z, rfl⟩, h⟩, _, ⟨x', y', z', rfl⟩, h'⟩⟩

variable (p : W → Prop)

-- The row of *and*, and the initial context: it is safe to suppose `p`.
theorem commitments_and : contextCommitments E [st] (fun q : W → Prop ↦ p ⊓ q) = p :=
  funext fun _ ↦ propext <| contextCommitments₁.trans
    ⟨fun ⟨⟨_, h⟩, _⟩ ↦ h.1, fun h ↦ ⟨⟨⊤, h, trivial⟩, ⊥, fun h' ↦ h'.2⟩⟩

-- The row of *or*: it is safe to suppose that `p` is false.
theorem commitments_or : contextCommitments E [st] (fun q : W → Prop ↦ p ⊔ q) = pᶜ :=
  funext fun _ ↦ propext <| contextCommitments₁.trans
    ⟨fun ⟨_, _, h⟩ hp ↦ h (Or.inl hp), fun h ↦ ⟨⟨⊤, Or.inr trivial⟩, ⊥, fun h' ↦ h'.elim h id⟩⟩

-- The row of the material conditional: it is safe to suppose the antecedent.
theorem commitments_imp : contextCommitments E [st] (fun q : W → Prop ↦ p ⇨ q) = p :=
  funext fun _ ↦ propext <| contextCommitments₁.trans
    ⟨fun ⟨_, _, h⟩ ↦ by_contra fun hp ↦ h fun hp' ↦ (hp hp').elim,
      fun h ↦ ⟨⟨⊤, fun _ ↦ trivial⟩, ⊥, fun h' ↦ h' h⟩⟩

-- The row of negation, which adds nothing.
theorem commitments_not : contextCommitments E [st] (fun q : W → Prop ↦ qᶜ) = ⊤ :=
  funext fun _ ↦ propext <| contextCommitments₁.trans
    ⟨fun _ ↦ trivial, fun _ ↦ ⟨⟨⊥, id⟩, ⊤, fun h ↦ h trivial⟩⟩

end Commitments

/-! ### Commitments and transparency -/

section Transparency

variable {b : Ty Base} {κ : Set W → b.Domain E W → Set W} {x : Set W}

/-- The local context of transparency, for a truth-functional gap, is included in the
commitments of the context of the gap. -/
theorem isLocalContext_subset_commitments (hκ : ∀ y, IsTruthFunctional (κ · y))
    (hx : IsLocalContext univ (range fun y q ↦ κ q y) x) :
    x ⊆ {w | contextCommitments E [st, b] (fun q y w ↦ w ∈ κ {w | q w} y) w} := fun w hw ↦ by
  have h := (hx.subset_commitments (by rintro _ ⟨y, rfl⟩; exact hκ y) hw).2
  obtain ⟨⟨_, hp, h₁⟩, _, hq, h₂⟩ := mem_commitments.1 h
  simp only [mem_iUnion, mem_range, exists_prop, exists_exists_eq_and] at hp hq
  obtain ⟨y, q, rfl⟩ := hp
  obtain ⟨y', q', rfl⟩ := hq
  exact contextCommitments₂.2 ⟨⟨(· ∈ q), y, h₁⟩, (· ∈ q'), y', h₂⟩

-- A sentence-final gap: the commitments are the local context of transparency.
theorem isLocalContext_commitments {κ : Set W → Set W} (hκ : IsTruthFunctional κ) :
    IsLocalContext univ {κ} {w | contextCommitments E [st] (fun q w ↦ w ∈ κ {w | q w}) w} := by
  convert isLocalContext_singleton_of_isTruthFunctional (C := univ) hκ using 1
  rw [univ_inter]
  ext w
  refine (contextCommitments₁ (E := E) (a := st)).trans ?_
  rw [mem_commitments]
  simp only [mem_range, exists_exists_eq_and]
  exact ⟨fun ⟨⟨_, h⟩, _, h'⟩ ↦ ⟨⟨_, h⟩, _, h'⟩,
    fun ⟨⟨q, h⟩, q', h'⟩ ↦ ⟨⟨(· ∈ q), h⟩, (· ∈ q'), h'⟩⟩

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
theorem commitments_and_or (p : W → Prop) :
    contextCommitments E [st, st] (fun q c : W → Prop ↦ p ⊓ q ⊔ c) = ⊤ :=
  funext fun _ ↦ propext <| contextCommitments₂.trans
    ⟨fun _ ↦ trivial, fun _ ↦ ⟨⟨⊥, ⊤, Or.inr trivial⟩, ⊥, ⊥, fun h ↦ h.elim (·.2) id⟩⟩

end Transparency

/-! ### Conjunction -/

/-- Conjunction, taking the right conjunct first. -/
def conj : (st ⇒ st ⇒ st).Domain E W := fun q p ↦ p ⊓ q

section Conjunction

variable (rain : W → Prop) (ann : E) (t : Item E W (Ty.e ⇒ st)) (κ : (W → Prop) → W → Prop)

-- In *it rained and Ann [knows it rained]*, the context of the verb phrase contains the left
-- conjunct.
theorem value_right_conjunct :
    (ba (lex (a := st) rain) (fa (lex conj) (ba (lex ann) (.leaf t)))).value [] κ =
      t [] fun v ↦ κ (rain ⊓ v ann) := rfl

/-- The commitments of the context of a verb phrase in a right conjunct, in the initial context
of `c`, entail the left conjunct. -/
theorem commitments_right_conjunct (c : W → Prop) :
    contextCommitments E [Ty.e ⇒ st] (fun v : E → W → Prop ↦ c ⊓ (rain ⊓ v ann)) = c ⊓ rain :=
  funext fun _ ↦ propext <| contextCommitments₁.trans
    ⟨fun ⟨⟨_, hc, hr, _⟩, _⟩ ↦ ⟨hc, hr⟩, fun ⟨hc, hr⟩ ↦
      ⟨⟨fun _ ↦ ⊤, hc, hr, trivial⟩, fun _ ↦ ⊥, fun h ↦ h.2.2⟩⟩

-- In *Ann [knows it rained] and it rained*, the context of the verb phrase awaits the right
-- conjunct.
theorem value_left_conjunct :
    (ba (ba (lex ann) (.leaf t)) (fa (lex conj) (lex (a := st) rain))).value [] κ =
      t [st ⇒ st] (fun v f ↦ κ (f (v ann))) (conj (E := E) rain) := rfl

/-- The context of a verb phrase in a left conjunct has the commitments of the initial
context. -/
theorem commitments_left_conjunct :
    contextCommitments E [Ty.e ⇒ st, st ⇒ st]
        (fun (v : E → W → Prop) (f : (W → Prop) → W → Prop) ↦ κ (f (v ann))) =
      contextCommitments E [st] κ :=
  funext fun _ ↦ propext <| contextCommitments₂.trans <| Iff.trans
    ⟨fun ⟨⟨_, _, h⟩, _, _, h'⟩ ↦ ⟨⟨_, h⟩, _, h'⟩,
      fun ⟨⟨q, h⟩, q', h'⟩ ↦ ⟨⟨fun _ ↦ q, id, h⟩, fun _ ↦ q', id, h'⟩⟩
    contextCommitments₁.symm

-- With the symmetric rule, the context of a verb phrase in a left conjunct contains the right
-- conjunct.
theorem realize_sym_left_conjunct :
    (Deriv.binary (L := continuized application) (Continuized.sym Application.ba st)
        (.binary (Continuized.sym Application.ba st) (.leaf (Continuized.Item.at
          (p := st) (W := Item E W) (a := Ty.e) (fun _ κ ↦ κ ann) []))
          (.leaf (.at t [])))
        (.leaf (.at (a := st ⇒ st) (fun _ κ ↦ κ (conj (E := E) rain)) []))).realize
      (inferInstance : (continuized application).Structure (Ty.Dom (Base.Dom E W)))
      (fun | .at x l => x l) κ = t [] fun v ↦ κ (v ann ⊓ rain) := rfl

end Conjunction

/-! ### Epistemic modality -/

section Might

variable (c rain : W → Prop)

/-- *Might* as a test: the *might* of domain semantics at the commitments of the local
context. -/
def mightTest : Item E W (st ⇒ st) :=
  fun l κ ↦ κ fun p ↦
    (Sentence.ofProp {w | p w}).might {w | contextCommitments E ((st ⇒ st) :: l) κ w}

-- In *not rain and [might] rain*, the context of the modal contains the left conjunct.
theorem value_modal_right_conjunct (t : Item E W (st ⇒ st)) (κ : (W → Prop) → W → Prop) :
    (ba (lex (a := st) rainᶜ) (fa (lex conj) (fa (.leaf t) (lex (a := st) rain)))).value [] κ =
      t [st] (fun (f : (W → Prop) → W → Prop) (q : W → Prop) ↦ κ (rainᶜ ⊓ f q)) rain := rfl

private theorem commitments_modal_right_conjunct :
    contextCommitments E [st ⇒ st, st]
      (fun (f : (W → Prop) → W → Prop) (q : W → Prop) ↦ c ⊓ (rainᶜ ⊓ f q)) = c ⊓ rainᶜ :=
  funext fun _ ↦ propext <| contextCommitments₂.trans
    ⟨fun ⟨⟨_, _, hc, hr, _⟩, _⟩ ↦ ⟨hc, hr⟩, fun ⟨hc, hr⟩ ↦
      ⟨⟨fun _ ↦ ⊤, ⊥, hc, hr, trivial⟩, fun _ ↦ ⊥, ⊥, fun h ↦ h.2.2⟩⟩

/-- *It isn't raining, but it might be raining* is a contradiction in every initial context. -/
theorem not_rain_and_mightTest_rain :
    (ba (lex (a := st) rainᶜ) (fa (lex conj) (fa (.leaf (mightTest (E := E)))
      (lex (a := st) rain)))).value [] (fun p : W → Prop ↦ (c ⊓ p : W → Prop)) =
      (⊥ : W → Prop) := by
  refine funext fun w ↦ propext ⟨fun hw ↦ ?_, False.elim⟩
  obtain ⟨_, _, w', hw', hr⟩ := hw
  exact ((congrFun (commitments_modal_right_conjunct (E := E) c rain) w').mp hw').2 hr

-- *It might be raining, but it isn't raining* is true at the worlds of the initial context
-- without rain, if the initial context is consistent with rain.
theorem mightTest_rain_and_not_rain (h : ∃ w, c w ∧ rain w) :
    (ba (fa (.leaf (mightTest (E := E))) (lex (a := st) rain))
      (fa (lex conj) (lex (a := st) rainᶜ))).value [] (fun p : W → Prop ↦ (c ⊓ p : W → Prop)) =
      c ⊓ rainᶜ := by
  have hc : contextCommitments E [st ⇒ st, st, st ⇒ st] (fun (f : (W → Prop) → W → Prop)
      (q : W → Prop) (g : (W → Prop) → W → Prop) ↦ c ⊓ g (f q)) = c :=
    funext fun _ ↦ propext <| contextCommitments₃.trans
      ⟨fun ⟨⟨_, _, _, h, _⟩, _⟩ ↦ h, fun h ↦ ⟨⟨id, ⊤, id, h, trivial⟩, id, ⊥, id, fun h' ↦ h'.2⟩⟩
  refine funext fun w ↦ propext ⟨fun ⟨hw, _, hr⟩ ↦ ⟨hw, hr⟩, fun ⟨hw, hr⟩ ↦ ⟨hw, ?_, hr⟩⟩
  obtain ⟨w', hw', hr'⟩ := h
  exact ⟨w', (congrFun hc w').mpr hw', hr'⟩

/-- The domain condition of bounded *might* in a context with commitments `s`: if the evaluation
world is in `s`, so are its epistemic alternatives. -/
def bounded (R : SetRel W W) (s : W → Prop) : W → Prop := fun w ↦ s w → □[R] s w

-- With bounded *might*, *it isn't raining, but it might be raining* is false wherever the modal
-- is defined.
theorem not_rain_and_might_rain_of_bounded (R : SetRel W W) {w : W}
    (hw : bounded R (contextCommitments E [st ⇒ st, st]
      (fun (f : (W → Prop) → W → Prop) (q : W → Prop) ↦ c ⊓ (rainᶜ ⊓ f q))) w) :
    ¬ (c ⊓ (rainᶜ ⊓ ◇[R] rain)) w := by
  rintro ⟨hc, hr, w', hd, hw'⟩
  rw [commitments_modal_right_conjunct] at hw
  exact (hw ⟨hc, hr⟩ w' hd).2 hw'

end Might

/-! ### Attitude verbs -/

section Attitudes

variable (want : (W → Prop) → E → W → Prop) (dox : E → W → Prop)

/-- *Wants* applies its continuized complement to the context of the subject's beliefs. -/
def wants (p : Cont (W → Prop) (W → Prop)) : Item E W (Ty.e ⇒ st) :=
  fun _ κ ↦ κ fun x ↦ want (p fun q ↦ (q ⊓ dox x : W → Prop)) x

-- In *wants Bill [to stop smoking]*, the context of the embedded verb phrase is that of the
-- subject's beliefs.
theorem wants_ba (bill : E) (t : Item E W (Ty.e ⇒ st)) (l : List (Ty Base))
    (κ : (E → W → Prop) → (Ty.arrows l st).Domain E W) :
    wants want dox ((ba (lex bill) (.leaf t)).value []) l κ =
      κ fun x ↦ want (t [] fun v ↦ (v bill ⊓ dox x : W → Prop)) x := rfl

-- The commitments of the context of the verb phrase under *wants* are the subject's beliefs.
theorem commitments_wants (bill x : E) :
    contextCommitments E [Ty.e ⇒ st] (fun v : E → W → Prop ↦ v bill ⊓ dox x) = dox x :=
  funext fun _ ↦ propext <| contextCommitments₁.trans
    ⟨fun ⟨⟨_, h⟩, _⟩ ↦ h.2, fun h ↦ ⟨⟨fun _ ↦ ⊤, trivial, h⟩, fun _ ↦ ⊥, fun h' ↦ h'.1⟩⟩

end Attitudes

/-! ### A trigger evaluated before its arguments -/

section Both

variable {a b c : Ty Base} (κ : c.Domain E W → W → Prop)

-- In *[both] eyes opened*, the context of the determiner contains neither of its arguments.
theorem value_fa_fa (t : Item E W (a ⇒ b ⇒ c)) (x : a.Domain E W) (y : b.Domain E W) :
    (fa (fa (.leaf t) (lex x)) (lex y)).value [] κ = t [a, b] (fun f x y ↦ κ (f x y)) x y := rfl

-- The context of a functor both of whose arguments are still to come has the commitments of the
-- context of the whole.
theorem commitments_fa_fa [Nonempty (a.Domain E W)] [Nonempty (b.Domain E W)] :
    contextCommitments E [a ⇒ b ⇒ c, a, b] (fun (f : (a ⇒ b ⇒ c).Domain E W) x y ↦ κ (f x y)) =
      contextCommitments E [c] κ :=
  funext fun _ ↦ propext <| contextCommitments₃.trans <| Iff.trans
    ⟨fun ⟨⟨_, _, _, h⟩, _, _, _, h'⟩ ↦ ⟨⟨_, h⟩, _, h'⟩, fun ⟨⟨z, h⟩, z', h'⟩ ↦
      ⟨⟨fun _ _ ↦ z, Classical.arbitrary _, Classical.arbitrary _, h⟩,
        fun _ _ ↦ z', Classical.arbitrary _, Classical.arbitrary _, h'⟩⟩
    contextCommitments₁.symm

end Both

end Barker2022
