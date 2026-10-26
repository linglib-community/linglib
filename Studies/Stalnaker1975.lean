module

public import Linglib.Semantics.Conditionals.SelectionFunction
public import Linglib.Semantics.Reference.Rigidity

/-!
# Stalnaker (1975): Indicative Conditionals

This file formalizes Stalnaker's account of the direct argument, *either the butler or
the gardener did it, so if the butler didn't, the gardener did*. The indicative conditional
has the selection-function truth condition of Stalnaker's earlier theory, and entails the material
conditional without being entailed by it (`Conditional.selectionConditional_subset_materialImp`,
`not_entails_direct`). What makes the argument compelling is pragmatic: in a context, an
indicative conditional's selection function keeps to the context set whenever the antecedent
is compatible with it (`pragmaticConstraint`), and a disjunction is appropriately asserted only
where each disjunct can hold without the other. Under Stalnaker's earlier condition (4) on
selection functions, the constraint says that restricting the selection function to the context
set changes nothing at context worlds (`pragmaticConstraint_iff_restrict`). Under the
constraint, a proposition accepted in the context is accepted under any compatible antecedent
(`selectionConditional_of_accepted`), the indicative and the material conditional are accepted
in the same contexts (`accepted_iff_material`), and so the direct argument, contraposition and
the hypothetical syllogism are reasonable for indicatives (`direct_argument`, `contraposition`,
`hypothetical_syllogism`) though invalid (`Stalnaker1968.not_valid_contraposition`,
`Stalnaker1968.not_valid_trans`).

The appendix's calculus makes reasonable inference a logical notion: a pragmatic
interpretation assigns each sentence a proposition in a context, an appropriateness relation
and a change function obeying two postulates, and an inference is reasonable when every
context in which its premisses are appropriately asserted in sequence comes to entail its
conclusion (`PragmaticInterpretation.Reasonable`). An entailment whose conclusion expresses
the same proposition in every context is reasonable (`Reasonable.of_entails`). On the
language of the direct argument, whose contexts carry a
selection function obeying the constraint, the direct argument is reasonable in the language
(`direct_argument_reasonable`) though not an entailment in it. The fatalist's argument
(`fatalism`) draws each of its conditional conclusions reasonably within the context that
supposes a disjunct, and fails only by detaching them: constructive dilemma, valid for
entailment (`Entails.or`), does not hold for reasonable inference.

## Implementation notes

A context of the conditional language is a context set together with a selection function
obeying the pragmatic constraint for it, and assertion restricts the selection function to
the updated set, so that indicatives conform to the constraint after every assertion. The
appropriateness relation encodes the paper's two generalizations, that a disjunction requires
each disjunct to be open without the other and that an indicative conditional requires a
compatible antecedent, together with the first postulate. Subjunctive conditionals, which
suspend the constraint, are outside the language.

## References

* [stalnaker-1975]
* [stalnaker-1968]
* [grice-1975]
* [anderson-1951]
-/

@[expose] public section


namespace Stalnaker1975

open Conditional

/-! ### The pragmatic constraint -/

section Constraint

variable {W : Type*} (s : SelectionFunction W) {C : Set W}

/-- The pragmatic constraint on a selection function relative to a context set `C`. At a world of
`C`, an antecedent true somewhere in `C` selects a world of `C`, which Stalnaker glosses as the
worlds of the context set being closer to each other than to any world outside it. -/
def pragmaticConstraint (C : Set W) : Prop :=
  ∀ w (A : Set W), w ∈ C → (A ∩ C).Nonempty → s.sel w A ∈ C

theorem pragmaticConstraint_restrict (C : Set W) : pragmaticConstraint (s.restrict C) C :=
  fun w A hw hA ↦ by
    rw [s.restrict_sel_of_mem C hw hA]
    exact (s.inclusion w (A ∩ C) hA).2

/-- Under Stalnaker's condition (4), the pragmatic constraint says that restricting the selection
function to the context set changes nothing at context worlds. -/
theorem pragmaticConstraint_iff_restrict {s : SelectionFunction W} (hs : s.IsCSO) :
    pragmaticConstraint s C ↔ ∀ w ∈ C, ∀ A, (s.restrict C).sel w A = s.sel w A := by
  constructor
  · intro h w hw A
    by_cases hAC : (A ∩ C).Nonempty
    · rw [s.restrict_sel_of_mem C hw hAC]
      exact ((hs.sel_mem_iff hAC).1 (h w A hw hAC)).symm
    · exact s.restrict_sel_of_not_nonempty C hAC
  · intro h w A hw hAC
    rw [← h w hw A, s.restrict_sel_of_mem C hw hAC]
    exact (s.inclusion w (A ∩ C) hAC).2

theorem mem_selectionConditional_of_forall_mem {p q : Set W} {w : W} (hw : w ∈ C)
    (hopen : (p ∩ C).Nonempty) (hC : pragmaticConstraint s C)
    (himp : ∀ w' ∈ C, w' ∈ p → w' ∈ q) : w ∈ selectionConditional s p q := by
  obtain ⟨v, hv, -⟩ := id hopen
  rw [mem_selectionConditional_of_nonempty s ⟨v, hv⟩]
  exact himp _ (hC w p hw hopen) (s.inclusion w p ⟨v, hv⟩)

end Constraint

/-! ### The indicative conditional in a context -/

section Context

variable {W : Type*} (s : SelectionFunction W) {C p q r : Set W}

theorem selectionConditional_of_accepted (hC : pragmaticConstraint s C) (hp : ∃ w ∈ C, w ∈ p)
    (hq : ∀ w ∈ C, w ∈ q) : ∀ w ∈ C, w ∈ selectionConditional s p q := fun _ hw ↦
  mem_selectionConditional_of_forall_mem s hw (hp.imp fun _ hv ↦ ⟨hv.2, hv.1⟩) hC
    fun w' hw' _ ↦ hq w' hw'

theorem direct_argument (hC : pragmaticConstraint s C) (hopen : ∃ w ∈ C, w ∉ p)
    (hdisj : ∀ w ∈ C, w ∈ p ∨ w ∈ q) : ∀ w ∈ C, w ∈ selectionConditional s pᶜ q := fun _ hw ↦
  mem_selectionConditional_of_forall_mem s hw (hopen.imp fun _ hv ↦ ⟨hv.2, hv.1⟩) hC
    fun w' hw' hnp ↦ (hdisj w' hw').resolve_left hnp

theorem accepted_iff_material (hC : pragmaticConstraint s C) (hp : ∃ w ∈ C, w ∈ p) :
    (∀ w ∈ C, w ∈ selectionConditional s p q) ↔ ∀ w ∈ C, w ∈ p → w ∈ q :=
  ⟨fun h w hw ↦ selectionConditional_subset_materialImp s (h w hw), fun h _ hw ↦
    mem_selectionConditional_of_forall_mem s hw (hp.imp fun _ hv ↦ ⟨hv.2, hv.1⟩) hC h⟩

theorem contraposition (hC : pragmaticConstraint s C) (hq : ∃ w ∈ C, w ∉ q)
    (h : ∀ w ∈ C, w ∈ selectionConditional s p q) :
    ∀ w ∈ C, w ∈ selectionConditional s qᶜ pᶜ := by
  intro w hw
  have hne : (qᶜ).Nonempty := hq.imp fun _ hv ↦ hv.2
  rw [mem_selectionConditional_of_nonempty s hne]
  have hsel : s.sel w qᶜ ∈ C := hC w _ hw (hq.imp fun _ hv ↦ ⟨hv.2, hv.1⟩)
  exact fun hp ↦ s.inclusion w qᶜ hne (selectionConditional_subset_materialImp s (h _ hsel) hp)

theorem hypothetical_syllogism (hC : pragmaticConstraint s C) (hp : ∃ w ∈ C, w ∈ p)
    (h₁ : ∀ w ∈ C, w ∈ selectionConditional s p q) (h₂ : ∀ w ∈ C, w ∈ selectionConditional s q r) :
    ∀ w ∈ C, w ∈ selectionConditional s p r := by
  intro w hw
  have hne : p.Nonempty := hp.imp fun _ hv ↦ hv.2
  rw [mem_selectionConditional_of_nonempty s hne]
  have hsel : s.sel w p ∈ C := hC w _ hw (hp.imp fun _ hv ↦ ⟨hv.2, hv.1⟩)
  exact selectionConditional_subset_materialImp s (h₂ _ hsel)
    (selectionConditional_subset_materialImp s (h₁ _ hsel) (s.inclusion w p hne))

end Context

/-! ### Reasonable inference -/

/-- A pragmatic interpretation of a language, the paper's appendix, gives the proposition each
sentence expresses in a context, an appropriateness relation, and a change function, obeying
the two postulates that an appropriate assertion is compatible with the context and that an
assertion adds its proposition to the context set. -/
structure PragmaticInterpretation (L W K : Type*) where
  /-- The context set of a context. -/
  contextSet : K → Set W
  /-- The proposition a sentence expresses in a context. -/
  prop : L → K → Set W
  /-- Appropriateness of asserting a sentence in a context. -/
  appropriate : L → K → Prop
  /-- The context resulting from asserting a sentence. -/
  change : L → K → K
  /-- The first postulate: an appropriate assertion is compatible with the context. -/
  appropriate_compatible : ∀ P k, appropriate P k → (contextSet k ∩ prop P k).Nonempty
  /-- The second postulate: an assertion narrows the context set to its proposition. -/
  contextSet_change : ∀ P k, contextSet (change P k) = contextSet k ∩ prop P k

namespace PragmaticInterpretation

variable {L W K : Type*} (I : PragmaticInterpretation L W K)

/-- The context after asserting a sequence of sentences. -/
def changeSeq (σ : List L) (k : K) : K := σ.foldl (fun k P ↦ I.change P k) k

/-- A sequence of sentences is appropriate when each is appropriate in the context the
preceding ones produce. -/
def AppropriateSeq : List L → K → Prop
  | [], _ => True
  | P :: σ, k => I.appropriate P k ∧ AppropriateSeq σ (I.change P k)

/-- An inference is reasonable when every context in which the premisses are appropriately
asserted in sequence comes to entail the conclusion. -/
def Reasonable (σ : List L) (P : L) : Prop :=
  ∀ k, I.AppropriateSeq σ k → I.contextSet (I.changeSeq σ k) ⊆ I.prop P (I.changeSeq σ k)

/-- A sentence entails another in the language when the premiss's proposition is included in
the conclusion's in every context. -/
def Entails (P Q : L) : Prop := ∀ k, I.prop P k ⊆ I.prop Q k

theorem changeSeq_singleton (P : L) (k : K) : I.changeSeq [P] k = I.change P k := rfl

theorem Reasonable.of_entails {P Q : L} (hQ : IsRigid (I.prop Q)) (h : I.Entails P Q) :
    I.Reasonable [P] Q := fun k _ ↦ by
  rw [changeSeq_singleton, I.contextSet_change, hQ (I.change P k) k]
  exact fun _ hw ↦ h _ hw.2

/-- Constructive dilemma holds for entailment, since with disjunction interpreted as union,
entailments from the disjuncts yield an entailment from the disjunction. -/
theorem Entails.or {P₁ P₂ Q₁ Q₂ P Q : L} (hP : ∀ k, I.prop P k = I.prop P₁ k ∪ I.prop P₂ k)
    (hQ : ∀ k, I.prop Q k = I.prop Q₁ k ∪ I.prop Q₂ k) (h₁ : I.Entails P₁ Q₁)
    (h₂ : I.Entails P₂ Q₂) : I.Entails P Q := fun k ↦ by
  rw [hP, hQ]
  exact Set.union_subset_union (h₁ k) (h₂ k)

end PragmaticInterpretation

/-! ### The language of the direct argument -/

/-- The sentences are built from atoms by negation, disjunction, and the indicative conditional. -/
inductive Sentence (Atom : Type*)
  | atom (a : Atom)
  | not (P : Sentence Atom)
  | or (P Q : Sentence Atom)
  | ifThen (P Q : Sentence Atom)

/-- A context is a context set with a selection function obeying the pragmatic constraint for
it. -/
structure Context (W : Type*) where
  /-- The context set. -/
  set : Set W
  /-- The selection function of the context. -/
  sel : SelectionFunction W
  /-- Indicative conditionals conform to the constraint. -/
  constraint : pragmaticConstraint sel set

variable {Atom W : Type*}

/-- The proposition a sentence expresses in a context under a valuation of the atoms. -/
def Sentence.prop (V : Atom → Set W) : Sentence Atom → Context W → Set W
  | .atom a, _ => V a
  | .not P, k => (P.prop V k)ᶜ
  | .or P Q, k => P.prop V k ∪ Q.prop V k
  | .ifThen P Q, k => selectionConditional k.sel (P.prop V k) (Q.prop V k)

/-- An assertion is appropriate when it is compatible with the context, a disjunction moreover
requires each disjunct to be open without the other, and an indicative conditional requires a
compatible antecedent. -/
def Sentence.Appropriate (V : Atom → Set W) : Sentence Atom → Context W → Prop
  | .or P Q, k =>
    (k.set ∩ (P.prop V k ∩ (Q.prop V k)ᶜ)).Nonempty ∧
      (k.set ∩ (Q.prop V k ∩ (P.prop V k)ᶜ)).Nonempty
  | .ifThen P Q, k =>
    (k.set ∩ P.prop V k).Nonempty ∧ (k.set ∩ (Sentence.ifThen P Q).prop V k).Nonempty
  | P, k => (k.set ∩ P.prop V k).Nonempty

/-- The context after accepting a proposition has the narrowed context set with the selection
function restricted to it. -/
noncomputable def Context.update (k : Context W) (P : Set W) : Context W :=
  ⟨k.set ∩ P, k.sel.restrict (k.set ∩ P), pragmaticConstraint_restrict _ _⟩

/-- The pragmatic interpretation of the language under a valuation. -/
noncomputable def interp (V : Atom → Set W) : PragmaticInterpretation (Sentence Atom) W (Context W)
    where
  contextSet := Context.set
  prop := Sentence.prop V
  appropriate := Sentence.Appropriate V
  change P k := k.update (P.prop V k)
  appropriate_compatible P k h := by
    cases P with
    | or P Q =>
      obtain ⟨w, hw, hP, -⟩ := h.1
      exact ⟨w, hw, Or.inl hP⟩
    | ifThen P Q => exact h.2
    | atom a => exact h
    | not P => exact h
  contextSet_change _ _ := rfl

/-- An inference is reasonable in the language when it is reasonable under every valuation. -/
def ReasonableInL (W : Type*) (σ : List (Sentence Atom)) (P : Sentence Atom) : Prop :=
  ∀ V : Atom → Set W, (interp V).Reasonable σ P

/-- A sentence entails another in the language when it does so under every valuation. -/
def EntailsInL (W : Type*) (P Q : Sentence Atom) : Prop :=
  ∀ V : Atom → Set W, (interp V).Entails P Q

theorem ifThen_entails_material (P Q : Sentence Atom) :
    EntailsInL W (.ifThen P Q) (.or (.not P) Q) := fun V k w h ↦ by
  by_cases hp : w ∈ P.prop V k
  · exact Or.inr (selectionConditional_subset_materialImp k.sel h hp)
  · exact Or.inl hp

theorem direct_argument_reasonable (a b : Atom) :
    ReasonableInL W [.or (.atom a) (.atom b)] (.ifThen (.not (.atom a)) (.atom b)) := by
  rintro V k ⟨⟨-, hopen⟩, -⟩
  refine direct_argument (Context.sel _) (Context.constraint _) ?_ ?_
  · obtain ⟨w, hw, hb, ha⟩ := hopen
    exact ⟨w, ⟨hw, Or.inr hb⟩, ha⟩
  · exact fun w hw ↦ hw.2

/-! ### The direct argument is not an entailment -/

/-- The suspects. -/
inductive Suspect
  | butler | gardener | someoneElse
  deriving DecidableEq, Repr

/-- The atoms of the butler-or-gardener argument. -/
inductive Culprit
  | butler | gardener
  deriving DecidableEq, Repr

/-- The valuation on which each atom names its suspect. -/
def culpritOf : Culprit → Set Suspect
  | .butler => {.butler}
  | .gardener => {.gardener}

open Classical in
/-- A selection function that, off the antecedent, reaches for someone else first. -/
noncomputable def someoneElseFirst : SelectionFunction Suspect :=
  .ofSel (fun w A ↦
      if w ∈ A then w
      else if Suspect.someoneElse ∈ A then .someoneElse
      else if Suspect.gardener ∈ A then .gardener
      else .butler)
    (fun w A hA ↦ by
      split_ifs with hw hs hg
      · exact hw
      · exact hs
      · exact hg
      · obtain ⟨v, hv⟩ := hA
        cases v with
        | butler => exact hv
        | gardener => exact absurd hv hg
        | someoneElse => exact absurd hv hs)
    fun w A hw ↦ by simp [hw]

theorem not_entails_direct :
    ¬ EntailsInL Suspect (.or (.atom Culprit.butler) (.atom .gardener))
      (.ifThen (.not (.atom .butler)) (.atom .gardener)) := by
  intro h
  have := h culpritOf ⟨Set.univ, someoneElseFirst, fun _ _ _ _ ↦ trivial⟩
    (show Suspect.butler ∈ (interp culpritOf).prop (.or (.atom .butler) (.atom .gardener)) _ from
      Or.inl rfl)
  change Suspect.butler ∈ selectionConditional someoneElseFirst {Suspect.butler}ᶜ {.gardener}
    at this
  have h1 : Suspect.butler ∉ ({Suspect.butler}ᶜ : Set Suspect) := fun h ↦ h rfl
  have h2 : Suspect.someoneElse ∈ ({Suspect.butler}ᶜ : Set Suspect) :=
    fun h ↦ Suspect.noConfusion h
  rw [mem_selectionConditional_of_nonempty _ ⟨_, h2⟩] at this
  simp only [someoneElseFirst, SelectionFunction.sel_ofSel, ite_eq_right h1, ite_eq_left h2]
    at this
  exact (by decide : Suspect.someoneElse ≠ .gardener) this

/-! ### Fatalism -/

/-- The atoms of the fatalist's argument are being killed and taking precautions. -/
inductive Fate
  | killed | precautions
  deriving DecidableEq, Repr

/-- A world records whether one is killed and whether one takes precautions. -/
abbrev Outcome := Bool × Bool

/-- The valuation of the fatalist's atoms. -/
def fateOf : Fate → Set Outcome
  | .killed => {w | w.1 = true}
  | .precautions => {w | w.2 = true}

open Classical in
/-- A selection function that, off the antecedent, reaches first for survival. -/
noncomputable def survivalFirst : SelectionFunction Outcome :=
  .ofSel (fun w A ↦
      if w ∈ A then w
      else if (false, true) ∈ A then (false, true)
      else if (false, false) ∈ A then (false, false)
      else if (true, true) ∈ A then (true, true)
      else (true, false))
    (fun w A hA ↦ by
      split_ifs with hw h1 h2 h3
      · exact hw
      · exact h1
      · exact h2
      · exact h3
      · obtain ⟨v, hv⟩ := hA
        rcases v with ⟨_ | _, _ | _⟩
        · exact absurd hv h2
        · exact absurd hv h1
        · exact hv
        · exact absurd hv h3)
    fun w A hw ↦ by simp [hw]

/-- The null context of the fatalist, with a selection function reaching first for survival. -/
noncomputable def fateCtx : Context Outcome := ⟨Set.univ, survivalFirst, fun _ _ _ _ ↦ trivial⟩

/-- *I will be killed.* -/
def killed : Sentence Fate := .atom .killed

/-- *I take precautions.* -/
def precautions : Sentence Fate := .atom .precautions

theorem fatalism :
    (Sentence.or killed (.not killed)).Appropriate fateOf fateCtx ∧
    (fateCtx.update (killed.prop fateOf fateCtx)).set ⊆
      (Sentence.ifThen precautions killed).prop fateOf
        (fateCtx.update (killed.prop fateOf fateCtx)) ∧
    (fateCtx.update ((Sentence.not killed).prop fateOf fateCtx)).set ⊆
      (Sentence.ifThen (.not precautions) (.not killed)).prop fateOf
        (fateCtx.update ((Sentence.not killed).prop fateOf fateCtx)) ∧
    ¬ (fateCtx.update ((Sentence.or killed (.not killed)).prop fateOf fateCtx)).set ⊆
      (Sentence.or (.ifThen precautions killed) (.ifThen (.not precautions) (.not killed))).prop
        fateOf (fateCtx.update ((Sentence.or killed (.not killed)).prop fateOf fateCtx)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · show (Set.univ ∩ (fateOf .killed ∩ ((fateOf .killed)ᶜ)ᶜ)).Nonempty ∧
      (Set.univ ∩ ((fateOf .killed)ᶜ ∩ (fateOf .killed)ᶜ)).Nonempty
    exact ⟨⟨(true, true), trivial, rfl, fun h ↦ h rfl⟩,
      ⟨(false, true), trivial, Bool.false_ne_true, Bool.false_ne_true⟩⟩
  · have h1 := selectionConditional_of_accepted (survivalFirst.restrict (Set.univ ∩ fateOf .killed))
      (pragmaticConstraint_restrict _ _) (p := fateOf .precautions) (q := fateOf .killed)
      ⟨(true, true), ⟨trivial, rfl⟩, rfl⟩ fun _ hw ↦ hw.2
    exact fun w hw ↦ h1 w hw
  · have h2 := selectionConditional_of_accepted
      (survivalFirst.restrict (Set.univ ∩ (fateOf .killed)ᶜ)) (pragmaticConstraint_restrict _ _)
      (p := (fateOf .precautions)ᶜ) (q := (fateOf .killed)ᶜ)
      ⟨(false, false), ⟨trivial, Bool.false_ne_true⟩, Bool.false_ne_true⟩ fun _ hw ↦ hw.2
    exact fun w hw ↦ h2 w hw
  · intro h
    have hw := h (show (true, false) ∈ (fateCtx.update
      ((Sentence.or killed (.not killed)).prop fateOf fateCtx)).set from ⟨trivial, Or.inl rfl⟩)
    rcases hw with hw | hw
    · change (true, false) ∈ selectionConditional (survivalFirst.restrict _)
        (fateOf .precautions) (fateOf .killed) at hw
      rw [mem_selectionConditional_of_nonempty _
        (⟨(true, true), rfl⟩ : (fateOf .precautions).Nonempty),
        SelectionFunction.restrict_sel_of_mem] at hw
      · simp [survivalFirst, fateOf, Sentence.prop, fateCtx, killed] at hw
      · exact ⟨trivial, Or.inl rfl⟩
      · exact ⟨(false, true), rfl, trivial, Or.inr Bool.false_ne_true⟩
    · change (true, false) ∈ selectionConditional (survivalFirst.restrict _)
        (fateOf .precautions)ᶜ (fateOf .killed)ᶜ at hw
      rw [mem_selectionConditional_of_nonempty _
        (⟨(false, false), Bool.false_ne_true⟩ : (fateOf .precautions)ᶜ.Nonempty),
        SelectionFunction.centering] at hw
      · exact hw rfl
      · exact Bool.false_ne_true

end Stalnaker1975
