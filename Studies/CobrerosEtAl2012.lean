module

public import Linglib.Logic.Modal.Basic
public import Linglib.Logic.Trivalent.Propositional

/-!
# Cobreros, Égré, Ripley and van Rooij 2012: Tolerant, classical, strict

A T-model is a classical model whose predicates each carry an indifference relation `∼_P`, reflexive
and symmetric but possibly non-transitive (Definition 4), the vague predicate's "looks the same with
respect to `P`". Besides classical truth a T-model supports two further notions defined by
simultaneous induction (Definition 9): `Pa` is strictly true when every `∼_P`-neighbour of `a` is
classically `P` and tolerantly true when some neighbour is, negation swapping the two, so that the
strict extension sharpens and the tolerant extension coarsens the classical one (Lemma 1) and the
tolerance principle `Pa ∧ a I_P b → Pb` is tolerantly valid (Fact 2) up to two similarity steps
(Fact 3). Borderline cases are the tolerantly-but-not-strictly `P` individuals (Definition 10), the
ones tolerantly both `P` and `¬P`. On the similarity-free vocabulary tolerant validity is classical
validity while nothing is strictly valid (Theorems 1 and 2), so strict validity is not Fine's
supervaluationist validity, which is classical; and tolerant and strict consequence are Priest's LP
and Kleene's strong K3 (Theorem 3), via the model correspondences of Lemmas 4 and 5. Mixing the
three notions gives nine consequence relations `⊨ᵐⁿ` (Definition 17), ordered by Lemma 7, dualised
by Lemma 6, collapsing to four on the restricted vocabulary (Lemmas 8 and 9) but distinct once
similarity statements are expressible (§3.4), where the deduction theorem singles out the self-dual
`st`, `cc` and `ts` (Lemma 10). A relation is reflexive iff its premise standard is at most its
conclusion standard, and closed under cut when it is at least (§3.3.2); `ct`, `sc` and `st` fail
even simple transitivity (§3.4.1). The paper's choice is `st`, strict premises to tolerant
conclusions: it validates tolerance and modus ponens and is non-transitive, so it validates every
step of a sorites while invalidating the chain (§3.6, Version 1), and it makes the tolerance-premise
sorites valid but unsound, its tolerance premise not being strictly true (Version 2). The five-men
model of §4.2.3 gives the paper's account of Alxatib and Pelletier's data: the median man is
borderline however he is classified.

## Main definitions

* `TModel`, `TModel.Realize`, `Mode`: T-models and their three notions of truth, the modes
  ordered by strength `strict < classical < tolerant`.
* `TModel.Borderline`: Definition 10.
* `Valid`, `Unsat`, `Consequence`: Definitions 11, 12 and 17, the last multiple-conclusion
  `Consequence.MixedConsequence`.
* `IsRestricted`, `TModel.identity`, `allBorderline`, `toMV`, `ofMV`: the restricted
  vocabulary and the models of Lemmas 2, 3, 4 and 5.
* `series`: the sorites series of §3.4.1 and §3.6, whose instances are the four-element model
  of p. 354 and the five-men model of §4.2.3.

## Main results

* `TModel.realize_mono` (Lemma 1), `isDual` (Remark 1), `tolerance_valid` (Fact 2),
  `st_two_step` (Fact 3).
* `TModel.Borderline.exists_ne`: a model with a borderline case has two (footnote 4);
  `TModel.eq_tolerant_of_realize_conj_neg`: a contradiction can only be tolerantly true.
* `valid_tolerant_iff`, `unsat_strict_iff` (Theorem 1); `not_valid_strict`,
  `exists_realize_tolerant` (Theorem 2); `consequence_tolerant_iff_lp`,
  `consequence_strict_iff_k3` (Theorem 3).
* `consequence_iff_dual` (Lemma 6), `Consequence.mono` (Lemma 7), `Consequence.restricted_iff`
  (Lemma 8), `not_consequence_tolerant_strict` (Lemma 9), `Consequence.iff_valid_imp`,
  `deductionTheorem_iff`, `Consequence.iff_valid_imp_of_restricted` (Lemma 10).
* `not_cc_one_step`, `not_valid_classical_tolerance`, `not_sc_two_step`, `not_ct_two_step`:
  the §3.4 distinctness of `cc`, `sc`, `ct` and `st`, on the four-element model.
* `stdRefl_consequence_iff`, `Consequence.cut`, `isTrans_consequence_iff`: reflexivity and
  transitivity of the nine relations (§§3.3.2, 3.4.1).
* `not_st_version1`, `st_version2`, `not_series_realize_strict_tolerance`: the sorites of
  §3.6.
* `alxatibPelletier_median_borderline`: the five-men model of §4.2.3.

## Implementation notes

The language is the paper's propositional fragment over a set of constants `C`: negation and
conjunction over predications `Pa` and similarity statements `a I_P b`, with disjunction and
the conditional defined classically. The universally quantified principles appear as their
instances, which the paper notes changes nothing (§3.6). Identity, which the paper adds in
§2.3.1, is not represented. Consequence quantifies over T-models of every domain in the
universe of `C` (`TModels`), as the paper's does; the atomic strict and tolerant clauses are
`ModalLogic.Box` and `ModalLogic.Diamond` along `∼_P`, so Lemma 1's atomic case is the T axiom.

## References

* [P. Cobreros, P. Égré, D. Ripley and R. van Rooij, *Tolerant, Classical, Strict*
  (2012)][cobreros-etal-2012]
* [S. Alxatib and F. J. Pelletier, *The Psychology of Vagueness: Borderline Cases and
  Contradictions* (2011)][alxatib-pelletier-2011]
* [K. Fine, *Vagueness, truth and logic* (1975)][fine-1975]
* [S. C. Kleene, *Introduction to Metamathematics* (1952)][kleene-1952]
* [G. Priest, *The Logic of Paradox* (1979)][priest-1979]
-/

@[expose] public section

universe u

namespace CobrerosEtAl2012

open ModalLogic (IsKTBFrame Box Diamond box_T)
open scoped SetRel
open scoped ModalLogic Trivalent.Formula
open Consequence (IsDual MixedConsequence isTrans_mixedConsequence mixedConsequence_cons_cons_iff
  mixedConsequence_iff_dual mixedConsequence_nil_singleton mixedConsequence_singleton_nil
  mixedConsequence_singleton_right stdRefl_mixedConsequence_iff)

/-! ### T-models -/

/-- A T-model (Definition 4) is a classical model of the constants `C` and predicates `Pred` over
the domain `D`, with for each predicate a reflexive and symmetric, possibly non-transitive,
indifference relation `∼_P`. -/
structure TModel (Pred C : Type*) (D : Type*) where
  /-- The interpretation of the constants. -/
  const : C → D
  /-- The classical extension of each predicate. -/
  interp : Pred → D → Prop
  /-- The indifference relation `∼_P` of each predicate. -/
  sim : Pred → SetRel D D
  sim_ktb : ∀ P, IsKTBFrame (sim P)

variable {Pred : Type*} {C : Type u} {D : Type*}

instance (M : TModel Pred C D) (P : Pred) : IsKTBFrame (M.sim P) := M.sim_ktb P

/-- The three notions of truth, ordered by strength as `strict < classical < tolerant`. -/
inductive Mode
  | strict
  | classical
  | tolerant
  deriving DecidableEq, Fintype

namespace Mode

/-- The duality `d` of Definition 20, with `d(t) = s`, `d(s) = t` and `d(c) = c`. -/
def dual : Mode → Mode
  | strict => tolerant
  | classical => classical
  | tolerant => strict

theorem dual_involutive : Function.Involutive dual := fun m ↦ by cases m <;> rfl

@[simp] theorem dual_dual (m : Mode) : m.dual.dual = m := dual_involutive m

@[simp] theorem dual_strict : strict.dual = tolerant := rfl
@[simp] theorem dual_classical : classical.dual = classical := rfl
@[simp] theorem dual_tolerant : tolerant.dual = strict := rfl

def rank : Mode → Fin 3
  | strict => 0
  | classical => 1
  | tolerant => 2

instance : LinearOrder Mode := LinearOrder.lift' rank (by decide)

theorem strict_le (m : Mode) : strict ≤ m := by cases m <;> decide

theorem le_tolerant (m : Mode) : m ≤ tolerant := by cases m <;> decide

end Mode

/-- The atomic sentences are predications `Pa` and similarity statements `a I_P b`
(Definition 8). -/
inductive Atom (Pred C : Type*)
  | pred : Pred → C → Atom Pred C
  | sim : Pred → C → C → Atom Pred C

/-- The propositional fragment of the language (Definition 2). -/
abbrev Formula (Pred C : Type*) := Trivalent.Formula (Atom Pred C)

/-- The instance `Pa ∧ a I_P b → Pb` of the tolerance principle (1). -/
def tolerance (P : Pred) (a b : C) : Formula Pred C :=
  Trivalent.Formula.cond (.conj (.atom (.pred P a)) (.atom (.sim P a b))) (.atom (.pred P b))

namespace TModel

/-- Truth in a mode (Definition 9, with Definition 5 for the classical mode). A predication is
strictly true when `P` holds throughout the `∼_P`-neighbourhood of the individual, `□`, and
tolerantly true when it holds somewhere in it, `◇`; negation swaps to the dual mode; and
similarity statements are classical in every mode (Remark 2). -/
def Realize (M : TModel Pred C D) : Mode → Formula Pred C → Prop
  | _, .atom (.sim P a b) => (M.const a) ~[M.sim P] (M.const b)
  | .classical, .atom (.pred P a) => M.interp P (M.const a)
  | .strict, .atom (.pred P a) => □[M.sim P] (M.interp P) (M.const a)
  | .tolerant, .atom (.pred P a) => ◇[M.sim P] (M.interp P) (M.const a)
  | m, .neg φ => ¬ M.Realize m.dual φ
  | m, .conj φ ψ => M.Realize m φ ∧ M.Realize m ψ
  | m, .disj φ ψ => M.Realize m φ ∨ M.Realize m ψ
  | m, .cond φ ψ => M.Realize m.dual φ → M.Realize m ψ

variable (M : TModel Pred C D)

@[simp] theorem realize_sim (m : Mode) (P : Pred) (a b : C) :
    M.Realize m (.atom (.sim P a b)) ↔ (M.const a) ~[M.sim P] (M.const b) := by cases m <;> rfl

@[simp] theorem realize_classical_pred (P : Pred) (a : C) :
    M.Realize .classical (.atom (.pred P a)) ↔ M.interp P (M.const a) := Iff.rfl

@[simp] theorem realize_strict_pred (P : Pred) (a : C) :
    M.Realize .strict (.atom (.pred P a)) ↔ □[M.sim P] (M.interp P) (M.const a) := Iff.rfl

@[simp] theorem realize_tolerant_pred (P : Pred) (a : C) :
    M.Realize .tolerant (.atom (.pred P a)) ↔ ◇[M.sim P] (M.interp P) (M.const a) := Iff.rfl

@[simp] theorem realize_neg (m : Mode) (φ : Formula Pred C) :
    M.Realize m (.neg φ) ↔ ¬ M.Realize m.dual φ := Iff.rfl

@[simp] theorem realize_conj (m : Mode) (φ ψ : Formula Pred C) :
    M.Realize m (.conj φ ψ) ↔ M.Realize m φ ∧ M.Realize m ψ := Iff.rfl

@[simp] theorem realize_disj (m : Mode) (φ ψ : Formula Pred C) :
    M.Realize m (φ.disj ψ) ↔ M.Realize m φ ∨ M.Realize m ψ := Iff.rfl

-- Fact 3
@[simp] theorem realize_cond (m : Mode) (φ ψ : Formula Pred C) :
    M.Realize m (φ.cond ψ) ↔ (M.Realize m.dual φ → M.Realize m ψ) := Iff.rfl

@[simp] theorem realize_foldr_conj (m : Mode) (φ : Formula Pred C) (Γ : List (Formula Pred C)) :
    M.Realize m (Γ.foldr .conj φ) ↔ (∀ γ ∈ Γ, M.Realize m γ) ∧ M.Realize m φ := by
  induction Γ with
  | nil => simp
  | cons γ Γ ih => simp [ih, and_assoc]

@[simp] theorem realize_foldr_disj (m : Mode) (φ : Formula Pred C) (Δ : List (Formula Pred C)) :
    M.Realize m (Δ.foldr .disj φ) ↔ (∃ δ ∈ Δ, M.Realize m δ) ∨ M.Realize m φ := by
  induction Δ with
  | nil => simp
  | cons δ Δ ih => simp [ih, or_assoc]

instance decidableRealize [Fintype D] [∀ P x y, Decidable (x ~[M.sim P] y)]
    [∀ P, DecidablePred (M.interp P)] : ∀ (m : Mode) (φ : Formula Pred C), Decidable (M.Realize m φ)
  | _, .atom (.sim P a b) => inferInstanceAs (Decidable ((M.const a) ~[M.sim P] (M.const b)))
  | .classical, .atom (.pred P a) => inferInstanceAs (Decidable (M.interp P (M.const a)))
  | .strict, .atom (.pred P a) =>
    inferInstanceAs (Decidable (□[M.sim P] (M.interp P) (M.const a)))
  | .tolerant, .atom (.pred P a) =>
    inferInstanceAs (Decidable (◇[M.sim P] (M.interp P) (M.const a)))
  | m, .neg φ => @instDecidableNot _ (decidableRealize m.dual φ)
  | m, .conj φ ψ => @instDecidableAnd _ _ (decidableRealize m φ) (decidableRealize m ψ)
  | m, .disj φ ψ => @instDecidableOr _ _ (decidableRealize m φ) (decidableRealize m ψ)
  | m, .cond φ ψ =>
    haveI := decidableRealize m.dual φ
    haveI := decidableRealize m ψ
    inferInstanceAs (Decidable (M.Realize m.dual φ → M.Realize m ψ))

/-- Strict truth implies classical truth, which implies tolerant truth (Lemma 1). -/
theorem realize_mono (φ : Formula Pred C) : Monotone (M.Realize · φ) := by
  have h : ∀ φ : Formula Pred C,
      (M.Realize .strict φ → M.Realize .classical φ) ∧
      (M.Realize .classical φ → M.Realize .tolerant φ) := by
    intro φ
    induction φ with
    | atom α =>
      cases α with
      | pred P a => exact ⟨box_T, fun h ↦ ⟨M.const a, (M.sim P).refl _, h⟩⟩
      | sim => exact ⟨id, id⟩
    | neg ψ ih => exact ⟨fun h hc ↦ h (ih.2 hc), fun h hs ↦ h (ih.1 hs)⟩
    | conj ψ χ ihψ ihχ =>
      exact ⟨fun h ↦ ⟨ihψ.1 h.1, ihχ.1 h.2⟩, fun h ↦ ⟨ihψ.2 h.1, ihχ.2 h.2⟩⟩
    | disj ψ χ ihψ ihχ => exact ⟨Or.imp ihψ.1 ihχ.1, Or.imp ihψ.2 ihχ.2⟩
    | cond ψ χ ihψ ihχ =>
      exact ⟨fun h hc ↦ ihχ.1 (h (ihψ.2 hc)), fun h hs ↦ ihχ.2 (h (ihψ.1 hs))⟩
  intro m m' hm x
  cases m <;> cases m' <;> first
    | exact x
    | exact absurd hm (by decide)
    | exact (h φ).1 x
    | exact (h φ).2 x
    | exact (h φ).2 ((h φ).1 x)

/-- A contradiction is true only tolerantly (§4.1). -/
theorem eq_tolerant_of_realize_conj_neg {m : Mode} {φ : Formula Pred C}
    (h : M.Realize m (.conj φ (.neg φ))) : m = .tolerant := by
  cases m with
  | tolerant => rfl
  | classical => exact absurd h.1 h.2
  | strict => exact absurd (M.realize_mono φ (by decide : Mode.strict ≤ .tolerant) h.1) h.2

-- §2.4
theorem realize_disj_neg {m : Mode} (hm : m ≠ .strict) (φ : Formula Pred C) :
    M.Realize m (φ.disj (.neg φ)) := by
  rw [realize_disj, realize_neg]
  cases m with
  | strict => exact absurd rfl hm
  | classical => exact em _
  | tolerant => exact (em _).imp_left (M.realize_mono φ (by decide))

/-! ### Borderline cases -/

/-- `d` is a borderline case of `P` iff it is tolerantly but not strictly `P` (Definition 10). -/
def Borderline (P : Pred) (d : D) : Prop :=
  ◇[M.sim P] (M.interp P) d ∧ ¬ □[M.sim P] (M.interp P) d

instance [Fintype D] [∀ P x y, Decidable (x ~[M.sim P] y)] [∀ P, DecidablePred (M.interp P)]
    (P : Pred) (d : D) : Decidable (M.Borderline P d) :=
  inferInstanceAs (Decidable (_ ∧ ¬ _))

-- p. 365
theorem borderline_iff (P : Pred) (d : D) : M.Borderline P d ↔
    (∃ e, d ~[M.sim P] e ∧ M.interp P e) ∧ ∃ e, d ~[M.sim P] e ∧ ¬ M.interp P e := by
  simp [Borderline, Box, Diamond]

-- Definition 10
theorem borderline_iff_realize_conj_neg (P : Pred) (a : C) :
    M.Borderline P (M.const a) ↔
      M.Realize .tolerant (.conj (.atom (.pred P a)) (.neg (.atom (.pred P a)))) := Iff.rfl

-- Definition 10
theorem borderline_iff_not_realize_strict (P : Pred) (a : C) :
    M.Borderline P (M.const a) ↔
      ¬ M.Realize .strict (.atom (.pred P a)) ∧ ¬ M.Realize .strict (.neg (.atom (.pred P a))) := by
  simp [Borderline, and_comm]

-- §2.4
theorem Borderline.not_realize_strict_disj {P : Pred} {a : C} (h : M.Borderline P (M.const a)) :
    ¬ M.Realize .strict ((Trivalent.Formula.atom (.pred P a)).disj (.neg (.atom (.pred P a)))) := by
  rw [realize_disj, realize_neg]
  exact fun hd ↦ hd.elim h.2 (fun hn ↦ hn h.1)

/-- By symmetry, a model with a borderline case has at least two (footnote 4). -/
theorem Borderline.exists_ne {P : Pred} {d : D} (h : M.Borderline P d) :
    ∃ e ≠ d, M.Borderline P e := by
  obtain ⟨⟨e₁, h₁, hP₁⟩, e₂, h₂, hP₂⟩ := (M.borderline_iff P d).1 h
  by_cases hd : M.interp P d
  · exact ⟨e₂, fun he ↦ hP₂ (he ▸ hd),
      (M.borderline_iff P e₂).2 ⟨⟨d, (M.sim P).symm h₂, hd⟩, e₂, (M.sim P).refl _, hP₂⟩⟩
  · exact ⟨e₁, fun he ↦ hd (he ▸ hP₁),
      (M.borderline_iff P e₁).2 ⟨⟨e₁, (M.sim P).refl _, hP₁⟩, d, (M.sim P).symm h₁, hd⟩⟩

end TModel

/-! ### Consequence -/

/-- The T-models of the language over every domain, which validity and consequence quantify
over (Definitions 11 and 17). -/
abbrev TModels (Pred : Type*) (C : Type u) := (D : Type u) × TModel Pred C D

/-- Truth in a bundled model. -/
abbrev TModels.Realize (M : TModels Pred C) : Mode → Formula Pred C → Prop := M.2.Realize

-- Lemma 1
theorem TModels.realize_monotone : Monotone fun m (M : TModels Pred C) ↦ M.Realize m :=
  fun _ _ hm M φ ↦ M.2.realize_mono φ hm

/-- `φ` is `n`-valid iff every T-model `n`-satisfies it (Definition 11). -/
abbrev Valid (n : Mode) (φ : Formula Pred C) : Prop := ∀ M : TModels Pred C, M.Realize n φ

/-- `φ` is `n`-unsatisfiable iff no T-model `n`-satisfies it (Definition 12). -/
abbrev Unsat (n : Mode) (φ : Formula Pred C) : Prop := ∀ M : TModels Pred C, ¬ M.Realize n φ

/-- `Γ ⊨ᵐⁿ Δ` iff every T-model that `m`-satisfies all of `Γ` `n`-satisfies some member of `Δ`
(Definition 17). -/
abbrev Consequence (m n : Mode) (Γ Δ : List (Formula Pred C)) : Prop :=
  MixedConsequence (TModels.Realize · m) (TModels.Realize · n) Γ Δ

variable {m n : Mode} {Γ Δ : List (Formula Pred C)} {φ ψ : Formula Pred C}

-- Definition 18
theorem consequence_nil_singleton : Consequence m n [] [φ] ↔ Valid n φ :=
  mixedConsequence_nil_singleton

-- Definition 18
theorem consequence_singleton_nil : Consequence m n [φ] [] ↔ Unsat m φ :=
  mixedConsequence_singleton_nil

theorem unsat_iff_valid_neg (n : Mode) (φ : Formula Pred C) :
    Unsat n φ ↔ Valid n.dual (.neg φ) := by
  simp [Valid]

/-- Consequence grows as premises are held to a stronger standard and conclusions to a weaker one
(Lemma 7). -/
theorem Consequence.mono {m' n' : Mode} (hm : m' ≤ m) (hn : n ≤ n') (h : Consequence m n Γ Δ) :
    Consequence m' n' Γ Δ :=
  MixedConsequence.mono (TModels.realize_monotone hm) (TModels.realize_monotone hn) h

/-- Negation swaps tolerant and strict truth and fixes classical truth (Remark 1, Definition 20). -/
theorem isDual (m : Mode) :
    IsDual .neg (fun M : TModels Pred C ↦ M.Realize m.dual) (TModels.Realize · m) :=
  fun M φ ↦ by simp [TModels.Realize]

/-- `⊨ᵐⁿ` is the dual of `⊨^{d(n)d(m)}`, so `Γ ⊨ᵐⁿ Δ` iff `¬Δ ⊨^{d(n)d(m)} ¬Γ` (Lemma 6). -/
theorem consequence_iff_dual :
    Consequence m n Γ Δ ↔ Consequence n.dual m.dual (Δ.map .neg) (Γ.map .neg) :=
  mixedConsequence_iff_dual (isDual m) (isDual n)

-- §3.1
theorem consequence_iff_dual_self (h : m = n.dual) :
    Consequence m n Γ Δ ↔ Consequence m n (Δ.map .neg) (Γ.map .neg) := by
  subst h
  simpa using consequence_iff_dual (m := n.dual) (n := n) (Γ := Γ) (Δ := Δ)

theorem Consequence.cons_cons_iff (h : m = n.dual) :
    Consequence m n (φ :: Γ) (ψ :: Δ) ↔ Consequence m n Γ (φ.cond ψ :: Δ) := by
  subst h
  exact mixedConsequence_cons_cons_iff fun M ↦ M.2.realize_cond n φ ψ

theorem consequence_cons_cons_iff_foldr :
    Consequence m n (φ :: Γ) (ψ :: Δ) ↔ Consequence m n [Γ.foldr .conj φ] [Δ.foldr .disj ψ] := by
  simp [MixedConsequence, Consequence.Satisfies, and_comm, or_comm]

/-- When `m = d(n)`, `Γ ⊨ᵐⁿ Δ` iff `⊨ᵐⁿ ⋀Γ → ⋁Δ`, for nonempty finite sides (Lemma 10, right to
left; footnote 13). -/
theorem Consequence.iff_valid_imp (h : m = n.dual) :
    Consequence m n (φ :: Γ) (ψ :: Δ) ↔ Valid n ((Γ.foldr .conj φ).cond (Δ.foldr .disj ψ)) :=
  consequence_cons_cons_iff_foldr.trans <|
    (Consequence.cons_cons_iff h).trans consequence_nil_singleton

/-- Cut holds when the premise standard is at least the conclusion standard, so `tc` and `cs`
are transitive (§3.3.2, footnote 11). -/
theorem Consequence.cut (h : n ≤ m) (h₁ : Consequence m n (φ :: Γ) Δ)
    (h₂ : Consequence m n Γ (φ :: Δ)) : Consequence m n Γ Δ :=
  MixedConsequence.cut (TModels.realize_monotone h) h₁ h₂

-- footnote 14, §3.3.2
theorem isTrans_consequence (h : n ≤ m) :
    IsTrans (Formula Pred C) fun φ ψ ↦ Consequence m n [φ] [ψ] :=
  isTrans_mixedConsequence (TModels.realize_monotone h)

/-! ### Tolerance -/

/-- The tolerance principle is tolerantly valid (Fact 2). -/
theorem tolerance_valid (P : Pred) (a b : C) : Valid .tolerant (tolerance P a b) := by
  rintro ⟨D, M⟩
  simp only [TModels.Realize, tolerance, TModel.realize_cond, TModel.realize_conj,
    TModel.realize_sim, Mode.dual_tolerant, TModel.realize_strict_pred,
    TModel.realize_tolerant_pred]
  exact fun ⟨hs, hab⟩ ↦ ⟨M.const b, (M.sim P).refl _, hs _ hab⟩

-- §3.4
theorem sc_one_step (P : Pred) (a b : C) :
    Consequence .strict .classical [.atom (.pred P a), .atom (.sim P a b)] [.atom (.pred P b)] :=
  mixedConsequence_singleton_right.2 fun ⟨_, M⟩ h ↦ by
    simp only [TModels.Realize, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq,
      TModel.realize_strict_pred, TModel.realize_sim] at h
    exact h.1 _ h.2

-- §3.4
theorem ct_one_step (P : Pred) (a b : C) :
    Consequence .classical .tolerant [.atom (.pred P a), .atom (.sim P a b)] [.atom (.pred P b)] :=
  mixedConsequence_singleton_right.2 fun ⟨_, M⟩ h ↦ by
    simp only [TModels.Realize, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq,
      TModel.realize_classical_pred, TModel.realize_sim] at h
    exact ⟨M.const a, (M.sim P).symm h.2, h.1⟩

-- §3.6
theorem st_one_step (P : Pred) (a b : C) :
    Consequence .strict .tolerant [.atom (.pred P a), .atom (.sim P a b)] [.atom (.pred P b)] :=
  (sc_one_step P a b).mono le_rfl (by decide)

/-- Tolerance holds up to two similarity steps (Fact 3). -/
theorem st_two_step (P : Pred) (a b c : C) :
    Consequence .strict .tolerant
      [.atom (.pred P a), .atom (.sim P a b), .atom (.sim P b c)] [.atom (.pred P c)] :=
  mixedConsequence_singleton_right.2 fun ⟨_, M⟩ h ↦ by
    simp only [TModels.Realize, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq,
      TModel.realize_strict_pred, TModel.realize_sim] at h
    exact ⟨M.const b, (M.sim P).symm h.2.2, h.1 _ h.2.1⟩

/-! ### The restricted vocabulary -/

/-- A formula is in the restricted vocabulary (§2) when it contains no similarity statements. -/
def IsRestricted : Formula Pred C → Prop
  | .atom (.pred _ _) => True
  | .atom (.sim _ _ _) => False
  | .neg φ => IsRestricted φ
  | .conj φ ψ | .disj φ ψ | .cond φ ψ => IsRestricted φ ∧ IsRestricted ψ

namespace TModel

variable (M : TModel Pred C D)

/-- The T-model of Lemma 2 is `M` with identity as every indifference relation. -/
def identity : TModel Pred C D :=
  { M with
    sim := fun _ ↦ .id
    sim_ktb := fun _ ↦ { refl := fun _ ↦ rfl, symm := fun _ _ ↦ Eq.symm } }

-- Lemma 2
theorem identity_realize (m : Mode) (φ : Formula Pred C) :
    M.identity.Realize m φ ↔ M.identity.Realize .classical φ := by
  induction φ generalizing m with
  | atom α =>
    cases α with
    | pred P a => cases m <;> simp [identity, Box, Diamond, SetRel.mem_id]
    | sim P a b => simp
  | neg ψ ih => simp [ih]
  | conj ψ χ ihψ ihχ | disj ψ χ ihψ ihχ | cond ψ χ ihψ ihχ => simp [ihψ, ihχ]

theorem identity_realize_classical {φ : Formula Pred C} (hφ : IsRestricted φ) :
    M.identity.Realize .classical φ ↔ M.Realize .classical φ := by
  induction φ with
  | atom α =>
    cases α with
    | pred P a => exact Iff.rfl
    | sim P a b => exact hφ.elim
  | neg ψ ih => simp [ih hφ]
  | conj ψ χ ihψ ihχ | disj ψ χ ihψ ihχ | cond ψ χ ihψ ihχ => simp [ihψ hφ.1, ihχ hφ.2]

end TModel

/-- On the restricted vocabulary, tolerant validity is classical validity (Theorem 1). -/
theorem valid_tolerant_iff (hφ : IsRestricted φ) : Valid .tolerant φ ↔ Valid .classical φ :=
  ⟨fun h ⟨D, M⟩ ↦ (M.identity_realize_classical hφ).1
      ((M.identity_realize _ φ).1 (h ⟨D, M.identity⟩)),
    fun h M ↦ M.2.realize_mono φ (by decide) (h M)⟩

/-- On the restricted vocabulary, strict unsatisfiability is classical unsatisfiability
(Theorem 1). -/
theorem unsat_strict_iff (hφ : IsRestricted φ) : Unsat .strict φ ↔ Unsat .classical φ := by
  rw [unsat_iff_valid_neg, unsat_iff_valid_neg, Mode.dual_strict, Mode.dual_classical]
  exact valid_tolerant_iff hφ

/-- The model of Lemma 3 has an individual for each constant plus one more, all indifferent, the
extra one alone falling outside every predicate, so that every predication is borderline. -/
def allBorderline (Pred C : Type*) : TModel Pred C (Option C) where
  const := some
  interp _ d := d.isSome
  sim _ := .univ
  sim_ktb _ := { refl := fun _ ↦ trivial, symm := fun _ _ _ ↦ trivial }

-- Lemma 3
theorem allBorderline_realize (hφ : IsRestricted φ) :
    ¬ (allBorderline Pred C).Realize .strict φ ∧ (allBorderline Pred C).Realize .tolerant φ := by
  induction φ with
  | atom α =>
    cases α with
    | pred P a =>
      exact ⟨fun h ↦ by simpa [allBorderline] using h none trivial, some a, trivial, rfl⟩
    | sim P a b => exact hφ.elim
  | neg ψ ih => exact ⟨fun h ↦ h (ih hφ).2, (ih hφ).1⟩
  | conj ψ χ ihψ ihχ => exact ⟨fun h ↦ (ihψ hφ.1).1 h.1, (ihψ hφ.1).2, (ihχ hφ.2).2⟩
  | disj ψ χ ihψ ihχ =>
    exact ⟨fun h ↦ h.elim (ihψ hφ.1).1 (ihχ hφ.2).1, .inl (ihψ hφ.1).2⟩
  | cond ψ χ ihψ ihχ => exact ⟨fun h ↦ (ihχ hφ.2).1 (h (ihψ hφ.1).2), fun _ ↦ (ihχ hφ.2).2⟩

/-- No restricted formula is strictly valid (Theorem 2). -/
theorem not_valid_strict (hφ : IsRestricted φ) : ¬ Valid .strict φ :=
  fun h ↦ (allBorderline_realize hφ).1 (h ⟨_, allBorderline Pred C⟩)

/-- Every restricted formula is tolerantly satisfiable (Theorem 2). -/
theorem exists_realize_tolerant (hφ : IsRestricted φ) :
    ∃ M : TModels Pred C, M.Realize .tolerant φ :=
  ⟨⟨_, allBorderline Pred C⟩, (allBorderline_realize hφ).2⟩

-- Lemma 8
theorem Consequence.classical_of_st (hΓ : ∀ γ ∈ Γ, IsRestricted γ) (hΔ : ∀ δ ∈ Δ, IsRestricted δ)
    (h : Consequence .strict .tolerant Γ Δ) : Consequence .classical .classical Γ Δ :=
  h.comap (fun M ↦ ⟨_, M.2.identity⟩)
    (fun M γ hγ h ↦ (M.2.identity_realize _ γ).2 ((M.2.identity_realize_classical (hΓ γ hγ)).2 h))
    fun M δ hδ h ↦ (M.2.identity_realize_classical (hΔ δ hδ)).1 ((M.2.identity_realize _ δ).1 h)

/-- On the restricted vocabulary `cc`, `sc`, `ct` and `st` coincide (Lemma 8). -/
theorem Consequence.restricted_iff (hΓ : ∀ γ ∈ Γ, IsRestricted γ) (hΔ : ∀ δ ∈ Δ, IsRestricted δ)
    (hm : m ≤ .classical) (hn : .classical ≤ n) :
    Consequence m n Γ Δ ↔ Consequence .classical .classical Γ Δ :=
  ⟨fun h ↦ classical_of_st hΓ hΔ (h.mono (Mode.strict_le _) (Mode.le_tolerant _)),
    fun h ↦ h.mono hm hn⟩

/-- On the restricted vocabulary `ts`-consequence is empty (Lemma 9). -/
theorem not_consequence_tolerant_strict (hΓ : ∀ γ ∈ Γ, IsRestricted γ)
    (hΔ : ∀ δ ∈ Δ, IsRestricted δ) : ¬ Consequence .tolerant .strict Γ Δ := fun h ↦
  let ⟨δ, hδ, hs⟩ := h ⟨_, allBorderline Pred C⟩ fun γ hγ ↦ (allBorderline_realize (hΓ γ hγ)).2
  (allBorderline_realize (hΔ δ hδ)).1 hs

/-! ### LP and K3 -/

open Classical in
/-- In the MV-model of Lemma 4, a predication is `1` when strictly true, `-1` when not
tolerantly true and `0` when borderline, and similarity statements are two-valued. -/
noncomputable def toMV (M : TModel Pred C D) : Trivalent.Model (Atom Pred C)
  | .pred P a =>
    if □[M.sim P] (M.interp P) (M.const a) then 1
    else if ◇[M.sim P] (M.interp P) (M.const a) then 0 else -1
  | .sim P a b => if (M.const a) ~[M.sim P] (M.const b) then 1 else -1

-- Lemma 4
theorem TModel.realize_toMV (M : TModel Pred C D) (φ : Formula Pred C) :
    (M.Realize .tolerant φ ↔ toMV M ⊨[.strongKleene, .lp] φ) ∧
      (M.Realize .strict φ ↔ toMV M ⊨[.strongKleene, .k3] φ) := by
  induction φ with
  | atom α =>
    cases α with
    | pred P a =>
      simp only [TModel.realize_tolerant_pred, TModel.realize_strict_pred,
        Trivalent.Formula.realize_atom, Trivalent.Designation.threshold_lp,
        Trivalent.Designation.threshold_k3, SignType.nonneg_iff_ne_neg_one, SignType.one_le_iff,
        toMV]
      split_ifs with hs ht
      · exact ⟨iff_of_true ⟨_, (M.sim P).refl _, box_T hs⟩ (by decide), iff_of_true hs rfl⟩
      · exact ⟨iff_of_true ht (by decide), iff_of_false hs (by decide)⟩
      · exact ⟨iff_of_false ht (fun h ↦ h rfl), iff_of_false hs (by decide)⟩
    | sim P a b =>
      simp only [TModel.realize_sim, Trivalent.Formula.realize_atom,
        Trivalent.Designation.threshold_lp, Trivalent.Designation.threshold_k3,
        SignType.nonneg_iff_ne_neg_one, SignType.one_le_iff, toMV]
      split_ifs with h <;> simp [h]
  | neg ψ ih =>
    simp only [TModel.realize_neg, Trivalent.Formula.realize_neg, Mode.dual_tolerant,
      Mode.dual_strict, Trivalent.Designation.dual_lp, Trivalent.Designation.dual_k3]
    exact ⟨not_congr ih.2, not_congr ih.1⟩
  | conj ψ χ ihψ ihχ =>
    simp only [TModel.realize_conj, Trivalent.Formula.realize_conj]
    exact ⟨and_congr ihψ.1 ihχ.1, and_congr ihψ.2 ihχ.2⟩
  | disj ψ χ ihψ ihχ =>
    simp only [TModel.realize_disj, Trivalent.Formula.realize_disj]
    exact ⟨or_congr ihψ.1 ihχ.1, or_congr ihψ.2 ihχ.2⟩
  | cond ψ χ ihψ ihχ =>
    simp only [TModel.realize_cond, Trivalent.Formula.realize_cond, Mode.dual_tolerant,
      Mode.dual_strict, Trivalent.Designation.dual_lp, Trivalent.Designation.dual_k3]
    exact ⟨imp_congr ihψ.2 ihχ.1, imp_congr ihψ.1 ihχ.2⟩

/-- The T-model of Lemma 5 lives on the doubled domain, where `(a, false)` is `a` and
`(a, true)` its double `a'`, indifferent from each other and from nothing else; `a` is `P` when
`v` makes `Pa` true and `a'` when `v` makes it non-false. -/
def ofMV (v : Trivalent.Model (Atom Pred C)) : TModel Pred C (C × Bool) where
  const a := (a, false)
  interp P
    | (a, false) => v (.pred P a) = 1
    | (a, true) => v (.pred P a) ≠ -1
  sim _ := {p | p.1.1 = p.2.1}
  sim_ktb _ := { refl := fun _ ↦ rfl, symm := fun _ _ ↦ Eq.symm }

-- Lemma 5
theorem ofMV_realize (v : Trivalent.Model (Atom Pred C)) (hφ : IsRestricted φ) :
    ((ofMV v).Realize .tolerant φ ↔ v ⊨[.strongKleene, .lp] φ) ∧
      ((ofMV v).Realize .strict φ ↔ v ⊨[.strongKleene, .k3] φ) := by
  induction φ with
  | atom α =>
    cases α with
    | pred P a =>
      simp only [TModel.realize_tolerant_pred, TModel.realize_strict_pred,
        Trivalent.Formula.realize_atom, Trivalent.Designation.threshold_lp,
        Trivalent.Designation.threshold_k3, SignType.nonneg_iff_ne_neg_one, SignType.one_le_iff,
        ofMV, Box, Diamond]
      refine ⟨⟨?_, fun h ↦ ⟨(a, true), rfl, h⟩⟩, ⟨fun h ↦ h (a, false) rfl, ?_⟩⟩
      · rintro ⟨⟨b, i⟩, hb, h⟩
        obtain rfl : a = b := hb
        cases i <;> simp_all
      · rintro h ⟨b, i⟩ hb
        obtain rfl : a = b := hb
        cases i <;> simp [h]
    | sim P a b => exact hφ.elim
  | neg ψ ih =>
    simp only [TModel.realize_neg, Trivalent.Formula.realize_neg, Mode.dual_tolerant,
      Mode.dual_strict, Trivalent.Designation.dual_lp, Trivalent.Designation.dual_k3]
    exact ⟨not_congr (ih hφ).2, not_congr (ih hφ).1⟩
  | conj ψ χ ihψ ihχ =>
    simp only [TModel.realize_conj, Trivalent.Formula.realize_conj]
    exact ⟨and_congr (ihψ hφ.1).1 (ihχ hφ.2).1, and_congr (ihψ hφ.1).2 (ihχ hφ.2).2⟩
  | disj ψ χ ihψ ihχ =>
    simp only [TModel.realize_disj, Trivalent.Formula.realize_disj]
    exact ⟨or_congr (ihψ hφ.1).1 (ihχ hφ.2).1, or_congr (ihψ hφ.1).2 (ihχ hφ.2).2⟩
  | cond ψ χ ihψ ihχ =>
    simp only [TModel.realize_cond, Trivalent.Formula.realize_cond, Mode.dual_tolerant,
      Mode.dual_strict, Trivalent.Designation.dual_lp, Trivalent.Designation.dual_k3]
    exact ⟨imp_congr (ihψ hφ.1).2 (ihχ hφ.2).1, imp_congr (ihψ hφ.1).1 (ihχ hφ.2).2⟩

/-- On the restricted vocabulary, tolerant consequence is LP-consequence, by the model
correspondences of Lemmas 4 and 5 (Theorem 3). -/
theorem consequence_tolerant_iff_lp (hΓ : ∀ γ ∈ Γ, IsRestricted γ)
    (hΔ : ∀ δ ∈ Δ, IsRestricted δ) :
    Consequence .tolerant .tolerant Γ Δ ↔ Trivalent.Consequence .strongKleene .lp .lp Γ Δ :=
  ⟨fun h ↦ h.comap (fun v ↦ ⟨_, ofMV v⟩) (fun v γ hγ ↦ (ofMV_realize v (hΓ γ hγ)).1.2)
      fun v δ hδ ↦ (ofMV_realize v (hΔ δ hδ)).1.1,
    fun h ↦ h.comap (fun M ↦ toMV M.2) (fun M γ _ ↦ (M.2.realize_toMV γ).1.1)
      fun M δ _ ↦ (M.2.realize_toMV δ).1.2⟩

/-- On the restricted vocabulary, strict consequence is K3-consequence (Theorem 3). -/
theorem consequence_strict_iff_k3 (hΓ : ∀ γ ∈ Γ, IsRestricted γ)
    (hΔ : ∀ δ ∈ Δ, IsRestricted δ) :
    Consequence .strict .strict Γ Δ ↔ Trivalent.Consequence .strongKleene .k3 .k3 Γ Δ :=
  ⟨fun h ↦ h.comap (fun v ↦ ⟨_, ofMV v⟩) (fun v γ hγ ↦ (ofMV_realize v (hΓ γ hγ)).2.2)
      fun v δ hδ ↦ (ofMV_realize v (hΔ δ hδ)).2.1,
    fun h ↦ h.comap (fun M ↦ toMV M.2) (fun M γ _ ↦ (M.2.realize_toMV γ).2.1)
      fun M δ _ ↦ (M.2.realize_toMV δ).2.2⟩

/-! ### The deduction theorem -/

/-- In this model on the constants, `a` alone is `P` and everything is indifferent, so tolerance
from `a` to another constant fails classically. -/
def cutAt (a : C) : TModel Pred C C where
  const := id
  interp _ d := d = a
  sim _ := .univ
  sim_ktb _ := { refl := fun _ ↦ trivial, symm := fun _ _ _ ↦ trivial }

/-- The deduction theorem holds for `⊨ᵐⁿ` iff `m = d(n)`, so only for `st`, `cc` and `ts` (Lemma
10). -/
theorem deductionTheorem_iff {m n : Mode} [Nonempty Pred] [Nontrivial C] :
    (∀ (φ ψ : Formula Pred C) Γ Δ, Consequence m n (φ :: Γ) (ψ :: Δ) ↔
      Valid n ((Γ.foldr .conj φ).cond (Δ.foldr .disj ψ))) ↔ m = n.dual := by
  refine ⟨fun h ↦ ?_, fun h _ _ _ _ ↦ Consequence.iff_valid_imp h⟩
  obtain ⟨P⟩ := ‹Nonempty Pred›
  obtain ⟨a, b, hab⟩ := exists_pair_ne C
  have hbot (x : Mode) (φ : Formula Pred C) :
      Consequence x n [φ] [.neg (.atom (.sim P a a))] ↔ Unsat x φ := by
    simp [Unsat, TModels.Realize, fun M : TModels Pred C ↦
      ((M.2.sim P).refl _ : M.2.const a ~[M.2.sim P] M.2.const a)]
  have key (φ : Formula Pred C) : Unsat m φ ↔ Unsat n.dual φ :=
    (hbot m φ).symm.trans <| (h φ _ [] []).trans <|
      (Consequence.iff_valid_imp rfl).symm.trans (hbot n.dual φ)
  have hc₁ (x : Mode) (hx : x ≠ .tolerant) :
      Unsat x (.conj (.atom (.pred P a)) (.neg (.atom (.pred P a)))) :=
    fun M h ↦ hx (M.2.eq_tolerant_of_realize_conj_neg h)
  have hc₂ : ¬ Unsat .tolerant (.conj (.atom (.pred P a)) (.neg (.atom (.pred P a)))) :=
    fun h ↦ h ⟨_, allBorderline Pred C⟩
      (allBorderline_realize (φ := .conj (.atom (.pred P a)) (.neg (.atom (.pred P a))))
        ⟨trivial, trivial⟩).2
  have ht₁ : Unsat .strict (.neg (tolerance P a b)) := fun M h ↦ h (tolerance_valid P a b M)
  have ht₂ : ¬ Unsat .classical (.neg (tolerance P a b)) := fun h ↦
    h ⟨_, cutAt a⟩ (by simp [TModels.Realize, tolerance, cutAt, hab.symm])
  cases m <;> cases n <;> first
    | rfl
    | exact absurd ((key _).1 (hc₁ _ (by decide))) hc₂
    | exact absurd ((key _).2 (hc₁ _ (by decide))) hc₂
    | exact absurd ((key _).1 ht₁) ht₂
    | exact absurd ((key _).2 ht₁) ht₂

/-- On the restricted vocabulary the deduction theorem also holds for `sc` and `ct`, which there
coincide with `cc` and `st` (§3.4). -/
theorem Consequence.iff_valid_imp_of_restricted (hΓ : ∀ γ ∈ φ :: Γ, IsRestricted γ)
    (hΔ : ∀ δ ∈ ψ :: Δ, IsRestricted δ) (hm : m ≤ .classical) (hn : .classical ≤ n) :
    Consequence m n (φ :: Γ) (ψ :: Δ) ↔ Valid n ((Γ.foldr .conj φ).cond (Δ.foldr .disj ψ)) := by
  have hdn : n.dual ≤ .classical := by cases n <;> first | decide | exact absurd hn (by decide)
  rw [Consequence.restricted_iff hΓ hΔ hm hn, ← Consequence.restricted_iff hΓ hΔ hdn hn]
  exact Consequence.iff_valid_imp rfl

/-! ### Sorites series -/

/-- The sorites series of §3.4.1 and §3.6 has `n` individuals in a line, each indifferent from its
neighbours, the first `i` classically `P`. `series 4 2` is the four-element model of p. 354,
`a, b, c, d` being `0, 1, 2, 3` and the classical extension `{a, b}`. -/
def series (n i : ℕ) : TModel Unit (Fin n) (Fin n) where
  const := id
  interp _ x := x.val < i
  sim _ := {p | p.1.val ≤ p.2.val + 1 ∧ p.2.val ≤ p.1.val + 1}
  sim_ktb _ := { refl := fun _ ↦ ⟨Nat.le_succ _, Nat.le_succ _⟩, symm := fun _ _ ↦ And.symm }

instance (n i : ℕ) (P : Unit) (x y : Fin n) : Decidable (x ~[(series n i).sim P] y) :=
  inferInstanceAs (Decidable (x.val ≤ y.val + 1 ∧ y.val ≤ x.val + 1))

instance (n i : ℕ) (P : Unit) : DecidablePred ((series n i).interp P) :=
  fun x ↦ inferInstanceAs (Decidable (x.val < i))

variable {n i : ℕ}

theorem series_realize_tolerant (hi : 0 < i) (x : Fin n) :
    (series n i).Realize .tolerant (.atom (.pred () x)) ↔ x.val ≤ i := by
  simp only [TModel.realize_tolerant_pred, Diamond, series, id, Set.mem_ofPred_eq]
  refine ⟨fun ⟨y, ⟨h₁, _⟩, h₃⟩ ↦ by omega, fun h ↦ ?_⟩
  rcases Nat.lt_or_ge x.val i with hx | hx
  · exact ⟨x, ⟨Nat.le_succ _, Nat.le_succ _⟩, hx⟩
  · exact ⟨⟨x.val - 1, by omega⟩, by simp; omega, by simp; omega⟩

theorem series_realize_strict (hin : i < n) (x : Fin n) :
    (series n i).Realize .strict (.atom (.pred () x)) ↔ x.val + 1 < i := by
  simp only [TModel.realize_strict_pred, Box, series, id, Set.mem_ofPred_eq]
  refine ⟨fun h ↦ ?_, fun h y ⟨_, h₂⟩ ↦ by omega⟩
  by_cases hx : x.val + 1 < n
  · simpa using h ⟨x.val + 1, hx⟩ ⟨Nat.le_succ_of_le (Nat.le_succ _), le_rfl⟩
  · have := h x ⟨Nat.le_succ _, Nat.le_succ _⟩
    omega

theorem series_borderline (hi : 0 < i) (hin : i < n) (x : Fin n) :
    (series n i).Borderline () x ↔ x.val + 1 = i ∨ x.val = i := by
  rw [TModel.Borderline, show ◇[(series n i).sim ()] ((series n i).interp ()) x ↔ x.val ≤ i from
    series_realize_tolerant hi x, show □[(series n i).sim ()] ((series n i).interp ()) x ↔
    x.val + 1 < i from series_realize_strict hin x]
  omega

-- p. 354
theorem series_four_two (x : Fin 4) :
    ((series 4 2).Realize .strict (.atom (.pred () x)) ↔ x = 0) ∧
    ((series 4 2).Realize .classical (.atom (.pred () x)) ↔ x = 0 ∨ x = 1) ∧
    ((series 4 2).Realize .tolerant (.atom (.pred () x)) ↔ x ≠ 3) ∧
    ((series 4 2).Borderline () x ↔ x = 1 ∨ x = 2) := by
  revert x; decide

-- p. 356
theorem series_four_two_realize_conj_neg :
    (series 4 2).Realize .tolerant
      (.conj (.atom (.pred () 1)) (.neg (.atom (.pred () (1 : Fin 4))))) := by
  decide

/-- `{Pa, a I_P b} ⊨ Pb` is not `cc`-valid (§3.4), as `b, c` of the four-element model show. -/
theorem not_cc_one_step :
    ¬ Consequence .classical .classical
      [.atom (.pred () 1), .atom (.sim () 1 2)] [.atom (.pred () (2 : Fin 4))] :=
  fun h ↦ absurd (h ⟨_, series 4 2⟩ (by decide)) (by decide)

/-- Tolerance is not classically valid, hence neither `cc`- nor `sc`-valid (§3.4). -/
theorem not_valid_classical_tolerance : ¬ Valid .classical (tolerance () (1 : Fin 4) 2) :=
  fun h ↦ absurd (h ⟨_, series 4 2⟩) (by decide)

/-- `{Pa, a I_P b, b I_P c} ⊨ Pc` is not `sc`-valid (§3.4), as `a, b, c` of the four-element
model show. -/
theorem not_sc_two_step :
    ¬ Consequence .strict .classical
      [.atom (.pred () 0), .atom (.sim () 0 1), .atom (.sim () 1 2)]
      [.atom (.pred () (2 : Fin 4))] :=
  fun h ↦ absurd (h ⟨_, series 4 2⟩ (by decide)) (by decide)

/-- `{Pa, a I_P b, b I_P c} ⊨ Pc` is not `ct`-valid (§3.4), as `b, c, d` of the four-element
model show. -/
theorem not_ct_two_step :
    ¬ Consequence .classical .tolerant
      [.atom (.pred () 1), .atom (.sim () 1 2), .atom (.sim () 2 3)]
      [.atom (.pred () (3 : Fin 4))] :=
  fun h ↦ absurd (h ⟨_, series 4 2⟩ (by decide)) (by decide)

-- §3.3.2
theorem exists_realize_pred_not_realize {m n : Mode} (P : Pred) (a : C) (h : n < m) :
    ∃ M : TModels Pred C, M.Realize m (.atom (.pred P a)) ∧ ¬ M.Realize n (.atom (.pred P a)) := by
  have hv := ofMV_realize (fun _ ↦ 0) (φ := .atom (.pred P a)) trivial
  have hvt : (ofMV fun _ ↦ 0).Realize .tolerant (.atom (.pred P a)) :=
    hv.1.2 (show 0 ≤ 0 by decide)
  have hvc : ¬ (ofMV fun _ ↦ 0).Realize .classical (.atom (.pred P a)) :=
    show ¬ 0 = 1 by decide
  have hvs : ¬ (ofMV fun _ ↦ 0).Realize .strict (.atom (.pred P a)) :=
    fun hs ↦ absurd (hv.2.1 hs) (show ¬ (1 : SignType) ≤ 0 by decide)
  have hb := allBorderline_realize (Pred := Pred) (C := C) (φ := .atom (.pred P a)) trivial
  cases m <;> cases n <;> first
    | exact absurd h (by decide)
    | exact ⟨⟨_, allBorderline Pred C⟩, rfl, hb.1⟩
    | exact ⟨⟨_, ofMV fun _ ↦ 0⟩, hvt, hvc⟩
    | exact ⟨⟨_, ofMV fun _ ↦ 0⟩, hvt, hvs⟩

/-- `⊨ᵐⁿ` is reflexive iff `m ≤ n` (§3.3.2), so `φ ⊨ᵗᵗ φ` and `φ ⊨ˢˢ φ` but `Pa ⊭ᵗᶜ Pa` and
`Pa ⊭ᶜˢ Pa`. -/
theorem stdRefl_consequence_iff {m n : Mode} [Nonempty Pred] [Nonempty C] :
    Std.Refl (fun φ ψ : Formula Pred C ↦ Consequence m n [φ] [ψ]) ↔ m ≤ n := by
  refine ⟨fun h ↦ not_lt.1 fun hnm ↦ ?_,
    fun h ↦ stdRefl_mixedConsequence_iff.2 (TModels.realize_monotone h)⟩
  obtain ⟨P⟩ := ‹Nonempty Pred›
  obtain ⟨a⟩ := ‹Nonempty C›
  obtain ⟨M, hm, hn⟩ := exists_realize_pred_not_realize P a hnm
  exact hn (stdRefl_mixedConsequence_iff.1 h M _ hm)

-- §3.4.1
theorem not_isTrans_ct :
    ¬ IsTrans (Formula Unit (Fin 4)) fun φ ψ ↦ Consequence .classical .tolerant [φ] [ψ] := by
  rintro ⟨h⟩
  refine absurd (h (.conj (.atom (.pred () 1)) (.conj (.atom (.sim () 1 2)) (.atom (.sim () 2 3))))
    (.conj (.atom (.pred () 2)) (.atom (.sim () 2 3))) (.atom (.pred () 3)) ?_ ?_
    ⟨_, series 4 2⟩ (by decide)) (by decide) <;>
  refine mixedConsequence_singleton_right.2 fun ⟨_, M⟩ h ↦ ?_ <;>
  simp only [TModels.Realize, List.forall_mem_singleton, TModel.realize_conj,
    TModel.realize_classical_pred, TModel.realize_tolerant_pred, TModel.realize_sim] at h ⊢
  exacts [⟨⟨M.const 1, (M.sim ()).symm h.2.1, h.1⟩, h.2.2⟩,
    ⟨M.const 2, (M.sim ()).symm h.2, h.1⟩]

-- §3.4.1
theorem not_isTrans_sc :
    ¬ IsTrans (Formula Unit (Fin 4)) fun φ ψ ↦ Consequence .strict .classical [φ] [ψ] := by
  rintro ⟨h⟩
  refine absurd (h (.conj (.atom (.pred () 0)) (.conj (.atom (.sim () 0 1)) (.atom (.sim () 1 2))))
    (.conj (.atom (.pred () 1)) (.atom (.sim () 1 2))) (.atom (.pred () 2)) ?_ ?_
    ⟨_, series 4 2⟩ (by decide)) (by decide) <;>
  refine mixedConsequence_singleton_right.2 fun ⟨_, M⟩ h ↦ ?_ <;>
  simp only [TModels.Realize, List.forall_mem_singleton, TModel.realize_conj,
    TModel.realize_strict_pred, TModel.realize_classical_pred, TModel.realize_sim] at h ⊢
  exacts [⟨h.1 _ h.2.1, h.2.2⟩, h.1 _ h.2]

-- Fact 3, §3.4.1
theorem not_isTrans_st :
    ¬ IsTrans (Formula Unit (Fin 4)) fun φ ψ ↦ Consequence .strict .tolerant [φ] [ψ] := by
  rintro ⟨h⟩
  refine absurd (h (.conj (.atom (.pred () 0))
      (.conj (.atom (.sim () 0 1)) (.conj (.atom (.sim () 1 2)) (.atom (.sim () 2 3)))))
    (.conj (.atom (.pred () 1)) (.conj (.atom (.sim () 1 2)) (.atom (.sim () 2 3))))
    (.atom (.pred () 3)) ?_ ?_ ⟨_, series 4 2⟩ (by decide)) (by decide) <;>
  refine mixedConsequence_singleton_right.2 fun ⟨_, M⟩ h ↦ ?_ <;>
  simp only [TModels.Realize, List.forall_mem_singleton, TModel.realize_conj,
    TModel.realize_strict_pred, TModel.realize_tolerant_pred, TModel.realize_sim] at h ⊢
  exacts [⟨⟨M.const 1, (M.sim ()).refl _, h.1 _ h.2.1⟩, h.2.2⟩,
    ⟨M.const 2, (M.sim ()).symm h.2.2, h.1 _ h.2.1⟩]

/-- On the sorites language `⊨ᵐⁿ` is transitive iff `n ≤ m`, as for `tc`, `cs`, `ts` and the unmixed
three (§3.3.2) but not `ct`, `sc`, `st` (§3.4.1). -/
theorem isTrans_consequence_iff {m n : Mode} :
    IsTrans (Formula Unit (Fin 4)) (fun φ ψ ↦ Consequence m n [φ] [ψ]) ↔ n ≤ m := by
  refine ⟨fun h ↦ ?_, isTrans_consequence⟩
  cases m <;> cases n <;> first
    | decide
    | exact absurd h not_isTrans_ct
    | exact absurd h not_isTrans_sc
    | exact absurd h not_isTrans_st

/-- The similarity premises `a₁ I_P a₂, …, aₙ I_P aₙ₊₁` of the sorites (§3.6). -/
def steps (n : ℕ) : List (Formula Unit (Fin (n + 1))) :=
  (List.finRange n).map fun k ↦ .atom (.sim () k.castSucc k.succ)

/-- The tolerance premises `Pa₁ ∧ a₁ I_P a₂ → Pa₂, …` of the sorites, Version 2 (§3.6). -/
def tolerances (n : ℕ) : List (Formula Unit (Fin (n + 1))) :=
  (List.finRange n).map fun k ↦ tolerance () k.castSucc k.succ

/-- Version 1 of the sorites is `st`-invalid for every series of at least four members, the
four-element model being a countermodel, although each of its steps is `st`-valid
(`st_one_step`). Below four members it is valid by Facts 2 and 3. -/
theorem not_st_version1 (hn : 3 ≤ n) :
    ¬ Consequence .strict .tolerant (.atom (.pred () 0) :: steps n)
      [.atom (.pred () (Fin.last n))] := by
  intro h
  have := (series_realize_tolerant (by omega) _).1
    (mixedConsequence_singleton_right.1 h ⟨_, series (n + 1) 2⟩ ?_)
  · simp at this
    omega
  intro γ hγ
  simp only [List.mem_cons, steps, List.mem_map, List.mem_finRange, true_and] at hγ
  rcases hγ with rfl | ⟨k, rfl⟩
  · exact (series_realize_strict (by omega) _).2 (by simp)
  · exact ⟨by simp [series]; omega, by simp [series]⟩

/-- Version 2 of the sorites, with tolerance as a premise, is `st`-valid, since it is classically
valid and `st` extends classical consequence. -/
theorem st_version2 (n : ℕ) :
    Consequence .strict .tolerant (.atom (.pred () 0) :: steps n ++ tolerances n)
      [.atom (.pred () (Fin.last n))] := by
  refine Consequence.mono (by decide) (by decide)
    (mixedConsequence_singleton_right.2 fun ⟨D, M⟩ h ↦ ?_ : Consequence .classical .classical _ _)
  have hstep : ∀ k : Fin n, M.Realize .classical (.atom (.pred () k.castSucc)) →
      M.Realize .classical (.atom (.pred () k.succ)) := by
    intro k hk
    have ht : M.Realize .classical (tolerance () k.castSucc k.succ) :=
      h _ (List.mem_cons_of_mem _
        (List.mem_append_right _ (List.mem_map_of_mem (List.mem_finRange k))))
    have hs : M.Realize .classical (.atom (.sim () k.castSucc k.succ)) :=
      h _ (List.mem_cons_of_mem _
        (List.mem_append_left _ (List.mem_map_of_mem (List.mem_finRange k))))
    rw [tolerance, M.realize_cond, Mode.dual_classical] at ht
    exact ht ⟨hk, hs⟩
  suffices ∀ k (hk : k ≤ n), M.Realize .classical (.atom (.pred () ⟨k, by omega⟩)) from
    this n le_rfl
  intro k
  induction k with
  | zero => exact fun _ ↦ h _ (List.mem_cons_self ..)
  | succ k ih => exact fun hk ↦ hstep ⟨k, by omega⟩ (ih (by omega))

/-- Version 2 is unsound, since across the cut of any series the tolerance premise is not
strictly true (§3.6). -/
theorem not_series_realize_strict_tolerance (hi : 0 < i) (hin : i < n) :
    ¬ (series n i).Realize .strict (tolerance () ⟨i - 1, by omega⟩ ⟨i, hin⟩) := by
  simp only [tolerance, TModel.realize_cond, TModel.realize_conj, TModel.realize_sim,
    Mode.dual_strict, series_realize_tolerant hi, series_realize_strict hin]
  simp [series]
  omega

/-- Whichever way [alxatib-pelletier-2011]'s median man is ranked, he is borderline, tolerantly tall
and tolerantly not tall (§4.2.3). -/
theorem alxatibPelletier_median_borderline (hi : i = 2 ∨ i = 3) :
    (series 5 i).Borderline () 2 :=
  (series_borderline (by omega) (by omega) 2).2 (by show 2 + 1 = i ∨ 2 = i; omega)

end CobrerosEtAl2012
