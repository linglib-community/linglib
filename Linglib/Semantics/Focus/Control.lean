/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.Composition.WithAlternatives

/-!
# Focus antecedents

The anaphoric source of the squiggle's contrast set ([rooth-1992]):
what the preceding discourse supplies — a question, a prior assertion
to correct, explicitly offered alternatives, or a parallel focus, the
four contexts that control a focus in [hartmann-zimmermann-2007] §1.2,
the notion of control being [uhmann-1991]'s. `Use` classifies the shapes;
felicity (`Antecedent.Admits`) is containment of the antecedent's
contrast set in the focus value, uniformly across uses — and `use_not_factorsThrough_contrastSet`
shows the four-way split is invisible to the semantics.

`SquiggleSet`/`SquiggleInd` state the full presuppositions of
[rooth-1992]'s ~ operator (his (40), set and individual cases):
`Admits` is only the first set-case clause, and the contrast clauses
are what make ~ anaphorically demanding — `not_squiggleSet_unfeatured`
derives "the argument must contain a focus" from the unit focus value
of focus-free phrases. `Antecedent.Resolves` routes each antecedent
shape through the appropriate case.

## Implementation notes

Payloads are flat Hamblin sets, `Set (Set W)`, keeping antecedents over finite models
`decide`-friendly; a `Question` supplies one through `Question.alt`. The `assertion` payload
is a raw prior proposition; the `HasAssertion` hookup (a correction/denial move) is deferred.
-/

@[expose] public section

namespace Focus

variable {W : Type*}

/-- The four pragmatic uses of one semantic focus ([uhmann-1991]):
the image of `Antecedent.use`. -/
inductive Use where
  | newInfo      -- controlled by a question
  | corrective   -- correction of a prior assertion
  | selective    -- selection from explicitly offered alternatives
  | contrastive  -- parallel contrast across utterances
  deriving DecidableEq, Repr, Inhabited

/-- A focus antecedent is the discourse object that supplies the squiggle's antecedent, a
contrast set for [rooth-1992]'s set case or a single contrasting ordinary value for the
individual case. -/
inductive Antecedent (W : Type*) where
  /-- A question with (flat Hamblin) denotation `q`. -/
  | question (q : Set (Set W))
  /-- A prior assertion `p`, corrected among alternatives `alts`. -/
  | assertion (p : Set W) (alts : Set (Set W))
  /-- Explicitly offered alternatives ('coffee or tea?'). -/
  | offer (alts : Set (Set W))
  /-- A parallel focus with focus value `alts`. -/
  | parallel (alts : Set (Set W))
  /-- A contrasting phrase's ordinary value ([rooth-1992]'s individual
  case; the "contrasting phrases" rule). -/
  | phrase (γ : Set W)

/-- The contrast set Γ an antecedent supplies to the squiggle. -/
def Antecedent.contrastSet : Antecedent W → Set (Set W)
  | .question q        => q
  | .assertion _ alts  => alts
  | .offer alts        => alts
  | .parallel alts     => alts
  | .phrase γ          => {γ}

/-- The pragmatic use an antecedent shape licenses. -/
def Antecedent.use : Antecedent W → Use
  | .question _     => .newInfo
  | .assertion _ _  => .corrective
  | .offer _        => .selective
  | .parallel _     => .contrastive
  | .phrase _       => .contrastive

@[simp] theorem contrastSet_question (q : Set (Set W)) :
    (Antecedent.question q).contrastSet = q := rfl
@[simp] theorem contrastSet_assertion (p : Set W) (alts : Set (Set W)) :
    (Antecedent.assertion p alts).contrastSet = alts := rfl
@[simp] theorem contrastSet_offer (alts : Set (Set W)) :
    (Antecedent.offer alts).contrastSet = alts := rfl
@[simp] theorem contrastSet_parallel (alts : Set (Set W)) :
    (Antecedent.parallel alts).contrastSet = alts := rfl

@[simp] theorem use_question (q : Set (Set W)) :
    (Antecedent.question q).use = .newInfo := rfl
@[simp] theorem use_assertion (p : Set W) (alts : Set (Set W)) :
    (Antecedent.assertion p alts).use = .corrective := rfl
@[simp] theorem use_offer (alts : Set (Set W)) :
    (Antecedent.offer alts).use = .selective := rfl
@[simp] theorem use_parallel (alts : Set (Set W)) :
    (Antecedent.parallel alts).use = .contrastive := rfl
@[simp] theorem contrastSet_phrase (γ : Set W) :
    (Antecedent.phrase γ).contrastSet = {γ} := rfl
@[simp] theorem use_phrase (γ : Set W) :
    (Antecedent.phrase γ).use = .contrastive := rfl

/-- The canonical antecedent of each use over a designated
ordinary-value/alternative pair `(o, a)`: a question, an assertion of
the alternative to be corrected, an offer, or a parallel focus — the
minimal contentful model of the four controlling contexts. -/
def Use.model (o a : Set W) : Use → Antecedent W
  | .newInfo     => .question {o, a}
  | .corrective  => .assertion a {o, a}
  | .selective   => .offer {o, a}
  | .contrastive => .parallel {o, a}

@[simp] theorem use_model (o a : Set W) (u : Use) :
    (Use.model o a u).use = u := by cases u <;> rfl

/-- Every pragmatic use is realised by some antecedent shape. -/
theorem use_surjective : Function.Surjective (Antecedent.use (W := W)) :=
  fun u => ⟨Use.model ∅ ∅ u, use_model ∅ ∅ u⟩

/-- An antecedent admits a focus value when its contrast set lies inside the focus value,
[rooth-1992]'s focus interpretation principle. -/
def Antecedent.Admits (c : Antecedent W) (fv : Set (Set W)) : Prop :=
  c.contrastSet ⊆ fv

/-- `Admits` is monotone in the focus value. -/
theorem Antecedent.Admits.mono {c : Antecedent W} {fv fv' : Set (Set W)}
    (hc : c.Admits fv) (h : fv ⊆ fv') : c.Admits fv' := hc.trans h

/-- An intersection of focus values is admitted iff both are. -/
theorem admits_inter_iff {c : Antecedent W} {fv fv' : Set (Set W)} :
    c.Admits (fv ∩ fv') ↔ c.Admits fv ∧ c.Admits fv' :=
  Set.subset_inter_iff

/-! ### The squiggle presupposition

[rooth-1992]'s ~ operator introduces the presuppositions of its (40),
over an ordinary value `o` and focus value `fv` of any type: in the set
case the resolved antecedent `Γ` is a subset of `fv` containing `o` and
a distinct alternative; in the individual case the antecedent is a
member of `fv` distinct from `o`. `Admits` is the first set-case clause;
the contrast clauses are what make ~ anaphorically demanding. -/

section Squiggle

variable {α : Type*}

/-- The ~ presupposition in the set case requires `Γ ⊆ fv`, `o ∈ Γ`, and an alternative in `Γ`
distinct from `o` ([rooth-1992] (40)). -/
def SquiggleSet (o : α) (fv Γ : Set α) : Prop :=
  Γ ⊆ fv ∧ o ∈ Γ ∧ ∃ x ∈ Γ, x ≠ o

/-- The ~ presupposition in the individual case requires the antecedent to be a member of `fv`
distinct from `o` ([rooth-1992] (40)); the contrasting-phrases rule is this with `γ := ⟦β⟧ᵒ`. -/
def SquiggleInd (o : α) (fv : Set α) (γ : α) : Prop :=
  γ ∈ fv ∧ γ ≠ o

/-- The first set-case clause alone: the antecedent is a subset of the
focus value (at the propositional level, the focus interpretation principle). -/
theorem SquiggleSet.subset {o : α} {fv Γ : Set α} (h : SquiggleSet o fv Γ) :
    Γ ⊆ fv := h.1

/-- A resolved antecedent is nontrivial: it contains the ordinary value
and a distinct alternative. -/
theorem SquiggleSet.nontrivial {o : α} {fv Γ : Set α}
    (h : SquiggleSet o fv Γ) : Γ.Nontrivial :=
  let ⟨_, ho, x, hx, hne⟩ := h; ⟨x, hx, o, ho, hne⟩

/-- A unit focus value defeats the contrast clause: nothing resolves
against `{o}`. -/
theorem not_squiggleSet_singleton (o : α) (Γ : Set α) :
    ¬ SquiggleSet o {o} Γ :=
  fun ⟨hsub, _, _, hx, hne⟩ => hne (hsub hx)

theorem not_squiggleInd_singleton (o γ : α) : ¬ SquiggleInd o {o} γ :=
  fun ⟨hγ, hne⟩ => hne hγ

/-- "The argument must contain a focus": a focus-free phrase has a unit
focus value, so no antecedent resolves against it ([rooth-1992] §10). -/
theorem not_squiggleSet_unfeatured (x : α) (Γ : Set α) :
    ¬ SquiggleSet (WithAlternatives.unfeatured x).ordinary
      (WithAlternatives.unfeatured x).alternatives Γ := by
  rw [WithAlternatives.unfeatured_alternatives, WithAlternatives.unfeatured_ordinary]
  exact not_squiggleSet_singleton x Γ

end Squiggle

/-- Full Roothian resolution of an antecedent against a two-dimensional
meaning `(o, fv)`: the set case for question / offer / parallel
antecedents, the individual case for contrasting phrases — and for
assertion antecedents additionally the correction clause: the resolved
ordinary value replaces (differs from) the prior assertion. -/
def Antecedent.Resolves : Antecedent W → Set W → Set (Set W) → Prop
  | .phrase γ, o, fv         => SquiggleInd o fv γ
  | .assertion p alts, o, fv => SquiggleSet o fv alts ∧ o ≠ p
  | c, o, fv                 => SquiggleSet o fv c.contrastSet

/-- Full resolution entails felicity: `Admits` is the set case's first
clause, and a resolved contrasting phrase is a member of the focus
value. -/
theorem Antecedent.Resolves.admits {c : Antecedent W} {o : Set W}
    {fv : Set (Set W)} (h : c.Resolves o fv) : c.Admits fv := by
  cases c with
  | phrase γ => exact Set.singleton_subset_iff.mpr h.1
  | question q => exact h.1
  | assertion p alts => exact h.1.1
  | offer alts => exact h.1
  | parallel alts => exact h.1


/-- Felicity factors through the contrast set: the semantics sees Γ,
never the use label. -/
theorem admits_factorsThrough_contrastSet (fv : Set (Set W)) :
    Function.FactorsThrough (Antecedent.Admits · fv)
      (Antecedent.contrastSet (W := W)) :=
  fun _ _ h => congrArg (· ⊆ fv) h

/-- Distinct uses can supply one and the same Γ (a question and an
explicit offer, say), so the four-way split is invisible to the
Roothian semantics — pragmatic, not semantic. -/
theorem use_not_factorsThrough_contrastSet :
    ¬ Function.FactorsThrough (Antecedent.use (W := W))
        Antecedent.contrastSet :=
  fun h => absurd (h (a := .question ∅) (b := .offer ∅) rfl) (by simp)

/-! ### Composed answers over a pair

The minimal contentful scenario: a two-point answer domain
`{d, d'}` with `d` the true answer. The answer is built by the
composition engine — the singleton complete-answer predicate mapped
over the F-marked argument — and every canonical antecedent shape
fully resolves against it. -/

/-- The composed focused answer `d` over the pair `{d, d'}`. -/
def pairAnswer {W : Type*} (d d' : W) : WithAlternatives (Set W) :=
  (fun x => ({x} : Set W)) <$> (⟨d, {d, d'}⟩ : WithAlternatives W)

@[simp] theorem pairAnswer_ordinary {W : Type*} (d d' : W) :
    (pairAnswer d d').ordinary = {d} := rfl

@[simp] theorem pairAnswer_alternatives {W : Type*} (d d' : W) :
    (pairAnswer d d').alternatives = {{d}, {d'}} := by
  ext q
  simp only [pairAnswer, WithAlternatives.mem_alternatives_map]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rcases (by simpa using ha : a = d ∨ a = d') with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨d, by simp, rfl⟩
    · exact ⟨d', by simp, rfl⟩

/-- Every canonical antecedent shape fully resolves, all squiggle clauses including the
correction clause, against the composed answer over its pair, so the four pragmatic uses share
one semantics. -/
theorem use_model_resolves {W : Type*} {d d' : W} (hne : d' ≠ d) (u : Use) :
    (Use.model {d} {d'} u).Resolves
      (pairAnswer d d').ordinary (pairAnswer d d').alternatives := by
  have hne' : ({d'} : Set W) ≠ {d} :=
    fun h => hne (Set.singleton_eq_singleton_iff.mp h)
  have hSq : SquiggleSet (pairAnswer d d').ordinary (pairAnswer d d').alternatives
      {{d}, {d'}} := by
    rw [pairAnswer_ordinary, pairAnswer_alternatives]
    exact ⟨subset_rfl, Or.inl rfl, ⟨{d'}, Or.inr rfl, hne'⟩⟩
  cases u with
  | newInfo     => exact hSq
  | corrective  => exact ⟨hSq, by rw [pairAnswer_ordinary]; exact hne'.symm⟩
  | selective   => exact hSq
  | contrastive => exact hSq

end Focus
