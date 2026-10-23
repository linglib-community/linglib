module

public import Linglib.Logic.Natural.Completeness
public import Linglib.Semantics.Polarity.Strength

/-!
# Icard (2012): Inclusion and Exclusion in Natural Language

This file formalizes Icard's projectivity calculus, which extends the Monotonicity Calculus from
inclusion to the exclusion relations of MacCartney and Manning. The relations, their join and
projection tables and the composition of signatures are the library's `NaturalLogic` substrate,
whose implementations this file checks against the printed cells; on top of them it builds the typed
language of Section 2, with the projectivity markings of a lexicon's constants, the projectivity of
a context (Definition 2.9, `Ctx.pro`), and the soundness of projectivity marking (Proposition 2.10,
`Model.soundFor_ctxFun`). The calculus 𝒞 of Section 3 is `Derives`, with the Substitution rule over
contexts, and Theorem 3.1 is `Derives.sound`. The worked example of Section 3.2, that *Every job
that involves a giant squid is dangerous* entails *Not every job that involves a cephalopod is
safe*, is derived from the paper's assumption set by three substitutions and two compositions
(`derives_squid`), and Section 4's correspondence between the signatures and Zwarts's three classes
of negative polarity items is `Licenses`, read off the substrate's strength map
`Signature.negationStrength`.

## Implementation notes

* Types are unmarked and the markings live on the lexicon's constants, one signature per
  arrow, outermost first; the topmost projectivity of a term is its first remaining marking,
  `•` when none is left. A model's constants are functions of their signatures over the whole
  unmarked domains, Boolean algebras, which is stronger than the paper's marked domains and
  leaves Definition 2.8's subtyping of marked types aside.
* The paper's remark that terms of additive and anti-additive types always alternate, the
  witness of incompleteness, is not formalized: in the unmarked function lattice the constant
  `⊤` function and complementation are additive and anti-additive without being disjoint.
* One cell of the printed projection table deviates from Definition 2.3 (`project_equiv`).

## References

* [icard-2012]
* [maccartney-manning-2009]
* [zwarts-1998]
-/

@[expose] public section

namespace Icard2012

open NaturalLogic NaturalLogic.Relation NaturalLogic.Signature

/-! ### The printed tables

The join table (Lemma 1.5), the projection table (Lemma 2.4) and the composition table
(Lemma 2.7) are the substrate's `join`, `project` and `compose`; the cells are certified sound
and least in `Logic/Natural/Soundness.lean` and `Logic/Natural/Completeness.lean`. -/

example : join .alternation .negation = .forward := rfl
example : join .alternation .reverse = .alternation := rfl
example : ∀ R : Relation, 1 * R = R ∧ R * 1 = R := by decide
example : ∀ R : Relation, ⊤ * R = ⊤ ∧ R * ⊤ = ⊤ := by decide
example : IsLeast {T : Relation | ∀ x y z : Finset (Fin 3),
    Relation.Holds .forward x y → Relation.Holds .negation y z → T.Holds x z}
    .alternation := Relation.isLeast_join .forward .negation

example : project .forward .antiAdd = .reverse := rfl
example : project .negation .addMult = .negation := rfl
example : project .alternation .mult = .alternation := rfl
example : project .negation .mono = .independent := rfl

/-- The printed remark that `•` projects every relation to `#` overshoots at `≡`, since every
function preserves equality. -/
example : project .equiv .all = .equiv := rfl

example : compose .antiAdd .additive = .antiAdd := rfl
example : compose .mult .addMult = .mult := rfl
example : negationSignature * negationSignature = .addMult := rfl

/-! ### The typed language (Sections 2.1 and 2.3) -/

/-- The basic types are predicates, intransitive verbs and truth values. -/
inductive Base
  | p
  | v
  | t
  deriving DecidableEq

/-- Unmarked types. -/
inductive Ty
  | base : Base → Ty
  | arrow : Ty → Ty → Ty
  deriving DecidableEq

/-- A lexicon gives the constants' types and the projectivity markings of their arrows,
outermost first (Definition 2.1). -/
structure Lexicon (κ : Type*) where
  ty : κ → Ty
  marks : κ → List Signature

variable {κ : Type*}

/-- The terms of the language (Definition 2.8) are constants and applications. -/
inductive Term (L : Lexicon κ) : Ty → Type _
  | const (c : κ) : Term L (L.ty c)
  | app {σ τ : Ty} : Term L (.arrow σ τ) → Term L σ → Term L τ

variable {L : Lexicon κ}

/-- The markings a term still carries, applying a term consuming its outermost marking. -/
def Term.marks : ∀ {τ}, Term L τ → List Signature
  | _, .const c => L.marks c
  | _, .app s _ => s.marks.tail

/-- The topmost projectivity of a term (Section 2.4) is its outermost marking, `•` when it
has none. -/
def Term.top {τ : Ty} (t : Term L τ) : Signature := t.marks.headD .all

/-- A context (Section 2.4) is a term with one hole of type `σ`, in function or argument
position. -/
inductive Ctx (L : Lexicon κ) (σ : Ty) : Ty → Type _
  | hole : Ctx L σ σ
  | appL {ρ τ : Ty} : Ctx L σ (.arrow ρ τ) → Term L ρ → Ctx L σ τ
  | appR {ρ τ : Ty} : Term L (.arrow ρ τ) → Ctx L σ ρ → Ctx L σ τ

variable {σ : Ty}

/-- Filling the hole of a context. -/
def Ctx.fill : ∀ {τ}, Ctx L σ τ → Term L σ → Term L τ
  | _, .hole, s => s
  | _, .appL c u, s => .app (c.fill s) u
  | _, .appR f c, s => .app f (c.fill s)

/-- The projectivity of a context (Definition 2.9) is the identity marking at the hole, the
context's own projectivity into the function position, and the function's topmost
projectivity composed with the argument's into the argument position. -/
def Ctx.pro : ∀ {τ}, Ctx L σ τ → Signature
  | _, .hole => .addMult
  | _, .appL c _ => c.pro
  | _, .appR f c => f.top * c.pro

/-! ### Models (Definition 2.8)

The domain of a basic type is a Boolean algebra and that of an arrow all functions, the
Boolean lattice of Proposition 1.1; a constant denotes a function of its signature whose
values again are (Definition 2.2). -/

universe u

/-- The domains of the unmarked types. -/
def Dom (B : Base → Type u) : Ty → Type u
  | .base b => B b
  | .arrow σ τ => Dom B σ → Dom B τ

section Dom

variable {B : Base → Type u} [∀ b, BooleanAlgebra (B b)]

/-- The Boolean algebra of a domain is that of the basic type, or the pointwise one on
functions. -/
@[reducible] def Dom.booleanAlgebra : ∀ τ, BooleanAlgebra (Dom B τ)
  | .base b => inferInstanceAs (BooleanAlgebra (B b))
  | .arrow _ τ => @Pi.instBooleanAlgebra _ _ λ _ => Dom.booleanAlgebra τ

@[reducible] instance Dom.instBooleanAlgebra (τ : Ty) : BooleanAlgebra (Dom B τ) :=
  Dom.booleanAlgebra τ

/-- A value of a type is of the given markings when it is a function of the first marking
whose values are of the remaining ones (Definition 2.2). -/
def Mem : List Signature → ∀ τ, Dom B τ → Prop
  | φ :: ms, .arrow σ τ, f => φ.SoundFor (f : Dom B σ → Dom B τ) ∧ ∀ x, Mem ms τ (f x)
  | _, _, _ => True

end Dom

/-- A model of the language gives domains for the basic types and a denotation for each
constant of its markings. -/
structure Model (L : Lexicon κ) where
  B : Base → Type u
  [ba : ∀ b, BooleanAlgebra (B b)]
  val : ∀ c, Dom B (L.ty c)
  mem : ∀ c, Mem (L.marks c) (L.ty c) (val c)

attribute [instance] Model.ba

namespace Model

variable (M : Model L)

/-- The denotation of a term. -/
def eval : ∀ {τ}, Term L τ → Dom M.B τ
  | _, .const c => M.val c
  | _, .app s u => eval s (eval u)

/-- The function a context denotes (Section 2.4). -/
def ctxFun : ∀ {τ}, Ctx L σ τ → Dom M.B σ → Dom M.B τ
  | _, .hole => id
  | _, .appL c u => λ a => ctxFun c a (eval M u)
  | _, .appR f c => eval M f ∘ ctxFun c

theorem eval_fill : ∀ {τ} (c : Ctx L σ τ) (s : Term L σ),
    eval M (c.fill s) = ctxFun M c (eval M s)
  | _, .hole, _ => rfl
  | _, .appL c u, s => congrArg (· (eval M u)) (eval_fill c s)
  | _, .appR f c, s => congrArg (eval M f) (eval_fill c s)

theorem mem_eval : ∀ {τ} (t : Term L τ), Mem t.marks τ (eval M t)
  | _, .const c => M.mem c
  | _, .app s u => by
    have h := mem_eval s
    show Mem s.marks.tail _ (eval M s (eval M u))
    rcases hm : s.marks with _ | ⟨φ, ms⟩
    · exact trivial
    · rw [hm] at h
      exact h.2 (eval M u)

/-- Projectivity marking is sound (Proposition 2.10), a context denoting a function of its
projectivity. -/
theorem soundFor_ctxFun : ∀ {τ} (c : Ctx L σ τ), c.pro.SoundFor (ctxFun M c)
  | _, .hole => soundFor_addMult_id
  | _, .appL c u => λ R x y hR => (soundFor_ctxFun c R x y hR).apply (eval M u)
  | _, .appR f c => by
    have h := mem_eval M f
    show Signature.SoundFor (f.top * c.pro) (eval M f ∘ ctxFun M c)
    rcases hm : f.marks with _ | ⟨φ, ms⟩
    · rw [show f.top = .all by simp [Term.top, hm],
        show (Signature.all * c.pro) = .all from compose_all_left _]
      exact soundFor_all _
    · rw [hm] at h
      rw [show f.top = φ by simp [Term.top, hm]]
      exact h.1.comp (soundFor_ctxFun c)

end Model

/-! ### The calculus 𝒞 (Section 3.1) -/

/-- The projectivity calculus 𝒞 derives relational statements between terms of a type from an
assumption set by Reflexivity, the four Symmetry rules, Absurdity, Composition along the join,
and Substitution through a context with the projection of the relation. -/
inductive Derives (Γ : ∀ {τ}, Term L τ → Relation → Term L τ → Prop) :
    ∀ {τ}, Term L τ → Relation → Term L τ → Prop
  | ax {τ} {t t' : Term L τ} {R} : Γ t R t' → Derives Γ t R t'
  | refl {τ} (t : Term L τ) : Derives Γ t .forward t
  | symm_forward {τ} {t t' : Term L τ} : Derives Γ t .forward t' → Derives Γ t' .reverse t
  | symm_reverse {τ} {t t' : Term L τ} : Derives Γ t .reverse t' → Derives Γ t' .forward t
  | symm_alternation {τ} {t t' : Term L τ} :
      Derives Γ t .alternation t' → Derives Γ t' .alternation t
  | symm_cover {τ} {t t' : Term L τ} : Derives Γ t .cover t' → Derives Γ t' .cover t
  | absurd {τ ρ} {t : Term L τ} {s s' : Term L ρ} (R : Relation) :
      Derives Γ t .alternation t → Derives Γ s R s'
  | comp {τ} {t u v : Term L τ} {R S} :
      Derives Γ t R u → Derives Γ u S v → Derives Γ t (R * S) v
  | subst {σ τ} {s s' : Term L σ} {R} (c : Ctx L σ τ) :
      Derives Γ s R s' → Derives Γ (c.fill s) (project R c.pro) (c.fill s')

/-- 𝒞 is sound (Theorem 3.1), a derivable statement holding in every model of the
assumptions in which no term denotes `⊥`; Composition is Lemma 1.6, Substitution
Corollary 2.12, and Absurdity needs the nonvacuity. -/
theorem Derives.sound (M : Model L) {Γ : ∀ {τ}, Term L τ → Relation → Term L τ → Prop}
    (hΓ : ∀ {τ} {t t' : Term L τ} {R}, Γ t R t' → R.Holds (M.eval t) (M.eval t'))
    (hv : ∀ {τ} (t : Term L τ), M.eval t ≠ ⊥) {τ} {t t' : Term L τ} {R}
    (h : Derives Γ t R t') : R.Holds (M.eval t) (M.eval t') := by
  induction h with
  | ax h => exact hΓ h
  | refl t => exact le_refl _
  | symm_forward _ ih => exact ih
  | symm_reverse _ ih => exact ih
  | symm_alternation _ ih => exact ih.symm
  | symm_cover _ ih => exact ih.symm
  | absurd _ _ ih => exact (hv _ (disjoint_self.mp ih)).elim
  | comp _ _ ih₁ ih₂ => exact ih₁.join ih₂
  | subst c _ ih => rw [M.eval_fill, M.eval_fill]; exact M.soundFor_ctxFun c _ _ _ ih

/-! ### The worked example (Section 3.2) -/

/-- The constants of the fragment. -/
inductive Const
  | every | some | no | notEvery | job | giantSquid | cephalopod | safe | dangerous
  | is | involves | that
  deriving DecidableEq

/-- In the fragment's lexicon *every* is anti-additive then multiplicative, *some* additive
twice, *no* anti-additive twice, *not every* additive then anti-multiplicative, and the
adjectives, copula, verb and relativizer morphisms. -/
def lexicon : Lexicon Const where
  ty
    | .every | .some | .no | .notEvery => .arrow (.base .p) (.arrow (.base .v) (.base .t))
    | .job | .giantSquid | .cephalopod => .base .p
    | .safe | .dangerous => .arrow (.base .p) (.base .p)
    | .is => .arrow (.arrow (.base .p) (.base .p)) (.base .v)
    | .involves => .arrow (.arrow (.base .v) (.base .t)) (.base .v)
    | .that => .arrow (.base .v) (.arrow (.base .p) (.base .p))
  marks
    | .every => [.antiAdd, .mult]
    | .some => [.additive, .additive]
    | .no => [.antiAdd, .antiAdd]
    | .notEvery => [.additive, .antiMult]
    | .job | .giantSquid | .cephalopod => []
    | .safe | .dangerous | .is | .involves => [.addMult]
    | .that => [.addMult, .addMult]

/-- A constant as a term. -/
def k (c : Const) : Term lexicon (lexicon.ty c) := .const c

/-- The assumption set Γ of Section 3.2. -/
inductive Assumption : ∀ {τ}, Term lexicon τ → Relation → Term lexicon τ → Prop
  | everyNegNotEvery : Assumption (k .every) .negation (k .notEvery)
  | someNegNo : Assumption (k .some) .negation (k .no)
  | noAltEvery : Assumption (k .no) .alternation (k .every)
  | safeAltDangerous : Assumption (k .safe) .alternation (k .dangerous)
  | squidLeCephalopod : Assumption (k .giantSquid) .forward (k .cephalopod)

theorem derives_no_forward_notEvery : Derives Assumption (k .no) .forward (k .notEvery) :=
  .comp (.ax Assumption.noAltEvery) (.ax Assumption.everyNegNotEvery)

/-- *Q job that involves a N is A*, for a determiner `q`, a noun `n` and an adjective `a`. -/
def sentence (q : Term lexicon (lexicon.ty .every)) (n : Term lexicon (.base .p))
    (a : Term lexicon (lexicon.ty .safe)) : Term lexicon (.base .t) :=
  .app (.app q (.app (.app (k .that) (.app (k .involves) (.app (k .some) n))) (k .job)))
    (.app (k .is) a)

/-- *Every job that involves a giant squid is dangerous*. -/
def t₀ : Term lexicon (.base .t) := sentence (k .every) (k .giantSquid) (k .dangerous)
/-- *Every job that involves a giant squid is safe*. -/
def u₀ : Term lexicon (.base .t) := sentence (k .every) (k .giantSquid) (k .safe)
/-- *Every job that involves a cephalopod is safe*. -/
def v₀ : Term lexicon (.base .t) := sentence (k .every) (k .cephalopod) (k .safe)
/-- *Not every job that involves a cephalopod is safe*. -/
def t₀' : Term lexicon (.base .t) := sentence (k .notEvery) (k .cephalopod) (k .safe)

/-- The context of the adjective, whose projectivity is `top(every(job…)) ∘ top(is) = ⊞`. -/
def adjectiveCtx : Ctx lexicon (.arrow (.base .p) (.base .p)) (.base .t) :=
  .appR (.app (k .every) (.app (.app (k .that) (.app (k .involves) (.app (k .some)
    (k .giantSquid)))) (k .job))) (.appR (k .is) .hole)

/-- The context of the noun under *a*, with the adjective already *safe*, whose projectivity
is `top(every) ∘ top(that) ∘ top(involves) ∘ top(a) = ◇`. -/
def nounCtx : Ctx lexicon (.base .p) (.base .t) :=
  .appL (.appR (k .every) (.appL (.appR (k .that) (.appR (k .involves)
    (.appR (k .some) .hole))) (k .job))) (.app (k .is) (k .safe))

/-- The context of the determiner, under no function, of projectivity `⊕⊞`. -/
def determinerCtx : Ctx lexicon (lexicon.ty .every) (.base .t) :=
  .appL (.appL .hole (.app (.app (k .that) (.app (k .involves) (.app (k .some)
    (k .cephalopod)))) (k .job))) (.app (k .is) (k .safe))

example : adjectiveCtx.pro = .mult := rfl
example : nounCtx.pro = .antiAdd := rfl
example : determinerCtx.pro = .addMult := rfl

theorem derives_squid : Derives Assumption t₀ .forward t₀' :=
  have h₁ : Derives Assumption t₀ .alternation u₀ :=
    .subst adjectiveCtx (.symm_alternation (.ax Assumption.safeAltDangerous))
  have h₂ : Derives Assumption u₀ .reverse v₀ :=
    .subst nounCtx (.ax Assumption.squidLeCephalopod)
  have h₃ : Derives Assumption v₀ .negation t₀' :=
    .subst determinerCtx (.ax Assumption.everyNegNotEvery)
  (h₁.comp h₂).comp h₃

/-- The calculus is not confluent (Section 3.3). Substituting *octopus* for *squid* under
*some* on the assumption *squid* | *octopus* yields `#`, from which nothing stronger is
recovered, though *some squid* ⊑ *some cephalopod* is derivable directly. -/
example : project .alternation .additive = .independent ∧ ⊤ * Relation.forward = ⊤ :=
  ⟨rfl, rfl⟩

/-! ### Negative polarity items (Section 4)

The three classes of [zwarts-1998] are the signatures' downward half: weak items need an
antitone context, strong ones an anti-additive context and superstrong ones an
anti-morphic one. -/

/-- A signature licenses an item of a Zwarts class when the strength of negation it realizes,
`Signature.negationStrength`, is at least as strong. -/
def Licenses (level : Negation.Strength) (σ : Signature) : Prop :=
  (level : WithBot Negation.Strength) ≤ σ.negationStrength

instance (level : Negation.Strength) (σ : Signature) : Decidable (Licenses level σ) :=
  inferInstanceAs (Decidable (_ ≤ _))

theorem licenses_weak {σ : Signature} (h : σ.sign = -1) :
    Licenses .weak σ := by
  cases σ <;> first | decide | exact absurd h (by decide)

/-- Examples (1)–(2) put *yet* under *not every* and under *few*, antitone contexts. -/
example : Licenses .weak .antiMult ∧ Licenses .weak .anti := by decide

/-- Examples (3)–(4) put *in years* under *few* and under *no*, whose second argument is
anti-additive. -/
example : ¬ Licenses .antiAdditive .anti ∧ Licenses .antiAdditive .antiAdd := by decide

/-- Examples (5)–(6) put *a tad bit* under *no* and under *not*, the anti-morphism. -/
example : ¬ Licenses .antiMorphic .antiAdd ∧ Licenses .antiMorphic negationSignature := by
  decide

end Icard2012
