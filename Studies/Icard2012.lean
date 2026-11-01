module

public import Linglib.Logic.Natural.Completeness
public import Linglib.Semantics.Negation.Strength
public import Linglib.Data.Examples.Icard2012

/-!
# Icard (2012): Inclusion and Exclusion in Natural Language

This file formalizes Icard's projectivity calculus, which extends the Monotonicity Calculus from
inclusion to the exclusion relations of MacCartney and Manning. The relations, their join and
projection tables and the composition of signatures are the library's `NaturalLogic` substrate,
which computes them from rules on single constraints and properties, and this file checks the
computed cells against the printed ones; on top of them it builds the typed
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

## Errata

* The orders ≪ on relations (p. 710 and its footnote 2) and ≼ on signatures (p. 715) are defined
  as implication, but Lemma 1.3 and Definitions 1.4, 2.3 and 2.6 take the ≪- or ≼-maximal element
  to be the most informative one, which is the least in the defined order. Read as printed, every
  join and projection would be `#` and every composition `•`.
* The remark under the projection table that `[R]^• = #` for every `R` (p. 715) fails at `≡`,
  since every function preserves equality (`Signature.project_equiv`).
* Three cells of the composition table (p. 716) are wrong. Anti-additive after anti-additive is
  printed antitone but is monotone; anti-multiplicative after multiplicative is printed antitone
  but is anti-multiplicative; anti-morphic after anti-multiplicative is printed additive but is
  multiplicative. The first and third printed values fail for complementation, the second is
  sound but not the most specific.
* The witness of incompleteness (p. 719), that terms of an additive and of an anti-additive type
  always stand in `|`, fails: the constant `⊤` function is additive, complementation is
  anti-additive, and the two are not disjoint.
* The conclusion of the worked example is stated on p. 720 with *giant squid*, but the
  introduction (p. 708) and the derivation (pp. 721–722) end at *cephalopod*, as does
  `derives_squid`.

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
(Lemma 2.7) are the substrate's `join`, `project` and `compose`, computed from rules on single
constraints and properties; the cells are certified sound and least in
`Logic/Natural/Soundness.lean` and `Logic/Natural/Completeness.lean`, and agree with the printed
ones except where the errata say. -/

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

example : compose .antiAdd .additive = .antiAdd := rfl
example : compose .mult .addMult = .mult := rfl

-- p. 716: composition is not commutative
example : (.antiMult : Signature) * .antiAdd = .additive ∧
    (.antiAdd : Signature) * .antiMult = .mult := ⟨rfl, rfl⟩

-- p. 716: only `⊕` and `⊖` have inverses, so the signatures do not form a group
example : IsUnit (.antiAddMult : Signature) ∧ ¬ IsUnit (.antiAdd : Signature) :=
  ⟨isUnit_iff.2 ⟨.negative, rfl⟩, fun h ↦ by
    obtain ⟨p, hp⟩ := isUnit_iff.1 h
    cases p <;> cases hp⟩

/-- Negation after negation is a morphism, `⊖ ∘ ⊖ = ⊕`, certified on complementation itself. -/
example {α : Type*} [BooleanAlgebra α] :
    Signature.SoundFor (.antiAddMult * .antiAddMult) ((compl : α → α) ∘ compl) :=
  compl_soundFor_antiAddMult.comp compl_soundFor_antiAddMult

/-! ### Errata -/

/-- Read with the printed implication order, the ≪-maximal sound chaining of Definition 1.4 is
always `#`. -/
example (R S : Relation) : IsGreatest {T : Relation | ∀ x y z : Finset (Fin 3),
    R.Holds x y → S.Holds y z → T.Holds x z} ⊤ :=
  ⟨fun _ _ _ _ _ ↦ trivial, fun _ _ ↦ le_top⟩

/-- The printed remark that `•` projects every relation to `#` overshoots at `≡`, since every
function preserves equality. -/
example : project .equiv .all = .equiv := rfl

/-- Anti-additive after anti-additive is monotone; the printed antitone fails for complementation,
which applied twice is the identity. -/
example : (.antiAdd : Signature) * .antiAdd = .mono ∧
    ∃ f g : Bool → Bool, Signature.HoldsFor .antiAdd f ∧ Signature.HoldsFor .antiAdd g ∧
      ¬ Signature.HoldsFor .anti (f ∘ g) :=
  ⟨rfl, compl, compl, by decide⟩

/-- Anti-multiplicative after multiplicative is anti-multiplicative, more specific than the
printed antitone. -/
example : (.antiMult : Signature) * .mult = .antiMult ∧ (.antiMult : Signature) < .anti :=
  ⟨rfl, lt_of_le_of_ne (by decide) (by decide)⟩

/-- Anti-morphic after anti-multiplicative is multiplicative; the printed additive fails for
complementation after the constant `⊤`, which is the constant `⊥`. -/
example : (.antiAddMult : Signature) * .antiMult = .mult ∧
    ∃ f g : Bool → Bool, Signature.HoldsFor .antiAddMult f ∧ Signature.HoldsFor .antiMult g ∧
      ¬ Signature.HoldsFor .additive (f ∘ g) :=
  ⟨rfl, compl, fun _ ↦ true, by decide⟩

/-- An additive and an anti-additive function need not stand in `|`: the constant `⊤` and
complementation are not disjoint. -/
example : Signature.HoldsFor .additive (fun _ : Bool ↦ true) ∧
    Signature.HoldsFor .antiAdd (compl : Bool → Bool) ∧
      ¬ Disjoint (fun _ : Bool ↦ true) (compl : Bool → Bool) := by
  refine ⟨by decide, by decide, ?_⟩
  rw [disjoint_iff]
  decide

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
        show (Signature.all * c.pro) = .all from Signature.top_mul _]
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

/-- 𝒞 is sound for models of the assumptions in which no term denotes `⊥` (Theorem 3.1, Lemma 1.6,
Corollary 2.12). -/
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

/-- Each of the examples (1)–(6) is acceptable exactly when its context licenses its item: weak
*yet* under *not every* and *few*, strong *in years* under *few* and *no*, and superstrong *a tad
bit* under *no* and *not*, with the second arguments of *not every*, *few* and *no*
anti-multiplicative, antitone and anti-additive and *not* anti-morphic. -/
theorem licenses_iff_acceptable :
    (Licenses .weak .antiMult ↔ Examples.s4_1.judgment = .acceptable) ∧
    (Licenses .weak .anti ↔ Examples.s4_2.judgment = .acceptable) ∧
    (Licenses .antiAdditive .anti ↔ Examples.s4_3.judgment = .acceptable) ∧
    (Licenses .antiAdditive .antiAdd ↔ Examples.s4_4.judgment = .acceptable) ∧
    (Licenses .antiMorphic .antiAdd ↔ Examples.s4_5.judgment = .acceptable) ∧
    (Licenses .antiMorphic .antiAddMult ↔ Examples.s4_6.judgment = .acceptable) := by
  decide

end Icard2012
