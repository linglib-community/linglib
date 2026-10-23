module

public import Linglib.Logic.Trivalent.Four
public import Linglib.Logic.Bilattice.Guard
public import Mathlib.Order.Fin.Basic
public import Mathlib.Data.Bool.Basic

/-!
# Schöter (1996b): Evidential Bilattice Logic and Lexical Inference

This file formalizes the value space of the paper's Evidential Bilattice Logic. Natural
reasoning is partial, paraconsistent, relevant and defeasible, and the paper captures the four
properties by climbing a progression of lattices (Fig. 1): the classical two values, Kleene's
three, Belnap's `FOUR`, and the evidential bilattice `PRESUP` over the chain `0 < ½ < 1`, whose
values are pairs of degrees of evidence for and against a proposition (`PRESUP`, the diagonal
product `Fin 3 ⊙ Fin 3`), so that presumptions, confusion and defeated
defaults join the gap and the glut. `FOUR` embeds in it preserving both orders (`embed_le`,
`embed_kLE`). The evidential space is partitioned into Fitting's classical and consistent
values and the paper's designated and semi-designated ones, with the paper's order-theoretic
characterizations of the latter two (`designated_iff_top_kLE`, `semiDesignated_iff`). The
semi-designation function, the `presumably` operator of the evaluation clauses and the
evidential weighting that keeps only the dominant evidence are value-level connectives
(`semiDesignation`, `presumably`, `weight`), the last mapping `PRESUP` onto the constants of
[ginsberg-1988]'s default bilattice without being a homomorphism.

## Implementation notes

* The paper writes a value as `⟨against, for⟩`, reversing Fitting's coordinate order to fit its
  diagrams; this file keeps the substrate's `(for, against)` order, so the paper's `⟨a, b⟩` is
  `.mk b a` here.
* Fitting's conflation on `PRESUP` complements each coordinate on the chain by `Fin.rev`; it is
  the study's `Conflation` instance, built by `Bilattice.Product.conflation`.
* The paper's epistemic states, evidential links, its assertion, evaluation and closure
  semantics, and the §4 analyses of entailment, implicature and presupposition that run on
  them are not formalized; only the value level is.

## References

* [schoter-1996b]
* [fitting-1994]
* [ginsberg-1988]
* [belnap-1977]
-/

@[expose] public section

open Bilattice

namespace Schoter1996b

/-- The paper's `PRESUP` (§2.1): the evidential bilattice over the 3-chain `Fin 3 ~ {0, ½, 1}`,
`FOUR` with defeasible and presumed values added. -/
abbrev PRESUP := Fin 3 ⊙ Fin 3

/-- Fitting's conflation on `PRESUP`, complementing each coordinate on the chain by `Fin.rev`. -/
instance : Conflation PRESUP := Product.conflation Fin.rev Fin.rev_involutive Fin.rev_anti

namespace PRESUP

/-- `⊥`: no information, a presupposition gap. -/
def U : PRESUP := .mk 0 0
/-- Definite truth: full evidence for, none against. -/
def T : PRESUP := .mk 2 0
/-- Definite falsity. -/
def F : PRESUP := .mk 0 2
/-- Inconsistent or overdefined, a glut. -/
def I : PRESUP := .mk 2 2
/-- Presumably true: defeasible (`½`) evidence for, none against. -/
def Pplus : PRESUP := .mk 1 0
/-- Presumably false. -/
def Pminus : PRESUP := .mk 0 1
/-- Confused: conflicting defeasible evidence, not as strong a contradiction as `I` (§2.1). -/
def C : PRESUP := .mk 1 1
/-- The defeated default `D⁺`: default evidence for falsity overridden by definite evidence for
truth (§2.1). -/
def Dplus : PRESUP := .mk 2 1
/-- The defeated default `D⁻`: default evidence for truth overridden by definite evidence for
falsity (§2.1). -/
def Dminus : PRESUP := .mk 1 2

end PRESUP

/-- `Bool ↪ Fin 3`: `false ↦ 0` (no evidence), `true ↦ 2` (full evidence). -/
def boolToFin3 : Bool → Fin 3 := fun b ↦ if b then 2 else 0

/-- The embedding of `FOUR` into `PRESUP`, onto the definite values. -/
def embed (x : FOUR) : PRESUP := .mk (boolToFin3 x.pro) (boolToFin3 x.con)

theorem embed_le (x y : FOUR) : x ≤ y ↔ embed x ≤ embed y := by
  obtain ⟨xa, xb⟩ := x; obtain ⟨ya, yb⟩ := y
  cases xa <;> cases xb <;> cases ya <;> cases yb <;> decide

theorem embed_kLE (x y : FOUR) : x ≤ₖ y ↔ embed x ≤ₖ embed y := by
  obtain ⟨xa, xb⟩ := x; obtain ⟨ya, yb⟩ := y
  cases xa <;> cases xb <;> cases ya <;> cases yb <;> decide

theorem gap_and_presumption_consistent :
    IsConsistent PRESUP.U ∧ IsConsistent PRESUP.Pplus ∧ ¬ IsConsistent PRESUP.I := by
  decide

/-! ### Partitions of the evidential space (§2.2)

The classical and consistent subspaces are Fitting's (`IsExact`, `IsConsistent`); the designated and semi-designated subspaces are the paper's, with
its footnote characterizations `DES = {x | t ≤ₖ x}` and `SEMI = {x | ¬x ≤ x, U <ₖ x}` proved as
order-theoretic facts. -/

section Partitions

variable {S : Type*} [LinearOrder S] [BoundedOrder S]

/-- A designated value (§2.2) has maximal positive evidence: `DES = {⟨a, b⟩ | b = 1}`. -/
@[reducible] def Designated (x : S ⊙ S) : Prop := x.pro = ⊤

/-- A semi-designated value (§2.2) has some positive evidence, at least as strong as its
negative evidence: `SEMI = {⟨a, b⟩ | a ≤ b, 0 < b}`. -/
@[reducible] def SemiDesignated (x : S ⊙ S) : Prop :=
  x.con ≤ x.pro ∧ ⊥ < x.pro

/-- The footnote characterization of designation: a value is designated iff it is
knowledge-above the truth top, `DES = {x | t ≤ₖ x}` (§2.2). -/
theorem designated_iff_top_kLE {x : S ⊙ S} :
    Designated x ↔ (⊤ : S ⊙ S) ≤ₖ x :=
  ⟨fun h ↦ ⟨h.ge, bot_le⟩, fun h ↦ le_antisymm le_top h.1⟩

/-- A value is semi-designated iff it is truer than its negation and carries some information
(footnote, §2.2). -/
theorem semiDesignated_iff {x : S ⊙ S} :
    SemiDesignated x ↔ xᶜ ≤ x ∧ (⊥ : Know (S ⊙ S)) < toKnow x := by
  constructor
  · rintro ⟨hle, hlt⟩
    exact ⟨⟨hle, hle⟩, bot_lt_iff_ne_bot.mpr fun h ↦ hlt.ne' (congrArg Prod.fst h)⟩
  · rintro ⟨hneg, hlt⟩
    refine ⟨hneg.1, bot_lt_iff_ne_bot.mpr fun hp ↦ hlt.ne' ?_⟩
    exact Prod.ext hp (le_bot_iff.mp (hneg.1.trans hp.le))

/-- The designated subspace of `PRESUP` is `{T, D⁺, I}` (§2.2). -/
theorem designated_cases :
    ∀ x : PRESUP, Designated x ↔ x = PRESUP.T ∨ x = PRESUP.Dplus ∨ x = PRESUP.I := by
  decide

/-- The semi-designated subspace of `PRESUP` is `{P⁺, C, T, D⁺, I}` (§2.2). -/
theorem semiDesignated_cases :
    ∀ x : PRESUP, SemiDesignated x ↔ x = PRESUP.Pplus ∨ x = PRESUP.C ∨ x = PRESUP.T
      ∨ x = PRESUP.Dplus ∨ x = PRESUP.I := by
  decide

/-- On `FOUR`, with no defeasible evidence, semi-designation collapses to designation,
`SEMI = DES` (§2.2). -/
theorem four_semiDesignated_iff_designated :
    ∀ x : FOUR, SemiDesignated x ↔ Designated x := by
  decide

/-- The consistent fragment of `FOUR` is closed under negation, the truth operations and
consensus `⊓ₖ` (§2.2). -/
theorem four_consistent_closed :
    ∀ x y : FOUR, IsConsistent x → IsConsistent y →
      IsConsistent xᶜ ∧ IsConsistent (x ⊓ y) ∧ IsConsistent (x ⊔ y) ∧ IsConsistent (x ⊓ₖ y) :=
  fun _ y hx hy ↦ ⟨hx.compl, hx.inf hy, hx.sup hy, hx.kInf y⟩

theorem four_consistent_not_closed_kSup :
    ¬ ∀ x y : FOUR, IsConsistent x → IsConsistent y → IsConsistent (x ⊔ₖ y) :=
  fun h ↦ absurd (h FOUR.T FOUR.F (by decide) (by decide)) (by decide)

/-- The classical fragment of `FOUR` is closed under negation and the truth operations
(§2.2), and so supports classical logic. -/
theorem four_isClassical_closed :
    ∀ x y : FOUR, IsExact x → IsExact y → IsExact xᶜ ∧ IsExact (x ⊓ y) ∧ IsExact (x ⊔ y) :=
  fun _ _ hx hy ↦ ⟨hx.compl, hx.inf hy, hx.sup hy⟩

end Partitions

/-! ### Value-level connectives (Definitions 4, 5, 14 and 16)

The recursive evaluation clauses of Definition 14 are value-functional except for the
inference-link connective: clause 1 is Ginsberg negation `ᶜ`, clauses 3 and 4 are `⊓` and `⊔`, clause 5
is Fitting's guard, and clause 2, the `presumably` operator, is built from the guard and the
semi-designation function. -/

section Connectives

open Bilattice.Product (guard)

variable {S : Type*} [LinearOrder S] [BoundedOrder S]

/-- The semi-designation function `σ` (Definition 5): `T` on the semi-designated values, `F`
elsewhere. -/
def semiDesignation (x : S ⊙ S) : S ⊙ S :=
  if SemiDesignated x then .mk ⊤ ⊥ else .mk ⊥ ⊤

/-- The value-level `presumably` operator `π` (Definition 14, clause 2): `σ(v) : T ⊕ σ(¬v) : F`,
presumably true if the value is semi-designated, presumably false if its negation is, the two
unified informationally. -/
def presumably (v : S ⊙ S) : S ⊙ S :=
  (guard (semiDesignation v) (.mk ⊤ ⊥) ⊔ₖ
    guard (semiDesignation vᶜ) (.mk ⊥ ⊤))

theorem presumably_table :
    presumably PRESUP.Pplus = PRESUP.T ∧ presumably PRESUP.T = PRESUP.T ∧
      presumably PRESUP.F = PRESUP.F ∧ presumably PRESUP.U = PRESUP.U ∧
      presumably PRESUP.I = PRESUP.I := by
  decide

/-- The evidential-weighting function `f⋆` (Definition 16) suppresses the dominated evidence, so
that only the dominant evidence figures in evaluation. -/
def weight (x : S ⊙ S) : S ⊙ S :=
  if x.con < x.pro then .mk x.pro ⊥ else if x.pro < x.con then .mk ⊥ x.con else x

theorem weight_dplus : weight PRESUP.Dplus = PRESUP.T := by decide

theorem weight_dminus : weight PRESUP.Dminus = PRESUP.F := by decide

/-- `f⋆` maps `PRESUP` onto the seven constants of [ginsberg-1988]'s default bilattice
(Definition 16). -/
theorem weight_mem_default :
    ∀ x : PRESUP, weight x ∈ [PRESUP.U, PRESUP.Pminus, PRESUP.Pplus, PRESUP.C,
      PRESUP.F, PRESUP.T, PRESUP.I] := by
  decide

/-- The weighting is not a bilattice homomorphism onto the default bilattice (Definition 16):
it fails to commute with gullibility `⊔ₖ`. -/
theorem weight_not_kSup_hom :
    ¬ ∀ x y : PRESUP, weight (x ⊔ₖ y) = weight x ⊔ₖ weight y := by
  decide

end Connectives

end Schoter1996b
