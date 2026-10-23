module

public import Linglib.Logic.ComparativeProbability.Defs

/-!
# Validity patterns for comparative probability

Yalcin assesses semantics for *probably* and the comparative *at least as likely as* against
inference patterns: the intuitively valid V1–V12, the invalid I1–I3, and the questionable
Conjunctivitis E1. Holliday and Icard's Figure 1 keeps his labels for V1–V7, V11, V12 and
I1–I3, leaves out the conditional patterns V8–V10 and E1, and adds V13, which Lassiter defends
against symmetric fuzzy measures. Each pattern is a predicate on a likelihood relation `r` on a
Boolean algebra, with the account's modals (V6, V7) and conditional (V8–V10) as parameters; I1
is `RightUnion`. Each valid pattern is derived once from the axioms in `Defs.lean`, so a model
discharges it by instance resolution.

## Main statements

* `mustToProbably_eq_top_iff`, `probablyToMight_ne_bot_iff`: for the quantifiers `a = ⊤` and
  `a ≠ ⊥` over the epistemic space, V6 says that the tautology is probable and V7 that the
  contradiction is not.
* `strictDisjunctionIntro_iff`: over a monotone order, V13 says that an event at least as
  likely as a disjunction it is part of leaves the rest no more likely than `⊥`.
* `chancyModusTollens_iff`: V9 is V8 by contraposition, whatever the conditional.
* `equiprobabilityCollapse_of_rightUnion`, `hamblinCollapse_of_equiprobabilityCollapse`,
  `complementTransfer_of_equiprobabilityCollapse`: I1 gives I2, as Yalcin derives it, and I2
  gives I3 and V12. This is why Holliday and Icard's Fact 1 finds V12 valid for the l-lifting
  although Yalcin counts it among the failures of Kratzer's account.

## References

* [yalcin-2010]
* [holliday-icard-2013]
* [lassiter-2015]
-/

@[expose] public section

namespace ComparativeProbability

variable {α : Type*} [BooleanAlgebra α] (r : α → α → Prop)

/-- V1, *probably* to not *probably* not, holds when `△a` gives `¬△aᶜ`. -/
def ProbablyToNotProbablyNot : Prop := ∀ a : α, Probably r a → ¬ Probably r aᶜ
/-- V2, distribution over conjunction, holds when `△(a ⊓ b)` gives `△a` and `△b`. -/
def ProbablyDistribInf : Prop := ∀ a b : α, Probably r (a ⊓ b) → Probably r a ∧ Probably r b
/-- V3, chancy disjunction introduction, holds when `△a` gives `△(a ⊔ b)`. -/
def ChancyDisjunctionIntro : Prop := ∀ a b : α, Probably r a → Probably r (a ⊔ b)
/-- V4, minimality, holds when every `a` is at least as likely as `⊥`. -/
def Minimality : Prop := ∀ a : α, r a ⊥
/-- V5, maximality, holds when `⊤` is at least as likely as every `a`. -/
def Maximality : Prop := ∀ a : α, r ⊤ a
/-- V6, *must* to *probably*, holds when `□a` gives `△a` for the account's necessity modal. -/
def MustToProbably (must : α → Prop) : Prop := ∀ a : α, must a → Probably r a
/-- V7, *probably* to *might*, holds when `△a` gives `◇a` for the account's possibility
modal. -/
def ProbablyToMight (might : α → Prop) : Prop := ∀ a : α, Probably r a → might a
/-- V8, chancy modus ponens, holds when *if `a`, `b`* and `△a` give `△b` for the account's
indicative conditional. -/
def ChancyModusPonens (ifThen : α → α → Prop) : Prop :=
  ∀ a b : α, ifThen a b → Probably r a → Probably r b
/-- V9, chancy modus tollens, holds when *if `a`, `b`* and `¬△b` give `¬△a`. -/
def ChancyModusTollens (ifThen : α → α → Prop) : Prop :=
  ∀ a b : α, ifThen a b → ¬ Probably r b → ¬ Probably r a
/-- V10, conditional to comparative, holds when *if `a`, `b`* gives `b ≽ a`. -/
def ConditionalToComparative (ifThen : α → α → Prop) : Prop := ∀ a b : α, ifThen a b → r b a
/-- V11, positive form transfer, holds when `b ≽ a` and `△a` give `△b`. -/
def PositiveFormTransfer : Prop := ∀ a b : α, r b a → Probably r a → Probably r b
/-- V12, complement transfer, holds when `b ≽ a` and `a ≽ aᶜ` give `b ≽ bᶜ`. -/
def ComplementTransfer : Prop := ∀ a b : α, r b a → r a aᶜ → r b bᶜ
/-- V13, strict disjunction introduction, holds when `(a \ b) ≻ ⊥` gives `(a ⊔ b) ≻ b`. -/
def StrictDisjunctionIntro : Prop := ∀ a b : α, Strict r (a \ b) ⊥ → Strict r (a ⊔ b) b
/-- I2, collapse of equiprobability into certainty, holds when `a ≽ aᶜ` gives `a ≽ b`. The
premise is Figure 1's one-directional one, where Yalcin writes *as likely as*. -/
def EquiprobabilityCollapse : Prop := ∀ a b : α, r a aᶜ → r a b
/-- I3, Hamblin's collapse, holds when `△a` gives `a ≽ b`. -/
def HamblinCollapse : Prop := ∀ a b : α, Probably r a → r a b
/-- E1, Conjunctivitis, holds when `△a` and `△b` give `△(a ⊓ b)`. -/
def Conjunctivitis : Prop := ∀ a b : α, Probably r a → Probably r b → Probably r (a ⊓ b)

variable {r}

theorem probablyToNotProbablyNot : ProbablyToNotProbablyNot r := by
  rintro a ⟨_, hanot⟩ ⟨hac, _⟩
  rw [compl_compl] at hac; exact hanot hac

/-- V9 is V8 by contraposition, for any conditional. -/
theorem chancyModusTollens_iff {ifThen : α → α → Prop} :
    ChancyModusTollens r ifThen ↔ ChancyModusPonens r ifThen :=
  ⟨fun h a b hab ha ↦ by_contra (h a b hab · ha), fun h a b hab hb ha ↦ hb (h a b hab ha)⟩

/-- V6 for the necessity modal `a = ⊤` says exactly that the tautology is probable. -/
theorem mustToProbably_eq_top_iff : MustToProbably r (· = ⊤) ↔ Probably r ⊤ :=
  ⟨fun h ↦ h ⊤ rfl, fun h _ ha ↦ ha ▸ h⟩

/-- V7 for the possibility modal `a ≠ ⊥` says exactly that the contradiction is not
probable. -/
theorem probablyToMight_ne_bot_iff : ProbablyToMight r (· ≠ ⊥) ↔ ¬ Probably r ⊥ :=
  ⟨fun h hb ↦ h ⊥ hb rfl, fun h _ ha hb ↦ h (hb ▸ ha)⟩

/-- I3 is I2 with a strict premise. -/
theorem hamblinCollapse_of_equiprobabilityCollapse (h : EquiprobabilityCollapse r) :
    HamblinCollapse r := fun a b ha ↦ h a b ha.1

section Mono

variable [IsLikelihoodMono r]

theorem minimality : Minimality r := fun _ ↦ mono _ _ bot_le

theorem maximality : Maximality r := fun _ ↦ mono _ _ le_top

theorem mustToProbably [IsNontrivial r] : MustToProbably r (· = ⊤) :=
  mustToProbably_eq_top_iff.2 probably_top

theorem probablyToMight : ProbablyToMight r (· ≠ ⊥) :=
  probablyToMight_ne_bot_iff.2 not_probably_bot

theorem conditionalToComparative_le : ConditionalToComparative r (· ≤ ·) := fun _ _ ↦ mono _ _

theorem probablyDistribInf [IsTrans α r] : ProbablyDistribInf r :=
  fun _ _ h ↦ ⟨h.mono inf_le_left, h.mono inf_le_right⟩

theorem chancyDisjunctionIntro [IsTrans α r] : ChancyDisjunctionIntro r :=
  fun _ _ h ↦ h.mono le_sup_left

theorem chancyModusPonens_le [IsTrans α r] : ChancyModusPonens r (· ≤ ·) :=
  fun _ _ ↦ Probably.mono

theorem chancyModusTollens_le [IsTrans α r] : ChancyModusTollens r (· ≤ ·) :=
  chancyModusTollens_iff.2 chancyModusPonens_le

/-- Over a monotone order, V13 says that a proposition at least as likely as a disjunction it
is part of leaves the rest of the disjunction no more likely than `⊥`. -/
theorem strictDisjunctionIntro_iff :
    StrictDisjunctionIntro r ↔ ∀ a b, r b (a ⊔ b) → r ⊥ (a \ b) := by
  refine ⟨fun h a b hb ↦ by_contra fun hne ↦ (h a b ⟨mono _ _ bot_le, hne⟩).2 hb, ?_⟩
  rintro h a b ⟨-, hne⟩
  exact ⟨mono _ _ le_sup_right, fun hc ↦ hne (h a b hc)⟩

theorem strictDisjunctionIntro [IsQualitativeAdditive r] : StrictDisjunctionIntro r :=
  strictDisjunctionIntro_iff.2 fun a b hb ↦ by
    have := (qadd b (a ⊔ b)).1 hb
    rwa [sdiff_eq_bot_iff.2 le_sup_right, sup_sdiff_right_self] at this

end Mono

section Trans

variable [IsTrans α r]

theorem positiveFormTransfer [IsComplementReversing r] : PositiveFormTransfer r :=
  fun _ _ hba ha ↦ strict_of_strict_of_rel (strict_of_rel_of_strict hba ha) (complRev _ _ hba)

theorem complementTransfer [IsComplementReversing r] : ComplementTransfer r :=
  fun _ _ hba ha ↦ _root_.trans (_root_.trans hba ha) (complRev _ _ hba)

/-- I2 makes V12 trivial, since `a ≽ aᶜ` already gives `a ≽ bᶜ`. -/
theorem complementTransfer_of_equiprobabilityCollapse (h : EquiprobabilityCollapse r) :
    ComplementTransfer r :=
  fun a b hba ha ↦ _root_.trans hba (h a bᶜ ha)

/-- The union property gives I2, as Yalcin derives it, since I1 for `a`, `a` and `aᶜ` gives
`a ≽ ⊤` and V5 does the rest. -/
theorem equiprobabilityCollapse_of_rightUnion [IsLikelihoodMono r] (hJ : RightUnion r) :
    EquiprobabilityCollapse r := fun a _ ha ↦
  _root_.trans (sup_compl_eq_top (x := a) ▸ hJ a a aᶜ (mono _ _ le_rfl) ha) (mono _ _ le_top)

end Trans

end ComparativeProbability
