module

public import Mathlib.Order.UpperLower.Basic
public import Studies.Rett2020a
public import Studies.Heinamaki1974
public import Linglib.Data.Examples.Rett2026

/-!
# Rett (2026): Semantic ambivalence and expletive negation

This file formalizes the paper's account of low expletive negation, negation that targets
truth-conditional content without changing it. A scalar construction licenses it when it is
fixed-point ambidirectional: the construction relates the informative bound of its argument,
and an interval and its complement share that bound. The degrees an individual reaches and
the degrees it does not both have the individual's height as their bound, `sharesBounds_Iic`,
so a comparative with a negated standard is the comparative, `tallerNeg_iff_taller`, whereas
a scale with a top gives the complement a second bound and blocks the pattern. The runtime of
a negated event is the interval before it, `preEvent`, whose end *before*, *until* and *since*
read as the event's start, `before_preEvent_completive_iff`; *after* gains nothing from it and
*while* is not ambidirectional. The negated standard stays downward entailing, so negative
polarity items survive. The paper's examples are rows, and `en_rows` records which
constructions attest expletive negation.

## Implementation notes

Degrees are a linear order and a degree relative denotes the ray of degrees an individual
reaches; maximality relativized to a scale is the least upper bound on the positive scale and
the greatest lower bound on the negative one, which is what a negated degree relative
carries. Times carry a bottom, the paper's minus infinity, so that the pre-event interval is a
closed interval of the substrate. The survey counts of Jin and Koenig, the high expletive
negation of exclamations, the manner implicature effects and the negative verbs are discussed
in the paper without a proposal formalized here.

## References

* [J. Rett, *Semantic ambivalence and expletive negation* (2026)][rett-2026]
* [J. Rett, *Eliminating EARLIEST* (2020)][rett-2020a]
* [P. Cépeda, *Negation and time: against expletive negation in temporal clauses*
  (2018)][cepeda-2018]
* [Y. Jin, J.-P. Koenig, *A cross-linguistic study of expletive negation*
  (2021)][jin-koenig-2021]
* [C. Greco, *Negative polarity items and expletive negation* (2018)][greco-2018]
* [D. J. Napoli, M. Nespor, *Negatives in comparatives* (1976)][napoli-nespor-1976]
* [C. Kennedy, L. McNally, *Scale structure, degree modification, and the semantics of
  gradable predicates* (2005)][kennedy-mcnally-2005]
* [O. Heinämäki, *Semantics of English temporal connectives* (1974)][heinamaki-1974]
-/

@[expose] public section

namespace Rett2026

open Degree Tense Rett2020a

/-! ### Ambivalence -/

/-- Semantic ambivalence (4) is a sentence's ambiguity between two propositions each equivalent to
the negation of the other. -/
def Ambivalent (p q : Prop) : Prop := p ↔ ¬ q

/-- Ambivalence is symmetric. -/
theorem Ambivalent.symm {p q : Prop} (h : Ambivalent p q) : Ambivalent q p := h.not_left.symm

/-! ### Degrees -/

section Degrees

variable {E D : Type*} [LinearOrder D] (μ : E → D)

/-- The informative bounds of a set of degrees are its greatest lower and least upper bounds, when
it has them. -/
def informativeBounds (X : Set D) : Set D := {x | IsGLB X x ∨ IsLUB X x}

/-- A degree set is fixed-point ambidirectional when every informative bound of its complement is
one of its own, so a relation to the informative bound is insensitive to negation. -/
def SharesBounds (X : Set D) : Prop := informativeBounds Xᶜ ⊆ informativeBounds X

theorem sharesBounds_Iic [DenselyOrdered D] [NoMaxOrder D] (a : D) :
    SharesBounds (Set.Iic a) := by
  intro x hx
  rw [Set.compl_Iic] at hx
  rcases hx with hx | hx
  · exact Or.inr (hx.unique isGLB_Ioi ▸ isLUB_Iic)
  · exact (not_bddAbove_Ioi a hx.bddAbove).elim

theorem not_sharesBounds_Iic [OrderTop D] {a : D} (ha : a < ⊤) : ¬ SharesBounds (Set.Iic a) := by
  intro h
  have htop : ⊤ ∈ informativeBounds (Set.Iic a)ᶜ := by
    rw [Set.compl_Iic]
    exact Or.inr ⟨fun _ _ ↦ le_top, fun b hb ↦ hb ha⟩
  rcases h htop with hx | hx
  · exact absurd (hx.1 (Set.mem_Iic.mpr le_rfl)) (not_le.mpr ha)
  · exact absurd (hx.2 (fun _ hx ↦ hx)) (not_le.mpr ha)

variable (a b : E)

/-- The comparative (47) holds when the least upper bound of the target's degrees exceeds that of
the standard's. -/
def taller : Prop := ∃ d' d, IsLUB (Set.Iic (μ a)) d' ∧ IsLUB (Set.Iic (μ b)) d ∧ d < d'

/-- The comparative with a negated standard (53) reads the standard's degree relative on the
negative scale, so its informative bound is the greatest lower bound of the degrees the standard
does not reach. -/
def tallerNeg : Prop := ∃ d' d, IsLUB (Set.Iic (μ a)) d' ∧ IsGLB (Set.Ioi (μ b)) d ∧ d < d'

theorem taller_iff : taller μ a b ↔ μ b < μ a :=
  ⟨fun ⟨_, _, h', h, hlt⟩ ↦ by rwa [h.unique isLUB_Iic, h'.unique isLUB_Iic] at hlt,
    fun h ↦ ⟨μ a, μ b, isLUB_Iic, isLUB_Iic, h⟩⟩

theorem tallerNeg_iff [DenselyOrdered D] : tallerNeg μ a b ↔ μ b < μ a :=
  ⟨fun ⟨_, _, h', h, hlt⟩ ↦ by rwa [h.unique isGLB_Ioi, h'.unique isLUB_Iic] at hlt,
    fun h ↦ ⟨μ a, μ b, isLUB_Iic, isGLB_Ioi, h⟩⟩

theorem tallerNeg_iff_taller [DenselyOrdered D] : tallerNeg μ a b ↔ taller μ a b :=
  (tallerNeg_iff μ a b).trans (taller_iff μ a b).symm

/-- The comparative is downward entailing in its standard (80). -/
theorem taller_antitone {c : E} (h : μ b ≤ μ a) : taller μ c a → taller μ c b :=
  fun ht ↦ (taller_iff μ c b).mpr (h.trans_lt ((taller_iff μ c a).mp ht))

theorem tallerNeg_antitone [DenselyOrdered D] {c : E} (h : μ b ≤ μ a) :
    tallerNeg μ c a → tallerNeg μ c b :=
  fun ht ↦ (tallerNeg_iff_taller μ c b).mpr
    (taller_antitone μ a b h ((tallerNeg_iff_taller μ c a).mp ht))

end Degrees

/-! ### Times -/

section Times

variable {T : Type*} [LinearOrder T] (A : Set (NonemptyInterval T))

/-- *A until B* (73) holds when the last time of `A` precedes the first time of `B`. -/
def until_ (B : Set (NonemptyInterval T)) : Prop :=
  ∃ m ∈ maxOnScale .gt (timeTrace A), ∃ m' ∈ maxOnScale .lt (timeTrace B), m < m'

theorem until_iff_of_isLeast {B : Set (NonemptyInterval T)} {m' : T}
    (h : IsLeast (timeTrace B) m') :
    until_ A B ↔ ∃ m ∈ maxOnScale .gt (timeTrace A), m < m' := by
  simp only [until_, maxOnScale_lt_eq, Set.mem_ofPred_eq]
  exact ⟨fun ⟨m, hm, _, hm', hlt⟩ ↦ ⟨m, hm, hm'.unique h ▸ hlt⟩,
    fun ⟨m, hm, hlt⟩ ↦ ⟨m, hm, m', h, hlt⟩⟩

variable [OrderBot T] (s : T)

/-- The runtime of a negated event is the interval from the beginning of time to the event's start.
-/
def preEvent : Set (NonemptyInterval T) := Set.Iic ⟨⟨⊥, s⟩, bot_le⟩

theorem isLeast_timeTrace_preEvent : IsLeast (timeTrace (preEvent s)) ⊥ :=
  isLeast_timeTrace_stative _

theorem isGreatest_timeTrace_preEvent : IsGreatest (timeTrace (preEvent s)) s :=
  isGreatest_timeTrace_stative _

theorem isLeast_timeTrace_completive_preEvent :
    IsLeast (timeTrace (completive (preEvent s))) s := by
  rw [timeTrace_completive_of_isGreatest (isGreatest_timeTrace_preEvent s)]
  exact isLeast_singleton

theorem not_before_preEvent : ¬ before A (preEvent s) := by
  rw [before_iff_of_isLeast (isLeast_timeTrace_preEvent s)]
  rintro ⟨_, _, h⟩
  exact not_lt_bot h

theorem before_preEvent_completive_iff :
    before A (completive (preEvent s)) ↔ ∃ t ∈ timeTrace A, t < s :=
  before_completive_iff (isGreatest_timeTrace_preEvent s)

theorem before_ambidirectional (i : NonemptyInterval T) :
    before A (Set.Iic i) ↔ before A (completive (preEvent i.fst)) :=
  (before_iff_of_isLeast (isLeast_timeTrace_stative i)).trans
    (before_preEvent_completive_iff A i.fst).symm

theorem after_preEvent_iff : after A (preEvent s) ↔ ∃ t ∈ timeTrace A, s < t :=
  after_iff_of_isGreatest (isGreatest_timeTrace_preEvent s)

theorem after_preEvent_inchoative {t : T} (ht : t ∈ timeTrace A) (h : t ≠ ⊥) :
    after A (inchoative (preEvent s)) :=
  (after_inchoative_iff (isLeast_timeTrace_preEvent s)).mpr ⟨t, ht, bot_lt_iff_ne_bot.mpr h⟩

theorem until_preEvent_completive_iff (i : NonemptyInterval T) :
    until_ A (Set.Iic i) ↔ until_ A (completive (preEvent i.fst)) := by
  rw [until_iff_of_isLeast A (isLeast_timeTrace_stative i),
    until_iff_of_isLeast A (isLeast_timeTrace_completive_preEvent i.fst)]

theorem since_preEvent_completive_iff :
    Heinamaki1974.since A (completive (preEvent s)) ↔
      Heinamaki1974.since A {NonemptyInterval.pure s} := by
  unfold Heinamaki1974.since
  rw [timeTrace_completive_of_isGreatest (isGreatest_timeTrace_preEvent s), timeTrace_singleton,
    NonemptyInterval.coe_pure]

end Times

section NotAmbidirectional

/-- A scalar construction `f` is ambidirectional at `B` when it returns the same result on `B` and
on its complement, as maximality does when it picks the same boundary from both; this is the
mechanism behind expletive negation. -/
def IsAmbidirectional {α : Type*} (f : Set α → Prop) (B : Set α) : Prop :=
  f B ↔ f Bᶜ

variable {T : Type*}

theorem after_not_ambidirectional [LinearOrder T] (hab : ∃ a b : T, a < b) :
    ¬ ∀ (A : Set (NonemptyInterval T)) (B : Set T),
      IsAmbidirectional (fun X ↦ ∃ t ∈ timeTrace A, ∃ m ∈ maxOnScale .gt X, m < t) B := by
  obtain ⟨a, b, hab⟩ := hab
  intro h
  have h_amb := h {NonemptyInterval.pure b} {a}
  have h_fB : ∃ t ∈ timeTrace ({NonemptyInterval.pure b} : Set (NonemptyInterval T)),
      ∃ m ∈ maxOnScale .gt ({a} : Set T), m < t :=
    ⟨b, ⟨NonemptyInterval.pure b, rfl, le_refl _, le_refl _⟩,
     a, ⟨rfl, fun _ hx' hne ↦ absurd hx' hne⟩, hab⟩
  obtain ⟨t, ht_A, m, ⟨_, hm_dom⟩, htm⟩ := h_amb.mp h_fB
  obtain ⟨j, hj_mem, hj_s, hj_f⟩ := ht_A
  simp only [Set.mem_singleton_iff] at hj_mem
  subst hj_mem
  simp only [NonemptyInterval.pure] at hj_s hj_f
  have ht_eq : t = b := le_antisymm hj_f hj_s
  have hb_compl : b ∈ ({a} : Set T)ᶜ := by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; exact ne_of_gt hab
  by_cases hmb : m = b
  · rw [ht_eq, hmb] at htm; exact absurd htm (lt_irrefl _)
  · rw [ht_eq] at htm
    exact absurd htm (not_lt.mpr (le_of_lt (hm_dom b hb_compl (Ne.symm hmb))))

/-- *While* is not ambidirectional, so Hungarian *amíg* with negation reads only as *until* (74). -/
theorem while_not_ambidirectional [Inhabited T] :
    ¬ ∀ (A B : Set T), IsAmbidirectional (fun X ↦ ∀ t ∈ A, t ∈ X) B := by
  intro h
  have := h {default} {default}
  simp only [IsAmbidirectional] at this
  have lhs : ∀ t ∈ ({default} : Set T), t ∈ ({default} : Set T) := fun _ h ↦ h
  have rhs := this.mp lhs (default : T) rfl
  exact absurd rfl rhs

end NotAmbidirectional

/-! ### The paper's examples -/

/-- The constructions of the paper's examples. -/
inductive Construction where
  | before
  | until
  | since
  | comparative
  | closedScaleComparative
  | differentialComparative
  | equative
  | preference
  | negativeVerb
  | exclamative
  | surpriseNegation
  | notSure
  deriving DecidableEq, Fintype

/-- The constructions by their `paperFeatures` labels. -/
def Construction.labels : List (String × Construction) :=
  [("before", .before), ("until", .until), ("since", .since), ("comparative", .comparative),
   ("closedScaleComparative", .closedScaleComparative),
   ("differentialComparative", .differentialComparative), ("equative", .equative),
   ("preference", .preference), ("negativeVerb", .negativeVerb), ("exclamative", .exclamative),
   ("surpriseNegation", .surpriseNegation), ("notSure", .notSure)]

/-- The scalar relations the paper analyzes as fixed-point ambidirectional. -/
def Construction.Scalar : Construction → Prop
  | .before | .until | .since | .comparative | .equative => True
  | _ => False

instance : DecidablePred Construction.Scalar := fun c ↦ by
  cases c <;> unfold Construction.Scalar <;> infer_instance

/-- An example records its construction and judgment. -/
structure Row where
  construction : Construction
  judgment : Judgment

/-- A datum read into its row. -/
def Row.ofDatum (e : Datum) : Option Row := do
  pure ⟨← e.parse? "construction" Construction.labels, e.judgment⟩

theorem isSome_ofDatum : ∀ e ∈ Examples.all, (Row.ofDatum e).isSome := by decide

/-- The paper's examples. -/
def data : List Row := Examples.all.filterMap Row.ofDatum

theorem en_rows :
    (∀ c : Construction, c.Scalar →
        ∃ d ∈ data, d.construction = c ∧ d.judgment = .acceptable) ∧
      ∀ d ∈ data, d.construction = .closedScaleComparative → d.judgment ≠ .acceptable := by
  decide

end Rett2026
