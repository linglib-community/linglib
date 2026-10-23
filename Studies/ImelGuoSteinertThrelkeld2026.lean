module

public import Linglib.Semantics.Modality.Universals
public import Linglib.Data.Examples.ImelGuoSteinertThrelkeld2026
public import Linglib.Fragments.Washo.Modals
public import Studies.MocnikAbramovitz2019
public import Linglib.Fragments.Greek.StandardModern.Modals
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.Probability.UniformOn
public import Mathlib.Tactic.Linarith

/-!
# Imel, Guo and Steinert-Threlkeld (2026): An Efficient Communication Analysis of Modal Typology

This file formalizes the efficient-communication model of [imel-guo-steinert-threlkeld-2026].
A modal meaning is a subset of the six-point space `space`, weak and strong force by epistemic,
deontic and circumstantial flavor, and a language is a multiset of meanings. The complexity of
a meaning, Equation (1), is the least number of atoms of a formula of a Boolean Language of
Thought denoting it, computed here from the denotations of formulas with a given number of
atoms (`Formula.dens`, `complexity`). The informativeness of a language, Equations (2) and (3),
is the expected utility of literal communication under a communicative need distribution
(a `MeasureTheory.Measure` on the space): the speaker picks uniformly among the modals
expressing the intended point (`speak`), the listener guesses uniformly among the points of the
modal heard (`ProbabilityTheory.uniformOn`) and earns half credit for each axis guessed right
(`listen`, `informativeness`). Languages are compared by Pareto dominance, the product order on
their pairs of complexity and communicative cost (`costPair`), and naturalness is the fraction of
a vocabulary satisfying the Independence of Force and Flavor universal of
[steinert-threlkeld-imel-guo-2023], the substrate's `Modality.ForceFlavorIndependent`.

The paper's three results, that every Pareto-optimal system consists of IFF modals, that
naturalness correlates with optimality, and that the attested inventories are more optimal than
the sampled ones, are computational and are not formalized. What is proved are the properties
of the measures the results rest on. Table 2's complexities are recomputed over the experiment's
space, a modal for each point conveys every point exactly (the informativeness is the need of
the space) where a single all-purpose modal earns five twelfths of it, a product meaning's
listener utility depends only on its two axis sizes, and a language with synonyms is dominated
by, and so never Pareto-optimal against, the same language without them.

## Implementation notes

* Table 2 illustrates complexity over a four-flavor space with a teleological flavor the
  library folds into circumstantial. Over the experiment's six-point space *may* is denoted by
  *w ∧ ¬c* and has complexity two, not the table's three, so the table's language has total
  complexity seven rather than eight.
* *may* and St'át'imcets *k'a* are read off the paper's examples (2) and (3), whose rows record
  a force and a flavor each.
* The paper's two counterexamples to the Single Axis of Variability universal, Washo *-eʔ* and
  Koryak *ivək*, are not in its sample of 27 languages. *ivək*'s doxastic and assertive
  flavors ([mocnik-abramovitz-2019]) lie outside the six-point space.
* The probabilistic layer is measure-theoretic: the need distribution is a measure, the
  listener is `ProbabilityTheory.uniformOn` and the speaker a sum of Dirac measures over the
  multiset of applicable modals, so synonyms keep their multiplicity, and the statements are
  `ℝ≥0∞`-valued; `cost` is a truncated subtraction, zero if a non-probability need drove the
  informativeness above one.

## References

* [imel-guo-steinert-threlkeld-2026]
* [steinert-threlkeld-imel-guo-2023]
* [nauze-2008]
* [rullmann-matthewson-davis-2008]
* [bochnak-2015a]
* [mocnik-abramovitz-2019]
-/

@[expose] public section

namespace ImelGuoSteinertThrelkeld2026

open MeasureTheory Modality Finset ProbabilityTheory
open scoped ENNReal

/-- The forces of the experiment's space, weak and strong. -/
def forces : Finset ModalForce := {.possibility, .necessity}

/-- The flavors of the experiment's space. -/
def flavors : Finset ModalFlavor := {.epistemic, .deontic, .circumstantial}

/-- The meaning space `P`, six force-flavor pairs. -/
def space : Finset ForceFlavor := forces ×ˢ flavors

/-- A modal meaning, the force-flavor pairs a modal can express. -/
abbrev Meaning := Finset ForceFlavor

/-! ### The paper's examples -/

/-- The force-flavor pair a row's annotation records. -/
def Examples.forceFlavor (e : Datum) : Option ForceFlavor := do
  let fo ← match e.paperFeatures.lookup "force" with
    | some "weak" => some ModalForce.possibility
    | some "strong" => some ModalForce.necessity
    | _ => none
  let fl ← match e.paperFeatures.lookup "flavor" with
    | some "epistemic" => some ModalFlavor.epistemic
    | some "deontic" => some ModalFlavor.deontic
    | some "circumstantial" => some ModalFlavor.circumstantial
    | _ => none
  return (fo, fl)

/-- English *may*, the pairs of examples (2a) and (2b). -/
def may : Meaning := ([Examples.s2a, Examples.s2b].filterMap Examples.forceFlavor).toFinset

/-- St'át'imcets *k'a*, the pairs of examples (3a) and (3b), after
[rullmann-matthewson-davis-2008]. -/
def ka : Meaning := ([Examples.s3a, Examples.s3b].filterMap Examples.forceFlavor).toFinset

theorem may_eq : may = {(.possibility, .epistemic), (.possibility, .deontic)} := by decide

theorem ka_eq : ka = {(.necessity, .epistemic), (.possibility, .epistemic)} := by decide

/-- Table 1: *may* varies in flavor and *k'a* in force, each on a single axis. -/
theorem singleAxis_may_ka : SingleAxis may ∧ SingleAxis ka := by
  rw [may_eq, ka_eq]; decide

/-! ### The Language of Thought and complexity -/

/-- The atoms of the Language of Thought, one per force and one per flavor of the space. -/
inductive Atom
  | weak
  | strong
  | epistemic
  | deontic
  | circumstantial
  deriving DecidableEq, Fintype

/-- The points at which an atom holds, a row or a column of the space. -/
def Atom.den : Atom → Meaning
  | .weak => {.possibility} ×ˢ flavors
  | .strong => {.necessity} ×ˢ flavors
  | .epistemic => forces ×ˢ {.epistemic}
  | .deontic => forces ×ˢ {.deontic}
  | .circumstantial => forces ×ˢ {.circumstantial}

/-- The atom for a force of the space. -/
def Atom.ofForce : ModalForce → Atom
  | .possibility => .weak
  | _ => .strong

/-- The atom for a flavor of the space. -/
def Atom.ofFlavor : ModalFlavor → Atom
  | .epistemic => .epistemic
  | .deontic => .deontic
  | _ => .circumstantial

/-- Formulas of the Boolean Language of Thought. -/
inductive Formula
  | atom (a : Atom)
  | not (φ : Formula)
  | and (φ ψ : Formula)
  | or (φ ψ : Formula)

namespace Formula

/-- The number of atom occurrences, the length in literals of the complexity measure. -/
def atoms : Formula → ℕ
  | atom _ => 1
  | not φ => φ.atoms
  | and φ ψ | or φ ψ => φ.atoms + ψ.atoms

/-- The points of the space at which a formula holds. -/
def den : Formula → Meaning
  | atom a => a.den
  | not φ => space \ φ.den
  | and φ ψ => φ.den ∩ ψ.den
  | or φ ψ => φ.den ∪ ψ.den

theorem one_le_atoms (φ : Formula) : 1 ≤ φ.atoms := by
  induction φ <;> simp only [atoms] <;> omega

theorem den_subset : ∀ φ : Formula, φ.den ⊆ space
  | atom a => by cases a <;> exact product_subset_product (by decide) (by decide)
  | not _ => sdiff_subset
  | and φ _ => inter_subset_left.trans φ.den_subset
  | or φ ψ => union_subset φ.den_subset ψ.den_subset

/-- The conjunction of a force atom and a flavor atom denoting one point of the space. -/
def point (p : ForceFlavor) : Formula :=
  and (atom (.ofForce p.force)) (atom (.ofFlavor p.flavor))

theorem den_point {p : ForceFlavor} (hp : p ∈ space) : (point p).den = {p} := by
  revert hp
  rcases p with ⟨f, fl⟩
  cases f <;> cases fl <;> decide

theorem exists_den (m : Meaning) (hm : m ⊆ space) : ∃ φ : Formula, φ.den = m := by
  induction m using Finset.induction_on with
  | empty => exact ⟨and (atom .weak) (atom .strong), by decide⟩
  | insert p s _ ih =>
    obtain ⟨φ, hφ⟩ := ih ((subset_insert _ _).trans hm)
    exact ⟨or (point p) φ, by rw [den, hφ, den_point (hm (mem_insert_self _ _)), insert_eq]⟩

/-! #### Denotations by number of atoms

`dens n` is the set of denotations of formulas with exactly `n` atoms: the literals for one
atom, and for more the meets and joins of denotations of formulas whose atoms add up to `n`.
The recursion is fuelled so that it computes. -/

/-- The denotations of literals, an atom's points or their complement in the space. -/
def literals : Finset Meaning := univ.image Atom.den ∪ univ.image (space \ Atom.den ·)

/-- The meets and joins of a member of each set. -/
def combine (A B : Finset Meaning) : Finset Meaning :=
  (A ×ˢ B).image (λ x => x.1 ∩ x.2) ∪ (A ×ˢ B).image (λ x => x.1 ∪ x.2)

theorem inter_mem_combine {A B : Finset Meaning} {a b : Meaning} (ha : a ∈ A) (hb : b ∈ B) :
    a ∩ b ∈ combine A B :=
  mem_union_left _ (mem_image_of_mem _ (mk_mem_product ha hb))

theorem union_mem_combine {A B : Finset Meaning} {a b : Meaning} (ha : a ∈ A) (hb : b ∈ B) :
    a ∪ b ∈ combine A B :=
  mem_union_right _ (mem_image_of_mem _ (mk_mem_product ha hb))

theorem mem_combine {A B : Finset Meaning} {m : Meaning} :
    m ∈ combine A B ↔ ∃ a ∈ A, ∃ b ∈ B, m = a ∩ b ∨ m = a ∪ b := by
  simp only [combine, mem_union, mem_image, mem_product, Prod.exists]
  constructor
  · rintro (⟨a, b, ⟨ha, hb⟩, rfl⟩ | ⟨a, b, ⟨ha, hb⟩, rfl⟩)
    exacts [⟨a, ha, b, hb, Or.inl rfl⟩, ⟨a, ha, b, hb, Or.inr rfl⟩]
  · rintro ⟨a, ha, b, hb, rfl | rfl⟩
    exacts [Or.inl ⟨a, b, ⟨ha, hb⟩, rfl⟩, Or.inr ⟨a, b, ⟨ha, hb⟩, rfl⟩]

/-- `densAux fuel n` is `dens n` once `n ≤ fuel`. -/
def densAux : ℕ → ℕ → Finset Meaning
  | 0, _ => ∅
  | fuel + 1, n =>
    if n = 1 then literals
    else (range (n - 1)).biUnion λ i => combine (densAux fuel (i + 1)) (densAux fuel (n - 1 - i))

/-- The denotations of formulas with exactly `n` atoms. -/
def dens (n : ℕ) : Finset Meaning := densAux n n

theorem densAux_succ (f n : ℕ) :
    densAux (f + 1) n = if n = 1 then literals
      else (range (n - 1)).biUnion λ i => combine (densAux f (i + 1)) (densAux f (n - 1 - i)) :=
  rfl

theorem densAux_eq : ∀ {n f g : ℕ}, n ≤ f → n ≤ g → densAux f n = densAux g n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro f g hf hg
    rcases f with _ | f <;> rcases g with _ | g
    · rfl
    · obtain rfl : n = 0 := by omega
      simp [densAux]
    · obtain rfl : n = 0 := by omega
      simp [densAux]
    · rw [densAux_succ, densAux_succ]
      split_ifs
      · rfl
      · refine biUnion_congr rfl λ i hi => ?_
        rw [mem_range] at hi
        rw [ih (i + 1) (by omega) (f := f) (g := g) (by omega) (by omega),
          ih (n - 1 - i) (by omega) (f := f) (g := g) (by omega) (by omega)]

theorem dens_one : dens 1 = literals := rfl

theorem dens_eq_biUnion {n : ℕ} (hn : 2 ≤ n) :
    dens n = (range (n - 1)).biUnion λ i => combine (dens (i + 1)) (dens (n - 1 - i)) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [dens, densAux_succ, ite_eq_right (show k + 1 ≠ 1 by omega)]
  refine biUnion_congr rfl λ i hi => ?_
  rw [mem_range] at hi
  rw [densAux_eq (n := i + 1) (f := k) (g := i + 1) (by omega) le_rfl,
    densAux_eq (n := k + 1 - 1 - i) (f := k) (g := k + 1 - 1 - i) (by omega) le_rfl]
  rfl

theorem combine_dens_subset {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    combine (dens a) (dens b) ⊆ dens (a + b) := by
  rw [dens_eq_biUnion (n := a + b) (by omega)]
  have h : combine (dens a) (dens b) = combine (dens (a - 1 + 1)) (dens (a + b - 1 - (a - 1))) := by
    congr 2 <;> omega
  rw [h]
  exact subset_biUnion_of_mem (λ i => combine (dens (i + 1)) (dens (a + b - 1 - i)))
    (mem_range.2 (by omega))

theorem den_mem_dens : ∀ φ : Formula, φ.den ∈ dens φ.atoms ∧ space \ φ.den ∈ dens φ.atoms
  | atom a => ⟨mem_union_left _ (mem_image_of_mem _ (mem_univ a)),
      mem_union_right _ (mem_image_of_mem _ (mem_univ a))⟩
  | not φ => by
    obtain ⟨h₁, h₂⟩ := den_mem_dens φ
    exact ⟨h₂, by rw [den, Finset.sdiff_sdiff_eq_self φ.den_subset]; exact h₁⟩
  | and φ ψ => by
    obtain ⟨h₁, h₂⟩ := den_mem_dens φ
    obtain ⟨h₃, h₄⟩ := den_mem_dens ψ
    refine ⟨combine_dens_subset φ.one_le_atoms ψ.one_le_atoms (inter_mem_combine h₁ h₃), ?_⟩
    rw [den, sdiff_inter_distrib_right]
    exact combine_dens_subset φ.one_le_atoms ψ.one_le_atoms (union_mem_combine h₂ h₄)
  | or φ ψ => by
    obtain ⟨h₁, h₂⟩ := den_mem_dens φ
    obtain ⟨h₃, h₄⟩ := den_mem_dens ψ
    refine ⟨combine_dens_subset φ.one_le_atoms ψ.one_le_atoms (union_mem_combine h₁ h₃), ?_⟩
    rw [den, sdiff_union_distrib]
    exact combine_dens_subset φ.one_le_atoms ψ.one_le_atoms (inter_mem_combine h₂ h₄)

theorem exists_den_of_mem_dens : ∀ {n : ℕ} {m : Meaning}, m ∈ dens n →
    ∃ φ : Formula, φ.atoms = n ∧ φ.den = m := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro m hm
    rcases n with _ | _ | n
    · exact absurd hm (by simp [dens, densAux])
    · rw [dens_one, literals, mem_union, mem_image, mem_image] at hm
      rcases hm with ⟨a, -, rfl⟩ | ⟨a, -, rfl⟩
      exacts [⟨atom a, rfl, rfl⟩, ⟨not (atom a), rfl, rfl⟩]
    · rw [dens_eq_biUnion (by omega), mem_biUnion] at hm
      obtain ⟨i, hi, hm⟩ := hm
      rw [mem_range] at hi
      obtain ⟨a, ha, b, hb, rfl | rfl⟩ := mem_combine.1 hm
      · obtain ⟨φ, hφ, rfl⟩ := ih (i + 1) (by omega) ha
        obtain ⟨ψ, hψ, rfl⟩ := ih (n + 2 - 1 - i) (by omega) hb
        exact ⟨and φ ψ, by simp only [atoms]; omega, rfl⟩
      · obtain ⟨φ, hφ, rfl⟩ := ih (i + 1) (by omega) ha
        obtain ⟨ψ, hψ, rfl⟩ := ih (n + 2 - 1 - i) (by omega) hb
        exact ⟨or φ ψ, by simp only [atoms]; omega, rfl⟩

theorem exists_mem_dens {m : Meaning} (hm : m ⊆ space) : ∃ n, m ∈ dens n :=
  let ⟨φ, hφ⟩ := exists_den m hm
  ⟨_, hφ ▸ (den_mem_dens φ).1⟩

end Formula

/-- Equation (1) for one modal, the least number of atoms of a formula denoting it. -/
def complexity (m : Meaning) : ℕ :=
  if h : m ⊆ space then Nat.find (Formula.exists_mem_dens h) else 0

theorem complexity_eq_iff {m : Meaning} (hm : m ⊆ space) {n : ℕ} :
    complexity m = n ↔ m ∈ Formula.dens n ∧ ∀ k < n, m ∉ Formula.dens k := by
  rw [complexity, dite_eq_left hm, Nat.find_eq_iff]

theorem le_complexity_iff {m : Meaning} (hm : m ⊆ space) {n : ℕ} :
    n ≤ complexity m ↔ ∀ k < n, m ∉ Formula.dens k := by
  rw [complexity, dite_eq_left hm, Nat.le_find_iff]

theorem complexity_le {m : Meaning} (φ : Formula) (h : φ.den = m) : complexity m ≤ φ.atoms := by
  rw [complexity, dite_eq_left (h ▸ φ.den_subset)]
  exact Nat.find_le (h ▸ (Formula.den_mem_dens φ).1)

theorem exists_den_atoms {m : Meaning} (hm : m ⊆ space) :
    ∃ φ : Formula, φ.atoms = complexity m ∧ φ.den = m := by
  rw [complexity, dite_eq_left hm]
  exact Formula.exists_den_of_mem_dens (Nat.find_spec (Formula.exists_mem_dens hm))

theorem one_le_complexity {m : Meaning} (hm : m ⊆ space) : 1 ≤ complexity m := by
  obtain ⟨φ, hφ, -⟩ := exists_den_atoms hm
  exact hφ ▸ φ.one_le_atoms

/-- The hypothetical *mought* of Table 2, weak epistemic or strong deontic. -/
def mought : Meaning := {(.possibility, .epistemic), (.necessity, .deontic)}

/-- The hypothetical *notcirc* of Table 2, everything but circumstantial. -/
def notcirc : Meaning := forces ×ˢ {.epistemic, .deontic}

/-- Over the six-point space *may* is *w ∧ ¬c*, two atoms, where Table 2's four-flavor space
needs three. -/
theorem complexity_may : complexity may = 2 := by
  rw [may_eq, complexity_eq_iff (by decide)]; decide +kernel

theorem complexity_mought : complexity mought = 4 :=
  le_antisymm
    (complexity_le (.or (.and (.atom .weak) (.atom .epistemic))
      (.and (.atom .strong) (.atom .deontic))) (by decide))
    ((le_complexity_iff (by decide)).2 (by decide +kernel))

theorem complexity_notcirc : complexity notcirc = 1 := by
  rw [complexity_eq_iff (by decide)]; decide +kernel

/-- Complexity of a language, the sum over its modals, Equation (1). -/
def totalComplexity (L : Multiset Meaning) : ℕ := (L.map complexity).sum

/-- Table 2's language costs seven atoms over the experiment's space, one fewer than the
paper's eight over its illustration space. -/
theorem totalComplexity_table2 : totalComplexity {may, mought, notcirc} = 7 := by
  simp [totalComplexity, complexity_may, complexity_mought, complexity_notcirc]

theorem totalComplexity_replicate (k : ℕ) (m : Meaning) :
    totalComplexity (Multiset.replicate k m) = k * complexity m := by
  simp [totalComplexity, Multiset.map_replicate, Multiset.sum_replicate]

/-! ### Informativeness -/

instance : MeasurableSpace ModalForce := ⊤
instance : MeasurableSingletonClass ModalForce := ⟨fun _ => trivial⟩

instance : MeasurableSpace ModalFlavor := ⊤
instance : MeasurableSingletonClass ModalFlavor := ⟨fun _ => trivial⟩

instance : MeasurableSpace Meaning := ⊤
instance : MeasurableSingletonClass Meaning := ⟨fun _ => trivial⟩

/-- Equation (3), half credit for each axis of the intended point guessed right. -/
noncomputable def utility (p q : ForceFlavor) : ℝ≥0∞ :=
  (if p.force = q.force then 1 / 2 else 0) + (if p.flavor = q.flavor then 1 / 2 else 0)

/-- The expected utility when the speaker intends `p` and a literal listener guesses uniformly
among the points a modal expresses. -/
noncomputable def listen (m : Meaning) (p : ForceFlavor) : ℝ≥0∞ :=
  ∫⁻ q, utility p q ∂uniformOn ↑m

theorem listen_eq_measure (m : Meaning) (p : ForceFlavor) :
    listen m p =
      (uniformOn ↑m {q : ForceFlavor | p.force = q.force} +
        uniformOn ↑m {q : ForceFlavor | p.flavor = q.flavor}) / 2 := by
  have h (P : ForceFlavor → Prop) [DecidablePred P] :
      ∫⁻ q, (if P q then (1 / 2 : ℝ≥0∞) else 0) ∂uniformOn ↑m
        = uniformOn ↑m {q : ForceFlavor | P q} / 2 :=
    calc ∫⁻ q, (if P q then (1 / 2 : ℝ≥0∞) else 0) ∂uniformOn ↑m
        = ∫⁻ q, {q : ForceFlavor | P q}.indicator (fun _ => (1 / 2 : ℝ≥0∞)) q
            ∂uniformOn ↑m :=
          lintegral_congr fun q => by simp [Set.indicator_apply]
      _ = 1 / 2 * uniformOn ↑m {q : ForceFlavor | P q} :=
          lintegral_indicator_const .of_discrete _
      _ = uniformOn ↑m {q : ForceFlavor | P q} / 2 := by
          rw [one_div, ← ENNReal.div_eq_inv_mul]
  rw [listen]
  simp only [utility]
  rw [lintegral_add_left .of_discrete, h fun q => p.force = q.force,
    h fun q => p.flavor = q.flavor, ENNReal.div_add_div_same]

theorem listen_eq (m : Meaning) (p : ForceFlavor) :
    listen m p =
      (#(m.filter fun q : ForceFlavor => p.force = q.force) / #m +
        #(m.filter fun q : ForceFlavor => p.flavor = q.flavor) / #m) / 2 := by
  have h (P : ForceFlavor → Prop) [DecidablePred P] :
      uniformOn ↑m {q : ForceFlavor | P q} = #(m.filter P) / #m := by
    rw [show {q : ForceFlavor | P q} = ↑(Finset.univ.filter P) from by ext q; simp,
      uniformOn_apply_finset, show m ∩ Finset.univ.filter P = m.filter P from by ext q; simp]
  rw [listen_eq_measure, h, h]

theorem listen_singleton (p : ForceFlavor) : listen {p} p = 1 := by
  rw [listen_eq]
  norm_num [filter_singleton]
  exact ENNReal.div_self two_ne_zero ENNReal.ofNat_ne_top

theorem listen_product {F : Finset ModalForce} {Φ : Finset ModalFlavor} {p : ForceFlavor}
    (hF : p.force ∈ F) (hΦ : p.flavor ∈ Φ) :
    listen (F ×ˢ Φ) p = (1 / #F + 1 / #Φ) / 2 := by
  have hFc : (#F : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 (card_pos.2 ⟨_, hF⟩).ne'
  have hΦc : (#Φ : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 (card_pos.2 ⟨_, hΦ⟩).ne'
  have h1 : (F ×ˢ Φ).filter (fun q : ForceFlavor => p.force = q.force) = {p.force} ×ˢ Φ := by
    ext ⟨a, b⟩
    simp only [mem_filter, mem_product, mem_singleton]
    exact ⟨fun ⟨⟨_, hb⟩, ha⟩ => ⟨ha.symm, hb⟩, fun ⟨ha, hb⟩ => ⟨⟨ha ▸ hF, hb⟩, ha.symm⟩⟩
  have h2 : (F ×ˢ Φ).filter (fun q : ForceFlavor => p.flavor = q.flavor) = F ×ˢ {p.flavor} := by
    ext ⟨a, b⟩
    simp only [mem_filter, mem_product, mem_singleton]
    exact ⟨fun ⟨⟨ha, _⟩, hb⟩ => ⟨ha, hb.symm⟩, fun ⟨ha, hb⟩ => ⟨⟨ha, hb ▸ hΦ⟩, hb.symm⟩⟩
  have e1 := ENNReal.mul_div_mul_right 1 (#F : ℝ≥0∞) hΦc (ENNReal.natCast_ne_top #Φ)
  have e2 := ENNReal.mul_div_mul_left 1 (#Φ : ℝ≥0∞) hFc (ENNReal.natCast_ne_top #F)
  rw [one_mul] at e1
  rw [mul_one] at e2
  rw [listen_eq, h1, h2, card_product, card_product, card_product, card_singleton,
    card_singleton, one_mul, mul_one]
  push_cast
  rw [e1, e2]

/-- Table 2's *may* and *mought* have two points each; the IFF one is the more informative,
sharing an axis with any guess. -/
theorem listen_may_mought :
    listen may (.possibility, .epistemic) = 3 / 4 ∧
      listen mought (.possibility, .epistemic) = 1 / 2 := by
  constructor
  · rw [may_eq, listen_eq]
    norm_num [filter_insert, filter_singleton, ForceFlavor.force, ForceFlavor.flavor]
    rw [← one_div, ENNReal.div_add_div_same, show ((2 : ℝ≥0∞) + 1) = 3 from by norm_num,
      div_eq_mul_inv, div_eq_mul_inv, mul_assoc,
      ← ENNReal.mul_inv (by norm_num) (by norm_num),
      show ((2 : ℝ≥0∞) * 2) = 4 from by norm_num, ← div_eq_mul_inv]
  · rw [listen_eq]
    norm_num [mought, filter_insert, filter_singleton, ForceFlavor.force, ForceFlavor.flavor]
    rw [ENNReal.inv_two_add_inv_two, one_div]

/-- The modals of a language a literal speaker chooses among to express `p`. -/
def speakers (L : Multiset Meaning) (p : ForceFlavor) : Multiset Meaning := L.filter (p ∈ ·)

/-- The literal speaker's choice among the modals of `L` expressing `p`, uniform over the
multiset so that synonyms keep their multiplicity. -/
noncomputable def speak (L : Multiset Meaning) (p : ForceFlavor) : Measure Meaning :=
  (Multiset.card (speakers L p) : ℝ≥0∞)⁻¹ • ((speakers L p).map Measure.dirac).sum

/-- Equation (2), the expected utility of literal communication under a communicative need
distribution. -/
noncomputable def informativeness (need : Measure ForceFlavor) (L : Multiset Meaning) : ℝ≥0∞ :=
  ∫⁻ p, ∫⁻ m, listen m p ∂speak L p ∂need

/-- Communicative cost, the inverse of informativeness. -/
noncomputable def cost (need : Measure ForceFlavor) (L : Multiset Meaning) : ℝ≥0∞ :=
  1 - informativeness need L

/-- Table 5, the communicative need distribution estimated from the corpus. -/
noncomputable def needTable5 : Measure ForceFlavor :=
  (139 / 1000 : ℝ≥0∞) • Measure.dirac (.possibility, .epistemic) +
    (42 / 1000 : ℝ≥0∞) • Measure.dirac (.possibility, .deontic) +
    (143 / 1000 : ℝ≥0∞) • Measure.dirac (.possibility, .circumstantial) +
    (104 / 1000 : ℝ≥0∞) • Measure.dirac (.necessity, .epistemic) +
    (254 / 1000 : ℝ≥0∞) • Measure.dirac (.necessity, .deontic) +
    (318 / 1000 : ℝ≥0∞) • Measure.dirac (.necessity, .circumstantial)

/-- The corpus need distribution sums to one. -/
instance : IsProbabilityMeasure needTable5 := by
  constructor
  simp only [needTable5, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul,
    mul_one]
  rw [ENNReal.div_add_div_same, ENNReal.div_add_div_same, ENNReal.div_add_div_same,
    ENNReal.div_add_div_same, ENNReal.div_add_div_same,
    show (139 + 42 + 143 + 104 + 254 + 318 : ℝ≥0∞) = 1000 from by norm_num,
    ENNReal.div_self (by norm_num) (by norm_num)]

theorem speak_of_speakers_eq_zero {L : Multiset Meaning} {p : ForceFlavor}
    (h : speakers L p = 0) : speak L p = 0 := by
  rw [speak, h]
  simp

/-- A language with a modal for each point of the space. -/
def singletons : Multiset Meaning := space.val.map ({·})

/-- The language of one modal expressing every point. -/
def whole : Multiset Meaning := {space}

theorem speakers_singletons {p : ForceFlavor} (hp : p ∈ space) :
    speakers singletons p = {{p}} := by
  rw [speakers, singletons, Multiset.filter_map]
  simp only [Function.comp_def, mem_singleton]
  rw [Multiset.filter_eq, Multiset.count_eq_one_of_mem space.nodup hp, Multiset.replicate_one,
    Multiset.map_singleton]

theorem speakers_singletons_of_notMem {p : ForceFlavor} (hp : p ∉ space) :
    speakers singletons p = 0 :=
  Multiset.filter_eq_nil.2 fun m hm => by
    obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.1 hm
    exact fun h => hp (mem_singleton.1 h ▸ hq)

theorem speak_singletons {p : ForceFlavor} (hp : p ∈ space) :
    speak singletons p = Measure.dirac {p} := by
  rw [speak, speakers_singletons hp]
  simp

theorem informativeness_singletons (need : Measure ForceFlavor) :
    informativeness need singletons = need ↑space := by
  rw [informativeness, ← lintegral_indicator_one .of_discrete]
  refine lintegral_congr fun p => ?_
  by_cases hp : p ∈ space
  · rw [speak_singletons hp, lintegral_dirac, listen_singleton,
      Set.indicator_of_mem (mem_coe.2 hp), Pi.one_apply]
  · rw [speak_of_speakers_eq_zero (speakers_singletons_of_notMem hp), lintegral_zero_measure,
      Set.indicator_of_notMem fun h => hp (mem_coe.1 h)]

theorem speakers_whole {p : ForceFlavor} (hp : p ∈ space) : speakers whole p = {space} := by
  rw [speakers, whole, Multiset.filter_singleton, ite_eq_left hp]

theorem speakers_whole_of_notMem {p : ForceFlavor} (hp : p ∉ space) : speakers whole p = 0 := by
  rw [speakers, whole, Multiset.filter_singleton, ite_eq_right hp]
  rfl

theorem informativeness_whole (need : Measure ForceFlavor) :
    informativeness need whole = 5 / 12 * need ↑space := by
  rw [informativeness, ← lintegral_indicator_const (MeasurableSet.of_discrete) (5 / 12)]
  refine lintegral_congr fun p => ?_
  by_cases hp : p ∈ space
  · have hs : speak whole p = Measure.dirac space := by
      rw [speak, speakers_whole hp]
      simp
    obtain ⟨h1, h2⟩ := mem_product.1 hp
    rw [hs, lintegral_dirac, show listen space p = 5 / 12 from ?_,
      Set.indicator_of_mem (mem_coe.2 hp)]
    rw [space, listen_product h1 h2,
      show #forces = 2 from rfl, show #flavors = 3 from rfl,
      show (1 : ℝ≥0∞) / (2 : ℕ) = 3 / 6 from by
        rw [Nat.cast_ofNat, ENNReal.div_eq_div_iff (by norm_num) (by norm_num) (by norm_num)
          (by norm_num)]
        norm_num,
      show (1 : ℝ≥0∞) / (3 : ℕ) = 2 / 6 from by
        rw [Nat.cast_ofNat, ENNReal.div_eq_div_iff (by norm_num) (by norm_num) (by norm_num)
          (by norm_num)]
        norm_num,
      ENNReal.div_add_div_same, show ((3 : ℝ≥0∞) + 2) = 5 from by norm_num,
      div_eq_mul_inv, div_eq_mul_inv, mul_assoc,
      ← ENNReal.mul_inv (by norm_num) (by norm_num),
      show ((6 : ℝ≥0∞) * 2) = 12 from by norm_num, ← div_eq_mul_inv]
  · rw [speak_of_speakers_eq_zero (speakers_whole_of_notMem hp), lintegral_zero_measure,
      Set.indicator_of_notMem fun h => hp (mem_coe.1 h)]

/-! ### Synonymy and dominance -/

/-- The complexity and the communicative cost of a language. One language dominates another when
its pair is smaller in the product order, so the Pareto-optimal languages of a pool are those with
`MinimalFor (· ∈ pool) (costPair need)`. -/
noncomputable def costPair (need : Measure ForceFlavor) (L : Multiset Meaning) : ℕ × ℝ≥0∞ :=
  (totalComplexity L, cost need L)

theorem speakers_replicate (k : ℕ) (m : Meaning) (p : ForceFlavor) :
    speakers (Multiset.replicate k m) p = if p ∈ m then Multiset.replicate k m else 0 := by
  split_ifs with hp
  · exact Multiset.filter_eq_self.2 fun a ha => Multiset.eq_of_mem_replicate ha ▸ hp
  · exact Multiset.filter_eq_nil.2 fun a ha => Multiset.eq_of_mem_replicate ha ▸ hp

theorem speak_replicate {k : ℕ} (hk : k ≠ 0) (m : Meaning) (p : ForceFlavor) :
    speak (Multiset.replicate k m) p = speak {m} p := by
  rw [speak, speak, ← Multiset.replicate_one m, speakers_replicate, speakers_replicate,
    Multiset.replicate_one]
  split_ifs with hp
  · simp only [Multiset.card_replicate, Multiset.map_replicate, Multiset.sum_replicate,
      Multiset.card_singleton, Multiset.map_singleton, Multiset.sum_singleton, Nat.cast_one,
      inv_one, one_smul]
    rw [← Nat.cast_smul_eq_nsmul ℝ≥0∞, smul_smul,
      ENNReal.inv_mul_cancel (Nat.cast_ne_zero.2 hk) (ENNReal.natCast_ne_top k), one_smul]
  · simp

theorem informativeness_replicate (need : Measure ForceFlavor) {k : ℕ} (hk : k ≠ 0)
    (m : Meaning) :
    informativeness need (Multiset.replicate k m) = informativeness need {m} :=
  lintegral_congr fun p => by rw [speak_replicate hk]

theorem costPair_lt_replicate (need : Measure ForceFlavor) {m : Meaning} (hm : m ⊆ space)
    {k : ℕ} (hk : 2 ≤ k) : costPair need {m} < costPair need (Multiset.replicate k m) := by
  have h1 := one_le_complexity hm
  have hc : totalComplexity {m} = complexity m := by simp [totalComplexity]
  have hcost : cost need {m} = cost need (Multiset.replicate k m) := by
    rw [cost, cost, informativeness_replicate need (by omega)]
  refine Prod.mk_lt_mk_of_lt_of_le ?_ hcost.le
  rw [hc, totalComplexity_replicate]
  nlinarith

theorem not_minimalFor_replicate (need : Measure ForceFlavor)
    {pool : Set (Multiset Meaning)} {m : Meaning} (hm : m ⊆ space) (hpool : {m} ∈ pool)
    {k : ℕ} (hk : 2 ≤ k) : ¬ MinimalFor (· ∈ pool) (costPair need) (Multiset.replicate k m) :=
  fun h => h.not_lt hpool (costPair_lt_replicate need hm hk)

/-! ### The universals and naturalness -/

/-- Naturalness, the fraction of an inventory satisfying the IFF universal. -/
noncomputable def naturalness (L : List ModalItem) : ℝ≥0∞ :=
  (L.countP (ForceFlavorIndependent ·.meaning) : ℝ≥0∞) / L.length

theorem washo_not_singleAxis_forceFlavorIndependent :
    ¬ SingleAxis Washo.modalEq.meaning ∧
      ForceFlavorIndependent Washo.modalEq.meaning := by
  decide

theorem ivek_not_singleAxis : ¬ SingleAxis MocnikAbramovitz2019.attested :=
  MocnikAbramovitz2019.not_singleAxis_attested

theorem not_forceFlavorIndependent_diagonal :
    ¬ ForceFlavorIndependent
      ({(.necessity, .epistemic), (.possibility, .circumstantial)} : Meaning) := by
  decide

theorem naturalness_greek : naturalness Greek.StandardModern.modals = 1 / 3 := by
  rw [naturalness,
    show Greek.StandardModern.modals.countP (ForceFlavorIndependent ·.meaning) = 1 from by
      decide,
    show Greek.StandardModern.modals.length = 3 from rfl]
  norm_num

end ImelGuoSteinertThrelkeld2026
