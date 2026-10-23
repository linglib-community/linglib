/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.Conditionals.SelectionFunction
public import Linglib.Semantics.Conditionals.Restrictor
public import Linglib.Semantics.Modality.HistoricalAlternatives
public import Linglib.Core.Probability.UniformOn
public import Mathlib.Order.Hom.CompleteLattice
public import Mathlib.Tactic.DeriveFintype

/-!
# Cariani and Santorio 2018: *will* done better

Cariani and Santorio analyse *will* as a modal that selects rather than quantifies. Its modal
parameter is the set of historical alternatives of the context, *will A* is true at a world when
`A` holds at the world a Stalnaker selection function picks from the parameter, and an
*if*-clause restricts the parameter. Selection makes *will* a Boolean homomorphism, so it is
scopeless with respect to negation, and gives *will A* the credence of `A`, where a universal
analysis gives an open future credence 0. In their Sports Fan model the cap-conditional has
credence 1/3 or 2/3, never its conditional probability 1/2, until contents are taken to be sets
of pairs of a world and a selection function.

## Main definitions

* `will`, `willIf`: selectional *will*, and *if A, will B* over the restricted parameter.
* `Valid1`, `Valid2`: truth at every context and at every index.
* `content2D`: the content of a sentence as a set of pairs of a world and a selection function.

## Main results

* `will_compl`, `willIf_compl`: Negation Swap, unembedded and under an *if*-clause.
* `will_excluded_middle`, `willIf_excluded_middle`: excluded middle is valid₂.
* `valid1_materialImp_will`, `not_valid2_materialImp_will`: *will A* entails `A` at every
  context but not at every index.
* `will_eq_core`, `necessity_compl_eq_iff`: *will* is necessity along a selection, and a
  universal analysis commutes with negation only if it is one.
* `will_alternatives_eq`: the candidate worlds of a context give *will* one modal parameter.
* `will_inter_self`, `measure_will`: Transparency, so *will A* has the credence of `A`.
* `measure_necessity_eq_zero`: universal *will* gives an open future credence 0.
* `credence_willIf_wearsCap`, `no_unconditional_one_half`: the cap-conditional has credence 2/3
  or 1/3, and no proposition of the model has credence 1/2.
* `credence2D_willIf_wearsCap`: over pairs the cap-conditional has its conditional probability.

## Implementation notes

* A sentence is a map from a selection function and a modal parameter to a set of worlds, so an
  *if*-clause, rule (21), shifts the parameter.
* At an empty parameter `will` evaluates the junk selection; the paper restricts its conditional
  principles to antecedents compatible with the modal base (§7).
* Section and example numbers follow the accepted manuscript (Draft of November 2, 2015).

## References

* [F. Cariani and P. Santorio, *Will done Better: Selection Semantics, Future Credence, and
  Indeterminacy* (2018)][cariani-santorio-2018]
* [R. C. Stalnaker, *A Theory of Conditionals* (1968)][stalnaker-1968]
* [A. Kratzer, *The Notional Category of Modality* (1981)][kratzer-1981]
* [S. Kaufmann, *Conditional Truth and Future Reference* (2005)][kaufmann-2005-truth]
* [A. Hajek, *Probabilities of Conditionals — Revisited* (1989)][hajek-1989]
-/

@[expose] public section

namespace CarianiSantorio2018

open Conditional Modality HistoricalAlternatives MeasureTheory ProbabilityTheory

section General

variable {W : Type*} (s : SelectionFunction W) {f A B C : Set W} {w : W}

/-! ### Selectional *will*

The clause for *will* is (16) of §5.2, and its collapse at the context is (18). -/

/-- *Will* over the modal parameter `f` sends `A` to the worlds whose selection from `f` is an
`A`-world, the selectional modal along the constant relation to `f`. -/
def will (f : Set W) : CompleteLatticeHom (Set W) (Set W) :=
  s.modal (.ofSuccessors fun _ ↦ f)

@[simp] theorem mem_will : w ∈ will s f A ↔ s.sel w f ∈ A := Iff.rfl

/-- *Will* is necessity along the graph of selection from `f`, a modal that quantifies over a
single world (§5.2). -/
theorem will_eq_core : will s f A = (Function.graph fun w ↦ s.sel w f).core A :=
  SelectionFunction.modal_eq_core A

/-- *Will* commutes with negation, which is Negation Swap (§7). -/
theorem will_compl : will s f Aᶜ = (will s f A)ᶜ := map_compl' _ A

theorem mem_will_of_mem (hw : w ∈ f) : w ∈ will s f A ↔ w ∈ A := by
  rw [mem_will, s.centering w f hw]

/-- On the modal parameter *will A* and `A` hold at the same worlds, which is Transparency
(§8.1). -/
theorem will_inter_self : will s f A ∩ f = A ∩ f :=
  SelectionFunction.modal_inter_refl A

theorem will_eq_selectionConditional (hf : f.Nonempty) : will s f A = selectionConditional s f A :=
  (selectionConditional_eq_modal hf A).symm

/-! ### Validity -/

/-- A sentence is valid₂ when it is true at every index, every world under every selection
function and modal parameter. -/
def Valid2 (φ : SelectionFunction W → Set W → Set W) : Prop := ∀ s f, φ s f = Set.univ

/-- A sentence is valid₁ when it is true at every context, an index whose world lies in the modal
parameter. -/
def Valid1 (φ : SelectionFunction W → Set W → Set W) : Prop := ∀ s f, f ⊆ φ s f

theorem Valid2.valid1 {φ : SelectionFunction W → Set W → Set W} (h : Valid2 φ) : Valid1 φ :=
  fun s f ↦ (h s f).symm ▸ Set.subset_univ f

/-- Will Excluded Middle is valid₂ (§7). -/
theorem will_excluded_middle : Valid2 fun s f ↦ will s f A ∪ will s f Aᶜ := fun s _ ↦ by
  simp only [will_compl, Set.union_compl_self]

/-- Every context at which *will A* is true verifies `A`. -/
theorem valid1_materialImp_will : Valid1 fun s f ↦ materialImp (will s f A) A :=
  fun s _ _ hw ↦ (mem_will_of_mem s hw).1

/-! ### *If*-clauses

An *if*-clause restricts the modal parameter of *will* to the antecedent-worlds, by rule (21) of
§5.3.1. -/

/-- *If A, will B* is *will B* over the modal parameter restricted to the `A`-worlds. -/
def willIf (f A : Set W) : CompleteLatticeHom (Set W) (Set W) := will s (f ∩ A)

/-- *Will* commutes with negation under an *if*-clause, which is Negation Swap in conditionals (§7).
-/
theorem willIf_compl : willIf s f A Bᶜ = (willIf s f A B)ᶜ := will_compl s

/-- Conditional Excluded Middle for will-conditionals is valid₂ (§7). -/
theorem willIf_excluded_middle : Valid2 fun s f ↦ willIf s f A B ∪ willIf s f A Bᶜ :=
  fun s f ↦ will_excluded_middle s (f ∩ A)

/-- Under modal subordination, *If A, will B. Will C* is equivalent to *if A, will (B and C)* ((24)
of §5.3.1). -/
theorem willIf_inter : willIf s f A B ∩ willIf s f A C = willIf s f A (B ∩ C) :=
  (map_inf _ B C).symm

theorem willIf_eq_selectionConditional (h : (f ∩ A).Nonempty) :
    willIf s f A B = selectionConditional s (f ∩ A) B :=
  will_eq_selectionConditional s h

/-! ### Contexts

At a context the modal parameter of *will* is the set of historical alternatives of the
context's world at its time (§3, §5.1). -/

section Contexts

variable {T : Type*} [Preorder T] {F : Temporal.TWFrame W T} {t : T}

/-- At a context *will A* is true exactly when `A` is, the collapse (18). -/
theorem mem_will_alternatives_iff : w ∈ will s (F.alternatives (w, t)) A ↔ w ∈ A :=
  mem_will_of_mem s Temporal.TWFrame.mem_alternatives_self

/-- Every candidate world of a context has the same historical alternatives, so the content of *will
A* is fixed even when the context is indeterminate (§3). -/
theorem will_alternatives_eq {v : W} (hv : v ∈ F.alternatives (w, t)) :
    will s (F.alternatives (v, t)) = will s (F.alternatives (w, t)) := by
  rw [Temporal.TWFrame.alternatives_eq_of_mem hv]

end Contexts

/-! ### Cognitive role -/

/-- Under a credence concentrated on the modal parameter, the content of *will A* has the
credence of `A` (§8.1). -/
theorem measure_will [MeasurableSpace W] (μ : Measure W) (h : μ fᶜ = 0) :
    μ (will s f A) = μ A := by
  rw [← measure_inter_conull h, will_inter_self, measure_inter_conull h]

/-! ### Universal *will*

The modal analyses the paper argues against make *will* necessity over the best open worlds,
the `necessity f g` of [kratzer-1981] with the open worlds as modal base, such as the most likely
open worlds of [kaufmann-2005-truth]. They differ in the ordering source `g` (§2.4, (14)). -/

/-- A universal analysis commutes with negation for every prejacent iff it is truth at a selected
world (§2.2, §2.4). -/
theorem necessity_compl_eq_iff {f g : Background W} :
    (∀ p : W → Prop, necessity f g pᶜ = (necessity f g p)ᶜ) ↔
      ∃ σ : W → W, ∀ p : W → Prop, necessity f g p = p ∘ σ := by
  refine ⟨fun h ↦ ?_, fun ⟨σ, hσ⟩ p ↦ by rw [hσ, hσ]; rfl⟩
  obtain ⟨σ, hσ⟩ := ModalLogic.box_compl_eq_iff.1 h
  exact ⟨σ, fun p ↦ by rw [← ModalLogic.box_graph σ p, hσ]; rfl⟩

/-- If the best worlds include an `A`-world and a non-`A`-world, universal *will* verifies neither
*will A* nor *will not A* (§2.4). -/
theorem not_necessity_or_necessity_compl {f g : Background W} {v v' : W}
    (hv : v ∈ bestWorlds f g w) (hv' : v' ∈ bestWorlds f g w) (hA : v ∈ A) (hA' : v' ∉ A) :
    ¬ (necessity f g (· ∈ A) w ∨ necessity f g (· ∈ Aᶜ) w) := by
  rintro (h | h)
  exacts [hA' (h v' hv'), h v hv hA]

/-- A credence certain that the best worlds hold a non-`A`-world gives universal *will A*
credence 0, whatever the ordering source (§2.4). -/
theorem measure_necessity_eq_zero [MeasurableSpace W] (μ : Measure W) {f g : Background W}
    (h : ∀ᵐ w ∂μ, ¬ bestWorlds f g w ⊆ A) : μ {w | necessity f g (· ∈ A) w} = 0 :=
  measure_eq_zero_iff_ae_notMem.2 <| h.mono fun _ hw hn ↦ hw hn

/-! ### Two-dimensional content

Uncertainty about the selection function joins uncertainty about the world when contents are
sets of pairs of a world and a selection function (§8.2). -/

/-- The 2D content of a sentence at a modal parameter is the set of pairs of a world and a
selection function at which the sentence is true. -/
def content2D (φ : SelectionFunction W → Set W → Set W) (f : Set W) :
    Set (W × SelectionFunction W) :=
  {p | p.1 ∈ φ p.2 f}

@[simp] theorem mem_content2D {φ : SelectionFunction W → Set W → Set W}
    {p : W × SelectionFunction W} : p ∈ content2D φ f ↔ p.1 ∈ φ p.2 f :=
  Iff.rfl

end General

/-! ### The Sports Fan model -/

/-- The three worlds of the Sports Fan scenario (§2.3), in which Cynthia wears a Warriors cap, a
Giants cap, or no cap. -/
inductive W where
  | cw | cg | cn
  deriving DecidableEq, Repr, Fintype

/-- Cynthia's cap choice is the one matter of particular fact, dated tomorrow at time `1`, so two
worlds are historical alternatives up to a time when they agree on it or it is not yet dated. -/
def frame : Temporal.TWFrame W ℕ := .ofDatedFacts (fun _ ↦ 1) (· = ·)

@[simp] theorem alternatives_today (w : W) : frame.alternatives (w, 0) = Set.univ :=
  Set.eq_univ_of_forall fun _ _ h ↦ (Nat.not_succ_le_zero 0 h).elim

/-- The proposition that Cynthia wears a Warriors cap. -/
def warriorsCap : Set W := {.cw}

/-- The proposition that Cynthia wears some cap, Warriors or Giants. -/
def wearsCap : Set W := {.cw, .cg}

/-- *Cynthia will wear a Warriors cap* is true at the Warriors-cap context and false at the
Giants-cap context, so its truth value is indeterminate (§3, §6). -/
theorem will_warriorsCap_indeterminate (s : SelectionFunction W) :
    .cw ∈ will s (frame.alternatives (.cw, 0)) warriorsCap ∧
      .cg ∉ will s (frame.alternatives (.cg, 0)) warriorsCap := by
  rw [mem_will_alternatives_iff s, mem_will_alternatives_iff s]
  simp [warriorsCap]

/-- *Will A* does not valid₂-entail `A`. At the Warriors-cap world, with the no-cap world as the
only modal parameter, *Cynthia will wear no cap* is true and its prejacent false. -/
theorem not_valid2_materialImp_will :
    ¬ Valid2 fun s f ↦ materialImp (will s f {W.cn}) {W.cn} := fun h ↦ by
  obtain ⟨s, hs⟩ := SelectionFunction.exists_sel_eq (w := W.cw) (Set.mem_singleton W.cn) (by simp)
  have := Set.eq_univ_iff_forall.1 (h s {.cn}) .cw
  simp [mem_materialImp, hs] at this

instance : MeasurableSpace W := ⊤

instance : DiscreteMeasurableSpace W := ⟨fun _ ↦ trivial⟩

/-- The agent's credence is uniform, each cap choice getting 1/3. -/
noncomputable def cynthiaCredence : Measure W := uniformOn Set.univ

private theorem cynthiaCredence_real (S : Set W) : cynthiaCredence.real S = S.ncard / 3 := by
  rw [cynthiaCredence, uniformOn_univ_real_apply, show Fintype.card W = 3 from rfl,
    Nat.cast_ofNat]

/-- Whatever the selection function and the world of the context, *Cynthia will wear a Warriors
cap* has credence 1/3, that of its prejacent (§8.1). -/
theorem credence_will_warriorsCap (s : SelectionFunction W) (w : W) :
    cynthiaCredence.real (will s (frame.alternatives (w, 0)) warriorsCap) = 1 / 3 := by
  rw [measureReal_def, measure_will s cynthiaCredence (f := frame.alternatives (w, 0)) (by simp),
    ← measureReal_def, cynthiaCredence_real, warriorsCap, Set.ncard_singleton]
  norm_num

/-- The historical modal base, the background of the relation to today's historical
alternatives. -/
def histBase : Background W := .ofRel (.ofSuccessors fun w ↦ frame.alternatives (w, 0))

@[simp] theorem accessibleWorlds_histBase (w : W) : histBase.accessibleWorlds w = Set.univ := by
  simp [histBase]

/-- On the universal reading over the historical modal base, *Cynthia will wear a Warriors cap*
has credence 0 (§2.3). -/
theorem credence_necessity_warriorsCap :
    cynthiaCredence {w | necessity histBase ⊥ (· ∈ warriorsCap) w} = 0 :=
  measure_necessity_eq_zero _ <| .of_forall fun _ h ↦ by
    simpa [warriorsCap] using h (show W.cg ∈ bestWorlds histBase ⊥ _ by simp)

/-- On the universal reading, *Cynthia will wear a Warriors cap* and *Cynthia will not wear a
Warriors cap* are both false at every world (§2.4). -/
theorem not_necessity_warriorsCap_or_compl (w : W) :
    ¬ (necessity histBase ⊥ (· ∈ warriorsCap) w ∨ necessity histBase ⊥ (· ∈ warriorsCapᶜ) w) :=
  not_necessity_or_necessity_compl (v := .cw) (v' := .cg) (by simp) (by simp)
    (by simp [warriorsCap]) (by simp [warriorsCap])

theorem not_conditionalNecessity_wearsCap_or_compl (w : W) :
    ¬ (Restrictor.conditionalNecessity histBase ⊥ (· ∈ wearsCap) (· ∈ warriorsCap) w ∨
      Restrictor.conditionalNecessity histBase ⊥ (· ∈ wearsCap) (· ∈ warriorsCapᶜ) w) :=
  not_necessity_or_necessity_compl (v := .cw) (v' := .cg)
    (by simp [-Background.mem_accessibleWorlds, wearsCap])
    (by simp [-Background.mem_accessibleWorlds, wearsCap]) (by simp [warriorsCap])
    (by simp [warriorsCap])

/-! ### The cap-conditional

The cap-conditional is (31) of §8.2. -/

/-- *If Cynthia wears a cap, she will wear a Warriors cap* is true exactly at the Warriors-cap world
and at a no-cap world selecting it (footnote 32). -/
theorem mem_willIf_wearsCap_warriorsCap (s : SelectionFunction W) (w v : W) :
    v ∈ willIf s (frame.alternatives (w, 0)) wearsCap warriorsCap ↔
      v = .cw ∨ v = .cn ∧ s.sel .cn wearsCap = .cw := by
  rw [willIf, alternatives_today, Set.univ_inter]
  cases v
  · simp [s.centering _ _ (show W.cw ∈ wearsCap by simp [wearsCap]), warriorsCap]
  · simp [s.centering _ _ (show W.cg ∈ wearsCap by simp [wearsCap]), warriorsCap]
  · simp [warriorsCap]

/-- The content of the cap-conditional has credence 2/3 when the no-cap world selects the
Warriors-cap world and 1/3 otherwise (footnote 32). -/
theorem credence_willIf_wearsCap (s : SelectionFunction W) (w : W) :
    cynthiaCredence.real (willIf s (frame.alternatives (w, 0)) wearsCap warriorsCap) =
      if s.sel .cn wearsCap = .cw then 2 / 3 else 1 / 3 := by
  split_ifs with h
  · rw [show willIf s (frame.alternatives (w, 0)) wearsCap warriorsCap = {.cw, .cn} by
      ext; rw [mem_willIf_wearsCap_warriorsCap]; simp [h], cynthiaCredence_real,
      Set.ncard_pair (by decide)]
    norm_num
  · rw [show willIf s (frame.alternatives (w, 0)) wearsCap warriorsCap = {.cw} by
      ext; rw [mem_willIf_wearsCap_warriorsCap]; simp [h], cynthiaCredence_real,
      Set.ncard_singleton]
    norm_num

theorem cond_wearsCap_warriorsCap : cynthiaCredence[|wearsCap].real warriorsCap = 1 / 2 := by
  rw [cynthiaCredence, uniformOn_univ_cond, uniformOn_real_apply,
    show wearsCap ∩ warriorsCap = {.cw} by ext v; cases v <;> simp [wearsCap, warriorsCap],
    Set.ncard_singleton, wearsCap, Set.ncard_pair (by decide)]
  norm_num

/-- No proposition over the Sports Fan model has credence 1/2, since every credence is a multiple
of 1/3, so no reading of the cap-conditional has its conditional probability. It is an instance
of the point of [hajek-1989] that conditional probabilities outnumber unconditional ones. -/
theorem no_unconditional_one_half (S : Set W) : cynthiaCredence.real S ≠ 1 / 2 := by
  rw [cynthiaCredence_real]
  intro h
  have : S.ncard * 2 = 3 := by field_simp at h; exact_mod_cast h
  omega

/-! ### The two-dimensional cap-conditional

Which world the no-cap world selects for the cap antecedent is open, so the agent is uncertain
between two selection functions, `sw` selecting the Warriors-cap world and `sv` the Giants-cap
world (§8.2). -/

/-- A selection function selecting the cap world `v` for the no-cap world and the cap
antecedent. -/
noncomputable def candidate (v : W) (hv : v ∈ wearsCap) : SelectionFunction W :=
  (SelectionFunction.exists_sel_eq hv (show W.cn ∉ wearsCap by simp [wearsCap])).choose

theorem candidate_sel {v : W} (hv : v ∈ wearsCap) : (candidate v hv).sel .cn wearsCap = v :=
  (SelectionFunction.exists_sel_eq hv (show W.cn ∉ wearsCap by simp [wearsCap])).choose_spec

/-- The candidate selecting the Warriors-cap world. -/
noncomputable def sw : SelectionFunction W := candidate .cw (by simp [wearsCap])

/-- The candidate selecting the Giants-cap world. -/
noncomputable def sv : SelectionFunction W := candidate .cg (by simp [wearsCap])

theorem sw_ne_sv : sw ≠ sv := fun h ↦
  absurd (congrArg (·.sel .cn wearsCap) h) (by simp [sw, sv, candidate_sel])

/-- The six pairs of a world and a candidate selection function. -/
def pairs : Set (W × SelectionFunction W) := Set.univ ×ˢ {sw, sv}

instance : MeasurableSpace (SelectionFunction W) := ⊤

instance : DiscreteMeasurableSpace (SelectionFunction W) := ⟨fun _ ↦ trivial⟩

/-- The uniform credence over the six pairs gives the 2D content of the cap-conditional its
conditional probability 1/2 (§8.2). -/
theorem credence2D_willIf_wearsCap (w : W) :
    (uniformOn pairs).real
        (content2D (fun s f ↦ willIf s f wearsCap warriorsCap) (frame.alternatives (w, 0))) =
      cynthiaCredence[|wearsCap].real warriorsCap := by
  have hsel : sw.sel .cn wearsCap = .cw ∧ sv.sel .cn wearsCap = .cg :=
    ⟨candidate_sel _, candidate_sel _⟩
  have hinter :
      pairs ∩ content2D (fun s f ↦ willIf s f wearsCap warriorsCap) (frame.alternatives (w, 0)) =
      {(.cw, sw), (.cw, sv), (.cn, sw)} := by
    ext ⟨v, s⟩
    simp only [pairs, Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, true_and, mem_content2D,
      mem_willIf_wearsCap_warriorsCap, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
    constructor
    · rintro ⟨rfl | rfl, rfl | ⟨rfl, h⟩⟩ <;> simp_all
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp [hsel]
  rw [uniformOn_real_apply_of_finite (s := pairs)
      (Set.finite_univ.prod ((Set.finite_singleton sv).insert sw)),
    hinter, Set.ncard_insert_of_notMem (by simp [sw_ne_sv]), Set.ncard_insert_of_notMem (by simp),
    Set.ncard_singleton, pairs, Set.ncard_prod, Set.ncard_univ, Set.ncard_pair sw_ne_sv,
    cond_wearsCap_warriorsCap, Nat.card_eq_fintype_card, show Fintype.card W = 3 from rfl]
  norm_num

end CarianiSantorio2018
