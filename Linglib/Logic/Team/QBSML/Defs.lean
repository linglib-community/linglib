module

public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Fintype.Basic
public import Linglib.Logic.Assignment
public import Linglib.Logic.Modal.FirstOrder.Semantics
public import Linglib.Core.ModelTheory.LanguageMap
public import Linglib.Logic.Team.Operations
public import Linglib.Logic.Team.Kripke

/-!
# Quantified bilateral state-based modal logic (QBSML)

QBSML is the first-order extension of BSML. A formula is supported or anti-supported at a
*state*, a finite set of *indices* `⟨w, g⟩` pairing a world with a partial assignment. An index
has modal successors `R(wᵢ)[gᵢ]` and `x`-variants `i[x/d]`. The modalities are BSML's over the
successors, and the quantifiers are the box and the lax diamond of modal inclusion logic over the
variants. Disjunction splits states, and the non-emptiness atom `NE` is the only source of
non-classical behaviour.

## Main definitions

* `Index`, `Index.update`: indices `⟨w, g⟩` and their updates `i[x/d]`.
* `Index.successors`, `Index.variants`: the modal successors and the `x`-variants of an index.
* `State.worldProj`, `State.modalLift`: the world projection `s↓` and the pairing `X[g]`.
* `State.extendUniversal`, `State.extendFunctional`: the extensions `s[x]` and `s[x/h]`.
* `Formula`, `Formula.nec`, `Formula.NEFree`: formulas, the derived `□`, the `NE`-free fragment.
* `Model`, `Model.ofMonadic`: models over the monadic signature with constants.
* `eval`, `support`, `antiSupport`: bilateral evaluation.

## Main statements

* `support_poss_iff`, `support_exi_iff`: the paper's clauses for `◇` and `∃`.

## Implementation notes

* The paper takes `□` primitive and derives `◇`; we invert this, so `eval`'s `poss` clauses are
  the paper's derived `◇`-clauses. Predicates are monadic, as in all of the paper's examples.
* The paper's existential clause is the lax diamond over the variants (`support_exi_iff`), the
  lax quantifier of the paper's fn. 10; the universal clause `s[x] ⊨ φ` is the box over them.
* The paper's requirement that the indices of a state share an assignment domain is not
  enforced; the state operations preserve it.

## References

* [aloni-vanormondt-2023] Aloni and van Ormondt, Modified Numerals and Split Disjunction: The
  First-Order Case
* [aloni-2022] Aloni, Logic and Conversation: The Case of Free Choice
* [anttila-haggblom-yang-2025] Anttila, Häggblom and Yang, Axiomatizing modal inclusion logic
  and its variants
* [yan-2023] Yan, Monotonicity in Intensional Contexts: Weakening and Pragmatic Effects under
  Modals and Attitudes
-/

@[expose] public section

namespace QBSML

open FirstOrder

variable {W Var Domain : Type*}

/-! ### Indices -/

/-- An index `⟨w, g⟩` pairs a world with a partial assignment ([aloni-vanormondt-2023]
    Definition 4.2). -/
abbrev Index (W Var Domain : Type*) := W × PartialAssign Var Domain

/-- The world component of an index. -/
abbrev Index.world (i : Index W Var Domain) : W := i.1

/-- The assignment component of an index. -/
abbrev Index.assign (i : Index W Var Domain) : PartialAssign Var Domain := i.2

section Update

variable [DecidableEq Var]

/-- The update `i[x/d] = ⟨wᵢ, gᵢ[x/d]⟩` of an index ([aloni-vanormondt-2023] Definitions 4.3
    and 4.4). -/
def Index.update (i : Index W Var Domain) (x : Var) (d : Domain) : Index W Var Domain :=
  (i.world, i.assign.update x d)

@[simp] theorem Index.world_update (i : Index W Var Domain) (x : Var) (d : Domain) :
    (i.update x d).world = i.world := rfl

@[simp] theorem Index.assign_update (i : Index W Var Domain) (x : Var) (d : Domain) :
    (i.update x d).assign = i.assign.update x d := rfl

end Update

/-! ### World projection and modal pairing -/

section WorldProj

variable [DecidableEq W] {s : Finset (Index W Var Domain)}

/-- The world projection `s↓ = {w | ⟨w, g⟩ ∈ s}` of a state ([aloni-vanormondt-2023]
    Definition 4.10). -/
def State.worldProj (s : Finset (Index W Var Domain)) : Finset W :=
  s.image Index.world

@[simp] theorem State.mem_worldProj {w : W} : w ∈ State.worldProj s ↔ ∃ i ∈ s, i.world = w :=
  Finset.mem_image

theorem State.worldProj_mono {t : Finset (Index W Var Domain)} (h : s ⊆ t) :
    State.worldProj s ⊆ State.worldProj t :=
  Finset.image_subset_image h

theorem State.worldProj_nonempty (h : s.Nonempty) : (State.worldProj s).Nonempty :=
  h.image _

end WorldProj

section ModalLift

variable [DecidableEq W] [Fintype Var] [DecidableEq Domain]

/-- The pairing `X[g] = {⟨w, g⟩ | w ∈ X}` of a set of worlds with one assignment
    ([aloni-vanormondt-2023] Definition 4.9). -/
def State.modalLift (X : Finset W) (g : PartialAssign Var Domain) :
    Finset (Index W Var Domain) :=
  X.image fun v ↦ (v, g)

variable {s : Finset (Index W Var Domain)} {X : Finset W} {g : PartialAssign Var Domain}

@[simp] theorem State.mem_modalLift {i : Index W Var Domain} :
    i ∈ State.modalLift X g ↔ i.world ∈ X ∧ i.assign = g where
  mp h := by
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp h
    exact ⟨hv, rfl⟩
  mpr := by
    rintro ⟨h, rfl⟩
    exact Finset.mem_image.mpr ⟨i.world, h, rfl⟩

@[simp] theorem State.modalLift_singleton (w : W) (g : PartialAssign Var Domain) :
    State.modalLift {w} g = {(w, g)} :=
  Finset.image_singleton ..

theorem State.modalLift_mono {Y : Finset W} (h : X ⊆ Y) :
    State.modalLift X g ⊆ State.modalLift Y g :=
  Finset.image_subset_image h

theorem State.worldProj_subset_of_subset_modalLift (h : s ⊆ State.modalLift X g) :
    State.worldProj s ⊆ X := fun _ hw ↦ by
  obtain ⟨i, hi, rfl⟩ := State.mem_worldProj.mp hw
  exact (State.mem_modalLift.mp (h hi)).1

theorem State.modalLift_worldProj_of_subset (h : s ⊆ State.modalLift X g) :
    State.modalLift (State.worldProj s) g = s := by
  ext i
  simp only [State.mem_modalLift, State.mem_worldProj]
  constructor
  · rintro ⟨⟨j, hjs, hjw⟩, hig⟩
    obtain rfl : i = j := Prod.ext hjw.symm (hig.trans (State.mem_modalLift.mp (h hjs)).2.symm)
    exact hjs
  · exact fun his ↦ ⟨⟨i, his, rfl⟩, (State.mem_modalLift.mp (h his)).2⟩

/-- The modal successors `R(wᵢ)[gᵢ]` of an index: the worlds its world accesses, paired with its
    assignment ([aloni-vanormondt-2023] Definition 4.9). -/
def Index.successors (R : W → Finset W) (i : Index W Var Domain) : Finset (Index W Var Domain) :=
  State.modalLift (R i.world) i.assign

@[simp] theorem Index.mem_successors {R : W → Finset W} {i j : Index W Var Domain} :
    j ∈ i.successors R ↔ j.world ∈ R i.world ∧ j.assign = i.assign :=
  State.mem_modalLift

end ModalLift

/-! ### Variants and state extensions -/

section Variants

variable [DecidableEq W] [DecidableEq Var] [Fintype Var] [DecidableEq Domain]

/-- The `x`-variants `{i[x/d] | d ∈ D}` of an index. -/
def Index.variants [Fintype Domain] (x : Var) (i : Index W Var Domain) :
    Finset (Index W Var Domain) :=
  Finset.univ.image (i.update x)

@[simp] theorem Index.mem_variants [Fintype Domain] {x : Var} {i j : Index W Var Domain} :
    j ∈ i.variants x ↔ ∃ d, i.update x d = j := by
  simp [Index.variants]

/-- The functional extension `s[x/h] = {i[x/d] | i ∈ s, d ∈ h(i)}` ([aloni-vanormondt-2023]
    Definition 4.7). -/
def State.extendFunctional (s : Finset (Index W Var Domain)) (x : Var)
    (h : Index W Var Domain → Finset Domain) : Finset (Index W Var Domain) :=
  s.biUnion fun i ↦ (h i).image (i.update x)

/-- The universal extension `s[x] = {i[x/d] | i ∈ s, d ∈ D}` ([aloni-vanormondt-2023]
    Definition 4.6), the union of the `x`-variants of the indices of `s`. -/
def State.extendUniversal [Fintype Domain] (s : Finset (Index W Var Domain)) (x : Var) :
    Finset (Index W Var Domain) :=
  s.biUnion (Index.variants x)

variable {s : Finset (Index W Var Domain)} {x : Var} {j : Index W Var Domain}

@[simp] theorem State.mem_extendFunctional {h : Index W Var Domain → Finset Domain} :
    j ∈ State.extendFunctional s x h ↔ ∃ i ∈ s, ∃ d ∈ h i, i.update x d = j := by
  simp [State.extendFunctional]

@[simp] theorem State.mem_extendUniversal [Fintype Domain] :
    j ∈ State.extendUniversal s x ↔ ∃ i ∈ s, ∃ d, i.update x d = j := by
  simp [State.extendUniversal]

/-- A state is in the lax diamond of a property over the `x`-variants iff one of its functional
    `x`-extensions is in it. -/
theorem State.mem_possLax_variants_iff [Fintype Domain]
    {P : Team.TeamProperty (Index W Var Domain)} :
    s ∈ Team.possLax (Index.variants x) P ↔
      ∃ h : Index W Var Domain → Finset Domain,
        (∀ i ∈ s, (h i).Nonempty) ∧ State.extendFunctional s x h ∈ P where
  mp := fun ⟨S, hS, hcov, hSP⟩ ↦ by
    refine ⟨fun i ↦ Finset.univ.filter fun d ↦ i.update x d ∈ S, fun i hi ↦ ?_, ?_⟩
    · obtain ⟨_, hjS, hj⟩ := hcov i hi
      obtain ⟨d, rfl⟩ := Index.mem_variants.mp hj
      exact ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_univ d, hjS⟩⟩
    · convert hSP using 1
      ext j
      simp only [State.mem_extendFunctional, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨fun ⟨_, _, _, hd, hj⟩ ↦ hj ▸ hd, fun hj ↦ ?_⟩
      obtain ⟨i, hi, hji⟩ := Finset.mem_biUnion.mp (hS hj)
      obtain ⟨d, rfl⟩ := Index.mem_variants.mp hji
      exact ⟨i, hi, d, hj, rfl⟩
  mpr := fun ⟨h, hne, hP⟩ ↦ by
    refine ⟨State.extendFunctional s x h, fun j hj ↦ ?_, fun i hi ↦ ?_, hP⟩
    · obtain ⟨i, hi, d, -, rfl⟩ := State.mem_extendFunctional.mp hj
      exact Finset.mem_biUnion.mpr ⟨i, hi, Index.mem_variants.mpr ⟨d, rfl⟩⟩
    · obtain ⟨d, hd⟩ := hne i hi
      exact ⟨i.update x d, State.mem_extendFunctional.mpr ⟨i, hi, d, hd, rfl⟩,
        Index.mem_variants.mpr ⟨d, rfl⟩⟩

end Variants

/-! ### The formula language -/

variable {Const Pred : Type*}

/-- The formulas of QBSML ([aloni-vanormondt-2023] Definition 4.1) over variables `Var`,
    individual constants `Const` and monadic predicates `Pred`. The terms `t := c | x` appear as
    the two atom constructors, and `□` is the abbreviation `Formula.nec`. -/
inductive Formula (Var : Type*) (Const : Type*) (Pred : Type*) where
  /-- A predicate applied to a variable. -/
  | pred : Pred → Var → Formula Var Const Pred
  /-- A predicate applied to an individual constant. -/
  | predc : Pred → Const → Formula Var Const Pred
  /-- The non-emptiness atom. -/
  | ne : Formula Var Const Pred
  /-- Negation, which swaps support and anti-support. -/
  | neg : Formula Var Const Pred → Formula Var Const Pred
  /-- Conjunction. -/
  | conj : Formula Var Const Pred → Formula Var Const Pred → Formula Var Const Pred
  /-- Split disjunction. -/
  | disj : Formula Var Const Pred → Formula Var Const Pred → Formula Var Const Pred
  /-- The possibility modality. -/
  | poss : Formula Var Const Pred → Formula Var Const Pred
  /-- The existential quantifier. -/
  | exi : Var → Formula Var Const Pred → Formula Var Const Pred
  /-- The universal quantifier. -/
  | univ : Var → Formula Var Const Pred → Formula Var Const Pred
  deriving Repr

/-- Necessity `□φ` abbreviates `¬◇¬φ`. -/
def Formula.nec (φ : Formula Var Const Pred) : Formula Var Const Pred :=
  .neg (.poss (.neg φ))

/-- The `NE`-free fragment, on which QBSML is classical first-order modal logic
    ([aloni-vanormondt-2023] Proposition 4.1). -/
inductive Formula.NEFree : Formula Var Const Pred → Prop
  | pred (P : Pred) (x : Var) : NEFree (.pred P x)
  | predc (P : Pred) (c : Const) : NEFree (.predc P c)
  | neg {φ : Formula Var Const Pred} : NEFree φ → NEFree (.neg φ)
  | conj {φ ψ : Formula Var Const Pred} : NEFree φ → NEFree ψ → NEFree (.conj φ ψ)
  | disj {φ ψ : Formula Var Const Pred} : NEFree φ → NEFree ψ → NEFree (.disj φ ψ)
  | poss {φ : Formula Var Const Pred} : NEFree φ → NEFree (.poss φ)
  | exi (x : Var) {φ : Formula Var Const Pred} : NEFree φ → NEFree (.exi x φ)
  | univ (x : Var) {φ : Formula Var Const Pred} : NEFree φ → NEFree (.univ x φ)

/-! ### Atom substitution -/

/-- Substitute a formula for each atom, commuting with the connectives and quantifiers and fixing
    `NE`; [yan-2023]'s reinterpretation function is an instance. -/
def Formula.mapAtoms (fp : Pred → Var → Formula Var Const Pred)
    (fc : Pred → Const → Formula Var Const Pred) :
    Formula Var Const Pred → Formula Var Const Pred
  | .pred P x => fp P x
  | .predc P c => fc P c
  | .ne => .ne
  | .neg φ => .neg (φ.mapAtoms fp fc)
  | .conj φ ψ => .conj (φ.mapAtoms fp fc) (ψ.mapAtoms fp fc)
  | .disj φ ψ => .disj (φ.mapAtoms fp fc) (ψ.mapAtoms fp fc)
  | .poss φ => .poss (φ.mapAtoms fp fc)
  | .exi x φ => .exi x (φ.mapAtoms fp fc)
  | .univ x φ => .univ x (φ.mapAtoms fp fc)

theorem Formula.NEFree.mapAtoms {fp : Pred → Var → Formula Var Const Pred}
    {fc : Pred → Const → Formula Var Const Pred} (hfp : ∀ P x, (fp P x).NEFree)
    (hfc : ∀ P c, (fc P c).NEFree) {φ : Formula Var Const Pred} (h : φ.NEFree) :
    (φ.mapAtoms fp fc).NEFree := by
  induction h with
  | pred P x => exact hfp P x
  | predc P c => exact hfc P c
  | neg _ ih => exact .neg ih
  | conj _ _ ih₁ ih₂ => exact .conj ih₁ ih₂
  | disj _ _ ih₁ ih₂ => exact .disj ih₁ ih₂
  | poss _ ih => exact .poss ih
  | exi x _ ih => exact .exi x ih
  | univ x _ ih => exact .univ x ih

/-! ### Models -/

/-- A QBSML model `⟨W, D, R, I⟩` ([aloni-vanormondt-2023] Definition 4.2) is a constant-domain
    first-order Kripke structure over the monadic signature with constants. -/
abbrev Model (W : Type*) (Domain : Type*) (Const : Type*) (Pred : Type*) :=
  FirstOrder.Language.ModalStructure ((Language.monadic Pred)[[Const]]) W Domain

/-- The unary relation symbol of the predicate `P`. -/
abbrev predSymb (P : Pred) : ((Language.monadic Pred)[[Const]]).Relations 1 :=
  Sum.inl P

/-- The QBSML model with accessibility `access`, constant interpretation `κ`, and valuation
    `V`. -/
def Model.ofMonadic {W Domain Const Pred : Type*} (access : W → Finset W)
    (κ : W → Const → Domain) (V : W → Pred → Domain → Prop) :
    Model W Domain Const Pred :=
  ⟨access, fun w =>
    letI := Language.monadic.structure (V w)
    letI := Language.constantsOn.structure (κ w)
    inferInstance⟩

@[simp] theorem predInterp_ofMonadic {W Domain Const Pred : Type*}
    (access : W → Finset W) (κ : W → Const → Domain)
    (V : W → Pred → Domain → Prop) (P : Pred) (w : W) (d : Domain) :
    (Model.ofMonadic access κ V).relInterp₁ (predSymb P) w d ↔ V w P d :=
  Iff.rfl

@[simp] theorem constInterp_ofMonadic {W Domain Const Pred : Type*}
    (access : W → Finset W) (κ : W → Const → Domain)
    (V : W → Pred → Domain → Prop) (c : Const) (w : W) :
    (Model.ofMonadic access κ V).constInterp ((Language.monadic Pred).con c) w = κ w c :=
  rfl

/-! ### Bilateral evaluation -/

section Evaluation

variable [DecidableEq W] [DecidableEq Var] [Fintype Var] [DecidableEq Domain] [Fintype Domain]

/-- Bilateral evaluation ([aloni-vanormondt-2023] Definition 4.9): `eval M true φ s` is support
    `M, s ⊨ φ` and `eval M false φ s` is anti-support `M, s ⫤ φ`. -/
def eval (M : Model W Domain Const Pred) :
    Bool → Formula Var Const Pred → Finset (Index W Var Domain) → Prop
  | true,  .pred P x, s =>
      s ∈ Team.flat fun i ↦ ∃ d : Domain, i.assign x = ↑d ∧ M.relInterp₁ (predSymb P) i.world d
  | false, .pred P x, s =>
      s ∈ Team.flat fun i ↦ ∃ d : Domain, i.assign x = ↑d ∧ ¬ M.relInterp₁ (predSymb P) i.world d
  | true,  .predc P c, s =>
      s ∈ Team.flat fun i ↦
        M.relInterp₁ (predSymb P) i.world (M.constInterp ((Language.monadic Pred).con c) i.world)
  | false, .predc P c, s =>
      s ∈ Team.flat fun i ↦
        ¬ M.relInterp₁ (predSymb P) i.world (M.constInterp ((Language.monadic Pred).con c) i.world)
  | true,  .ne, s => s ∈ Team.ne
  | false, .ne, s => s ∈ ({∅} : Team.TeamProperty (Index W Var Domain))
  | true,  .neg ψ, s => eval M false ψ s
  | false, .neg ψ, s => eval M true ψ s
  | true,  .conj φ ψ, s => eval M true φ s ∧ eval M true ψ s
  | false, .conj φ ψ, s => s ∈ Team.tensor {t | eval M false φ t} {t | eval M false ψ t}
  | true,  .disj φ ψ, s => s ∈ Team.tensor {t | eval M true φ t} {t | eval M true ψ t}
  | false, .disj φ ψ, s => eval M false φ s ∧ eval M false ψ s
  | true,  .poss ψ, s => s ∈ Team.poss (Index.successors M.access) {t | eval M true ψ t}
  | false, .poss ψ, s => s ∈ Team.nec (Index.successors M.access) {t | eval M false ψ t}
  | true,  .univ x ψ, s => s ∈ Team.necImage (Index.variants x) {t | eval M true ψ t}
  | false, .univ x ψ, s => s ∈ Team.possLax (Index.variants x) {t | eval M false ψ t}
  | true,  .exi x ψ, s => s ∈ Team.possLax (Index.variants x) {t | eval M true ψ t}
  | false, .exi x ψ, s => s ∈ Team.necImage (Index.variants x) {t | eval M false ψ t}

/-- Support: positive evaluation. -/
abbrev support (M : Model W Domain Const Pred) (φ : Formula Var Const Pred)
    (s : Finset (Index W Var Domain)) : Prop :=
  eval M true φ s

/-- Anti-support: negative evaluation. -/
abbrev antiSupport (M : Model W Domain Const Pred) (φ : Formula Var Const Pred)
    (s : Finset (Index W Var Domain)) : Prop :=
  eval M false φ s

@[simp] lemma support_neg (M : Model W Domain Const Pred) (φ : Formula Var Const Pred)
    (s : Finset (Index W Var Domain)) : support M (.neg φ) s ↔ antiSupport M φ s := Iff.rfl

@[simp] lemma antiSupport_neg (M : Model W Domain Const Pred) (φ : Formula Var Const Pred)
    (s : Finset (Index W Var Domain)) : antiSupport M (.neg φ) s ↔ support M φ s := Iff.rfl

variable {M : Model W Domain Const Pred} {φ : Formula Var Const Pred} {x : Var}
  {s : Finset (Index W Var Domain)}

theorem support_poss_iff : support M (.poss φ) s ↔
    ∀ i ∈ s, ∃ X ⊆ M.access i.world, X.Nonempty ∧ support M φ (State.modalLift X i.assign) :=
  forall₂_congr fun i _ ↦
    ⟨fun ⟨t, ht, hne, h⟩ ↦ ⟨State.worldProj t, State.worldProj_subset_of_subset_modalLift ht,
        State.worldProj_nonempty hne, (State.modalLift_worldProj_of_subset ht).symm ▸ h⟩,
      fun ⟨X, hX, hne, h⟩ ↦ ⟨State.modalLift X i.assign, State.modalLift_mono hX, hne.image _, h⟩⟩

theorem antiSupport_poss_iff : antiSupport M (.poss φ) s ↔
    ∀ i ∈ s, antiSupport M φ (State.modalLift (M.access i.world) i.assign) := Iff.rfl

theorem support_univ_iff : support M (.univ x φ) s ↔ support M φ (State.extendUniversal s x) :=
  Iff.rfl

theorem antiSupport_exi_iff :
    antiSupport M (.exi x φ) s ↔ antiSupport M φ (State.extendUniversal s x) := Iff.rfl

theorem support_exi_iff : support M (.exi x φ) s ↔ ∃ h : Index W Var Domain → Finset Domain,
    (∀ i ∈ s, (h i).Nonempty) ∧ support M φ (State.extendFunctional s x h) :=
  State.mem_possLax_variants_iff

theorem antiSupport_univ_iff : antiSupport M (.univ x φ) s ↔
    ∃ h : Index W Var Domain → Finset Domain,
      (∀ i ∈ s, (h i).Nonempty) ∧ antiSupport M φ (State.extendFunctional s x h) :=
  State.mem_possLax_variants_iff

end Evaluation

end QBSML
