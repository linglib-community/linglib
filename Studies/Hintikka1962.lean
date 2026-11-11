module

public import Linglib.Logic.Epistemic.Basic
public import Linglib.Data.Examples.Hintikka1962
public import Linglib.Discourse.Role
public import Mathlib.Logic.Relation

/-!
# Hintikka (1962): Knowledge and Belief

This file formalizes Hintikka's reading of consistency for sentences about knowledge and belief
as defensibility, embeddability in a member of a model system: a family of partial descriptions
of states of affairs linked by epistemic and doxastic alternativeness. Defensibility is
[truth at a world of a model](##defensible_iff_exists_sat) whose knowledge is reflexive and
transitive and whose belief is serial and transitive. Moore's sentence "p but I do not believe
that p" is defensible but [its believed form is not](##indefensible_B_moore), and grading
sentences by the indefensibility of their believed and known forms
[predicts the judged sentences](##rows_judgment) but five.

## Implementation notes

* A `ModelSystem` carries the conditions common to every combination Hintikka lists, among them
  (C.K*) and (C.dox). The two he shows interchangeable with transitivity, (C.KK*) and (C.BB*), are
  the classes `ModelSystem.IsKKStar` and `ModelSystem.IsBBStar`: defensibility asks for both, and
  the arguments he says avoid one of them are stated for every model system.
* A model system relates arbitrary sets of formulas; only the relations between its members
  matter.
* Doxastic and epistemic indefensibility are defined for one sentence, the conjunction of the
  book's finite set of statements.
* The judged sentences are formulas in one atom `𝐩` whose agents are the discourse roles, `none`
  being a third person.

## TODO

* Chapter 6's quantified model sets.

## References

* [hintikka-1962]
-/

@[expose] public section

namespace Hintikka1962

open ModalLogic SetRel

universe u v

open EpistemicLogic EpistemicLogic.Formula

variable {V : Type u} {A : Type v}

/-! ### Model sets and model systems -/

/-- A model set (Sections 3.1 and 3.2): a set of formulas closed under the (C) conditions that
concern a single set, a partial description of a possible state of affairs. -/
structure IsModelSet (μ : Set (Formula V A)) : Prop where
  /-- (C.∼) -/
  neg : ∀ {p}, p ∈ μ → ∼p ∉ μ
  /-- (C.&) -/
  and : ∀ {p q}, p ⋏ q ∈ μ → p ∈ μ ∧ q ∈ μ
  /-- (C.v) -/
  or : ∀ {p q}, p ⋎ q ∈ μ → p ∈ μ ∨ q ∈ μ
  /-- (C.∼∼) -/
  neg_neg : ∀ {p}, ∼∼p ∈ μ → p ∈ μ
  /-- (C.∼&) -/
  neg_and : ∀ {p q}, ∼(p ⋏ q) ∈ μ → ∼p ∈ μ ∨ ∼q ∈ μ
  /-- (C.∼v) -/
  neg_or : ∀ {p q}, ∼(p ⋎ q) ∈ μ → ∼p ∈ μ ∧ ∼q ∈ μ
  /-- (C.K): whatever is known is true. -/
  know : ∀ {a p}, K a p ∈ μ → p ∈ μ
  /-- (C.∼K) -/
  neg_know : ∀ {a p}, ∼K a p ∈ μ → P a ∼p ∈ μ
  /-- (C.∼P) -/
  neg_poss : ∀ {a p}, ∼P a p ∈ μ → K a ∼p ∈ μ
  /-- (C.∼B) -/
  neg_believe : ∀ {a p}, ∼B a p ∈ μ → C a ∼p ∈ μ
  /-- (C.∼C) -/
  neg_compat : ∀ {a p}, ∼C a p ∈ μ → B a ∼p ∈ μ

/-- A model system (Sections 3.2 to 3.6): a set of model sets with, for each agent, an
epistemic and a doxastic alternativeness relation, satisfying the conditions common to the
combinations of Sections 3.4 and 3.5 and (C.dox), that doxastic alternatives are epistemic
alternatives. -/
structure ModelSystem (V : Type u) (A : Type v) where
  /-- The model sets. -/
  sets : Set (Set (Formula V A))
  /-- Epistemic alternativeness with respect to an agent. -/
  epi : A → SetRel (Set (Formula V A)) (Set (Formula V A))
  /-- Doxastic alternativeness with respect to an agent. -/
  dox : A → SetRel (Set (Formula V A)) (Set (Formula V A))
  isModelSet : ∀ {μ}, μ ∈ sets → IsModelSet μ
  /-- (C.P*) -/
  P_star : ∀ {a p μ}, μ ∈ sets → P a p ∈ μ → ∃ ν ∈ sets, μ ~[epi a] ν ∧ p ∈ ν
  /-- (C.K*) -/
  K_star : ∀ {a p μ ν}, μ ~[epi a] ν → K a p ∈ μ → p ∈ ν
  /-- (C.C*) -/
  C_star : ∀ {a p μ}, μ ∈ sets → C a p ∈ μ → ∃ ν ∈ sets, μ ~[dox a] ν ∧ p ∈ ν
  /-- (C.b*) -/
  b_star : ∀ {a p μ}, μ ∈ sets → B a p ∈ μ → ∃ ν ∈ sets, μ ~[dox a] ν ∧ p ∈ ν
  /-- (C.B*) -/
  B_star : ∀ {a p μ ν}, μ ~[dox a] ν → B a p ∈ μ → p ∈ ν
  /-- (C.dox) -/
  dox_le_epi : ∀ a, dox a ⊆ epi a

namespace ModelSystem

variable (S : ModelSystem V A)

/-- (C.KK*) (Section 3.2): what an agent knows in a model set he knows in its epistemic
alternatives. -/
class IsKKStar : Prop where
  KK_star : ∀ {a p μ ν}, μ ~[S.epi a] ν → K a p ∈ μ → K a p ∈ ν

/-- (C.BB*) (Section 3.5): what an agent believes in a model set he believes in its doxastic
alternatives. -/
class IsBBStar : Prop where
  BB_star : ∀ {a p μ ν}, μ ~[S.dox a] ν → B a p ∈ μ → B a p ∈ ν

variable {S} {a : A} {p q : Formula V A} {μ ν : Set (Formula V A)}

/-! The conditions on a model set, read at a member of a model system. -/

section Member

variable (hμ : μ ∈ S.sets)
include hμ

theorem neg (h : p ∈ μ) : ∼p ∉ μ := (S.isModelSet hμ).neg h
theorem and (h : p ⋏ q ∈ μ) : p ∈ μ ∧ q ∈ μ := (S.isModelSet hμ).and h
theorem or (h : p ⋎ q ∈ μ) : p ∈ μ ∨ q ∈ μ := (S.isModelSet hμ).or h
theorem neg_neg (h : ∼∼p ∈ μ) : p ∈ μ := (S.isModelSet hμ).neg_neg h
theorem neg_and (h : ∼(p ⋏ q) ∈ μ) : ∼p ∈ μ ∨ ∼q ∈ μ := (S.isModelSet hμ).neg_and h
theorem neg_or (h : ∼(p ⋎ q) ∈ μ) : ∼p ∈ μ ∧ ∼q ∈ μ := (S.isModelSet hμ).neg_or h
theorem know (h : K a p ∈ μ) : p ∈ μ := (S.isModelSet hμ).know h
theorem neg_know (h : ∼K a p ∈ μ) : P a ∼p ∈ μ := (S.isModelSet hμ).neg_know h
theorem neg_poss (h : ∼P a p ∈ μ) : K a ∼p ∈ μ := (S.isModelSet hμ).neg_poss h
theorem neg_believe (h : ∼B a p ∈ μ) : C a ∼p ∈ μ := (S.isModelSet hμ).neg_believe h
theorem neg_compat (h : ∼C a p ∈ μ) : B a ∼p ∈ μ := (S.isModelSet hμ).neg_compat h

end Member

theorem KK_star [S.IsKKStar] (h : μ ~[S.epi a] ν) (hp : K a p ∈ μ) : K a p ∈ ν :=
  IsKKStar.KK_star h hp

theorem BB_star [S.IsBBStar] (h : μ ~[S.dox a] ν) (hp : B a p ∈ μ) : B a p ∈ ν :=
  IsBBStar.BB_star h hp

-- Section 3.6
theorem KK_star_dox [S.IsKKStar] (h : μ ~[S.dox a] ν) (hp : K a p ∈ μ) : K a p ∈ ν :=
  S.KK_star (S.dox_le_epi a h) hp

theorem K_star_dox (h : μ ~[S.dox a] ν) (hp : K a p ∈ μ) : p ∈ ν :=
  S.K_star (S.dox_le_epi a h) hp

end ModelSystem

/-! ### Defensibility -/

/-- A set of sentences is defensible when it can be embedded in a member of a model system
(Section 3.3). -/
def Defensible (Γ : Set (Formula V A)) : Prop :=
  ∃ (S : ModelSystem V A) (_ : S.IsKKStar) (_ : S.IsBBStar), ∃ μ ∈ S.sets, Γ ⊆ μ

/-- Indefensibility, the book's reinterpretation of inconsistency (Section 2.6). -/
def Indefensible (Γ : Set (Formula V A)) : Prop := ¬ Defensible Γ

/-- A sentence is self-sustaining when its negation is indefensible (Section 2.6). -/
def SelfSustaining (p : Formula V A) : Prop := Indefensible {∼p}

/-- `p` virtually implies `q` when `p ⟹ q` is self-sustaining (Section 2.6). -/
def VirtuallyImplies (p q : Formula V A) : Prop := SelfSustaining (p ⟹ q)

/-- Virtual equivalence: virtual implication in both directions. -/
def VirtuallyEquivalent (p q : Formula V A) : Prop :=
  VirtuallyImplies p q ∧ VirtuallyImplies q p

/-- A sentence is doxastically indefensible for the person referred to by `a` to utter when
its believed form is indefensible (Section 4.8). -/
def DoxasticallyIndefensible (a : A) (p : Formula V A) : Prop := Indefensible {B a p}

/-- Doxastic implication: `p` implies `q` doxastically for `a` when `p ⋏ ∼q` is doxastically
indefensible (Section 4.9). -/
def DoxasticallyImplies (a : A) (p q : Formula V A) : Prop :=
  DoxasticallyIndefensible a (p ⋏ ∼q)

/-- Epistemic indefensibility for the person referred to by `a`: the known form is
indefensible (Section 4.12). -/
def EpistemicallyIndefensible (a : A) (p : Formula V A) : Prop := Indefensible {K a p}

/-- Epistemic implication (Section 4.12). -/
def EpistemicallyImplies (a : A) (p q : Formula V A) : Prop :=
  EpistemicallyIndefensible a (p ⋏ ∼q)

/-- Doxastic self-sustenance (Section 4.9): "a does not believe that p" is indefensible. -/
def DoxasticallySelfSustaining (a : A) (p : Formula V A) : Prop := Indefensible {∼B a p}

variable {a b : A} {p q : Formula V A}

theorem indefensible_singleton : Indefensible {p} ↔
    ∀ S : ModelSystem V A, S.IsKKStar → S.IsBBStar → ∀ μ ∈ S.sets, p ∉ μ :=
  ⟨fun h S h₁ h₂ μ hμ hp ↦ h ⟨S, h₁, h₂, μ, hμ, Set.singleton_subset_iff.2 hp⟩,
    fun h ⟨S, h₁, h₂, μ, hμ, hΓ⟩ ↦ h S h₁ h₂ μ hμ (hΓ rfl)⟩

theorem indefensible_pair : Indefensible {p, q} ↔
    ∀ S : ModelSystem V A, S.IsKKStar → S.IsBBStar → ∀ μ ∈ S.sets, p ∈ μ → q ∉ μ :=
  ⟨fun h S h₁ h₂ μ hμ hp hq ↦
      h ⟨S, h₁, h₂, μ, hμ, Set.insert_subset hp (Set.singleton_subset_iff.2 hq)⟩,
    fun h ⟨S, h₁, h₂, μ, hμ, hΓ⟩ ↦ h S h₁ h₂ μ hμ (hΓ (.inl rfl)) (hΓ (.inr rfl))⟩

theorem Indefensible.of_and (h : Indefensible {p, q}) : Indefensible {p ⋏ q} :=
  indefensible_singleton.2 fun S _ _ μ hμ hpq ↦
    let h' := S.and hμ hpq; indefensible_pair.1 h S ‹_› ‹_› μ hμ h'.1 h'.2

theorem Indefensible.doxasticallyIndefensible (h : Indefensible {p}) :
    DoxasticallyIndefensible a p :=
  indefensible_singleton.2 fun S _ _ μ hμ hB ↦
    let ⟨ν, hν, _, hp⟩ := S.b_star hμ hB; indefensible_singleton.1 h S ‹_› ‹_› ν hν hp

-- Section 3.10
theorem virtuallyImplies_of_indefensible (h : Indefensible {p, ∼q}) : VirtuallyImplies p q :=
  indefensible_singleton.2 fun S _ _ μ hμ hn ↦
    let h₁ := S.and hμ (S.neg_neg hμ hn)
    indefensible_pair.1 h S ‹_› ‹_› μ hμ h₁.1 h₁.2

-- Section 4.8
theorem doxasticallyIndefensible_iff : DoxasticallyIndefensible a p ↔ Indefensible {p, B a p} :=
  ⟨fun h ↦ indefensible_pair.2 fun S _ _ μ hμ _ hB ↦ indefensible_singleton.1 h S ‹_› ‹_› μ hμ hB,
    fun h ↦ indefensible_singleton.2 fun S _ _ μ hμ hB ↦
      let ⟨ν, hν, hμν, hp⟩ := S.b_star hμ hB
      indefensible_pair.1 h S ‹_› ‹_› ν hν hp (S.BB_star hμν hB)⟩

/-! ### Possible-worlds models

Section 2.8 glosses the notions in terms of worlds "in which everybody follows the
consequences of what he knows as far as they lead him": a sentence is defensible when it is true
at some such world. The formulas true at a world of a model form a model set, and the truth sets
of a model form a model system, which satisfies (C.KK*) and (C.BB*) when the relations are
transitive, the condition (C.trans) of Section 3.4. -/

section Models

variable {W : Type*} (M : Model V A W)

theorem isModelSet_truthSet (w : W) : IsModelSet (M.truthSet w) where
  neg hp hnp := hnp hp
  and h := h
  or h := h
  neg_neg h := not_not.mp h
  neg_and h := not_and_or.mp h
  neg_or h := not_or.mp h
  know h := h w ((M.epi_refl _).refl w)
  neg_know h := not_box.mp h
  neg_poss h := not_diamond.mp h
  neg_believe h := not_box.mp h
  neg_compat h := not_diamond.mp h

/-- The truth sets of a model, with alternativeness inherited from the worlds, form a model
system. -/
def ModelSystem.ofModel : ModelSystem V A where
  sets := Set.range M.truthSet
  epi a := Prod.map M.truthSet M.truthSet '' M.epi a
  dox a := Prod.map M.truthSet M.truthSet '' M.dox a
  isModelSet := by rintro _ ⟨w, rfl⟩; exact isModelSet_truthSet M w
  P_star := by
    rintro a p _ ⟨w, rfl⟩ ⟨v, hv, hp⟩
    exact ⟨_, ⟨v, rfl⟩, ⟨(w, v), hv, rfl⟩, hp⟩
  K_star := by rintro a p _ _ ⟨⟨w, v⟩, hwv, ⟨⟩⟩ h; exact h v hwv
  C_star := by
    rintro a p _ ⟨w, rfl⟩ ⟨v, hv, hp⟩
    exact ⟨_, ⟨v, rfl⟩, ⟨(w, v), hv, rfl⟩, hp⟩
  b_star := by
    rintro a p _ ⟨w, rfl⟩ h
    obtain ⟨v, hv⟩ := (M.dox_serial a).serial w
    exact ⟨_, ⟨v, rfl⟩, ⟨(w, v), hv, rfl⟩, h v hv⟩
  B_star := by rintro a p _ _ ⟨⟨w, v⟩, hwv, ⟨⟩⟩ h; exact h v hwv
  dox_le_epi a := Set.image_mono (M.dox_le_epi a)

instance [∀ a, (M.epi a).IsTrans] : (ModelSystem.ofModel M).IsKKStar where
  KK_star := by
    rintro a p _ _ ⟨⟨w, v⟩, hwv, ⟨⟩⟩ h u hvu
    exact h u ((M.epi a).trans hwv hvu)

instance [∀ a, (M.dox a).IsTrans] : (ModelSystem.ofModel M).IsBBStar where
  BB_star := by
    rintro a p _ _ ⟨⟨w, v⟩, hwv, ⟨⟩⟩ h u hvu
    exact h u ((M.dox a).trans hwv hvu)

theorem ModelSystem.mem_ofModel (w : W) : M.truthSet w ∈ (ModelSystem.ofModel M).sets :=
  ⟨w, rfl⟩

variable [∀ a, (M.epi a).IsTrans] [∀ a, (M.dox a).IsTrans]

theorem defensible_of_subset_truthSet {Γ : Set (Formula V A)} {w : W}
    (h : Γ ⊆ M.truthSet w) : Defensible Γ :=
  ⟨ModelSystem.ofModel M, inferInstance, inferInstance, _, ModelSystem.mem_ofModel M w, h⟩

theorem defensible_of_sat {w : W} (h : M.Sat p w) : Defensible {p} :=
  defensible_of_subset_truthSet M (Set.singleton_subset_iff.mpr h)

theorem not_virtuallyImplies_of_sat {w : W} (h : M.Sat (p ⋏ ∼q) w) : ¬ VirtuallyImplies p q :=
  not_not_intro (defensible_of_sat M (not_not_intro h))

end Models

/-! ### The canonical model

The model sets of a model system are themselves the worlds of a model, the canonical model:
epistemic alternativeness is accessibility, the ancestral of alternativeness that Section 3.4
uses to trade (C.KK*) for (C.trans), and doxastic alternativeness is its transitive closure,
together with a loop at each model set without doxastic alternatives, which (C.b*) shows holds
no belief. Every formula of a model set is true at it, so defensibility is truth at a world. -/

namespace ModelSystem

open Relation

variable (S : ModelSystem V A)

/-- The canonical model of a model system. -/
def toModel : Model V A S.sets where
  epi a := {(μ, ν) | ReflTransGen (fun μ ν : S.sets ↦ ↑μ ~[S.epi a] ↑ν) μ ν}
  dox a := {(μ, ν) | TransGen (fun μ ν : S.sets ↦ ↑μ ~[S.dox a] ↑ν) μ ν ∨
    μ = ν ∧ ∀ ξ : S.sets, ¬ ↑μ ~[S.dox a] ↑ξ}
  val v μ := atom v ∈ (μ : Set (Formula V A))
  epi_refl _ := ⟨fun _ ↦ .refl⟩
  dox_serial a := ⟨fun μ ↦ by
    by_cases h : ∃ ν : S.sets, ↑μ ~[S.dox a] ↑ν
    · obtain ⟨ν, h⟩ := h
      exact ⟨ν, .inl (.single h)⟩
    · exact ⟨μ, .inr ⟨rfl, not_exists.mp h⟩⟩⟩
  dox_le_epi a := by
    rintro ⟨μ, ν⟩ (h | ⟨rfl, -⟩)
    · exact ReflTransGen.mono (r := fun μ ν : S.sets ↦ ↑μ ~[S.dox a] ↑ν)
        (fun _ _ h ↦ S.dox_le_epi a h) _ _ h.to_reflTransGen
    · exact .refl

instance (a : A) : (S.toModel.epi a).IsTrans := ⟨fun _ _ _ ↦ ReflTransGen.trans⟩

instance (a : A) : (S.toModel.dox a).IsTrans := ⟨by
  rintro μ ν ξ (h | ⟨rfl, hμ⟩) (h' | ⟨rfl, -⟩)
  · exact .inl (h.trans h')
  · exact .inl h
  · obtain ⟨ν, hν, -⟩ := TransGen.head'_iff.mp h'
    exact absurd hν (hμ ν)
  · exact .inr ⟨rfl, hμ⟩⟩

variable {S}

theorem mem_of_epi_toModel [S.IsKKStar] {μ ν : S.sets} (h : K a p ∈ (μ : Set (Formula V A)))
    (hμν : μ ~[S.toModel.epi a] ν) : p ∈ (ν : Set (Formula V A)) := by
  have : K a p ∈ (ν : Set (Formula V A)) := by
    change ReflTransGen _ μ ν at hμν
    induction hμν with
    | refl => exact h
    | tail _ h' ih => exact S.KK_star h' ih
  exact S.know ν.2 this

theorem mem_of_dox_toModel [S.IsBBStar] {μ ν : S.sets} (h : B a p ∈ (μ : Set (Formula V A)))
    (hμν : μ ~[S.toModel.dox a] ν) : p ∈ (ν : Set (Formula V A)) := by
  change TransGen _ μ ν ∨ _ at hμν
  rcases hμν with hμν | ⟨rfl, hμ⟩
  · have : B a p ∈ (ν : Set (Formula V A)) ∧ p ∈ (ν : Set (Formula V A)) := by
      induction hμν with
      | single h' => exact ⟨S.BB_star h' h, S.B_star h' h⟩
      | tail _ h' ih => exact ⟨S.BB_star h' ih.1, S.B_star h' ih.1⟩
    exact this.2
  · obtain ⟨ν, hν, hμν, -⟩ := S.b_star μ.2 h
    exact absurd hμν (hμ ⟨ν, hν⟩)

variable [S.IsKKStar] [S.IsBBStar]

theorem sat_toModel (p : Formula V A) (μ : S.sets) :
    (p ∈ (μ : Set (Formula V A)) → S.toModel.Sat p μ) ∧
      (∼p ∈ (μ : Set (Formula V A)) → ¬ S.toModel.Sat p μ) := by
  induction p generalizing μ with
  | atom v => exact ⟨id, fun h h' ↦ S.neg μ.2 h' h⟩
  | neg p ih => exact ⟨(ih μ).2, fun h hn ↦ hn ((ih μ).1 (S.neg_neg μ.2 h))⟩
  | and p q ihp ihq =>
    refine ⟨fun h ↦ ?_, fun h ⟨hp, hq⟩ ↦ ?_⟩
    · have h' := S.and μ.2 h
      exact ⟨(ihp μ).1 h'.1, (ihq μ).1 h'.2⟩
    · exact (S.neg_and μ.2 h).elim (fun h ↦ (ihp μ).2 h hp) fun h ↦ (ihq μ).2 h hq
  | or p q ihp ihq =>
    refine ⟨fun h ↦ (S.or μ.2 h).imp (ihp μ).1 (ihq μ).1, fun h ↦ ?_⟩
    have h' := S.neg_or μ.2 h
    exact not_or_intro ((ihp μ).2 h'.1) ((ihq μ).2 h'.2)
  | K a p ih =>
    refine ⟨fun h ν hμν ↦ (ih ν).1 (mem_of_epi_toModel h hμν), fun h hK ↦ ?_⟩
    obtain ⟨ν, hν, hμν, hp⟩ := S.P_star μ.2 (S.neg_know μ.2 h)
    exact (ih ⟨ν, hν⟩).2 hp (hK ⟨ν, hν⟩ (.single hμν))
  | P a p ih =>
    refine ⟨fun h ↦ ?_, fun h ⟨ν, hμν, hp⟩ ↦ ?_⟩
    · obtain ⟨ν, hν, hμν, hp⟩ := S.P_star μ.2 h
      exact ⟨⟨ν, hν⟩, .single hμν, (ih ⟨ν, hν⟩).1 hp⟩
    · exact (ih ν).2 (mem_of_epi_toModel (S.neg_poss μ.2 h) hμν) hp
  | B a p ih =>
    refine ⟨fun h ν hμν ↦ (ih ν).1 (mem_of_dox_toModel h hμν), fun h hB ↦ ?_⟩
    obtain ⟨ν, hν, hμν, hp⟩ := S.C_star μ.2 (S.neg_believe μ.2 h)
    exact (ih ⟨ν, hν⟩).2 hp (hB ⟨ν, hν⟩ (.inl (.single hμν)))
  | C a p ih =>
    refine ⟨fun h ↦ ?_, fun h ⟨ν, hμν, hp⟩ ↦ ?_⟩
    · obtain ⟨ν, hν, hμν, hp⟩ := S.C_star μ.2 h
      exact ⟨⟨ν, hν⟩, .inl (.single hμν), (ih ⟨ν, hν⟩).1 hp⟩
    · exact (ih ν).2 (mem_of_dox_toModel (S.neg_compat μ.2 h) hμν) hp

theorem subset_truthSet_toModel (μ : S.sets) :
    (μ : Set (Formula V A)) ⊆ S.toModel.truthSet μ :=
  fun p hp ↦ (sat_toModel p μ).1 hp

end ModelSystem

/-- Defensibility is truth at a world of a model with transitive alternativeness, the gloss of
Section 2.8: a set of sentences is defensible exactly when it is true together at some world in
which everybody follows the consequences of what he knows as far as they lead him. -/
theorem defensible_iff_exists_sat {Γ : Set (Formula V A)} :
    Defensible Γ ↔ ∃ (W : Type (max u v)) (M : Model V A W) (_ : ∀ a, (M.epi a).IsTrans)
      (_ : ∀ a, (M.dox a).IsTrans) (w : W), Γ ⊆ M.truthSet w :=
  ⟨fun ⟨S, _, _, μ, hμ, hΓ⟩ ↦ ⟨S.sets, S.toModel, inferInstance, inferInstance, ⟨μ, hμ⟩,
      hΓ.trans (S.subset_truthSet_toModel ⟨μ, hμ⟩)⟩,
    fun ⟨_, M, _, _, _, h⟩ ↦ defensible_of_subset_truthSet M h⟩

-- Section 2.8
theorem selfSustaining_iff : SelfSustaining p ↔ ∀ (W : Type (max u v)) (M : Model V A W),
    (∀ a, (M.epi a).IsTrans) → (∀ a, (M.dox a).IsTrans) → ∀ w, M.Sat p w :=
  ⟨fun h _ M _ _ w ↦ by_contra fun hn ↦ h (defensible_of_sat M (w := w) hn),
    fun h hd ↦ let ⟨W, M, h₁, h₂, w, hw⟩ := defensible_iff_exists_sat.1 hd
      hw rfl (h W M h₁ h₂ w)⟩

-- Section 3.10
theorem virtuallyImplies_iff_indefensible : VirtuallyImplies p q ↔ Indefensible {p, ∼q} := by
  refine ⟨fun h hd ↦ h ?_, virtuallyImplies_of_indefensible⟩
  obtain ⟨W, M, _, _, w, hw⟩ := defensible_iff_exists_sat.1 hd
  exact defensible_of_sat M (w := w) fun hn ↦ hn ⟨hw (.inl rfl), hw (.inr rfl)⟩

/-! ### The countermodels

The countermodels have one atomic sentence `𝐩` and the agents `𝐈`, the speaker, `𝐲`, the
addressee, and `𝐡`, a third person. -/

open Discourse

/-- The atomic sentence of the countermodels. -/
local notation "𝐩" => (Formula.atom () : Formula Unit (Option Role))
/-- The speaker. -/
local notation "𝐈" => (some Role.speaker : Option Role)
/-- The addressee. -/
local notation "𝐲" => (some Role.addressee : Option Role)
/-- A third person. -/
local notation "𝐡" => (none : Option Role)

/-- A model in which belief and knowledge diverge at `0`, which believes `1` but cannot rule out
`2`. -/
abbrev mK : Model Unit (Option Role) (Fin 3) where
  epi _ := {p | p.1 = p.2 ∨ p.1 = 0}
  dox _ := {p | (p.1 = 0 ∧ p.2 = 1) ∨ (p.1 ≠ 0 ∧ p.1 = p.2)}
  val _ w := w ≠ 2
  epi_refl _ := ⟨by decide +revert⟩
  dox_serial _ := ⟨fun _ ↦ by decide +revert⟩
  dox_le_epi a := by rintro ⟨w, v⟩ h; revert a w v h; decide

instance (a : Option Role) : (mK.epi a).IsTrans := ⟨by decide +revert⟩
instance (a : Option Role) : (mK.dox a).IsTrans := ⟨by decide +revert⟩

/-- A model in which the speaker believes that a third person believes what the speaker does not. -/
abbrev mB : Model Unit (Option Role) (Fin 3) where
  epi _ := .univ
  dox a := {p | (a = 𝐈 ∧ ((p.1 = 0 ∧ p.2 ≠ 0) ∨ (p.1 ≠ 0 ∧ p.2 = 1))) ∨ (a ≠ 𝐈 ∧ p.2 = 0)}
  val _ w := w ≠ 2
  epi_refl _ := ⟨fun _ ↦ trivial⟩
  dox_serial _ := ⟨fun _ ↦ by decide +revert⟩
  dox_le_epi _ _ _ := trivial

instance (a : Option Role) : (mB.epi a).IsTrans := ⟨fun _ _ _ _ _ ↦ trivial⟩
instance (a : Option Role) : (mB.dox a).IsTrans := ⟨by revert a; decide⟩

/-- The model system of Section 4.14 for (45). -/
abbrev model45 : Model Unit (Option Role) (Fin 3) where
  epi a := {p | p.1 = p.2 ∨ (a = 𝐈 ∧ p.1 < p.2)}
  dox a := {p | (a = 𝐈 ∧ p.1 ≠ 2 ∧ p.2 = 1) ∨ ((a ≠ 𝐈 ∨ p.1 = 2) ∧ p.1 = p.2)}
  val _ w := w = 1
  epi_refl _ := ⟨fun _ ↦ .inl rfl⟩
  dox_serial _ := ⟨by decide +revert⟩
  dox_le_epi a := by rintro ⟨w, v⟩ h; revert a w v h; decide

instance (a : Option Role) : (model45.epi a).IsTrans := ⟨by revert a; decide⟩
instance (a : Option Role) : (model45.dox a).IsTrans := ⟨by revert a; decide⟩

/-- The model system of (74)-(82), its doxastic alternativeness closed under transitivity. -/
abbrev model73 : Model Unit (Option Role) (Fin 3) where
  epi _ := {p | p.1 ≤ p.2}
  dox a := {p | (a = 𝐈 ∧ (p.1 = 0 ∧ p.2 ≠ 0 ∨ p.1 ≠ 0 ∧ p.2 = 2)) ∨ (a ≠ 𝐈 ∧ p.1 = p.2)}
  val _ w := w = 2
  epi_refl _ := ⟨by decide +revert⟩
  dox_serial _ := ⟨by decide +revert⟩
  dox_le_epi a := by rintro ⟨w, v⟩ h; revert a w v h; decide

instance (a : Option Role) : (model73.epi a).IsTrans := ⟨by decide +revert⟩
instance (a : Option Role) : (model73.dox a).IsTrans := ⟨by revert a; decide⟩

/-- A model in which a third person disbelieves the atom, true at `0`; the others are omniscient. -/
abbrev mThird : Model Unit (Option Role) (Fin 2) where
  epi a := {p | p.1 = p.2 ∨ a = 𝐡 ∧ p.1 = 0}
  dox a := {p | a = 𝐡 ∧ p.2 = 1 ∨ a ≠ 𝐡 ∧ p.1 = p.2}
  val _ w := w = 0
  epi_refl _ := ⟨fun _ ↦ .inl rfl⟩
  dox_serial _ := ⟨by decide +revert⟩
  dox_le_epi a := by rintro ⟨w, v⟩ h; revert a w v h; decide

instance (a : Option Role) : (mThird.epi a).IsTrans := ⟨by decide +revert⟩
instance (a : Option Role) : (mThird.dox a).IsTrans := ⟨by decide +revert⟩

/-- A model in which the speaker cannot tell the two worlds apart and believes the atom true. -/
abbrev mUndecided : Model Unit (Option Role) (Fin 2) where
  epi a := {p | p.1 = p.2 ∨ a = 𝐈}
  dox a := {p | a = 𝐈 ∧ p.2 = 1 ∨ a ≠ 𝐈 ∧ p.1 = p.2}
  val _ w := w = 1
  epi_refl _ := ⟨fun _ ↦ .inl rfl⟩
  dox_serial _ := ⟨by decide +revert⟩
  dox_le_epi a := by rintro ⟨w, v⟩ h; revert a w v h; decide

instance (a : Option Role) : (mUndecided.epi a).IsTrans := ⟨by decide +revert⟩
instance (a : Option Role) : (mUndecided.dox a).IsTrans := ⟨by decide +revert⟩

/-- A model with intransitive alternativeness, whose truth sets satisfy neither (C.KK*) nor
(C.BB*). -/
abbrev nonTransitive : Model Unit (Option Role) (Fin 3) where
  epi _ := {p | p.1 = p.2 ∨ p.2 = p.1 + 1}
  dox _ := {p | p.2 = p.1 + 1}
  val _ w := w ≠ 2
  epi_refl _ := ⟨fun _ ↦ .inl rfl⟩
  dox_serial _ := ⟨by decide +revert⟩
  dox_le_epi a := by rintro ⟨w, v⟩ h; revert a w v h; decide

/-! ### Chapter 3: consequences and rejected conditions

(C.KB), that whatever is known is believed to be known, follows from (C.dox) (Section 3.6).
(C.BK), that whatever is believed is known to be believed, would make "a believes that p"
virtually imply "a knows that it is possible, for all a knows, that p", and (C.PK), that
whatever is possible is known to be possible, would make (13) self-sustaining; neither is a
consequence of the conditions (Sections 3.7 and 3.8). -/

variable (a b p)

theorem virtuallyImplies_K_B_K : VirtuallyImplies (K a p) (B a (K a p)) :=
  virtuallyImplies_of_indefensible <| indefensible_pair.2 fun S _ _ μ hμ hK hn ↦ by
    obtain ⟨ν, hν, hμν, h⟩ := S.C_star hμ (S.neg_believe hμ hn)
    exact S.neg hν (S.KK_star_dox hμν hK) h

-- Section 3.7
theorem not_virtuallyImplies_B_K_P : ¬ VirtuallyImplies (B 𝐈 𝐩) (K 𝐈 (P 𝐈 𝐩)) :=
  not_virtuallyImplies_of_sat mK (w := 0) (by decide)

-- Section 3.7
theorem not_virtuallyImplies_B_K_B : ¬ VirtuallyImplies (B 𝐈 𝐩) (K 𝐈 (B 𝐈 𝐩)) :=
  not_virtuallyImplies_of_sat mK (w := 0) (by decide)

-- (13), Section 3.8
theorem not_virtuallyImplies_K_P : ¬ VirtuallyImplies 𝐩 (K 𝐈 (P 𝐈 𝐩)) :=
  not_virtuallyImplies_of_sat mK (w := 0) (by decide)

/-! ### Chapter 4: knowing that others know -/

-- (20)-(26), Sections 4.1 and 4.2
theorem virtuallyImplies_K_K_K : VirtuallyImplies (K a (K b p)) (K a p) :=
  virtuallyImplies_of_indefensible <| indefensible_pair.2 fun S _ _ μ hμ hK hn ↦ by
    obtain ⟨ν, hν, hμν, h⟩ := S.P_star hμ (S.neg_know hμ hn)
    exact S.neg hν (S.know hν (S.K_star hμν hK)) h

-- (27), Section 4.3
theorem not_virtuallyImplies_B_B_B : ¬ VirtuallyImplies (B 𝐈 (B 𝐡 𝐩)) (B 𝐈 𝐩) :=
  not_virtuallyImplies_of_sat mB (w := 0) (by decide)

-- Section 4.4
theorem not_virtuallyImplies_B_K_K : ¬ VirtuallyImplies (B 𝐈 (K 𝐲 𝐩)) (K 𝐈 𝐩) :=
  not_virtuallyImplies_of_sat mK (w := 0) (by decide)

/-! ### Chapter 4: Moore's problem

Moore's sentence (8), "p but I do not believe that p", is defensible, but (30)*, its believed
form, is not: what uttering (8) violates is the presumption that the speaker can believe what
he says (Sections 4.5 and 4.6). The believed form (30)(a)* of the third-person variant (8)(a)
is defensible unless the believer is the person spoken about. The indefensibility of (30)* turns
on (C.BB*) (p. 68, note 4), but that of (8) together with (30)* does not (Section 4.7). -/

/-- The model of Section 4.6's discussion of (8) and (8)(a): two states of affairs, the atom
true in the first; every agent believes only the second, except `a`, who believes only the
first. -/
def mooreModel : Model V A Bool where
  epi _ := .univ
  dox c := {p | (c = a ∧ p.2 = false) ∨ (c ≠ a ∧ p.2 = true)}
  val _ w := w = true
  epi_refl _ := ⟨fun _ ↦ trivial⟩
  dox_serial c := ⟨fun _ ↦ by
    by_cases h : c = a
    · exact ⟨false, .inl ⟨h, rfl⟩⟩
    · exact ⟨true, .inr ⟨h, rfl⟩⟩⟩
  dox_le_epi _ _ _ := trivial

instance (c : A) : ((mooreModel (V := V) a).epi c).IsTrans := ⟨fun _ _ _ _ _ ↦ trivial⟩
instance (c : A) : ((mooreModel (V := V) a).dox c).IsTrans := ⟨fun _ _ _ _ h ↦ h⟩

-- (8)
theorem defensible_moore (v : V) : Defensible {(atom v : Formula V A) ⋏ ∼B a (atom v)} :=
  defensible_of_sat (mooreModel a) (w := true)
    ⟨rfl, fun h ↦ Bool.false_ne_true (h false (.inl ⟨rfl, rfl⟩))⟩

-- (30)(a)*, Section 4.6
theorem defensible_B_moore_of_ne (hab : b ≠ a) (v : V) :
    Defensible {B b ((atom v : Formula V A) ⋏ ∼B a (atom v))} :=
  defensible_of_sat (mooreModel a) (w := true) fun x hx ↦ by
    rcases hx with ⟨rfl, _⟩ | ⟨_, rfl⟩
    · exact absurd rfl hab
    · exact ⟨rfl, fun h ↦ Bool.false_ne_true (h false (.inl ⟨rfl, rfl⟩))⟩

/-- Moore's problem (Section 4.6): (30)*, "a believes that p but that a does not believe that
p", is indefensible, by the reductive argument (33)-(39). -/
theorem indefensible_B_moore : Indefensible {B a (p ⋏ ∼B a p)} :=
  indefensible_singleton.2 fun S _ _ μ hμ h ↦ by
    obtain ⟨ν, hν, hμν, h₁⟩ := S.b_star hμ h
    have h₂ := S.BB_star hμν h
    obtain ⟨ξ, hξ, hνξ, h₃⟩ := S.C_star hν (S.neg_believe hν (S.and hν h₁).2)
    exact S.neg hξ (S.and hξ (S.B_star hνξ h₂)).1 h₃

-- (30), p. 68, note 4
theorem exists_B_moore_mem :
    ∃ S : ModelSystem Unit (Option Role), ∃ μ ∈ S.sets, B 𝐈 (𝐩 ⋏ ∼B 𝐈 𝐩) ∈ μ :=
  ⟨ModelSystem.ofModel nonTransitive, _, ModelSystem.mem_ofModel nonTransitive 0, by decide⟩

-- Section 4.7, (8), (30)
theorem ModelSystem.moore_and_B_moore_not_mem (S : ModelSystem V A) {μ : Set (Formula V A)}
    (hμ : μ ∈ S.sets) : (p ⋏ ∼B a p) ⋏ B a (p ⋏ ∼B a p) ∉ μ := fun h ↦ by
  obtain ⟨h₁, h₂⟩ := S.and hμ h
  obtain ⟨ν, hν, hμν, h₃⟩ := S.C_star hμ (S.neg_believe hμ (S.and hμ h₁).2)
  exact S.neg hν (S.and hν (S.B_star hμν h₂)).1 h₃

-- Section 4.8, (8)
theorem doxasticallyIndefensible_moore : DoxasticallyIndefensible a (p ⋏ ∼B a p) :=
  indefensible_B_moore a p

-- Section 4.9
theorem doxasticallyImplies_B : DoxasticallyImplies a p (B a p) :=
  indefensible_B_moore a p

-- Section 4.9 (p. 76)
theorem doxasticallySelfSustaining_iff : DoxasticallySelfSustaining a p ↔ SelfSustaining p := by
  refine ⟨fun h hd ↦ h ?_, fun h ↦ indefensible_singleton.2 fun S _ _ μ hμ hn ↦ ?_⟩
  · obtain ⟨W, M, _, _, w, hw⟩ := defensible_iff_exists_sat.1 hd
    exact defensible_of_sat (M.withPredecessor w) (M.sat_withPredecessor_none_neg_B w (hw rfl))
  · obtain ⟨ν, hν, -, hp⟩ := S.C_star hμ (S.neg_believe hμ hn)
    exact indefensible_singleton.1 h S ‹_› ‹_› ν hν hp

/-! ### Chapter 4: the analogue for knowledge

(9), "p but I do not know whether p", is (4)*'s `p ⋏ notKnowsWhether a p`; its known form
(40)* and the simpler (41) are indefensible in every model system, (C.KK*) or not, so that any
sentence implies "I know it" epistemically (Sections 4.11 to 4.13). Knowledge and belief come
apart in (44) and (45) (Section 4.14). -/

-- (41), Section 4.11
theorem ModelSystem.K_moore_not_mem (S : ModelSystem V A) {μ : Set (Formula V A)}
    (hμ : μ ∈ S.sets) : K a (p ⋏ ∼K a p) ∉ μ := fun h ↦ by
  have h₁ := S.and hμ (S.know hμ h)
  obtain ⟨ν, hν, hμν, h₂⟩ := S.P_star hμ (S.neg_know hμ h₁.2)
  exact S.neg hν (S.and hν (S.K_star hμν h)).1 h₂

-- (41)
theorem indefensible_K_moore : Indefensible {K a (p ⋏ ∼K a p)} :=
  indefensible_singleton.2 fun S _ _ _ hμ ↦ S.K_moore_not_mem a p hμ

-- (40)*, (9), Section 4.11
theorem indefensible_K_moore_whether : Indefensible {K a (p ⋏ notKnowsWhether a p)} :=
  indefensible_singleton.2 fun S _ _ μ hμ h ↦ by
    have h₁ := S.and hμ (S.know hμ h)
    obtain ⟨ν, hν, hμν, h₂⟩ := S.P_star hμ (S.neg_know hμ (S.and hμ h₁.2).1)
    exact S.neg hν (S.and hν (S.K_star hμν h)).1 h₂

-- Sections 4.12 and 4.13 (p. 82)
theorem epistemicallyImplies_K : EpistemicallyImplies a p (K a p) :=
  indefensible_K_moore a p

-- (42)*, Section 4.13
theorem epistemicallyIndefensible_K_neg_K : EpistemicallyIndefensible b (K a p ⋏ ∼K b p) :=
  indefensible_singleton.2 fun S _ _ μ hμ h ↦ by
    have h₁ := S.and hμ (S.know hμ h)
    obtain ⟨ν, hν, hμν, h₂⟩ := S.P_star hμ (S.neg_know hμ h₁.2)
    exact S.neg hν (S.know hν (S.and hν (S.K_star hμν h)).1) h₂

-- (43), Section 4.13
theorem defensible_K_knowsWhether :
    Defensible {K 𝐈 (knowsWhether 𝐡 𝐩 ⋏ ∼knowsWhether 𝐈 𝐩)} :=
  defensible_of_sat mUndecided (w := 0) (by decide)

-- (44), Section 4.14
theorem indefensible_K_neg_B : Indefensible {K a (p ⋏ ∼B a p)} :=
  indefensible_singleton.2 fun S _ _ μ hμ h ↦ by
    have h₁ := S.and hμ (S.know hμ h)
    obtain ⟨ν, hν, hμν, h₂⟩ := S.C_star hμ (S.neg_believe hμ h₁.2)
    exact S.neg hν (S.and hν (S.K_star_dox hμν h)).1 h₂

-- (45), Section 4.14
theorem defensible_B_neg_K : Defensible {B 𝐈 (𝐩 ⋏ ∼K 𝐈 𝐩)} :=
  defensible_of_sat model45 (w := 0) (by decide)

-- (46), (47), Section 4.14
theorem virtuallyImplies_B_and :
    VirtuallyImplies (B a (p ⋏ notKnowsWhether a p)) (B a p ⋏ ∼K a p) :=
  virtuallyImplies_of_indefensible <| indefensible_pair.2 fun S _ _ μ hμ h₀ hn ↦ by
    rcases S.neg_and hμ hn with h | h
    · obtain ⟨ν, hν, hμν, h₁⟩ := S.C_star hμ (S.neg_believe hμ h)
      exact S.neg hν (S.and hν (S.B_star hμν h₀)).1 h₁
    · obtain ⟨ν, hν, hμν, h₁⟩ := S.b_star hμ h₀
      exact S.neg hν (S.KK_star_dox hμν (S.neg_neg hμ h)) (S.and hν (S.and hν h₁).2).1

-- (47), (46), Section 4.14
theorem doxasticallyImplies_B_of_and :
    DoxasticallyImplies a (B a p ⋏ ∼K a p) (B a (p ⋏ notKnowsWhether a p)) :=
  indefensible_singleton.2 fun S _ _ μ hμ h₀ ↦ by
    obtain ⟨ν, hν, hμν, h₁⟩ := S.b_star hμ h₀
    obtain ⟨h₂, h₃⟩ := S.and hν h₁
    obtain ⟨ξ, hξ, hνξ, h₄⟩ := S.C_star hν (S.neg_believe hν h₃)
    have hp := S.B_star hνξ (S.and hν h₂).1
    have hK := (S.and hξ (S.and hξ (S.B_star hνξ (S.BB_star hμν h₀))).1).2
    rcases S.neg_and hξ h₄ with h | h
    · exact S.neg hξ hp h
    · rcases S.neg_and hξ h with h | h
      · exact S.neg hξ (S.neg_neg hξ h) hK
      · exact S.neg hξ hp (S.know hξ (S.neg_neg hξ h))

-- (48), (47), Section 4.14
theorem defensible_K_B_neg_K : Defensible {K 𝐈 (B 𝐈 𝐩 ⋏ ∼K 𝐈 𝐩)} :=
  defensible_of_sat mUndecided (w := 0) (by decide)

-- Section 4.14 (p. 84)
theorem defensible_K_B_notKnowsWhether : Defensible {K 𝐈 (B 𝐈 𝐩 ⋏ notKnowsWhether 𝐈 𝐩)} :=
  defensible_of_sat mUndecided (w := 0) (by decide)

-- (51), Section 4.16
theorem defensible_K_B_P : Defensible {K 𝐈 (B 𝐈 𝐩 ⋏ P 𝐈 ∼𝐩)} :=
  defensible_of_sat mUndecided (w := 0) (by decide)

-- (51), Section 4.16
theorem defensible_B_B_P : Defensible {B 𝐈 (B 𝐈 𝐩 ⋏ P 𝐈 ∼𝐩)} :=
  defensible_of_sat mUndecided (w := 0) (by decide)

-- (51)(a), Section 4.16
theorem indefensible_B_C : Indefensible {B a p ⋏ C a ∼p} :=
  indefensible_singleton.2 fun S _ _ μ hμ h ↦ by
    obtain ⟨h₁, h₂⟩ := S.and hμ h
    obtain ⟨ν, hν, hμν, h₃⟩ := S.C_star hμ h₂
    exact S.neg hν (S.B_star hμν h₁) h₃

-- (51)(b), Section 4.16
theorem epistemicallyIndefensible_C : EpistemicallyIndefensible a (p ⋏ C a ∼p) :=
  indefensible_singleton.2 fun S _ _ μ hμ h ↦ by
    obtain ⟨ν, hν, hμν, h₁⟩ := S.C_star hμ (S.and hμ (S.know hμ h)).2
    exact S.neg hν (S.and hν (S.K_star_dox hμν h)).1 h₁

-- (51)(b), Section 4.16
theorem doxasticallyIndefensible_C : DoxasticallyIndefensible a (p ⋏ C a ∼p) :=
  indefensible_singleton.2 fun S _ _ μ hμ h ↦ by
    obtain ⟨ν, hν, hμν, h₁⟩ := S.b_star hμ h
    obtain ⟨ξ, hξ, hνξ, h₂⟩ := S.C_star hν (S.and hν h₁).2
    exact S.neg hξ (S.and hξ (S.B_star hνξ (S.BB_star hμν h))).1 h₂

-- (51)(c), Section 4.16
theorem epistemicallyIndefensible_P : EpistemicallyIndefensible a (p ⋏ P a ∼p) :=
  indefensible_singleton.2 fun S _ _ μ hμ h ↦ by
    obtain ⟨ν, hν, hμν, h₁⟩ := S.P_star hμ (S.and hμ (S.know hμ h)).2
    exact S.neg hν (S.and hν (S.K_star hμν h)).1 h₁

-- (51)(c), Section 4.16
theorem defensible_B_P : Defensible {B 𝐈 (𝐩 ⋏ P 𝐈 ∼𝐩)} :=
  defensible_of_sat mUndecided (w := 0) (by decide)

/-! ### Chapter 5: knowing that one knows

"Knowing" and "knowing that one knows" are virtually equivalent, by (C.KK*) (Sections 5.2 and
5.4), but a model system lacking (C.KK*) holds (70), "a knows that p but he does not know that
he knows": its indefensibility depends on a's failure to follow the implications of what he
knows (Section 5.5). Its first-person form (71) is epistemically indefensible in every model
system (p. 123, note 29). Believing virtually implies believing that one believes, but not
conversely (Section 5.10). -/

-- (65)-(69), Section 5.2
theorem virtuallyImplies_K_KK : VirtuallyImplies (K a p) (K a (K a p)) :=
  virtuallyImplies_of_indefensible <| indefensible_pair.2 fun S _ _ μ hμ hK hn ↦ by
    obtain ⟨ν, hν, hμν, h⟩ := S.P_star hμ (S.neg_know hμ hn)
    exact S.neg hν (S.KK_star hμν hK) h

-- Section 5.2
theorem virtuallyImplies_KK_K : VirtuallyImplies (K a (K a p)) (K a p) :=
  virtuallyImplies_of_indefensible <| indefensible_pair.2 fun S _ _ _ hμ hK hn ↦
    S.neg hμ (S.know hμ hK) hn

/-- Section 5.2: (63), "a knows that a knows that p", and (64), "a knows that p", are virtually
equivalent. -/
theorem virtuallyEquivalent_K_KK : VirtuallyEquivalent (K a p) (K a (K a p)) :=
  ⟨virtuallyImplies_K_KK a p, virtuallyImplies_KK_K a p⟩

-- (70), (71), Section 5.5
theorem indefensible_K_and_not_KK : Indefensible {K a p ⋏ ∼K a (K a p)} :=
  (virtuallyImplies_iff_indefensible.1 (virtuallyImplies_K_KK a p)).of_and

-- (70), Section 5.5
theorem exists_K_and_not_KK_mem :
    ∃ S : ModelSystem Unit (Option Role), ∃ μ ∈ S.sets, K 𝐡 𝐩 ⋏ ∼K 𝐡 (K 𝐡 𝐩) ∈ μ :=
  ⟨ModelSystem.ofModel nonTransitive, _, ModelSystem.mem_ofModel nonTransitive 0, by decide⟩

-- (71), p. 123, note 29
theorem ModelSystem.K_and_not_KK_not_mem (S : ModelSystem V A) {μ : Set (Formula V A)}
    (hμ : μ ∈ S.sets) : K a (K a p ⋏ ∼K a (K a p)) ∉ μ :=
  S.K_moore_not_mem a (K a p) hμ

-- Section 5.2
theorem not_virtuallyImplies_negK_K_negK : ¬ VirtuallyImplies (∼K 𝐈 𝐩) (K 𝐈 ∼K 𝐈 𝐩) :=
  not_virtuallyImplies_of_sat mK (w := 0) (by decide)

-- Section 5.3 (p. 110)
theorem not_virtuallyImplies_B_negK_K :
    ¬ VirtuallyImplies (B 𝐈 𝐩 ⋏ ∼K 𝐈 𝐩) (K 𝐈 (B 𝐈 𝐩 ⋏ ∼K 𝐈 𝐩)) :=
  not_virtuallyImplies_of_sat mK (w := 0) (by decide)

-- (72), (73), Sections 5.3 and 5.10
theorem virtuallyImplies_B_BB : VirtuallyImplies (B a p) (B a (B a p)) :=
  virtuallyImplies_of_indefensible <| indefensible_pair.2 fun S _ _ μ hμ hB hn ↦ by
    obtain ⟨ν, hν, hμν, h⟩ := S.C_star hμ (S.neg_believe hμ hn)
    exact S.neg hν (S.BB_star hμν hB) h

/-- Section 5.10: (73), "a believes that a believes that p", does not virtually imply (72), "a
believes that p", by the model system of (74)-(82). -/
theorem not_virtuallyImplies_BB_B : ¬ VirtuallyImplies (B 𝐈 (B 𝐈 𝐩)) (B 𝐈 𝐩) :=
  not_virtuallyImplies_of_sat model73 (w := 0) (by decide)

-- Section 5.10 (p. 125)
theorem doxasticallyIndefensible_B_neg : DoxasticallyIndefensible a (B a p ⋏ ∼p) :=
  indefensible_singleton.2 fun S _ _ μ hμ h ↦ by
    obtain ⟨ν, hν, hμν, h₁⟩ := S.b_star hμ h
    obtain ⟨ξ, hξ, hνξ, h₂⟩ := S.b_star hν (S.BB_star hμν h)
    exact S.neg hξ (S.B_star hνξ (S.and hν h₁).1) (S.and hξ h₂).2

-- (84), Section 5.10
theorem doxasticallyIndefensible_BB_neg_B : DoxasticallyIndefensible a (B a (B a p) ⋏ ∼B a p) :=
  doxasticallyIndefensible_B_neg a (B a p)

/-! ### The judged sentences

Hintikka grades an utterance by its speaker to an addressee: it is absurd when doxastically
indefensible for the speaker (Sections 4.6 and 4.8), odd when epistemically indefensible for the
speaker (Sections 4.11 and 4.12) or to address to the addressee (Sections 4.17 and 4.18), and in
order otherwise. Judged sentences in tense, stress or "cannot", (29) and (57) to (59), are
outside the language. The grading predicts every other judgment except five, each of which the
book explains by a factor outside the logic: the complexity of (46) (p. 83), the intended
antiperformatory effect of the prize sentence (p. 91), the purposes of religious discourse in
(55) (p. 100), the redundancy of (60) beside (62) (p. 113), and the dependence of (70) on a's
failure to follow the implications of what he knows (p. 112, `exists_K_and_not_KK_mem`). -/

open Classical in
/-- The judgment Hintikka's grading predicts for a sentence. -/
noncomputable def predictedJudgment (p : Formula Unit (Option Role)) : Judgment :=
  if DoxasticallyIndefensible 𝐈 p then .unacceptable
  else if EpistemicallyIndefensible 𝐈 p ∨ EpistemicallyIndefensible 𝐲 p then .questionable
  else .acceptable

variable {p : Formula Unit (Option Role)}

theorem predictedJudgment_of_doxasticallyIndefensible (h : DoxasticallyIndefensible 𝐈 p) :
    predictedJudgment p = .unacceptable := by
  simp only [predictedJudgment, h, ↓reduceIte]

theorem predictedJudgment_of_epistemicallyIndefensible (h : Defensible {B 𝐈 p})
    (h' : EpistemicallyIndefensible 𝐈 p ∨ EpistemicallyIndefensible 𝐲 p) :
    predictedJudgment p = .questionable := by
  simp only [predictedJudgment, show ¬ DoxasticallyIndefensible 𝐈 p from not_not_intro h, h',
    ↓reduceIte]

theorem predictedJudgment_of_sat {W : Type*} (M : Model Unit (Option Role) W)
    [∀ a, (M.epi a).IsTrans] [∀ a, (M.dox a).IsTrans] {w : W}
    (h : M.Sat (B 𝐈 p ⋏ K 𝐈 p ⋏ K 𝐲 p) w) : predictedJudgment p = .acceptable := by
  simp only [predictedJudgment, ↓reduceIte,
    show ¬ DoxasticallyIndefensible 𝐈 p from not_not_intro (defensible_of_sat M h.1.1),
    show ¬ (EpistemicallyIndefensible 𝐈 p ∨ EpistemicallyIndefensible 𝐲 p) from
      not_or_intro (not_not_intro (defensible_of_sat M h.1.2))
        (not_not_intro (defensible_of_sat M h.2))]

/-- The judged sentences whose judgments the grading predicts, with their forms. -/
def rows : List (Datum × Formula Unit (Option Role)) :=
  [(Examples.s8, 𝐩 ⋏ ∼B 𝐈 𝐩),
   (Examples.s9, 𝐩 ⋏ notKnowsWhether 𝐈 𝐩),
   (Examples.s28, 𝐩 ⋏ ∼B 𝐡 𝐩),
   (Examples.s30, B 𝐈 (𝐩 ⋏ ∼B 𝐈 𝐩)),
   (Examples.s30a, B 𝐈 (𝐩 ⋏ ∼B 𝐡 𝐩)),
   (Examples.s40, K 𝐈 (𝐩 ⋏ notKnowsWhether 𝐈 𝐩)),
   (Examples.s42, K 𝐡 𝐩 ⋏ ∼K 𝐈 𝐩),
   (Examples.s43, knowsWhether 𝐡 𝐩 ⋏ ∼knowsWhether 𝐈 𝐩),
   (Examples.s47, B 𝐈 𝐩 ⋏ ∼K 𝐈 𝐩),
   (Examples.s49, B 𝐈 𝐩 ⋏ ∼K 𝐈 (B 𝐈 𝐩)),
   (Examples.s51, B 𝐈 𝐩 ⋏ P 𝐈 ∼𝐩),
   (Examples.s52, 𝐩 ⋏ ∼K 𝐲 𝐩),
   (Examples.s56, 𝐩 ⋏ ∼K 𝐈 𝐩),
   (Examples.s61, K 𝐡 (K 𝐈 𝐩)),
   (Examples.s62, K 𝐈 𝐩),
   (Examples.s71, K 𝐈 𝐩 ⋏ ∼K 𝐈 (K 𝐈 𝐩))]

/-- The judged sentences whose judgments depart from the grading, with their forms. -/
def departures : List (Datum × Formula Unit (Option Role)) :=
  [(Examples.s46, B 𝐈 (𝐩 ⋏ notKnowsWhether 𝐈 𝐩)),
   (Examples.prize, 𝐩 ⋏ ∼K 𝐲 𝐩),
   (Examples.s55, 𝐩 ⋏ ∼K 𝐈 𝐩),
   (Examples.s60, K 𝐈 (K 𝐈 𝐩)),
   (Examples.s70, K 𝐡 𝐩 ⋏ ∼K 𝐡 (K 𝐡 𝐩))]

/-- The judged sentences outside the language. -/
def unexpressed : List Datum := [Examples.s29, Examples.s57, Examples.s58, Examples.s59]

theorem rows_departures_unexpressed :
    (rows.map Prod.fst ++ departures.map Prod.fst ++ unexpressed).Perm Examples.all := by
  decide

/-- Hintikka's grading predicts the judgment of every judged sentence in the language but the
five departures. -/
theorem rows_judgment : ∀ r ∈ rows, predictedJudgment r.2 = r.1.judgment := by
  simp only [rows, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    and_true]
  refine ⟨predictedJudgment_of_doxasticallyIndefensible (doxasticallyIndefensible_moore 𝐈 𝐩),
    predictedJudgment_of_epistemicallyIndefensible
      (defensible_of_sat mUndecided (w := 0) (by decide))
      (.inl (indefensible_K_moore_whether 𝐈 𝐩)),
    predictedJudgment_of_sat mThird (w := 0) (by decide),
    predictedJudgment_of_doxasticallyIndefensible
      (indefensible_B_moore 𝐈 𝐩).doxasticallyIndefensible,
    predictedJudgment_of_sat mThird (w := 0) (by decide),
    predictedJudgment_of_doxasticallyIndefensible
      (indefensible_K_moore_whether 𝐈 𝐩).doxasticallyIndefensible,
    predictedJudgment_of_epistemicallyIndefensible
      (defensible_of_sat mUndecided (w := 0) (by decide))
      (.inl (epistemicallyIndefensible_K_neg_K 𝐡 𝐈 𝐩)),
    predictedJudgment_of_sat mUndecided (w := 0) (by decide),
    predictedJudgment_of_sat mUndecided (w := 0) (by decide),
    predictedJudgment_of_epistemicallyIndefensible
      (defensible_of_sat model45 (w := 0) (by decide)) (.inl (indefensible_K_moore 𝐈 (B 𝐈 𝐩))),
    predictedJudgment_of_sat mUndecided (w := 0) (by decide),
    predictedJudgment_of_epistemicallyIndefensible (defensible_of_sat mB (w := 1) (by decide))
      (.inr (indefensible_K_moore 𝐲 𝐩)),
    predictedJudgment_of_epistemicallyIndefensible defensible_B_neg_K
      (.inl (indefensible_K_moore 𝐈 𝐩)),
    predictedJudgment_of_sat mK (w := 1) (by decide),
    predictedJudgment_of_sat mK (w := 1) (by decide),
    predictedJudgment_of_doxasticallyIndefensible
      (indefensible_K_and_not_KK 𝐈 𝐩).doxasticallyIndefensible⟩

theorem departures_judgment : ∀ r ∈ departures, predictedJudgment r.2 ≠ r.1.judgment := by
  simp only [departures, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [predictedJudgment_of_sat mUndecided (w := 0) (by decide)]; decide
  · rw [predictedJudgment_of_epistemicallyIndefensible
      (defensible_of_sat mB (w := 1) (by decide)) (.inr (indefensible_K_moore 𝐲 𝐩))]; decide
  · rw [predictedJudgment_of_epistemicallyIndefensible defensible_B_neg_K
      (.inl (indefensible_K_moore 𝐈 𝐩))]; decide
  · rw [predictedJudgment_of_sat mK (w := 1) (by decide)]; decide
  · rw [predictedJudgment_of_doxasticallyIndefensible
      (indefensible_K_and_not_KK 𝐡 𝐩).doxasticallyIndefensible]; decide

end Hintikka1962
