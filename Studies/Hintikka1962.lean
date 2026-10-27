module

public import Linglib.Logic.Modal.Basic
public import Mathlib.Data.Set.Basic

/-!
# Hintikka (1962): Knowledge and Belief

This file formalizes the model-set semantics of [hintikka-1962] for the operators "a knows
that", "it is possible, for all that a knows, that", "a believes that" and "it is compatible
with everything a believes that", and the book's applications of it to Moore's sentence "p but
I do not believe that p" and to knowing that one knows. A `ModelSystem` is a set of model
sets, partial descriptions of states of affairs closed under the (C) conditions of Chapter 3,
with epistemic and doxastic alternativeness relations between them; a set of sentences is
`Defensible` when it can be embedded in a member of a model system, and a sentence
`VirtuallyImplies` another when the implication between them is self-sustaining. Chapter 4's
solution to Moore's problem is that the sentence is defensible but its believed form is not,
so that the sentence is `DoxasticallyIndefensible` for its speaker to utter; the reductive
arguments of the book are the proofs, one condition per step, and the model systems it
exhibits are possible-worlds models carried to model systems by `Model.toModelSystem`.
Chapter 5's equivalence of knowing and knowing that one knows, and the failure of its
doxastic counterpart in Section 5.10, close the file.

## Implementation notes

* Model systems carry the first of the combinations of conditions listed in Section 3.4,
  (C.K) with (C.KK*), and the belief conditions (C.b*), (C.B*) and (C.BB*) of Section 3.5;
  the reflexivity and transitivity of alternativeness that the book shows to be equivalent to
  these as far as defensibility is concerned are the frame conditions of `Model`, whose truth
  sets are model sets.
* Virtual implication is the self-sustenance of the material implication, as in Section 2.6;
  Section 3.10 is used in the direction from the indefensibility of the antecedent with the
  negated consequent to the self-sustenance of the implication, the only direction the
  reductive arguments need, since the failures of virtual implication are witnessed by models.
* Doxastic and epistemic indefensibility are defined for a sentence, the conjunction of the
  book's finite set of statements.

## References

* [hintikka-1962]
-/

@[expose] public section

namespace Hintikka1962

open ModalLogic SetRel

/-- The formulas of Section 1.6: atomic sentences, negation, conjunction, disjunction and the
epistemic operators `K a` ("a knows that"), `P a` ("it is possible, for all that a knows,
that"), `B a` ("a believes that") and `C a` ("it is compatible with everything a believes
that"). -/
inductive Formula (V A : Type*)
  | atom : V → Formula V A
  | neg : Formula V A → Formula V A
  | and : Formula V A → Formula V A → Formula V A
  | or : Formula V A → Formula V A → Formula V A
  | K : A → Formula V A → Formula V A
  | P : A → Formula V A → Formula V A
  | B : A → Formula V A → Formula V A
  | C : A → Formula V A → Formula V A

namespace Formula

variable {V A : Type*}

/-- Negation. -/
scoped notation:max "∼" p:66 => Formula.neg p
/-- Conjunction. -/
scoped infixl:65 " ⋏ " => Formula.and
/-- Disjunction. -/
scoped infixl:60 " ⋎ " => Formula.or

/-- Material implication, eliminated in terms of the other connectives. -/
def imp (p q : Formula V A) : Formula V A := ∼(p ⋏ ∼q)

@[inherit_doc] scoped infixr:55 " ⟹ " => Formula.imp

/-- (2)*: "a knows whether p", `K a p ⋎ K a ∼p`. -/
def knowsWhether (a : A) (p : Formula V A) : Formula V A := K a p ⋎ K a ∼p

/-- (4)*: "a does not know whether p", `∼K a p ⋏ ∼K a ∼p`. -/
def notKnowsWhether (a : A) (p : Formula V A) : Formula V A := ∼K a p ⋏ ∼K a ∼p

end Formula

open Formula

variable {V A W : Type*}

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
epistemic and a doxastic alternativeness relation, satisfying the starred conditions on
knowledge and belief and (C.dox), that doxastic alternatives are epistemic alternatives. -/
structure ModelSystem (V A : Type*) where
  /-- The model sets. -/
  sets : Set (Set (Formula V A))
  /-- Epistemic alternativeness with respect to an agent. -/
  epi : A → sets → sets → Prop
  /-- Doxastic alternativeness with respect to an agent. -/
  dox : A → sets → sets → Prop
  isModelSet : ∀ μ : sets, IsModelSet (μ : Set (Formula V A))
  /-- (C.P*) -/
  P_star : ∀ {a p} (μ : sets), P a p ∈ (μ : Set (Formula V A)) →
    ∃ ν, epi a μ ν ∧ p ∈ (ν : Set (Formula V A))
  /-- (C.KK*) -/
  KK_star : ∀ {a p} {μ ν : sets}, epi a μ ν → K a p ∈ (μ : Set (Formula V A)) →
    K a p ∈ (ν : Set (Formula V A))
  /-- (C.C*) -/
  C_star : ∀ {a p} (μ : sets), C a p ∈ (μ : Set (Formula V A)) →
    ∃ ν, dox a μ ν ∧ p ∈ (ν : Set (Formula V A))
  /-- (C.b*) -/
  b_star : ∀ {a p} (μ : sets), B a p ∈ (μ : Set (Formula V A)) →
    ∃ ν, dox a μ ν ∧ p ∈ (ν : Set (Formula V A))
  /-- (C.B*) -/
  B_star : ∀ {a p} {μ ν : sets}, dox a μ ν → B a p ∈ (μ : Set (Formula V A)) →
    p ∈ (ν : Set (Formula V A))
  /-- (C.BB*) -/
  BB_star : ∀ {a p} {μ ν : sets}, dox a μ ν → B a p ∈ (μ : Set (Formula V A)) →
    B a p ∈ (ν : Set (Formula V A))
  /-- (C.dox) -/
  dox_le_epi : ∀ a, dox a ≤ epi a

namespace ModelSystem

variable {S : ModelSystem V A} {a : A} {p : Formula V A} {μ ν : S.sets}

-- Section 3.4
theorem K_star (h : S.epi a μ ν) (hp : K a p ∈ (μ : Set (Formula V A))) :
    p ∈ (ν : Set (Formula V A)) :=
  (S.isModelSet ν).know (S.KK_star h hp)

-- Section 3.6
theorem KK_star_dox (h : S.dox a μ ν) (hp : K a p ∈ (μ : Set (Formula V A))) :
    K a p ∈ (ν : Set (Formula V A)) :=
  S.KK_star (S.dox_le_epi a μ ν h) hp

theorem K_star_dox (h : S.dox a μ ν) (hp : K a p ∈ (μ : Set (Formula V A))) :
    p ∈ (ν : Set (Formula V A)) :=
  (S.isModelSet ν).know (S.KK_star_dox h hp)

end ModelSystem

/-! ### Defensibility -/

/-- A set of sentences is defensible when it can be embedded in a member of a model system
(Section 3.3). -/
def Defensible (Γ : Set (Formula V A)) : Prop :=
  ∃ (S : ModelSystem V A) (μ : S.sets), Γ ⊆ (μ : Set (Formula V A))

/-- Indefensibility, the book's reinterpretation of inconsistency (Section 2.6). -/
def Indefensible (Γ : Set (Formula V A)) : Prop := ¬ Defensible Γ

/-- A sentence is self-sustaining when its negation is indefensible (Section 2.6). -/
def SelfSustaining (p : Formula V A) : Prop := Indefensible {∼p}

/-- `p` virtually implies `q` when `p ⟹ q` is self-sustaining (Section 2.6). -/
def VirtuallyImplies (p q : Formula V A) : Prop := SelfSustaining (p ⟹ q)

/-- Virtual equivalence: virtual implication in both directions. -/
def VirtuallyEquivalent (p q : Formula V A) : Prop :=
  VirtuallyImplies p q ∧ VirtuallyImplies q p

-- Section 3.10
theorem virtuallyImplies_of_indefensible {p q : Formula V A} (h : Indefensible {p, ∼q}) :
    VirtuallyImplies p q := by
  rintro ⟨S, μ, hμ⟩
  have h₁ := (S.isModelSet μ).and ((S.isModelSet μ).neg_neg (hμ (Set.mem_singleton _)))
  exact h ⟨S, μ, by rintro _ (rfl | rfl) <;> [exact h₁.1; exact h₁.2]⟩

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

/-! ### Possible-worlds models

Section 2.8 glosses the notions in terms of worlds "in which everybody follows the
consequences of what he knows as far as they lead him": a model is a set of such worlds with
epistemic alternativeness reflexive and transitive, doxastic alternativeness serial and
transitive, and doxastic alternatives among the epistemic ones, the frame conditions that the
book shows to be equivalent to its conditions (Sections 3.4 to 3.6). The formulas true at a
world form a model set, and the truth sets of a model form a model system, so that
satisfiability in a model yields defensibility. -/

/-- A possible-worlds model of the epistemic language. -/
structure Model (V A W : Type*) where
  /-- Epistemic alternativeness. -/
  epi : A → SetRel W W
  /-- Doxastic alternativeness. -/
  dox : A → SetRel W W
  /-- Valuation of the atomic sentences. -/
  val : V → W → Prop
  epi_refl : ∀ a, (epi a).IsRefl
  epi_trans : ∀ a, (epi a).IsTrans
  dox_serial : ∀ a, IsSerial (dox a)
  dox_trans : ∀ a, (dox a).IsTrans
  dox_le_epi : ∀ a, dox a ⊆ epi a

namespace Model

variable (M : Model V A W)

/-- Satisfaction: the epistemic operators are `box` and `diamond` over the agent's
alternativeness. -/
def Sat : Formula V A → W → Prop
  | .atom v, w => M.val v w
  | .neg p, w => ¬ Sat p w
  | .and p q, w => Sat p w ∧ Sat q w
  | .or p q, w => Sat p w ∨ Sat q w
  | .K a p, w => □[M.epi a] (Sat p) w
  | .P a p, w => ◇[M.epi a] (Sat p) w
  | .B a p, w => □[M.dox a] (Sat p) w
  | .C a p, w => ◇[M.dox a] (Sat p) w

/-- The formulas true at a world. -/
def truthSet (w : W) : Set (Formula V A) := {p | M.Sat p w}

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
def toModelSystem : ModelSystem V A where
  sets := Set.range M.truthSet
  epi a μ ν := ∃ w v, M.truthSet w = μ ∧ M.truthSet v = ν ∧ w ~[M.epi a] v
  dox a μ ν := ∃ w v, M.truthSet w = μ ∧ M.truthSet v = ν ∧ w ~[M.dox a] v
  isModelSet := by rintro ⟨_, w, rfl⟩; exact M.isModelSet_truthSet w
  P_star := by
    rintro a p ⟨_, w, rfl⟩ ⟨v, hv, hp⟩
    exact ⟨⟨_, v, rfl⟩, ⟨w, v, rfl, rfl, hv⟩, hp⟩
  KK_star := by
    rintro a p ⟨_, w₀, rfl⟩ ⟨_, v₀, rfl⟩ ⟨w, v, hw, hv, hwv⟩ h
    have h' : K a p ∈ M.truthSet w := hw ▸ h
    have hv' : M.truthSet v = M.truthSet v₀ := hv
    show K a p ∈ M.truthSet v₀
    rw [← hv']
    exact λ u hvu => h' u ((M.epi_trans a).trans _ _ _ hwv hvu)
  C_star := by
    rintro a p ⟨_, w, rfl⟩ ⟨v, hv, hp⟩
    exact ⟨⟨_, v, rfl⟩, ⟨w, v, rfl, rfl, hv⟩, hp⟩
  b_star := by
    rintro a p ⟨_, w, rfl⟩ h
    obtain ⟨v, hv⟩ := (M.dox_serial a).serial w
    exact ⟨⟨_, v, rfl⟩, ⟨w, v, rfl, rfl, hv⟩, h v hv⟩
  B_star := by
    rintro a p ⟨_, w₀, rfl⟩ ⟨_, v₀, rfl⟩ ⟨w, v, hw, hv, hwv⟩ h
    have h' : B a p ∈ M.truthSet w := hw ▸ h
    have hv' : M.truthSet v = M.truthSet v₀ := hv
    show p ∈ M.truthSet v₀
    rw [← hv']
    exact h' v hwv
  BB_star := by
    rintro a p ⟨_, w₀, rfl⟩ ⟨_, v₀, rfl⟩ ⟨w, v, hw, hv, hwv⟩ h
    have h' : B a p ∈ M.truthSet w := hw ▸ h
    have hv' : M.truthSet v = M.truthSet v₀ := hv
    show B a p ∈ M.truthSet v₀
    rw [← hv']
    exact λ u hvu => h' u ((M.dox_trans a).trans _ _ _ hwv hvu)
  dox_le_epi := by
    rintro a μ ν ⟨w, v, hw, hv, hwv⟩
    exact ⟨w, v, hw, hv, M.dox_le_epi a hwv⟩

theorem defensible_of_subset_truthSet {Γ : Set (Formula V A)} {w : W}
    (h : Γ ⊆ M.truthSet w) : Defensible Γ :=
  ⟨M.toModelSystem, ⟨_, w, rfl⟩, h⟩

theorem defensible_of_sat {p : Formula V A} {w : W} (h : M.Sat p w) : Defensible {p} :=
  M.defensible_of_subset_truthSet (Set.singleton_subset_iff.mpr h)

theorem not_virtuallyImplies_of_sat {p q : Formula V A} {w : W} (h : M.Sat (p ⋏ ∼q) w) :
    ¬ VirtuallyImplies p q :=
  not_not_intro (M.defensible_of_sat (not_not_intro h))

section Decidable

variable [Fintype W] [∀ a w v, Decidable (w ~[M.epi a] v)] [∀ a w v, Decidable (w ~[M.dox a] v)]
  [∀ v, DecidablePred (M.val v)]

/-- Satisfaction is decidable over finitely many worlds. -/
def decSat : ∀ (p : Formula V A) (w : W), Decidable (M.Sat p w)
  | .atom v, w => inferInstanceAs (Decidable (M.val v w))
  | .neg p, w => haveI := decSat p w; inferInstanceAs (Decidable (¬ M.Sat p w))
  | .and p q, w =>
    haveI := decSat p w; haveI := decSat q w
    inferInstanceAs (Decidable (M.Sat p w ∧ M.Sat q w))
  | .or p q, w =>
    haveI := decSat p w; haveI := decSat q w
    inferInstanceAs (Decidable (M.Sat p w ∨ M.Sat q w))
  | .K a p, w =>
    haveI : DecidablePred (M.Sat p) := decSat p
    inferInstanceAs (Decidable (□[M.epi a] (M.Sat p) w))
  | .P a p, w =>
    haveI : DecidablePred (M.Sat p) := decSat p
    inferInstanceAs (Decidable (◇[M.epi a] (M.Sat p) w))
  | .B a p, w =>
    haveI : DecidablePred (M.Sat p) := decSat p
    inferInstanceAs (Decidable (□[M.dox a] (M.Sat p) w))
  | .C a p, w =>
    haveI : DecidablePred (M.Sat p) := decSat p
    inferInstanceAs (Decidable (◇[M.dox a] (M.Sat p) w))

instance (p : Formula V A) (w : W) : Decidable (M.Sat p w) := M.decSat p w

end Decidable

end Model

/-! ### Chapter 3: consequences and rejected conditions

(C.KB), that whatever is known is believed to be known, follows from (C.dox) (Section 3.6).
(C.BK), that whatever is believed is known to be believed, would make "a believes that p"
virtually imply "a knows that it is possible, for all a knows, that p", and (C.PK), that
whatever is possible is known to be possible, would make (13) self-sustaining; neither is a
consequence of the conditions (Sections 3.7 and 3.8). -/

variable (a b : A) (p : Formula V A)

theorem virtuallyImplies_K_B_K : VirtuallyImplies (K a p) (B a (K a p)) :=
  virtuallyImplies_of_indefensible <| by
    rintro ⟨S, μ, hμ⟩
    obtain ⟨ν, hν, h⟩ := S.C_star μ ((S.isModelSet μ).neg_believe
      (hμ (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
    exact (S.isModelSet ν).neg (S.KK_star_dox hν (hμ (Set.mem_insert _ _))) h

section Countermodels

/-- The countermodels: one atomic sentence, two agents and three worlds. -/
local notation "𝐩" => (Formula.atom () : Formula Unit (Fin 2))

/-- A model in which belief and knowledge diverge: from world `0` the doxastic alternative is
`1` and the epistemic alternatives are all three worlds, each other world being its own only
alternative; the atom holds at `0` and `1`. -/
abbrev mK : Model Unit (Fin 2) (Fin 3) where
  epi _ := {p | p.1 = p.2 ∨ p.1 = 0}
  dox _ := {p | (p.1 = 0 ∧ p.2 = 1) ∨ (p.1 ≠ 0 ∧ p.1 = p.2)}
  val _ w := w ≠ 2
  epi_refl _ := ⟨by decide +revert⟩
  epi_trans _ := ⟨by decide +revert⟩
  dox_serial _ := ⟨λ _ => by decide +revert⟩
  dox_trans _ := ⟨by decide +revert⟩
  dox_le_epi a := by rintro ⟨w, v⟩ h; revert a w v h; decide

theorem not_virtuallyImplies_B_K_P : ¬ VirtuallyImplies (B 0 𝐩) (K 0 (P 0 𝐩)) :=
  mK.not_virtuallyImplies_of_sat (w := 0) (by decide)

-- Section 3.7
theorem not_virtuallyImplies_B_K_B : ¬ VirtuallyImplies (B 0 𝐩) (K 0 (B 0 𝐩)) :=
  mK.not_virtuallyImplies_of_sat (w := 0) (by decide)

-- (13)
theorem not_virtuallyImplies_K_P : ¬ VirtuallyImplies 𝐩 (K 0 (P 0 𝐩)) :=
  mK.not_virtuallyImplies_of_sat (w := 0) (by decide)

end Countermodels

/-! ### Chapter 4: knowing that others know -/

-- (20), Sections 4.1 and 4.2
theorem virtuallyImplies_K_K_K : VirtuallyImplies (K a (K b p)) (K a p) :=
  virtuallyImplies_of_indefensible <| by
    rintro ⟨S, μ, hμ⟩
    obtain ⟨ν, hν, h⟩ := S.P_star μ ((S.isModelSet μ).neg_know
      (hμ (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
    exact (S.isModelSet ν).neg
      ((S.isModelSet ν).know (S.K_star hν (hμ (Set.mem_insert _ _)))) h

section Countermodels

local notation "𝐩" => (Formula.atom () : Formula Unit (Fin 2))

/-- A model of belief: from world `0` agent `0` considers `1` and `2` doxastically possible,
from the other worlds only `1`; agent `1` always considers only `0` possible; knowledge is
trivial; the atom holds at `0` and `1`. -/
abbrev mB : Model Unit (Fin 2) (Fin 3) where
  epi _ := .univ
  dox a := {p | (a = 0 ∧ ((p.1 = 0 ∧ p.2 ≠ 0) ∨ (p.1 ≠ 0 ∧ p.2 = 1))) ∨ (a = 1 ∧ p.2 = 0)}
  val _ w := w ≠ 2
  epi_refl _ := ⟨λ _ => trivial⟩
  epi_trans _ := ⟨λ _ _ _ _ _ => trivial⟩
  dox_serial _ := ⟨λ _ => by decide +revert⟩
  dox_trans _ := ⟨by decide +revert⟩
  dox_le_epi _ _ _ := trivial

-- (27), Section 4.3
theorem not_virtuallyImplies_B_B_B : ¬ VirtuallyImplies (B 0 (B 1 𝐩)) (B 0 𝐩) :=
  mB.not_virtuallyImplies_of_sat (w := 0) (by decide)

-- Section 4.4
theorem not_virtuallyImplies_B_K_K : ¬ VirtuallyImplies (B 0 (K 1 𝐩)) (K 0 𝐩) :=
  mK.not_virtuallyImplies_of_sat (w := 0) (by decide)

end Countermodels

/-! ### Chapter 4: Moore's problem

Moore's sentence (8), "p but I do not believe that p", is defensible, but (30)*, its believed
form, is not: what uttering (8) violates is the presumption that the speaker can believe what
he says (Sections 4.5 and 4.6). The believed form of the third-person variant (8)(a) is
defensible unless the believer is the person spoken about. -/

/-- The model of Section 4.6's discussion of (8) and (8)(a): two states of affairs, the atom
true in the first; every agent believes only the second, except `a`, who believes only the
first. -/
def mooreModel : Model V A Bool where
  epi _ := .univ
  dox c := {p | (c = a ∧ p.2 = false) ∨ (c ≠ a ∧ p.2 = true)}
  val _ w := w = true
  epi_refl _ := ⟨λ _ => trivial⟩
  epi_trans _ := ⟨λ _ _ _ _ _ => trivial⟩
  dox_serial c := ⟨λ _ => by
    by_cases h : c = a
    · exact ⟨false, Or.inl ⟨h, rfl⟩⟩
    · exact ⟨true, Or.inr ⟨h, rfl⟩⟩⟩
  dox_trans _ := ⟨λ _ _ _ _ h => h⟩
  dox_le_epi _ _ _ := trivial

-- (8)
theorem defensible_moore (v : V) : Defensible {(atom v : Formula V A) ⋏ ∼B a (atom v)} :=
  (mooreModel a).defensible_of_sat (w := true)
    ⟨rfl, λ h => Bool.false_ne_true (h false (Or.inl ⟨rfl, rfl⟩))⟩

-- (30), (8)
theorem defensible_B_moore_of_ne (hab : b ≠ a) (v : V) :
    Defensible {B b ((atom v : Formula V A) ⋏ ∼B a (atom v))} :=
  (mooreModel a).defensible_of_sat (w := true) λ x hx => by
    rcases hx with ⟨rfl, _⟩ | ⟨_, rfl⟩
    · exact absurd rfl hab
    · exact ⟨rfl, λ h => Bool.false_ne_true (h false (Or.inl ⟨rfl, rfl⟩))⟩

-- (30), (33), (39)
theorem indefensible_B_moore : Indefensible {B a (p ⋏ ∼B a p)} := by
  rintro ⟨S, μ, hμ⟩
  obtain ⟨ν, hν, h₁⟩ := S.b_star μ (hμ (Set.mem_singleton _))
  have h₂ := S.BB_star hν (hμ (Set.mem_singleton _))
  obtain ⟨ξ, hξ, h₃⟩ :=
    S.C_star ν ((S.isModelSet ν).neg_believe ((S.isModelSet ν).and h₁).2)
  exact (S.isModelSet ξ).neg ((S.isModelSet ξ).and (S.B_star hξ h₂)).1 h₃

-- Section 4.7
theorem indefensible_moore_and_B_moore : Indefensible {(p ⋏ ∼B a p) ⋏ B a (p ⋏ ∼B a p)} := by
  rintro ⟨S, μ, hμ⟩
  obtain ⟨h₁, h₂⟩ := (S.isModelSet μ).and (hμ (Set.mem_singleton _))
  obtain ⟨ν, hν, h₃⟩ :=
    S.C_star μ ((S.isModelSet μ).neg_believe ((S.isModelSet μ).and h₁).2)
  exact (S.isModelSet ν).neg ((S.isModelSet ν).and (S.B_star hν h₂)).1 h₃

-- Section 4.8, (8)
theorem doxasticallyIndefensible_moore : DoxasticallyIndefensible a (p ⋏ ∼B a p) :=
  indefensible_B_moore a p

-- Section 4.9
theorem doxasticallyImplies_B : DoxasticallyImplies a p (B a p) :=
  indefensible_B_moore a p

/-! ### Chapter 4: the analogue for knowledge

(9), "p but I do not know whether p", is (4)*'s `p ⋏ notKnowsWhether a p`; its known form
(40)* and the simpler (41) are indefensible without (C.KK*), so that any sentence implies "I
know it" epistemically (Sections 4.11 to 4.13). Knowledge and belief come apart in (44) and
(45) (Section 4.14). -/

-- (41)
theorem indefensible_K_moore : Indefensible {K a (p ⋏ ∼K a p)} := by
  rintro ⟨S, μ, hμ⟩
  have h₁ := (S.isModelSet μ).and ((S.isModelSet μ).know (hμ (Set.mem_singleton _)))
  obtain ⟨ν, hν, h₂⟩ := S.P_star μ ((S.isModelSet μ).neg_know h₁.2)
  exact (S.isModelSet ν).neg
    ((S.isModelSet ν).and (S.K_star hν (hμ (Set.mem_singleton _)))).1 h₂

-- (40), (9)
theorem indefensible_K_moore_whether : Indefensible {K a (p ⋏ notKnowsWhether a p)} := by
  rintro ⟨S, μ, hμ⟩
  have h₁ := (S.isModelSet μ).and ((S.isModelSet μ).know (hμ (Set.mem_singleton _)))
  obtain ⟨ν, hν, h₂⟩ :=
    S.P_star μ ((S.isModelSet μ).neg_know ((S.isModelSet μ).and h₁.2).1)
  exact (S.isModelSet ν).neg
    ((S.isModelSet ν).and (S.K_star hν (hμ (Set.mem_singleton _)))).1 h₂

-- Section 4.12
theorem epistemicallyImplies_K : EpistemicallyImplies a p (K a p) :=
  indefensible_K_moore a p

-- (42), Section 4.13
theorem epistemicallyIndefensible_K_neg_K : EpistemicallyIndefensible b (K a p ⋏ ∼K b p) := by
  rintro ⟨S, μ, hμ⟩
  have h₁ := (S.isModelSet μ).and ((S.isModelSet μ).know (hμ (Set.mem_singleton _)))
  obtain ⟨ν, hν, h₂⟩ := S.P_star μ ((S.isModelSet μ).neg_know h₁.2)
  exact (S.isModelSet ν).neg ((S.isModelSet ν).know
    ((S.isModelSet ν).and (S.K_star hν (hμ (Set.mem_singleton _)))).1) h₂

-- (44), Section 4.14
theorem indefensible_K_neg_B : Indefensible {K a (p ⋏ ∼B a p)} := by
  rintro ⟨S, μ, hμ⟩
  have h₁ := (S.isModelSet μ).and ((S.isModelSet μ).know (hμ (Set.mem_singleton _)))
  obtain ⟨ν, hν, h₂⟩ := S.C_star μ ((S.isModelSet μ).neg_believe h₁.2)
  exact (S.isModelSet ν).neg
    ((S.isModelSet ν).and (S.K_star_dox hν (hμ (Set.mem_singleton _)))).1 h₂

-- (46), (47)
theorem virtuallyImplies_B_and : VirtuallyImplies (B a (p ⋏ ∼K a p)) (B a p ⋏ ∼K a p) :=
  virtuallyImplies_of_indefensible <| by
    rintro ⟨S, μ, hμ⟩
    have h₀ := hμ (Set.mem_insert _ _)
    rcases (S.isModelSet μ).neg_and (hμ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
      with h | h
    · obtain ⟨ν, hν, h₁⟩ := S.C_star μ ((S.isModelSet μ).neg_believe h)
      exact (S.isModelSet ν).neg ((S.isModelSet ν).and (S.B_star hν h₀)).1 h₁
    · obtain ⟨ν, hν, h₁⟩ := S.b_star μ h₀
      exact (S.isModelSet ν).neg (S.KK_star_dox hν ((S.isModelSet μ).neg_neg h))
        ((S.isModelSet ν).and h₁).2

-- (47), (46)
theorem doxasticallyImplies_B_of_and :
    DoxasticallyImplies a (B a p ⋏ ∼K a p) (B a (p ⋏ ∼K a p)) := by
  rintro ⟨S, μ, hμ⟩
  have h₀ := hμ (Set.mem_singleton _)
  obtain ⟨ν, hν, h₁⟩ := S.b_star μ h₀
  obtain ⟨h₂, h₃⟩ := (S.isModelSet ν).and h₁
  obtain ⟨ξ, hξ, h₄⟩ := S.C_star ν ((S.isModelSet ν).neg_believe h₃)
  rcases (S.isModelSet ξ).neg_and h₄ with h | h
  · exact (S.isModelSet ξ).neg (S.B_star hξ ((S.isModelSet ν).and h₂).1) h
  · have h₅ := ((S.isModelSet ξ).and (S.B_star hξ (S.BB_star hν h₀))).1
    exact (S.isModelSet ξ).neg ((S.isModelSet ξ).neg_neg h) ((S.isModelSet ξ).and h₅).2

section Countermodels

local notation "𝐩" => (Formula.atom () : Formula Unit (Fin 2))

/-- A model in which every world is epistemically possible from every world while only world
`1`, where the atom holds, is doxastically possible. -/
abbrev mKB : Model Unit (Fin 2) (Fin 3) where
  epi _ := .univ
  dox _ := {p | p.2 = 1}
  val _ w := w = 1
  epi_refl _ := ⟨λ _ => trivial⟩
  epi_trans _ := ⟨λ _ _ _ _ _ => trivial⟩
  dox_serial _ := ⟨λ _ => ⟨1, rfl⟩⟩
  dox_trans _ := ⟨λ _ _ _ _ h => h⟩
  dox_le_epi _ _ _ := trivial

/-- A model in which agent `0` knows whether the atom holds and agent `1` does not. -/
abbrev mWhether : Model Unit (Fin 2) (Fin 3) where
  epi a := {p | (a = 0 ∧ p.1 = p.2) ∨ a = 1}
  dox _ := {p | p.1 = p.2}
  val _ w := w = 1
  epi_refl _ := ⟨by decide +revert⟩
  epi_trans _ := ⟨by decide +revert⟩
  dox_serial _ := ⟨λ w => ⟨w, rfl⟩⟩
  dox_trans _ := ⟨λ _ _ _ h h' => h.trans h'⟩
  dox_le_epi a := by rintro ⟨w, v⟩ h; revert a w v h; decide

-- (43), Section 4.13
theorem defensible_K_knowsWhether :
    Defensible {K 1 (knowsWhether 0 𝐩 ⋏ ∼knowsWhether 1 𝐩)} :=
  mWhether.defensible_of_sat (w := 0) (by decide)

-- (45), Section 4.14
theorem defensible_B_neg_K : Defensible {B 0 (𝐩 ⋏ ∼K 0 𝐩)} :=
  mB.defensible_of_sat (w := 1) (by decide)

-- (48), (47)
theorem defensible_K_B_neg_K : Defensible {K 0 (B 0 𝐩 ⋏ ∼K 0 𝐩)} :=
  mKB.defensible_of_sat (w := 0) (by decide)

-- (51), Section 4.16
theorem defensible_K_B_P : Defensible {K 0 (B 0 𝐩 ⋏ P 0 ∼𝐩)} :=
  mKB.defensible_of_sat (w := 0) (by decide)

-- (51)
theorem defensible_B_B_P : Defensible {B 0 (B 0 𝐩 ⋏ P 0 ∼𝐩)} :=
  mKB.defensible_of_sat (w := 0) (by decide)

end Countermodels

-- (51), Section 4.16
theorem epistemicallyIndefensible_P : EpistemicallyIndefensible a (p ⋏ P a ∼p) := by
  rintro ⟨S, μ, hμ⟩
  obtain ⟨ν, hν, h₁⟩ :=
    S.P_star μ ((S.isModelSet μ).and ((S.isModelSet μ).know (hμ (Set.mem_singleton _)))).2
  exact (S.isModelSet ν).neg
    ((S.isModelSet ν).and (S.K_star hν (hμ (Set.mem_singleton _)))).1 h₁

-- (51)
theorem epistemicallyIndefensible_C : EpistemicallyIndefensible a (p ⋏ C a ∼p) := by
  rintro ⟨S, μ, hμ⟩
  obtain ⟨ν, hν, h₁⟩ :=
    S.C_star μ ((S.isModelSet μ).and ((S.isModelSet μ).know (hμ (Set.mem_singleton _)))).2
  exact (S.isModelSet ν).neg
    ((S.isModelSet ν).and (S.K_star_dox hν (hμ (Set.mem_singleton _)))).1 h₁

-- (51)
theorem doxasticallyIndefensible_C : DoxasticallyIndefensible a (p ⋏ C a ∼p) := by
  rintro ⟨S, μ, hμ⟩
  obtain ⟨ν, hν, h₁⟩ := S.b_star μ (hμ (Set.mem_singleton _))
  obtain ⟨ξ, hξ, h₂⟩ := S.C_star ν ((S.isModelSet ν).and h₁).2
  exact (S.isModelSet ξ).neg
    ((S.isModelSet ξ).and (S.B_star hξ (S.BB_star hν (hμ (Set.mem_singleton _))))).1 h₂

-- (51)
theorem indefensible_B_C : Indefensible {B a p ⋏ C a ∼p} := by
  rintro ⟨S, μ, hμ⟩
  obtain ⟨h₁, h₂⟩ := (S.isModelSet μ).and (hμ (Set.mem_singleton _))
  obtain ⟨ν, hν, h₃⟩ := S.C_star μ h₂
  exact (S.isModelSet ν).neg (S.B_star hν h₁) h₃

/-! ### Chapter 5: knowing that one knows -/

-- (65), (69), Section 5.2
theorem virtuallyImplies_K_KK : VirtuallyImplies (K a p) (K a (K a p)) :=
  virtuallyImplies_of_indefensible <| by
    rintro ⟨S, μ, hμ⟩
    obtain ⟨ν, hν, h⟩ := S.P_star μ ((S.isModelSet μ).neg_know
      (hμ (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
    exact (S.isModelSet ν).neg (S.KK_star hν (hμ (Set.mem_insert _ _))) h

theorem virtuallyImplies_KK_K : VirtuallyImplies (K a (K a p)) (K a p) :=
  virtuallyImplies_of_indefensible <| by
    rintro ⟨S, μ, hμ⟩
    exact (S.isModelSet μ).neg ((S.isModelSet μ).know (hμ (Set.mem_insert _ _)))
      (hμ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

-- (63), (64), Section 5.4
theorem virtuallyEquivalent_K_KK : VirtuallyEquivalent (K a p) (K a (K a p)) :=
  ⟨virtuallyImplies_K_KK a p, virtuallyImplies_KK_K a p⟩

-- (72), (73), Section 5.10
theorem virtuallyImplies_B_BB : VirtuallyImplies (B a p) (B a (B a p)) :=
  virtuallyImplies_of_indefensible <| by
    rintro ⟨S, μ, hμ⟩
    obtain ⟨ν, hν, h⟩ := S.C_star μ ((S.isModelSet μ).neg_believe
      (hμ (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
    exact (S.isModelSet ν).neg (S.BB_star hν (hμ (Set.mem_insert _ _))) h

section Countermodels

local notation "𝐩" => (Formula.atom () : Formula Unit (Fin 2))

-- Section 5.2
theorem not_virtuallyImplies_negK_K_negK : ¬ VirtuallyImplies (∼K 0 𝐩) (K 0 ∼K 0 𝐩) :=
  mK.not_virtuallyImplies_of_sat (w := 0) (by decide)

-- Section 5.10, (73), (72)
theorem not_virtuallyImplies_BB_B : ¬ VirtuallyImplies (B 0 (B 0 𝐩)) (B 0 𝐩) :=
  mB.not_virtuallyImplies_of_sat (w := 0) (by decide)

end Countermodels

end Hintikka1962
