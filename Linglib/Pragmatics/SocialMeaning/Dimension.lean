module

public import Linglib.Core.Combinatorics.SimpleGraph.MaximalIndepSet
public import Mathlib.Basic.Sign.Defs
public import Mathlib.Combinatorics.SimpleGraph.CompleteMultipartite

/-!
# Dimensions of social evaluation

This file characterizes the incompatibility relations that come from dimensions, and defines the
dimensions on which hearers evaluate a speaker. Burnett's incompatibility relation on properties
is any graph. It comes from dimensions, two properties being incompatible when they are distinct
values of one, exactly when its complement, the compatibility graph, is complete multipartite,
the dimensions being the parts; a persona, a maximal set of compatible properties, then takes
one property of each part. The dimensions of social evaluation are competence and warmth, the two
universal dimensions of social cognition of the Stereotype Content Model, and anti-solidarity,
the factor of Beltrama, Solt and Burnett's ratings that loads apart from warmth, and their values
are their two poles.

## Main definitions

* `SocialMeaning.dimensionalIncompatibility`: the graph joining distinct values of one dimension.
* `Dimension`: competence, warmth and anti-solidarity.
* `Pole`: the six ends of the dimensions, with `Pole.dimension` and `Pole.polarity`.
* `Pole.opposite`: the other end of a pole's dimension.

## Main results

* `SocialMeaning.isCompleteMultipartite_compl_iff`: an incompatibility graph comes from
  dimensions exactly when its compatibility graph is complete multipartite.
* `SocialMeaning.mem_maximalIndepSets_iff_of_isCompleteMultipartite_compl`: the personae are then
  the sets with exactly one property of each part.
* `Pole.eq_iff`: a pole is determined by its dimension and polarity.
* `Pole.incompatible_adj_iff`: two poles are incompatible when one is opposite the other.

## References

* [fiske-cuddy-glick-xu-2002]
* [fiske-cuddy-glick-2007]
* [beltrama-solt-burnett-2023]
* [burnett-2019]
-/

@[expose] public section

namespace SocialMeaning

section Dimensional

universe u

variable {P : Type u} {D : Type*} {dim : P → D} {G : SimpleGraph P}

theorem mem_maximalIndepSets_iff_of_isCompleteMultipartite_compl [Fintype P] [DecidableEq P]
    [DecidableRel G.Adj] (h : Gᶜ.IsCompleteMultipartite) {s : Finset P} :
    s ∈ G.maximalIndepSets ↔ ∀ p, (s.filter fun q ↦ q = p ∨ G.Adj q p).card = 1 := by
  have hr (a b : P) : ¬Gᶜ.Adj a b ↔ a = b ∨ G.Adj a b := by
    simp [SimpleGraph.compl_adj, or_iff_not_imp_left]
  have trans {a b c : P} (hab : a = b ∨ G.Adj a b) (hbc : b = c ∨ G.Adj b c) :
      a = c ∨ G.Adj a c :=
    (hr a c).1 (h.trans a b c ((hr a b).2 hab) ((hr b c).2 hbc))
  simp only [SimpleGraph.mem_maximalIndepSets,
    SimpleGraph.maximal_isIndepSet_iff_forall_exists_adj, SimpleGraph.IsIndepSet, Set.Pairwise,
    Finset.mem_coe, ← Nat.le_antisymm_iff.symm, Finset.card_le_one, Finset.one_le_card,
    Finset.Nonempty, Finset.mem_filter, forall_and]
  refine and_congr ⟨fun hs p a ha b hb ↦ ?_, fun hs a ha b hb hab hadj ↦
    hab (hs a a ⟨ha, .inl rfl⟩ b ⟨hb, .inr hadj.symm⟩)⟩ ⟨fun hd p ↦ ?_, fun hd v hv ↦ ?_⟩
  · by_contra hne
    exact (trans ha.2 (hb.2.imp Eq.symm (·.symm))).elim hne (hs ha.1 hb.1 hne)
  · by_cases hp : p ∈ s
    · exact ⟨p, hp, .inl rfl⟩
    · obtain ⟨w, hw, hadj⟩ := hd p hp
      exact ⟨w, hw, .inr hadj.symm⟩
  · obtain ⟨w, hw, rfl | hadj⟩ := hd v
    · exact absurd hw hv
    · exact ⟨w, hw, hadj.symm⟩

/-- The incompatibility of a family of dimensions joins two properties when they are distinct
values of one dimension. -/
def dimensionalIncompatibility (dim : P → D) : SimpleGraph P where
  Adj p q := p ≠ q ∧ dim p = dim q
  symm := ⟨fun _ _ h ↦ ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

@[simp] theorem dimensionalIncompatibility_adj {p q : P} :
    (dimensionalIncompatibility dim).Adj p q ↔ p ≠ q ∧ dim p = dim q := Iff.rfl

instance [DecidableEq P] [DecidableEq D] : DecidableRel (dimensionalIncompatibility dim).Adj :=
  fun _ _ ↦ inferInstanceAs (Decidable (_ ∧ _))

theorem compl_dimensionalIncompatibility :
    (dimensionalIncompatibility dim)ᶜ = (⊤ : SimpleGraph D).comap dim := by
  ext p q
  simp only [SimpleGraph.compl_adj, dimensionalIncompatibility_adj, SimpleGraph.comap_adj,
    SimpleGraph.top_adj]
  exact ⟨fun ⟨hne, h⟩ hd ↦ h ⟨hne, hd⟩, fun hd ↦ ⟨fun e ↦ hd (congrArg dim e), fun h ↦ hd h.2⟩⟩

theorem isCompleteMultipartite_compl_dimensionalIncompatibility :
    (dimensionalIncompatibility dim)ᶜ.IsCompleteMultipartite := by
  rw [compl_dimensionalIncompatibility]
  exact ⟨fun _ _ _ hab hbc ↦ by simp_all⟩

theorem isCompleteMultipartite_compl_iff :
    Gᶜ.IsCompleteMultipartite ↔
      ∃ (D : Type u) (dim : P → D), dimensionalIncompatibility dim = G := by
  refine ⟨fun h ↦ ⟨_, Quotient.mk h.setoid, ?_⟩, ?_⟩
  · ext p q
    simp only [dimensionalIncompatibility_adj, Quotient.eq]
    change p ≠ q ∧ ¬Gᶜ.Adj p q ↔ G.Adj p q
    rw [SimpleGraph.compl_adj]
    exact ⟨fun ⟨hne, h⟩ ↦ by_contra fun hn ↦ h ⟨hne, hn⟩, fun hadj ↦ ⟨hadj.ne, fun h ↦ h.2 hadj⟩⟩
  · rintro ⟨D, dim, rfl⟩
    exact isCompleteMultipartite_compl_dimensionalIncompatibility

theorem mem_maximalIndepSets_dimensionalIncompatibility_iff [Fintype P] [DecidableEq P]
    [DecidableEq D] {s : Finset P} :
    s ∈ (dimensionalIncompatibility dim).maximalIndepSets ↔
      ∀ p, (s.filter (dim · = dim p)).card = 1 := by
  rw [mem_maximalIndepSets_iff_of_isCompleteMultipartite_compl
    isCompleteMultipartite_compl_dimensionalIncompatibility]
  refine forall_congr' fun p ↦ ?_
  rw [Finset.filter_congr fun q _ ↦
    show q = p ∨ (dimensionalIncompatibility dim).Adj q p ↔ dim q = dim p from
      ⟨by rintro (rfl | h); exacts [rfl, h.2], fun h ↦ (eq_or_ne q p).imp_right (⟨·, h⟩)⟩]

end Dimensional

/-- The dimensions of social evaluation are competence and warmth, and anti-solidarity, the
factor on which pedantic and uptight load apart from the warmth scales. -/
inductive Dimension where
  | competence
  | warmth
  | antiSolidarity
  deriving DecidableEq

instance : Fintype Dimension :=
  ⟨{.competence, .warmth, .antiSolidarity}, fun d ↦ by cases d <;> simp⟩

/-- A pole is one end of a dimension of social evaluation. -/
inductive Pole where
  | competent
  | incompetent
  | warm
  | cold
  | solidary
  | antiSolidary
  deriving DecidableEq

instance : Fintype Pole :=
  ⟨{.competent, .incompetent, .warm, .cold, .solidary, .antiSolidary}, fun p ↦ by cases p <;> simp⟩

/-- The dimension a pole is an end of. -/
def Pole.dimension : Pole → Dimension
  | .competent | .incompetent => .competence
  | .warm | .cold => .warmth
  | .solidary | .antiSolidary => .antiSolidarity

/-- The polarity of a pole is positive at the end its dimension is named for, competent, warm
and antisolidary, and negative at the other. -/
def Pole.polarity : Pole → SignType
  | .competent | .warm | .antiSolidary => 1
  | .incompetent | .cold | .solidary => -1

theorem Pole.eq_iff {p q : Pole} :
    p = q ↔ p.dimension = q.dimension ∧ p.polarity = q.polarity := by
  revert p q; decide

/-- The other end of a pole's dimension. -/
def Pole.opposite : Pole → Pole
  | .competent => .incompetent
  | .incompetent => .competent
  | .warm => .cold
  | .cold => .warm
  | .solidary => .antiSolidary
  | .antiSolidary => .solidary

@[simp] theorem Pole.opposite_opposite (p : Pole) : p.opposite.opposite = p := by cases p <;> rfl

@[simp] theorem Pole.dimension_opposite (p : Pole) : p.opposite.dimension = p.dimension := by
  cases p <;> rfl

@[simp] theorem Pole.polarity_opposite (p : Pole) : p.opposite.polarity = -p.polarity := by
  cases p <;> rfl

/-- `Pole.opposite` as an involutive permutation. -/
def Pole.oppositeEquiv : Equiv.Perm Pole := Function.Involutive.toPerm _ Pole.opposite_opposite

@[simp] theorem Pole.oppositeEquiv_apply (p : Pole) : Pole.oppositeEquiv p = p.opposite := rfl

@[simp] theorem Pole.oppositeEquiv_symm : Pole.oppositeEquiv.symm = Pole.oppositeEquiv := rfl

theorem Pole.dimension_surjective : Function.Surjective Pole.dimension
  | .competence => ⟨.competent, rfl⟩
  | .warmth => ⟨.warm, rfl⟩
  | .antiSolidarity => ⟨.solidary, rfl⟩

theorem Pole.incompatible_adj_iff {p q : Pole} :
    (dimensionalIncompatibility Pole.dimension).Adj p q ↔ q = p.opposite := by
  revert p q; decide

theorem Pole.mem_maximalIndepSets_iff (s : Finset Pole) :
    s ∈ (dimensionalIncompatibility Pole.dimension).maximalIndepSets ↔
      ∀ d, (s.filter (·.dimension = d)).card = 1 :=
  mem_maximalIndepSets_dimensionalIncompatibility_iff.trans
    (Pole.dimension_surjective.forall (p := fun d ↦ (s.filter (·.dimension = d)).card = 1)).symm

end SocialMeaning
