module

public import Linglib.Phonology.OptimalityTheory.ElementaryRankingCondition.Antimatroid
public import Linglib.Phonology.OptimalityTheory.LinearExtension
public import Mathlib.Order.Concept

/-!
# Optimality-theoretic grammars

A set of elementary ranking conditions delimits the rankings that satisfy all of them, and a set
of rankings delimits the conditions that all of them satisfy. An Optimality-theoretic grammar over
`n` constraints is a set of rankings closed under this correspondence together with its
conditions: a formal concept of the satisfaction relation between rankings and ERCs. Its extent is
the set of its rankings, its legs, and its intent the set of ERCs they all satisfy. As Merchant
and Riggle observe, distinct sets of conditions can present the same grammar.

Grammars are therefore a complete lattice under inclusion of their rankings, mathlib's concept
lattice. The meet of two grammars has the rankings they share, the join is the least grammar
containing the rankings of both, the shared ranking information of Merchant and Riggle, the top
has every ranking, and the bottom is the grammar of all conditions. A grammar with a ranking
determines an antimatroid, and for the grammar of a partial order its feasible sets are the
[order ideals](##OptimalityTheory.Grammar.toAntimatroid_ofRel_isFeasible).

## Implementation notes

A grammar need not have a ranking: the grammar of an inconsistent set of conditions is the
bottom of the lattice, where Merchant and Riggle consider consistent sets only. Consistency is the
hypothesis `G.extent.Nonempty` of the statements that need it.

## References

* [N. Merchant, J. Riggle, *OT grammars, beyond partial orders: ERC sets and antimatroids*
  (2016)][merchant-riggle-2016]
* [R. P. Dilworth, *Lattices with unique irreducible decompositions* (1940)][dilworth-1940]
* [N. Merchant and A. Prince, *The Mother of All Tableaux* (2022)][merchant-prince-2022]
-/

@[expose] public section

namespace OptimalityTheory

variable {n : ℕ}

/-- An *Optimality-theoretic grammar* over `n` constraints: a formal concept of the satisfaction
relation between rankings and ERCs. Its extent is the set of its rankings and its intent the set
of ERCs that all of them satisfy. -/
abbrev Grammar (n : ℕ) := Concept (Ranking (Fin n) n) (ERC (Fin n)) ERC.SatisfiedBy

namespace Grammar

variable {E E' : Set (ERC (Fin n))} {σ : Ranking (Fin n) n} {G : Grammar n}

/-- The grammar presented by a set of ERCs, whose rankings are those satisfying all of them. -/
abbrev ofERCs (E : Set (ERC (Fin n))) : Grammar n := Concept.ofAttributes _ E

theorem mem_extent_ofERCs : σ ∈ (ofERCs E).extent ↔ ∀ α ∈ E, α.SatisfiedBy σ := Iff.rfl

theorem coe_linearExtensions (E : Finset (ERC (Fin n))) :
    (ERC.linearExtensions E : Set (Ranking (Fin n) n)) =
      (ofERCs (E : Set (ERC (Fin n)))).extent := by
  ext σ
  rw [Finset.mem_coe, ERC.mem_linearExtensions, mem_extent_ofERCs]
  rfl

/-- Two sets of ERCs present the same grammar iff the same rankings satisfy them. -/
theorem ofERCs_eq_iff : ofERCs E = ofERCs E' ↔
    ∀ σ : Ranking (Fin n) n, (∀ α ∈ E, α.SatisfiedBy σ) ↔ ∀ α ∈ E', α.SatisfiedBy σ :=
  Concept.extent_injective.eq_iff.symm.trans Set.ext_iff

/-- Over at least one constraint the bottom grammar has no ranking, since no ranking satisfies
the ERC with every constraint loser-preferring. -/
theorem extent_bot [NeZero n] : (⊥ : Grammar n).extent = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun σ hσ ↦ ?_
  have h : ERC.SatisfiedBy σ (fun _ ↦ .L) :=
    Concept.extent_subset_extent_iff.2 (bot_le (a := ofERCs {fun _ ↦ .L})) hσ
      (Set.mem_singleton _)
  obtain ⟨w, hw, -⟩ := (ERC.satisfiedBy_iff_dominance σ _).1 h 0 rfl
  exact absurd hw (by decide)

/-- A grammar over at least one constraint is inconsistent iff it has no ranking. -/
theorem eq_bot_iff_extent [NeZero n] : G = ⊥ ↔ G.extent = ∅ :=
  ⟨fun h ↦ h ▸ extent_bot, fun h ↦ Concept.ext (h.trans extent_bot.symm)⟩

/-! ### The antimatroid of a grammar -/

/-- The antimatroid of a grammar with a ranking: the antimatroid of its conditions, whose feasible
sets are the top segments of its rankings (`toAntimatroid_isFeasible`). -/
def toAntimatroid (G : Grammar n) (h : G.extent.Nonempty) : Antimatroid (Fin n) :=
  ERC.toAntimatroid G.intent (h.imp fun _ hσ _ hα ↦ G.rel_extent_intent hσ hα)

theorem toAntimatroid_isFeasible (h : G.extent.Nonempty) (S : Set (Fin n)) :
    (G.toAntimatroid h).IsFeasible S ↔ ∃ σ ∈ G.extent, ∃ k : Fin (n + 1), ↑(σ.take k) = S := by
  rw [toAntimatroid, ERC.toAntimatroid_isFeasible, ← G.lowerPolar_intent]
  rfl

/-- The antimatroid of the grammar that a set of ERCs presents is the antimatroid of the set. -/
theorem toAntimatroid_ofERCs_isFeasible (h : (ofERCs E).extent.Nonempty) (S : Set (Fin n)) :
    ((ofERCs E).toAntimatroid h).IsFeasible S ↔ ERC.IsFeasible E S :=
  toAntimatroid_isFeasible h S

end Grammar

/-! ### The grammars of a typology -/

/-- Each class of a typology is the set of rankings of a grammar: the rankings with a given
language are those satisfying its ERC grammar ([merchant-prince-2022]). -/
theorem ConstraintSystem.isExtent_setOf_typology {I O ι : Type*} (S : ConstraintSystem I O ι)
    (r : Ranking ι n) : Order.IsExtent ERC.SatisfiedBy {r' | S.typology r r'} :=
  ⟨S.ercGrammar r, Set.ext fun _ ↦
    ConstraintSystem.forall_ercGrammar_satisfiedBy_iff.trans eq_comm⟩

/-! ### The grammar of a relation

Each related pair of a relation on the constraints is a simple ERC, and the rankings satisfying
them all are the linear extensions of the relation. -/

section Rel

variable {r : Fin n → Fin n → Prop} {σ : Ranking (Fin n) n}

/-- The ERCs of a relation: the simple ERC `a ≫ b` for each related pair, which is trivial when
`a = b`. -/
def ERC.ofRel (r : Fin n → Fin n → Prop) : Set (ERC (Fin n)) :=
  {α | ∃ a b, r a b ∧ simpleERC a b = α}

theorem ERC.forall_mem_ofRel_satisfiedBy_iff :
    (∀ α ∈ ERC.ofRel r, α.SatisfiedBy σ) ↔ σ.IsLinearExtension r := by
  refine ⟨fun h a b hab ↦ (simpleERC_satisfiedBy_toRel_iff a b σ).1 (h _ ⟨a, b, hab, rfl⟩),
    fun h α hα ↦ ?_⟩
  obtain ⟨a, b, hab, rfl⟩ := hα
  exact (simpleERC_satisfiedBy_toRel_iff a b σ).2 (h a b hab)

theorem ERC.isSimple_or_isTrivial_of_mem_ofRel {α : ERC (Fin n)} (hα : α ∈ ERC.ofRel r) :
    α.IsSimple ∨ α.IsTrivial := by
  obtain ⟨a, b, -, rfl⟩ := hα
  exact simpleERC_isSimple_or_isTrivial a b

/-- The grammar of a relation on the constraints, whose rankings are its linear extensions. -/
def Grammar.ofRel (r : Fin n → Fin n → Prop) : Grammar n := .ofERCs (ERC.ofRel r)

@[simp] theorem Grammar.mem_extent_ofRel :
    σ ∈ (Grammar.ofRel r).extent ↔ σ.IsLinearExtension r :=
  ERC.forall_mem_ofRel_satisfiedBy_iff

theorem Grammar.extent_ofRel (r : Fin n → Fin n → Prop) [DecidableRel r] :
    (Grammar.ofRel r).extent = ↑(Ranking.linearExtensions r) := by
  ext σ
  rw [Grammar.mem_extent_ofRel, Finset.mem_coe, Ranking.mem_linearExtensions]

/-- A ranking is the only ranking of the grammar of its own order. -/
theorem Grammar.extent_ofRel_toRel (σ : Ranking (Fin n) n) :
    (Grammar.ofRel σ.toRel).extent = {σ} := by
  ext τ
  rw [Grammar.mem_extent_ofRel, Set.mem_singleton_iff, Ranking.IsLinearExtension,
    Ranking.toRel_le_toRel_iff, eq_comm]

/-- The grammar of a partial order has a ranking. -/
theorem Grammar.extent_ofRel_nonempty (r : Fin n → Fin n → Prop) [IsPartialOrder (Fin n) r] :
    (Grammar.ofRel r).extent.Nonempty :=
  (Ranking.exists_isLinearExtension r).imp fun _ ↦ Grammar.mem_extent_ofRel.2

private theorem forall_isFeasible_ofRel_iff (h : (Grammar.ofRel r).extent.Nonempty)
    {S : Finset (Fin n)} :
    (∀ α ∈ ERC.ofRel r, ERC.IsFeasible {α} (S : Set (Fin n))) ↔
      ∀ a b, r a b → b ∈ S → a ∈ S := by
  obtain ⟨σ, hσ⟩ := h
  have hsat : ∀ α ∈ ERC.ofRel r, ∃ σ : Ranking (Fin n) n, ERC.SatisfiedBy σ α :=
    fun α hα ↦ ⟨σ, hσ hα⟩
  refine ⟨fun h a b hrel hbS ↦ ?_, fun h α hα ↦ ?_⟩
  · rcases eq_or_ne a b with rfl | hab
    · exact hbS
    · have hα : simpleERC a b ∈ ERC.ofRel r := ⟨a, b, hrel, rfl⟩
      obtain ⟨w, hwS, hwW⟩ := (ERC.isFeasible_singleton_iff (hsat _ hα) S).mp (h _ hα)
        ⟨b, hbS, simpleERC_apply_L hab⟩
      rwa [(simpleERC_eq_W_iff w).mp hwW] at hwS
  · rw [ERC.isFeasible_singleton_iff (hsat α hα)]
    obtain ⟨a, b, hrel, rfl⟩ := hα
    rintro ⟨l, hlS, hlL⟩
    have hab : a ≠ b := by rintro rfl; exact simpleERC_self_isTrivial a l hlL
    rw [(simpleERC_eq_L_iff hab l).mp hlL] at hlS
    exact ⟨a, h a b hrel hlS, simpleERC_apply_W⟩

/-- The feasible sets of the antimatroid of a relation's grammar are its order ideals, the sets
containing every constraint that the relation ranks above one of their members
([dilworth-1940], [merchant-riggle-2016]). -/
theorem Grammar.toAntimatroid_ofRel_isFeasible (h : (Grammar.ofRel r).extent.Nonempty)
    {S : Finset (Fin n)} :
    ((Grammar.ofRel r).toAntimatroid h).IsFeasible (↑S : Set (Fin n)) ↔
      ∀ a b, r a b → b ∈ S → a ∈ S := by
  refine (Grammar.toAntimatroid_ofERCs_isFeasible (E := ERC.ofRel r) h _).trans ?_
  rw [ERC.isFeasible_iff_forall_singleton_of_simple h
    fun _ ↦ ERC.isSimple_or_isTrivial_of_mem_ofRel]
  exact forall_isFeasible_ofRel_iff h

end Rel

end OptimalityTheory
