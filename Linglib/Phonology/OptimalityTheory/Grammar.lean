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
[order ideals](##OptimalityTheory.Grammar.Enumeration.toAntimatroid_ofRel_isFeasible).

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

variable {ι : Type*} {n : ℕ}

/-- An *Optimality-theoretic grammar* over the constraints `ι`: a formal concept of the satisfaction
relation between rankings and ERCs. Its extent is the set of its rankings and its intent the set
of ERCs that all of them satisfy. -/
abbrev Grammar.Enumeration (ι : Type*) (n : ℕ) :=
  Concept (Ranking.Enumeration ι n) (ERC ι) ERC.SatisfiedBy

/-- The grammars over the constraints `ι`, with rankings given by the constraints alone. What is
proved of a `Grammar.Enumeration ι n` holds of it. -/
abbrev Grammar (ι : Type*) [Fintype ι] := Grammar.Enumeration ι (Fintype.card ι)

namespace Grammar.Enumeration

variable {E E' : Set (ERC ι)} {σ : Ranking.Enumeration ι n} {G : Grammar.Enumeration ι n}

/-- The grammar presented by a set of ERCs, whose rankings are those satisfying all of them. -/
abbrev ofERCs (E : Set (ERC ι)) : Grammar.Enumeration ι n := Concept.ofAttributes _ E

theorem mem_extent_ofERCs : σ ∈ (ofERCs E).extent ↔ ∀ α ∈ E, α.SatisfiedBy σ := Iff.rfl

theorem coe_linearExtensions [Fintype ι] [DecidableEq ι] (E : Finset (ERC ι)) :
    ((ERC.linearExtensions E : Finset (Ranking.Enumeration ι n)) : Set (Ranking.Enumeration ι n)) =
      (ofERCs (E : Set (ERC ι))).extent := by
  ext σ
  rw [Finset.mem_coe, ERC.mem_linearExtensions, mem_extent_ofERCs]
  rfl

/-- Two sets of ERCs present the same grammar iff the same rankings satisfy them. -/
theorem ofERCs_eq_iff : (ofERCs E : Grammar.Enumeration ι n) = ofERCs E' ↔
    ∀ σ : Ranking.Enumeration ι n, (∀ α ∈ E, α.SatisfiedBy σ) ↔ ∀ α ∈ E', α.SatisfiedBy σ :=
  Concept.extent_injective.eq_iff.symm.trans Set.ext_iff

/-- Over at least one constraint the bottom grammar has no ranking, since no ranking satisfies
the ERC with every constraint loser-preferring. -/
theorem extent_bot [Nonempty ι] : (⊥ : Grammar.Enumeration ι n).extent = ∅ := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  refine Set.eq_empty_of_forall_notMem fun σ hσ ↦ ?_
  have h : ERC.SatisfiedBy σ (fun _ ↦ .L) :=
    Concept.extent_subset_extent_iff.2 (bot_le (a := ofERCs {fun _ ↦ .L})) hσ
      (Set.mem_singleton _)
  obtain ⟨w, hw, -⟩ := (ERC.satisfiedBy_iff_dominance σ _).1 h i rfl
  exact absurd hw (by decide)

/-- A grammar over at least one constraint is inconsistent iff it has no ranking. -/
theorem eq_bot_iff_extent [Nonempty ι] : G = ⊥ ↔ G.extent = ∅ :=
  ⟨fun h ↦ h ▸ extent_bot, fun h ↦ Concept.ext (h.trans extent_bot.symm)⟩

/-- Two grammars share no ranking when an ERC of the one and an ERC of the other fuse to an ERC
with an `L` and no `W`. -/
theorem ofERCs_inf_ofERCs_eq_bot [Nonempty ι] {α β : ERC ι} (hα : α ∈ E) (hβ : β ∈ E')
    (h : (α.fuse β).IsContradictory) : (ofERCs E ⊓ ofERCs E' : Grammar.Enumeration ι n) = ⊥ :=
  eq_bot_iff_extent.2 <| Set.eq_empty_of_forall_notMem fun _ ⟨h₁, h₂⟩ ↦
    ERC.not_satisfiedBy_of_isContradictory_fuse h (h₁ hα) (h₂ hβ)

/-! ### The antimatroid of a grammar -/

/-- The antimatroid of a grammar with a ranking: the antimatroid of its conditions, whose feasible
sets are the top segments of its rankings (`toAntimatroid_isFeasible`). -/
def toAntimatroid [Fintype ι] (G : Grammar.Enumeration ι n)
    (h : G.extent.Nonempty) : Antimatroid ι :=
  ERC.toAntimatroid G.intent (h.imp fun _ hσ _ hα ↦ G.rel_extent_intent hσ hα)

theorem toAntimatroid_isFeasible [Fintype ι] (h : G.extent.Nonempty) (S : Set ι) :
    (G.toAntimatroid h).IsFeasible S ↔ ∃ σ ∈ G.extent, ∃ k : Fin (n + 1), ↑(σ.take k) = S := by
  rw [toAntimatroid, ERC.toAntimatroid_isFeasible, ← G.lowerPolar_intent]
  rfl

/-- The antimatroid of the grammar that a set of ERCs presents is the antimatroid of the set. -/
theorem toAntimatroid_ofERCs_isFeasible [Fintype ι]
    (h : (ofERCs E : Grammar.Enumeration ι n).extent.Nonempty) (S : Set ι) :
    ((ofERCs E).toAntimatroid h).IsFeasible S ↔ ERC.IsFeasible n E S :=
  toAntimatroid_isFeasible h S

end Grammar.Enumeration

/-! ### The grammar of a winner -/

section Winner

variable {C : Type*} {con : ConstraintSet C ι} {candidates : Finset C} {w : C}
  {σ : Ranking.Enumeration ι n}

/-- The grammar of a winner among the candidates of a tableau, presented by its ERC against each
candidate. -/
def Grammar.Enumeration.ofWinner (con : ConstraintSet C ι) (candidates : Finset C)
    (w : C) : Grammar.Enumeration ι n :=
  .ofERCs ((fun l ↦ ercOfProfiles (con · w) (con · l)) '' candidates)

/-- The rankings of the grammar of a winner are those under which it is optimal. -/
theorem Grammar.Enumeration.mem_extent_ofWinner (hw : w ∈ candidates) :
    σ ∈ (Grammar.Enumeration.ofWinner con candidates w).extent ↔
      w ∈ (Tableau.ofRanking con σ candidates).optimal := by
  rw [Tableau.ofRanking_mem_optimal_iff_satisfiedBy, and_iff_right hw]
  exact ⟨fun h l hl ↦ h ⟨l, Finset.mem_coe.2 hl, rfl⟩, by rintro h _ ⟨l, hl, rfl⟩; exact h l hl⟩

/-- The comparative tableau of a winner: its ERC against each of the listed competitors, the
rows of `W`, `L` and `e` of [prince-2002]. -/
def comparative (con : ConstraintSet C ι) (w : C) (losers : List C) : List (ERC ι) :=
  losers.map fun d ↦ ercOfProfiles (con · w) (con · d)

/-- The grammar of a winner is the grammar its comparative tableau presents. -/
theorem Grammar.Enumeration.ofERCs_comparative [DecidableEq C] (l : List C) :
    (Grammar.Enumeration.ofERCs {α | α ∈ comparative con w (l.filter
        (· ≠ w))} : Grammar.Enumeration ι n) =
      Grammar.Enumeration.ofWinner con l.toFinset w := by
  refine Concept.ext (Set.ext fun σ ↦ ⟨fun h ↦ ?_, fun h α hα ↦ ?_⟩)
  · rintro _ ⟨d, hd, rfl⟩
    by_cases hdw : d = w
    · subst hdw
      exact ERC.trivial_satisfiedBy
        (fun k hk ↦ lt_irrefl _ ((ercOfProfiles_eq_L_iff _ _ k).1 hk)) σ
    · exact h (List.mem_map.2 ⟨d, List.mem_filter.2 ⟨List.mem_toFinset.1 hd, by simpa using hdw⟩,
        rfl⟩)
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hα
    exact h ⟨d, Finset.mem_coe.2 (List.mem_toFinset.2 (List.mem_filter.1 hd).1), rfl⟩

/-- A winner is the sole winner when no row of its comparative tableau is neutral
throughout. -/
theorem Tableau.ofRanking_optimal_eq_singleton_of_comparative [DecidableEq C] {l : List C}
    (hw : w ∈ (Tableau.ofRanking con σ l.toFinset).optimal)
    (h : ∀ α ∈ comparative con w (l.filter (· ≠ w)), ∃ k, α k ≠ .e) :
    (Tableau.ofRanking con σ l.toFinset).optimal = {w} :=
  (Tableau.ofRanking_optimal_eq_singleton_iff_of_mem hw).2 fun d hd he ↦ by
    by_contra hne
    obtain ⟨k, hk⟩ := h _ (List.mem_map.2
      ⟨d, List.mem_filter.2 ⟨List.mem_toFinset.1 hd, by simpa using hne⟩, rfl⟩)
    exact hk ((ercOfProfiles_eq_e_iff _ _ k).2 (he k).symm)

/-- Two winners are optimal together under no ranking when an ERC of the one and an ERC of the
other fuse to an ERC with an `L` and no `W`. -/
theorem Grammar.Enumeration.ofWinner_inf_ofWinner_eq_bot [Nonempty ι] {C' : Type*}
    {con' : ConstraintSet C' ι} {candidates' : Finset C'} {w' : C'} {d : C} {d' : C'}
    (hd : d ∈ candidates) (hd' : d' ∈ candidates')
    (h : ((ercOfProfiles (con · w) (con · d)).fuse
      (ercOfProfiles (con' · w') (con' · d'))).IsContradictory) :
    (Grammar.Enumeration.ofWinner con candidates w ⊓
      Grammar.Enumeration.ofWinner con' candidates' w' : Grammar.Enumeration ι n) =
      ⊥ :=
  Grammar.Enumeration.ofERCs_inf_ofERCs_eq_bot ⟨d, Finset.mem_coe.2 hd, rfl⟩
    ⟨d', Finset.mem_coe.2 hd', rfl⟩ h

end Winner

/-! ### The grammars of a typology -/

/-- Each class of a typology is the set of rankings of a grammar: the rankings with a given
language are those satisfying its ERC grammar ([merchant-prince-2022]). -/
theorem ConstraintSystem.isExtent_setOf_typology {I O ι : Type*} (S : ConstraintSystem I O ι)
    (r : Ranking.Enumeration ι n) : Order.IsExtent ERC.SatisfiedBy {r' | S.typology r r'} :=
  ⟨S.ercGrammar r, Set.ext fun _ ↦
    ConstraintSystem.forall_ercGrammar_satisfiedBy_iff.trans eq_comm⟩

/-! ### The grammar of a relation

Each related pair of a relation on the constraints is a simple ERC, and the rankings satisfying
them all are the linear extensions of the relation. -/

section Rel

variable [DecidableEq ι] {r : ι → ι → Prop} {σ : Ranking.Enumeration ι n}

/-- The ERCs of a relation: the simple ERC `a ≫ b` for each related pair, which is trivial when
`a = b`. -/
def ERC.ofRel (r : ι → ι → Prop) : Set (ERC ι) :=
  {α | ∃ a b, r a b ∧ simpleERC a b = α}

theorem ERC.forall_mem_ofRel_satisfiedBy_iff :
    (∀ α ∈ ERC.ofRel r, α.SatisfiedBy σ) ↔ σ.IsLinearExtension r := by
  refine ⟨fun h a b hab ↦ (simpleERC_satisfiedBy_toRel_iff a b σ).1 (h _ ⟨a, b, hab, rfl⟩),
    fun h α hα ↦ ?_⟩
  obtain ⟨a, b, hab, rfl⟩ := hα
  exact (simpleERC_satisfiedBy_toRel_iff a b σ).2 (h a b hab)

theorem ERC.isSimple_or_isTrivial_of_mem_ofRel {α : ERC ι} (hα : α ∈ ERC.ofRel r) :
    α.IsSimple ∨ α.IsTrivial := by
  obtain ⟨a, b, -, rfl⟩ := hα
  exact simpleERC_isSimple_or_isTrivial a b

/-- The grammar of a relation on the constraints, whose rankings are its linear extensions. -/
def Grammar.Enumeration.ofRel (r : ι → ι → Prop) : Grammar.Enumeration ι n := .ofERCs (ERC.ofRel r)

@[simp] theorem Grammar.Enumeration.mem_extent_ofRel :
    σ ∈ (Grammar.Enumeration.ofRel r).extent ↔ σ.IsLinearExtension r :=
  ERC.forall_mem_ofRel_satisfiedBy_iff

omit [DecidableEq ι] in
/-- An ERC that holds of a relation is satisfied by every ranking extending the relation. -/
theorem ERC.Holds.satisfiedBy {α : ERC ι} (h : α.Holds r) (hσ : σ.IsLinearExtension r) :
    α.SatisfiedBy σ :=
  (ERC.satisfiedBy_iff_holds σ α).2 fun j hj ↦ by
    obtain ⟨i, hi, hij⟩ := h j hj
    have hne : i ≠ j := by rintro rfl; rw [hi] at hj; exact absurd hj (by decide)
    exact ⟨i, hi, hσ.dominates hij hne⟩

omit [DecidableEq ι] in
/-- An ERC holds of a transitive antisymmetric relation, such as a partial order on the
constraints, iff every ranking extending the relation satisfies it. -/
theorem ERC.holds_iff_forall_satisfiedBy [Fintype ι] [ht : IsTrans ι r] [ha : Std.Antisymm r]
    {α : ERC ι} (hn : Fintype.card ι = n := by simp) :
    α.Holds r ↔ ∀ σ : Ranking.Enumeration ι n, σ.IsLinearExtension r → α.SatisfiedBy σ := by
  refine ⟨fun h σ hσ ↦ h.satisfiedBy hσ, fun h j hj ↦ ?_⟩
  by_contra hno
  have hup : ∀ {a b : ι}, r a b → (b = j ∨ r b j) → (a = j ∨ r a j) := fun hab hb ↦
    hb.elim (fun e ↦ Or.inr (e ▸ hab)) fun hbj ↦ Or.inr (ht.trans _ _ _ hab hbj)
  -- the order that also puts everything at or above `j` above everything else
  have hpo : IsPartialOrder ι
      (fun a b ↦ a = b ∨ r a b ∨ ((a = j ∨ r a j) ∧ ¬ (b = j ∨ r b j))) :=
    { refl := fun a ↦ Or.inl rfl
      trans := by
        intro a b c h1 h2
        rcases h1 with rfl | h1 | ⟨ha', hb⟩
        · exact h2
        · rcases h2 with rfl | h2 | ⟨hb, hc⟩
          · exact Or.inr (Or.inl h1)
          · exact Or.inr (Or.inl (ht.trans _ _ _ h1 h2))
          · exact Or.inr (Or.inr ⟨hup h1 hb, hc⟩)
        · rcases h2 with rfl | h2 | ⟨hb', hc⟩
          · exact Or.inr (Or.inr ⟨ha', hb⟩)
          · exact Or.inr (Or.inr ⟨ha', fun hc ↦ hb (hup h2 hc)⟩)
          · exact absurd hb' hb
      antisymm := by
        intro a b h1 h2
        rcases h1 with rfl | h1 | ⟨ha', hb⟩
        · rfl
        · rcases h2 with rfl | h2 | ⟨hb, ha'⟩
          · rfl
          · exact ha.antisymm _ _ h1 h2
          · exact absurd (hup h1 hb) ha'
        · rcases h2 with rfl | h2 | ⟨hb', _⟩
          · rfl
          · exact absurd (hup h2 ha') hb
          · exact absurd hb' hb }
  obtain ⟨σ, hσ⟩ := Ranking.Enumeration.exists_isLinearExtension
    (fun a b ↦ a = b ∨ r a b ∨ ((a = j ∨ r a j) ∧ ¬ (b = j ∨ r b j))) hn
  obtain ⟨i, hi, hij⟩ := (ERC.satisfiedBy_iff_holds σ α).1
    (h σ fun a b hab ↦ hσ a b (Or.inr (Or.inl hab))) j hj
  have hUi : i = j ∨ r i j := by
    by_contra hni
    exact absurd hij (not_lt.2 (hσ j i (Or.inr (Or.inr ⟨Or.inl rfl, hni⟩))))
  rcases hUi with rfl | hij'
  · rw [hi] at hj; exact absurd hj (by decide)
  · exact hno ⟨i, hi, hij'⟩

/-- The intent of the grammar of a transitive antisymmetric relation: the ERCs that hold of
it. -/
theorem Grammar.Enumeration.mem_intent_ofRel [Fintype ι] [IsTrans ι r] [Std.Antisymm r] {α : ERC ι}
    (hn : Fintype.card ι = n := by simp) :
    α ∈ (Grammar.Enumeration.ofRel r : Grammar.Enumeration ι n).intent ↔ α.Holds r := by
  rw [ERC.holds_iff_forall_satisfiedBy hn, ← Concept.upperPolar_extent]
  exact forall_congr' fun σ ↦ by rw [Grammar.Enumeration.mem_extent_ofRel]

/-- The grammar of a diagram lies below the grammar of a winner iff each of the winner's ERCs
holds of the diagram: the winner is optimal under every ranking that extends the diagram. -/
theorem Grammar.Enumeration.ofRel_le_ofWinner_iff [Fintype ι] [IsTrans ι r] [Std.Antisymm r]
    {C : Type*}
    {con : ConstraintSet C ι} {candidates : Finset C} {w : C}
    (hn : Fintype.card ι = n := by simp) :
    (Grammar.Enumeration.ofRel r : Grammar.Enumeration ι n) ≤
        Grammar.Enumeration.ofWinner con candidates w ↔
      ∀ d ∈ candidates, (ercOfProfiles (con · w) (con · d)).Holds r := by
  rw [Grammar.Enumeration.ofWinner, Concept.le_ofAttributes_iff]
  exact ⟨fun h d hd ↦ (Grammar.Enumeration.mem_intent_ofRel hn).1 (h ⟨d, Finset.mem_coe.2 hd, rfl⟩),
    by rintro h _ ⟨d, hd, rfl⟩; exact (Grammar.Enumeration.mem_intent_ofRel hn).2 (h d hd)⟩

/-! ### Diagrams given by their edges

A printed Hasse diagram lists the edges of an order, its transitive reduction, and the ERCs
that hold of the diagram are those that hold of the order it generates. `below R a` computes the
constraints reachable from `a` along the edges `R`, so that an ERC is checked against a diagram
as the paper draws it. -/

/-- The constraints that the edges `R` put below `a`: those reachable from `a` in one or more
steps. -/
def below [Fintype ι] (R : ι → ι → Prop) [DecidableRel R] (a : ι) : Finset ι :=
  (fun S ↦ S ∪ S.biUnion fun b ↦ Finset.univ.filter (R b))^[Fintype.card ι]
    (Finset.univ.filter (R a))

theorem transGen_of_mem_below [Fintype ι] {R : ι → ι → Prop} [DecidableRel R]
    {a b : ι} (h : b ∈ below R a) : Relation.TransGen R a b := by
  have key : ∀ (k : ℕ) (S : Finset ι), (∀ c ∈ S, Relation.TransGen R a c) →
      ∀ c ∈ (fun S ↦ S ∪ S.biUnion fun b ↦ Finset.univ.filter (R b))^[k] S,
        Relation.TransGen R a c := by
    intro k
    induction k with
    | zero => exact fun S hS ↦ hS
    | succ k ih =>
      intro S hS
      rw [Function.iterate_succ_apply]
      refine ih _ fun c hc ↦ ?_
      rcases Finset.mem_union.1 hc with hc | hc
      · exact hS c hc
      · obtain ⟨b, hb, hbc⟩ := Finset.mem_biUnion.1 hc
        exact (hS b hb).tail (by simpa using hbc)
  exact key _ _ (fun c hc ↦ .single (by simpa using hc)) b h

/-- If each ERC of a set holds of the constraints the edges of a diagram put below one another,
the grammar of the diagram lies below the grammar the set presents. -/
theorem Grammar.Enumeration.ofRel_le_ofERCs_of_holds_below [Fintype ι] [DecidableRel r] {E : Set
    (ERC ι)}
    (h : ∀ α ∈ E, α.Holds fun a b ↦ b ∈ below r a) :
    (Grammar.Enumeration.ofRel r : Grammar.Enumeration ι n) ≤ Grammar.Enumeration.ofERCs E :=
  Concept.extent_subset_extent_iff.1 fun _ hσ α hα ↦
    ((h α hα).mono fun _ _ ↦ transGen_of_mem_below).satisfiedBy
      (Grammar.Enumeration.mem_extent_ofRel.1 hσ).transGen

/-- If each ERC of a winner holds of the constraints the edges of a diagram put below one
another, the grammar of the diagram lies below the grammar of the winner: the winner is optimal
under every ranking that extends the diagram. -/
theorem Grammar.Enumeration.ofRel_le_ofWinner_of_holds_below [Fintype ι] [DecidableRel r]
    {C : Type*}
    {con : ConstraintSet C ι} {candidates : Finset C} {w : C}
    (h : ∀ d ∈ candidates, (ercOfProfiles (con · w) (con · d)).Holds fun a b ↦ b ∈ below r a) :
    (Grammar.Enumeration.ofRel r : Grammar.Enumeration ι n) ≤
        Grammar.Enumeration.ofWinner con candidates w :=
  Grammar.Enumeration.ofRel_le_ofERCs_of_holds_below (by rintro _ ⟨d, hd, rfl⟩; exact h d hd)

theorem Grammar.Enumeration.extent_ofRel [Fintype ι] (r : ι → ι → Prop) [DecidableRel r] :
    (Grammar.Enumeration.ofRel r : Grammar.Enumeration ι n).extent =
        ↑(Ranking.Enumeration.linearExtensions
        (n := n) r) := by
  ext σ
  rw [Grammar.Enumeration.mem_extent_ofRel, Finset.mem_coe,
    Ranking.Enumeration.mem_linearExtensions]

/-- A ranking is the only ranking of the grammar of its own order. -/
theorem Grammar.Enumeration.extent_ofRel_toRel (σ : Ranking.Enumeration ι n) :
    (Grammar.Enumeration.ofRel σ.toRel).extent = {σ} := by
  ext τ
  rw [Grammar.Enumeration.mem_extent_ofRel, Set.mem_singleton_iff,
    Ranking.Enumeration.IsLinearExtension,
    Ranking.Enumeration.toRel_le_toRel_iff, eq_comm]

/-- The grammar of a partial order has a ranking. -/
theorem Grammar.Enumeration.extent_ofRel_nonempty [Fintype ι] (r : ι → ι → Prop)
    [IsPartialOrder ι r]
    (hn : Fintype.card ι = n := by simp) :
        (Grammar.Enumeration.ofRel r : Grammar.Enumeration ι n).extent.Nonempty :=
  (Ranking.Enumeration.exists_isLinearExtension r hn).imp fun _ ↦
    Grammar.Enumeration.mem_extent_ofRel.2

private theorem forall_isFeasible_ofRel_iff [Fintype ι]
    (h : (Grammar.Enumeration.ofRel r : Grammar.Enumeration ι n).extent.Nonempty)
    {S : Finset ι} :
    (∀ α ∈ ERC.ofRel r, ERC.IsFeasible n {α} (S : Set ι)) ↔
      ∀ a b, r a b → b ∈ S → a ∈ S := by
  obtain ⟨σ, hσ⟩ := h
  have hsat : ∀ α ∈ ERC.ofRel r, ∃ σ : Ranking.Enumeration ι n, ERC.SatisfiedBy σ α :=
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
theorem Grammar.Enumeration.toAntimatroid_ofRel_isFeasible [Fintype ι]
    (h : (Grammar.Enumeration.ofRel r : Grammar.Enumeration ι n).extent.Nonempty)
    {S : Finset ι} :
    ((Grammar.Enumeration.ofRel r).toAntimatroid h).IsFeasible (↑S : Set ι) ↔
      ∀ a b, r a b → b ∈ S → a ∈ S := by
  refine (Grammar.Enumeration.toAntimatroid_ofERCs_isFeasible (E := ERC.ofRel r) h _).trans ?_
  rw [ERC.isFeasible_iff_forall_singleton_of_simple h
    fun _ ↦ ERC.isSimple_or_isTrivial_of_mem_ofRel]
  exact forall_isFeasible_ofRel_iff h

end Rel

end OptimalityTheory
