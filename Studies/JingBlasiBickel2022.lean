module

public import Linglib.Data.UD.DepRel
public import Linglib.Syntax.DependencyGrammar.Catena
public import Linglib.Syntax.DependencyGrammar.Length
public import Linglib.Syntax.DependencyGrammar.Stemma
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.UniformOn

/-!
# Jing, Blasi and Bickel (2022): Dependency-length minimization and its limits: A possible role for a probabilistic version of the final-over-final condition

A two-dependency catena is a dependency with a dependency of its dependent (hierarchical) or two
of one head (parallel), harmonic when both point one way. The paper scores a sentence by the
chance that a baseline relinearization has longer catenae. Mirroring keeps
[harmony](##harmonic_mirror) and [the score](##dlm_mirror) and [exchanges head-final with
head-initial pairs](##headFinalPairs_mirror), so a law invariant under it, such as [one weighting
length alone](##map_mirror_eq_self), [gives the score one law at `k` head-final and at `k`
head-initial pairs](##measure_dlm_headFinal). A score falling with head-finality needs a cause that
sees direction, such as [a penalty on final over initial](##cond_harmonic).

## Implementation notes

* A sentence is a linearization `σ` of a tree `g`, the graph `g.map σ`: catenae and their
  head–dependent pairs are read off `g`, directions and lengths off `σ`. Only dependencies
  between verbs, nouns, adjectives and adverbs are measured, at distances counting every word;
  on catenae covering every arc the length is the total dependency length
  (`length_eq_totalLength`).
* `dlm` is the probability that the paper estimates from 100 baseline samples, for any baseline
  law; `fig2a` is one sample.
* The paper's tentative principle is modelled one catena at a time (`disprefer`): the
  final-over-initial configuration of a catena is downweighted by `ε < 1` in a mirror-invariant
  law. Like the paper, the model drops both restrictions of Biberauer, Holmberg and Roberts, that
  the two heads lie in one extended projection and share their value of ±V.
* The symmetry argument is the one Roberts makes against harmony as the source of the condition,
  in his chapter of the book of Sheehan, Biberauer, Roberts and Holmberg, whose chapter by
  Sheehan weighs the parsing accounts of the condition.

## Errata

* Fig. 2b, the free-word-order baseline, attaches *into* and *certain* to *article*, so it is
  not the dependency-preserving linearization of Figure 1 that §2.3 describes; with the heads of
  Figure 1 its order puts *into* after *parts*, reversing a dependency the baseline keeps.
* The reference list credits "Harmony, symmetry, and dominance in word order universals" to
  Biberauer, Holmberg, Roberts and Sheehan; the chapter is Roberts's alone.

## TODO

* The paper's three baselines as laws on projective linearizations, which needs the
  supplementary materials on function words and the order of siblings. `dlm_mirror` and
  `measure_dlm_headFinal` hold for every baseline.
* A law downweighting every final-over-initial catena of a sentence does not reduce to the
  model of one catena, since the other catenae break the symmetry `measure_swap_directions`
  gives.
* Behaghel's law against nested ordering: the second is mirror-symmetric and the first is not.

## References

* [jing-blasi-bickel-2022]
* [biberauer-holmberg-roberts-2014]
* [sheehan-biberauer-roberts-holmberg-2017]
* [sheehan-2017b]
-/

@[expose] public section

namespace JingBlasiBickel2022

open DependencyGrammar WordOrder MeasureTheory ProbabilityTheory Finset Morphology
open Stemma (node leaf)
open scoped ENNReal Nat

local instance {α : Type*} {k : ℕ} : MeasurableSpace (Arrangement α k) := ⊤

variable {L : Type*} {n : ℕ} {g : Graph L n}

/-! ### Two-dependency catenae, §2.2 -/

/-- The hierarchical two-dependency catenae of `g`: an arc and an arc out of its dependent. -/
def hierarchical (g : Graph L n) : Finset ((Fin n × Fin n) × (Fin n × Fin n)) :=
  {x ∈ g.arcs ×ˢ g.arcs | x.1.2 = x.2.1}

/-- The parallel two-dependency catenae of `g`: two arcs out of one head, each pair counted once,
with the first dependent at the lower position of `g`. -/
def parallel (g : Graph L n) : Finset ((Fin n × Fin n) × (Fin n × Fin n)) :=
  {x ∈ g.arcs ×ˢ g.arcs | x.1.1 = x.2.1 ∧ x.1.2 < x.2.2}

section Catena

variable {a b c : Fin n}

private theorem exists_linked (hcat : IsCatena g {a, b, c}) (hab : a ≠ b) {v : Fin n}
    (hv : v ∈ ({a, b, c} : Finset (Fin n))) :
    ∃ w ∈ ({a, b, c} : Finset (Fin n)), w ≠ v ∧ g.Linked v w := by
  have : Nontrivial ↥(↑({a, b, c} : Finset (Fin n)) : Set (Fin n)) :=
    ⟨⟨⟨a, by simp⟩, ⟨b, by simp⟩, fun h ↦ hab (congrArg Subtype.val h)⟩⟩
  obtain ⟨⟨w, hw⟩, h⟩ := SimpleGraph.Preconnected.exists_adj_of_nontrivial
    (SimpleGraph.Connected.preconnected hcat) ⟨v, by simpa using hv⟩
  rw [SimpleGraph.comap_adj, Function.Embedding.subtype_apply, Function.Embedding.subtype_apply,
    Graph.toSimpleGraph_adj] at h
  exact ⟨w, by simpa using hw, fun e ↦ h.1 e.symm, h.2⟩

private theorem exists_of_linked (hg : g.IsForest) {m x y : Fin n} (hx : g.Linked m x)
    (hy : g.Linked m y) (hxy : x ≠ y) :
    ∃ z ∈ hierarchical g ∪ parallel g,
      ({z.1.1, z.1.2, z.2.1, z.2.2} : Finset (Fin n)) = {m, x, y} := by
  simp only [hierarchical, parallel, mem_union, mem_filter, mem_product, Graph.mem_arcs]
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · rcases lt_or_gt_of_ne hxy with h | h
    · exact ⟨((m, x), (m, y)), Or.inr ⟨⟨hx, hy⟩, rfl, h⟩, by ext; simp; tauto⟩
    · exact ⟨((m, y), (m, x)), Or.inr ⟨⟨hy, hx⟩, rfl, h⟩, by ext; simp; tauto⟩
  · exact ⟨((y, m), (m, x)), Or.inl ⟨⟨hy, hx⟩, rfl⟩, by ext; simp; tauto⟩
  · exact ⟨((x, m), (m, y)), Or.inl ⟨⟨hx, hy⟩, rfl⟩, by ext; simp; tauto⟩
  · exact absurd (hg.leftUnique_adj hx hy) hxy

private theorem linked_or (hcat : IsCatena g {a, b, c}) (hab : a ≠ b) :
    g.Linked a b ∨ g.Linked a c := by
  obtain ⟨t, ht, hta, h⟩ := exists_linked hcat hab (v := a) (by simp)
  simp only [mem_insert, mem_singleton] at ht
  rcases ht with rfl | rfl | rfl
  exacts [absurd rfl hta, .inl h, .inr h]

-- §2.2: the catenae of three words are the hierarchical and the parallel ones
theorem isCatena_triple_iff (hg : g.IsForest) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    IsCatena g {a, b, c} ↔ ∃ x ∈ hierarchical g ∪ parallel g,
      ({x.1.1, x.1.2, x.2.1, x.2.2} : Finset (Fin n)) = {a, b, c} := by
  constructor
  · intro hcat
    rcases linked_or hcat hab with h₁ | h₂
    · by_cases h₂ : g.Linked a c
      · exact exists_of_linked hg h₁ h₂ hbc
      · have hc : g.Linked c a ∨ g.Linked c b :=
          linked_or (by rwa [show ({c, a, b} : Finset (Fin n)) = {a, b, c} by ext; simp; tauto])
            hac.symm
        obtain ⟨z, hz, e⟩ :=
          exists_of_linked hg h₁.symm (hc.resolve_left fun h ↦ h₂ h.symm).symm hac
        exact ⟨z, hz, e.trans (by ext; simp; tauto)⟩
    · by_cases h₁ : g.Linked a b
      · exact exists_of_linked hg h₁ h₂ hbc
      · have hb : g.Linked b a ∨ g.Linked b c := linked_or (by rwa [insert_comm]) hab.symm
        obtain ⟨z, hz, e⟩ :=
          exists_of_linked hg h₂.symm (hb.resolve_left fun h ↦ h₁ h.symm).symm hab
        exact ⟨z, hz, e.trans (by ext; simp; tauto)⟩
  · rintro ⟨x, hx, e⟩
    rw [← e, IsCatena]
    simp only [hierarchical, parallel, mem_union, mem_filter, mem_product, Graph.mem_arcs] at hx
    rcases hx with ⟨⟨h₁, h₂⟩, h⟩ | ⟨⟨h₁, h₂⟩, h, -⟩
    all_goals
      have e : (↑({x.1.1, x.1.2, x.2.1, x.2.2} : Finset (Fin n)) : Set (Fin n)) =
          ↑({x.1.1, x.1.2} : Finset (Fin n)) ∪ ↑({x.2.1, x.2.2} : Finset (Fin n)) := by
        ext; simp; tauto
      rw [e]
      exact SimpleGraph.induce_union_connected
        (SimpleGraph.Connected.preconnected (isCatena_pair g h₁ (hg.ne_of_adj h₁)))
        (SimpleGraph.Connected.preconnected (isCatena_pair g h₂ (hg.ne_of_adj h₂)))
        ⟨x.2.1, by simp [h]⟩

end Catena

/-! ### Harmony, head-finality, length and the DLM score -/

section Measures

variable (σ : Arrangement (Fin n) n) (C : Finset ((Fin n × Fin n) × (Fin n × Fin n)))
  (x : (Fin n × Fin n) × (Fin n × Fin n))

/-- The directions in `σ` of the two arcs of a catena. -/
def directions : HeadDirection × HeadDirection :=
  (σ.headDirection x.1.1 x.1.2, σ.headDirection x.2.1 x.2.2)

/-- A catena is harmonic in `σ` when its two arcs have one direction. -/
def IsHarmonic : Prop := (directions σ x).1 = (directions σ x).2

instance : Decidable (IsHarmonic σ x) := inferInstanceAs (Decidable (_ = _))

/-- The head–dependent pairs of the catenae `C`. -/
def pairs : Finset (Fin n × Fin n) := C.image Prod.fst ∪ C.image Prod.snd

/-- The catenae of `C` that are harmonic in `σ`. -/
def harmonic : Finset ((Fin n × Fin n) × (Fin n × Fin n)) := {y ∈ C | IsHarmonic σ y}

/-- The pairs of `C` that are head-final in `σ`. -/
def headFinalPairs : Finset (Fin n × Fin n) :=
  {p ∈ pairs C | σ.headDirection p.1 p.2 = .headFinal}

/-- The pairs of `C` that are head-initial in `σ`. -/
def headInitialPairs : Finset (Fin n × Fin n) :=
  {p ∈ pairs C | σ.headDirection p.1 p.2 = .headInitial}

/-- The summed length in `σ` of the pairs of `C`. -/
def length : ℕ := ∑ p ∈ pairs C, Nat.dist (σ p.1) (σ p.2)

/-- §2.4: the DLM score of `σ` against the baseline law `ν`, the probability of a baseline
linearization in which the pairs of `C` are strictly longer. -/
noncomputable def dlm (ν : Measure (Arrangement (Fin n) n)) : ℝ≥0∞ :=
  ν {τ | length σ C < length τ C}

variable {σ C x}

theorem directions_mirror (h₁ : x.1.1 ≠ x.1.2) (h₂ : x.2.1 ≠ x.2.2) :
    directions σ.mirror x = Prod.map HeadDirection.swap HeadDirection.swap (directions σ x) := by
  simp [directions, Arrangement.headDirection_mirror h₁, Arrangement.headDirection_mirror h₂]

theorem isHarmonic_mirror (h₁ : x.1.1 ≠ x.1.2) (h₂ : x.2.1 ≠ x.2.2) :
    IsHarmonic σ.mirror x ↔ IsHarmonic σ x := by
  rw [IsHarmonic, IsHarmonic, directions_mirror h₁ h₂]
  exact HeadDirection.swap_injective.eq_iff

theorem card_headFinalPairs_add_card_headInitialPairs :
    #(headFinalPairs σ C) + #(headInitialPairs σ C) = #(pairs C) := by
  rw [headFinalPairs, headInitialPairs, ← card_filter_add_card_filter_not (s := pairs C)
    (fun p ↦ σ.headDirection p.1 p.2 = .headFinal)]
  congr 1
  refine congrArg card (filter_congr fun p _ ↦ ?_)
  cases σ.headDirection p.1 p.2 <;> simp

private theorem ne_of_mem_arcs (hg : g.IsForest) {p : Fin n × Fin n} (hp : p ∈ g.arcs) :
    p.1 ≠ p.2 := hg.ne_of_adj (Graph.mem_arcs.1 hp)

private theorem mem_arcs_of_mem_pairs (hC : C ⊆ g.arcs ×ˢ g.arcs) {p : Fin n × Fin n}
    (hp : p ∈ pairs C) : p ∈ g.arcs := by
  simp only [pairs, mem_union, mem_image] at hp
  rcases hp with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩
  exacts [(mem_product.1 (hC hx)).1, (mem_product.1 (hC hx)).2]

-- mirroring keeps the harmonic catenae
theorem harmonic_mirror (hg : g.IsForest) (hC : C ⊆ g.arcs ×ˢ g.arcs) :
    harmonic σ.mirror C = harmonic σ C :=
  filter_congr fun _ hy ↦
    have hy := mem_product.1 (hC hy)
    isHarmonic_mirror (ne_of_mem_arcs hg hy.1) (ne_of_mem_arcs hg hy.2)

-- mirroring exchanges the head-final and the head-initial pairs
theorem headFinalPairs_mirror (hg : g.IsForest) (hC : C ⊆ g.arcs ×ˢ g.arcs) :
    headFinalPairs σ.mirror C = headInitialPairs σ C :=
  filter_congr fun p hp ↦ by
    rw [Arrangement.headDirection_mirror (ne_of_mem_arcs hg (mem_arcs_of_mem_pairs hC hp))]
    cases σ.headDirection p.1 p.2 <;> simp

@[simp] theorem length_mirror : length σ.mirror C = length σ C :=
  sum_congr rfl fun p _ ↦ by simp only [Arrangement.mirror_apply, Fin.dist_rev_rev]

-- mirroring keeps the DLM score against any baseline
@[simp] theorem dlm_mirror (ν : Measure (Arrangement (Fin n) n)) :
    dlm σ.mirror C ν = dlm σ C ν := by
  simp only [dlm, length_mirror]

-- §2.4: the score is the same against a mirrored baseline
theorem dlm_map_mirror (ν : Measure (Arrangement (Fin n) n)) :
    dlm σ C (ν.map Arrangement.mirror) = dlm σ C ν := by
  rw [dlm, dlm, Measure.map_apply .of_discrete .of_discrete]
  congr 1
  ext τ
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, length_mirror]

-- on catenae covering every arc, the length is the total dependency length
theorem length_eq_totalLength (hC : pairs C = g.arcs) : length σ C = (g.map σ).totalLength := by
  rw [Graph.totalLength_map_eq, length, hC]
  simp only [Graph.arcs, Graph.children, sum_filter, Fintype.sum_prod_type]

end Measures

/-! ### Figures 1 and 2a, §§2.1–2.4 -/

/-- §2.1: verbs, nouns, adjectives and adverbs, the categories whose dependencies are
measured. -/
def IsLexical (w : Word) : Prop :=
  w.cat = .VERB ∨ w.cat = .NOUN ∨ w.cat = .ADJ ∨ w.cat = .ADV

instance : DecidablePred IsLexical := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- The dependencies of `g` between lexical words, every word kept in place. -/
def lexical (g : Graph L n) : Graph L n :=
  { g with label := fun v w ↦
      if IsLexical (g.words v) ∧ IsLexical (g.words w) then g.label v w else none }

/-- Figure 1: *We certainly fit into certain parts of the article*. -/
def fig1 : Graph UD.DepRel 9 := Stemma.toGraph <|
  node (.mk' "fit" .VERB)
    [(.nsubj, leaf (.mk' "We" .PRON)), (.advmod, leaf (.mk' "certainly" .ADV))]
    [(.obl, node (.mk' "parts" .NOUN)
      [(.case, leaf (.mk' "into" .ADP)), (.amod, leaf (.mk' "certain" .ADJ))]
      [(.nmod, node (.mk' "article" .NOUN)
        [(.case, leaf (.mk' "of" .ADP)), (.det, leaf (.mk' "the" .DET))] [])])]

/-- Table 2: in Figure 1 the two hierarchical catenae, one of them harmonic, have three pairs of
summed length 7, one of them head-final, and the two parallel catenae, neither harmonic, have
four pairs of summed length 8, two of them head-final. -/
theorem table2 :
    (#(hierarchical (lexical fig1)), #(harmonic (Equiv.refl _) (hierarchical (lexical fig1))),
        #(pairs (hierarchical (lexical fig1))), length (Equiv.refl _) (hierarchical (lexical fig1)),
        #(headFinalPairs (Equiv.refl _) (hierarchical (lexical fig1)))) = (2, 1, 3, 7, 1) ∧
      (#(parallel (lexical fig1)), #(harmonic (Equiv.refl _) (parallel (lexical fig1))),
        #(pairs (parallel (lexical fig1))), length (Equiv.refl _) (parallel (lexical fig1)),
        #(headFinalPairs (Equiv.refl _) (parallel (lexical fig1)))) = (2, 0, 4, 8, 2) := by
  decide

/-- Figure 2a: *We fit certainly into certain of the article parts*, a linearization of the tree
of Figure 1 drawn by the paper's baseline. -/
def fig2a : Arrangement (Fin 9) 9 :=
  ⟨![0, 2, 1, 3, 4, 8, 5, 6, 7], ![0, 2, 1, 3, 4, 6, 7, 8, 5], by decide, by decide⟩

-- §2.4: the baseline sample is projective and its hierarchical catenae are 12 words long
theorem length_fig2a :
    (fig1.map fig2a).IsProjective ∧ length fig2a (hierarchical (lexical fig1)) = 12 := by
  decide

/-! ### The four orders of a chain, (6) -/

/-- The chain of (6): `A` heads `B`, which heads `C`. -/
def chain : Graph Unit 3 := Stemma.toGraph <|
  node (.mk' "A" .X) [] [((), node (.mk' "B" .X) [] [((), leaf (.mk' "C" .X))])]

/-- (6c): the order `A C B`, initial over final; (6a) is the identity, (6b) its mirror image and
(6d) the mirror image of (6c). -/
def ex6c : Arrangement (Fin 3) 3 := Equiv.swap 1 2

/-- (6): the harmonic orders of the chain have length 2 and the disharmonic ones length 3; (6d),
the mirror image of (6c), has its length, and is final over initial where (6c) is initial over
final. -/
theorem ex6 :
    (chain.map (.refl _)).totalLength = 2 ∧
      (chain.map (Arrangement.mirror (Equiv.refl (Fin 3)))).totalLength = 2 ∧
      (chain.map ex6c).totalLength = 3 ∧ (chain.map ex6c.mirror).totalLength = 3 ∧
      directions ex6c.mirror ((0, 1), (1, 2)) = (.headFinal, .headInitial) ∧
      directions ex6c ((0, 1), (1, 2)) = (.headInitial, .headFinal) := by
  have h₁ : (chain.map (.refl _)).totalLength = 2 := by decide
  have h₂ : (chain.map ex6c).totalLength = 3 := by decide
  refine ⟨h₁, ?_, h₂, ?_, by decide, by decide⟩
  · rw [Graph.totalLength_map_mirror, h₁]
  · rw [Graph.totalLength_map_mirror, h₂]

-- (6) lists the projective orders of the chain, one for each pair of directions
theorem projective_chain :
    {σ : Arrangement (Fin 3) 3 | (chain.map σ).IsProjective} =
        ↑({.refl _, Arrangement.mirror (Equiv.refl (Fin 3)), ex6c, ex6c.mirror} :
          Finset (Arrangement (Fin 3) 3)) ∧
      Set.BijOn (directions · ((0, 1), (1, 2))) {σ | (chain.map σ).IsProjective} .univ := by
  have e : {σ : Arrangement (Fin 3) 3 | (chain.map σ).IsProjective} =
      ↑({.refl _, Arrangement.mirror (Equiv.refl (Fin 3)), ex6c, ex6c.mirror} :
        Finset (Arrangement (Fin 3) 3)) := by
    ext σ
    simp only [Set.mem_ofPred_eq, mem_coe]
    revert σ
    decide
  refine ⟨e, ?_⟩
  rw [e]
  refine ⟨fun _ _ ↦ trivial, ?_, ?_⟩
  · intro σ hσ τ hτ h
    simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hσ hτ
    rcases hσ with rfl | rfl | rfl | rfl <;> rcases hτ with rfl | rfl | rfl | rfl <;>
      first | rfl | exact absurd h (by decide)
  · rintro ⟨_ | _, _ | _⟩ -
    · exact ⟨.refl _, by simp, by decide⟩
    · exact ⟨ex6c, by simp, by decide⟩
    · exact ⟨ex6c.mirror, by simp, by decide⟩
    · exact ⟨Arrangement.mirror (Equiv.refl (Fin 3)), by simp, by decide⟩

/-! ### Mirror-invariant laws -/

section Laws

variable {μ ν : Measure (Arrangement (Fin n) n)} {f : ℕ → ℝ≥0∞}
  {C : Finset ((Fin n × Fin n) × (Fin n × Fin n))} {x : (Fin n × Fin n) × (Fin n × Fin n)}
  {ε : ℝ≥0∞}

theorem map_mirror_eq_self (hμ : ∀ σ, μ {σ} = f (g.map σ).totalLength) :
    μ.map Arrangement.mirror = μ := by
  refine Measure.ext_iff_singleton.2 fun σ ↦ ?_
  have : Arrangement.mirror ⁻¹' {σ} = {σ.mirror} := by
    ext τ
    exact Arrangement.mirror_involutive.eq_iff
  rw [Measure.map_apply .of_discrete .of_discrete, this, hμ, hμ, Graph.totalLength_map_mirror]

/-- Under a law of linearizations invariant under mirroring, the DLM score has one distribution
at `k` head-final pairs and at `k` head-initial pairs, so no such law makes the score fall with
head-finality. Every law weighting dependency length alone is one (`map_mirror_eq_self`). -/
theorem measure_dlm_headFinal (hμ : μ.map Arrangement.mirror = μ) (hg : g.IsForest)
    (hC : C ⊆ g.arcs ×ˢ g.arcs) (S : Set ℝ≥0∞) (k : ℕ) :
    μ {σ | dlm σ C ν ∈ S ∧ #(headFinalPairs σ C) = k} =
      μ {σ | dlm σ C ν ∈ S ∧ #(headInitialPairs σ C) = k} := by
  have e : {σ | dlm σ C ν ∈ S ∧ #(headInitialPairs σ C) = k} =
      Arrangement.mirror ⁻¹' {σ | dlm σ C ν ∈ S ∧ #(headFinalPairs σ C) = k} := by
    ext σ
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, dlm_mirror, headFinalPairs_mirror hg hC]
  rw [e, ← Measure.map_apply .of_discrete .of_discrete, hμ]

/-- p. 412: under a law of linearizations invariant under mirroring, reversing the directions of
two dependencies preserves the probability of every event about their directions. Every law
weighting dependency length alone is one (`map_mirror_eq_self`). -/
theorem measure_swap_directions (hμ : μ.map Arrangement.mirror = μ) (h₁ : x.1.1 ≠ x.1.2)
    (h₂ : x.2.1 ≠ x.2.2) (S : Set (HeadDirection × HeadDirection)) :
    μ {σ | Prod.map HeadDirection.swap HeadDirection.swap (directions σ x) ∈ S} =
      μ {σ | directions σ x ∈ S} := by
  have e : {σ | Prod.map HeadDirection.swap HeadDirection.swap (directions σ x) ∈ S} =
      Arrangement.mirror ⁻¹' {σ | directions σ x ∈ S} := by
    ext σ
    simp [directions_mirror h₁ h₂]
  rw [e, ← Measure.map_apply .of_discrete .of_discrete, hμ]

private theorem measure_swap_eq (hμ : μ.map Arrangement.mirror = μ) (h₁ : x.1.1 ≠ x.1.2)
    (h₂ : x.2.1 ≠ x.2.2) (c : HeadDirection × HeadDirection) :
    μ {σ | directions σ x = Prod.map HeadDirection.swap HeadDirection.swap c} =
      μ {σ | directions σ x = c} := by
  have h := measure_swap_directions hμ h₁ h₂ {c}
  simp only [Set.mem_singleton_iff] at h
  rw [← h]
  congr 1
  ext σ
  exact (HeadDirection.swap_involutive.prodMap HeadDirection.swap_involutive).eq_iff.symm

private theorem ne_of_mem_catena (hg : g.IsForest) (hx : x ∈ hierarchical g ∪ parallel g) :
    x.1.1 ≠ x.1.2 ∧ x.2.1 ≠ x.2.2 := by
  have hx : x ∈ g.arcs ×ˢ g.arcs := by
    rcases mem_union.1 hx with hx | hx <;> exact (mem_filter.1 hx).1
  exact ⟨ne_of_mem_arcs hg (mem_product.1 hx).1, ne_of_mem_arcs hg (mem_product.1 hx).2⟩

-- (6), Table 4: a final-over-initial catena is as likely as an initial-over-final one
theorem measure_finalOverInitial (hμ : μ.map Arrangement.mirror = μ) (hg : g.IsForest)
    (hx : x ∈ hierarchical g) :
    μ {σ | directions σ x = (.headFinal, .headInitial)} =
      μ {σ | directions σ x = (.headInitial, .headFinal)} :=
  have h := ne_of_mem_catena hg (mem_union_left _ hx)
  measure_swap_eq hμ h.1 h.2 (.headInitial, .headFinal)

-- p. 412: parallel dependents pile up before their head as often as after it
theorem measure_pileUp (hμ : μ.map Arrangement.mirror = μ) (hg : g.IsForest)
    (hx : x ∈ parallel g) :
    μ {σ | directions σ x = (.headFinal, .headFinal)} =
      μ {σ | directions σ x = (.headInitial, .headInitial)} :=
  have h := ne_of_mem_catena hg (mem_union_right _ hx)
  measure_swap_eq hμ h.1 h.2 (.headInitial, .headInitial)

/-- `ν` with the final-over-initial configuration of the catena `x` downweighted by `ε`. -/
noncomputable def disprefer (ν : Measure (Arrangement (Fin n) n))
    (x : (Fin n × Fin n) × (Fin n × Fin n)) (ε : ℝ≥0∞) : Measure (Arrangement (Fin n) n) :=
  ν.withDensity fun σ ↦ if directions σ x = (.headFinal, .headInitial) then ε else 1

theorem disprefer_apply (c : HeadDirection × HeadDirection) :
    disprefer ν x ε {σ | directions σ x = c} =
      (if c = (.headFinal, .headInitial) then ε else 1) * ν {σ | directions σ x = c} := by
  rw [disprefer, withDensity_apply _ .of_discrete, ← setLIntegral_const]
  exact setLIntegral_congr_fun .of_discrete fun σ hσ ↦
    congrArg (fun c ↦ if c = (.headFinal, .headInitial) then ε else 1) hσ

@[simp] theorem disprefer_one : disprefer ν x 1 = ν := by
  simp [disprefer, withDensity_const]

/-- Table 4, Fig. 6: let `disprefer ν x ε` downweight by `ε < 1` the final-over-initial
configuration of two dependencies under a mirror-invariant law `ν`. Under `ν` the lower
dependency is as likely to be harmonic with the upper one when head-final as when head-initial;
under `disprefer ν x ε` the head-final probability is unchanged and the head-initial one is
greater. Every conditioning set has positive probability. -/
theorem cond_harmonic [IsFiniteMeasure ν] (hν : ν.map Arrangement.mirror = ν)
    (h₁ : x.1.1 ≠ x.1.2) (h₂ : x.2.1 ≠ x.2.2) (hε : ε < 1)
    (hII : ν {σ | directions σ x = (.headInitial, .headInitial)} ≠ 0)
    (hFI : ν {σ | directions σ x = (.headFinal, .headInitial)} ≠ 0) :
    (∀ d, ν {σ | (directions σ x).2 = d} ≠ 0 ∧
        disprefer ν x ε {σ | (directions σ x).2 = d} ≠ 0) ∧
      ν[{σ | IsHarmonic σ x} | {σ | (directions σ x).2 = .headFinal}] =
        ν[{σ | IsHarmonic σ x} | {σ | (directions σ x).2 = .headInitial}] ∧
      (disprefer ν x ε)[{σ | IsHarmonic σ x} | {σ | (directions σ x).2 = .headFinal}] =
        ν[{σ | IsHarmonic σ x} | {σ | (directions σ x).2 = .headFinal}] ∧
      (disprefer ν x ε)[{σ | IsHarmonic σ x} | {σ | (directions σ x).2 = .headFinal}] <
        (disprefer ν x ε)[{σ | IsHarmonic σ x} | {σ | (directions σ x).2 = .headInitial}] := by
  set A := fun c : HeadDirection × HeadDirection ↦ {σ | directions σ x = c}
  have hB : ∀ d, {σ : Arrangement (Fin n) n | (directions σ x).2 = d} =
      A (d.swap, d) ∪ A (d, d) := fun d ↦ by
    ext σ
    simp only [A, Set.mem_ofPred_eq, Set.mem_union]
    generalize directions σ x = y
    obtain ⟨d₁, d₂⟩ := y
    cases d <;> cases d₁ <;> cases d₂ <;> decide
  have hBH : ∀ d, {σ : Arrangement (Fin n) n | (directions σ x).2 = d} ∩
      {σ | IsHarmonic σ x} = A (d, d) := fun d ↦ by
    ext σ
    simp only [A, IsHarmonic, Set.mem_ofPred_eq, Set.mem_inter_iff]
    generalize directions σ x = y
    obtain ⟨d₁, d₂⟩ := y
    cases d <;> cases d₁ <;> cases d₂ <;> decide
  have hdisj : ∀ d, Disjoint (A (d.swap, d)) (A (d, d)) := fun d ↦
    Set.disjoint_left.2 fun σ h₁ h₂ ↦ HeadDirection.swap_ne_self d
      (Prod.ext_iff.1 ((show directions σ x = _ from h₁).symm.trans h₂)).1
  have hcond : ∀ (κ : Measure (Arrangement (Fin n) n)) d,
      κ[{σ | IsHarmonic σ x} | {σ | (directions σ x).2 = d}] =
        (κ (A (d.swap, d)) + κ (A (d, d)))⁻¹ * κ (A (d, d)) := fun κ d ↦ by
    rw [cond_apply .of_discrete, hBH, hB, measure_union (hdisj d) .of_discrete]
  set p := ν (A (.headInitial, .headInitial))
  set q := ν (A (.headFinal, .headInitial))
  have hFF : ν (A (.headFinal, .headFinal)) = p :=
    measure_swap_eq hν h₁ h₂ (.headInitial, .headInitial)
  have hIF : ν (A (.headInitial, .headFinal)) = q :=
    measure_swap_eq hν h₁ h₂ (.headFinal, .headInitial)
  have hw : ∀ c, disprefer ν x ε (A c) =
      (if c = (.headFinal, .headInitial) then ε else 1) * ν (A c) := disprefer_apply
  have hp : p ≠ ⊤ := measure_ne_top _ _
  have hq : q ≠ ⊤ := measure_ne_top _ _
  have hνF : ν[{σ | IsHarmonic σ x} | {σ | (directions σ x).2 = .headFinal}] = (q + p)⁻¹ * p := by
    rw [hcond]; simp only [HeadDirection.swap_headFinal, hFF, hIF]
  refine ⟨fun d ↦ ?_, ?_, ?_, ?_⟩
  · have hsub : A (d, d) ⊆ {σ | (directions σ x).2 = d} := hB d ▸ Set.subset_union_right
    have hdd : ν (A (d, d)) = p := by cases d; exacts [rfl, hFF]
    have hμdd : disprefer ν x ε (A (d, d)) = p := by rw [hw, hdd]; cases d <;> simp
    refine ⟨fun h ↦ hII ?_, fun h ↦ hII ?_⟩
    · have := measure_mono_null hsub h
      rw [hdd] at this
      exact this
    · have := measure_mono_null hsub h
      rw [hμdd] at this
      exact this
  · rw [hνF, hcond]; rfl
  · rw [hνF, hcond, hw, hw]
    simp only [HeadDirection.swap_headFinal, hFF, hIF]
    simp
  · rw [hcond, hcond, hw, hw, hw, hw]
    simp only [HeadDirection.swap_headFinal, HeadDirection.swap_headInitial, hFF, hIF]
    simp only [Prod.mk.injEq, reduceCtorEq, and_self, and_false, and_true, ↓reduceIte, one_mul]
    refine ENNReal.mul_lt_mul_left hII hp (ENNReal.inv_lt_inv.2 ?_)
    refine ENNReal.add_lt_add_right hp ?_
    simpa using ENNReal.mul_lt_mul_left hFI hq hε

end Laws

/-! ### The chain of (6) under the uniform law -/

-- against the uniform baseline, four of the six orders of the chain are longer than the identity
theorem dlm_chain : dlm (Equiv.refl _) (hierarchical chain) Measure.count = 4 := by
  rw [dlm, ← Finset.coe_filter_univ, Measure.count_apply_finset]
  exact (Nat.cast_inj (R := ℝ≥0∞)).2 (by decide)

-- the hierarchical catena of the chain covers its arcs, so its length is the total length
example (σ : Arrangement (Fin 3) 3) : length σ (hierarchical chain) = (chain.map σ).totalLength :=
  length_eq_totalLength (by decide)

-- the uniform law on the orders of the chain, which weights dependency length alone, meets the
-- hypotheses of `measure_dlm_headFinal` and `cond_harmonic`
example : chain.IsForest ∧ hierarchical chain ⊆ chain.arcs ×ˢ chain.arcs ∧
    (Measure.count : Measure (Arrangement (Fin 3) 3)).map Arrangement.mirror = Measure.count ∧
    Measure.count {σ : Arrangement (Fin 3) 3 |
      directions σ ((0, 1), (1, 2)) = (.headInitial, .headInitial)} ≠ 0 ∧
    Measure.count {σ : Arrangement (Fin 3) 3 |
      directions σ ((0, 1), (1, 2)) = (.headFinal, .headInitial)} ≠ 0 := by
  refine ⟨by decide, filter_subset _ _, map_mirror_eq_self (g := chain) (f := fun _ ↦ 1)
    Measure.count_singleton, ?_, ?_⟩ <;>
    rw [Ne, Measure.count_eq_zero_iff]
  exacts [Set.Nonempty.ne_empty ⟨.refl _, by decide⟩,
    Set.Nonempty.ne_empty ⟨ex6c.mirror, by decide⟩]

-- a law concentrated on one order is not mirror-invariant: the identity order of the chain has no
-- head-final pair and two head-initial ones, against `measure_dlm_headFinal`
example : Measure.dirac (Equiv.refl (Fin 3))
      {σ | dlm σ (hierarchical chain) .count ∈ Set.univ ∧
        #(headFinalPairs σ (hierarchical chain)) = 0} = 1 ∧
    Measure.dirac (Equiv.refl (Fin 3))
      {σ | dlm σ (hierarchical chain) .count ∈ Set.univ ∧
        #(headInitialPairs σ (hierarchical chain)) = 0} = 0 := by
  refine ⟨Measure.dirac_apply_of_mem ?_, ?_⟩
  · simp only [Set.mem_ofPred_eq, Set.mem_univ, true_and]
    decide
  · rw [Measure.dirac_apply,
      Set.indicator_of_notMem (by simp only [Set.mem_ofPred_eq, Set.mem_univ, true_and]; decide)]

-- a law concentrated on (6c), initial over final, breaks `measure_swap_directions`
example : Measure.dirac ex6c {σ | Prod.map HeadDirection.swap HeadDirection.swap
      (directions σ ((0, 1), (1, 2))) ∈ ({(.headInitial, .headFinal)} : Set _)} = 0 ∧
    Measure.dirac ex6c
      {σ | directions σ ((0, 1), (1, 2)) ∈ ({(.headInitial, .headFinal)} : Set _)} = 1 := by
  refine ⟨?_, Measure.dirac_apply_of_mem
    (by simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]; decide)⟩
  rw [Measure.dirac_apply,
    Set.indicator_of_notMem (by simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]; decide)]

-- without the penalty the asymmetry of `cond_harmonic` vanishes: at `ε = 1` the law is `ν`
example {ν : Measure (Arrangement (Fin n) n)} [IsFiniteMeasure ν]
    {x : (Fin n × Fin n) × (Fin n × Fin n)} (hν : ν.map Arrangement.mirror = ν)
    (h₁ : x.1.1 ≠ x.1.2) (h₂ : x.2.1 ≠ x.2.2)
    (hII : ν {σ | directions σ x = (.headInitial, .headInitial)} ≠ 0)
    (hFI : ν {σ | directions σ x = (.headFinal, .headInitial)} ≠ 0) :
    (disprefer ν x 1)[{σ | IsHarmonic σ x} | {σ | (directions σ x).2 = .headFinal}] =
      (disprefer ν x 1)[{σ | IsHarmonic σ x} | {σ | (directions σ x).2 = .headInitial}] := by
  rw [disprefer_one]
  exact (cond_harmonic hν h₁ h₂ (ε := 0) zero_lt_one hII hFI).2.1

/-! ### Nested ordering, §2.2 -/

-- p. 404: dependents of distinct sizes arranged at random grow outward from a head-initial head,
-- the nested order, with probability `1 / k!`: 16.67% for three, 4.17% for four
theorem uniformOn_strictMono {α : Type*} [Fintype α] [DecidableEq α] {ℓ : α → ℕ}
    (hℓ : Function.Injective ℓ) :
    uniformOn .univ {a : Arrangement α (Fintype.card α) | StrictMono (ℓ ∘ a.symm)} =
      ((Fintype.card α)! : ℝ≥0∞)⁻¹ := by
  set e := Fintype.equivFin α
  set f : Fin (Fintype.card α) → ℕ := ℓ ∘ e.symm
  have hf : Function.Injective f := hℓ.comp e.symm.injective
  have hs : {a : Arrangement α (Fintype.card α) | StrictMono (ℓ ∘ a.symm)} =
      {e.trans (Tuple.sort f).symm} := by
    ext a
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · intro h
      have hπ : a.symm.trans e = Tuple.sort f := by
        refine Tuple.eq_sort_iff.2 ⟨?_, fun i j hij hfij ↦
          absurd (hf hfij) ((a.symm.trans e).injective.ne hij.ne)⟩
        simpa [f, Function.comp_def] using h.monotone
      rw [← hπ]
      ext x
      simp
    · rintro rfl
      simpa [f, Function.comp_def] using (Tuple.monotone_sort f).strictMono_of_injective
        (hf.comp (Tuple.sort f).injective)
  rw [uniformOn_univ, hs, Measure.count_singleton, Fintype.card_equiv e, one_div]

end JingBlasiBickel2022
