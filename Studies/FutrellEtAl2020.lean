module

public import Linglib.Syntax.DependencyGrammar.HeadDirection
public import Linglib.Syntax.DependencyGrammar.Projectivity
public import Linglib.Syntax.DependencyGrammar.Reordering

/-!
# Futrell, Levy and Gibson (2020): Dependency Locality as an Explanatory Principle for Word Order

The length of a dependency is the distance in words between a head and its dependent, and the
dependency length of a sentence is the sum of the lengths of its dependencies,
`Digraph.totalLength`. Dependency length minimization is the hypothesis that
word orders keep this sum low. A dependency tree and an order of its words determine the sum, so
this file states each word order as a pullback of one tree and asks which orders are short.

A dependency is at least one word long, so a tree of `k` dependencies has length at least `k`,
and exactly `k` when every dependent stands next to its head. A tree in which each head has one
dependent has length `k` exactly when it has a head direction, every dependent lying on the same
side of its head (`totalLength_eq_card_arcs_iff_exists_hasDirection`). When a head has two
dependents no order with a head direction has length `k`, while the order with one dependent on
each side of the head may (`split_lt_of_hasDirection`). The mirror image of an order has the
opposite head direction (`Digraph.HasDirection.mirror`) and the same length
(`Digraph.totalLength_mirror`).

For the phrases after a head, the order in which they grow outward is shortest
(`shortBeforeLong_le_reorderDependents`), and the mirror images of two orders compare as the
orders do, so before a final head the longer phrase goes first. Exchanging two neighbouring
phrases after a head changes the length by the difference of their sizes
(`Digraph.totalLength_reorderDependents_swap_add`). Placing a particle after the
object therefore lengthens the dependencies by one word less than the object has
(`particleShift`), more the heavier the object is. Displacement makes a tree nonprojective, and for
a line of Ovid a projective order of the same tree is shorter (`ovidProjective_lt`).

## Implementation notes

* The figures carry no relation labels, so each tree is a digraph on the positions of its
  sentence, with an arc from each head to each of its dependents.
* The figures on the order of phrases draw one arc from the head into each bracketed phrase. Here
  the first word of a phrase heads its other words, so that a phrase is the set of positions
  reachable from its first word and `Digraph.reorderDependents` moves it as a block; the arcs
  inside a phrase have the same lengths in every order of the phrases.
* The length of a dependency is `Nat.dist`, the number of words between head and dependent plus
  one, the measure of the totals printed under the figures.
* The paper calls an order projective when its arcs can be drawn without crossing. The examples
  check both `Digraph.IsProjective` and `Digraph.IsPlanar`.

## TODO

* The corpus studies are not formalized: the random baselines, the linearization models and the
  comparison of languages. The head-final proportions and mean dependency lengths that the paper
  tabulates by language are the rows of `Data.UD.DependencyLength.FutrellEtAl2020`.
* The conversion of a Universal Dependencies tree to one in which adpositions head their nouns
  is not defined; the trees here are drawn after it.
* A head with several dependents is shortest with them on alternating sides in order of length
  [gildea-temperley-2007]; only the case of two dependents is proved.

## References

* [futrell-levy-gibson-2020]
* [gildea-temperley-2007]
* [gildea-temperley-2010]
* [behaghel-1909]
-/

@[expose] public section

namespace FutrellEtAl2020

open Finset Relation

variable {n : ℕ} {G : Digraph (Fin n)} [DecidableRel G.Adj] {r : Fin n} {d : HeadDirection}

/-! ### Projectivity and displacement -/

/-- (3) "I think a woman arrived who you know", with the relative clause extraposed from
*woman*. -/
abbrev extraposition : Digraph (Fin 8) :=
  .ofArcs
    [(1, 0), (1, 4), (4, 3), (3, 2), (3, 7), (7, 5), (7, 6)]

/-- (4) "I know what he thinks you did yesterday", with *what* the object of *did*. -/
abbrev whMovement : Digraph (Fin 8) :=
  .ofArcs
    [(1, 0), (1, 4), (4, 3), (4, 6), (6, 5), (6, 2), (6, 7)]

example : ¬ extraposition.IsProjective ∧ ¬ extraposition.IsPlanar := by decide
example : ¬ whMovement.IsProjective ∧ ¬ whMovement.IsPlanar := by decide

/-- (5a) "In nova fert animus mutatas dicere formas corpora", in Ovid's order. -/
abbrev ovid : Digraph (Fin 8) :=
  .ofArcs
    [(2, 3), (2, 5), (5, 6), (6, 4), (4, 0), (0, 7), (7, 1)]

/-- (5b) "Fert animus dicere formas mutatas in corpora nova", the tree of (5a) in an order in
which each phrase is contiguous. -/
abbrev ovidProjective : Digraph (Fin 8) := ovid.linearize [2, 3, 5, 6, 4, 0, 7, 1] (by decide)

/-- Ovid's order (5a) is nonprojective, and the projective order (5b) of the same tree has
shorter dependencies. -/
theorem ovidProjective_lt :
    ¬ ovid.IsProjective ∧ ovidProjective.IsProjective ∧
      ovidProjective.totalLength < ovid.totalLength := by
  decide

/-! ### Short before long after a head, long before short before it -/

/-- (7a) A [B] [C D] [E F G]: a head followed by phrases of one, two and three words. -/
abbrev shortBeforeLong : Digraph (Fin 7) :=
  .ofArcs [(0, 1), (0, 2), (2, 3), (0, 4), (4, 5), (4, 6)]

/-- The head of (7a) as a member of its local subtree. -/
abbrev head : shortBeforeLong.localSubtree 0 := ⟨0, shortBeforeLong.self_mem_localSubtree 0⟩

/-- (7b) A [E F G] [C D] [B]: the phrases of (7a) with the longest first and the shortest
last. -/
abbrev longBeforeShort : Digraph (Fin 7) :=
  shortBeforeLong.reorderDependents 0 (.swap ⟨1, by decide⟩ ⟨4, by decide⟩)

private theorem shortBeforeLong_isBranching : shortBeforeLong.IsBranching := by decide +kernel

private theorem shortBeforeLong_isProjective : shortBeforeLong.IsProjective := by decide +kernel

private theorem monovaryOn_shortBeforeLong :
    MonovaryOn (fun c : shortBeforeLong.localSubtree 0 ↦ #(shortBeforeLong.reachSet c).toFinset)
      (shortBeforeLong.localArrangement 0)
      ↑((shortBeforeLong.localArrangement 0).after head) := by
  decide +kernel

/-- (7): the phrases of (7a) grow outward from their head, and no reordering of them has shorter
dependencies. -/
theorem shortBeforeLong_le_reorderDependents (σ : Equiv.Perm (shortBeforeLong.localSubtree 0))
    (hσ : σ head = head) :
    shortBeforeLong.totalLength ≤ (shortBeforeLong.reorderDependents 0 σ).totalLength := by
  refine Digraph.totalLength_le_reorderDependents shortBeforeLong_isBranching
    shortBeforeLong_isProjective (fun c hc ↦ ?_) monovaryOn_shortBeforeLong
  refine WordOrder.Arrangement.mem_after.2 (Digraph.localArrangement_precedes.2 ?_)
  refine Fin.pos_iff_ne_zero.2 fun e ↦ Equiv.Perm.mem_support.1 hc ?_
  rw [show c = head from Subtype.ext e, hσ]

-- (7a), (7b)
theorem shortBeforeLong_lt_longBeforeShort :
    shortBeforeLong.totalLength < longBeforeShort.totalLength :=
  (Digraph.totalLength_lt_reorderDependents_iff shortBeforeLong_isBranching
    shortBeforeLong_isProjective (by decide +kernel) monovaryOn_shortBeforeLong).2
    (by decide +kernel)

-- (8a), (8b)
theorem mirror_shortBeforeLong_lt_mirror_longBeforeShort :
    shortBeforeLong.mirror.totalLength < longBeforeShort.mirror.totalLength := by
  simpa [Digraph.totalLength_mirror] using shortBeforeLong_lt_longBeforeShort

/-! ### Consistent head direction -/

omit [DecidableRel G.Adj] in
private theorem dist_eq_one_of_headInitial (hT : G.IsArborescence r)
    (hc : Relator.RightUnique G.Adj) (h : G.HasDirection .headInitial) ⦃v w : Fin n⦄
    (hvw : G.Adj v w) : Nat.dist v w = 1 := by
  have hle : ∀ {a b : Fin n}, G.Reachable a b → a ≤ b := fun hab ↦ by
    induction hab with
    | refl => exact le_rfl
    | tail _ hbc ih => exact ih.trans (h hbc).le
  have hlt : v < w := h hvw
  by_contra hne
  have hx : (v : ℕ) + 1 < n := by
    simp only [Nat.dist, Fin.lt_def] at hne hlt
    omega
  rcases ReflTransGen.total_of_right_unique hc (hT.reachable v)
    (hT.reachable ⟨v + 1, hx⟩) with hvx | hxv
  · obtain e | ⟨c, hvc, hcx⟩ := ReflTransGen.cases_head hvx
    · simpa using congrArg Fin.val e
    · have := hle (hc hvc hvw ▸ hcx)
      simp only [Nat.dist, Fin.lt_def, Fin.le_def] at hne hlt this
      omega
  · simpa [Fin.le_def] using hle hxv

/-- (9): a tree in which each head has one dependent has the least dependency length, one word
for each dependency, exactly when it has a head direction. -/
theorem totalLength_eq_card_arcs_iff_exists_hasDirection (hT : G.IsArborescence r)
    (hc : Relator.RightUnique G.Adj) : G.totalLength = #G.arcs ↔ ∃ d, G.HasDirection d := by
  have hl : ∀ v, ¬ G.Adj v v := fun _ ↦ hT.not_adj_self
  refine ⟨fun h ↦ ?_, ?_⟩
  · have h₁ := (Digraph.totalLength_eq_card_arcs_iff hl).1 h
    by_cases hr : ∃ c, G.Adj r c
    · obtain ⟨c, hrc⟩ := hr
      obtain ⟨d, hd⟩ : ∃ d : HeadDirection, d.Orders r c :=
        (lt_or_gt_of_ne (hT.ne_of_adj hrc)).elim (⟨.headInitial, ·⟩) (⟨.headFinal, ·⟩)
      refine ⟨d, fun v ↦ ?_⟩
      induction hT.reachable v with
      | refl => exact fun w hw ↦ hc hrc hw ▸ hd
      | @tail u v _ huv ih =>
        intro w hvw
        have o := ih huv
        have e₁ := h₁ huv
        have e₂ := h₁ hvw
        have hne : (u : ℕ) ≠ w := Fin.val_ne_of_ne fun e ↦
          hT.not_reachable_of_adj huv (e ▸ .single hvw)
        cases d <;>
          simp only [HeadDirection.headInitial_orders, HeadDirection.headFinal_orders, Fin.lt_def,
            Nat.dist] at o e₁ e₂ ⊢ <;>
          omega
    · refine ⟨.headInitial, fun v w hvw ↦ absurd ?_ hr⟩
      obtain rfl | ⟨c, hrc, -⟩ := ReflTransGen.cases_head (hT.reachable v)
      exacts [⟨w, hvw⟩, ⟨c, hrc⟩]
  · rintro ⟨d, hd⟩
    cases d with
    | headInitial =>
      exact (Digraph.totalLength_eq_card_arcs_iff hl).2 (dist_eq_one_of_headInitial hT hc hd)
    | headFinal =>
      have hT' : G.mirror.IsArborescence r.rev := hT.comap Fin.revPerm
      have hl' : ∀ v, ¬ G.mirror.Adj v v := fun _ ↦ hT'.not_adj_self
      have := (Digraph.totalLength_eq_card_arcs_iff hl').2 (dist_eq_one_of_headInitial hT'
        (fun _ _ _ h₁ h₂ ↦ Fin.rev_injective (hc h₁ h₂)) hd.mirror)
      rwa [Digraph.totalLength_mirror, Digraph.card_arcs_mirror] at this

/-- (9a) The chain A → B → C → D in the order A B C D. -/
abbrev chain : Digraph (Fin 4) := .ofArcs [(0, 1), (1, 2), (2, 3)]

/-- (9b) The chain of (9a) in the order A C D B. -/
abbrev mixedChain : Digraph (Fin 4) := chain.linearize [0, 2, 3, 1] (by decide)

example : chain.totalLength = 3 ∧ mixedChain.totalLength = 6 := by decide
example : chain.HasDirection .headInitial ∧ ¬ ∃ d, mixedChain.HasDirection d := by decide

-- (9): the orders of the chain with three words of dependency length are those with a head
-- direction
theorem totalLength_comap_chain_eq_iff (σ : Equiv.Perm (Fin 4)) :
    (chain.comap σ).totalLength = 3 ↔ ∃ d, (chain.comap σ).HasDirection d := by
  have hc : Relator.RightUnique chain.Adj := by unfold Relator.RightUnique; decide
  have hc' : Relator.RightUnique (chain.comap σ).Adj := fun _ _ _ h₁ h₂ ↦
    σ.injective (hc (h₁ : chain.Adj _ _) h₂)
  rw [← totalLength_eq_card_arcs_iff_exists_hasDirection
    ((by decide : chain.IsArborescence 0).comap σ) hc', Digraph.card_arcs_comap,
    (by decide : #chain.arcs = 3)]

/-! ### Exceptions to consistent head direction -/

/-- (10a) A B C D: the head A before both of its dependents, B and the phrase C D. -/
abbrev sameSide : Digraph (Fin 4) := .ofArcs [(0, 1), (0, 2), (2, 3)]

/-- (10b) B A C D: the tree of (10a) with the one-word dependent before the head. -/
abbrev split : Digraph (Fin 4) := sameSide.linearize [1, 0, 2, 3] (by decide)

example : sameSide.totalLength = 4 ∧ split.totalLength = 3 := by decide

/-- (10): the order (10b), with one dependent on each side of the head, is shorter than every
order of the same tree that has a head direction. -/
theorem split_lt_of_hasDirection (σ : Equiv.Perm (Fin 4)) (h : (sameSide.comap σ).HasDirection d) :
    split.totalLength < (sameSide.comap σ).totalLength := by
  have hl : ∀ v, ¬ (sameSide.comap σ).Adj v v := fun v hv ↦
    (by decide : ∀ v, ¬ sameSide.Adj v v) _ hv
  have h₁ : (sameSide.comap σ).Adj (σ.symm 0) (σ.symm 1) := by simp
  have h₂ : (sameSide.comap σ).Adj (σ.symm 0) (σ.symm 2) := by simp
  have := Digraph.card_arcs_lt_totalLength hl h₁ h₂ (σ.symm.injective.ne (by decide))
    (h h₁) (h h₂)
  rwa [Digraph.card_arcs_comap] at this

/-! ### Heavy NP shift -/

/-- (11a) "John threw out the trash". -/
abbrev lightEarly : Digraph (Fin 5) :=
  .ofArcs [(1, 0), (1, 2), (1, 4), (4, 3)]

/-- (11b) "John threw the trash out": the particle and the object of (11a) exchanged. -/
abbrev lightLate : Digraph (Fin 5) :=
  lightEarly.reorderDependents 1 (.swap ⟨2, by decide⟩ ⟨4, by decide⟩)

/-- (11c) "John threw out the trash sitting in the kitchen". -/
abbrev heavyEarly : Digraph (Fin 9) :=
  .ofArcs
    [(1, 0), (1, 2), (1, 4), (4, 3), (4, 5), (5, 6), (6, 8),
     (8, 7)]

/-- (11d) "John threw the trash sitting in the kitchen out": the particle and the object of (11c)
exchanged. -/
abbrev heavyLate : Digraph (Fin 9) :=
  heavyEarly.reorderDependents 1 (.swap ⟨2, by decide⟩ ⟨4, by decide⟩)

-- The exchanged orders are the trees drawn in (11b) and (11d).
example : ∀ v w, lightLate.Adj v w ↔
    (Digraph.ofArcs [(1, 0), (1, 3), (3, 2), (1, 4)] : Digraph (Fin 5)).Adj v w := by
  decide +kernel
example : ∀ v w, heavyLate.Adj v w ↔
    (Digraph.ofArcs [(1, 0), (1, 3), (3, 2), (3, 4), (4, 5), (5, 7), (7, 6), (1, 8)] :
      Digraph (Fin 9)).Adj v w := by
  decide +kernel

-- The totals printed under the four figures.
example : lightEarly.totalLength = 6 ∧ lightLate.totalLength = 7 := by decide +kernel
example : heavyEarly.totalLength = 11 ∧ heavyLate.totalLength = 16 := by decide +kernel

/-- (11): placing the particle after the object lengthens the dependencies by one word less than
the object has, by one for *the trash* and by five for *the trash sitting in the kitchen*. -/
theorem particleShift :
    lightLate.totalLength + 1 = lightEarly.totalLength + #(lightEarly.reachSet 4).toFinset ∧
      heavyLate.totalLength + 1 = heavyEarly.totalLength + #(heavyEarly.reachSet 4).toFinset := by
  have hl := Digraph.totalLength_reorderDependents_swap_add (G := lightEarly) (v := 1)
    (c := ⟨2, by decide⟩) (d := ⟨4, by decide⟩) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide +kernel)
  have hh := Digraph.totalLength_reorderDependents_swap_add (G := heavyEarly) (v := 1)
    (c := ⟨2, by decide⟩) (d := ⟨4, by decide⟩) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide +kernel)
  rw [show #(lightEarly.reachSet (2 : Fin 5)).toFinset = 1 by decide +kernel] at hl
  rw [show #(heavyEarly.reachSet (2 : Fin 9)).toFinset = 1 by decide +kernel] at hh
  exact ⟨hl, hh⟩

/-! ### Baselines: random trees, random orders and grammatical orders -/

/-- (12a) A random tree on five words. -/
abbrev randomTreeA : Digraph (Fin 5) := .ofArcs [(0, 2), (2, 3), (2, 4), (4, 1)]

/-- (12b) A random tree on five words. -/
abbrev randomTreeB : Digraph (Fin 5) := .ofArcs [(3, 0), (3, 1), (0, 2), (0, 4)]

/-- (12c) A random tree on five words. -/
abbrev randomTreeC : Digraph (Fin 5) := .ofArcs [(1, 0), (4, 1), (4, 2), (4, 3)]

example : randomTreeA.totalLength = 8 ∧ randomTreeB.totalLength = 11 ∧
    randomTreeC.totalLength = 7 := by decide

/-- (13a) "this story comes from the AP". -/
abbrev attested : Digraph (Fin 6) :=
  .ofArcs [(1, 0), (2, 1), (2, 3), (3, 5), (5, 4)]

/-- (13b) "from AP the this story comes", a random order of (13a). -/
abbrev randomOrderB : Digraph (Fin 6) := attested.linearize [3, 5, 4, 0, 1, 2] (by decide)

/-- (13c) "comes AP the from story this", a random order of (13a). -/
abbrev randomOrderC : Digraph (Fin 6) := attested.linearize [2, 5, 4, 3, 1, 0] (by decide)

/-- (15b) "from the AP comes this story", a grammatical order of (13a). -/
abbrev grammaticalOrder : Digraph (Fin 6) := attested.linearize [3, 4, 5, 2, 0, 1] (by decide)

-- The totals printed under the figures of (13) and (15).
example : attested.totalLength = 6 ∧ randomOrderB.totalLength = 9 ∧
    randomOrderC.totalLength = 11 ∧ grammaticalOrder.totalLength = 9 := by decide

/-! ### The figures are trees -/

example : extraposition.IsArborescence 1 ∧ whMovement.IsArborescence 1 ∧
    ovid.IsArborescence 2 := by decide
example : shortBeforeLong.IsArborescence 0 ∧ chain.IsArborescence 0 ∧
    sameSide.IsArborescence 0 := by decide
example : lightEarly.IsArborescence 1 ∧ heavyEarly.IsArborescence 1 ∧
    attested.IsArborescence 2 := by decide
example : randomTreeA.IsArborescence 0 ∧ randomTreeB.IsArborescence 3 ∧
    randomTreeC.IsArborescence 4 := by decide

end FutrellEtAl2020
