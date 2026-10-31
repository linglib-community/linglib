module

public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Pi
public import Linglib.Semantics.Modality.Directive
public import Linglib.Fragments.Romance.Portuguese.Modals
public import Linglib.Data.Examples.Ferreira2023
public import Linglib.Data.Examples.Readers

/-!
# Ferreira (2023): A square of necessities

This file formalizes Ferreira's square of necessities. Portuguese has a weak necessity
modal *dever* between *poder* and *ter que* ((28)–(29), by the test of Rubinstein (2021) in
(27)), and both necessity modals take past imperfect morphology (*devia*, *tinha que*) without
a change of force. That morphology is von Fintel and Iatridou's X-marking, read after
Stalnaker (1975) as the suspension of a presupposition: the modal base is replaced by its
∗-revision for the prejacent, which adds the prejacent-worlds most similar to the accessible
ones ((79), after Grano and Phillips-Brown 2022). The weak/strong contrast is X-marking of the
other parameter: the ∗∗-revision of an ordering source for a proposition makes every best world
satisfying it better than every best world failing it (131), and strong necessity under the
revised ordering is von Fintel and Iatridou's weak necessity, the best of the best worlds
under Kratzer's ordering ((129), (133)). The two shifters generate the square (134),
which Portuguese fills with *tem que*, *tinha que*, *deve*, *devia* (135).

## Main definitions

* `revise`, `starstar`: the ∗-revision of a modal base and the ∗∗-revision of a betterness
  relation, the two X-marking shifters.
* `Vertex`, `Vertex.necessity`: the square (134), a vertex recording which parameters are
  X-marked, and the necessity operator at a vertex.
* `interpret`: a modal force read as a Kratzer operator, weak necessity through the
  ∗∗-revision.
* `Pattern.Contradictory`, `Pattern.Consistent`, `Profile`: the conjunctions of §2 and the four
  bits of a model that decide them.

## Implementation notes

* The similarity ordering of (41) is a totally realistic ordering source, and (41b)(i) is read
  with the best worlds drawn from the domain. The ∗-revision is the modal base whose single
  premise is the widened domain of (79).
* (131) presupposes that a best world stays best when the domain widens, which fails
  (`domainIndependent_starstar_iff`), so `starstar` takes the domain as an argument and a
  vertex quantifies over the minimal elements of the revised relation (`bestOf`).
* The ordering revision's target is a contextual parameter different from the prejacent, the
  asymmetry §4 leaves open, and one target is shared by both conjuncts of a pattern, which is
  what makes (24) contradictory. Contradictoriness quantifies over models with nonempty best
  worlds, the deliberative reading of (27ii).
* The dialogues' modal bases are what A says; *devia* is weak necessity with the workday as
  the revision's target over a normality ordering.

## TODO

* (82b) claims that *tem que p* does not entail *tinha que p*. Under (79) and (132a) it does
  (`Vertex.entails_iff`): a best world of the widened domain is best in the original domain or
  an added prejacent-world. The paper's argument, that the best worlds of the two domains need
  not overlap, does not bear on this. (82a) and the second half of (82b) hold as stated.

## References

* [ferreira-2023]
* [von-fintel-iatridou-2008]
* [von-fintel-iatridou-2023]
* [rubinstein-2021]
* [stalnaker-1975]
* [grano-phillips-brown-2022]
* [kratzer-2012]
-/

@[expose] public section

namespace Ferreira2023

open Modality Modality.Directive

variable {W : Type*}

/-! ### ∗-revision of a modal base (79) -/

/-- The ∗-revision (79) of `f` for `p` under the similarity ordering `sim`, the modal base
whose domain at `w` is the domain of `f` together with the `p`-worlds most similar to some world
of it. -/
def revise (sim f : Background W) (p : W → Prop) : Background W :=
  fun w ↦ {fun w' ↦ w' ∈ f.accessibleWorlds w ∨
    ∃ w'' ∈ f.accessibleWorlds w, w' ∈ (premisePreorder (sim w'')).minimals {v | p v}}

section

variable {sim f g : Background W} {p q : W → Prop}
  {w : W}

theorem accessibleWorlds_revise (sim f : Background W) (p : W → Prop)
    (w : W) :
    (revise sim f p).accessibleWorlds w =
      f.accessibleWorlds w ∪
        {w' | ∃ w'' ∈ f.accessibleWorlds w,
          w' ∈ (premisePreorder (sim w'')).minimals {v | p v}} := by
  ext w'
  simp [Background.mem_accessibleWorlds, revise]

theorem subset_accessibleWorlds_revise (sim f : Background W)
    (p : W → Prop) (w : W) : f.accessibleWorlds w ⊆ (revise sim f p).accessibleWorlds w := by
  rw [accessibleWorlds_revise]; exact Set.subset_union_left

theorem prop_of_mem_accessibleWorlds_revise {w' : W}
    (h : w' ∈ (revise sim f p).accessibleWorlds w) (hn : w' ∉ f.accessibleWorlds w) : p w' := by
  rw [accessibleWorlds_revise] at h
  rcases h with h | ⟨_, _, h⟩
  · exact absurd h hn
  · exact Preorder.minimals_subset _ _ h

theorem strongNecessity_revise (sim : Background W) (h : strongNecessity f g q w) :
    strongNecessity (revise sim f q) g q w := by
  intro w' hw'
  by_cases hmem : w' ∈ f.accessibleWorlds w
  · exact h w' (Preorder.mem_minimals_of_subset (subset_accessibleWorlds_revise sim f q w) hw' hmem)
  · exact prop_of_mem_accessibleWorlds_revise hw'.1 hmem

/-! ### ∗∗-revision of an ordering source (130)–(131) -/

/-- The members of `D` no member betters under a relation, (41b)(i) for an arbitrary
betterness. -/
def bestOf (R : W → W → Prop) (D : Set W) : Set W := {u | u ∈ D ∧ ∀ v ∈ D, ¬ R v u}

-- (130)
theorem bestOf_strictlyBetter (A : Set (W → Prop)) (D : Set W) :
    bestOf (fun u v ↦ u <[A] v) D = (premisePreorder A).minimals D :=
  Set.ext fun _ ↦ and_congr_right fun _ ↦ forall₂_congr fun _ _ ↦ not_and_not_right

/-- The ∗∗-revision (131) of the betterness of `g w` on `D` for `p`, under which in addition every
best `p`-world betters every best non-`p`-world. -/
def starstar (g : Background W) (p : W → Prop) (w : W) (D : Set W) (u v : W) : Prop :=
  (u <[g w] v) ∨ (p u ∧ ¬ p v ∧
    u ∈ (premisePreorder (g w)).minimals D ∧ v ∈ (premisePreorder (g w)).minimals D)

-- (129b)
theorem bestOf_starstar (g : Background W) (p : W → Prop) (w : W) (D : Set W) :
    bestOf (starstar g p w D) D =
      (premisePreorder {p}).minimals ((premisePreorder (g w)).minimals D) := by
  ext u
  simp only [bestOf, starstar, Preorder.ofCriteria_lt_iff, Preorder.mem_minimals_iff,
    Preorder.ofCriteria_le_iff, Set.mem_singleton_iff, forall_eq,
    Set.mem_ofPred_eq]
  grind

/-- (131) asks for one betterness relation whose restriction to every domain is the ∗∗-revision
on that domain. -/
def DomainIndependent (F : Set W → W → W → Prop) : Prop :=
  ∃ R : W → W → Prop, ∀ D u v, u ∈ D → v ∈ D → (R u v ↔ F D u v)

/-- The ∗∗-revision is domain-independent iff a `p`-world and a non-`p`-world both best in a domain
stay best in every larger domain (131). -/
theorem domainIndependent_starstar_iff (g : Background W) (p : W → Prop) (w : W) :
    DomainIndependent (starstar g p w) ↔
      ∀ ⦃D D' : Set W⦄, D ⊆ D' → ∀ ⦃u v⦄, p u → ¬ p v →
        u ∈ (premisePreorder (g w)).minimals D → v ∈ (premisePreorder (g w)).minimals D →
          u ∈ (premisePreorder (g w)).minimals D' ∧ v ∈ (premisePreorder (g w)).minimals D' := by
  constructor
  · rintro ⟨R, hR⟩ D D' hD u v hu hv hbu hbv
    rcases (hR D' u v (hD hbu.1) (hD hbv.1)).1
      ((hR D u v hbu.1 hbv.1).2 (Or.inr ⟨hu, hv, hbu, hbv⟩)) with h | ⟨-, -, h⟩
    · exact absurd (hbv.2 hbu.1 (((premisePreorder _).lt_iff_le_not_ge _ _).1 h).1)
        (((premisePreorder _).lt_iff_le_not_ge _ _).1 h).2
    · exact h
  · intro h
    refine ⟨fun u v ↦ starstar g p w {u, v} u v, fun D u v hu hv ↦ ?_⟩
    have hp : ({u, v} : Set W) ⊆ D := Set.insert_subset hu (Set.singleton_subset_iff.2 hv)
    constructor
    · rintro (hlt | ⟨hpu, hpv, hbu, hbv⟩)
      · exact Or.inl hlt
      · exact Or.inr ⟨hpu, hpv, (h hp hpu hpv hbu hbv).1, (h hp hpu hpv hbu hbv).2⟩
    · rintro (hlt | ⟨hpu, hpv, hbu, hbv⟩)
      · exact Or.inl hlt
      · exact Or.inr ⟨hpu, hpv, Preorder.mem_minimals_of_subset hp hbu (by simp),
          Preorder.mem_minimals_of_subset hp hbv (by simp)⟩

/-! ### A three-world frame

Worlds `0` and `1` are incomparable, so both are best among `{0, 1}`, and `2` betters `1`.
Widening the domain to the whole frame unseats `1`, which is what defeats (131) and, in the
countermodels below, the entailment from *deve* to *devia*. Three worlds and all three criteria
are needed: a `p`-world and a non-`p`-world must both be best somewhere, and a third world must
better one of them. -/

/-- The ordering source of the three-world frame. -/
abbrev g₃ : Background (Fin 3) := fun _ ↦ {(· = 0), fun x ↦ x = 1 ∨ x = 2, (· = 2)}

theorem minimals_pair_g₃ : (premisePreorder (g₃ 0)).minimals ({0, 1} : Set (Fin 3)) = {0, 1} := by
  ext u
  simp only [Preorder.mem_minimals_iff, Preorder.ofCriteria_le_iff,
    Set.mem_insert_iff, Set.mem_singleton_iff,
      forall_eq_or_imp, forall_eq,
    implies_true]
  revert u
  decide

theorem minimals_univ_g₃ : (premisePreorder (g₃ 0)).minimals Set.univ = {0, 2} := by
  ext u
  simp only [Preorder.mem_minimals_iff, Preorder.ofCriteria_le_iff,
    Set.mem_univ, true_and, Set.mem_insert_iff,
    Set.mem_singleton_iff, forall_eq_or_imp, forall_eq,
    ]
  revert u
  decide

-- (131)
theorem not_domainIndependent_starstar : ¬ DomainIndependent (starstar g₃ (· = 1) 0) := by
  intro h
  have h₁ := (domainIndependent_starstar_iff g₃ (· = 1) 0).1 h (D := {0, 1}) (D' := Set.univ)
    (Set.subset_univ _) (u := 1) (v := 0) rfl (by decide) (by rw [minimals_pair_g₃]; simp)
    (by rw [minimals_pair_g₃]; simp)
  rw [minimals_univ_g₃] at h₁
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h₁
  exact absurd h₁.1 (by decide)

/-- In the paper's terms, no ordering source is a ∗∗-revision of `g₃` for `(· = 1)`. -/
theorem not_exists_starstar_orderingSource :
    ¬ ∃ g' : Background (Fin 3), ∀ (D : Set (Fin 3)) (u v : Fin 3), u ∈ D → v ∈ D →
      ((u <[g' 0] v) ↔ starstar g₃ (· = 1) 0 D u v) :=
  fun ⟨g', h⟩ ↦ not_domainIndependent_starstar ⟨fun u v ↦ u <[g' 0] v, h⟩

/-! ### The square of necessities (132)–(134) -/

/-- Strong necessity with the ordering source ∗∗-revised for `p` (132b). -/
def snXg (f g : Background W) (p q : W → Prop) (w : W) : Prop :=
  ∀ w' ∈ bestOf (starstar g p w (f.accessibleWorlds w)) (f.accessibleWorlds w), q w'

/-- Weak necessity (133) is strong necessity with an X-marked ordering source, the secondary
ordering source of [von-fintel-iatridou-2008] being the revision's target. -/
theorem snXg_iff_weakNecessity (f g : Background W) (p q : W → Prop)
    (w : W) : snXg f g p q w ↔ weakNecessity f g (fun _ ↦ {p}) q w := by
  rw [snXg, bestOf_starstar, weakNecessity, bestWorlds]

/-- A vertex of the square (134) records whether the modal base and the ordering source are
X-marked. -/
structure Vertex where
  /-- The modal base is ∗-revised for the prejacent. -/
  xf : Bool
  /-- The ordering source is ∗∗-revised. -/
  xg : Bool
  deriving DecidableEq, Repr

instance : Fintype Vertex :=
  Fintype.ofEquiv (Bool × Bool) ⟨fun x ↦ ⟨x.1, x.2⟩, fun v ↦ (v.xf, v.xg), fun _ ↦ rfl, fun _ ↦ rfl⟩

/-- The modal base at a vertex is `f` or its ∗-revision for the prejacent `q` (78), (84). -/
def Vertex.base (v : Vertex) (sim f : Background W) (q : W → Prop) :
    Background W :=
  if v.xf then revise sim f q else f

/-- The necessity at a vertex (134), over the vertex's base and the betterness of `g`,
∗∗-revised for `p` when the ordering source is X-marked. -/
def Vertex.necessity (v : Vertex) (sim f : Background W)
    (g : Background W) (p q : W → Prop) (w : W) : Prop :=
  let D := (v.base sim f q).accessibleWorlds w
  ∀ w' ∈ bestOf (if v.xg then starstar g p w D else fun u v ↦ u <[g w] v) D, q w'

theorem Vertex.necessity_xg_false (xf : Bool) :
    Vertex.necessity ⟨xf, false⟩ sim f g p q w ↔
      strongNecessity (Vertex.base ⟨xf, false⟩ sim f q) g q w := by
  simp only [Vertex.necessity, Bool.false_eq_true, ite_false, bestOf_strictlyBetter,
    strongNecessity, necessity_iff, bestWorlds]

theorem Vertex.necessity_xg_true (xf : Bool) :
    Vertex.necessity ⟨xf, true⟩ sim f g p q w ↔
      weakNecessity (Vertex.base ⟨xf, true⟩ sim f q) g (fun _ ↦ {p}) q w := by
  simp only [Vertex.necessity, ite_true, bestOf_starstar, weakNecessity, bestWorlds]

/-! ### The entailment order of the square ((29), (82)) -/

/-- Entailment between vertices, over every model whose similarity ordering is totally
realistic (41a). -/
def Vertex.Entails (v v' : Vertex) : Prop :=
  ∀ (W : Type) (sim : Background W), sim.IsTotallyRealistic →
    ∀ (f g : Background W) (p q : W → Prop) (w : W),
      v.necessity sim f g p q w → v'.necessity sim f g p q w

theorem Vertex.Entails.refl (v : Vertex) : v.Entails v := fun _ _ _ _ _ _ _ _ ↦ id

theorem Vertex.Entails.trans {u v x : Vertex} (h₁ : u.Entails v) (h₂ : v.Entails x) :
    u.Entails x :=
  fun _ sim hc f g p q w h ↦ h₂ _ sim hc f g p q w (h₁ _ sim hc f g p q w h)

-- (29)
theorem Vertex.entails_xg (xf : Bool) : Vertex.Entails ⟨xf, false⟩ ⟨xf, true⟩ :=
  fun _ _ _ _ _ _ _ _ h ↦ (Vertex.necessity_xg_true xf).2
    (strong_entails_weak _ _ _ _ _ ((Vertex.necessity_xg_false xf).1 h))

theorem Vertex.entails_xf : Vertex.Entails ⟨false, false⟩ ⟨true, false⟩ :=
  fun _ sim _ _ _ _ _ _ h ↦ (Vertex.necessity_xg_false true).2
    (strongNecessity_revise sim ((Vertex.necessity_xg_false false).1 h))

theorem Vertex.entails_of_sn : ∀ v, Vertex.Entails ⟨false, false⟩ v
  | ⟨false, false⟩ => .refl _
  | ⟨false, true⟩ => entails_xg false
  | ⟨true, false⟩ => entails_xf
  | ⟨true, true⟩ => entails_xf.trans (entails_xg true)

section countermodels

private theorem minimals_singleton (a : W) (A : Set (W → Prop)) :
    (premisePreorder A).minimals {a} = {a} :=
  Set.ext fun _ ↦ ⟨fun h ↦ h.1, fun h ↦ ⟨h, fun _ hv _ ↦ by
    rw [Set.mem_singleton_iff.mp hv, Set.mem_singleton_iff.mp h]
    exact (premisePreorder _).le_refl _⟩⟩

private theorem minimals_eq_singleton {S : Set W} {b : W} (hb : b ∈ S) :
    (premisePreorder {(· = b)}).minimals S = {b} := by
  rw [Preorder.minimals_ofCriteria_eq ⟨b, hb, by simp⟩]
  ext v
  simp only [Set.mem_singleton_iff, forall_eq, Set.mem_sep_iff,
    and_iff_right_iff_imp]
  rintro rfl
  exact hb

private theorem isTotallyRealistic_eq :
    Background.IsTotallyRealistic (fun w ↦ {(· = w)} : Background W) := by
  intro w; ext v; simp

/-! The first countermodel: nothing excluded, nothing ordered. The Xg vertices hold, since the
`p`-best world is the prejacent-world, and the others fail. -/

private theorem M1_acc (sim : Background Bool) (v : Vertex) :
    (v.base sim ⊥ (· = true)).accessibleWorlds true = Set.univ := by
  unfold Vertex.base
  split
  · exact Set.eq_univ_of_univ_subset
      (Background.accessibleWorlds_bot (W := Bool) true ▸
        subset_accessibleWorlds_revise _ _ _ _)
  · exact Background.accessibleWorlds_bot _

private theorem M1_iff (sim : Background Bool) (v : Vertex) :
    v.necessity sim ⊥ ⊥ (· = true) (· = true) true ↔ v.xg = true := by
  obtain ⟨xf, _ | _⟩ := v
  · rw [Vertex.necessity_xg_false, strongNecessity, necessity_iff, bestWorlds_bot,
      M1_acc]
    simp only [Bool.false_eq_true, iff_false, not_forall]
    exact ⟨false, Set.mem_univ _, Bool.false_ne_true⟩
  · rw [Vertex.necessity_xg_true, weakNecessity, bestWorlds_bot, M1_acc,
      minimals_eq_singleton (Set.mem_univ _)]
    simp

/-! The second countermodel: only the non-prejacent world is accessible, and the ordering
prefers the prejacent-world. The revision adds the prejacent-world, which is then best, so the
Xf vertices hold and the others fail. -/

private abbrev simB : Background Bool := fun w ↦ {(· = w)}

private theorem M2_acc :
    Background.accessibleWorlds (fun _ ↦ {(· = false)} : Background Bool) true =
      {false} := by
  ext v; simp

private theorem M2_mem :
    true ∈ Background.accessibleWorlds (revise simB (fun _ ↦ {(· = false)}) (· = true))
      true := by
  rw [accessibleWorlds_revise, M2_acc]
  exact Or.inr ⟨false, rfl, rfl, fun v hv _ ↦ by
    rw [show v = true from hv]; exact (premisePreorder _).le_refl _⟩

private theorem M2_iff (v : Vertex) :
    v.necessity simB (fun _ ↦ {(· = false)}) (fun _ ↦ {(· = true)}) (· = true) (· = true) true ↔
      v.xf = true := by
  have hft : ¬ Vertex.necessity ⟨false, true⟩ simB (fun _ ↦ {(· = false)})
      (fun _ ↦ {(· = true)}) (· = true) (· = true) true := by
    rw [Vertex.necessity_xg_true, weakNecessity, bestWorlds]
    simp only [Vertex.base, Bool.false_eq_true, ↓reduceIte]
    rw [M2_acc, minimals_singleton, minimals_singleton]
    simp
  have htf : Vertex.necessity ⟨true, false⟩ simB (fun _ ↦ {(· = false)})
      (fun _ ↦ {(· = true)}) (· = true) (· = true) true := by
    rw [Vertex.necessity_xg_false, strongNecessity, necessity_iff, bestWorlds]
    simp only [Vertex.base, ↓reduceIte]
    rw [Preorder.minimals_ofCriteria_eq ⟨true, M2_mem, by simp⟩]
    exact fun w' hw' ↦ hw'.2 _ (Set.mem_singleton _)
  obtain ⟨_ | _, _ | _⟩ := v
  · exact iff_of_false
      (fun h ↦ hft (Vertex.entails_xg false _ _ isTotallyRealistic_eq _ _ _ _ _ h))
      Bool.false_ne_true
  · exact iff_of_false hft Bool.false_ne_true
  · exact iff_of_true htf rfl
  · exact iff_of_true (Vertex.entails_xg true _ _ isTotallyRealistic_eq _ _ _ _ _ htf) rfl

/-! The third countermodel refutes *deve q ⊨ devia q* on the three-world frame: the base
excludes `2`, the revision for the prejacent puts it back, and `2` unseats `1`, the only
`p`-world. Only *deve* holds. -/

private abbrev f₃ : Background (Fin 3) := fun _ ↦ {fun w ↦ w ≠ 2}
private abbrev q₃ : Fin 3 → Prop := fun w ↦ w = 1 ∨ w = 2
private abbrev sim₃ : Background (Fin 3) := fun w ↦ {(· = w)}

private theorem accessibleWorlds_f₃ : f₃.accessibleWorlds 0 = {0, 1} := by
  ext u
  simp only [Background.mem_accessibleWorlds, Set.mem_insert_iff,
    Set.mem_singleton_iff, forall_eq,
    ]
  revert u
  decide

private theorem accessibleWorlds_revise_f₃ :
    (revise sim₃ f₃ q₃).accessibleWorlds 0 = Set.univ := by
  rw [accessibleWorlds_revise, accessibleWorlds_f₃]
  ext u
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq,
    Preorder.mem_minimals_iff, Preorder.ofCriteria_le_iff, forall_eq, Set.mem_univ, iff_true]
  revert u
  decide

private theorem M3_ft : Vertex.necessity ⟨false, true⟩ sim₃ f₃ g₃ (· = 1) q₃ 0 := by
  rw [Vertex.necessity_xg_true, weakNecessity, bestWorlds]
  simp only [Vertex.base, Bool.false_eq_true, ↓reduceIte]
  rw [accessibleWorlds_f₃, minimals_pair_g₃,
    minimals_eq_singleton (S := {0, 1}) (b := 1) (by simp)]
  rintro _ rfl
  exact Or.inl rfl

private theorem M3_not_tt : ¬ Vertex.necessity ⟨true, true⟩ sim₃ f₃ g₃ (· = 1) q₃ 0 := by
  rw [Vertex.necessity_xg_true, weakNecessity, bestWorlds]
  simp only [Vertex.base, ↓reduceIte]
  rw [accessibleWorlds_revise_f₃, minimals_univ_g₃]
  have h0 : (0 : Fin 3) ∈ (premisePreorder {(· = 1)}).minimals ({0, 2} : Set (Fin 3)) := by
    simp only [Preorder.mem_minimals_iff, Preorder.ofCriteria_le_iff,
      Set.mem_insert_iff, Set.mem_singleton_iff,
        forall_eq]
    decide
  exact fun h ↦ absurd (h 0 h0) (by decide)

private theorem M3_iff (v : Vertex) :
    v.necessity sim₃ f₃ g₃ (· = 1) q₃ 0 ↔ v = ⟨false, true⟩ := by
  obtain ⟨_ | _, _ | _⟩ := v
  · exact iff_of_false
      (fun h ↦ M3_not_tt (Vertex.entails_of_sn _ _ _ isTotallyRealistic_eq _ _ _ _ _ h)) (by decide)
  · exact iff_of_true M3_ft rfl
  · exact iff_of_false
      (fun h ↦ M3_not_tt (Vertex.entails_xg true _ _ isTotallyRealistic_eq _ _ _ _ _ h)) (by decide)
  · exact iff_of_false M3_not_tt (by decide)

end countermodels

/-- In the entailment order of the square (134), strong necessity entails every vertex, *tinha
que* entails *devia*, and nothing else entails anything ((29), (82a), (82b)). -/
theorem Vertex.entails_iff (v v' : Vertex) :
    v.Entails v' ↔ v = v' ∨ v = ⟨false, false⟩ ∨ (v = ⟨true, false⟩ ∧ v' = ⟨true, true⟩) := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · have h1 : v.xg = true → v'.xg = true := fun hv ↦
      (M1_iff _ v').1 (h _ _ isTotallyRealistic_eq _ _ _ _ _ ((M1_iff _ v).2 hv))
    have h2 : v.xf = true → v'.xf = true := fun hv ↦
      (M2_iff v').1 (h _ _ isTotallyRealistic_eq _ _ _ _ _ ((M2_iff v).2 hv))
    have h3 : v = ⟨false, true⟩ → v' = ⟨false, true⟩ := fun hv ↦
      (M3_iff v').1 (h _ _ isTotallyRealistic_eq _ _ _ _ _ ((M3_iff v).2 hv))
    clear h
    revert v v'
    decide
  · rintro (rfl | rfl | ⟨rfl, rfl⟩)
    exacts [.refl _, entails_of_sn _, entails_xg true]

-- (82), (82b)
theorem entails_82 :
    (¬ Vertex.Entails ⟨false, true⟩ ⟨true, true⟩ ∧ ¬ Vertex.Entails ⟨true, true⟩ ⟨false, true⟩) ∧
      (Vertex.Entails ⟨false, false⟩ ⟨true, false⟩ ∧
        ¬ Vertex.Entails ⟨true, false⟩ ⟨false, false⟩) := by
  simp only [Vertex.entails_iff]
  decide

/-! ### Forces as operators -/

/-- A force as a Kratzer operator over a modal base and an ordering source, possibility and
necessity over the best worlds and weak necessity through the ∗∗-revision for `p` (132b). -/
def interpret (φ : ModalForce) (f g : Background W) (p q : W → Prop)
    (w : W) : Prop :=
  match φ with
  | .possibility => possibility f g q w
  | .weakNecessity => snXg f g p q w
  | .necessity => strongNecessity f g q w

/-- The Portuguese necessity modal at each vertex (135). X-marking the ordering source is
lexical, from *ter que* to *dever*, and X-marking the modal base is the past imperfect. -/
def modalAt : Vertex → ModalAuxiliary
  | ⟨false, false⟩ => Portuguese.Modals.temQue
  | ⟨false, true⟩ => Portuguese.Modals.deve
  | ⟨true, false⟩ => Portuguese.Modals.tinhaQue
  | ⟨true, true⟩ => Portuguese.Modals.devia

/-- The modal item at a vertex. -/
def square (v : Vertex) : ModalItem := (modalAt v).toModalItem

-- (135)
theorem tense_square : ∀ v : Vertex, (modalAt v).features .tense = some .Imp ↔ v.xf = true := by
  decide

-- (83), (135)
theorem forces_square :
    ∀ v : Vertex, (square v).forces = {if v.xg then .weakNecessity else .necessity} := by
  decide

/-- Semantically (135), the necessity at a vertex is the operator of the force the fragment
gives the vertex's modal, over the vertex's base. -/
theorem necessity_iff_interpret {φ : ModalForce} (v : Vertex) (hφ : φ ∈ (square v).forces) :
    v.necessity sim f g p q w ↔ interpret φ (v.base sim f q) g p q w := by
  rw [forces_square, Finset.mem_singleton] at hφ
  subst hφ
  obtain ⟨xf, _ | _⟩ := v
  · simpa [interpret] using Vertex.necessity_xg_false (sim := sim) (f := f) (g := g) (p := p)
      (q := q) (w := w) xf
  · simpa [interpret, snXg_iff_weakNecessity] using
      Vertex.necessity_xg_true (sim := sim) (f := f) (g := g) (p := p) (q := q) (w := w) xf

/-! ### The conjunctions of §2 -/

/-- A conjunct is a modal of some force over the prejacent or its negation, possibly negated. -/
structure Conjunct where
  /-- The force of the modal. -/
  force : ModalForce
  /-- The modal is negated. -/
  negModal : Bool
  /-- The prejacent is negated. -/
  negPrejacent : Bool
  deriving DecidableEq, Repr

/-- The conjunct's truth at `w`, `p` the target of weak necessity's ordering revision and `q`
the prejacent. -/
def Conjunct.holds (c : Conjunct) (f g : Background W) (p q : W → Prop)
    (w : W) : Prop :=
  let m := interpret c.force f g p (if c.negPrejacent then fun v ↦ ¬ q v else q) w
  if c.negModal then ¬ m else m

/-- Entailment between conjuncts over every model with nonempty best worlds, the conclusion of
a deliberation (27ii). -/
def Conjunct.Entails (c₁ c₂ : Conjunct) : Prop :=
  ∀ (W : Type) (f g : Background W) (p q : W → Prop) (w : W),
    (bestWorlds f g w).Nonempty → c₁.holds f g p q w → c₂.holds f g p q w

/-- A conjunction of two modal claims about one prejacent, with one target for the ordering
revision. -/
structure Pattern where
  /-- The first conjunct. -/
  first : Conjunct
  /-- The second conjunct. -/
  second : Conjunct
  deriving DecidableEq, Repr

/-- The conjunction is contradictory as the conclusion of a deliberation: false in every model
with nonempty best worlds. -/
def Pattern.Contradictory (pat : Pattern) : Prop :=
  ∀ (W : Type) (f g : Background W) (p q : W → Prop) (w : W),
    (bestWorlds f g w).Nonempty → ¬ (pat.first.holds f g p q w ∧ pat.second.holds f g p q w)

/-- The conjunction has a model with nonempty best worlds. -/
def Pattern.Consistent (pat : Pattern) : Prop :=
  ∃ (W : Type) (f g : Background W) (p q : W → Prop) (w : W),
    (bestWorlds f g w).Nonempty ∧ pat.first.holds f g p q w ∧ pat.second.holds f g p q w

/-! ### Profiles: the four bits of a model that decide the conjunctions -/

/-- Which of the prejacent and its negation hold at some best world, and at some `p`-best of
the best worlds. -/
structure Profile where
  /-- Some best world is a prejacent-world. -/
  bestQ : Bool
  /-- Some best world is not a prejacent-world. -/
  bestNotQ : Bool
  /-- Some `p`-best of the best worlds is a prejacent-world. -/
  topQ : Bool
  /-- Some `p`-best of the best worlds is not a prejacent-world. -/
  topNotQ : Bool
  deriving DecidableEq, Repr

instance : Fintype Profile :=
  Fintype.ofEquiv (Bool × Bool × Bool × Bool)
    ⟨fun x ↦ ⟨x.1, x.2.1, x.2.2.1, x.2.2.2⟩, fun π ↦ (π.bestQ, π.bestNotQ, π.topQ, π.topNotQ),
      fun _ ↦ rfl, fun _ ↦ rfl⟩

/-- The profile of a model at `w`. -/
noncomputable def profile (f g : Background W) (p q : W → Prop) (w : W) :
    Profile :=
  open Classical in
  ⟨decide (∃ u ∈ bestWorlds f g w, q u), decide (∃ u ∈ bestWorlds f g w, ¬ q u),
    decide (∃ u ∈ (premisePreorder {p}).minimals (bestWorlds f g w), q u),
    decide (∃ u ∈ (premisePreorder {p}).minimals (bestWorlds f g w), ¬ q u)⟩

/-- A profile is valid when it is the profile of a model with nonempty best worlds, whose
`p`-best best worlds are nonempty and best. -/
def Profile.Valid (π : Profile) : Prop :=
  (π.topQ = true ∨ π.topNotQ = true) ∧ (π.topQ = true → π.bestQ = true) ∧
    (π.topNotQ = true → π.bestNotQ = true)

instance : DecidablePred Profile.Valid := fun π ↦
  inferInstanceAs (Decidable ((π.topQ = true ∨ π.topNotQ = true) ∧
    (π.topQ = true → π.bestQ = true) ∧ (π.topNotQ = true → π.bestNotQ = true)))

theorem minimals_singleton_nonempty {S : Set W} (hS : S.Nonempty) (p : W → Prop) :
    ((premisePreorder {p}).minimals S).Nonempty := by
  by_cases hp : ∃ v ∈ S, p v
  · obtain ⟨v, hv, hpv⟩ := hp
    exact ⟨v, hv, fun ⦃_⦄ _ _ _ hq _ ↦ Set.mem_singleton_iff.mp hq ▸ hpv⟩
  · push Not at hp
    obtain ⟨u, hu⟩ := hS
    exact ⟨u, hu, fun ⦃u'⦄ hu' _ _ hq hqu' ↦
      absurd (Set.mem_singleton_iff.mp hq ▸ hqu') (hp u' hu')⟩

theorem profile_valid (hne : (bestWorlds f g w).Nonempty) : (profile f g p q w).Valid := by
  obtain ⟨u, hu⟩ := minimals_singleton_nonempty hne p
  have hsub := Preorder.minimals_subset (premisePreorder {p}) (bestWorlds f g w)
  simp only [Profile.Valid, profile, decide_eq_true_eq]
  refine ⟨?_, fun ⟨v, hv, hq⟩ ↦ ⟨v, hsub hv, hq⟩, fun ⟨v, hv, hq⟩ ↦ ⟨v, hsub hv, hq⟩⟩
  by_cases hq : q u
  · exact Or.inl ⟨u, hu, hq⟩
  · exact Or.inr ⟨u, hu, hq⟩

/-- A conjunct's truth value on a profile. -/
def Conjunct.evalP (π : Profile) (c : Conjunct) : Bool :=
  let someQ := if c.negPrejacent then π.bestNotQ else π.bestQ
  let someNotQ := if c.negPrejacent then π.bestQ else π.bestNotQ
  let someTopNotQ := if c.negPrejacent then π.topQ else π.topNotQ
  let m : Bool := match c.force with
    | .possibility => someQ
    | .weakNecessity => !someTopNotQ
    | .necessity => !someNotQ
  if c.negModal then !m else m

theorem Conjunct.holds_iff_evalP (c : Conjunct) (f g : Background W)
    (p q : W → Prop) (w : W) : c.holds f g p q w ↔ c.evalP (profile f g p q w) = true := by
  obtain ⟨φ, m, n⟩ := c
  cases φ <;> cases m <;> cases n <;>
    simp [Conjunct.holds, Conjunct.evalP, interpret, profile, snXg_iff_weakNecessity,
      weakNecessity, strongNecessity]

section twoWorlds

/-- The modal base of the two-world family: nothing excluded, or one world accessible. -/
private def ofAcc : Option Bool → Background Bool
  | none => fun _ ↦ ∅
  | some b => fun _ ↦ {(· = b)}

private def accList : Option Bool → List Bool
  | none => [false, true]
  | some b => [b]

/-- The ordering revision's target in the family, a tie or a preference for one world. -/
private def ofRev : Option Bool → Bool → Prop
  | none => fun _ ↦ True
  | some b => (· = b)

private def topList (acc rev : Option Bool) : List Bool :=
  match rev with
  | none => accList acc
  | some b => [acc.getD b]

private theorem bestWorlds_ofAcc (acc : Option Bool) (w : Bool) :
    bestWorlds (ofAcc acc) ⊥ w = {v | v ∈ accList acc} := by
  rw [bestWorlds_bot]
  ext v
  cases acc <;> cases v <;> simp [Background.mem_accessibleWorlds, ofAcc, accList]

private theorem minimals_ofRev (acc rev : Option Bool) :
    (premisePreorder {ofRev rev}).minimals {v | v ∈ accList acc} = {v | v ∈ topList acc rev} := by
  ext u
  rcases acc with _ | _ | _ <;> rcases rev with _ | _ | _ <;> cases u <;>
    simp [Preorder.mem_minimals_iff, Preorder.ofCriteria_le_iff, accList, topList, ofRev]

private def famProfile (acc rev : Option Bool) (q : Bool → Bool) : Profile :=
  ⟨(accList acc).any q, (accList acc).any (!q ·), (topList acc rev).any q,
    (topList acc rev).any (!q ·)⟩

private theorem profile_ofAcc (acc rev : Option Bool) (q : Bool → Bool) :
    profile (ofAcc acc) ⊥ (ofRev rev) (q · = true) true = famProfile acc rev q := by
  simp only [profile, famProfile, bestWorlds_ofAcc, minimals_ofRev]
  rcases acc with _ | _ | _ <;> rcases rev with _ | _ | _ <;> simp [accList, topList]

private theorem exists_famProfile :
    ∀ π : Profile, π.Valid → ∃ acc rev : Option Bool, ∃ q : Bool → Bool,
      famProfile acc rev q = π := by
  decide

private theorem bestWorlds_ofAcc_nonempty (acc : Option Bool) (w : Bool) :
    (bestWorlds (ofAcc acc) ⊥ w).Nonempty := by
  rw [bestWorlds_ofAcc]
  cases acc
  · exact ⟨true, by simp [accList]⟩
  · exact ⟨_, List.mem_singleton_self _⟩

theorem Profile.Valid.exists_model {π : Profile} (hπ : π.Valid) :
    ∃ (f g : Background Bool) (p q : Bool → Prop),
      (bestWorlds f g true).Nonempty ∧ profile f g p q true = π :=
  let ⟨acc, rev, q, h⟩ := exists_famProfile π hπ
  ⟨ofAcc acc, ⊥, ofRev rev, (q · = true), bestWorlds_ofAcc_nonempty acc true,
    (profile_ofAcc acc rev q).trans h⟩

end twoWorlds

/-- A conjunction is contradictory exactly when no valid profile satisfies both conjuncts. -/
theorem Pattern.contradictory_iff (pat : Pattern) :
    pat.Contradictory ↔ ∀ π : Profile, π.Valid →
      ¬ (pat.first.evalP π = true ∧ pat.second.evalP π = true) := by
  constructor
  · intro h π hπ ⟨h₁, h₂⟩
    obtain ⟨f, g, p, q, hne, rfl⟩ := hπ.exists_model
    exact h Bool f g p q true hne
      ⟨(Conjunct.holds_iff_evalP _ _ _ _ _ _).2 h₁, (Conjunct.holds_iff_evalP _ _ _ _ _ _).2 h₂⟩
  · intro h W f g p q w hne ⟨h₁, h₂⟩
    rw [Conjunct.holds_iff_evalP] at h₁ h₂
    exact h _ (profile_valid hne) ⟨h₁, h₂⟩

theorem Pattern.consistent_iff (pat : Pattern) :
    pat.Consistent ↔ ∃ π : Profile, π.Valid ∧
      pat.first.evalP π = true ∧ pat.second.evalP π = true := by
  constructor
  · rintro ⟨W, f, g, p, q, w, hne, h₁, h₂⟩
    rw [Conjunct.holds_iff_evalP] at h₁ h₂
    exact ⟨_, profile_valid hne, h₁, h₂⟩
  · rintro ⟨π, hπ, h₁, h₂⟩
    obtain ⟨f, g, p, q, hne, rfl⟩ := hπ.exists_model
    exact ⟨Bool, f, g, p, q, true, hne, (Conjunct.holds_iff_evalP _ _ _ _ _ _).2 h₁,
      (Conjunct.holds_iff_evalP _ _ _ _ _ _).2 h₂⟩

theorem Conjunct.entails_iff (c₁ c₂ : Conjunct) :
    c₁.Entails c₂ ↔ ∀ π : Profile, π.Valid → c₁.evalP π = true → c₂.evalP π = true := by
  constructor
  · intro h π hπ h₁
    obtain ⟨f, g, p, q, hne, rfl⟩ := hπ.exists_model
    exact (Conjunct.holds_iff_evalP _ _ _ _ _ _).1
      (h Bool f g p q true hne ((Conjunct.holds_iff_evalP _ _ _ _ _ _).2 h₁))
  · intro h W f g p q w hne h₁
    rw [Conjunct.holds_iff_evalP] at h₁ ⊢
    exact h _ (profile_valid hne) h₁

instance : DecidablePred Pattern.Contradictory :=
  fun pat ↦ decidable_of_iff _ pat.contradictory_iff.symm

instance : DecidablePred Pattern.Consistent :=
  fun pat ↦ decidable_of_iff _ pat.consistent_iff.symm

instance : DecidableRel Conjunct.Entails :=
  fun c₁ c₂ ↦ decidable_of_iff _ (c₁.entails_iff c₂).symm

theorem Pattern.consistent_iff_not_contradictory (pat : Pattern) :
    pat.Consistent ↔ ¬ pat.Contradictory := by
  rw [pat.consistent_iff, pat.contradictory_iff]
  push Not
  rfl

/-- The scale of forces (28)–(29) is the entailment order, the prejacent held fixed, and no
entailment runs up the scale. -/
theorem scale : ∀ (φ ψ : ModalForce) (n : Bool),
    (φ ≤ ψ ↔ Conjunct.Entails ⟨ψ, false, n⟩ ⟨φ, false, n⟩) := by
  decide

/-- *Dever* passes Rubinstein's test for weak necessity (27). It is entailed by *ter que* and
not conversely, and *dever p* and *dever ¬p* are contradictory. -/
theorem rubinstein :
    (Conjunct.Entails ⟨.necessity, false, false⟩ ⟨.weakNecessity, false, false⟩ ∧
      ¬ Conjunct.Entails ⟨.weakNecessity, false, false⟩ ⟨.necessity, false, false⟩) ∧
      Pattern.Contradictory ⟨⟨.weakNecessity, false, false⟩, ⟨.weakNecessity, false, true⟩⟩ := by
  decide

/-! ### The paradigm ((16)–(25), (30), (32)) -/

/-- The conjuncts of the paper's examples, keyed as in `Data/Examples/Ferreira2023.json`. -/
def conjunctTable : List (String × Conjunct) :=
  [("pos_p", ⟨.possibility, false, false⟩), ("wn_p", ⟨.weakNecessity, false, false⟩),
   ("sn_p", ⟨.necessity, false, false⟩), ("pos_notp", ⟨.possibility, false, true⟩),
   ("wn_notp", ⟨.weakNecessity, false, true⟩), ("sn_notp", ⟨.necessity, false, true⟩),
   ("not_pos_p", ⟨.possibility, true, false⟩), ("not_wn_p", ⟨.weakNecessity, true, false⟩),
   ("not_sn_p", ⟨.necessity, true, false⟩)]

/-- A row pairs a conjunction with the paper's judgment. -/
structure Row where
  /-- The conjunction. -/
  pattern : Pattern
  /-- The paper's judgment. -/
  judgment : Judgment
  deriving DecidableEq, Repr

/-- The row of an example tagged with two conjuncts. -/
def Row.ofDatum (ex : Datum) : Option Row := do
  let first ← ex.parse? "first" conjunctTable
  let second ← ex.parse? "second" conjunctTable
  pure ⟨⟨first, second⟩, ex.judgment⟩

theorem row_ofDatum_isSome :
    ∀ ex ∈ Examples.all, (ex.feature? "first").isSome → (Row.ofDatum ex).isSome := by
  decide

/-- The conjunctions of §2. -/
def rows : List Row := Examples.all.filterMap Row.ofDatum

/-- A conjunction of (16)–(25), (30) or (32) is judged `#` exactly when it is contradictory. -/
theorem rows_unacceptable_iff :
    ∀ r ∈ rows, (r.judgment = .unacceptable ↔ r.pattern.Contradictory) := by
  decide

end

/-! ### (80)–(81): suspending the knowledge that Peter is not in his office -/

/-- A world of the dialogues records whether Peter is in his office and whether the day is a
holiday. -/
@[ext]
structure Day where
  /-- Peter is in his office. -/
  office : Bool
  /-- The day is a holiday. -/
  holiday : Bool
  deriving DecidableEq, Repr

instance : Fintype Day :=
  Fintype.ofEquiv (Bool × Bool)
    ⟨fun x ↦ ⟨x.1, x.2⟩, fun v ↦ (v.office, v.holiday), fun _ ↦ rfl, fun _ ↦ rfl⟩

namespace Day

/-- Similarity by agreement on each coordinate, a totally realistic ordering source (41a). -/
def sim : Background Day :=
  fun w ↦ {fun v ↦ v.office = w.office, fun v ↦ v.holiday = w.holiday}

theorem sim_isTotallyRealistic : sim.IsTotallyRealistic := by
  intro w
  ext v
  simp only [Background.mem_accessibleWorlds, sim, Set.mem_insert_iff, Set.mem_singleton_iff,
    forall_eq_or_imp, forall_eq, Day.ext_iff]

/-- Normally people are in the office on workdays and not on holidays. -/
def normal : Background Day :=
  fun _ ↦ {fun v ↦ v.holiday = true → v.office = false,
    fun v ↦ v.holiday = false → v.office = true}

/-- The prejacent, that Peter is in his office. -/
def atOffice (v : Day) : Prop := v.office = true

/-- The target of the ordering revision, that the day is a workday. -/
def workday (v : Day) : Prop := v.holiday = false

/-- A has checked, and Peter is not in his office (81). -/
def checked : Background Day := fun _ ↦ {fun v ↦ v.office = false}

/-- A has said that the day is a holiday (80). -/
def holidayInfo : Background Day := fun _ ↦ {fun v ↦ v.holiday = true}

private theorem accessibleWorlds_checked (w : Day) :
    checked.accessibleWorlds w = {v | v.office = false} := by
  ext v
  simp only [Background.mem_accessibleWorlds, checked, Set.mem_ofPred_eq,
    Set.mem_singleton_iff, forall_eq,
    ]

private theorem accessibleWorlds_holidayInfo (w : Day) :
    holidayInfo.accessibleWorlds w = {v | v.holiday = true} := by
  ext v
  simp only [Background.mem_accessibleWorlds, holidayInfo, Set.mem_ofPred_eq,
    Set.mem_singleton_iff, forall_eq,
    ]

private theorem minimals_atOffice_sim (w : Day) :
    (premisePreorder (sim w)).minimals {v | atOffice v} = {⟨true, w.holiday⟩} := by
  ext ⟨o, h⟩
  obtain ⟨o', h'⟩ := w
  simp only [Preorder.mem_minimals_iff, Preorder.ofCriteria_le_iff,
    sim, atOffice, Set.mem_ofPred_eq,
    Set.mem_singleton_iff, Set.mem_insert_iff, forall_eq_or_imp, forall_eq,
    ]
  cases o <;> cases h <;> cases o' <;> cases h' <;> decide

private theorem minimals_workday_sim (w : Day) :
    (premisePreorder (sim w)).minimals {v | workday v} = {⟨w.office, false⟩} := by
  ext ⟨o, h⟩
  obtain ⟨o', h'⟩ := w
  simp only [Preorder.mem_minimals_iff, Preorder.ofCriteria_le_iff, sim, workday, Set.mem_ofPred_eq,
    Set.mem_singleton_iff, Set.mem_insert_iff, forall_eq_or_imp, forall_eq,
    ]
  cases o <;> cases h <;> cases o' <;> cases h' <;> decide

-- (81)
private theorem accessibleWorlds_revise_checked (w : Day) :
    (revise sim checked atOffice).accessibleWorlds w = Set.univ := by
  rw [accessibleWorlds_revise, accessibleWorlds_checked]
  ext ⟨o, h⟩
  simp only [Set.mem_union, Set.mem_ofPred_eq, minimals_atOffice_sim, Set.mem_singleton_iff,
    Set.mem_univ, iff_true]
  cases o <;> cases h <;> decide

-- (80)
private theorem accessibleWorlds_revise_holidayInfo (w : Day) :
    (revise sim holidayInfo atOffice).accessibleWorlds w = {v | v.holiday = true} := by
  rw [accessibleWorlds_revise, accessibleWorlds_holidayInfo]
  ext ⟨o, h⟩
  simp only [Set.mem_union, Set.mem_ofPred_eq, minimals_atOffice_sim, Set.mem_singleton_iff]
  cases o <;> cases h <;> decide

-- footnote 18
private theorem accessibleWorlds_revise_workday (w : Day) :
    (revise sim holidayInfo workday).accessibleWorlds w = Set.univ := by
  rw [accessibleWorlds_revise, accessibleWorlds_holidayInfo]
  ext ⟨o, h⟩
  simp only [Set.mem_union, Set.mem_ofPred_eq, minimals_workday_sim, Set.mem_singleton_iff,
    Set.mem_univ, iff_true]
  cases o <;> cases h <;> decide

private theorem minimals_normal_univ (w : Day) :
    (premisePreorder (normal w)).minimals Set.univ = {⟨true, false⟩, ⟨false, true⟩} := by
  ext ⟨o, h⟩
  simp only [Preorder.mem_minimals_iff, Preorder.ofCriteria_le_iff, normal, Set.mem_univ, true_and,
    Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq,
    ]
  cases o <;> cases h <;> decide

private theorem minimals_normal_away (w : Day) :
    (premisePreorder (normal w)).minimals {v | v.office = false} = {⟨false, true⟩} := by
  rw [Preorder.minimals_ofCriteria_eq (s := ({v | v.office = false} : Set Day))
    (criteria := normal w)
    ⟨⟨false, true⟩, by simp, by simp [normal]⟩]
  ext ⟨o, h⟩
  simp only [normal, Set.mem_ofPred_eq, Set.mem_singleton_iff, Set.mem_insert_iff,
      forall_eq_or_imp, forall_eq,
    ]
  cases o <;> cases h <;> decide

private theorem minimals_normal_holiday (w : Day) :
    (premisePreorder (normal w)).minimals {v | v.holiday = true} = {⟨false, true⟩} := by
  rw [Preorder.minimals_ofCriteria_eq (s := ({v | v.holiday = true} : Set Day))
    (criteria := normal w)
    ⟨⟨false, true⟩, by simp, by simp [normal]⟩]
  ext ⟨o, h⟩
  simp only [normal, Set.mem_ofPred_eq, Set.mem_singleton_iff, Set.mem_insert_iff,
      forall_eq_or_imp, forall_eq,
    ]
  cases o <;> cases h <;> decide

private theorem minimals_workday_pair :
    (premisePreorder {workday}).minimals ({⟨true, false⟩, ⟨false, true⟩} : Set Day) =
      {⟨true, false⟩} := by
  ext ⟨o, h⟩
  simp only [Preorder.mem_minimals_iff, Preorder.ofCriteria_le_iff, workday, Set.mem_insert_iff,
    Set.mem_singleton_iff, forall_eq_or_imp, forall_eq,
    implies_true,
    ]
  cases o <;> cases h <;> decide

theorem deve_guess (w : Day) :
    Vertex.necessity ⟨false, true⟩ sim ⊥ normal workday atOffice w := by
  rw [Vertex.necessity_xg_true, weakNecessity, bestWorlds]
  simp only [Vertex.base, Bool.false_eq_true, ↓reduceIte]
  rw [Background.accessibleWorlds_bot, minimals_normal_univ, minimals_workday_pair]
  rintro _ rfl
  rfl

/-- After A has checked (81), *deve* is false and *devia* is true. -/
theorem devia_81 (w : Day) :
    ¬ Vertex.necessity ⟨false, true⟩ sim checked normal workday atOffice w ∧
      Vertex.necessity ⟨true, true⟩ sim checked normal workday atOffice w := by
  constructor
  · rw [Vertex.necessity_xg_true, weakNecessity, bestWorlds]
    simp only [Vertex.base, Bool.false_eq_true, ↓reduceIte]
    rw [accessibleWorlds_checked, minimals_normal_away, minimals_singleton]
    exact fun h ↦ Bool.false_ne_true (h _ rfl)
  · rw [Vertex.necessity_xg_true, weakNecessity, bestWorlds]
    simp only [Vertex.base, ↓reduceIte]
    rw [accessibleWorlds_revise_checked, minimals_normal_univ, minimals_workday_pair]
    rintro _ rfl
    rfl

/-- On a holiday (80) the suspension adds only holiday worlds, and *devia* is false. -/
theorem not_devia_80 (w : Day) :
    ¬ Vertex.necessity ⟨true, true⟩ sim holidayInfo normal workday atOffice w := by
  rw [Vertex.necessity_xg_true, weakNecessity, bestWorlds]
  simp only [Vertex.base, ↓reduceIte]
  rw [accessibleWorlds_revise_holidayInfo, minimals_normal_holiday, minimals_singleton]
  exact fun h ↦ Bool.false_ne_true (h _ rfl)

/-- Revising the base of (80) for the salient proposition, the workday, instead of the prejacent
would wrongly make *devia* true (footnote 18). -/
theorem revise_workday_80 (w : Day) :
    Vertex.necessity ⟨false, true⟩ sim (revise sim holidayInfo workday) normal workday atOffice
      w := by
  rw [Vertex.necessity_xg_true, weakNecessity, bestWorlds]
  simp only [Vertex.base, Bool.false_eq_true, ↓reduceIte]
  rw [accessibleWorlds_revise_workday, minimals_normal_univ, minimals_workday_pair]
  rintro _ rfl
  rfl

/-- The modal base of each dialogue, keyed as in the JSON, is what A has said. -/
def baseTable : List (String × Background Day) :=
  [("checked", checked), ("holiday", holidayInfo)]

/-- In (80)–(81), *devia* is judged true exactly when the X-marked weak necessity holds over
what A has said. -/
theorem dialogues_predicted :
    ∀ ex ∈ [Examples.ex_80, Examples.ex_81], ∃ b ∈ ex.parse? "base" baseTable,
      (ex.judgment = .acceptable ↔
        ∀ w, Vertex.necessity ⟨true, true⟩ sim b normal workday atOffice w) := by
  simp only [List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true, and_true]
  exact ⟨⟨holidayInfo, rfl, iff_of_false (by decide) fun h ↦ not_devia_80 ⟨false, true⟩ (h _)⟩,
    ⟨checked, rfl, iff_of_true rfl fun w ↦ (devia_81 w).2⟩⟩

end Day

end Ferreira2023
