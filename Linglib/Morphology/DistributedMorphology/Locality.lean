module

public import Linglib.Morphology.DistributedMorphology.Basic
public import Mathlib.Data.Fintype.Card

/-!
# Locality domains for contextual allomorphy and allosemy

The category-defining heads of a complex head are cyclic: merging one sends the cyclic domains in
its complement to the interfaces, so the heads of a word fall into cycles — a head's cycle is the
number of cyclic heads at or below it — and a head undergoes Vocabulary Insertion in its own cycle,
the material below the first cyclic head in the first. When a head is spelled out, the heads of its
cycle and of the cycle before are present, the latter already realized, while earlier material is
inactive and later cycles are not yet merged; the root, in the complement of the first cyclic head,
is active in the first cycle only. Within a cycle each interface adds its own adjacency: a head
conditions another only across heads null at that interface — pruned phonological zeros for
allomorphy, semantically null heads for allosemy — so the two domains coincide exactly where the two
kinds of nullness do. The idiom domain is a different bound, the heads below an agentive Voice, and
neither contains the other.

## Main definitions

* `DistributedMorphology.ComplexHead.cycle`, `DistributedMorphology.ComplexHead.insertionCycle`:
  a head's cycle and the cycle of its insertion.
* `DistributedMorphology.ComplexHead.Coactive`, `DistributedMorphology.ComplexHead.RootLocal`:
  presence of one head at another's insertion, and of the root.
* `DistributedMorphology.ComplexHead.Sees`, `DistributedMorphology.ComplexHead.SeesRoot`: presence
  plus adjacency across heads null at an interface.
* `DistributedMorphology.ComplexHead.lastCycle`: the heads a probe merged above the word can find.
* `DistributedMorphology.ComplexHead.IdiomLocal`: the heads below an agentive Voice.

## Main results

* `cycle_mono`, `RootLocal.of_le`: cycles grow outward and the root's domain is an initial
  segment.
* `not_rootLocal_of_cyclic_of_cyclic`, `RootLocal.cyclic_first`: an outer cyclic head is not local
  to the root, and a local cyclic head is the first.
* `not_coactive_of_lt_of_cyclic`, `not_coactive_of_cyclic_of_cyclic`: nothing sees an outer cyclic
  head, so there is no outward sensitivity to, and no fusion with, a later category head.
* `not_coactive_of_add_two_le`: material two cycles down is inactive.
* `not_sees_of_not_null`, `sees_congr`: an intervening non-null head blocks conditioning, and the
  interface domains agree where nullness agrees.

## References

* [D. Embick, *Localism versus globalism in morphology and phonology*][embick-2010]
* [A. Marantz, *Locality domains for contextual allomorphy across the
  interfaces*][marantz-2013]
* [D. Embick, *The motivation for roots in Distributed Morphology*][embick-2021]
-/

@[expose] public section

namespace DistributedMorphology

namespace ComplexHead

variable {R H : Type*} (s : ComplexHead R H)

/-! ### Cycles -/

variable (cyclic : H → Prop) [DecidablePred cyclic]

/-- The cycle of a head, the number of cyclic heads at or below it. The root counts as cycle
zero. -/
def cycle (i : Fin s.heads.length) : ℕ :=
  (Finset.univ.filter fun j : Fin s.heads.length => j ≤ i ∧ cyclic s.heads[j]).card

/-- The cycle in which a head undergoes Vocabulary Insertion, its own, or the first for the
material below the first cyclic head. -/
def insertionCycle (i : Fin s.heads.length) : ℕ := max 1 (s.cycle cyclic i)

/-- Head `j` is present when head `i` is spelled out if it belongs to that cycle or to the one
before, whose heads remain present though already realized. -/
def Coactive (i j : Fin s.heads.length) : Prop :=
  s.cycle cyclic j ≤ s.insertionCycle cyclic i ∧ s.insertionCycle cyclic i ≤ s.cycle cyclic j + 1

/-- The root is present for the heads of the first cycle only, the first category head and the
noncyclic heads up to the next. -/
def RootLocal (i : Fin s.heads.length) : Prop := s.cycle cyclic i ≤ 1

instance (i j : Fin s.heads.length) : Decidable (s.Coactive cyclic i j) :=
  inferInstanceAs (Decidable (_ ∧ _))

instance (i : Fin s.heads.length) : Decidable (s.RootLocal cyclic i) :=
  inferInstanceAs (Decidable (_ ≤ _))

variable {s cyclic} {i j k : Fin s.heads.length}

theorem cycle_mono (hij : i ≤ j) : s.cycle cyclic i ≤ s.cycle cyclic j :=
  Finset.card_le_card fun x hx => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact ⟨hx.1.trans hij, hx.2⟩

theorem one_le_cycle_of_cyclic (hi : cyclic s.heads[i]) : 1 ≤ s.cycle cyclic i :=
  Finset.card_pos.2 ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, le_rfl, hi⟩⟩

theorem cycle_add_one_le_of_lt_of_cyclic (hij : i < j) (hj : cyclic s.heads[j]) :
    s.cycle cyclic i + 1 ≤ s.cycle cyclic j := by
  have hsub :
      insert j (Finset.univ.filter fun k : Fin s.heads.length => k ≤ i ∧ cyclic s.heads[k]) ⊆
        Finset.univ.filter fun k : Fin s.heads.length => k ≤ j ∧ cyclic s.heads[k] := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rcases hx with rfl | ⟨hxi, hx⟩
    · exact ⟨le_rfl, hj⟩
    · exact ⟨hxi.trans hij.le, hx⟩
  have hnot : j ∉ Finset.univ.filter fun k : Fin s.heads.length => k ≤ i ∧ cyclic s.heads[k] := by
    simp [not_le.2 hij]
  unfold cycle
  rw [← Finset.card_insert_of_notMem hnot]
  exact Finset.card_le_card hsub

theorem two_le_cycle_of_cyclic_of_cyclic (hjk : j < k) (hki : k ≤ i) (hj : cyclic s.heads[j])
    (hk : cyclic s.heads[k]) : 2 ≤ s.cycle cyclic i := by
  have h₁ : s.cycle cyclic j + 1 ≤ s.cycle cyclic k := cycle_add_one_le_of_lt_of_cyclic hjk hk
  have h₂ : s.cycle cyclic k ≤ s.cycle cyclic i := cycle_mono hki
  have h₃ : 1 ≤ s.cycle cyclic j := one_le_cycle_of_cyclic hj
  omega

/-! ### The root's domain -/

/-- The root's domain is an initial segment. -/
theorem RootLocal.of_le (h : s.RootLocal cyclic i) (hji : j ≤ i) : s.RootLocal cyclic j :=
  (cycle_mono hji).trans h

/-- A cyclic head above a cyclic head is not local to the root, since category change closes the
root's domain. -/
theorem not_rootLocal_of_cyclic_of_cyclic (hji : j < i) (hj : cyclic s.heads[j])
    (hi : cyclic s.heads[i]) : ¬ s.RootLocal cyclic i :=
  fun h => absurd (two_le_cycle_of_cyclic_of_cyclic hji le_rfl hj hi)
    (by unfold RootLocal at h; omega)

/-- A local cyclic head is the first one. -/
theorem RootLocal.cyclic_first (h : s.RootLocal cyclic i) (hi : cyclic s.heads[i]) :
    ∀ j < i, ¬ cyclic s.heads[j] :=
  fun _ hji hj => not_rootLocal_of_cyclic_of_cyclic hji hj hi h

/-! ### Presence between heads -/

theorem coactive_self (i : Fin s.heads.length) : s.Coactive cyclic i i := by
  unfold Coactive insertionCycle; omega

theorem coactive_of_cycle_eq (h : s.cycle cyclic i = s.cycle cyclic j) : s.Coactive cyclic i j := by
  unfold Coactive insertionCycle; omega

/-- Nothing already in a cycle sees a later cyclic head, so there is no outward sensitivity to a
further category head. -/
theorem not_coactive_of_lt_of_cyclic (hij : i < j) (hi : 1 ≤ s.cycle cyclic i)
    (hj : cyclic s.heads[j]) : ¬ s.Coactive cyclic i j := by
  have := cycle_add_one_le_of_lt_of_cyclic hij hj
  unfold Coactive insertionCycle; omega

/-- Two cyclic heads are never realized in one cycle, so category-defining heads do not fuse. -/
theorem not_coactive_of_cyclic_of_cyclic (hij : i < j) (hi : cyclic s.heads[i])
    (hj : cyclic s.heads[j]) : ¬ s.Coactive cyclic i j :=
  not_coactive_of_lt_of_cyclic hij (one_le_cycle_of_cyclic hi) hj

/-- Material two cycles down is inactive, the complement of an inner cyclic head being closed off
once the next cyclic head is spelled out. -/
theorem not_coactive_of_add_two_le (h : s.cycle cyclic j + 2 ≤ s.cycle cyclic i) :
    ¬ s.Coactive cyclic i j := by
  unfold Coactive insertionCycle; omega

/-! ### The last cycle

Merging a cyclic head spells out the cyclic domains below it, so a probe merged above a word
finds only the heads of its last cycle: the highest cyclic head and the noncyclic heads above
it. -/

variable (s cyclic) in
/-- The heads of the last cycle, outermost first, which are the noncyclic heads above the highest
cyclic head and that head. -/
def lastCycle : List H :=
  s.heads.reverse.takeWhile (fun h ↦ !decide (cyclic h)) ++
    (s.heads.reverse.dropWhile (fun h ↦ !decide (cyclic h))).take 1

theorem lastCycle_mk_append {r : R} {hs above : List H} {h : H} (hc : cyclic h)
    (ha : ∀ a ∈ above, ¬ cyclic a) :
    (⟨r, hs ++ h :: above⟩ : ComplexHead R H).lastCycle cyclic = above.reverse ++ [h] := by
  have key : ∀ l : List H, (∀ a ∈ l, ¬ cyclic a) →
      (l ++ h :: hs.reverse).takeWhile (fun x ↦ !decide (cyclic x)) ++
        ((l ++ h :: hs.reverse).dropWhile (fun x ↦ !decide (cyclic x))).take 1 = l ++ [h] := by
    intro l hl
    induction l with
    | nil => simp [hc]
    | cons a l ih =>
      have ha' : ¬ cyclic a := hl a (by simp)
      simp only [List.cons_append, List.takeWhile_cons, List.dropWhile_cons, ha', decide_false,
        Bool.not_false, ↓reduceIte] at ih ⊢
      rw [ih fun b hb ↦ hl b (by simp [hb])]
  simpa [lastCycle, List.reverse_append] using key above.reverse (by simpa using ha)

/-! ### Interface adjacency -/

variable (s cyclic) (null : H → Prop)

/-- Head `i` sees head `j` at an interface when `j` is present at `i`'s insertion and every head
between them is null there, pruned for allomorphy and semantically null for allosemy. -/
def Sees (i j : Fin s.heads.length) : Prop :=
  s.Coactive cyclic i j ∧ ∀ k, min i j < k → k < max i j → null s.heads[k]

/-- Head `i` sees the root when it is in the first cycle and every head below it is null at the
interface. -/
def SeesRoot (i : Fin s.heads.length) : Prop :=
  s.RootLocal cyclic i ∧ ∀ k < i, null s.heads[k]

instance [DecidablePred null] (i j : Fin s.heads.length) : Decidable (s.Sees cyclic null i j) :=
  inferInstanceAs (Decidable (_ ∧ ∀ _, _ → _ → _))

instance [DecidablePred null] (i : Fin s.heads.length) : Decidable (s.SeesRoot cyclic null i) :=
  inferInstanceAs (Decidable (_ ∧ ∀ k < i, _))

variable {s cyclic null}

theorem Sees.coactive (h : s.Sees cyclic null i j) : s.Coactive cyclic i j := h.1

theorem SeesRoot.rootLocal (h : s.SeesRoot cyclic null i) : s.RootLocal cyclic i := h.1

/-- An intervening head that is not null at the interface blocks conditioning. -/
theorem not_sees_of_not_null (hik : min i j < k) (hkj : k < max i j) (hk : ¬ null s.heads[k]) :
    ¬ s.Sees cyclic null i j :=
  fun h => hk (h.2 k hik hkj)

theorem not_seesRoot_of_not_null (hki : k < i) (hk : ¬ null s.heads[k]) :
    ¬ s.SeesRoot cyclic null i :=
  fun h => hk (h.2 k hki)

/-- The interface domains agree wherever the two kinds of nullness agree between the heads, one
cycle bounding both. -/
theorem sees_congr {null' : H → Prop}
    (h : ∀ k, min i j < k → k < max i j → (null s.heads[k] ↔ null' s.heads[k])) :
    s.Sees cyclic null i j ↔ s.Sees cyclic null' i j :=
  and_congr_right fun _ => forall_congr' fun k => forall₂_congr fun h₁ h₂ => h k h₁ h₂

theorem seesRoot_congr {null' : H → Prop} (h : ∀ k < i, null s.heads[k] ↔ null' s.heads[k]) :
    s.SeesRoot cyclic null i ↔ s.SeesRoot cyclic null' i :=
  and_congr_right fun _ => forall₂_congr fun k hk => h k hk

/-! ### The idiom domain -/

variable (s) (agentive : H → Prop)

/-- The heads below an agentive Voice, to whose structure special meaning may be assigned across
cyclic heads. -/
def IdiomLocal (i : Fin s.heads.length) : Prop :=
  ∀ j ≤ i, ¬ agentive s.heads[j]

instance [DecidablePred agentive] (i : Fin s.heads.length) : Decidable (s.IdiomLocal agentive i) :=
  inferInstanceAs (Decidable (∀ j ≤ i, _))

variable {s agentive}

theorem IdiomLocal.of_le (h : s.IdiomLocal agentive i) (hji : j ≤ i) : s.IdiomLocal agentive j :=
  fun _ hj => h _ (hj.trans hji)

end ComplexHead

end DistributedMorphology
