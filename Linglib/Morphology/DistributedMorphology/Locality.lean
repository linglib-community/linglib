module

public import Linglib.Morphology.DistributedMorphology.Basic
public import Mathlib.Data.Fintype.Card

/-!
# Locality domains for contextual allomorphy and allosemy

The category-defining heads of a complex head are cyclic: merging one spells out the cyclic
domain below it. The cycle of a position is its [level](##DistributedMorphology.ComplexHead.level),
the number of cyclic heads at or below it, the root being a position of level zero; the positions
of one level are a cyclic head with the noncyclic heads above it, the edge of its phase, and the
positions below are the interior. A position [is active](##DistributedMorphology.ComplexHead.Active)
when another is spelled out if it belongs to that cycle or to the one before, so
[material two cycles down is
inactive](##DistributedMorphology.ComplexHead.not_active_of_add_two_le),
[nothing is sensitive to an outer cyclic
head](##DistributedMorphology.ComplexHead.not_active_of_lt_of_cyclic), and
[the root is active for the first cycle
alone](##DistributedMorphology.ComplexHead.active_bot_iff).
Within a cycle [a head sees a position](##DistributedMorphology.ComplexHead.Sees) only across
heads null at the interface, phonologically for allomorphy and semantically for allosemy. A probe
above the word finds [its last cycle](##DistributedMorphology.ComplexHead.lastCycle). The idiom
domain is level zero of the agentive heads, and neither it nor the root's domain contains the
other.

## Implementation notes

* A position is the root `⊥` or a head, `WithBot (Fin s.heads.length)`, so the root's domain is
  activity with respect to `⊥`.
* Which heads are cyclic is a parameter; a study whose heads have categories takes the
  categorizers, `Minimalist.Cat.IsCategorizer`.
* Activity is the word-internal case of the Phase Impenetrability Condition: what is inactive when
  a cyclic head is spelled out is the interior of the phase below it. Transfer on trees is in
  `Syntax/Minimalist/Phase/Transfer.lean`, and the two are not derived from one definition.

## References

* [embick-2010]
* [embick-2015]
* [marantz-2013]
* [embick-2021]
* [marcolli-chomsky-berwick-2025]
* [chomsky-2001]
-/

@[expose] public section

namespace DistributedMorphology

namespace ComplexHead

variable {R H : Type*} (s : ComplexHead R H)

/-! ### Levels -/

section Level

variable (p : H → Prop) [DecidablePred p]

/-- The number of heads satisfying `p` at or below a position, which is zero at the root. -/
def level (i : WithBot (Fin s.heads.length)) : ℕ :=
  i.recBotCoe 0 fun i ↦ (s.heads.take (i + 1)).countP (p ·)

@[simp] theorem level_bot : s.level p ⊥ = 0 := rfl

theorem level_coe (i : Fin s.heads.length) :
    s.level p i = (s.heads.take (i + 1)).countP (p ·) := rfl

variable {s p} {i j : WithBot (Fin s.heads.length)} {k : Fin s.heads.length}

theorem level_mono : Monotone (s.level p) := by
  intro i j hij
  induction i using WithBot.recBotCoe with
  | bot => exact Nat.zero_le _
  | coe i =>
    induction j using WithBot.recBotCoe with
    | bot => exact absurd hij (WithBot.not_coe_le_bot i)
    | coe j =>
      exact (List.take_prefix_take_left
        (Nat.succ_le_succ (Fin.le_def.1 (WithBot.coe_le_coe.1 hij)))).countP_le

/-- A head satisfying `p` raises the level of everything below it by one. -/
theorem level_add_one_le_of_lt (hik : i < k) (hk : p s.heads[k]) :
    s.level p i + 1 ≤ s.level p k := by
  have hstep : s.level p k = (s.heads.take k).countP (p ·) + 1 := by
    rw [level_coe, List.take_succ_eq_append_getElem k.isLt, List.countP_append,
      List.countP_singleton]
    simp [show p s.heads[(k : ℕ)] from hk]
  rw [hstep, Nat.add_le_add_iff_right]
  induction i using WithBot.recBotCoe with
  | bot => exact Nat.zero_le _
  | coe i =>
    exact (List.take_prefix_take_left (Fin.lt_def.1 (WithBot.coe_lt_coe.1 hik))).countP_le

theorem level_pos (hk : p s.heads[k]) : 0 < s.level p k :=
  level_add_one_le_of_lt (WithBot.bot_lt_coe k) hk

/-- The level of a head is zero exactly when no head at or below it satisfies `p`. -/
theorem level_coe_eq_zero_iff :
    s.level p k = 0 ↔ ∀ j ≤ k, ¬ p s.heads[j] := by
  constructor
  · intro h j hjk hj
    have := level_mono (p := p) (WithBot.coe_le_coe.2 hjk)
    exact absurd (level_pos hj) (by omega)
  · intro h
    rw [level_coe, List.countP_eq_zero]
    intro a ha
    obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem ha
    rw [List.length_take] at hn
    rw [List.getElem_take]
    simpa using h ⟨n, by omega⟩ (Fin.le_def.2 (by simp only; omega))

end Level

/-! ### Cycles and presence -/

variable (cyclic : H → Prop) [DecidablePred cyclic]

/-- The cycle in which a position undergoes Vocabulary Insertion, its own, or the first for the
root and the material below the first cyclic head. -/
def insertionCycle (i : WithBot (Fin s.heads.length)) : ℕ := max 1 (s.level cyclic i)

/-- Position `j` is present when position `i` is spelled out if it belongs to that cycle or to the
one before, whose heads remain present though already realized. -/
def Active (i j : WithBot (Fin s.heads.length)) : Prop :=
  s.level cyclic j ≤ s.insertionCycle cyclic i ∧
    s.insertionCycle cyclic i ≤ s.level cyclic j + 1

instance (i j : WithBot (Fin s.heads.length)) : Decidable (s.Active cyclic i j) :=
  inferInstanceAs (Decidable (_ ∧ _))

variable {s cyclic} {i j : WithBot (Fin s.heads.length)} {k l : Fin s.heads.length}

theorem active_self (i : WithBot (Fin s.heads.length)) : s.Active cyclic i i := by
  unfold Active insertionCycle; omega

theorem active_of_level_eq (h : s.level cyclic i = s.level cyclic j) :
    s.Active cyclic i j := by
  unfold Active insertionCycle; omega

/-- Nothing already in a cycle sees a later cyclic head, so there is no outward sensitivity to a
further category head. -/
theorem not_active_of_lt_of_cyclic (hik : i < k) (hi : 1 ≤ s.level cyclic i)
    (hk : cyclic s.heads[k]) : ¬ s.Active cyclic i k := by
  have := level_add_one_le_of_lt hik hk
  unfold Active insertionCycle; omega

/-- Two cyclic heads are never realized in one cycle, so category-defining heads do not fuse. -/
theorem not_active_of_cyclic_of_cyclic (hkl : k < l) (hk : cyclic s.heads[k])
    (hl : cyclic s.heads[l]) : ¬ s.Active cyclic k l :=
  not_active_of_lt_of_cyclic (WithBot.coe_lt_coe.2 hkl) (level_pos hk) hl

/-- Material two cycles down is inactive, the complement of an inner cyclic head being closed off
once the next cyclic head is spelled out. -/
theorem not_active_of_add_two_le (h : s.level cyclic j + 2 ≤ s.level cyclic i) :
    ¬ s.Active cyclic i j := by
  unfold Active insertionCycle; omega

/-! ### The root's domain -/

/-- The root is present for the positions of the first cycle only, the first category head and
the noncyclic heads up to the next. -/
theorem active_bot_iff : s.Active cyclic i ⊥ ↔ s.level cyclic i ≤ 1 := by
  unfold Active insertionCycle; simp only [level_bot]; omega

/-- The root's domain is an initial segment. -/
theorem Active.bot_of_le (h : s.Active cyclic i ⊥) (hji : j ≤ i) : s.Active cyclic j ⊥ :=
  active_bot_iff.2 ((level_mono hji).trans (active_bot_iff.1 h))

/-- A cyclic head above a cyclic head is not local to the root, since category change closes the
root's domain. -/
theorem not_active_bot_of_cyclic_of_cyclic (hkl : k < l) (hk : cyclic s.heads[k])
    (hl : cyclic s.heads[l]) : ¬ s.Active cyclic l ⊥ := by
  have h₁ := level_add_one_le_of_lt (WithBot.coe_lt_coe.2 hkl) hl
  have h₂ := level_pos hk
  exact not_active_of_add_two_le (by simp only [level_bot]; omega)

/-- A cyclic head local to the root is the first one. -/
theorem Active.cyclic_first (h : s.Active cyclic l ⊥) (hl : cyclic s.heads[l]) :
    ∀ k < l, ¬ cyclic s.heads[k] :=
  fun _ hkl hk ↦ not_active_bot_of_cyclic_of_cyclic hkl hk hl h

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

variable (s cyclic) in
/-- The last cycle is an initial stretch of the heads read from the top. -/
theorem lastCycle_prefix : s.lastCycle cyclic <+: s.heads.reverse := by
  conv_rhs => rw [← List.takeWhile_append_dropWhile (p := fun h ↦ !decide (cyclic h))
    (l := s.heads.reverse)]
  exact (List.prefix_append_right_inj _).2 (List.take_prefix 1 _)

/-- Merging a cyclic head closes the cycles below it and starts a new one. -/
@[simp]
theorem lastCycle_concat_of_cyclic {r : R} {hs : List H} {h : H} (hc : cyclic h) :
    (⟨r, hs ++ [h]⟩ : ComplexHead R H).lastCycle cyclic = [h] := by
  simp [lastCycle, hc]

/-- A noncyclic head joins the cycle of the word it merges with. -/
@[simp]
theorem lastCycle_concat_of_not_cyclic {r : R} {hs : List H} {h : H} (hc : ¬ cyclic h) :
    (⟨r, hs ++ [h]⟩ : ComplexHead R H).lastCycle cyclic =
      h :: (⟨r, hs⟩ : ComplexHead R H).lastCycle cyclic := by
  simp [lastCycle, hc]

private theorem lastCycle_mk_eq_filter_zipIdx (r : R) (hs : List H) :
    (⟨r, hs⟩ : ComplexHead R H).lastCycle cyclic =
      ((hs.zipIdx.filter fun x ↦
        (hs.take (x.2 + 1)).countP (cyclic ·) = hs.countP (cyclic ·)).map Prod.fst).reverse := by
  induction hs using List.reverseRecOn with
  | nil => simp [lastCycle]
  | append_singleton hs h ih =>
    have hold : ∀ x ∈ hs.zipIdx, (hs ++ [h]).take (x.2 + 1) = hs.take (x.2 + 1) := fun x hx ↦
      List.take_append_of_le_length (by have := List.snd_lt_of_mem_zipIdx hx; omega)
    have hle : ∀ x ∈ hs.zipIdx, (hs.take (x.2 + 1)).countP (cyclic ·) ≤ hs.countP (cyclic ·) :=
      fun x _ ↦ (List.take_prefix _ _).countP_le
    by_cases hc : cyclic h
    · have hnil : (hs.zipIdx.filter fun x ↦ (List.take (x.2 + 1) (hs ++ [h])).countP (cyclic ·) =
          (hs ++ [h]).countP (cyclic ·)) = [] :=
        List.filter_eq_nil_iff.2 fun x hx ↦ by
          have := hle x hx
          simp only [hold x hx, List.countP_append, List.countP_singleton, hc, decide_true,
            ↓reduceIte, decide_eq_true_eq]
          omega
      rw [lastCycle_concat_of_cyclic hc, List.zipIdx_append, List.filter_append, hnil]
      simp [List.take_of_length_le]
    · have hfilter : (hs.zipIdx.filter fun x ↦
          (List.take (x.2 + 1) (hs ++ [h])).countP (cyclic ·) = (hs ++ [h]).countP (cyclic ·)) =
          hs.zipIdx.filter fun x ↦
            (hs.take (x.2 + 1)).countP (cyclic ·) = hs.countP (cyclic ·) :=
        List.filter_congr fun x hx ↦ by simp [hold x hx, hc]
      rw [lastCycle_concat_of_not_cyclic hc, ih, List.zipIdx_append, List.filter_append, hfilter]
      simp [List.take_of_length_le]

variable (s cyclic) in
/-- The last cycle is the positions of the highest level, outermost first. -/
theorem lastCycle_eq_filter_level :
    s.lastCycle cyclic =
      (((List.finRange s.heads.length).filter fun i : Fin s.heads.length ↦
        s.level cyclic i = s.heads.countP (cyclic ·)).map fun i ↦ s.heads[i]).reverse := by
  have hz : s.heads.zipIdx =
      (List.finRange s.heads.length).map fun i : Fin s.heads.length ↦ (s.heads[i], (i : ℕ)) :=
    List.ext_getElem (by simp) fun i h₁ h₂ ↦ by simp
  rw [show s = ⟨s.root, s.heads⟩ from rfl, lastCycle_mk_eq_filter_zipIdx, hz, List.filter_map,
    List.map_map]
  rfl

/-! ### Interface adjacency -/

variable (s cyclic) (null : H → Prop)

/-- Position `i` sees position `j` at an interface when `j` is present at `i`'s insertion and
every head between them is null there, pruned for allomorphy and semantically null for
allosemy. -/
def Sees (i j : WithBot (Fin s.heads.length)) : Prop :=
  s.Active cyclic i j ∧
    ∀ k : Fin s.heads.length, min i j < k → (k : WithBot (Fin s.heads.length)) < max i j →
      null s.heads[k]

instance [DecidablePred null] (i j : WithBot (Fin s.heads.length)) :
    Decidable (s.Sees cyclic null i j) :=
  inferInstanceAs (Decidable (_ ∧ ∀ _, _ → _ → _))

variable {s cyclic null}

theorem Sees.active (h : s.Sees cyclic null i j) : s.Active cyclic i j := h.1

/-- A head sees the root when it is in the first cycle and every head below it is null. -/
theorem sees_bot_iff :
    s.Sees cyclic null l ⊥ ↔ s.level cyclic l ≤ 1 ∧ ∀ k < l, null s.heads[k] := by
  simp [Sees, active_bot_iff]

/-- An intervening head that is not null at the interface blocks conditioning. -/
theorem not_sees_of_not_null (hik : min i j < k)
    (hkj : (k : WithBot (Fin s.heads.length)) < max i j) (hk : ¬ null s.heads[k]) :
    ¬ s.Sees cyclic null i j :=
  fun h ↦ hk (h.2 k hik hkj)

/-- The interface domains agree wherever the two kinds of nullness agree between the positions,
one cycle bounding both. -/
theorem sees_congr {null' : H → Prop}
    (h : ∀ k : Fin s.heads.length, min i j < k → (k : WithBot (Fin s.heads.length)) < max i j →
      (null s.heads[k] ↔ null' s.heads[k])) :
    s.Sees cyclic null i j ↔ s.Sees cyclic null' i j :=
  and_congr_right fun _ ↦ forall_congr' fun k ↦ forall₂_congr fun h₁ h₂ ↦ h k h₁ h₂

end ComplexHead

end DistributedMorphology
