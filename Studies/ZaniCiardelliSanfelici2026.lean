module

public import Linglib.Semantics.Conditionals.Counterfactual.Alternatives
public import Studies.BarLevFox2020

/-!
# Zani, Ciardelli and Sanfelici (2026): Simplification of Disjunctive Antecedents

This file formalizes the semantic predictions that Zani, Ciardelli and Sanfelici test in an
acquisition study of conditionals with disjunctive antecedents, *if A or B, C*. The three
readings of Table 2 are truth conditions over a similarity model: the simplification reading
SDA is the conjunction of the two simplifications, the substrate's `distributiveImp`; the
disjunctive conditional reading `DCR` is their disjunction; and the asymmetric reading AR is
the simplification of the more realistic disjunct. Under Lewis's minimal-change
semantics, the substrate's `disjunctiveImp`, the DAC quantifies over the closest worlds of the
disjunction, and §2's case analysis follows: when neither disjunct is more realistic than the
other the DAC is equivalent to SDA (`would_iff_distributive_of_equallyRealistic`), and when
one is more realistic it is equivalent to that disjunct's simplification
(`would_iff_of_moreRealistic`). The readings are ordered by strength, SDA entails AR entails
DCR (`would_of_distributive`, `dcr_of_would`).

The experiment's target items (9) are evaluated in the race scenario of §4: the squirrel and
the tortoise compete, the prize named in the consequent belongs to one of them, and the
similarity orderings of Figure 3 make the squirrel a more realistic winner than the tortoise
or tie them. Table 3's response patterns follow by computation (`table3_sda`, `table3_dcr`,
`table3_ar`), and acceptance of the closeness evaluation item *if the hare doesn't win, the
squirrel will win* reveals that the participant regards the squirrel as the more realistic
winner (`moreRealistic_of_closeness`). On the homogeneity accounts of Santorio and of
Cariani and Goldstein, SDA is the universal and DCR the existential resolution of the
homogeneous quantification over the disjuncts (`dcr_iff_homogeneity_ne_false`), which is the
source of the paper's prediction that children shift from DCR to SDA as they do for plural
definites; on Bar-Lev and Fox's account, the literal meaning is Lewis's (`literal_eq_would`)
and exhaustification strengthens it to SDA (`distributive_of_exh`).

## Implementation notes

* A proposition is more realistic than another at `w` when it has closest worlds and each of
  them is strictly closer than every closest world of the other (`MoreRealistic`); the case
  analysis of §2 assumes total similarity preorders on finitely many worlds.
* The scenario's worlds are the three possible winners, ordered by speed from the actual
  world in which the hare wins; the two orderings realize the conditions of Figure 3.

## TODO

* The response patterns of Tables 5–8, the rates of Figures 4 and 5 and the regression of
  Table 4 await a data format for experimental results.

## References

* [zani-ciardelli-sanfelici-2026]
* [lewis-1973b]
* [alonso-ovalle-2009]
* [santorio-2018]
* [cariani-goldstein-2020]
* [bar-lev-fox-2020]
* [tieu-kriz-chemla-2019]
-/

@[expose] public section

namespace ZaniCiardelliSanfelici2026

open Conditional

section Closest

variable {W : Type*} (ord : W → Preorder W) (A B : Set W) (w : W)

/-! ### Realism (§2) -/

/-- `A` is more realistic than `B` at `w` when `A` has closest worlds and each of them is
strictly closer to `w` than every closest `B`-world. -/
def MoreRealistic : Prop :=
  ((ord w).minimals A).Nonempty ∧ ∀ a ∈ (ord w).minimals A, ∀ b ∈ (ord w).minimals B,
    (ord w).lt a b

variable {ord A B w} [Finite W]

private theorem exists_mem_minimals_le {S : Set W} {x : W} (hx : x ∈ S) :
    ∃ b ∈ (ord w).minimals S, (ord w).le b x :=
  Preorder.exists_le_mem_minimals (let := ord w; wellFounded_lt) hx

-- §2
theorem minimals_union_of_moreRealistic (htot : ∀ w, Std.Total (ord w).le)
    (h : MoreRealistic ord A B w) : (ord w).minimals (A ∪ B) = (ord w).minimals A := by
  let := ord w
  obtain ⟨⟨a₀, ha₀⟩, hAB⟩ := h
  ext x
  rw [Preorder.mem_minimals_iff_forall_le (htot w), Preorder.mem_minimals_iff_forall_le (htot w)]
  refine ⟨fun ⟨hx, hle⟩ ↦ ⟨hx.resolve_right fun hxB ↦ ?_, fun u hu ↦ hle u (.inl hu)⟩,
    fun ⟨hx, hle⟩ ↦ ⟨.inl hx, ?_⟩⟩
  · obtain ⟨b, hb, hbx⟩ := exists_mem_minimals_le hxB
    exact (hAB a₀ ha₀ b hb).not_ge (hbx.trans (hle a₀ (.inl ha₀.1)))
  · rintro u (hu | hu)
    · exact hle u hu
    · obtain ⟨b, hb, hbu⟩ := exists_mem_minimals_le hu
      exact (hAB x ((Preorder.mem_minimals_iff_forall_le (htot w)).2 ⟨hx, hle⟩) b hb).le.trans hbu

-- §2
theorem minimals_union_of_equallyRealistic (htot : ∀ w, Std.Total (ord w).le)
    (hAB : ¬ MoreRealistic ord A B w) (hBA : ¬ MoreRealistic ord B A w) :
    (ord w).minimals (A ∪ B) = (ord w).minimals A ∪ (ord w).minimals B := by
  let := ord w
  have key : ∀ {S T : Set W}, ¬ MoreRealistic ord T S w →
      (ord w).minimals S ⊆ (ord w).minimals (S ∪ T) := by
    intro S T hTS x hx
    rw [Preorder.mem_minimals_iff_forall_le (htot w)] at hx ⊢
    refine ⟨.inl hx.1, ?_⟩
    rintro u (hu | hu)
    · exact hx.2 u hu
    by_contra hxu
    have hux := (((htot w).total x u).resolve_left hxu).lt_of_not_ge hxu
    obtain ⟨b, hb, hbu⟩ := exists_mem_minimals_le hu
    refine hTS ⟨⟨b, hb⟩, fun b' hb' a ha ↦ ?_⟩
    rw [Preorder.mem_minimals_iff_forall_le (htot w)] at hb hb'
    exact (hb'.2 b hb.1).trans_lt (hbu.trans_lt (hux.trans_le (hx.2 a ha.1)))
  refine subset_antisymm Preorder.minimals_union_subset (Set.union_subset (key hBA) ?_)
  rw [Set.union_comm]
  exact key hAB

end Closest

variable {W : Type*} (ord : W → Preorder W) (A B : Finset W) (C : Set W) (w : W)

/-! ### The three readings (Table 2) -/

/-- The disjunctive conditional reading holds when some simplification holds. -/
def DCR : Prop := w ∈ closestImp ord ↑A C ∨ w ∈ closestImp ord ↑B C

variable {ord A B w}

section Pair

variable [DecidableEq W]

section Finite

variable [Fintype W]

theorem would_iff_distributive_of_equallyRealistic (htot : ∀ w, Std.Total (ord w).le)
    (hAB : ¬ MoreRealistic ord ↑A ↑B w) (hBA : ¬ MoreRealistic ord ↑B ↑A w) :
    w ∈ disjunctiveImp ord {A, B} C ↔ w ∈ distributiveImp ord {A, B} C := by
  rw [disjunctiveImp_pair, mem_closestImp, minimals_union_of_equallyRealistic htot hAB hBA,
    Set.union_subset_iff, mem_distributiveImp_pair, mem_closestImp, mem_closestImp]

theorem would_iff_of_moreRealistic (htot : ∀ w, Std.Total (ord w).le)
    (h : MoreRealistic ord ↑A ↑B w) :
    w ∈ disjunctiveImp ord {A, B} C ↔ w ∈ closestImp ord ↑A C := by
  rw [disjunctiveImp_pair, mem_closestImp, minimals_union_of_moreRealistic htot h, mem_closestImp]

end Finite

theorem would_of_distributive (h : w ∈ distributiveImp ord {A, B} C) :
    w ∈ disjunctiveImp ord {A, B} C :=
  mem_disjunctiveImp_pair_of_mem_distributiveImp h

theorem dcr_of_would (htot : ∀ w, Std.Total (ord w).le) (h : w ∈ disjunctiveImp ord {A, B} C) :
    DCR ord A B C w := by
  rw [disjunctiveImp_pair] at h
  exact mem_closestImp_or_of_mem_union htot h

/-! ### Homogeneity and exhaustification (§2, §3) -/

theorem dcr_iff_homogeneity_ne_false [Fintype W] [∀ w, DecidableRel (ord w).le]
    [DecidablePred (· ∈ C)] :
    DCR ord A B C w ↔ homogeneousImp ord {A, B} C w ≠ -1 := by
  simp only [DCR, Ne, homogeneousImp_eq_neg_one_iff, Finset.insert_nonempty, true_and,
    Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq, not_and_or, not_not]

open BarLevFox2020 in
theorem literal_eq_would : closestImp ord (↑A ∪ ↑B) C = disjunctiveImp ord {A, B} C :=
  (disjunctiveImp_pair A B).symm

open BarLevFox2020 in
theorem distributive_of_exh
    (htot : ∀ w, Std.Total (ord w).le)
    (h₁ : ∃ v ∈ closestImp ord (↑A ∪ ↑B) C,
      v ∉ closestImp ord ↑B C ∪ closestImp ord (↑A ∩ ↑B) C)
    (h₂ : ∃ v ∈ closestImp ord (↑A ∪ ↑B) C,
      v ∉ closestImp ord ↑A C ∪ closestImp ord (↑A ∩ ↑B) C)
    (h : ∃ v ∈ closestImp ord ↑A C ∩ closestImp ord ↑B C, v ∉ closestImp ord (↑A ∩ ↑B) C)
    (hw : w ∈ Exhaustification.exhIEII (sdaAlts ord ↑A ↑B C) (closestImp ord (↑A ∪ ↑B) C)) :
    w ∈ distributiveImp ord {A, B} C := by
  rw [sda htot h₁ h₂ h] at hw
  exact mem_distributiveImp_pair.2 ⟨hw.1.1, hw.1.2⟩

end Pair

/-! ### The closeness evaluation item (§4) -/

variable [Fintype W]

theorem moreRealistic_of_closeness (htot : ∀ w, Std.Total (ord w).le) {H S T : Finset W}
    (hclose : w ∈ closestImp ord (↑H)ᶜ ↑S) (hS : S.Nonempty)
    (hT : ∀ t ∈ T, t ∉ H) (hST : ∀ t ∈ T, t ∉ S) : MoreRealistic ord ↑S ↑T w := by
  let := ord w
  refine ⟨(ord w).minimals_nonempty_of_finite S.finite_toSet (Finset.coe_nonempty.2 hS),
    fun a ha b hb ↦ ?_⟩
  rw [Preorder.mem_minimals_iff_forall_le (htot w)] at ha hb
  have hbH : b ∈ (↑H : Set W)ᶜ := hT b hb.1
  obtain ⟨m, hm, hmb⟩ := exists_mem_minimals_le (ord := ord) (w := w) hbH
  have ham := ha.2 m (hclose hm)
  refine (ham.trans hmb).lt_of_not_ge fun hba ↦ hST b hb.1 (hclose ?_)
  rw [Preorder.mem_minimals_iff_forall_le (htot w)] at hm ⊢
  exact ⟨hbH, fun u hu ↦ (hba.trans ham).trans (hm.2 u hu)⟩

/-! ### The race scenario and Table 3 -/

/-- The competitors of a scenario, in order of speed. -/
inductive Competitor
  | hare | squirrel | tortoise
  deriving DecidableEq, Fintype, Repr

/-- The prizes; each competitor's prize is fixed by the scenario. -/
inductive Prize
  | carrot | hazelnut | lettuce
  deriving DecidableEq, Repr

/-- Each competitor's prize. -/
def Competitor.prize : Competitor → Prize
  | .hare => .carrot
  | .squirrel => .hazelnut
  | .tortoise => .lettuce

/-- Speed rank, the hare fastest. -/
def Competitor.speed : Competitor → ℕ
  | .hare => 0
  | .squirrel => 1
  | .tortoise => 2

/-- In Figure 3(a), the non-equally realistic condition, a faster competitor is a more realistic
winner. -/
abbrev nonEqual (_ : Competitor) : Preorder Competitor := Preorder.lift Competitor.speed

/-- In Figure 3(b), the equally realistic condition, the squirrel and the tortoise tie. -/
abbrev equal (_ : Competitor) : Preorder Competitor := Preorder.lift fun v ↦ min v.speed 1

theorem nonEqual_total (w₀ : Competitor) : Std.Total (nonEqual w₀).le :=
  Preorder.total_lift _

/-- A target item (9) reads *if `first` or `second` wins, it will get `prize`*. -/
structure Item where
  first : Competitor
  second : Competitor
  prize : Prize

/-- The four target items (9a)–(9d). -/
def items : List Item :=
  [⟨.squirrel, .tortoise, .hazelnut⟩, ⟨.tortoise, .squirrel, .hazelnut⟩,
    ⟨.squirrel, .tortoise, .lettuce⟩, ⟨.tortoise, .squirrel, .lettuce⟩]

/-- The SDA verdict on an item in the actual world, where the hare won. -/
def Item.sda (it : Item) : Prop :=
  .hare ∈ distributiveImp nonEqual {{it.first}, {it.second}} {v | v.prize = it.prize}

/-- The DCR verdict on an item. -/
def Item.dcr (it : Item) : Prop :=
  DCR nonEqual {it.first} {it.second} {v | v.prize = it.prize} .hare

/-- Lewis's verdict on an item in the non-equally realistic condition is the asymmetric
reading. -/
def Item.ar (it : Item) : Prop :=
  .hare ∈ disjunctiveImp nonEqual {{it.first}, {it.second}} {v | v.prize = it.prize}

instance (it : Item) : Decidable it.sda := inferInstanceAs (Decidable (_ ∈ distributiveImp _ _ _))
instance (it : Item) : Decidable it.dcr := inferInstanceAs (Decidable (_ ∨ _))
instance (it : Item) : Decidable it.ar := inferInstanceAs (Decidable (_ ∈ disjunctiveImp _ _ _))

/-- On SDA in Table 3 every target item is false, since one simplification always fails. -/
theorem table3_sda : items.map (fun it ↦ decide it.sda) = [false, false, false, false] := by
  decide

/-- On DCR in Table 3 every target item is true, since one simplification always holds. -/
theorem table3_dcr : items.map (fun it ↦ decide it.dcr) = [true, true, true, true] := by
  decide

/-- On AR in Table 3 the items naming the squirrel's prize are true and the others false. -/
theorem table3_ar : items.map (fun it ↦ decide it.ar) = [true, true, false, false] := by
  decide

theorem table3_equal :
    items.map (fun it ↦ decide (.hare ∈ disjunctiveImp equal {{it.first}, {it.second}}
      {v | v.prize = it.prize})) = [false, false, false, false] := by
  decide

theorem closeness_item :
    .hare ∈ closestImp nonEqual {.hare}ᶜ {.squirrel} ∧
      .hare ∉ closestImp equal {.hare}ᶜ {.squirrel} := by
  decide

-- Table 3
theorem squirrel_moreRealistic : MoreRealistic nonEqual {.squirrel} {.tortoise} .hare := by
  simpa using moreRealistic_of_closeness nonEqual_total (H := {.hare}) (S := {.squirrel})
    (T := {.tortoise}) (by simpa using closeness_item.1) ⟨.squirrel, by simp⟩ (by decide)
    (by decide)

end ZaniCiardelliSanfelici2026
