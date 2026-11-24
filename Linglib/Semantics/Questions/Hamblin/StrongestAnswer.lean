module

public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Order.Antichain
public import Linglib.Semantics.Questions.Hamblin.Basic

/-!
# The strongest true answer

Let `H` be a Hamblin set. A strongest true answer at a world `w` is a member of `H` that is true at
`w` and entails every member of `H` that is true at `w`. We write `IsStrongestTrueAnswer H w p`,
which unfolds to `IsLeast (karttunen H w) p`.

[dayal-1996] proposes that a question presupposes that it has a strongest true answer. We call this
condition `HasStrongestTrueAnswer H w`.

The main result is that the presupposition holds at `w` if and only if the weak answer at `w` is
itself a member of `H`. See `Question.hasStrongestTrueAnswer_iff`.

## References

* [dayal-1996]
* [heim-1994]
* [beck-rullmann-1999]
* [dayal-2016]
* [xiang-2022]
-/

@[expose] public section

namespace Question

variable {W : Type*} (H : Set (Set W)) (w : W)

/-! ### Dayal's strongest true answer -/

/-- A strongest true answer at `w` is a member of `H` true at `w` that entails every member true
at `w`, [dayal-1996]'s maximally informative true member. -/
abbrev IsStrongestTrueAnswer (p : Set W) : Prop := IsLeast (karttunen H w) p

/-- Dayal's existential presupposition holds at `w` when a strongest true member exists. -/
def HasStrongestTrueAnswer : Prop := ∃ p, IsStrongestTrueAnswer H w p

/-- The worlds where Dayal's existential presupposition holds. -/
def presupposition : Set W := {w | HasStrongestTrueAnswer H w}

@[simp] theorem mem_presupposition : w ∈ presupposition H ↔ HasStrongestTrueAnswer H w := Iff.rfl

theorem isStrongestTrueAnswer_iff {p : Set W} :
    IsStrongestTrueAnswer H w p ↔ p ∈ H ∧ p = weakAnswer H w := by
  constructor
  · intro h
    exact ⟨h.1.1,
      (Set.subset_sInter fun _ hq => h.2 hq).antisymm (Set.sInter_subset_of_mem h.1)⟩
  · rintro ⟨hp, rfl⟩
    exact ⟨⟨hp, self_mem_weakAnswer H w⟩, fun _ hq => Set.sInter_subset_of_mem hq⟩

theorem hasStrongestTrueAnswer_iff : HasStrongestTrueAnswer H w ↔ weakAnswer H w ∈ H :=
  ⟨fun ⟨_, h⟩ =>
    have h' := (isStrongestTrueAnswer_iff H w).1 h
    h'.2 ▸ h'.1,
   fun h => ⟨_, (isStrongestTrueAnswer_iff H w).2 ⟨h, rfl⟩⟩⟩

theorem HasStrongestTrueAnswer.exists_mem {H : Set (Set W)} {w : W}
    (h : HasStrongestTrueAnswer H w) : ∃ p ∈ H, w ∈ p :=
  let ⟨p, hp⟩ := h; ⟨p, hp.1.1, hp.1.2⟩

/-- When the members exclude one another, Dayal's presupposition is that one of them is true. -/
theorem presupposition_eq_sUnion {H : Set (Set W)} (hH : H.PairwiseDisjoint id) :
    presupposition H = ⋃₀ H := by
  refine Set.ext fun w ↦ ⟨fun h ↦ let ⟨p, hp, hw⟩ := h.exists_mem; ⟨p, hp, hw⟩,
    fun ⟨p, hp, hw⟩ ↦ ⟨p, ⟨hp, hw⟩, fun q hq ↦ ?_⟩⟩
  rw [hH.elim hq.1 hp (Set.not_disjoint_iff.2 ⟨w, hq.2, hw⟩)]

/-- A proposition and its negation carry no presupposition as a question. -/
theorem presupposition_pair_compl (p : Set W) : presupposition {p, pᶜ} = Set.univ := by
  rw [presupposition_eq_sUnion, Set.sUnion_pair, Set.union_compl_self]
  rintro a (rfl | rfl) b (rfl | rfl) hab
  exacts [absurd rfl hab, disjoint_compl_right, disjoint_compl_left, absurd rfl hab]

/-! ### Topical properties

A question as a topical property `P : α → Set W`, from short answers to propositions
([xiang-2022]), has the Hamblin set `Set.range P`, or `P '' D` over a domain `D` of short answers,
whose true members are the image of the true short answers. -/

section Range

variable {α : Type*}

theorem karttunen_image (P : α → Set W) (D : Set α) (w : W) :
    karttunen (P '' D) w = P '' {a ∈ D | w ∈ P a} := by
  ext p
  constructor
  · rintro ⟨⟨a, ha, rfl⟩, hw⟩
    exact ⟨a, ⟨ha, hw⟩, rfl⟩
  · rintro ⟨a, ⟨ha, hw⟩, rfl⟩
    exact ⟨⟨a, ha, rfl⟩, hw⟩

theorem karttunen_range (P : α → Set W) (w : W) :
    karttunen (Set.range P) w = P '' {a | w ∈ P a} := by
  rw [← Set.image_univ, karttunen_image, Set.sep_univ]

theorem hasStrongestTrueAnswer_range_iff (P : α → Set W) (w : W) :
    HasStrongestTrueAnswer (Set.range P) w ↔
      ∃ a, w ∈ P a ∧ ∀ b, w ∈ P b → P a ⊆ P b := by
  constructor
  · rintro ⟨p, ⟨⟨a, rfl⟩, hw⟩, hmin⟩
    exact ⟨a, hw, fun b hb => hmin ⟨⟨b, rfl⟩, hb⟩⟩
  · rintro ⟨a, hw, hmin⟩
    exact ⟨P a, ⟨⟨a, rfl⟩, hw⟩, by rintro q ⟨⟨b, rfl⟩, hb⟩; exact hmin b hb⟩

theorem isStrongestTrueAnswer_range_iff {P : α → Set W} {a : α} {w : W} :
    IsStrongestTrueAnswer (Set.range P) w (P a) ↔ w ∈ P a ∧ ∀ b, w ∈ P b → P a ⊆ P b := by
  rw [IsStrongestTrueAnswer, karttunen_range]
  exact and_congr ⟨fun ⟨_, hb, h⟩ => h ▸ hb, fun h => ⟨a, h, rfl⟩⟩ Set.forall_mem_image

theorem hasStrongestTrueAnswer_range_iff_exists {P : α → Set W} {w : W} :
    HasStrongestTrueAnswer (Set.range P) w ↔
      ∃ a, IsStrongestTrueAnswer (Set.range P) w (P a) := by
  refine ⟨fun ⟨p, hp⟩ => ?_, fun ⟨a, ha⟩ => ⟨_, ha⟩⟩
  obtain ⟨⟨a, rfl⟩, -⟩ := hp.1
  exact ⟨a, hp⟩

section LinearOrder

variable [LinearOrder α] {φ : α → Set W} {w : W}

theorem hasStrongestTrueAnswer_range_iff_isGreatest (hφ : StrictAnti φ) :
    HasStrongestTrueAnswer (Set.range φ) w ↔ ∃ m, IsGreatest {d | w ∈ φ d} m := by
  rw [hasStrongestTrueAnswer_range_iff]
  exact ⟨fun ⟨x, hxw, hent⟩ => ⟨x, hxw, fun y hy => not_lt.1 fun hxy => (hφ hxy).2 (hent y hy)⟩,
    fun ⟨m, hm⟩ => ⟨m, hm.1, fun _ hb => hφ.antitone (hm.2 hb)⟩⟩

theorem hasStrongestTrueAnswer_range_iff_isLeast (hφ : StrictMono φ) :
    HasStrongestTrueAnswer (Set.range φ) w ↔ ∃ m, IsLeast {d | w ∈ φ d} m :=
  hasStrongestTrueAnswer_range_iff_isGreatest (φ := fun d : αᵒᵈ => φ (OrderDual.ofDual d))
    fun _ _ h => hφ h

end LinearOrder

end Range

theorem isLeast_singleton (p : Set W) : IsLeast {p} p :=
  ⟨Set.mem_singleton p, fun _ hq => le_of_eq (Set.mem_singleton_iff.1 hq).symm⟩

theorem isStrongestTrueAnswer_iff_of_antichain (hH : IsAntichain (· ⊆ ·) H) {p : Set W} :
    IsStrongestTrueAnswer H w p ↔ karttunen H w = {p} := by
  constructor
  · intro h
    refine Set.eq_singleton_iff_unique_mem.2 ⟨h.1, fun q hq => ?_⟩
    by_contra hne
    exact hH h.1.1 hq.1 (Ne.symm hne) (h.2 hq)
  · intro h
    rw [IsStrongestTrueAnswer, h]
    exact isLeast_singleton p

theorem hasStrongestTrueAnswer_iff_of_antichain (hH : IsAntichain (· ⊆ ·) H) :
    HasStrongestTrueAnswer H w ↔ ∃ p, karttunen H w = {p} :=
  exists_congr fun _ => isStrongestTrueAnswer_iff_of_antichain H w hH

open Classical in
/-- Dayal's answerhood operator Ans-D returns the strongest true member when the presupposition
holds. -/
noncomputable def dayalAns : Option (Set W) :=
  if weakAnswer H w ∈ H then some (weakAnswer H w) else none

theorem dayalAns_eq_some_iff {p : Set W} :
    dayalAns H w = some p ↔ IsStrongestTrueAnswer H w p := by
  rw [isStrongestTrueAnswer_iff, dayalAns]
  split_ifs with h
  · constructor
    · intro e
      rw [Option.some.injEq] at e
      exact ⟨e ▸ h, e.symm⟩
    · rintro ⟨_, e⟩
      rw [e]
  · exact ⟨fun e => (by simp at e), fun ⟨hp, e⟩ => (h (e ▸ hp)).elim⟩

theorem dayalAns_isSome_iff : (dayalAns H w).isSome ↔ HasStrongestTrueAnswer H w := by
  rw [hasStrongestTrueAnswer_iff, dayalAns]
  split_ifs with h <;> simp [h]

theorem dayalAns_eq_none_iff : dayalAns H w = none ↔ ¬ HasStrongestTrueAnswer H w := by
  rw [hasStrongestTrueAnswer_iff, dayalAns]
  split_ifs with h <;> simp [h]

/-! ### Resolvability on an information state -/

/-- The members of `H` an information state `s` supports. -/
def supported (s : Set W) : Set (Set W) := {p ∈ H | s ⊆ p}

@[simp] theorem mem_supported {s p : Set W} : p ∈ supported H s ↔ p ∈ H ∧ s ⊆ p := Iff.rfl

@[simp] theorem supported_singleton : supported H {w} = karttunen H w := by
  ext p
  simp [supported, karttunen]

/-- Dayal's presupposition holds on an information state when the state supports a least member.
On the singleton state `{w}` it is the presupposition at `w`. -/
def HasStrongestAnswerOn (s : Set W) : Prop := ∃ p, IsLeast (supported H s) p

theorem hasStrongestAnswerOn_singleton :
    HasStrongestAnswerOn H {w} ↔ HasStrongestTrueAnswer H w := by
  rw [HasStrongestAnswerOn, supported_singleton]
  rfl

end Question
