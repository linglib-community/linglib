module

public import Mathlib.Data.Finset.Basic
public import Linglib.Semantics.Questions.Basic
public import Linglib.Semantics.Questions.Resolution
public import Linglib.Semantics.Questions.Partition.Inquisitive
public import Linglib.Logic.Modal.Basic

/-!
# Answerhood operators on Hamblin sets

A Hamblin set `H : Set (Set W)` is a set of propositions. The theories that
take a question to denote such a set locate "the answer at world `w`" by an
operator on the members of `H` true at `w`:

- `trueAnswers H w`, the [karttunen-1977] set of true members;
- `weakAnswer H w`, their intersection, the weakly exhaustive answer of
  [heim-1994] (Ans₁) and [beck-rullmann-1999];
- `strongAnswer H w`, the worlds deciding every member as `w` does, the
  strongly exhaustive answer of [groenendijk-stokhof-1984], and on a Hamblin
  set also Heim's Ans₂, since the weak answer determines the true members
  (`ker_weakAnswer`);
- `partition H`, the Groenendijk–Stokhof partition as a `Setoid`, the kernel of
  `trueAnswers H`: its cells are the strong answers (`strongAnswer_eq_cell`), and as an
  inquisitive question it is the meet of the members' polar questions
  (`fromSetoid_partition`);
- `IsStrongestTrueAnswer H w p`, [dayal-1996]'s maximally informative true
  member: the least true member under entailment, `IsLeast`. Its existence is
  Dayal's existential presupposition `IsExhaustivelyResolvable`; `dayalAns`
  returns it and `dayalStrongAns` applies Heim's strengthening to it;
- `IsExhaustivelyResolvableOn H s`, the presupposition on an information
  state: a least member the state supports, Dayal's at the singleton `{w}`;
- `isExhaustivelyResolvable_range_iff`, the presupposition on a topical
  property `P : α → Set W` from short answers to propositions ([xiang-2022]),
  whose Hamblin set is `Set.range P`: a true short answer entailing every
  true one, the maximally informative member of Fox and Hackl, which on a strictly
  monotone property is the greatest or least true degree
  (`isExhaustivelyResolvable_range_iff_isGreatest`);
- `box H R`, the question under necessity, the image of `H` under
  `SetRel.core R`, whose presupposition at a world is the prejacent's on
  that world's modal base (`isExhaustivelyResolvable_box_iff`);
- `KnowsAnswer H w Dox`, the center's knowledge of the answer, the box
  `SetRel.core` over its doxastic alternatives applied to the weak answer, and
  `PossiblyIgnorant H c Dox`, [dayal-2025]'s requirement on the perspectival
  center of a question;
- `exhCell H p`, [fox-2018]'s cells;
- `ofFinset F`, a finite family of finite propositions, on which the
  presuppositions are decidable.

The presupposition holds exactly when the weak answer is itself a member
(`isExhaustivelyResolvable_iff`), so Dayal's operator agrees with Heim's and
Beck and Rullmann's wherever it is defined, and its strong form agrees with
the Groenendijk–Stokhof answer (`dayalStrongAns_eq_some_iff`). An inquisitive
question `Q : Question W` enters through its alternatives `alt Q`, an
antichain, over which the least true member is the only true member
(`isStrongestTrueAnswer_iff_of_antichain`): the number-sensitive answerhood
of [dayal-2016] needs Hamblin sets whose members entail one another, which
`alt` discards.

## References

* [karttunen-1977]
* [groenendijk-stokhof-1984]
* [heim-1994]
* [dayal-1996]
* [beck-rullmann-1999]
* [dayal-2016]
* [dayal-2025]
* [fox-2018]
* [xiang-2022]
-/

@[expose] public section

namespace Question

open Question
open SetRel

variable {W : Type*} (H : Set (Set W)) (w : W)

/-! ### Karttunen sets and the weak and strong answers -/

/-- The true answers at `w` are the members of `H` true at `w`, the [karttunen-1977] denotation. -/
def trueAnswers : Set (Set W) := {p ∈ H | w ∈ p}

@[simp] theorem mem_trueAnswers {p : Set W} :
    p ∈ trueAnswers H w ↔ p ∈ H ∧ w ∈ p := Iff.rfl

theorem trueAnswers_subset : trueAnswers H w ⊆ H := fun _ h => h.1

/-- The weakly exhaustive answer is the intersection of the true members ([heim-1994]'s Ans₁,
[beck-rullmann-1999]'s Ans-BR). -/
def weakAnswer : Set W := ⋂₀ trueAnswers H w

@[simp] theorem mem_weakAnswer {v : W} :
    v ∈ weakAnswer H w ↔ ∀ p ∈ H, w ∈ p → v ∈ p := by
  simp [weakAnswer, and_imp]

theorem self_mem_weakAnswer : w ∈ weakAnswer H w := by simp

theorem weakAnswer_subset {p : Set W} (hp : p ∈ H) (hw : w ∈ p) :
    weakAnswer H w ⊆ p :=
  Set.sInter_subset_of_mem ⟨hp, hw⟩

/-- The strongly exhaustive answer at `w` is the set of worlds that decide every member of `H` as
`w` does ([groenendijk-stokhof-1984], [heim-1994]'s Ans₂). -/
def strongAnswer : Set W := {v | ∀ p ∈ H, (w ∈ p ↔ v ∈ p)}

@[simp] theorem mem_strongAnswer {v : W} :
    v ∈ strongAnswer H w ↔ ∀ p ∈ H, (w ∈ p ↔ v ∈ p) := Iff.rfl

theorem strongAnswer_subset_weakAnswer : strongAnswer H w ⊆ weakAnswer H w :=
  fun _ hv => (mem_weakAnswer H w).2 fun p hp hwp => (hv p hp).1 hwp

@[simp] theorem self_mem_strongAnswer : w ∈ strongAnswer H w := fun _ _ => Iff.rfl

/-- In the partition of [groenendijk-stokhof-1984], two worlds are equivalent when they have the
same true members: the kernel of the Karttunen denotation, whose cell [heim-1994]'s generalized
analysis has the agent believe. -/
def partition : Setoid W := Setoid.ker (trueAnswers H)

variable {H} in
theorem partition_iff {v w : W} : partition H v w ↔ ∀ p ∈ H, (v ∈ p ↔ w ∈ p) := by
  simp only [Setoid.ker_def, Set.ext_iff, mem_trueAnswers, and_congr_right_iff]

/-- The partition is the meet of the polar questions of the members. -/
theorem partition_eq_iInf : partition H = ⨅ p ∈ H, Setoid.polar p := by
  ext v w
  simp only [partition_iff, Setoid.iInf_iff, Setoid.polar_iff]

/-- The weak answer determines the true members: a world lies in each one's weak answer and
each one's weak answer lies in all of its true members, so [heim-1994]'s Ans₂ on a Hamblin
set, the proposition that the weak answer is what it is, is the cell of the partition. -/
theorem ker_weakAnswer : Setoid.ker (weakAnswer H) = partition H := by
  ext v w
  rw [Setoid.ker_def, partition_iff]
  constructor
  · intro h p hp
    have hw : w ∈ weakAnswer H v := h ▸ self_mem_weakAnswer H w
    have hv : v ∈ weakAnswer H w := h ▸ self_mem_weakAnswer H v
    exact ⟨fun hvp ↦ weakAnswer_subset H v hp hvp hw, fun hwp ↦ weakAnswer_subset H w hp hwp hv⟩
  · intro h
    ext u
    simp only [mem_weakAnswer]
    exact ⟨fun hu p hp hw ↦ hu p hp ((h p hp).2 hw), fun hu p hp hv ↦ hu p hp ((h p hp).1 hv)⟩

/-- The strong answer at `w` is the cell of `w`. -/
theorem strongAnswer_eq_cell : strongAnswer H w = (partition H).cell w := by
  ext v
  simp only [mem_strongAnswer, Setoid.mem_cell, partition_iff]
  exact forall₂_congr fun _ _ ↦ Iff.comm

theorem classes_partition : (partition H).classes = Set.range (strongAnswer H) := by
  ext C
  simp only [Setoid.classes, Set.mem_ofPred_eq, Set.mem_range, strongAnswer_eq_cell, eq_comm]
  rfl

/-- Two strong answers are equal or disjoint. -/
theorem strongAnswer_eq_or_disjoint (w v : W) :
    strongAnswer H w = strongAnswer H v ∨ Disjoint (strongAnswer H w) (strongAnswer H v) := by
  simpa only [strongAnswer_eq_cell] using (partition H).cell_eq_or_disjoint w v

/-- As an inquisitive question, the partition is the meet of the polar questions of the members:
a state resolves it iff it resolves whether each member holds. -/
theorem fromSetoid_partition : fromSetoid (partition H) = ⨅ p ∈ H, polar p := by
  simp only [partition_eq_iInf, fromSetoid_iInf, fromSetoid_polar]

/-- The strongly exhaustive answer to an inquisitive question mention-all answers it. -/
theorem completelyAnsweredBy_strongAnswer (Q : Question W) :
    CompletelyAnsweredBy Q (strongAnswer (alt Q) w) := by
  intro p hp
  by_cases hw : w ∈ p
  · exact Or.inl fun _ hv => (hv p hp).1 hw
  · exact Or.inr fun _ hv => (hv p hp).not.1 hw

/-! ### Dayal's strongest true answer -/

/-- A strongest true answer at `w` is a member of `H` true at `w` that entails every member true
at `w`, [dayal-1996]'s maximally informative true member. -/
abbrev IsStrongestTrueAnswer (p : Set W) : Prop := IsLeast (trueAnswers H w) p

/-- Dayal's existential presupposition holds at `w` when a strongest true member exists. -/
def IsExhaustivelyResolvable : Prop := ∃ p, IsStrongestTrueAnswer H w p

theorem isStrongestTrueAnswer_iff {p : Set W} :
    IsStrongestTrueAnswer H w p ↔ p ∈ H ∧ p = weakAnswer H w := by
  constructor
  · intro h
    exact ⟨h.1.1,
      (Set.subset_sInter fun _ hq => h.2 hq).antisymm (Set.sInter_subset_of_mem h.1)⟩
  · rintro ⟨hp, rfl⟩
    exact ⟨⟨hp, self_mem_weakAnswer H w⟩, fun _ hq => Set.sInter_subset_of_mem hq⟩

/-- The presupposition holds exactly when the weak answer is itself a member. -/
theorem isExhaustivelyResolvable_iff : IsExhaustivelyResolvable H w ↔ weakAnswer H w ∈ H :=
  ⟨fun ⟨_, h⟩ =>
    have h' := (isStrongestTrueAnswer_iff H w).1 h
    h'.2 ▸ h'.1,
   fun h => ⟨_, (isStrongestTrueAnswer_iff H w).2 ⟨h, rfl⟩⟩⟩

theorem IsExhaustivelyResolvable.exists_mem {H : Set (Set W)} {w : W}
    (h : IsExhaustivelyResolvable H w) : ∃ p ∈ H, w ∈ p :=
  let ⟨p, hp⟩ := h; ⟨p, hp.1.1, hp.1.2⟩

/-! ### Topical properties

A question as a topical property `P : α → Set W`, from short answers to propositions
([xiang-2022]), has the Hamblin set `Set.range P`, whose true members are the image of the
true short answers. -/

section Range

variable {α : Type*}

theorem trueAnswers_range (P : α → Set W) (w : W) :
    trueAnswers (Set.range P) w = P '' {a | w ∈ P a} := by
  ext p
  constructor
  · rintro ⟨⟨a, rfl⟩, hw⟩
    exact ⟨a, hw, rfl⟩
  · rintro ⟨a, hw, rfl⟩
    exact ⟨⟨a, rfl⟩, hw⟩

/-- On a topical property, Dayal's presupposition asks for a true short answer whose proposition
entails every true one. -/
theorem isExhaustivelyResolvable_range_iff (P : α → Set W) (w : W) :
    IsExhaustivelyResolvable (Set.range P) w ↔
      ∃ a, w ∈ P a ∧ ∀ b, w ∈ P b → P a ⊆ P b := by
  constructor
  · rintro ⟨p, ⟨⟨a, rfl⟩, hw⟩, hmin⟩
    exact ⟨a, hw, fun b hb => hmin ⟨⟨b, rfl⟩, hb⟩⟩
  · rintro ⟨a, hw, hmin⟩
    exact ⟨P a, ⟨⟨a, rfl⟩, hw⟩, by rintro q ⟨⟨b, rfl⟩, hb⟩; exact hmin b hb⟩

/-- The proposition of a short answer is the strongest true answer of a topical property when it
is true and entails every true one. -/
theorem isStrongestTrueAnswer_range_iff {P : α → Set W} {a : α} {w : W} :
    IsStrongestTrueAnswer (Set.range P) w (P a) ↔ w ∈ P a ∧ ∀ b, w ∈ P b → P a ⊆ P b := by
  rw [IsStrongestTrueAnswer, trueAnswers_range]
  exact and_congr ⟨fun ⟨_, hb, h⟩ => h ▸ hb, fun h => ⟨a, h, rfl⟩⟩ Set.forall_mem_image

/-- A topical property has a strongest true answer exactly when the proposition of some short
answer is one. -/
theorem isExhaustivelyResolvable_range_iff_exists {P : α → Set W} {w : W} :
    IsExhaustivelyResolvable (Set.range P) w ↔
      ∃ a, IsStrongestTrueAnswer (Set.range P) w (P a) := by
  refine ⟨fun ⟨p, hp⟩ => ?_, fun ⟨a, ha⟩ => ⟨_, ha⟩⟩
  obtain ⟨⟨a, rfl⟩, -⟩ := hp.1
  exact ⟨a, hp⟩

section LinearOrder

variable [LinearOrder α] {φ : α → Set W} {w : W}

/-- On a strictly antitone topical property Dayal's presupposition holds exactly when some degree
is the greatest true one. -/
theorem isExhaustivelyResolvable_range_iff_isGreatest (hφ : StrictAnti φ) :
    IsExhaustivelyResolvable (Set.range φ) w ↔ ∃ m, IsGreatest {d | w ∈ φ d} m := by
  rw [isExhaustivelyResolvable_range_iff]
  exact ⟨fun ⟨x, hxw, hent⟩ => ⟨x, hxw, fun y hy => not_lt.1 fun hxy => (hφ hxy).2 (hent y hy)⟩,
    fun ⟨m, hm⟩ => ⟨m, hm.1, fun _ hb => hφ.antitone (hm.2 hb)⟩⟩

/-- On a strictly monotone topical property Dayal's presupposition holds exactly when some degree
is the least true one. -/
theorem isExhaustivelyResolvable_range_iff_isLeast (hφ : StrictMono φ) :
    IsExhaustivelyResolvable (Set.range φ) w ↔ ∃ m, IsLeast {d | w ∈ φ d} m :=
  isExhaustivelyResolvable_range_iff_isGreatest (φ := fun d : αᵒᵈ => φ (OrderDual.ofDual d))
    fun _ _ h => hφ h

end LinearOrder

end Range

theorem isLeast_singleton (p : Set W) : IsLeast {p} p :=
  ⟨Set.mem_singleton p, fun _ hq => le_of_eq (Set.mem_singleton_iff.1 hq).symm⟩

/-- Over an antichain the least true member is the only true member. -/
theorem isStrongestTrueAnswer_iff_of_antichain (hH : IsAntichain (· ⊆ ·) H) {p : Set W} :
    IsStrongestTrueAnswer H w p ↔ trueAnswers H w = {p} := by
  constructor
  · intro h
    refine Set.eq_singleton_iff_unique_mem.2 ⟨h.1, fun q hq => ?_⟩
    by_contra hne
    exact hH h.1.1 hq.1 (Ne.symm hne) (h.2 hq)
  · intro h
    rw [IsStrongestTrueAnswer, h]
    exact isLeast_singleton p

theorem isExhaustivelyResolvable_iff_of_antichain (hH : IsAntichain (· ⊆ ·) H) :
    IsExhaustivelyResolvable H w ↔ ∃ p, trueAnswers H w = {p} :=
  exists_congr fun _ => isStrongestTrueAnswer_iff_of_antichain H w hH

/-- Over inquisitive alternatives the strongest true answer is the only true alternative. -/
theorem isStrongestTrueAnswer_alt_iff (Q : Question W) {p : Set W} :
    IsStrongestTrueAnswer (alt Q) w p ↔ trueAnswers (alt Q) w = {p} :=
  isStrongestTrueAnswer_iff_of_antichain _ w (alt_isAntichain Q)

/-! ### Knowing the answer -/

section Knowing

variable {c A : Set W} {Dox : SetRel W W}

/-- The center knows the answer to `H` at `w`: the weak answer holds throughout its doxastic
alternatives `Dox`, [karttunen-1977]'s meaning postulate for *know*. -/
def KnowsAnswer (Dox : SetRel W W) : Prop := w ∈ Dox.core (weakAnswer H w)

/-- The perspectival center is possibly ignorant in the context `c` when it may not know the
answer there, [dayal-2025]'s requirement on the center of a question. -/
def PossiblyIgnorant (c : Set W) (Dox : SetRel W W) : Prop := ∃ w ∈ c, ¬ KnowsAnswer H w Dox

variable {H} {w}

/-- Asserting content that entails the center's knowledge of the answer leaves no
world where the requirement holds. -/
theorem not_possiblyIgnorant_inter_of_subset (hA : A ⊆ {w | KnowsAnswer H w Dox}) :
    ¬ PossiblyIgnorant H (c ∩ A) Dox :=
  fun ⟨_, ⟨_, hw⟩, hk⟩ => hk (hA hw)

/-- Asserting that the center does not know the answer leaves the requirement to the
context. -/
theorem possiblyIgnorant_inter_compl_iff :
    PossiblyIgnorant H (c ∩ {w | KnowsAnswer H w Dox}ᶜ) Dox ↔ PossiblyIgnorant H c Dox :=
  ⟨fun ⟨w, ⟨hc, _⟩, hk⟩ => ⟨w, hc, hk⟩, fun ⟨w, hc, hk⟩ => ⟨w, ⟨hc, hk⟩, hk⟩⟩

/-- Asking whether some content holds leaves the requirement to the context. -/
theorem possiblyIgnorant_inter_union_compl_iff :
    PossiblyIgnorant H (c ∩ (A ∪ Aᶜ)) Dox ↔ PossiblyIgnorant H c Dox := by
  rw [Set.union_compl_self, Set.inter_univ]

/-- A center whose only doxastic alternative is the actual world knows every answer. -/
theorem knowsAnswer_id : KnowsAnswer H w .id := by
  rw [KnowsAnswer, SetRel.core_id]
  exact self_mem_weakAnswer H w

/-- A center with every world open knows only trivial answers. -/
theorem knowsAnswer_univ_iff :
    KnowsAnswer H w Set.univ ↔ weakAnswer H w = Set.univ :=
  ⟨fun h => Set.eq_univ_of_forall fun _ => h trivial, fun h _ _ => h ▸ Set.mem_univ _⟩

end Knowing

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

theorem dayalAns_isSome_iff : (dayalAns H w).isSome ↔ IsExhaustivelyResolvable H w := by
  rw [isExhaustivelyResolvable_iff, dayalAns]
  split_ifs with h <;> simp [h]

theorem dayalAns_eq_none_iff : dayalAns H w = none ↔ ¬ IsExhaustivelyResolvable H w := by
  rw [isExhaustivelyResolvable_iff, dayalAns]
  split_ifs with h <;> simp [h]

/-! ### Resolvability on an information state -/

/-- The members of `H` an information state `s` supports. -/
def supported (s : Set W) : Set (Set W) := {p ∈ H | s ⊆ p}

@[simp] theorem mem_supported {s p : Set W} : p ∈ supported H s ↔ p ∈ H ∧ s ⊆ p := Iff.rfl

@[simp] theorem supported_singleton : supported H {w} = trueAnswers H w := by
  ext p
  simp [supported, trueAnswers]

/-- Dayal's presupposition holds on an information state when the state supports a least member.
On the singleton state `{w}` it is the presupposition at `w`. -/
def IsExhaustivelyResolvableOn (s : Set W) : Prop := ∃ p, IsLeast (supported H s) p

theorem isExhaustivelyResolvableOn_singleton :
    IsExhaustivelyResolvableOn H {w} ↔ IsExhaustivelyResolvable H w := by
  rw [IsExhaustivelyResolvableOn, supported_singleton]
  rfl

/-! ### Questions under necessity -/

/-- The question `□Q` over the accessibility `R` necessitates every member: it is the image of
`H` under `SetRel.core R`. -/
def box {W' : Type*} (R : SetRel W' W) : Set (Set W') := R.core '' H

theorem mem_box {W' : Type*} {R : SetRel W' W} {q : Set W'} :
    q ∈ box H R ↔ ∃ p ∈ H, R.core p = q := Iff.rfl

/-- Necessity lifts the presupposition: `□Q` is resolvable at `x` iff `Q` is resolvable on the
worlds accessible from `x`, provided every world is the sole world accessible from some `x`. -/
theorem isExhaustivelyResolvable_box_iff {W' : Type*} {R : SetRel W' W}
    (hR : ∀ v, ∃ x, ∀ u, x ~[R] u ↔ u = v) {x : W'} {s : Set W} (hs : ∀ v, x ~[R] v ↔ v ∈ s) :
    IsExhaustivelyResolvable (box H R) x ↔ IsExhaustivelyResolvableOn H s := by
  have mem : ∀ p, x ∈ R.core p ↔ s ⊆ p := fun p =>
    ⟨fun h v hv => h ((hs v).2 hv), fun h v hv => h ((hs v).1 hv)⟩
  have mono : ∀ p q : Set W, p ⊆ q → R.core p ⊆ R.core q := fun _ _ ↦ core_subset_core
  have refl : ∀ p q : Set W, R.core p ⊆ R.core q → p ⊆ q := by
    intro p q h v hv
    obtain ⟨y, hy⟩ := hR v
    exact h (fun u hu => ((hy u).1 hu) ▸ hv) ((hy v).2 rfl)
  constructor
  · rintro ⟨q, ⟨⟨p, hp, rfl⟩, hx⟩, hmin⟩
    refine ⟨p, ⟨hp, (mem p).1 hx⟩, fun r ⟨hr, hsr⟩ => refl p r (hmin ⟨⟨r, hr, rfl⟩, (mem r).2 hsr⟩)⟩
  · rintro ⟨p, ⟨hp, hsp⟩, hmin⟩
    refine ⟨_, ⟨⟨p, hp, rfl⟩, (mem p).2 hsp⟩, ?_⟩
    rintro q ⟨⟨r, hr, rfl⟩, hx⟩
    exact mono p r (hmin ⟨hr, (mem r).1 hx⟩)

/-! ### Cells ([fox-2018]) -/

/-- The cell of `p` is the set of worlds where `p` is the strongest true member. -/
def exhCell (p : Set W) : Set W := {w | IsStrongestTrueAnswer H w p}

@[simp] theorem mem_exhCell {p : Set W} {w : W} :
    w ∈ exhCell H p ↔ IsStrongestTrueAnswer H w p := Iff.rfl

theorem exhCell_subset (p : Set W) : exhCell H p ⊆ p := fun _ h => h.1.2

/-- Where `p` is the strongest true member, the true members are those `p` entails. -/
theorem trueAnswers_eq_of_isStrongestTrueAnswer {p : Set W}
    (h : IsStrongestTrueAnswer H w p) : trueAnswers H w = {q ∈ H | p ⊆ q} :=
  Set.ext fun _ => ⟨fun hq => ⟨hq.1, h.2 hq⟩, fun ⟨hq, hpq⟩ => ⟨hq, hpq h.1.2⟩⟩

/-- The cell of the strongest true member at `w` is the strong answer at `w`. -/
theorem exhCell_eq_strongAnswer {p : Set W} (h : IsStrongestTrueAnswer H w p) :
    exhCell H p = strongAnswer H w := by
  ext v
  rw [mem_exhCell, mem_strongAnswer]
  constructor
  · exact fun hv q hq =>
      ⟨fun hwq => h.2 ⟨hq, hwq⟩ hv.1.2, fun hvq => hv.2 ⟨hq, hvq⟩ h.1.2⟩
  · exact fun hv =>
      ⟨⟨h.1.1, (hv p h.1.1).1 h.1.2⟩, fun _ hq => h.2 ⟨hq.1, (hv _ hq.1).2 hq.2⟩⟩

/-- Dayal's strong operator Ans-D/H, [heim-1994]'s strengthening of Ans-D, returns the worlds with
the same strongest true member as `w`. -/
noncomputable def dayalStrongAns : Option (Set W) := (dayalAns H w).map (exhCell H)

/-- Where defined, Dayal's strong operator is the Groenendijk–Stokhof answer. -/
theorem dayalStrongAns_eq_some_iff {A : Set W} :
    dayalStrongAns H w = some A ↔ IsExhaustivelyResolvable H w ∧ A = strongAnswer H w := by
  simp only [dayalStrongAns, Option.map_eq_some_iff, dayalAns_eq_some_iff]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨⟨p, hp⟩, exhCell_eq_strongAnswer H w hp⟩
  · rintro ⟨⟨p, hp⟩, rfl⟩
    exact ⟨p, hp, exhCell_eq_strongAnswer H w hp⟩

/-! ### Finite Hamblin sets

A finite family of finite propositions is the carrier on which the
presupposition is decidable; `ofFinset` places it in the `Set (Set W)` API. -/

section Finite

/-- The Hamblin set of a finite family of finite propositions. -/
def ofFinset (F : Finset (Finset W)) : Set (Set W) := ((↑) : Finset W → Set W) '' ↑F

@[simp] theorem mem_ofFinset {F : Finset (Finset W)} {p : Set W} :
    p ∈ ofFinset F ↔ ∃ q ∈ F, ↑q = p := by
  simp [ofFinset]

theorem isExhaustivelyResolvable_ofFinset_iff (F : Finset (Finset W)) (w : W) :
    IsExhaustivelyResolvable (ofFinset F) w ↔ ∃ p ∈ F, w ∈ p ∧ ∀ q ∈ F, w ∈ q → p ⊆ q := by
  constructor
  · rintro ⟨p, ⟨hp, hw⟩, hmin⟩
    obtain ⟨p', hp', rfl⟩ := mem_ofFinset.1 hp
    exact ⟨p', hp', hw, fun q hq hwq =>
      Finset.coe_subset.1 (hmin ⟨mem_ofFinset.2 ⟨q, hq, rfl⟩, hwq⟩)⟩
  · rintro ⟨p, hp, hw, hmin⟩
    refine ⟨↑p, ⟨mem_ofFinset.2 ⟨p, hp, rfl⟩, hw⟩, ?_⟩
    rintro q ⟨hq, hwq⟩
    obtain ⟨q', hq', rfl⟩ := mem_ofFinset.1 hq
    exact Finset.coe_subset.2 (hmin q' hq' hwq)

instance [DecidableEq W] (F : Finset (Finset W)) (w : W) :
    Decidable (IsExhaustivelyResolvable (ofFinset F) w) :=
  decidable_of_iff _ (isExhaustivelyResolvable_ofFinset_iff F w).symm

theorem isExhaustivelyResolvableOn_ofFinset_iff (F : Finset (Finset W)) (s : Finset W) :
    IsExhaustivelyResolvableOn (ofFinset F) ↑s ↔
      ∃ p ∈ F, s ⊆ p ∧ ∀ q ∈ F, s ⊆ q → p ⊆ q := by
  constructor
  · rintro ⟨p, ⟨hp, hs⟩, hmin⟩
    obtain ⟨p', hp', rfl⟩ := mem_ofFinset.1 hp
    exact ⟨p', hp', Finset.coe_subset.1 hs, fun q hq hsq =>
      Finset.coe_subset.1 (hmin ⟨mem_ofFinset.2 ⟨q, hq, rfl⟩, Finset.coe_subset.2 hsq⟩)⟩
  · rintro ⟨p, hp, hs, hmin⟩
    refine ⟨↑p, ⟨mem_ofFinset.2 ⟨p, hp, rfl⟩, Finset.coe_subset.2 hs⟩, ?_⟩
    rintro q ⟨hq, hsq⟩
    obtain ⟨q', hq', rfl⟩ := mem_ofFinset.1 hq
    exact Finset.coe_subset.2 (hmin q' hq' (Finset.coe_subset.1 hsq))

instance [DecidableEq W] (F : Finset (Finset W)) (s : Finset W) :
    Decidable (IsExhaustivelyResolvableOn (ofFinset F) ↑s) :=
  decidable_of_iff _ (isExhaustivelyResolvableOn_ofFinset_iff F s).symm

end Finite

/-! ### Polar and declarative questions -/

section Polar

variable {w} {p : Set W} (hne : p ≠ ∅) (hnu : p ≠ Set.univ)
include hne hnu

theorem trueAnswers_polar_of_pos (hwp : w ∈ p) :
    trueAnswers (alt (polar p)) w = {p} := by
  ext q
  constructor
  · rintro ⟨hq, hwq⟩
    rcases (mem_alt_polar_of_nontrivial hne hnu q).1 hq with rfl | rfl
    · exact Set.mem_singleton _
    · exact (hwq hwp).elim
  · intro hq
    obtain rfl := Set.mem_singleton_iff.1 hq
    exact ⟨(mem_alt_polar_of_nontrivial hne hnu _).2 (Or.inl rfl), hwp⟩

theorem trueAnswers_polar_of_neg (hwp : w ∉ p) :
    trueAnswers (alt (polar p)) w = {pᶜ} := by
  ext q
  constructor
  · rintro ⟨hq, hwq⟩
    rcases (mem_alt_polar_of_nontrivial hne hnu q).1 hq with rfl | rfl
    · exact (hwp hwq).elim
    · exact Set.mem_singleton _
  · intro hq
    obtain rfl := Set.mem_singleton_iff.1 hq
    exact ⟨(mem_alt_polar_of_nontrivial hne hnu _).2 (Or.inr rfl), hwp⟩

theorem weakAnswer_polar_of_pos (hwp : w ∈ p) : weakAnswer (alt (polar p)) w = p := by
  rw [weakAnswer, trueAnswers_polar_of_pos hne hnu hwp, Set.sInter_singleton]

theorem weakAnswer_polar_of_neg (hwp : w ∉ p) : weakAnswer (alt (polar p)) w = pᶜ := by
  rw [weakAnswer, trueAnswers_polar_of_neg hne hnu hwp, Set.sInter_singleton]

theorem strongAnswer_polar_of_pos (hwp : w ∈ p) : strongAnswer (alt (polar p)) w = p := by
  ext v
  simp only [mem_strongAnswer, alt_polar_of_nontrivial hne hnu, Set.mem_insert_iff,
    Set.mem_singleton_iff, forall_eq_or_imp, forall_eq, Set.mem_compl_iff]
  exact ⟨fun h => h.1.1 hwp,
    fun hv => ⟨iff_of_true hwp hv, iff_of_false (not_not.2 hwp) (not_not.2 hv)⟩⟩

theorem strongAnswer_polar_of_neg (hwp : w ∉ p) : strongAnswer (alt (polar p)) w = pᶜ := by
  ext v
  simp only [mem_strongAnswer, alt_polar_of_nontrivial hne hnu, Set.mem_insert_iff,
    Set.mem_singleton_iff, forall_eq_or_imp, forall_eq, Set.mem_compl_iff]
  exact ⟨fun h => h.2.1 hwp, fun hv => ⟨iff_of_false hwp hv, iff_of_true hwp hv⟩⟩

theorem isStrongestTrueAnswer_polar_of_pos (hwp : w ∈ p) :
    IsStrongestTrueAnswer (alt (polar p)) w p := by
  rw [IsStrongestTrueAnswer, trueAnswers_polar_of_pos hne hnu hwp]
  exact isLeast_singleton p

theorem isStrongestTrueAnswer_polar_of_neg (hwp : w ∉ p) :
    IsStrongestTrueAnswer (alt (polar p)) w pᶜ := by
  rw [IsStrongestTrueAnswer, trueAnswers_polar_of_neg hne hnu hwp]
  exact isLeast_singleton pᶜ

/-- A non-trivial polar question always satisfies Dayal's presupposition. -/
theorem isExhaustivelyResolvable_polar_of_nontrivial (w : W) :
    IsExhaustivelyResolvable (alt (polar p)) w := by
  by_cases hwp : w ∈ p
  · exact ⟨p, isStrongestTrueAnswer_polar_of_pos hne hnu hwp⟩
  · exact ⟨pᶜ, isStrongestTrueAnswer_polar_of_neg hne hnu hwp⟩

end Polar

theorem weakAnswer_ofSet_of_pos {p : Set W} {w : W} (hwp : w ∈ p) :
    weakAnswer (alt (ofSet p)) w = p := by
  ext v
  simp [weakAnswer, trueAnswers, alt_ofSet, hwp]

theorem strongAnswer_ofSet_of_pos {p : Set W} {w : W} (hwp : w ∈ p) :
    strongAnswer (alt (ofSet p)) w = p := by
  ext v
  simp [strongAnswer, alt_ofSet, hwp]

end Question
