module

public import Linglib.Core.Order.OfCriteria
public import Mathlib.Order.Minimal
public import Mathlib.Data.Fintype.Card
public import Mathlib.Order.Preorder.Finite

/-!
# Minimal elements under a preorder given as a term

`Preorder.minimals p s` is the set of minimal elements of `s` under a preorder `p` that is passed
as a term rather than found by instance resolution. Mathlib's `Minimal` reads the order from the
`LE` instance of the type, which does not fit a setting where many preorders on one type are in
play and the preorder is itself data, as with the orderings of worlds in modal and conditional
semantics. The definition unfolds to `Minimal` for the membership predicate, so the lemmas of
`Mathlib.Order.Minimal` apply after `letI := p`.

Under a well-founded strict order [every element of a set lies above a minimal
one](##Preorder.exists_le_mem_minimals), so a set has minimal elements exactly when it is
nonempty. Under a total preorder the minimal elements are [the least
elements](##Preorder.mem_minimals_iff_forall_le), as for mathlib's `DirectedOn.minimal_iff_isLeast`,
and the minimal elements of the sets [determine the preorder](##Preorder.eq_of_minimals_eq). Under
the pullback of a linear order along a map they are [the elements of least
value](##Preorder.mem_minimals_lift), and under a preorder derived from criteria they are [the
elements satisfying every criterion](##Preorder.minimals_ofCriteria_eq) whenever some element does.

## Implementation notes

`Preorder.lift_le_iff` and `Preorder.lift_lt_iff` are not simp lemmas: a subtype is ordered by
`Preorder.lift Subtype.val`, so they would rewrite every subtype comparison to its coercion and
loop against `Subtype.coe_le_coe`. Mathlib has no decidability instance for `Minimal`; the one here
decides it on a finite type with decidable order and predicate.
-/

@[expose] public section

namespace Preorder

variable {α : Type*} {p : Preorder α} {s t : Set α} {a : α}

/-- The minimal elements of `s` under the preorder `p`. -/
def minimals (p : Preorder α) (s : Set α) : Set α := {a | @Minimal α p.toLE (· ∈ s) a}

theorem mem_minimals_iff : a ∈ p.minimals s ↔ a ∈ s ∧ ∀ ⦃b⦄, b ∈ s → p.le b a → p.le a b :=
  Iff.rfl

theorem minimals_subset (p : Preorder α) (s : Set α) : p.minimals s ⊆ s := fun _ h ↦ h.1

@[simp] theorem minimals_empty (p : Preorder α) : p.minimals ∅ = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ h ↦ h.1

/-- A minimal element of a union is a minimal element of one of its parts. -/
theorem minimals_union_subset : p.minimals (s ∪ t) ⊆ p.minimals s ∪ p.minimals t :=
  fun _ ha ↦ ha.1.imp (Minimal.mono ha fun _ ↦ .inl) (Minimal.mono ha fun _ ↦ .inr)

/-- An element minimal in a set is minimal in any subset that contains it. -/
theorem mem_minimals_of_subset (h : s ⊆ t) (ha : a ∈ p.minimals t) (has : a ∈ s) :
    a ∈ p.minimals s :=
  Minimal.mono ha (fun _ hb ↦ h hb) has

/-- Two preorders that agree on a set have the same minimal elements of it. -/
theorem minimals_congr {q : Preorder α} (h : ∀ a ∈ s, ∀ b ∈ s, p.le a b ↔ q.le a b) :
    p.minimals s = q.minimals s :=
  Set.ext fun a ↦
    ⟨fun ha ↦ ⟨ha.1, fun b hb hba ↦ (h a ha.1 b hb).1 (ha.2 hb ((h b hb a ha.1).2 hba))⟩,
      fun ha ↦ ⟨ha.1, fun b hb hba ↦ (h a ha.1 b hb).2 (ha.2 hb ((h b hb a ha.1).1 hba))⟩⟩

/-- The minimal elements of a set depend only on the strict order. -/
theorem minimals_eq_of_lt_iff {q : Preorder α} (h : ∀ a b, p.lt a b ↔ q.lt a b) :
    p.minimals s = q.minimals s :=
  Set.ext fun _ ↦ (@minimal_iff_forall_lt α _ _ p).trans <| by
    simp only [h]; exact (@minimal_iff_forall_lt α _ _ q).symm

/-- Under the preorder that relates every two elements, every element of a set is minimal. -/
@[simp] theorem minimals_top (s : Set α) : (⊤ : Preorder α).minimals s = s :=
  Set.ext fun _ ↦ ⟨fun h ↦ h.1, fun h ↦ ⟨h, fun _ _ _ ↦ trivial⟩⟩

/-- Under a well-founded strict order every element of a set lies above a minimal element of
the set. -/
theorem exists_le_mem_minimals (hp : WellFounded p.lt) (ha : a ∈ s) :
    ∃ b ∈ p.minimals s, p.le b a :=
  letI := p
  haveI : WellFoundedLT α := hp
  let ⟨b, hba, hb⟩ := exists_minimal_le_of_wellFoundedLT (· ∈ s) a ha
  ⟨b, hb, hba⟩

/-- Under a well-founded strict order a set has a minimal element exactly when it is
nonempty. -/
theorem minimals_nonempty_iff (hp : WellFounded p.lt) : (p.minimals s).Nonempty ↔ s.Nonempty :=
  ⟨fun ⟨a, ha⟩ ↦ ⟨a, ha.1⟩, fun ⟨_, ha⟩ ↦ (exists_le_mem_minimals hp ha).imp fun _ h ↦ h.1⟩

/-- Under a well-founded strict order the minimal elements of `s` lie in `t` exactly when every
element of `s` outside `t` lies strictly above an element of `s` in `t`. -/
theorem minimals_subset_iff_forall_exists_lt (hp : WellFounded p.lt) :
    p.minimals s ⊆ t ↔ ∀ a ∈ s, a ∉ t → ∃ b ∈ s, b ∈ t ∧ p.lt b a := by
  refine ⟨fun h a ha hat ↦ ?_, fun h a ha ↦ by_contra fun hat ↦ ?_⟩
  · obtain ⟨b, hb, hba⟩ := exists_le_mem_minimals hp ha
    refine ⟨b, hb.1, h hb, (p.lt_iff_le_not_ge _ _).2 ⟨hba, fun hab ↦ hat (h ⟨ha, fun c hc hca ↦
      p.le_trans _ _ _ hab (hb.2 hc (p.le_trans _ _ _ hca hab))⟩)⟩⟩
  · obtain ⟨b, hb, -, hlt⟩ := h a ha.1 hat
    have hlt' := (p.lt_iff_le_not_ge _ _).1 hlt
    exact hlt'.2 (ha.2 hb hlt'.1)

/-- Under a total preorder `a < b` exactly when `b ≤ a` fails. -/
theorem lt_iff_not_ge (hp : Std.Total p.le) {b : α} : p.lt a b ↔ ¬ p.le b a :=
  (p.lt_iff_le_not_ge a b).trans (and_iff_right_of_imp fun h ↦ (hp.total a b).resolve_right h)

/-- Under a total preorder the minimal elements of a set are its least elements. -/
theorem mem_minimals_iff_forall_le (hp : Std.Total p.le) :
    a ∈ p.minimals s ↔ a ∈ s ∧ ∀ b ∈ s, p.le a b :=
  letI := p
  haveI : Std.Total fun x y : α ↦ y ≤ x := ⟨fun a b ↦ hp.total b a⟩
  (Std.Total.directedOn s).minimal_iff_isLeast

/-- Under a total antisymmetric preorder a set has at most one minimal element. -/
theorem minimals_subsingleton (hp : Std.Total p.le) (ha : Std.Antisymm p.le) :
    (p.minimals s).Subsingleton := fun _ has _ hbs ↦
  letI : PartialOrder α := { p with le_antisymm := ha.antisymm }
  IsLeast.unique ((mem_minimals_iff_forall_le hp).1 has) ((mem_minimals_iff_forall_le hp).1 hbs)

/-- Under a well-founded total preorder, two sets whose minimal elements each lie in the other
have the same minimal elements. -/
theorem minimals_eq_of_subset_of_subset (hwf : WellFounded p.lt) (hp : Std.Total p.le)
    (hst : p.minimals s ⊆ t) (hts : p.minimals t ⊆ s) : p.minimals s = p.minimals t := by
  have key {s t : Set α} (hst : p.minimals s ⊆ t) (hts : p.minimals t ⊆ s) :
      p.minimals s ⊆ p.minimals t := fun a ha ↦ by
    obtain ⟨b, hb, -⟩ := exists_le_mem_minimals hwf (hst ha)
    have hab := ((mem_minimals_iff_forall_le hp).1 ha).2 b (hts hb)
    exact (mem_minimals_iff_forall_le hp).2 ⟨hst ha, fun c hc ↦
      p.le_trans _ _ _ hab (((mem_minimals_iff_forall_le hp).1 hb).2 c hc)⟩
  exact subset_antisymm (key hst hts) (key hts hst)

/-- Under a well-founded total preorder the minimal elements of a nonempty `s` lie in `t` exactly
when some element of `s` in `t` lies strictly below every element of `s` outside `t`. -/
theorem minimals_subset_iff_exists_forall_lt (hp : WellFounded p.lt) (hc : Std.Total p.le)
    (hs : s.Nonempty) : p.minimals s ⊆ t ↔ ∃ a ∈ s ∩ t, ∀ b ∈ s \ t, p.lt a b := by
  refine ⟨fun h ↦ ?_, fun ⟨a, ⟨has, _⟩, hlt⟩ b hb ↦ by_contra fun hbt ↦ ?_⟩
  · obtain ⟨a, ha, -⟩ := exists_le_mem_minimals hp hs.some_mem
    rw [mem_minimals_iff_forall_le hc] at ha
    refine ⟨a, ⟨ha.1, h ((mem_minimals_iff_forall_le hc).2 ha)⟩, fun b hb ↦
      (lt_iff_not_ge hc).2 fun hba ↦ hb.2 (h ?_)⟩
    exact (mem_minimals_iff_forall_le hc).2 ⟨hb.1, fun c hc' ↦ p.le_trans _ _ _ hba (ha.2 c hc')⟩
  · have hlt' := (p.lt_iff_le_not_ge _ _).1 (hlt b ⟨hb.1, hbt⟩)
    exact hlt'.2 (hb.2 has hlt'.1)

/-- Under a total preorder an element is minimal in a pair exactly when it is below the other
element. -/
theorem mem_minimals_pair (hp : Std.Total p.le) {b : α} : a ∈ p.minimals {a, b} ↔ p.le a b := by
  rw [mem_minimals_iff_forall_le hp]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or, true_and, forall_eq_or_imp,
    forall_eq]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨p.le_refl a, h⟩⟩

/-- Under a total preorder, when the minimal elements of `s` meet `t`, the minimal elements of
`s ∩ t` are those of `s` in `t`. -/
theorem minimals_inter_eq (hp : Std.Total p.le) (h : (p.minimals s ∩ t).Nonempty) :
    p.minimals (s ∩ t) = p.minimals s ∩ t := by
  obtain ⟨b, hb, hbt⟩ := h
  rw [mem_minimals_iff_forall_le hp] at hb
  ext a
  simp only [Set.mem_inter_iff, mem_minimals_iff_forall_le hp]
  exact ⟨fun ⟨⟨has, hat⟩, ha⟩ ↦ ⟨⟨has, fun c hc ↦ p.le_trans _ _ _ (ha b ⟨hb.1, hbt⟩) (hb.2 c hc)⟩,
      hat⟩, fun ⟨⟨has, ha⟩, hat⟩ ↦ ⟨⟨has, hat⟩, fun c hc ↦ ha c hc.1⟩⟩

/-- A total preorder is determined by its minimal elements. -/
theorem eq_of_minimals_eq {q : Preorder α} (hp : Std.Total p.le) (hq : Std.Total q.le)
    (h : p.minimals = q.minimals) : p = q :=
  Preorder.ext fun a b ↦ by rw [← mem_minimals_pair hp, ← mem_minimals_pair hq, h]

/-- On a finite type every nonempty set has a minimal element. -/
theorem minimals_nonempty [Finite α] (p : Preorder α) (hs : s.Nonempty) :
    (p.minimals s).Nonempty :=
  let ⟨_, ha⟩ := hs
  let ⟨b, hb, _⟩ := exists_le_mem_minimals (p := p) (letI := p; wellFounded_lt) ha
  ⟨b, hb⟩

/-- Every nonempty finite set has a minimal element. -/
theorem minimals_nonempty_of_finite (p : Preorder α) (hfin : s.Finite) (hs : s.Nonempty) :
    (p.minimals s).Nonempty :=
  letI := p
  hfin.exists_minimal hs

instance [Fintype α] (p : Preorder α) [DecidableRel p.le] (s : Set α) [DecidablePred (· ∈ s)]
    (a : α) : Decidable (a ∈ p.minimals s) :=
  decidable_of_iff (a ∈ s ∧ ∀ b, b ∈ s → p.le b a → p.le a b) Iff.rfl

instance {β : Type*} [Preorder β] [Fintype β] [DecidableLE β] {P : β → Prop}
    [DecidablePred P] (b : β) : Decidable (Minimal P b) :=
  decidable_of_iff (P b ∧ ∀ c, P c → c ≤ b → b ≤ c) Iff.rfl

/-! ### Preorders pulled back along a map -/

section lift

variable {β : Type*} (f : α → β)

-- Not `@[simp]`; see the implementation notes.
theorem lift_le_iff [Preorder β] {a b : α} : (Preorder.lift f).le a b ↔ f a ≤ f b :=
  Iff.rfl

theorem lift_lt_iff [Preorder β] {a b : α} : (Preorder.lift f).lt a b ↔ f a < f b :=
  Iff.rfl

instance [Preorder β] [DecidableLE β] : DecidableRel (Preorder.lift f).le :=
  fun a b ↦ inferInstanceAs (Decidable (f a ≤ f b))

instance [Preorder β] [DecidableLT β] : DecidableRel (Preorder.lift f).lt :=
  fun a b ↦ inferInstanceAs (Decidable (f a < f b))

/-- The pullback of a linear order is total. -/
theorem total_lift [LinearOrder β] : Std.Total (Preorder.lift f).le :=
  ⟨fun a b ↦ le_total (f a) (f b)⟩

/-- The pullback of a well-founded order is well-founded. -/
theorem wellFounded_lt_lift [Preorder β] [WellFoundedLT β] : WellFounded (Preorder.lift f).lt :=
  InvImage.wf f wellFounded_lt

/-- The minimal elements under the pullback of a linear order are the elements of least
value. -/
theorem mem_minimals_lift [LinearOrder β] :
    a ∈ (Preorder.lift f).minimals s ↔ a ∈ s ∧ ∀ b ∈ s, f a ≤ f b :=
  mem_minimals_iff_forall_le (total_lift f)

end lift

/-- Under a criteria-derived preorder, when some element of the set satisfies every criterion,
the minimal elements are exactly those that do. -/
theorem minimals_ofCriteria_eq {C : Type*} {sat : α → C → Prop} {criteria : Set C}
    (hex : ∃ a ∈ s, ∀ c ∈ criteria, sat a c) :
    (Preorder.ofCriteria sat criteria).minimals s = {a ∈ s | ∀ c ∈ criteria, sat a c} :=
  let ⟨_, hb, hsat⟩ := hex
  Set.ext fun _ ↦
    ⟨fun ⟨ha, hmin⟩ ↦ ⟨ha, fun c hc ↦ hmin hb (fun c' hc' _ ↦ hsat c' hc') c hc (hsat c hc)⟩,
      fun ⟨ha, hall⟩ ↦ ⟨ha, fun _ _ _ c hc _ ↦ hall c hc⟩⟩

end Preorder
