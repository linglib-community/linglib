module

public import Linglib.Core.Data.Set.Sups
public import Mathlib.Order.Closure
public import Mathlib.Order.CompleteBooleanAlgebra

/-!
# Truthmaker content

This file defines conjunctive parthood, the containment relation of Kit Fine's theory of
truthmaker content. States are ordered by parthood, with fusion as join, and a unilateral
proposition is the set of states that exactly verify it, so a proposition over states `S` is a
`Set S`. Conjunction is the pointwise fusion `s ⊻ t`, disjunction is the union `s ∪ t`, and
Fine's entailment of `t` by `s` is the inclusion `s ⊆ t`.

A state inexactly verifies `s` when some part of it exactly verifies `s`, that is, when it lies
in `upperClosure s`. Inexact verification obeys the classical clauses: `upperClosure_sups` and
`upperClosure_union` say that the inexact verifiers of `s ⊻ t` and `s ∪ t` are the common and the
pooled inexact verifiers of `s` and `t`.

## Main definitions

* `Truthmaker.IsConjunctivePart t s`: every verifier of `s` contains a verifier of `t`, and every
  verifier of `t` is part of a verifier of `s`.
* `Truthmaker.regularClosure`: the closure operator sending `s` to the states that contain a
  verifier of `s` and are part of the fusion of its verifiers. Its closed sets are Fine's regular
  propositions, and the regular closure of `s ∪ t` is his disjunction in a regular domain.

## Main results

* `Truthmaker.isConjunctivePart_iff`: conjunctive parthood compares upper and lower closures.
* `Truthmaker.IsConjunctivePart.antisymm`: conjunctive parthood is antisymmetric on convex
  propositions.
* `Truthmaker.isConjunctivePart_singleton_right_iff`: parts of a single state are its parts.
* `Truthmaker.isConjunctivePart_sups_left`: a conjunct is a conjunctive part of a conjunction.
* `Truthmaker.isConjunctivePart_union_left_iff`: `s` contains `s ∨ t` only when every verifier of
  `t` is part of a verifier of `s`, so disjunction introduction fails for containment.
* `Truthmaker.isConjunctivePart_iff_sups_eq`: a closed convex proposition contains `t` exactly
  when conjoining `t` leaves it unchanged.
* `Truthmaker.isClosed_regularClosure_iff`: the regular propositions are those closed under
  nonempty fusions and convex.
* `Truthmaker.isConjunctivePart_regularClosure_iff`: regular closure does not change containment.
* `Truthmaker.regularClosure_eq_iff`: a regular proposition is determined by its inexact verifiers
  and its subject-matter.
* `Truthmaker.regularClosure_sups`, `Truthmaker.regularClosure_iSups`: in a distributive space,
  regular closure distributes over conjunction.
* `Truthmaker.regularClosure_union_sups`: disjunction distributes over conjunction in a regular
  domain.

## Implementation notes

Fine defines conjunctive parthood only between propositions with a verifier. The relation here is
total, and the empty proposition is a conjunctive part only of itself. Fine's closure condition asks
for closure under arbitrary nonempty fusions, which `isClosed_regularClosure_iff` states and of
which `SupClosed` is the finitary version. Fine states the distribution of regular closure over
conjunction, and the distribution of disjunction over conjunction, for regular propositions, but his
proofs apply them to unions and to sets of excluders that need not be regular. They are stated here
for arbitrary nonempty propositions. His distributivity assumption is mathlib's `Order.Frame`.

## References

* [K. Fine, *A Theory of Truthmaker Content I: Conjunction, Disjunction and Negation*
  (2017)][fine-2017a]
* [K. Fine, *Truthmaker Semantics* (2017)][fine-2017]
* [M. Jago, *Truthmaker Semantics* (2026)][jago-2026]
-/

@[expose] public section

open SetFamily

namespace Truthmaker

variable {S : Type*}

section Preorder

variable [Preorder S] {s t u : Set S}

/-- A proposition `t` is a conjunctive part of `s`, or `s` contains `t`, if every verifier of `s`
contains a verifier of `t` and every verifier of `t` is part of a verifier of `s`. -/
def IsConjunctivePart (t s : Set S) : Prop :=
  s ⊆ upperClosure t ∧ t ⊆ lowerClosure s

/-- Conjunctive parthood asks that every inexact verifier of `s` inexactly verify `t`, and that
every state below a verifier of `t` lie below a verifier of `s`. -/
theorem isConjunctivePart_iff :
    IsConjunctivePart t s ↔ upperClosure t ≤ upperClosure s ∧ lowerClosure t ≤ lowerClosure s := by
  rw [le_upperClosure, lowerClosure_le, IsConjunctivePart]

@[refl]
theorem IsConjunctivePart.refl (s : Set S) : IsConjunctivePart s s :=
  ⟨subset_upperClosure, subset_lowerClosure⟩

theorem IsConjunctivePart.rfl : IsConjunctivePart s s :=
  .refl s

theorem IsConjunctivePart.trans (hut : IsConjunctivePart u t) (hts : IsConjunctivePart t s) :
    IsConjunctivePart u s :=
  have h₁ := isConjunctivePart_iff.1 hut
  have h₂ := isConjunctivePart_iff.1 hts
  isConjunctivePart_iff.2 ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩

/-- Two convex propositions that are conjunctive parts of each other are equal. -/
theorem IsConjunctivePart.antisymm (hs : s.OrdConnected) (ht : t.OrdConnected)
    (hts : IsConjunctivePart t s) (hst : IsConjunctivePart s t) : s = t := by
  obtain ⟨hu₁, hl₁⟩ := isConjunctivePart_iff.1 hts
  obtain ⟨hu₂, hl₂⟩ := isConjunctivePart_iff.1 hst
  rw [← hs.upperClosure_inter_lowerClosure, ← ht.upperClosure_inter_lowerClosure,
    le_antisymm hu₂ hu₁, le_antisymm hl₂ hl₁]

/-- A proposition with a verifier is a conjunctive part of the proposition verified by `a` alone
exactly when each of its verifiers is part of `a`. -/
theorem isConjunctivePart_singleton_right_iff (ht : t.Nonempty) {a : S} :
    IsConjunctivePart t {a} ↔ ∀ b ∈ t, b ≤ a := by
  refine ⟨fun h b hb ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨_, rfl, hba⟩ := mem_lowerClosure.1 (h.2 hb)
    exact hba
  · obtain ⟨b, hb⟩ := ht
    exact ⟨Set.singleton_subset_iff.2 (mem_upperClosure.2 ⟨b, hb, h b hb⟩),
      fun c hc ↦ mem_lowerClosure.2 ⟨a, rfl, h c hc⟩⟩

theorem isConjunctivePart_singleton_left_iff (hs : s.Nonempty) {b : S} :
    IsConjunctivePart {b} s ↔ ∀ a ∈ s, b ≤ a := by
  refine ⟨fun h a ha ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨_, rfl, hba⟩ := mem_upperClosure.1 (h.1 ha)
    exact hba
  · obtain ⟨a, ha⟩ := hs
    exact ⟨fun c hc ↦ mem_upperClosure.2 ⟨b, rfl, h c hc⟩,
      Set.singleton_subset_iff.2 (mem_lowerClosure.2 ⟨a, ha, h a ha⟩)⟩

@[simp]
theorem isConjunctivePart_singleton_singleton {a b : S} :
    IsConjunctivePart {b} {a} ↔ b ≤ a := by
  simp [isConjunctivePart_singleton_right_iff]

/-- A proposition `s` contains the disjunction `s ∪ t` exactly when every verifier of `t` is part
of a verifier of `s`. -/
theorem isConjunctivePart_union_left_iff : IsConjunctivePart (s ∪ t) s ↔ t ⊆ lowerClosure s :=
  ⟨fun h ↦ Set.subset_union_right.trans h.2, fun h ↦
    ⟨Set.subset_union_left.trans subset_upperClosure, Set.union_subset subset_lowerClosure h⟩⟩

end Preorder

section SemilatticeSup

variable [SemilatticeSup S] {s t : Set S}

/-- A conjunct is a conjunctive part of a conjunction whose other conjunct has a verifier. -/
theorem isConjunctivePart_sups_left (ht : t.Nonempty) : IsConjunctivePart s (s ⊻ t) :=
  let ⟨b, hb⟩ := ht
  ⟨Set.sups_subset_iff.2 fun a ha _ _ ↦ mem_upperClosure.2 ⟨a, ha, le_sup_left⟩,
    fun a ha ↦ mem_lowerClosure.2 ⟨a ⊔ b, Set.sup_mem_sups ha hb, le_sup_left⟩⟩

theorem isConjunctivePart_sups_right (hs : s.Nonempty) : IsConjunctivePart t (s ⊻ t) :=
  Set.sups_comm t s ▸ isConjunctivePart_sups_left hs

theorem IsConjunctivePart.sups {u : Set S} (hu : SupClosed u) (hs : IsConjunctivePart s u)
    (ht : IsConjunctivePart t u) : IsConjunctivePart (s ⊻ t) u := by
  refine ⟨fun x hx ↦ ?_, Set.sups_subset_iff.2 fun a ha b hb ↦ ?_⟩
  · rw [upperClosure_sups]
    exact ⟨hs.1 hx, ht.1 hx⟩
  · obtain ⟨c, hc, hac⟩ := mem_lowerClosure.1 (hs.2 ha)
    obtain ⟨d, hd, hbd⟩ := mem_lowerClosure.1 (ht.2 hb)
    exact mem_lowerClosure.2 ⟨c ⊔ d, hu hc hd, sup_le_sup hac hbd⟩

/-- A closed, convex proposition `s` with a verifier contains `t` exactly when `s ⊻ t = s`. -/
theorem isConjunctivePart_iff_sups_eq (hs : s.Nonempty) (hsc : SupClosed s)
    (hso : s.OrdConnected) : IsConjunctivePart t s ↔ s ⊻ t = s := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ isConjunctivePart_sups_right hs⟩
  refine (Set.sups_subset_iff.2 fun a ha b hb ↦ ?_).antisymm fun a ha ↦ ?_
  · obtain ⟨c, hc, hbc⟩ := mem_lowerClosure.1 (h.2 hb)
    exact hso.out ha (hsc ha hc) ⟨le_sup_left, sup_le_sup_left hbc a⟩
  · obtain ⟨b, hb, hba⟩ := mem_upperClosure.1 (h.1 ha)
    exact Set.mem_sups.2 ⟨a, ha, b, hb, sup_eq_left.2 hba⟩

end SemilatticeSup

section CompleteLattice

variable [CompleteLattice S] {s t u : Set S}

theorem IsConjunctivePart.sSup_le (h : IsConjunctivePart t s) : sSup t ≤ sSup s :=
  _root_.sSup_le fun _ hb ↦
    let ⟨_, ha, hba⟩ := mem_lowerClosure.1 (h.2 hb)
    hba.trans (le_sSup ha)

theorem isConjunctivePart_iff_sSup_le (hs : sSup s ∈ s) :
    IsConjunctivePart t s ↔ s ⊆ upperClosure t ∧ sSup t ≤ sSup s :=
  ⟨fun h ↦ ⟨h.1, h.sSup_le⟩, fun ⟨h₁, h₂⟩ ↦
    ⟨h₁, fun _ hb ↦ mem_lowerClosure.2 ⟨_, hs, (le_sSup hb).trans h₂⟩⟩⟩

/-- The regular closure of a proposition `s` consists of the states that contain a verifier of `s`
and are part of the fusion of its verifiers. It is unrelated to the regular closure of
possibility semantics. -/
def regularClosure : ClosureOperator (Set S) :=
  .mk' (fun s ↦ ↑(upperClosure s) ∩ Set.Iic (sSup s))
    (fun _ _ h _ hx ↦ ⟨upperClosure_anti h hx.1, hx.2.trans (sSup_le_sSup h)⟩)
    (fun _ _ ha ↦ ⟨subset_upperClosure ha, le_sSup ha⟩)
    (fun _ _ ⟨hx₁, hx₂⟩ ↦
      let ⟨_, ⟨hb, _⟩, hbx⟩ := mem_upperClosure.1 hx₁
      let ⟨a, ha, hab⟩ := mem_upperClosure.1 hb
      ⟨mem_upperClosure.2 ⟨a, ha, hab.trans hbx⟩, hx₂.trans (sSup_le fun _ hy ↦ hy.2)⟩)

theorem mem_regularClosure {x : S} :
    x ∈ regularClosure s ↔ (∃ a ∈ s, a ≤ x) ∧ x ≤ sSup s :=
  Iff.rfl

@[simp] theorem regularClosure_empty : regularClosure (∅ : Set S) = ∅ := by
  ext
  simp [mem_regularClosure]

@[simp] theorem regularClosure_singleton (a : S) : regularClosure ({a} : Set S) = {a} := by
  ext x
  refine ⟨fun ⟨hx₁, hx₂⟩ ↦ ?_, fun hx ↦ regularClosure.le_closure _ hx⟩
  obtain ⟨_, rfl, hax⟩ := mem_upperClosure.1 hx₁
  exact le_antisymm (by simpa using hx₂) hax

theorem sSup_mem_regularClosure (hs : s.Nonempty) : sSup s ∈ regularClosure s :=
  let ⟨a, ha⟩ := hs
  ⟨mem_upperClosure.2 ⟨a, ha, le_sSup ha⟩, le_rfl⟩

@[simp] theorem sSup_regularClosure (s : Set S) : sSup (regularClosure s) = sSup s :=
  le_antisymm (sSup_le fun _ hx ↦ hx.2) (sSup_le_sSup (regularClosure.le_closure s))

@[simp] theorem upperClosure_regularClosure (s : Set S) :
    upperClosure (regularClosure s) = upperClosure s :=
  le_antisymm (upperClosure_anti (regularClosure.le_closure s)) (le_upperClosure.2 fun _ hx ↦ hx.1)

/-- Two propositions have the same regular closure exactly when they have the same inexact
verifiers and, if they have verifiers, the same subject-matter. -/
theorem regularClosure_eq_iff : regularClosure s = regularClosure t ↔
    upperClosure s = upperClosure t ∧ (s.Nonempty → sSup s = sSup t) := by
  refine ⟨fun h ↦ ⟨?_, fun _ ↦ ?_⟩, fun ⟨h₁, h₂⟩ ↦ ?_⟩
  · rw [← upperClosure_regularClosure s, h, upperClosure_regularClosure]
  · rw [← sSup_regularClosure s, h, sSup_regularClosure]
  · rcases s.eq_empty_or_nonempty with rfl | hs
    · rw [eq_comm, upperClosure_empty, upperClosure_eq_top_iff] at h₁
      rw [h₁]
    · change ↑(upperClosure s) ∩ Set.Iic (sSup s) = ↑(upperClosure t) ∩ Set.Iic (sSup t)
      rw [h₁, h₂ hs]

/-- The regular propositions, the closed sets of `regularClosure`, are those closed under nonempty
fusions and convex. -/
theorem isClosed_regularClosure_iff :
    regularClosure.IsClosed s ↔ (∀ t ⊆ s, t.Nonempty → sSup t ∈ s) ∧ s.OrdConnected := by
  rw [ClosureOperator.isClosed_iff_closure_le]
  refine ⟨fun h ↦ ⟨fun t hts ⟨b, hb⟩ ↦
    h ⟨mem_upperClosure.2 ⟨b, hts hb, le_sSup hb⟩, sSup_le_sSup hts⟩,
      ⟨fun a ha b hb x hx ↦ h ⟨mem_upperClosure.2 ⟨a, ha, hx.1⟩, hx.2.trans (le_sSup hb)⟩⟩⟩, ?_⟩
  rintro ⟨hc, ho⟩ x ⟨hx₁, hx₂⟩
  obtain ⟨a, ha, hax⟩ := mem_upperClosure.1 hx₁
  exact ho.out ha (hc s le_rfl ⟨a, ha⟩) ⟨hax, hx₂⟩

theorem isClosed_regularClosure_iff' :
    regularClosure.IsClosed s ↔ s.OrdConnected ∧ (s.Nonempty → sSup s ∈ s) := by
  rw [isClosed_regularClosure_iff]
  refine ⟨fun ⟨hc, ho⟩ ↦ ⟨ho, hc s le_rfl⟩, fun ⟨ho, hs⟩ ↦ ⟨fun t hts ⟨b, hb⟩ ↦ ?_, ho⟩⟩
  exact ho.out (hts hb) (hs ⟨b, hts hb⟩) ⟨le_sSup hb, sSup_le_sSup hts⟩

theorem supClosed_of_isClosed_regularClosure (hs : regularClosure.IsClosed s) : SupClosed s :=
  fun a ha b hb ↦ by simpa using
    (isClosed_regularClosure_iff.1 hs).1 {a, b} (Set.pair_subset ha hb) (Set.insert_nonempty a {b})

theorem ordConnected_of_isClosed_regularClosure (hs : regularClosure.IsClosed s) :
    s.OrdConnected :=
  (isClosed_regularClosure_iff.1 hs).2

/-- Regular closure preserves containment. -/
theorem IsConjunctivePart.regularClosure (h : IsConjunctivePart t s) :
    IsConjunctivePart (regularClosure t) (regularClosure s) := by
  refine isConjunctivePart_iff.2 ⟨?_, lowerClosure_le.2 fun x hx ↦ ?_⟩
  · simpa using (isConjunctivePart_iff.1 h).1
  · obtain ⟨b, hb, -⟩ := mem_upperClosure.1 hx.1
    obtain ⟨a, ha, -⟩ := mem_lowerClosure.1 (h.2 hb)
    exact mem_lowerClosure.2 ⟨sSup s, sSup_mem_regularClosure ⟨a, ha⟩, hx.2.trans h.sSup_le⟩

/-- If `s` contains the fusion of its verifiers, the regular closure of `s` contains that of `t`
exactly when `s` contains `t`. -/
theorem isConjunctivePart_regularClosure_iff (hs : sSup s ∈ s) :
    IsConjunctivePart (regularClosure t) (regularClosure s) ↔ IsConjunctivePart t s := by
  refine ⟨fun h ↦ (isConjunctivePart_iff_sSup_le hs).2 ⟨fun a ha ↦ ?_, ?_⟩,
    IsConjunctivePart.regularClosure⟩
  · simpa using h.1 (regularClosure.le_closure s ha)
  · simpa using h.sSup_le

end CompleteLattice

section Frame

variable [Order.Frame S] {s t u : Set S}

/-- In a distributive space, regular closure distributes over the conjunction of propositions with
verifiers. -/
theorem regularClosure_sups (hs : s.Nonempty) (ht : t.Nonempty) :
    regularClosure (s ⊻ t) = regularClosure s ⊻ regularClosure t := by
  ext x
  constructor
  · rintro ⟨hx₁, hx₂⟩
    obtain ⟨_, ⟨a, ha, b, hb, rfl⟩, habx⟩ := mem_upperClosure.1 hx₁
    rw [Set.sSup_sups hs ht] at hx₂
    refine Set.mem_sups.2 ⟨x ⊓ sSup s, ⟨mem_upperClosure.2 ⟨a, ha, le_inf (le_sup_left.trans habx)
      (le_sSup ha)⟩, inf_le_right⟩, x ⊓ sSup t, ⟨mem_upperClosure.2 ⟨b, hb,
      le_inf (le_sup_right.trans habx) (le_sSup hb)⟩, inf_le_right⟩, ?_⟩
    rw [← inf_sup_left, inf_eq_left.2 hx₂]
  · rintro ⟨y, ⟨hy₁, hy₂⟩, z, ⟨hz₁, hz₂⟩, rfl⟩
    obtain ⟨a, ha, hay⟩ := mem_upperClosure.1 hy₁
    obtain ⟨b, hb, hbz⟩ := mem_upperClosure.1 hz₁
    refine ⟨mem_upperClosure.2 ⟨a ⊔ b, Set.sup_mem_sups ha hb, sup_le_sup hay hbz⟩, ?_⟩
    rw [Set.sSup_sups hs ht]
    exact sup_le_sup hy₂ hz₂

/-- In a distributive space, regular closure distributes over the conjunction of a family of
propositions with verifiers. -/
theorem regularClosure_iSups {ι : Type*} {s : ι → Set S} (hs : ∀ i, (s i).Nonempty) :
    regularClosure (Set.iSups s) = Set.iSups fun i ↦ regularClosure (s i) := by
  ext x
  constructor
  · rintro ⟨hx₁, hx₂⟩
    obtain ⟨_, hy, hyx⟩ := mem_upperClosure.1 hx₁
    obtain ⟨f, hf, rfl⟩ := Set.mem_iSups.1 hy
    rw [Set.sSup_iSups hs] at hx₂
    refine Set.mem_iSups.2 ⟨fun i ↦ x ⊓ sSup (s i), fun i ↦ ⟨mem_upperClosure.2 ⟨f i, hf i,
      le_inf ((le_iSup f i).trans hyx) (le_sSup (hf i))⟩, inf_le_right⟩, ?_⟩
    rw [← inf_iSup_eq, inf_eq_left.2 hx₂]
  · intro hx
    obtain ⟨g, hg, rfl⟩ := Set.mem_iSups.1 hx
    choose f hf hfg using fun i ↦ mem_upperClosure.1 (hg i).1
    refine ⟨mem_upperClosure.2 ⟨_, Set.iSup_mem_iSups hf, iSup_mono hfg⟩, ?_⟩
    rw [Set.sSup_iSups hs]
    exact iSup_mono fun i ↦ (hg i).2

theorem isClosed_regularClosure_sups (hs : regularClosure.IsClosed s)
    (ht : regularClosure.IsClosed t) : regularClosure.IsClosed (s ⊻ t) := by
  rcases s.eq_empty_or_nonempty with rfl | hs'
  · simpa using regularClosure.isClosed_iff.2 regularClosure_empty
  rcases t.eq_empty_or_nonempty with rfl | ht'
  · simpa using regularClosure.isClosed_iff.2 regularClosure_empty
  rw [ClosureOperator.isClosed_iff_closure_le, regularClosure_sups hs' ht', hs.closure_eq,
    ht.closure_eq]

theorem regularClosure_sups_union (hs : s.Nonempty) (htu : (t ∪ u).Nonempty) :
    regularClosure s ⊻ regularClosure (t ∪ u) = regularClosure (s ⊻ t ∪ s ⊻ u) := by
  rw [← regularClosure_sups hs htu, Set.sups_union_right]

/-- Disjunction distributes over conjunction in a regular domain. -/
theorem regularClosure_union_sups (ht : t.Nonempty) (hu : u.Nonempty) :
    regularClosure (s ∪ t ⊻ u) = regularClosure (s ∪ t) ⊻ regularClosure (s ∪ u) := by
  rw [← regularClosure_sups (ht.mono Set.subset_union_right) (hu.mono Set.subset_union_right)]
  refine le_antisymm (regularClosure.monotone ?_) (regularClosure.le_closure_iff.1 ?_)
  · rintro x (hx | ⟨b, hb, c, hc, rfl⟩)
    · exact ⟨x, .inl hx, x, .inl hx, sup_idem x⟩
    · exact Set.sup_mem_sups (.inr hb) (.inr hc)
  · obtain ⟨b₀, hb₀⟩ := ht
    obtain ⟨c₀, hc₀⟩ := hu
    rintro _ ⟨x, hx, y, hy, rfl⟩
    have hxle : x ≤ sSup (s ∪ t ⊻ u) := hx.elim (fun h ↦ le_sSup (.inl h))
      fun h ↦ le_sup_left.trans (le_sSup (.inr (Set.sup_mem_sups h hc₀)))
    have hyle : y ≤ sSup (s ∪ t ⊻ u) := hy.elim (fun h ↦ le_sSup (.inl h))
      fun h ↦ le_sup_right.trans (le_sSup (.inr (Set.sup_mem_sups hb₀ h)))
    refine ⟨mem_upperClosure.2 ?_, sup_le hxle hyle⟩
    rcases hx with hx | hx
    · exact ⟨x, .inl hx, le_sup_left⟩
    rcases hy with hy | hy
    · exact ⟨y, .inl hy, le_sup_right⟩
    · exact ⟨x ⊔ y, .inr (Set.sup_mem_sups hx hy), le_rfl⟩

end Frame

end Truthmaker
