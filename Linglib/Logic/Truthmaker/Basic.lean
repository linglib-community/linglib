module

public import Linglib.Core.Data.Set.Sups
public import Mathlib.Order.Closure
public import Mathlib.Order.CompleteBooleanAlgebra

/-!
# Truthmaker content

States are ordered by parthood, with fusion as join, and a unilateral proposition is the set of
states that exactly verify it, so a proposition over states `S` is a `Set S`. Conjunction is the
pointwise fusion `s ⊻ t`, disjunction is the union `s ∪ t`, and entailment of `t` by `s` is the
inclusion `s ⊆ t`. A state inexactly verifies `s` when it lies in `upperClosure s`.

Kit Fine's second consequence relation is containment: `t` is a
[conjunctive part](##Truthmaker.IsConjunctivePart) of `s` when every verifier of `s` contains a
verifier of `t` and every verifier of `t` is part of a verifier of `s`. It is a preorder,
[antisymmetric on convex propositions](##Truthmaker.IsConjunctivePart.antisymm), and
[disjunction introduction fails for it](##Truthmaker.isConjunctivePart_union_left_iff). A
proposition is [regular](##Truthmaker.IsRegular) when it is closed under nonempty fusions and
convex, and the [regular closure](##Truthmaker.regularClosure) of `s` is the span from `s` to the
fusion of its verifiers. Among regular propositions with a verifier, a conjunction is the least
proposition containing its conjuncts: it
[contains each of them](##Truthmaker.isConjunctivePart_iSups) and
[is contained in every regular proposition that does](##Truthmaker.IsConjunctivePart.iSups), and
containment [compares inexact verifiers and
subject-matters](##Truthmaker.isConjunctivePart_iff_sSup_le). In a distributive space
[regular closure distributes over conjunction](##Truthmaker.regularClosure_iSups), so conjunctions
of regular propositions are regular, and
[disjunction distributes over conjunction](##Truthmaker.regularClosure_union_sups) in a regular
domain.

## Implementation notes

Fine defines conjunctive parthood only between propositions with a verifier. The relation here is
total, and the empty proposition is a conjunctive part only of itself. Fine states the
distribution of regular closure over conjunction for regular propositions with a verifier; it is
stated here for arbitrary propositions, and the distribution of disjunction over conjunction for
arbitrary propositions whose conjuncts have verifiers. His distributivity assumption is mathlib's
`Order.Frame`.

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

@[trans]
theorem IsConjunctivePart.trans (hut : IsConjunctivePart u t) (hts : IsConjunctivePart t s) :
    IsConjunctivePart u s :=
  have h₁ := isConjunctivePart_iff.1 hut
  have h₂ := isConjunctivePart_iff.1 hts
  isConjunctivePart_iff.2 ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩

@[simp]
theorem isConjunctivePart_empty_left : IsConjunctivePart ∅ s ↔ s = ∅ := by
  simp [IsConjunctivePart]

@[simp]
theorem isConjunctivePart_empty_right : IsConjunctivePart t ∅ ↔ t = ∅ := by
  simp [IsConjunctivePart]

theorem IsConjunctivePart.nonempty_iff (h : IsConjunctivePart t s) : t.Nonempty ↔ s.Nonempty :=
  ⟨fun ⟨_, hb⟩ ↦ let ⟨a, ha, _⟩ := mem_lowerClosure.1 (h.2 hb); ⟨a, ha⟩,
    fun ⟨_, ha⟩ ↦ let ⟨b, hb, _⟩ := mem_upperClosure.1 (h.1 ha); ⟨b, hb⟩⟩

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

/-- The proposition verified by the null state alone is a conjunctive part of every proposition
with a verifier. -/
theorem isConjunctivePart_singleton_bot [OrderBot S] (hs : s.Nonempty) :
    IsConjunctivePart {⊥} s :=
  (isConjunctivePart_singleton_left_iff hs).2 fun _ _ ↦ bot_le

/-- The proposition verified by the full state alone contains every proposition with a
verifier. -/
theorem isConjunctivePart_singleton_top [OrderTop S] (ht : t.Nonempty) :
    IsConjunctivePart t {⊤} :=
  (isConjunctivePart_singleton_right_iff ht).2 fun _ _ ↦ le_top

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

/-- A closed, convex proposition `s` with a verifier contains `t` exactly when it is the
conjunction of `t` with a proposition that has a verifier. -/
theorem isConjunctivePart_iff_exists_sups_eq (hs : s.Nonempty) (hsc : SupClosed s)
    (hso : s.OrdConnected) : IsConjunctivePart t s ↔ ∃ u : Set S, u.Nonempty ∧ u ⊻ t = s :=
  ⟨fun h ↦ ⟨s, hs, (isConjunctivePart_iff_sups_eq hs hsc hso).1 h⟩,
    fun ⟨_, hu, h⟩ ↦ h ▸ isConjunctivePart_sups_right hu⟩

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

/-- Each conjunct is a conjunctive part of a conjunction of propositions with verifiers. -/
theorem isConjunctivePart_iSups {ι : Type*} {s : ι → Set S} (hs : ∀ i, (s i).Nonempty) (i : ι) :
    IsConjunctivePart (s i) (Set.iSups s) := by
  refine ⟨fun x hx ↦ ?_, fun a ha ↦ ?_⟩
  · obtain ⟨f, hf, rfl⟩ := Set.mem_iSups.1 hx
    exact mem_upperClosure.2 ⟨f i, hf i, le_iSup f i⟩
  · obtain ⟨b, hb, hab⟩ := Set.exists_mem_iSups_ge hs ha
    exact mem_lowerClosure.2 ⟨b, hb, hab⟩

/-- A proposition is regular if it is closed under nonempty fusions and convex. -/
@[mk_iff]
structure IsRegular (s : Set S) : Prop where
  /-- The fusion of any verifiers is a verifier. -/
  sSup_mem ⦃t : Set S⦄ : t ⊆ s → t.Nonempty → sSup t ∈ s
  /-- A state between two verifiers is a verifier. -/
  ordConnected : s.OrdConnected

theorem IsRegular.supClosed (hs : IsRegular s) : SupClosed s :=
  fun a ha b hb ↦ by
    simpa using hs.sSup_mem (Set.pair_subset ha hb) (Set.insert_nonempty a {b})

/-- A regular proposition with a verifier is verified by its subject-matter, the fusion of its
verifiers. -/
theorem IsRegular.sSup_mem_self (hs : IsRegular s) (hne : s.Nonempty) : sSup s ∈ s :=
  hs.sSup_mem le_rfl hne

/-- A proposition is regular exactly when it is convex and, if it has a verifier, the fusion of
its verifiers verifies it. -/
theorem isRegular_iff_sSup_mem : IsRegular s ↔ s.OrdConnected ∧ (s.Nonempty → sSup s ∈ s) :=
  ⟨fun h ↦ ⟨h.ordConnected, h.sSup_mem_self⟩, fun ⟨ho, hs⟩ ↦ ⟨fun _ hts ⟨b, hb⟩ ↦
    ho.out (hts hb) (hs ⟨b, hts hb⟩) ⟨le_sSup hb, sSup_le_sSup hts⟩, ho⟩⟩

/-- In a finite lattice, the regular propositions are the convex sup-closed sets. -/
theorem isRegular_iff_of_finite [Finite S] : IsRegular s ↔ SupClosed s ∧ s.OrdConnected :=
  ⟨fun h ↦ ⟨h.supClosed, h.ordConnected⟩, fun ⟨hc, ho⟩ ↦
    ⟨fun _ hts ht ↦ hc.sSup_mem_of_nonempty (Set.toFinite _) ht hts, ho⟩⟩

/-- The span from `r` to `a`, the states that contain a member of `r` and are part of `a`, is
regular. -/
theorem isRegular_upperClosure_inter_Iic (r : Set S) (a : S) :
    IsRegular (↑(upperClosure r) ∩ Set.Iic a) :=
  ⟨fun _ ht ⟨_, hb⟩ ↦
      ⟨(upperClosure r).upper (le_sSup hb) (ht hb).1, sSup_le fun _ hx ↦ (ht hx).2⟩,
    (upperClosure r).upper.ordConnected.inter Set.ordConnected_Iic⟩

@[simp] theorem isRegular_empty : IsRegular (∅ : Set S) :=
  isRegular_iff_sSup_mem.2 ⟨Set.ordConnected_empty, fun h ↦ h.ne_empty.elim rfl⟩

@[simp] theorem isRegular_univ : IsRegular (Set.univ : Set S) :=
  ⟨fun _ _ _ ↦ trivial, Set.ordConnected_univ⟩

@[simp] theorem isRegular_singleton (a : S) : IsRegular ({a} : Set S) :=
  isRegular_iff_sSup_mem.2 ⟨Set.ordConnected_singleton, fun _ ↦ by simp⟩

/-- A regular proposition contains every proposition each of whose conjuncts it contains. -/
theorem IsConjunctivePart.iSups {ι : Type*} [Nonempty ι] {s : ι → Set S} (hu : IsRegular u)
    (hs : ∀ i, IsConjunctivePart (s i) u) : IsConjunctivePart (Set.iSups s) u := by
  refine ⟨fun x hx ↦ ?_, fun a ha ↦ ?_⟩
  · choose f hf hfx using fun i ↦ mem_upperClosure.1 ((hs i).1 hx)
    exact mem_upperClosure.2 ⟨_, Set.iSup_mem_iSups hf, iSup_le hfx⟩
  · obtain ⟨f, hf, rfl⟩ := Set.mem_iSups.1 ha
    choose g hg hfg using fun i ↦ mem_lowerClosure.1 ((hs i).2 (hf i))
    exact mem_lowerClosure.2
      ⟨_, hu.sSup_mem (Set.range_subset_iff.2 hg) (Set.range_nonempty g), iSup_mono hfg⟩

/-- The regular closure of a proposition `s` is the least regular proposition including it. It
consists of the states that contain a verifier of `s` and are part of the fusion of its
verifiers. It is unrelated to the regular closure of possibility semantics. -/
@[simps! isClosed]
def regularClosure : ClosureOperator (Set S) :=
  .ofPred (fun s ↦ ↑(upperClosure s) ∩ Set.Iic (sSup s)) IsRegular
    (fun _ _ ha ↦ ⟨subset_upperClosure ha, le_sSup ha⟩)
    (fun s ↦ isRegular_upperClosure_inter_Iic s (sSup s))
    (fun _ _ hst ht _ ⟨hx₁, hx₂⟩ ↦
      let ⟨_, ha, hax⟩ := mem_upperClosure.1 hx₁
      ht.ordConnected.out (hst ha) (ht.sSup_mem hst ⟨_, ha⟩) ⟨hax, hx₂⟩)

theorem mem_regularClosure {x : S} :
    x ∈ regularClosure s ↔ (∃ a ∈ s, a ≤ x) ∧ x ≤ sSup s :=
  Iff.rfl

@[simp] theorem subset_regularClosure : s ⊆ regularClosure s :=
  regularClosure.le_closure _

@[simp] theorem isRegular_regularClosure (s : Set S) : IsRegular (regularClosure s) :=
  regularClosure.isClosed_closure _

theorem regularClosure_mono : Monotone (regularClosure : Set S → Set S) :=
  regularClosure.monotone

theorem regularClosure_min (hst : s ⊆ t) (ht : IsRegular t) : regularClosure s ⊆ t :=
  ClosureOperator.closure_min hst ht

@[simp] theorem regularClosure_eq_self : regularClosure s = s ↔ IsRegular s :=
  regularClosure.isClosed_iff.symm

alias ⟨_, IsRegular.regularClosure_eq⟩ := regularClosure_eq_self

theorem regularClosure_idem (s : Set S) : regularClosure (regularClosure s) = regularClosure s :=
  regularClosure.idempotent _

@[simp] theorem regularClosure_empty : regularClosure (∅ : Set S) = ∅ := by simp

@[simp] theorem regularClosure_singleton (a : S) : regularClosure ({a} : Set S) = {a} := by simp

@[simp] theorem regularClosure_univ : regularClosure (Set.univ : Set S) = Set.univ := by simp

@[simp] theorem regularClosure_nonempty : (regularClosure s).Nonempty ↔ s.Nonempty :=
  ⟨fun ⟨_, hx⟩ ↦ let ⟨a, ha, _⟩ := mem_upperClosure.1 hx.1; ⟨a, ha⟩,
    fun h ↦ h.mono subset_regularClosure⟩

theorem sSup_mem_regularClosure (hs : s.Nonempty) : sSup s ∈ regularClosure s :=
  let ⟨a, ha⟩ := hs
  ⟨mem_upperClosure.2 ⟨a, ha, le_sSup ha⟩, le_rfl⟩

@[simp] theorem sSup_regularClosure (s : Set S) : sSup (regularClosure s) = sSup s :=
  le_antisymm (sSup_le fun _ hx ↦ hx.2) (sSup_le_sSup subset_regularClosure)

@[simp] theorem upperClosure_regularClosure (s : Set S) :
    upperClosure (regularClosure s) = upperClosure s :=
  le_antisymm (upperClosure_anti subset_regularClosure) (le_upperClosure.2 fun _ hx ↦ hx.1)

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
  · simpa using h.1 (subset_regularClosure ha)
  · simpa using h.sSup_le

end CompleteLattice

section Frame

variable [Order.Frame S] {s t u : Set S}

/-- In a distributive space, regular closure distributes over conjunction. -/
theorem regularClosure_sups (s t : Set S) :
    regularClosure (s ⊻ t) = regularClosure s ⊻ regularClosure t := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  rcases t.eq_empty_or_nonempty with rfl | ht
  · simp
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
propositions. -/
theorem regularClosure_iSups {ι : Type*} (s : ι → Set S) :
    regularClosure (Set.iSups s) = Set.iSups fun i ↦ regularClosure (s i) := by
  by_cases hs : ∀ i, (s i).Nonempty
  swap
  · rw [Set.not_nonempty_iff_eq_empty.1 (mt Set.iSups_nonempty.1 hs), regularClosure_empty,
      eq_comm, ← Set.not_nonempty_iff_eq_empty, Set.iSups_nonempty]
    simpa using hs
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

/-- In a distributive space, the conjunction of regular propositions is regular. -/
theorem IsRegular.sups (hs : IsRegular s) (ht : IsRegular t) : IsRegular (s ⊻ t) := by
  rw [← regularClosure_eq_self, regularClosure_sups, hs.regularClosure_eq, ht.regularClosure_eq]

theorem IsRegular.iSups {ι : Type*} {s : ι → Set S} (hs : ∀ i, IsRegular (s i)) :
    IsRegular (Set.iSups s) := by
  rw [← regularClosure_eq_self, regularClosure_iSups]
  simp only [(hs _).regularClosure_eq]

/-- Conjunction distributes over disjunction in a regular domain. -/
theorem regularClosure_sups_union (s t u : Set S) :
    regularClosure s ⊻ regularClosure (t ∪ u) = regularClosure (s ⊻ t ∪ s ⊻ u) := by
  rw [← regularClosure_sups, Set.sups_union_right]

/-- Disjunction distributes over conjunction in a regular domain. -/
theorem regularClosure_union_sups (ht : t.Nonempty) (hu : u.Nonempty) :
    regularClosure (s ∪ t ⊻ u) = regularClosure (s ∪ t) ⊻ regularClosure (s ∪ u) := by
  rw [← regularClosure_sups]
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
