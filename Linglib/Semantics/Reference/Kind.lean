module

public import Linglib.Semantics.Mereology.Classical
public import Linglib.Semantics.Reference.Description
public import Linglib.Semantics.Reference.Iota
public import Mathlib.Basic.PEquiv
public import Mathlib.Order.UpperLower.Closure

/-!
# Kinds

Chierchia models a kind as an individual concept: at each situation it picks out the sum of its
instances, and it has no value where it has none. Both of his operators act on the value at one
situation. For a set `s` of individuals ordered by part-of, `Kind.down s` is the largest member
of `s`, a partial individual, and for a partial individual `k`, `Kind.up k` is the set of parts
of `k`, empty where `k` has no value. So `Kind.down s = iota {x | IsGreatest s x}`, and
`Kind.up` is `Set.Iic` on the individuals that exist. The operator 'down', ∩, of a property
`P : S → Set E` is `Kind.down ∘ P`, which is the property's kind where that concept is a kind,
and the operator 'up', ∪, of a kind `k : S → Part E` is `Kind.up ∘ k`.

`Kind.down (Kind.up k) = k` (`Kind.down_up`), and `Kind.up (Kind.down s) = s` for a lower set
`s` that has a largest member if it has a member (`Kind.up_down`), and for no other set
(`Kind.up_down_eq_iff`), so the two are inverse bijections between partial individuals and such
sets (`Kind.upEquiv`). On the sets with a largest member `Kind.down` is left adjoint to `Kind.up`:
its value is part of `e` iff the set is included in the parts of `e` (`Kind.le_iff_subset_up`).
The largest member is the sum of the set where the set contains its sum
(`Kind.down_dom_iff_sSup_mem`), so the adjunction is the one between `sSup` and `Set.Iic`, cut
down to the sets on which the sum is attained. Closure under sums gives the
largest member, not closure downward: in a classical mereology `Kind.down` is defined on a
nonempty set that contains its sum, where its value is that sum
(`Kind.down_dom_of_isClassical`), and on a finite nonempty set closed under binary sums
(`Kind.down_dom_of_supClosed`). On the plural of a singular property, `Kind.up ∘ Kind.down`
restores the atoms beneath the pluralities (`Kind.up_down_of_forall_isMin`). ∩ of a singular
property is no kind when no kind is singular wherever it has a value
(`Kind.down_comp_notMem_of_isMin`). Derived kind predication, which applies a predicate of
objects to a kind by quantifying existentially over its instances, is
`Quantifier.Det.some (Kind.up (k s))`, which holds of a predicate iff the value of the kind is
in the predicate's upper closure (`Kind.inter_up_nonempty_iff`).

In Chierchia's earlier theory ∩ takes a property to an entity, its correlate, and ∪ takes the
correlate back, a partial equivalence between properties and entities. The Russell property, of
being the correlate of a property one lacks, has no correlate (`Kind.apply_russell_eq_none`),
and the correlate is no function of the property's extension
(`Kind.not_exists_apply_eq_comp`).

## Implementation notes

The operators take the extension and the value at one situation, not a property and a concept
with the situation as a further argument: the value of ∩ at a situation depends on the
property's extension there alone. The set of kinds is a parameter `K : Set (S → Part E)` of the
theorems that need it, primitive as in Chierchia. Chierchia states (17c) with AT_P "the set that
generates P under PL", which is read here as the atoms beneath members of `P`. Read as the
singular property whose plural `P` is, (17c) fails at a situation with exactly one instance,
where the plural has no member and ∩ no value (`Studies/Chierchia1998.lean`).

## References

* [chierchia-1984]
* [chierchia-1998]
* [partee-1987]
-/

@[expose] public section

namespace Kind

open Mereology

variable {S E : Type*} {s t : Set E} {k : Part E} {d x : E}

section Preorder

variable [Preorder E]

/-- ∪: the instances of a kind at a situation are the parts of its value there, and there are none
where it has no value. -/
def up (k : Part E) : Set E := {x | ∃ d ∈ k, x ≤ d}

@[simp] theorem mem_up : x ∈ up k ↔ ∃ d ∈ k, x ≤ d := Iff.rfl

theorem up_of_mem (h : d ∈ k) : up k = Set.Iic d :=
  Set.ext fun _ ↦ ⟨fun ⟨_, hd, hx⟩ ↦ Part.mem_unique hd h ▸ hx, fun hx ↦ ⟨d, h, hx⟩⟩

@[simp] theorem up_some (d : E) : up (Part.some d) = Set.Iic d := up_of_mem (Part.mem_some d)

theorem up_of_not_dom (h : ¬ k.Dom) : up k = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ ⟨_, hd, _⟩ ↦ h (Part.dom_iff_mem.2 ⟨_, hd⟩)

@[simp] theorem up_none : up (Part.none : Part E) = ∅ := up_of_not_dom id

theorem isLowerSet_up : IsLowerSet (up k) :=
  fun _ _ hba ⟨d, hd, had⟩ ↦ ⟨d, hd, hba.trans had⟩

/-- A set has a member among the instances of a kind iff the value of the kind is in its upper
closure: derived kind predication extends a predicate of objects to its upper closure. -/
theorem inter_up_nonempty_iff {V : Set E} :
    (up k ∩ V).Nonempty ↔ ∃ d ∈ k, d ∈ upperClosure V :=
  ⟨fun ⟨x, ⟨d, hd, hx⟩, hV⟩ ↦ ⟨d, hd, mem_upperClosure.2 ⟨x, hV, hx⟩⟩,
    fun ⟨d, hd, h⟩ ↦ let ⟨x, hV, hx⟩ := mem_upperClosure.1 h; ⟨x, ⟨d, hd, hx⟩, hV⟩⟩

end Preorder

/-- ∩: the largest member of the extension of a property at a situation, the value there of the
property's kind where it has one. -/
noncomputable def down [LE E] (s : Set E) : Part E :=
  iota {x | IsGreatest s x}

section PartialOrder

variable [PartialOrder E]

@[simp] theorem mem_down : d ∈ down s ↔ IsGreatest s d :=
  mem_iota_isGreatest

theorem down_dom : (down s).Dom ↔ ∃ d, IsGreatest s d :=
  iota_isGreatest_dom

theorem down_eq_none_iff : down s = Part.none ↔ ¬ ∃ d, IsGreatest s d :=
  iota_isGreatest_eq_none_iff

/-- ∩∪d = d, Chierchia's (17a). -/
@[simp] theorem down_up (k : Part E) : down (up k) = k :=
  Part.ext fun d ↦ mem_down.trans
    ⟨fun ⟨⟨d', hd', hle⟩, hub⟩ ↦ hle.antisymm (hub ⟨d', hd', le_rfl⟩) ▸ hd',
      fun h ↦ ⟨⟨d, h, le_rfl⟩, fun _ ⟨_, hd', hx⟩ ↦ Part.mem_unique hd' h ▸ hx⟩⟩

theorem up_injective : Function.Injective (up : Part E → Set E) :=
  Function.LeftInverse.injective down_up

/-- ∪∩P = P at a situation where the extension is closed downward and ∩P is defined if there
are instances, Chierchia's (17b). -/
theorem up_down (hs : IsLowerSet s) (hdef : s.Nonempty → (down s).Dom) : up (down s) = s :=
  Set.ext fun x ↦
    ⟨fun ⟨_, hd, hx⟩ ↦ hs hx (mem_down.1 hd).1, fun hx ↦
      have ⟨d, hd⟩ := Part.dom_iff_mem.1 (hdef ⟨x, hx⟩)
      ⟨d, hd, (mem_down.1 hd).2 hx⟩⟩

/-- ∩ is left adjoint to ∪ on the sets with a largest member: the value of ∩ is part of `e` iff
every member of the set is. -/
theorem le_iff_subset_up {e : E} (hd : d ∈ down s) : d ≤ e ↔ s ⊆ up (Part.some e) := by
  rw [up_some]
  exact ⟨fun h _ hx ↦ ((mem_down.1 hd).2 hx).trans h, fun h ↦ h (mem_down.1 hd).1⟩

/-- A set with a largest member is included in ∪∩ of it, the lower set its largest member
generates. -/
theorem subset_up_down (h : (down s).Dom) : s ⊆ up (down s) := fun _ hx ↦
  let ⟨d, hd⟩ := Part.dom_iff_mem.1 h
  ⟨d, hd, (mem_down.1 hd).2 hx⟩

/-- ∪∩ fixes exactly the sets closed downward that have a largest member if they have a
member. -/
theorem up_down_eq_iff : up (down s) = s ↔ IsLowerSet s ∧ (s.Nonempty → (down s).Dom) :=
  ⟨fun h ↦ ⟨h ▸ isLowerSet_up (k := down s), fun ⟨x, hx⟩ ↦ by
      rw [← h] at hx
      obtain ⟨d, hd, -⟩ := hx
      exact Part.dom_iff_mem.2 ⟨d, hd⟩⟩,
    fun h ↦ up_down h.1 h.2⟩

/-- On the plural `s` of a singular property with extension `t`, true of what is not in `t` and
has only atoms of `t`, ∪∩ adds the atoms beneath the pluralities where ∩ is defined, Chierchia's
(17c). -/
theorem up_down_of_forall_isMin (ht : ∀ x ∈ t, IsMin x)
    (hs : ∀ x, x ∈ s ↔ x ∉ t ∧ ∀ y ≤ x, IsMin y → y ∈ t)
    (hdef : s.Nonempty → (down s).Dom) :
    up (down s) = s ∪ {a | IsMin a ∧ ∃ x ∈ s, a ≤ x} := by
  rcases s.eq_empty_or_nonempty with h0 | hne
  · rw [up_of_not_dom fun h ↦ (down_dom.1 h).elim fun _ hd ↦ h0.subset hd.1, h0]
    simp
  obtain ⟨m, hm⟩ := Part.dom_iff_mem.1 (hdef hne)
  have hgm := mem_down.1 hm
  rw [up_of_mem hm]
  ext y
  refine ⟨fun hy ↦ ?_, ?_⟩
  · by_cases ha : IsMin y
    · exact .inr ⟨ha, m, hgm.1, hy⟩
    · exact .inl ((hs y).2 ⟨fun hyt ↦ ha (ht y hyt),
        fun z hz hza ↦ ((hs m).1 hgm.1).2 z (hz.trans hy) hza⟩)
  · rintro (hy | ⟨-, x, hx, hyx⟩)
    exacts [hgm.2 hy, hyx.trans (hgm.2 hx)]

/-- ∩ of a singular property is no kind when no kind is singular in every situation where it
has a value: the concept of a singular property is singular wherever it has one. -/
theorem down_comp_notMem_of_isMin {K : Set (S → Part E)} {P : S → Set E}
    (hK : ∀ k ∈ K, ¬ ∀ s, ∀ d ∈ k s, IsMin d) (hP : ∀ s, ∀ x ∈ P s, IsMin x) : down ∘ P ∉ K :=
  fun h ↦ hK _ h fun s _ hd ↦ hP s _ (mem_down.1 hd).1

end PartialOrder

theorem down_dom_of_supClosed [SemilatticeSup E] (hcum : SupClosed s) (hfin : s.Finite)
    (hne : s.Nonempty) : (down s).Dom :=
  hcum.directedOn.iota_isGreatest_dom hfin hne

section CompleteSemilatticeSup

variable {L : Type*} [CompleteSemilatticeSup L] {s : Set L} {d : L}

/-- Where every set has a sum, ∩ is defined on the sets that contain their sum. -/
theorem down_dom_iff_sSup_mem : (down s).Dom ↔ sSup s ∈ s :=
  down_dom.trans ⟨fun ⟨_, hd⟩ ↦ hd.isLUB.sSup_eq ▸ hd.1, fun h ↦ ⟨_, h, fun _ ↦ le_sSup⟩⟩

/-- The value of ∩ is the sum of the set. -/
theorem eq_sSup_of_mem_down (h : d ∈ down s) : d = sSup s :=
  (mem_down.1 h).isLUB.sSup_eq.symm

end CompleteSemilatticeSup

section Classical

variable [PartialOrder E]

/-- In a classical mereology ∩ is defined on a nonempty extension that contains its sum, and
its value is that sum. -/
theorem down_dom_of_isClassical (h : IsClassical E) (hsum : ∀ ⦃x⦄, IsLUB s x → x ∈ s)
    (hne : s.Nonempty) : (down s).Dom :=
  let ⟨x, hx⟩ := h.exists_isLUB s hne
  Part.dom_iff_mem.2 ⟨x, mem_down.2 ⟨hsum hx, hx.1⟩⟩

/-- ∪∩P = P at a situation where the extension is closed downward and contains its sum,
whatever its size. -/
theorem up_down_of_isClassical (h : IsClassical E) (hs : IsLowerSet s)
    (hsum : ∀ ⦃x⦄, IsLUB s x → x ∈ s) : up (down s) = s :=
  up_down hs (down_dom_of_isClassical h hsum)

end Classical

/-! ### ∪ and ∩ as inverse bijections -/

section Equiv

variable [PartialOrder E]

/-- ∪ and ∩ are inverse bijections between the partial individuals and the sets closed downward
that have a largest member if they have a member, Chierchia's (17a) and (17b). -/
noncomputable def upEquiv :
    Part E ≃ {s : Set E // IsLowerSet s ∧ (s.Nonempty → ∃ d, IsGreatest s d)} where
  toFun k := ⟨up k, isLowerSet_up, fun ⟨_, d, hd, _⟩ ↦
    ⟨d, ⟨d, hd, le_rfl⟩, fun _ ⟨_, hd', h⟩ ↦ Part.mem_unique hd' hd ▸ h⟩⟩
  invFun s := down s.1
  left_inv := down_up
  right_inv s := Subtype.ext (up_down s.2.1 fun h ↦ down_dom.2 (s.2.2 h))

@[simp] theorem coe_upEquiv (k : Part E) : (upEquiv k : Set E) = up k := rfl

@[simp] theorem upEquiv_symm_apply
    (s : {s : Set E // IsLowerSet s ∧ (s.Nonempty → ∃ d, IsGreatest s d)}) :
    upEquiv.symm s = down s.1 := rfl

/-- ∩ at a situation is the maximal definite: ∩ is the definite shift ι taken at each situation,
and differs from it in being defined only where the resulting concept is a kind. -/
theorem down_eq_maximal {Ctx W : Type*} (R : Ctx → W → Set E) (c : Ctx) (s : W) :
    down (R c s) = Definite.maximal R c s := rfl

end Equiv

/-! ### Kinds as correlates of properties -/

section Correlate

variable {P : S → Set E} {s : S} (c : (S → Set E) ≃. E)

/-- The Russell property of a pairing of properties with correlates: at each situation, being the
correlate of a property one lacks there. -/
def russell : S → Set E := fun s ↦ {x | ∃ P ∈ c.symm x, x ∉ P s}

/-- The Russell property has no correlate, so ∩ is only almost total ([partee-1987], §3.1). -/
theorem apply_russell_eq_none [Nonempty S] : c (russell c) = none := by
  refine Option.eq_none_iff_forall_ne_some.2 fun r h ↦ ?_
  have hr : c.symm r = some (russell c) := c.eq_some_iff.2 h
  obtain ⟨s⟩ := ‹Nonempty S›
  exact iff_not_self (a := r ∈ russell c s)
    ⟨fun ⟨_, hP, hrP⟩ ↦ (Option.some_injective _ (hr.symm.trans hP)) ▸ hrP, fun h ↦ ⟨_, hr, h⟩⟩

/-- The correlate is no function of the extension at a situation: where ∩ is defined on a property,
a different property with the same extension there defeats any such function, which is why
[partee-1987] calls an extensional ∩ a misrepresentation (§3.1). -/
theorem not_exists_apply_eq_comp {P' : S → Set E} (hs : P s = P' s) (hne : P ≠ P')
    (hx : c P = some x) : ¬ ∃ f : Set E → Option E, ∀ Q, c Q = f (Q s) := fun ⟨f, hf⟩ ↦
  hne <| c.inj hx <| by rw [hf P', ← hs, ← hf P]; exact hx

end Correlate

end Kind
