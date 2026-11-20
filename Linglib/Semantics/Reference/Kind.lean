module

public import Linglib.Semantics.Mereology.Classical
public import Linglib.Semantics.Reference.Iota
public import Mathlib.Basic.PEquiv

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
`s` that has a largest member if it has a member (`Kind.up_down`). Closure under sums gives the
largest member, not closure downward: in a classical mereology `Kind.down` is defined on a
nonempty set that contains its sum, where its value is that sum
(`Kind.down_dom_of_isClassical`), and on a finite nonempty set closed under binary sums
(`Kind.down_dom_of_supClosed`). On the plural of a singular property, `Kind.up ∘ Kind.down`
restores the atoms beneath the pluralities (`Kind.up_down_of_forall_isMin`). ∩ of a singular
property is no kind when no kind is singular wherever it has a value
(`Kind.down_comp_notMem_of_isMin`). Derived kind predication, which applies a predicate of
objects to a kind by quantifying existentially over its instances, is
`Quantifier.Det.some (Kind.up (k s))`.

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
