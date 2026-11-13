module

public import Linglib.Semantics.Mereology
public import Linglib.Semantics.Reference.Iota
public import Mathlib.Basic.PEquiv

/-!
# Kinds

Chierchia models a kind as an individual concept: at each situation it picks out the sum of its
instances, and it has no value where it has none. The operator 'down', ∩, takes a property to the
concept of the largest member of its extension at each situation, which is the property's kind
where that concept is a kind, and the operator 'up', ∪, takes a kind to the property of being one
of its instances, the parts of its value. ∩ is ι applied at each situation to the largest
members, and ∪ its partial inverse, `Set.Iic`.

[∩ undoes ∪](##Kind.down_up), and [∪ undoes ∩](##Kind.up_down) on a property closed downward
wherever ∩ is defined, that is, wherever the property has instances its extension has a largest
member. Closure under sums gives the largest member, not closure downward: over a complete
semilattice ∩ is defined on a property closed under arbitrary sums, so ∪ undoes ∩ on one that is
also closed downward (`Kind.up_down_of_sSup_mem`), and ∩ is defined on a finite property closed
under binary sums (`Kind.down_dom_of_supClosed`). On the plural of a singular property, ∪∩
restores the [atoms beneath the pluralities](##Kind.up_down_of_forall_atom). ∩ is
[undefined for a singular property](##Kind.down_notMem_of_atom) when no kind is singular wherever
it has a value. Derived kind predication, which applies a predicate of objects to a kind by
quantifying existentially over its instances, is `Quantifier.Det.some (Kind.up k s)`.

In Chierchia's earlier theory ∩ takes a property to an entity, its correlate, and ∪ takes the
correlate back, a partial equivalence between properties and entities. The Russell property, of
being the correlate of a property one lacks, [has no correlate](##Kind.apply_russell_eq_none), and
the correlate is [no function of the property's extension](##Kind.not_exists_apply_eq_comp).

## Main definitions

* `Kind.up`: ∪, the instances of a kind at a situation.
* `Kind.down`: ∩, the concept of the largest member of a property's extension.

## Implementation notes

The set of kinds is a parameter `K : Set (S → Part E)` of the theorems that need it, primitive
as in Chierchia. Chierchia states (17c) with AT_P "the set that generates P under PL", which is
read here as the atoms beneath members of `P`. Read as the singular property whose plural `P`
is, (17c) fails at a situation with exactly one instance, where the plural has no member and ∩
no value (`Studies/Chierchia1998.lean`).

## References

* [chierchia-1984]
* [chierchia-1998]
* [partee-1987]
-/

@[expose] public section

namespace Kind

open Mereology

variable {S E : Type*} {P F : S → Set E} {k : S → Part E} {s : S} {d x : E}

section Preorder

variable [Preorder E]

/-- ∪: the instances of a kind at a situation are the parts of its value there, and there are none
where it has no value. -/
def up (k : S → Part E) (s : S) : Set E := {x | ∃ d ∈ k s, x ≤ d}

@[simp] theorem mem_up : x ∈ up k s ↔ ∃ d ∈ k s, x ≤ d := Iff.rfl

theorem up_apply_of_mem (h : d ∈ k s) : up k s = Set.Iic d :=
  Set.ext fun _ ↦ ⟨fun ⟨_, hd, hx⟩ ↦ Part.mem_unique hd h ▸ hx, fun hx ↦ ⟨d, h, hx⟩⟩

theorem up_apply_of_not_dom (h : ¬ (k s).Dom) : up k s = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ ⟨_, hd, _⟩ ↦ h (Part.dom_iff_mem.2 ⟨_, hd⟩)

theorem isLowerSet_up : IsLowerSet (up k s) :=
  fun _ _ hba ⟨d, hd, had⟩ ↦ ⟨d, hd, hba.trans had⟩

end Preorder

/-- ∩: the concept of the largest member of a property's extension at each situation, which is the
property's kind where it is a kind. -/
noncomputable def down [LE E] (P : S → Set E) (s : S) : Part E :=
  iota {x | IsGreatest (P s) x}

section PartialOrder

variable [PartialOrder E]

@[simp] theorem mem_down : d ∈ down P s ↔ IsGreatest (P s) d :=
  mem_iota_isGreatest

theorem down_dom : (down P s).Dom ↔ ∃ d, IsGreatest (P s) d :=
  iota_isGreatest_dom

theorem down_eq_none_iff : down P s = Part.none ↔ ¬ ∃ d, IsGreatest (P s) d :=
  iota_isGreatest_eq_none_iff

/-- ∩∪d = d, Chierchia's (17a). -/
theorem down_up (k : S → Part E) : down (up k) = k :=
  funext fun s ↦ Part.ext fun d ↦ mem_down.trans
    ⟨fun ⟨⟨d', hd', hle⟩, hub⟩ ↦ hle.antisymm (hub ⟨d', hd', le_rfl⟩) ▸ hd',
      fun h ↦ ⟨⟨d, h, le_rfl⟩, fun _ ⟨_, hd', hx⟩ ↦ Part.mem_unique hd' h ▸ hx⟩⟩

/-- ∪∩P = P for a property closed downward wherever ∩P is defined, Chierchia's (17b): wherever
the property has instances, its extension has a largest member. -/
theorem up_down (hP : ∀ s, IsLowerSet (P s)) (hdef : ∀ s, (P s).Nonempty → (down P s).Dom) :
    up (down P) = P :=
  funext fun s ↦ Set.ext fun x ↦
    ⟨fun ⟨_, hd, hx⟩ ↦ hP s hx (mem_down.1 hd).1, fun hx ↦
      have ⟨d, hd⟩ := Part.dom_iff_mem.1 (hdef s ⟨x, hx⟩)
      ⟨d, hd, (mem_down.1 hd).2 hx⟩⟩

/-- On the plural of a singular property `F`, true of what is not `F` and has only `F`-atoms,
∪∩ adds the atoms beneath the pluralities wherever ∩ is defined, Chierchia's (17c). -/
theorem up_down_of_forall_atom (hF : ∀ s, ∀ x ∈ F s, Atom x)
    (hP : ∀ s x, x ∈ P s ↔ x ∉ F s ∧ ∀ y ≤ x, Atom y → y ∈ F s)
    (hdef : ∀ s, (P s).Nonempty → (down P s).Dom) (s : S) :
    up (down P) s = P s ∪ {a | Atom a ∧ ∃ x ∈ P s, a ≤ x} := by
  rcases (P s).eq_empty_or_nonempty with h0 | hne
  · rw [up_apply_of_not_dom fun h ↦ (down_dom.1 h).elim fun _ hd ↦ h0.subset hd.1, h0]
    simp
  obtain ⟨m, hm⟩ := Part.dom_iff_mem.1 (hdef s hne)
  have hgm := mem_down.1 hm
  rw [up_apply_of_mem hm]
  ext y
  refine ⟨fun hy ↦ ?_, ?_⟩
  · by_cases ha : Atom y
    · exact .inr ⟨ha, m, hgm.1, hy⟩
    · exact .inl ((hP s y).2 ⟨fun hyF ↦ ha (hF s y hyF),
        fun z hz hza ↦ ((hP s m).1 hgm.1).2 z (hz.trans hy) hza⟩)
  · rintro (hy | ⟨-, x, hx, hyx⟩)
    exacts [hgm.2 hy, hyx.trans (hgm.2 hx)]

/-- ∩ is undefined for a singular property when no kind is singular in every situation where it
has a value: the concept of a singular property is singular wherever it has one. -/
theorem down_notMem_of_atom {K : Set (S → Part E)} (hK : ∀ k ∈ K, ¬ ∀ s, ∀ d ∈ k s, Atom d)
    (hP : ∀ s, ∀ x ∈ P s, Atom x) : down P ∉ K :=
  fun h ↦ hK _ h fun s _ hd ↦ hP s _ (mem_down.1 hd).1

end PartialOrder

theorem down_dom_of_supClosed [SemilatticeSup E] (hcum : SupClosed (P s)) (hfin : (P s).Finite)
    (hne : (P s).Nonempty) : (down P s).Dom :=
  hcum.directedOn.iota_isGreatest_dom hfin hne

theorem up_down_of_sSup_mem [CompleteSemilatticeSup E] (hP : ∀ s, IsLowerSet (P s))
    (hsum : ∀ s, ∀ T ⊆ P s, T.Nonempty → sSup T ∈ P s) : up (down P) = P :=
  up_down hP fun s hne ↦ down_dom.2
    ⟨sSup (P s), hsum s _ subset_rfl hne, fun _ hx ↦ le_sSup hx⟩

/-! ### Kinds as correlates of properties -/

section Correlate

variable (c : (S → Set E) ≃. E)

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
