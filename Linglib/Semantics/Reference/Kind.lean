module

public import Linglib.Semantics.Mereology
public import Linglib.Semantics.Reference.Iota

/-!
# Kinds

Chierchia models a kind as an individual concept: at each situation it picks out the sum of its
instances, and it has no value where it has none. The operator 'down', ∩, takes a property to the
concept of the largest member of its extension at each situation, which is the property's kind
where that concept is a kind, and the operator 'up', ∪, takes a kind to the property of being one
of its instances, the parts of its value. ∩ is ι applied at each situation, and ∪ its partial
inverse, `Set.Iic`.

[∩ undoes ∪](##Kind.down_up), and [∪ undoes ∩](##Kind.up_down) on a property closed downward
wherever ∩ is defined, that is, wherever the property has instances its extension has a largest
member. Closure under sums gives the largest member, not closure downward: over a complete
semilattice ∩ is defined on a property closed under arbitrary sums, so ∪ undoes ∩ on one that is
also closed downward (`Kind.up_down_of_sSup_mem`), and ∩ is defined on a finite property closed
under binary sums (`Kind.down_isSome_of_supClosed`). On the plural of a singular property, ∪∩
restores the [atoms beneath the pluralities](##Kind.up_down_of_forall_atom). ∩ is
[undefined for a singular property](##Kind.down_notMem_of_atom) when no kind is singular wherever
it has a value. Derived kind predication, which applies a predicate of objects to a kind by
quantifying existentially over its instances, is `Quantifier.Det.some (Kind.up k s)`.

## Main definitions

* `Kind.up`: ∪, the instances of a kind at a situation.
* `Kind.down`: ∩, the concept of the largest member of a property's extension.

## Implementation notes

The set of kinds is a parameter `K : Set (S → Option E)` of the theorems that need it, primitive
as in Chierchia. Chierchia states (17c) with AT_P "the set that generates P under PL", which is
read here as the atoms beneath members of `P`. Read as the singular property whose plural `P`
is, (17c) fails at a situation with exactly one instance, where the plural has no member and ∩
no value (`Studies/Chierchia1998.lean`).

## References

* [chierchia-1998]
-/

@[expose] public section

namespace Kind

open Mereology

variable {S E : Type*} {P F : S → Set E} {k : S → Option E} {s : S} {d x : E}

section Preorder

variable [Preorder E]

/-- ∪: the instances of a kind at a situation are the parts of its value there, and there are none
where it has no value. -/
def up (k : S → Option E) (s : S) : Set E := (k s).elim ∅ Set.Iic

theorem up_apply_of_eq_some (h : k s = some d) : up k s = Set.Iic d := by simp [up, h]

theorem up_apply_of_eq_none (h : k s = none) : up k s = ∅ := by simp [up, h]

theorem mem_up : x ∈ up k s ↔ ∃ d ∈ k s, x ≤ d := by
  cases h : k s <;> simp [up_apply_of_eq_some, up_apply_of_eq_none, h]

end Preorder

/-- ∩: the concept of the largest member of a property's extension at each situation, which is the
property's kind where it is a kind. -/
noncomputable def down [LE E] (P : S → Set E) (s : S) : Option E := iota (IsGreatest (P s))

section PartialOrder

variable [PartialOrder E]

theorem down_eq_some_iff : down P s = some d ↔ IsGreatest (P s) d :=
  iota_isGreatest_eq_some_iff

theorem down_isSome_iff : (down P s).isSome ↔ ∃ d, IsGreatest (P s) d :=
  iota_isGreatest_isSome_iff

theorem down_eq_none_iff : down P s = none ↔ ¬ ∃ d, IsGreatest (P s) d :=
  iota_isGreatest_eq_none_iff

/-- ∩∪d = d, Chierchia's (17a). -/
theorem down_up (k : S → Option E) : down (up k) = k :=
  funext fun s ↦ iota_isGreatest_elim_Iic (k s)

/-- ∪∩P = P for a property closed downward wherever ∩P is defined, Chierchia's (17b): wherever
the property has instances, its extension has a largest member. -/
theorem up_down (hP : ∀ s, IsLowerSet (P s)) (hdef : ∀ s, (P s).Nonempty → (down P s).isSome) :
    up (down P) = P :=
  funext fun s ↦ elim_Iic_iota_isGreatest (hP s) fun hne ↦ down_isSome_iff.1 (hdef s hne)

/-- On the plural of a singular property `F`, true of what is not `F` and has only `F`-atoms,
∪∩ adds the atoms beneath the pluralities wherever ∩ is defined, Chierchia's (17c). -/
theorem up_down_of_forall_atom (hF : ∀ s, ∀ x ∈ F s, Atom x)
    (hP : ∀ s x, x ∈ P s ↔ x ∉ F s ∧ ∀ y ≤ x, Atom y → y ∈ F s)
    (hdef : ∀ s, (P s).Nonempty → (down P s).isSome) (s : S) :
    up (down P) s = P s ∪ {a | Atom a ∧ ∃ x ∈ P s, a ≤ x} := by
  rcases (P s).eq_empty_or_nonempty with h0 | hne
  · rw [up_apply_of_eq_none (down_eq_none_iff.2 fun ⟨_, hd⟩ ↦ h0.subset hd.1), h0]
    simp
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.1 (hdef s hne)
  have hgm := down_eq_some_iff.1 hm
  rw [up_apply_of_eq_some hm]
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
theorem down_notMem_of_atom {K : Set (S → Option E)} (hK : ∀ k ∈ K, ¬ ∀ s, ∀ d ∈ k s, Atom d)
    (hP : ∀ s, ∀ x ∈ P s, Atom x) : down P ∉ K :=
  fun h ↦ hK _ h fun s _ hd ↦ hP s _ (down_eq_some_iff.1 hd).1

end PartialOrder

theorem down_isSome_of_supClosed [SemilatticeSup E] (hcum : SupClosed (P s)) (hfin : (P s).Finite)
    (hne : (P s).Nonempty) : (down P s).isSome :=
  hcum.directedOn.iota_isGreatest_isSome hfin hne

theorem up_down_of_sSup_mem [CompleteSemilatticeSup E] (hP : ∀ s, IsLowerSet (P s))
    (hsum : ∀ s, ∀ T ⊆ P s, T.Nonempty → sSup T ∈ P s) : up (down P) = P :=
  up_down hP fun s hne ↦ down_isSome_iff.2
    ⟨sSup (P s), hsum s _ subset_rfl hne, fun _ hx ↦ le_sSup hx⟩

end Kind
