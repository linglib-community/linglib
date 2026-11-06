module

public import Mathlib.Data.Set.Subsingleton
public import Mathlib.Order.Antichain
public import Mathlib.Order.Preorder.Finite
public import Mathlib.Order.UpperLower.Basic

/-!
# Iota

The iota operator takes a set of individuals to its only member, when it has exactly one: it is
[the partial inverse](##iota_isPartialInv) of the singleton map, Partee's *ident*, which sends an
individual to the property of being it, so `iota s` is [the unique member of
`s`](##iota_eq_some_iff) and `none` when `s` is empty or has several members.

On individuals ordered by part-of, the definite picks out the largest member of a set,
`iota {d | IsGreatest X d}`. On an antichain, such as a set of atoms, [the largest member is the
only member](##IsAntichain.iota_isGreatest). On a lower set, such as the extension of a mass noun,
taking the largest member is [the partial inverse of `Set.Iic`](##IsLowerSet.iota_isGreatest),
which sends an individual to its parts, and a finite nonempty directed set [has a largest
member](##DirectedOn.iota_isGreatest_isSome).

## Implementation notes

Partee pairs *ident*, total and injective, with *iota*, its partial surjective inverse; a partial
individual is accordingly an `Option`, as `Function.partialInv` returns. Her properties are sets,
as are the restrictors and scopes of `Quantifier`, so *ident* is the singleton `{j}` and needs no
name of its own. The definedness of `iota s` is unique existence (`iota_isSome_iff`): the
existence and uniqueness of a member, which Coppock and Beaver separate, the article presupposing
uniqueness and existence coming from the type shift that makes a description an argument. Sharvy
generalizes the article to individuals ordered by part-of, and Chierchia adopts the
generalization; Krifka, following Link, writes σ for the largest member and defines it as
ιx[S(x) ∧ ∀x′[S(x′) → x′ ⊑ x]], which is `iota {d | IsGreatest X d}`.

## References

* [russell-1905]
* [partee-1987]
* [coppock-beaver-2015]
* [sharvy-1980]
* [chierchia-1998]
* [link-1983]
* [krifka-2026]
-/

@[expose] public section

variable {E : Type*} {s : Set E} {e : E}

/-- `iota s` is the only member of `s`, the partial inverse of `{·}`. -/
noncomputable def iota : Set E → Option E :=
  Function.partialInv ({·} : E → Set E)

theorem iota_isPartialInv : Function.IsPartialInv ({·} : E → Set E) iota :=
  Set.singleton_injective.isPartialInv

@[simp] theorem iota_singleton (j : E) : iota {j} = some j :=
  Function.partialInv_left Set.singleton_injective j

theorem iota_eq_some_iff : iota s = some e ↔ e ∈ s ∧ ∀ x ∈ s, x = e :=
  (iota_isPartialInv e s).trans <| eq_comm.trans Set.eq_singleton_iff_unique_mem

theorem iota_isSome_iff : (iota s).isSome ↔ ∃! x, x ∈ s :=
  Option.isSome_iff_exists.trans <| exists_congr fun _ ↦ iota_eq_some_iff

theorem iota_eq_none_iff : iota s = none ↔ ¬ ∃! x, x ∈ s := by
  rw [← Option.not_isSome_iff_eq_none, iota_isSome_iff]

theorem iota_eq_none_of_ne {e' : E} (he : e ∈ s) (he' : e' ∈ s) (hne : e ≠ e') : iota s = none :=
  iota_eq_none_iff.2 fun h ↦ hne (h.unique he he')

/-! ### Sets with at most one member -/

section Subsingleton

theorem Set.Subsingleton.iota_eq_some_iff (h : s.Subsingleton) : iota s = some e ↔ e ∈ s :=
  _root_.iota_eq_some_iff.trans ⟨And.left, fun he ↦ ⟨he, fun _ hx ↦ h hx he⟩⟩

theorem Set.Subsingleton.iota_isSome_iff (h : s.Subsingleton) : (iota s).isSome ↔ s.Nonempty :=
  _root_.iota_isSome_iff.trans
    ⟨fun ⟨x, hx, _⟩ ↦ ⟨x, hx⟩, fun ⟨x, hx⟩ ↦ ⟨x, hx, fun _ hy ↦ h hy hx⟩⟩

end Subsingleton

/-! ### The largest member -/

section Order

variable [PartialOrder E] {X : Set E} {d : E}

theorem iota_isGreatest_eq_some_iff : iota {x | IsGreatest X x} = some d ↔ IsGreatest X d :=
  Set.Subsingleton.iota_eq_some_iff fun _ ha _ hb ↦ ha.unique hb

theorem iota_isGreatest_isSome_iff :
    (iota {x | IsGreatest X x}).isSome ↔ ∃ d, IsGreatest X d :=
  Set.Subsingleton.iota_isSome_iff fun _ ha _ hb ↦ ha.unique hb

theorem iota_isGreatest_eq_none_iff :
    iota {x | IsGreatest X x} = none ↔ ¬ ∃ d, IsGreatest X d := by
  rw [← Option.not_isSome_iff_eq_none, iota_isGreatest_isSome_iff]

theorem iota_isGreatest_Iic : iota {x | IsGreatest (Set.Iic d) x} = some d :=
  iota_isGreatest_eq_some_iff.2 isGreatest_Iic

theorem iota_isGreatest_empty : iota {x | IsGreatest (∅ : Set E) x} = none :=
  iota_isGreatest_eq_none_iff.2 fun ⟨_, h, _⟩ ↦ h

theorem iota_isGreatest_elim_Iic (o : Option E) :
    iota {x | IsGreatest (o.elim ∅ Set.Iic) x} = o := by
  cases o
  exacts [iota_isGreatest_empty, iota_isGreatest_Iic]

theorem IsLowerSet.iota_isGreatest (hX : IsLowerSet X) :
    iota {x | IsGreatest X x} = Function.partialInv Set.Iic X :=
  Option.ext fun d ↦ iota_isGreatest_eq_some_iff.trans <|
    (⟨fun hd ↦ (hX.Iic_subset hd.1).antisymm hd.2, (· ▸ isGreatest_Iic)⟩ :
      IsGreatest X d ↔ Set.Iic d = X).trans (Set.Iic_injective.isPartialInv d X).symm

theorem elim_Iic_iota_isGreatest (hX : IsLowerSet X) (hd : X.Nonempty → ∃ d, IsGreatest X d) :
    (iota {x | IsGreatest X x}).elim ∅ Set.Iic = X := by
  rcases X.eq_empty_or_nonempty with rfl | hne
  · rw [iota_isGreatest_empty]
    rfl
  · obtain ⟨d, hd⟩ := hd hne
    rw [iota_isGreatest_eq_some_iff.2 hd]
    exact (hX.Iic_subset hd.1).antisymm hd.2

theorem IsAntichain.iota_isGreatest (hs : IsAntichain (· ≤ ·) X) :
    iota {x | IsGreatest X x} = iota X :=
  Option.ext fun _ ↦ (iota_isGreatest_eq_some_iff.trans <|
    hs.greatest_iff.trans Set.eq_singleton_iff_unique_mem).trans iota_eq_some_iff.symm

theorem IsAntichain.iota_isGreatest_eq_none (hs : IsAntichain (· ≤ ·) X) {a b : E}
    (ha : a ∈ X) (hb : b ∈ X) (hab : a ≠ b) : iota {x | IsGreatest X x} = none :=
  iota_isGreatest_eq_none_iff.2 fun ⟨_, hd⟩ ↦ by
    rw [hs.greatest_iff.1 hd] at ha hb
    exact hab (ha.trans hb.symm)

theorem DirectedOn.iota_isGreatest_isSome (hs : DirectedOn (· ≤ ·) X) (hfin : X.Finite)
    (hne : X.Nonempty) : (iota {x | IsGreatest X x}).isSome :=
  let ⟨m, hm⟩ := hfin.exists_maximal hne
  iota_isGreatest_isSome_iff.2
    ⟨m, hm.prop, hs.is_top_of_is_max hm.prop fun _ ha ↦ hm.le_of_ge ha⟩

end Order
