module

public import Mathlib.Data.Part
public import Mathlib.Data.Set.Subsingleton
public import Mathlib.Order.Antichain
public import Mathlib.Order.Preorder.Finite
public import Mathlib.Order.UpperLower.Basic

/-!
# Iota

The iota operator takes a set of individuals to its only member, when it has exactly one: it is
[the partial inverse](##mem_iota_iff_eq_singleton) of the singleton map, Partee's *ident*, which
sends an individual to the property of being it, so `iota s` is [the unique member of
`s`](##mem_iota) and is undefined when `s` is empty or has several members.

On individuals ordered by part-of, the definite picks out the largest member of a set,
`iota {d | IsGreatest X d}`. On an antichain, such as a set of atoms, [the largest member is the
only member](##IsAntichain.iota_isGreatest). On a lower set, such as the extension of a mass noun,
taking the largest member is [the partial inverse of `Set.Iic`](##IsLowerSet.mem_iota_isGreatest),
which sends an individual to its parts, and a finite nonempty directed set [has a largest
member](##DirectedOn.iota_isGreatest_dom).

## Implementation notes

Partee pairs *ident*, total and injective, with *iota*, its partial surjective inverse. A partial
individual is a `Part`, whose domain is the proposition that the individual exists, so the
definedness of `iota s` is unique existence by definition (`iota_dom`): the existence and
uniqueness of a member, which Coppock and Beaver separate, the article presupposing uniqueness and
existence coming from the type shift that makes a description an argument. Her properties are
sets, as are the restrictors and scopes of `Quantifier`, so *ident* is the singleton `{j}` and
needs no name of its own. Sharvy generalizes the article to individuals ordered by part-of, and
Chierchia adopts the generalization; Krifka, following Link, writes σ for the largest member and
defines it as ιx[S(x) ∧ ∀x′[S(x′) → x′ ⊑ x]], which is `iota {d | IsGreatest X d}`. Winter factors
σ the same way, as a choice function on singletons, here `iota`, after *sup*, which sends a set to
its members that bound it, `{d | IsGreatest X d}`, that is `X ∩ upperBounds X`; Bale and Khanjian
put the two on different heads.

## References

* [russell-1905]
* [partee-1987]
* [coppock-beaver-2015]
* [sharvy-1980]
* [chierchia-1998]
* [link-1983]
* [krifka-2026]
* [winter-2001b]
* [bale-khanjian-2014]
-/

@[expose] public section

variable {E : Type*} {s : Set E} {e : E}

/-- `iota s` is the only member of `s`, defined when `s` has exactly one. -/
noncomputable def iota (s : Set E) : Part E := ⟨∃! x, x ∈ s, fun h ↦ h.choose⟩

theorem iota_dom : (iota s).Dom ↔ ∃! x, x ∈ s := Iff.rfl

@[simp] theorem mem_iota : e ∈ iota s ↔ e ∈ s ∧ ∀ x ∈ s, x = e :=
  ⟨fun ⟨h, he⟩ ↦ he ▸ h.choose_spec, fun h ↦
    have hu : ∃! x, x ∈ s := ⟨e, h⟩
    ⟨hu, h.2 _ hu.choose_spec.1⟩⟩

/-- `iota` is the partial inverse of the singleton map: it denotes `e` exactly at `{e}`. -/
theorem mem_iota_iff_eq_singleton : e ∈ iota s ↔ s = {e} :=
  mem_iota.trans Set.eq_singleton_iff_unique_mem.symm

@[simp] theorem iota_singleton (j : E) : iota {j} = Part.some j :=
  Part.eq_some_iff.2 (mem_iota_iff_eq_singleton.2 rfl)

theorem iota_eq_none_iff : iota s = Part.none ↔ ¬ ∃! x, x ∈ s := Part.eq_none_iff'

theorem iota_eq_none_of_ne {e' : E} (he : e ∈ s) (he' : e' ∈ s) (hne : e ≠ e') :
    iota s = Part.none :=
  iota_eq_none_iff.2 fun h ↦ hne (h.unique he he')

/-! ### Sets with at most one member -/

section Subsingleton

theorem Set.Subsingleton.mem_iota (h : s.Subsingleton) : e ∈ iota s ↔ e ∈ s :=
  _root_.mem_iota.trans ⟨And.left, fun he ↦ ⟨he, fun _ hx ↦ h hx he⟩⟩

theorem Set.Subsingleton.iota_dom (h : s.Subsingleton) : (iota s).Dom ↔ s.Nonempty :=
  _root_.iota_dom.trans
    ⟨fun ⟨x, hx, _⟩ ↦ ⟨x, hx⟩, fun ⟨x, hx⟩ ↦ ⟨x, hx, fun _ hy ↦ h hy hx⟩⟩

end Subsingleton

/-! ### The largest member -/

section Order

variable [PartialOrder E] {X : Set E} {d : E}

@[simp] theorem mem_iota_isGreatest : d ∈ iota {x | IsGreatest X x} ↔ IsGreatest X d :=
  Set.Subsingleton.mem_iota fun _ ha _ hb ↦ ha.unique hb

theorem iota_isGreatest_dom : (iota {x | IsGreatest X x}).Dom ↔ ∃ d, IsGreatest X d :=
  Set.Subsingleton.iota_dom fun _ ha _ hb ↦ ha.unique hb

theorem iota_isGreatest_eq_none_iff :
    iota {x | IsGreatest X x} = Part.none ↔ ¬ ∃ d, IsGreatest X d := by
  rw [Part.eq_none_iff', iota_isGreatest_dom]

theorem iota_isGreatest_Iic : iota {x | IsGreatest (Set.Iic d) x} = Part.some d :=
  Part.eq_some_iff.2 (mem_iota_isGreatest.2 isGreatest_Iic)

theorem iota_isGreatest_empty : iota {x | IsGreatest (∅ : Set E) x} = Part.none :=
  iota_isGreatest_eq_none_iff.2 fun ⟨_, h, _⟩ ↦ h

/-- On a lower set, the largest member is the partial inverse of `Set.Iic`. -/
theorem IsLowerSet.mem_iota_isGreatest (hX : IsLowerSet X) :
    d ∈ iota {x | IsGreatest X x} ↔ Set.Iic d = X :=
  _root_.mem_iota_isGreatest.trans
    ⟨fun hd ↦ (hX.Iic_subset hd.1).antisymm hd.2, (· ▸ isGreatest_Iic)⟩

theorem IsAntichain.iota_isGreatest (hs : IsAntichain (· ≤ ·) X) :
    iota {x | IsGreatest X x} = iota X :=
  Part.ext fun _ ↦ (_root_.mem_iota_isGreatest.trans <|
    hs.greatest_iff.trans Set.eq_singleton_iff_unique_mem).trans _root_.mem_iota.symm

theorem IsAntichain.iota_isGreatest_eq_none (hs : IsAntichain (· ≤ ·) X) {a b : E}
    (ha : a ∈ X) (hb : b ∈ X) (hab : a ≠ b) : iota {x | IsGreatest X x} = Part.none :=
  iota_isGreatest_eq_none_iff.2 fun ⟨_, hd⟩ ↦ by
    rw [hs.greatest_iff.1 hd] at ha hb
    exact hab (ha.trans hb.symm)

theorem DirectedOn.iota_isGreatest_dom (hs : DirectedOn (· ≤ ·) X) (hfin : X.Finite)
    (hne : X.Nonempty) : (iota {x | IsGreatest X x}).Dom :=
  let ⟨m, hm⟩ := hfin.exists_maximal hne
  _root_.iota_isGreatest_dom.2
    ⟨m, hm.prop, hs.is_top_of_is_max hm.prop fun _ ha ↦ hm.le_of_ge ha⟩

end Order
