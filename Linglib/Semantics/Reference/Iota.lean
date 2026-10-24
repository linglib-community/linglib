module

public import Mathlib.Data.Set.Subsingleton
public import Mathlib.Order.Antichain
public import Mathlib.Order.Preorder.Finite
public import Mathlib.Order.UpperLower.Basic

/-!
# Iota

The iota operator takes a predicate to the individual it describes, when there is one. It is the
partial inverse of `ident`, which sends an individual to its singleton property, so `iota P` is
the unique satisfier of `P`, and `none` when `P` has no satisfier or several.

On individuals ordered by part-of, the definite picks out the largest member of a set,
`iota (IsGreatest X)`. On an antichain, such as a set of atoms, the largest member is the only
member. On a lower set, such as the extension of a mass noun, taking the largest member is the
partial inverse of `Set.Iic`, which sends an individual to its parts.

## Main definitions

* `ident`: the singleton property of an individual.
* `iota`: the partial inverse of `ident`.

## Main statements

* `iota_isPartialInv`: `iota P = some e` exactly when `P` is `ident e`.
* `iota_eq_some_iff`: `iota P` is the unique satisfier of `P`.
* `IsAntichain.iota_isGreatest`: on an antichain the largest member is the unique member.
* `IsLowerSet.iota_isGreatest`: on a lower set the largest member is the partial inverse of
  `Set.Iic`.
* `DirectedOn.iota_isGreatest_isSome`: a finite nonempty directed set has a largest member.

## Implementation notes

Partee pairs *ident*, total and injective, with *iota*, its partial surjective inverse; a partial
individual is accordingly an `Option`, as `Function.partialInv` returns. The definedness of
`iota P` is unique existence (`iota_isSome_iff`): the existence and uniqueness of a satisfier,
which Coppock and Beaver separate, the article presupposing uniqueness and existence coming from
the type shift that makes a description an argument. Sharvy generalizes the article to
individuals ordered by part-of, and Chierchia adopts the generalization; Krifka, following Link,
writes σ for the largest member and defines it as ιx[S(x) ∧ ∀x′[S(x′) → x′ ⊑ x]], which is
`iota (IsGreatest X)`.

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

variable {E : Type*} (P : E → Prop) {e : E}

/-- `ident j` is the singleton property of `j`. -/
def ident (j : E) : E → Prop := (· = j)

theorem ident_injective : Function.Injective (ident (E := E)) :=
  fun a _ h ↦ (congrFun h a).mp rfl

/-- `iota P` is the unique satisfier of `P`, the partial inverse of `ident`. -/
noncomputable def iota : (E → Prop) → Option E :=
  Function.partialInv ident

theorem iota_isPartialInv : Function.IsPartialInv ident (iota (E := E)) :=
  ident_injective.isPartialInv

theorem iota_ident (j : E) : iota (ident j) = some j :=
  Function.partialInv_left ident_injective j

theorem iota_eq_some_iff : iota P = some e ↔ P e ∧ ∀ x, P x → x = e :=
  (iota_isPartialInv e P).trans
    ⟨fun h ↦ h ▸ ⟨rfl, fun _ ↦ id⟩, fun h ↦ funext fun x ↦ propext ⟨(· ▸ h.1), h.2 x⟩⟩

theorem iota_isSome_iff : (iota P).isSome ↔ ∃! x, P x :=
  Option.isSome_iff_exists.trans <| exists_congr fun _ ↦ iota_eq_some_iff P

theorem iota_eq_none_iff : iota P = none ↔ ¬ ∃! x, P x := by
  rw [← Option.not_isSome_iff_eq_none, iota_isSome_iff]

theorem iota_eq_none_of_ne {e' : E} (he : P e) (he' : P e') (hne : e ≠ e') : iota P = none :=
  (iota_eq_none_iff P).2 fun h ↦ hne (h.unique he he')

/-! ### Predicates with at most one satisfier -/

section Subsingleton

variable {P}

theorem Set.Subsingleton.iota_eq_some_iff (h : {x | P x}.Subsingleton) :
    iota P = some e ↔ P e :=
  (_root_.iota_eq_some_iff P).trans ⟨And.left, fun he ↦ ⟨he, fun _ hx ↦ h hx he⟩⟩

theorem Set.Subsingleton.iota_isSome_iff (h : {x | P x}.Subsingleton) :
    (iota P).isSome ↔ ∃ x, P x :=
  (_root_.iota_isSome_iff P).trans
    ⟨ExistsUnique.exists, fun ⟨x, hx⟩ ↦ ⟨x, hx, fun _ hy ↦ h hy hx⟩⟩

end Subsingleton

/-! ### The largest member -/

section Order

variable [PartialOrder E] {X : Set E} {d : E}

theorem iota_isGreatest_eq_some_iff : iota (IsGreatest X) = some d ↔ IsGreatest X d :=
  Set.Subsingleton.iota_eq_some_iff fun _ ha _ hb ↦ ha.unique hb

theorem iota_isGreatest_isSome_iff : (iota (IsGreatest X)).isSome ↔ ∃ d, IsGreatest X d :=
  Set.Subsingleton.iota_isSome_iff fun _ ha _ hb ↦ ha.unique hb

theorem iota_isGreatest_eq_none_iff : iota (IsGreatest X) = none ↔ ¬ ∃ d, IsGreatest X d := by
  rw [← Option.not_isSome_iff_eq_none, iota_isGreatest_isSome_iff]

theorem iota_isGreatest_Iic : iota (IsGreatest (Set.Iic d)) = some d :=
  iota_isGreatest_eq_some_iff.2 isGreatest_Iic

theorem iota_isGreatest_empty : iota (IsGreatest (∅ : Set E)) = none :=
  iota_isGreatest_eq_none_iff.2 fun ⟨_, h, _⟩ ↦ h

theorem iota_isGreatest_elim_Iic (o : Option E) :
    iota (IsGreatest (o.elim ∅ Set.Iic)) = o := by
  cases o
  exacts [iota_isGreatest_empty, iota_isGreatest_Iic]

theorem IsLowerSet.iota_isGreatest (hX : IsLowerSet X) :
    iota (IsGreatest X) = Function.partialInv Set.Iic X :=
  Option.ext fun d ↦ iota_isGreatest_eq_some_iff.trans <|
    (⟨fun hd ↦ (hX.Iic_subset hd.1).antisymm hd.2, (· ▸ isGreatest_Iic)⟩ :
      IsGreatest X d ↔ Set.Iic d = X).trans (Set.Iic_injective.isPartialInv d X).symm

theorem elim_Iic_iota_isGreatest (hX : IsLowerSet X) (hd : X.Nonempty → ∃ d, IsGreatest X d) :
    (iota (IsGreatest X)).elim ∅ Set.Iic = X := by
  rcases X.eq_empty_or_nonempty with rfl | hne
  · rw [iota_isGreatest_empty]
    rfl
  · obtain ⟨d, hd⟩ := hd hne
    rw [iota_isGreatest_eq_some_iff.2 hd]
    exact (hX.Iic_subset hd.1).antisymm hd.2

theorem IsAntichain.iota_isGreatest (hs : IsAntichain (· ≤ ·) X) :
    iota (IsGreatest X) = iota (· ∈ X) :=
  Option.ext fun _ ↦ (iota_isGreatest_eq_some_iff.trans <|
    hs.greatest_iff.trans Set.eq_singleton_iff_unique_mem).trans (iota_eq_some_iff _).symm

theorem IsAntichain.iota_isGreatest_eq_none (hs : IsAntichain (· ≤ ·) X) {a b : E}
    (ha : a ∈ X) (hb : b ∈ X) (hab : a ≠ b) : iota (IsGreatest X) = none :=
  iota_isGreatest_eq_none_iff.2 fun ⟨_, hd⟩ ↦ by
    rw [hs.greatest_iff.1 hd] at ha hb
    exact hab (ha.trans hb.symm)

theorem DirectedOn.iota_isGreatest_isSome (hs : DirectedOn (· ≤ ·) X) (hfin : X.Finite)
    (hne : X.Nonempty) : (iota (IsGreatest X)).isSome :=
  let ⟨m, hm⟩ := hfin.exists_maximal hne
  iota_isGreatest_isSome_iff.2
    ⟨m, hm.prop, hs.is_top_of_is_max hm.prop fun _ ha ↦ hm.le_of_ge ha⟩

end Order
