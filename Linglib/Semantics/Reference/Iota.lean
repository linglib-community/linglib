module

public import Mathlib.Data.Set.Subsingleton
public import Mathlib.Order.Antichain
public import Mathlib.Order.Preorder.Finite
public import Linglib.Semantics.Quantification.Basic

/-!
# Iota

The iota operator takes a predicate to the individual it describes, when there is one: `iota P`
is the unique satisfier of `P`, and `none` when `P` has no satisfier or several. Its definedness
is unique existence, which splits into existence and uniqueness of the extension, the two
components that Coppock and Beaver separate into an assertion and a presupposition. The
determiner *the* asserts its scope of this referent.

Sharvy generalizes the definite article to individuals ordered by part-of, and Chierchia adopts
the generalization: the definite picks out the largest member of a set, `iota (IsGreatest X)`,
since a set has at most one largest member. No atom is larger than another, so on a set of atoms
the largest member exists only when there is exactly one member, while a finite nonempty set
closed under sum always has one. Sending an individual to its parts, `Set.Iic d`, undoes the
largest member.

## Main definitions

* `Reference.iota`: the unique satisfier of a predicate, or `none`.

## Main results

* `iota_eq_some_iff`, `iota_isSome_iff`, `iota_eq_none_iff`, `iota_eq_none_of_ne`.
* `existsUnique_iff_nonempty_subsingleton`: `∃!` is nonemptiness with subsingletonness.
* `the_sem_iff_iota`: the determiner *the* asserts its scope of the referent.
* `iota_isGreatest_eq_some_iff`: the largest member, Chierchia's (11a).
* `IsAntichain.iota_isGreatest`: on an antichain the largest member is the unique member,
  Chierchia's (11c), so an antichain with two members has none
  (`IsAntichain.iota_isGreatest_eq_none`).
* `DirectedOn.iota_isGreatest_isSome`: a finite nonempty directed set has a largest member.
* `iota_isGreatest_elim_Iic`, `elim_Iic_iota_isGreatest`: Chierchia's (17a) and (17b) at a
  single situation.

## Implementation notes

A partial individual is an `Option`. Krifka, following Link, writes σ for the largest member and
defines it as ιx[S(x) ∧ ∀x′[S(x′) → x′ ⊑ x]], which is `iota (IsGreatest X)`. A kind in
Chierchia's sense is a function `S → Option E` from situations to partial individuals. His ∩ is
`fun s ↦ iota (IsGreatest (P s))` where that is a kind, (16), and his ∪ is
`fun s ↦ (k s).elim ∅ Set.Iic`, the ι and Id of his (25) applied at each situation
(pp. 359–360). His (25e) prints Id(x) = λx[x ≤ y]; his footnote 14 shows that λy[y ≤ x] is
meant.

## References

* [russell-1905]
* [coppock-beaver-2015]
* [partee-1987]
* [sharvy-1980]
* [chierchia-1998]
* [link-1983]
* [krifka-2026]
-/

@[expose] public section

variable {α : Type*} {p : α → Prop}

/-- Unique existence is nonemptiness together with subsingletonness of the extension. -/
theorem existsUnique_iff_nonempty_subsingleton :
    (∃! x, p x) ↔ {x | p x}.Nonempty ∧ {x | p x}.Subsingleton :=
  (exists_congr fun _ ↦ Set.eq_singleton_iff_unique_mem.symm).trans
    Set.exists_eq_singleton_iff_nonempty_subsingleton

namespace Reference

variable {E : Type*} (P : E → Prop) {e : E}

/-- `iota P` is the unique satisfier of `P`, or `none` when `P` has no satisfier or
several. -/
noncomputable def iota : Option E :=
  letI := Classical.dec (∃! x, P x)
  if h : ∃! x, P x then some h.choose else none

theorem iota_eq_some_iff : iota P = some e ↔ P e ∧ ∀ x, P x → x = e := by
  classical
  unfold iota
  split_ifs with h
  · rw [Option.some_inj, h.choose_eq_iff]
    exact ⟨fun he ↦ ⟨he, fun _ hx ↦ h.unique hx he⟩, And.left⟩
  · exact ⟨(nomatch ·), fun he ↦ (h ⟨e, he⟩).elim⟩

theorem iota_isSome_iff : (iota P).isSome ↔ ∃! x, P x := by
  classical
  unfold iota
  split_ifs with h <;> simp [h]

theorem iota_eq_none_iff : iota P = none ↔ ¬ ∃! x, P x := by
  rw [← Option.not_isSome_iff_eq_none, iota_isSome_iff]

/-- A predicate with two distinct satisfiers has no iota. -/
theorem iota_eq_none_of_ne {e' : E} (he : P e) (he' : P e') (hne : e ≠ e') : iota P = none :=
  (iota_eq_none_iff P).2 fun h ↦ hne (h.unique he he')

/-! ### The definite article -/

section Article

open Quantifier Quantifier.GQ Quantifier.NP

/-- The iota of Partee's singleton property `ident j` is `j`. -/
theorem iota_ident (j : E) : iota (ident j) = some j :=
  (iota_eq_some_iff _).2 ⟨rfl, fun _ h ↦ h⟩

variable (S : E → Prop)

/-- The determiner *the* asserts its scope of the Russellian referent. -/
theorem the_sem_iff_iota : the P S ↔ ∃ x ∈ iota P, S x :=
  exists_congr fun x ↦ and_congr_left' <|
    (⟨fun h ↦ ⟨(h x).2 rfl, fun y ↦ (h y).1⟩, fun ⟨hx, hu⟩ y ↦ ⟨hu y, fun e ↦ e ▸ hx⟩⟩ :
      (∀ y, P y ↔ y = x) ↔ P x ∧ ∀ y, P y → y = x).trans (iota_eq_some_iff P).symm

end Article

/-! ### Predicates with at most one satisfier -/

section Subsingleton

variable {P}

theorem _root_.Set.Subsingleton.iota_eq_some_iff (h : {x | P x}.Subsingleton) :
    iota P = some e ↔ P e :=
  (Reference.iota_eq_some_iff P).trans ⟨And.left, fun he ↦ ⟨he, fun _ hx ↦ h hx he⟩⟩

theorem _root_.Set.Subsingleton.iota_isSome_iff (h : {x | P x}.Subsingleton) :
    (iota P).isSome ↔ ∃ x, P x :=
  (Reference.iota_isSome_iff P).trans
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

/-- The largest part of a partial individual is that individual. -/
theorem iota_isGreatest_elim_Iic (o : Option E) :
    iota (IsGreatest (o.elim ∅ Set.Iic)) = o := by
  cases o
  exacts [iota_isGreatest_empty, iota_isGreatest_Iic]

/-- If `X` is closed downward and has a largest member wherever it is nonempty, then `X` is the
set of parts of its largest member. -/
theorem elim_Iic_iota_isGreatest (hX : IsLowerSet X) (hd : X.Nonempty → ∃ d, IsGreatest X d) :
    (iota (IsGreatest X)).elim ∅ Set.Iic = X := by
  rcases X.eq_empty_or_nonempty with rfl | hne
  · rw [iota_isGreatest_empty]
    rfl
  · obtain ⟨d, hd⟩ := hd hne
    rw [iota_isGreatest_eq_some_iff.2 hd]
    exact Set.Subset.antisymm (fun _ hx ↦ hX hx hd.1) fun _ hx ↦ hd.2 hx

/-- On an antichain, such as a set of atoms, the largest member is the unique member. -/
theorem _root_.IsAntichain.iota_isGreatest (hs : IsAntichain (· ≤ ·) X) :
    iota (IsGreatest X) = iota (· ∈ X) :=
  Option.ext fun _ ↦ (iota_isGreatest_eq_some_iff.trans <|
    hs.greatest_iff.trans Set.eq_singleton_iff_unique_mem).trans (iota_eq_some_iff _).symm

/-- An antichain with two members, such as a set of two atoms, has no largest member. -/
theorem _root_.IsAntichain.iota_isGreatest_eq_none (hs : IsAntichain (· ≤ ·) X) {a b : E}
    (ha : a ∈ X) (hb : b ∈ X) (hab : a ≠ b) : iota (IsGreatest X) = none :=
  iota_isGreatest_eq_none_iff.2 fun ⟨_, hd⟩ ↦ by
    rw [hs.greatest_iff.1 hd] at ha hb
    exact hab (ha.trans hb.symm)

/-- A finite nonempty directed set, such as a finite nonempty sup-closed set, has a largest
member. -/
theorem _root_.DirectedOn.iota_isGreatest_isSome (hs : DirectedOn (· ≤ ·) X) (hfin : X.Finite)
    (hne : X.Nonempty) : (iota (IsGreatest X)).isSome :=
  let ⟨m, hm⟩ := hfin.exists_maximal hne
  iota_isGreatest_isSome_iff.2
    ⟨m, hm.prop, hs.is_top_of_is_max hm.prop fun _ ha ↦ hm.le_of_ge ha⟩

end Order

end Reference
