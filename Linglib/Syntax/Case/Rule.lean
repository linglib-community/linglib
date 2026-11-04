/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Feature.Slot
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Order.Fin.Basic

/-!
# Case rules

The state of a derivation gives each nominal the slot of its case (`FeatureSlot`): unvalued until a
value is assigned, valued once one is, and absent for a nominal that bears no case, such as PRO. A
nominal is *caseless* when its slot has no value, so PRO is caseless and competes for dependent case
without receiving one. A *case rule* says what an unvalued nominal takes, given how many caseless
nominals of its domain stand above it and how many below, and a [pass](##CaseRule.pass) applies a
rule across a domain at once; dependent case, Agree and licensing are such rules. A pass
[extends](##FeatureSlot.Extends) the state, so it is inflationary, but it is
[not monotone](##CaseRule.not_monotone_pass): valuing one nominal can bleed the case of another, so
no order-theoretic closure applies. On a chain a pass is
[lookup by rank](##CaseRule.passGoals_getElem).

## Implementation notes

The nominals are a type `ι`, whatever identifies them in a study: positions `Fin n`, labels, or the
tokens of a tree. C-command is a relation rather than an `LT` instance because it varies with the
phase, and a domain is a `Finset`, so restricting a pass to what a head sees is restricting the
domain.

## References

* [marantz-1991]
* [chomsky-2000]
* [kalin-2018]
-/

@[expose] public section

open Finset

/-! ### The state -/

namespace FeatureSlot

variable {ι κ : Type*} {D : Finset ι} {S T : Set κ} {s t u : ι → FeatureSlot κ} {x : ι} {v : κ}

/-- The caseless nominals of `D`: those without a value, whether unvalued or bearing no case. -/
def caseless (D : Finset ι) (s : ι → FeatureSlot κ) : Finset ι :=
  D.filter fun x ↦ (s x).value? = none

/-- The goals in `D`: the nominals with an unvalued case, which a probe relativized to them sees. A
nominal bearing no case is caseless but no goal. -/
def goals (D : Finset ι) (s : ι → FeatureSlot κ) : Finset ι :=
  D.filter fun x ↦ s x = .unvalued

@[simp] theorem mem_caseless : x ∈ caseless D s ↔ x ∈ D ∧ (s x).value? = none := mem_filter

@[simp] theorem mem_goals : x ∈ goals D s ↔ x ∈ D ∧ s x = .unvalued := mem_filter

@[simp] theorem caseless_goals : caseless (goals D s) s = goals D s :=
  filter_true_of_mem fun x hx ↦ by simp [(mem_goals.1 hx).2]

@[simp] theorem caseless_map {κ' : Type*} (g : κ → κ') :
    caseless D (fun x ↦ (s x).map g) = caseless D s := by
  ext; simp [Option.map_eq_none_iff]

@[simp] theorem goals_map {κ' : Type*} (g : κ → κ') :
    goals D (fun x ↦ (s x).map g) = goals D s := by
  ext; simp

/-- `t` extends `s` by values in `S`: each slot is as in `s`, or was unvalued there and is valued in
`t` with a value in `S`. -/
def Extends (S : Set κ) (s t : ι → FeatureSlot κ) : Prop :=
  ∀ x, s x = t x ∨ s x = .unvalued ∧ ∃ v ∈ S, t x = .valued v

namespace Extends

@[refl] protected theorem refl (s : ι → FeatureSlot κ) : Extends S s s := fun _ ↦ .inl rfl

theorem mono (hST : S ⊆ T) (h : Extends S s t) : Extends T s t :=
  fun x ↦ (h x).imp_right fun ⟨hs, v, hv, ht⟩ ↦ ⟨hs, v, hST hv, ht⟩

protected theorem trans (h₁ : Extends S s t) (h₂ : Extends S t u) : Extends S s u := fun x ↦ by
  rcases h₁ x with e | ⟨hs, v, hv, ht⟩
  · exact e ▸ h₂ x
  · rcases h₂ x with e | ⟨ht', -⟩
    · exact .inr ⟨hs, v, hv, e ▸ ht⟩
    · simp [ht] at ht'

/-- An extension is at least as valued. -/
protected theorem le (h : Extends S s t) : s ≤ t := fun x ↦ by
  rcases h x with e | ⟨hs, v, -, ht⟩
  · exact e.le
  · simp [hs, ht]

/-- A nominal bears no case in an extension exactly when it bears none before. -/
theorem eq_absent_iff (h : Extends S s t) : s x = .absent ↔ t x = .absent := by
  rcases h x with e | ⟨hs, v, -, ht⟩ <;> simp_all

/-- A value, once assigned, persists. -/
theorem valued (h : Extends S s t) (hs : s x = .valued v) : t x = .valued v :=
  FeatureSlot.valued_le_iff.1 (hs ▸ h.le x)

/-- A nominal unvalued in the extension was unvalued before. -/
theorem unvalued (h : Extends S s t) (ht : t x = .unvalued) : s x = .unvalued := by
  rcases h x with e | ⟨hs, -⟩
  · exact e.trans ht
  · exact hs

/-- A value of the extension was already assigned or lies in `S`. -/
theorem of_valued (h : Extends S s t) (ht : t x = .valued v) : s x = .valued v ∨ v ∈ S := by
  rcases h x with e | ⟨-, w, hw, ht'⟩
  · exact .inl (e.trans ht)
  · obtain rfl : v = w := FeatureSlot.valued_inj.1 (ht.symm.trans ht')
    exact .inr hw

/-- A sequence of steps each extending by `S` extends by `S`. -/
protected theorem foldl {γ : Type*} {F : γ → (ι → FeatureSlot κ) → ι → FeatureSlot κ} :
    ∀ (l : List γ), (∀ c ∈ l, ∀ s, Extends S s (F c s)) →
      ∀ s : ι → FeatureSlot κ, Extends S s (l.foldl (fun s c ↦ F c s) s)
  | [], _, s => .refl s
  | c :: l, hF, s =>
    (hF c List.mem_cons_self s).trans
      (Extends.foldl l (fun c hc ↦ hF c (List.mem_cons_of_mem _ hc)) _)

end Extends

end FeatureSlot

/-! ### Case rules -/

/-- A case rule: what an unvalued nominal takes, given how many caseless nominals of its domain
stand above it and how many below. -/
abbrev CaseRule (κ : Type*) := ℕ → ℕ → Option κ

namespace CaseRule

open FeatureSlot (Extends caseless goals)

variable {ι κ : Type*} {D : Finset ι} {s : ι → FeatureSlot κ} {x : ι}

/-- The values a rule can offer. -/
def values (r : CaseRule κ) : Set κ := {v | ∃ a b, r a b = some v}

/-- The rule valuing with `vs` by rank: a goal with `i` goals above it takes the `i`th, so on a
chain the highest takes the first and the next the second. -/
def inOrder (vs : List κ) : CaseRule κ := fun a _ ↦ vs[a]?

section Pass

variable [DecidableEq ι] (lt : ι → ι → Prop) [DecidableRel lt]

/-- A pass of the rule `r` over the domain `D`, `lt y x` saying that `y` c-commands `x`: each
unvalued nominal of `D` takes what `r` says of the caseless nominals of `D` above and below it, all
of them at once. -/
def pass (r : CaseRule κ) (D : Finset ι) (s : ι → FeatureSlot κ) : ι → FeatureSlot κ := fun x ↦
  if x ∈ D ∧ s x = .unvalued then
    .offer (r ((caseless D s).filter (lt · x)).card ((caseless D s).filter (lt x ·)).card)
  else s x

/-- A pass over the goals of `D`, as a probe relativized to them makes it: a nominal bearing no case
neither counts nor receives. -/
def passGoals (r : CaseRule κ) (D : Finset ι) (s : ι → FeatureSlot κ) : ι → FeatureSlot κ :=
  r.pass lt (goals D s) s

variable {lt} {r : CaseRule κ}

theorem pass_of_mem (hx : x ∈ D) (hs : s x = .unvalued) : r.pass lt D s x =
    .offer (r ((caseless D s).filter (lt · x)).card ((caseless D s).filter (lt x ·)).card) :=
  ite_eq_left ⟨hx, hs⟩

theorem pass_of_notMem (hx : x ∉ D) : r.pass lt D s x = s x :=
  ite_eq_right fun h ↦ hx h.1

theorem pass_of_ne_unvalued (hs : s x ≠ .unvalued) : r.pass lt D s x = s x :=
  ite_eq_right fun h ↦ hs h.2

theorem passGoals_of_mem (hx : x ∈ goals D s) : r.passGoals lt D s x =
    .offer (r ((goals D s).filter (lt · x)).card ((goals D s).filter (lt x ·)).card) := by
  rw [passGoals, pass_of_mem hx (FeatureSlot.mem_goals.1 hx).2, FeatureSlot.caseless_goals]

theorem passGoals_of_notMem (hx : x ∉ goals D s) : r.passGoals lt D s x = s x :=
  pass_of_notMem hx

/-- A rule that offers nothing leaves the state as it is. -/
theorem pass_of_forall_eq_none (hr : ∀ a b, r a b = none) : r.pass lt D s = s := by
  funext x
  by_cases h : x ∈ D ∧ s x = .unvalued
  · rw [pass_of_mem h.1 h.2, hr, FeatureSlot.offer_none, h.2]
  · exact ite_eq_right h

/-- A pass extends the state by what the rule can offer. -/
theorem extends_pass (r : CaseRule κ) (D : Finset ι) (s : ι → FeatureSlot κ) :
    Extends r.values s (r.pass lt D s) := fun x ↦ by
  by_cases h : x ∈ D ∧ s x = .unvalued
  · rw [pass_of_mem h.1 h.2]
    cases hr : r _ _ with
    | none => exact .inl h.2
    | some v => exact .inr ⟨h.2, v, ⟨_, _, hr⟩, rfl⟩
  · exact .inl (ite_eq_right h).symm

theorem extends_passGoals (r : CaseRule κ) (D : Finset ι) (s : ι → FeatureSlot κ) :
    Extends r.values s (r.passGoals lt D s) :=
  extends_pass r _ s

theorem extends_inOrder (vs : List κ) (D : Finset ι) (s : ι → FeatureSlot κ) :
    Extends {v | v ∈ vs} s ((inOrder vs).passGoals lt D s) :=
  (extends_passGoals _ D s).mono fun _ hv ↦ by
    obtain ⟨_, _, hw⟩ := hv
    exact List.mem_of_getElem? hw

/-- A pass is inflationary. -/
theorem le_pass (r : CaseRule κ) (D : Finset ι) (s : ι → FeatureSlot κ) : s ≤ r.pass lt D s :=
  (extends_pass r D s).le

/-- A pass commutes with renaming the values. -/
theorem map_pass {κ' : Type*} (g : κ → κ') (r : CaseRule κ) (D : Finset ι) (s : ι → FeatureSlot κ)
    (x : ι) : (r.pass lt D s x).map g =
      pass lt (fun a b ↦ (r a b).map g) D (fun x ↦ (s x).map g) x := by
  by_cases h : x ∈ D ∧ s x = .unvalued <;> simp [pass, h]

/-! ### Chains -/

variable [Std.Asymm lt]

/-- In a list ordered by `lt`, the number of members above one is its position. -/
theorem card_filter_lt_getElem : ∀ {G : List ι}, G.Pairwise lt → ∀ (i : ℕ) (hi : i < G.length),
    (G.toFinset.filter (lt · G[i])).card = i
  | [], _, _, hi => absurd hi (by simp)
  | g :: G, hG, 0, _ => by
    obtain ⟨hg, -⟩ := List.pairwise_cons.1 hG
    refine Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun y hy hyg ↦ ?_)
    rcases List.mem_cons.1 (List.mem_toFinset.1 hy) with rfl | hy
    · exact asymm hyg hyg
    · exact asymm hyg (hg y hy)
  | g :: G, hG, i + 1, hi => by
    obtain ⟨hg, hG⟩ := List.pairwise_cons.1 hG
    have hi' : i < G.length := Nat.lt_of_succ_lt_succ hi
    have hnot : g ∉ G.toFinset.filter (lt · G[i]) := fun h ↦ by
      have hm := List.mem_toFinset.1 (Finset.mem_filter.1 h).1
      exact asymm (hg g hm) (hg g hm)
    simp only [List.toFinset_cons, List.getElem_cons_succ, Finset.filter_insert,
      hg _ (List.getElem_mem hi'), ↓reduceIte, Finset.card_insert_of_notMem hnot,
      card_filter_lt_getElem hG i hi']

/-- In a list ordered by `lt`, the number of members below one is the number after it. -/
theorem card_filter_getElem_lt : ∀ {G : List ι}, G.Pairwise lt → ∀ (i : ℕ) (hi : i < G.length),
    (G.toFinset.filter (lt G[i] ·)).card = G.length - 1 - i
  | [], _, _, hi => absurd hi (by simp)
  | g :: G, hG, 0, _ => by
    obtain ⟨hg, hG'⟩ := List.pairwise_cons.1 hG
    have hnd : G.Nodup := List.Pairwise.imp (fun {a b} (h : lt a b) ↦ by
      rintro rfl
      exact asymm h h) hG'
    have hself : ¬ lt g g := fun h ↦ asymm h h
    simp only [List.toFinset_cons, List.getElem_cons_zero, Finset.filter_insert, hself, ↓reduceIte,
      Finset.filter_true_of_mem fun y hy ↦ hg y (List.mem_toFinset.1 hy),
      List.toFinset_card_of_nodup hnd, List.length_cons, Nat.add_sub_cancel, Nat.sub_zero]
  | g :: G, hG, i + 1, hi => by
    obtain ⟨hg, hG⟩ := List.pairwise_cons.1 hG
    have hi' : i < G.length := Nat.lt_of_succ_lt_succ hi
    have hnot : ¬ lt G[i] g := fun h ↦ asymm h (hg _ (List.getElem_mem hi'))
    simp only [List.toFinset_cons, List.getElem_cons_succ, Finset.filter_insert, hnot, ↓reduceIte,
      card_filter_getElem_lt hG i hi', List.length_cons]
    omega

/-- On a chain, a pass over the goals is lookup by rank: the goal with `i` goals above it, and so
all the rest below it, takes what the rule says of those two numbers. -/
theorem passGoals_getElem (r : CaseRule κ) {G : List ι} (hG : G.Pairwise lt)
    (hD : goals D s = G.toFinset) (i : ℕ) (hi : i < G.length) :
    r.passGoals lt D s G[i] = .offer (r i (G.length - 1 - i)) := by
  have hmem : G[i] ∈ goals D s := hD ▸ List.mem_toFinset.2 (List.getElem_mem hi)
  rw [passGoals_of_mem hmem, hD, card_filter_lt_getElem hG i hi, card_filter_getElem_lt hG i hi]

end Pass

/-- A pass is not monotone in the state whenever the rule offers something to a nominal with a
caseless nominal above it that it does not offer one alone: valuing the higher nominal bleeds the
lower one's case. -/
theorem not_monotone_pass {r : CaseRule κ} {c : κ} (h₁ : r 1 0 = some c) (h₀ : r 0 0 = none) :
    ¬ Monotone (r.pass (· < ·) (univ : Finset (Fin 2))) := by
  intro hmono
  let bled : Fin 2 → FeatureSlot κ := fun i ↦ if i = 0 then .valued c else .unvalued
  have hle : (fun _ ↦ .unvalued : Fin 2 → FeatureSlot κ) ≤ bled := by
    intro i
    by_cases hi : i = 0 <;> simp [bled, hi]
  have hcaseless : caseless univ bled = {1} := by
    ext i
    by_cases hi : i = 0
    · simp [bled, hi]
    · simp [bled, show i = 1 by omega]
  have hs : caseless univ (fun _ ↦ .unvalued : Fin 2 → FeatureSlot κ) = univ := by
    ext i
    simp
  have hbled : r.pass (· < ·) univ bled 1 = .unvalued := by
    rw [pass_of_mem (mem_univ _) (by simp [bled]), hcaseless,
      show (({1} : Finset (Fin 2)).filter (· < 1)).card = 0 by decide,
      show (({1} : Finset (Fin 2)).filter (1 < ·)).card = 0 by decide, h₀]
    rfl
  have hfull : r.pass (· < ·) univ (fun _ ↦ .unvalued : Fin 2 → FeatureSlot κ) 1 = .valued c := by
    rw [pass_of_mem (s := fun _ ↦ .unvalued) (mem_univ _) rfl, hs,
      show ((univ : Finset (Fin 2)).filter (· < 1)).card = 1 by decide,
      show ((univ : Finset (Fin 2)).filter (1 < ·)).card = 0 by decide, h₁]
    rfl
  have := hmono hle 1
  simp [hbled, hfull] at this

end CaseRule
