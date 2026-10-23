module

public import Mathlib.Data.Finset.Pairwise
public import Mathlib.Order.Partition.Finpartition
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Core.Data.Set.Functor
public import Linglib.Core.ModelTheory.Graph

/-!
# Reciprocal predicates

A reading of *the Xs R each other* is the relativization of a quantifier over binary relations,
a condition on the relation `R` restricted to the antecedent set `X` that is invariant under
isomorphism. Dalrymple, Kanazawa, Kim, Mchombo and Peters, following Westerståhl, take three such
quantifiers of type `⟨2⟩`, Lindström quantifiers over the language of graphs. On two or more
elements, `ful` relates any two distinct elements, `lin` joins them by a chain, and `tot` relates
each element to another, and `ful ≤ lin ≤ tot`. Taking the relation as it is or with its
direction ignored, as `Relation.SymmGen R`, gives their six schemes (`Reciprocal.Recip`),
ordered by entailment as the product of the two parameters. Weak Reciprocity and Partitioned
Strong Reciprocity lie outside the parameterization; with them the file covers the six readings
that Beck orders by entailment.

## Main definitions

* `Reciprocal.ful`, `Reciprocal.lin`, `Reciprocal.tot`: the three quantifiers of type `⟨2⟩`.
* `Reciprocal.StrongReciprocity R X`, `Reciprocal.IntermediateReciprocity R X`,
  `Reciprocal.OneWayWeakReciprocity R X`: their relativizations to `X`.
* `Reciprocal.InclusiveAlternativeOrdering R X`: One-way Weak Reciprocity at
  `Relation.SymmGen R`.
* `Reciprocal.Recip q R X`: the scheme at a setting `q : Coverage × Direction` of the two
  parameters.
* `Reciprocal.WeakReciprocity R X`, `Reciprocal.PartitionedStrongReciprocity R X`: every member
  of `X` is `R`-related to another member and another to it; `X` has a `Finpartition` into
  strongly reciprocal cells.

## Main results

* `Reciprocal.ful_le_lin`, `Reciprocal.lin_le_tot`, `Reciprocal.recip_antitone`: a stronger
  setting of the parameters entails a weaker one.
* `Reciprocal.strongReciprocity_iff`, `Reciprocal.intermediateReciprocity_iff`,
  `Reciprocal.oneWayWeakReciprocity_iff`: the relativizations stated over the members of `X`.
* `Reciprocal.IntermediateReciprocity.weak`, `Reciprocal.PartitionedStrongReciprocity.weak`:
  Weak Reciprocity follows from the intermediate and the partitioned schemes.
* `Reciprocal.weakReciprocity_iff_liftRel`: Weak Reciprocity is the cumulation `Set.LiftRel` of
  `R` with non-identity conjoined in.

## References

* [D. T. Langendoen, *The logic of reciprocity* (1978)][langendoen-1978]
* [R. Fiengo and H. Lasnik, *The logical structure of reciprocal sentences in English*
  (1973)][fiengo-lasnik-1973]
* [Z. Kański, *Logical symmetry and natural language reciprocals* (1987)][kanski-1987]
* [M. Dalrymple, M. Kanazawa, Y. Kim, S. A. Mchombo and S. Peters, *Reciprocal expressions and
  the concept of reciprocity* (1998)][dalrymple-et-al-1998]
* [S. Beck, *Reciprocals are definites* (2001)][beck-2001]
* [W. Sternefeld, *Reciprocity and cumulative predication* (1998)][sternefeld-1998]
* [S. Peters and D. Westerståhl, *Quantifiers in Language and Logic*
  (2006)][peters-westerstahl-2006]
-/

@[expose] public section

universe u

namespace Reciprocal

open FirstOrder Language Relation

/-! ### Three quantifiers of type `⟨2⟩` -/

private theorem transGen_comp_equiv {M N : Type u} (e : M ≃ N) (s : N → N → Prop) :
    TransGen (fun a b ↦ s (e a) (e b)) = fun x y ↦ TransGen s (e x) (e y) := by
  funext x y
  refine propext ⟨fun h ↦ TransGen.lift e (fun _ _ h ↦ h) _ _ h, fun h ↦ ?_⟩
  simpa [Function.onFun] using TransGen.lift e.symm (r := s) (p := fun a b ↦ s (e a) (e b))
    (fun a b h ↦ by simpa [Function.onFun] using h) _ _ h

private theorem exists_rel_ne_of_transGen {M : Type*} {r : M → M → Prop} {x y : M}
    (h : TransGen r x y) (hyx : y ≠ x) : ∃ z, z ≠ x ∧ r x z := by
  induction h with
  | single h => exact ⟨_, hyx, h⟩
  | @tail b c _ hbc ih =>
    by_cases hbx : b = x
    · exact ⟨c, hyx, hbx ▸ hbc⟩
    · exact ih hbx

/-- `FUL` holds when there are two or more elements and any two distinct elements are related. -/
def ful : LindstromQuantifier.{0, 0, u} Language.graph :=
  .ofGraphProperty (fun {M} r ↦ Nontrivial M ∧ Pairwise r) fun e s ↦
    and_congr e.nontrivial_congr (EquivLike.pairwise_comp_iff e s)

/-- `LIN` holds when there are two or more elements and any two distinct elements are joined by
a chain. -/
def lin : LindstromQuantifier.{0, 0, u} Language.graph :=
  .ofGraphProperty (fun {M} r ↦ Nontrivial M ∧ Pairwise (TransGen r)) fun e s ↦
    and_congr e.nontrivial_congr <| by
      rw [transGen_comp_equiv]
      exact EquivLike.pairwise_comp_iff e (TransGen s)

/-- `TOT` holds when there are two or more elements and each is related to another. -/
def tot : LindstromQuantifier.{0, 0, u} Language.graph :=
  .ofGraphProperty (fun {M} r ↦ Nontrivial M ∧ ∀ x, ∃ y, x ≠ y ∧ r x y) fun e s ↦
    and_congr e.nontrivial_congr
      ⟨fun h x ↦ let ⟨y, hne, hs⟩ := h (e.symm x)
        ⟨e y, fun hx ↦ hne (e.symm_apply_eq.2 hx), by simpa using hs⟩,
      fun h x ↦ let ⟨y, hne, hs⟩ := h (e x)
        ⟨e.symm y, fun hx ↦ hne (e.eq_symm_apply.1 hx), by simpa using hs⟩⟩

theorem ful_le_lin : ful.{u} ≤ lin := fun _ ⟨h, hr⟩ ↦ ⟨h, hr.mono fun _ _ h ↦ .single h⟩

theorem lin_le_tot : lin.{u} ≤ tot := fun _ ⟨h, hr⟩ ↦ ⟨h, fun x ↦
  let ⟨_, hy⟩ := exists_ne x
  let ⟨z, hzx, hz⟩ := exists_rel_ne_of_transGen (hr hy.symm) hy
  ⟨z, hzx.symm, hz⟩⟩

/-! ### Relativizations -/

variable {α : Type*} {R S : α → α → Prop} {X : Finset α}

/-- Strong Reciprocity ([langendoen-1978]) is `ful` relativized to `X`, so `X` has two or more
members and any two distinct members are `R`-related. -/
def StrongReciprocity (R : α → α → Prop) (X : Finset α) : Prop :=
  inducedGraph R ↑X ∈ ful.holds

/-- Intermediate Reciprocity ([langendoen-1978]) is `lin` relativized to `X`, so `X` has two or
more members and any two distinct members are joined by a chain of `R`-steps through `X`. -/
def IntermediateReciprocity (R : α → α → Prop) (X : Finset α) : Prop :=
  inducedGraph R ↑X ∈ lin.holds

/-- One-way Weak Reciprocity ([dalrymple-et-al-1998]) is `tot` relativized to `X`, so `X` has two
or more members and each is `R`-related to another. -/
def OneWayWeakReciprocity (R : α → α → Prop) (X : Finset α) : Prop :=
  inducedGraph R ↑X ∈ tot.holds

/-- Inclusive Alternative Ordering ([kanski-1987]) is One-way Weak Reciprocity with the direction
of `R` ignored, so each member of `X` is `R`-related to another in one direction or the other. -/
def InclusiveAlternativeOrdering (R : α → α → Prop) (X : Finset α) : Prop :=
  OneWayWeakReciprocity (SymmGen R) X

theorem strongReciprocity_iff : StrongReciprocity R X ↔ X.Nontrivial ∧ (X : Set α).Pairwise R :=
  and_congr Set.nontrivial_coe_sort (pairwise_subtype_iff_pairwise_set _ _)

private theorem transGen_subtype_iff {s : Set α} {a b : s} :
    TransGen (fun x y : s ↦ R x y) a b ↔ TransGen (fun x y ↦ x ∈ s ∧ y ∈ s ∧ R x y) a b := by
  refine ⟨fun h ↦ TransGen.lift Subtype.val (fun x y h ↦ ⟨x.2, y.2, h⟩) _ _ h, fun h ↦ ?_⟩
  suffices ∀ {x y : α} (hx : x ∈ s) (hy : y ∈ s),
      TransGen (fun x y ↦ x ∈ s ∧ y ∈ s ∧ R x y) x y →
        TransGen (fun x y : s ↦ R x y) ⟨x, hx⟩ ⟨y, hy⟩ from this a.2 b.2 h
  intro x y hx hy h
  induction h with
  | single h => exact .single h.2.2
  | @tail c d _ hcd ih => exact .tail (ih hcd.1) hcd.2.2

theorem intermediateReciprocity_iff : IntermediateReciprocity R X ↔
    X.Nontrivial ∧ (X : Set α).Pairwise (TransGen fun x y ↦ x ∈ X ∧ y ∈ X ∧ R x y) :=
  and_congr Set.nontrivial_coe_sort <| by
    rw [← pairwise_subtype_iff_pairwise_set]
    exact forall₂_congr fun _ _ ↦ imp_congr_right fun _ ↦ transGen_subtype_iff

theorem oneWayWeakReciprocity_iff :
    OneWayWeakReciprocity R X ↔ X.Nontrivial ∧ ∀ x ∈ X, ∃ y ∈ X, x ≠ y ∧ R x y :=
  and_congr Set.nontrivial_coe_sort <| by
    show (∀ x : (X : Set α), ∃ y : (X : Set α), x ≠ y ∧ R x y) ↔ _
    simp only [Subtype.forall, Subtype.exists, ne_eq, Subtype.mk.injEq, Finset.mem_coe,
      exists_prop]

theorem strongReciprocity_pair [DecidableEq α] {a b : α} :
    StrongReciprocity R {a, b} ↔ a ≠ b ∧ R a b ∧ R b a := by
  rw [strongReciprocity_iff, Finset.Nontrivial, Finset.coe_pair, Set.pairwise_pair]
  refine ⟨fun ⟨hn, h⟩ ↦ ?_, fun ⟨hab, h⟩ ↦ ⟨Set.nontrivial_pair hab, fun _ ↦ h⟩⟩
  have hab : a ≠ b := by
    rintro rfl
    simp at hn
  exact ⟨hab, h hab⟩

section Decidable

variable [DecidableEq α] (R : α → α → Prop) [DecidableRel R] (X : Finset α)

instance : Decidable (StrongReciprocity R X) :=
  decidable_of_iff _ strongReciprocity_iff.symm

instance : Decidable (OneWayWeakReciprocity R X) :=
  decidable_of_iff _ oneWayWeakReciprocity_iff.symm

instance : Decidable (InclusiveAlternativeOrdering R X) :=
  inferInstanceAs (Decidable (OneWayWeakReciprocity (SymmGen R) X))

end Decidable

theorem StrongReciprocity.mono (h : StrongReciprocity R X) (hRS : R ≤ S) :
    StrongReciprocity S X :=
  ⟨h.1, h.2.mono fun x y (hxy : R x y) ↦ hRS x y hxy⟩

theorem IntermediateReciprocity.mono (h : IntermediateReciprocity R X) (hRS : R ≤ S) :
    IntermediateReciprocity S X :=
  ⟨h.1, h.2.mono fun x y ↦ TransGen.mono (fun (a b : (X : Set α)) (hab : R a b) ↦ hRS a b hab) x y⟩

theorem OneWayWeakReciprocity.mono (h : OneWayWeakReciprocity R X) (hRS : R ≤ S) :
    OneWayWeakReciprocity S X :=
  ⟨h.1, fun (x : (X : Set α)) ↦ (h.2 x).imp fun y ⟨hne, (hxy : R x y)⟩ ↦ ⟨hne, hRS x y hxy⟩⟩

theorem StrongReciprocity.intermediate (h : StrongReciprocity R X) :
    IntermediateReciprocity R X :=
  ful_le_lin h

theorem IntermediateReciprocity.oneWayWeak (h : IntermediateReciprocity R X) :
    OneWayWeakReciprocity R X :=
  lin_le_tot h

theorem OneWayWeakReciprocity.inclusiveAlternativeOrdering (h : OneWayWeakReciprocity R X) :
    InclusiveAlternativeOrdering R X :=
  h.mono fun _ _ ↦ .of_rel

/-! ### The two parameters

Dalrymple and colleagues obtain their six schemes from two parameters: which of the three
quantifiers the relation must satisfy on the antecedent set, and whether the relation is the
scope relation or that relation with its direction ignored. Each parameter is ordered by
strength, and the schemes are antitone in the product order. -/

/-- How the reciprocal's relation must cover the antecedent set, ordered by strength. -/
inductive Coverage where
  /-- Every member is related to another member, `tot`. -/
  | tot
  /-- Every two distinct members are joined by a chain, `lin`. -/
  | lin
  /-- Every two distinct members are related directly, `ful`. -/
  | ful
  deriving DecidableEq, Repr, Fintype

/-- The strength of a coverage requirement. -/
def Coverage.rank : Coverage → ℕ
  | .tot => 0
  | .lin => 1
  | .ful => 2

instance : LinearOrder Coverage := LinearOrder.lift' Coverage.rank (by decide)

/-- The quantifier of type `⟨2⟩` a coverage requirement names. -/
def Coverage.quantifier : Coverage → LindstromQuantifier.{0, 0, u} Language.graph
  | .tot => Reciprocal.tot
  | .lin => Reciprocal.lin
  | .ful => Reciprocal.ful

theorem Coverage.quantifier_antitone : Antitone Coverage.quantifier.{u} := by
  intro c c' h
  cases c <;> cases c'
  all_goals first
    | exact le_rfl
    | exact absurd h (by decide)
    | exact lin_le_tot
    | exact ful_le_lin
    | exact ful_le_lin.trans lin_le_tot

theorem Coverage.mem_quantifier_mono (c : Coverage) (hRS : R ≤ S)
    (h : inducedGraph R ↑X ∈ c.quantifier.holds) : inducedGraph S ↑X ∈ c.quantifier.holds := by
  cases c
  · exact OneWayWeakReciprocity.mono (R := R) h hRS
  · exact IntermediateReciprocity.mono (R := R) h hRS
  · exact StrongReciprocity.mono (R := R) h hRS

/-- Whether the reciprocal relates the members by the scope relation itself or by that relation
with its direction ignored, ordered by strength. -/
inductive Direction where
  /-- The relation with its direction ignored, `Relation.SymmGen R`. -/
  | alternative
  /-- The scope relation itself. -/
  | plain
  deriving DecidableEq, Repr, Fintype

/-- The strength of a direction setting. -/
def Direction.rank : Direction → ℕ
  | .alternative => 0
  | .plain => 1

instance : LinearOrder Direction := LinearOrder.lift' Direction.rank (by decide)

/-- The relation a direction setting takes from the scope relation `R`. -/
def Direction.rel : Direction → (α → α → Prop) → α → α → Prop
  | .alternative, R => SymmGen R
  | .plain, R => R

theorem Direction.rel_anti {d d' : Direction} (h : d ≤ d') : d'.rel R ≤ d.rel R := by
  cases d <;> cases d'
  · exact le_rfl
  · exact fun _ _ ↦ .of_rel
  · exact absurd h (by decide)
  · exact le_rfl

/-- The reciprocal quantifier of [dalrymple-et-al-1998] at a setting of the two parameters, the
relativization to `X` of the setting's quantifier at the setting's relation. The setting
`(.ful, .plain)` gives Strong Reciprocity and `(.tot, .alternative)` Inclusive Alternative
Ordering. -/
def Recip (q : Coverage × Direction) (R : α → α → Prop) (X : Finset α) : Prop :=
  inducedGraph (q.2.rel R) ↑X ∈ q.1.quantifier.holds

/-- The entailment diagram of [dalrymple-et-al-1998]. A stronger setting of the two parameters
entails a weaker one. -/
theorem recip_antitone : Antitone fun q ↦ Recip q R X := by
  rintro ⟨c, d⟩ ⟨c', d'⟩ hle h
  obtain ⟨hc, hd⟩ := Prod.mk_le_mk.1 hle
  exact Coverage.quantifier_antitone hc (c'.mem_quantifier_mono (Direction.rel_anti hd) h)

/-! ### Weak Reciprocity -/

/-- Weak Reciprocity ([langendoen-1978]) holds when every member of `X` is `R`-related to another
member, and another member is `R`-related to it. -/
def WeakReciprocity (R : α → α → Prop) (X : Finset α) : Prop :=
  (∀ x ∈ X, ∃ y ∈ X, R x y ∧ x ≠ y) ∧ ∀ y ∈ X, ∃ x ∈ X, R x y ∧ x ≠ y

instance [DecidableEq α] (R : α → α → Prop) [DecidableRel R] (X : Finset α) :
    Decidable (WeakReciprocity R X) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Weak Reciprocity is `**` of the relation with non-identity conjoined into it, in the coverage
form `Set.LiftRel`, the bivalent common ground of [beck-2001] and [sternefeld-1998]. -/
theorem weakReciprocity_iff_liftRel (R : α → α → Prop) (X : Finset α) :
    WeakReciprocity R X ↔ Set.LiftRel (fun a b ↦ R a b ∧ a ≠ b) ↑X ↑X := Iff.rfl

theorem WeakReciprocity.oneWayWeak (h : WeakReciprocity R X) (hX : X.Nonempty) :
    OneWayWeakReciprocity R X := by
  obtain ⟨x, hx⟩ := hX
  obtain ⟨y, hy, -, hxy⟩ := h.1 x hx
  exact oneWayWeakReciprocity_iff.2 ⟨⟨x, hx, y, hy, hxy⟩, fun x hx ↦
    let ⟨y, hy, hR, hne⟩ := h.1 x hx
    ⟨y, hy, hne, hR⟩⟩

theorem IntermediateReciprocity.weak (h : IntermediateReciprocity R X) : WeakReciprocity R X := by
  obtain ⟨hX, hr⟩ := h
  have : Nontrivial (X : Set α) := hX
  refine ⟨fun x hx ↦ ?_, fun x hx ↦ ?_⟩ <;>
    obtain ⟨y, hyx⟩ := exists_ne (⟨x, hx⟩ : (X : Set α))
  · obtain ⟨z, hzx, hR⟩ := exists_rel_ne_of_transGen (hr hyx.symm) hyx
    exact ⟨z, z.2, hR, fun h ↦ hzx (Subtype.ext h.symm)⟩
  · obtain ⟨z, hzx, hR⟩ := exists_rel_ne_of_transGen (transGen_swap.2 (hr hyx)) hyx
    exact ⟨z, z.2, hR, fun h ↦ hzx (Subtype.ext h)⟩

/-! ### Partitioned Strong Reciprocity -/

/-- Partitioned Strong Reciprocity ([langendoen-1978]), the reciprocal relation of
[fiengo-lasnik-1973], holds when `X` splits into disjoint cells of two or more members within
each of which Strong Reciprocity holds. -/
def PartitionedStrongReciprocity [DecidableEq α] (R : α → α → Prop) (X : Finset α) : Prop :=
  ∃ P : Finpartition X, ∀ c ∈ P.parts, StrongReciprocity R c

variable [DecidableEq α]

theorem StrongReciprocity.partitionedStrong (h : StrongReciprocity R X) :
    PartitionedStrongReciprocity R X :=
  ⟨.indiscrete (strongReciprocity_iff.1 h).1.nonempty.ne_empty, fun c hc ↦ by
    rw [Finpartition.indiscrete_parts, Finset.mem_singleton] at hc
    exact hc ▸ h⟩

theorem PartitionedStrongReciprocity.weak (h : PartitionedStrongReciprocity R X) :
    WeakReciprocity R X := by
  obtain ⟨P, hP⟩ := h
  have hW {x} (hx : x ∈ X) : ∃ c ∈ P.parts, x ∈ c ∧ WeakReciprocity R c :=
    let ⟨c, hc, hxc⟩ := P.exists_mem hx
    ⟨c, hc, hxc, (hP c hc).intermediate.weak⟩
  refine ⟨fun x hx ↦ ?_, fun x hx ↦ ?_⟩ <;> obtain ⟨c, hc, hxc, hWc⟩ := hW hx
  · obtain ⟨y, hy, hR⟩ := hWc.1 x hxc
    exact ⟨y, P.le hc hy, hR⟩
  · obtain ⟨y, hy, hR⟩ := hWc.2 x hxc
    exact ⟨y, P.le hc hy, hR⟩

end Reciprocal
