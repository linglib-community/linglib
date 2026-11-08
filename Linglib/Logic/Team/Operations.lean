module

public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Order.Hom.BoundedLattice
public import Linglib.Core.Data.Set.Sups
public import Mathlib.Data.Finset.Lattice.Union
public import Linglib.Logic.Team.Closure
public import Linglib.Logic.Bilattice.Product

/-!
# Team operations

This file defines the connectives of team semantics as operations on `TeamProperty α`, the sets
of teams that support a formula. `Team.flat p` is the property of the teams all of whose points
satisfy `p`; a formula built from such atoms by these connectives defines a flat property, whose
teams are those all of whose points make the formula classically true. Split (tensor)
disjunction is the pointwise sup `P ⊻ Q` of `Finset α`, so its closure properties are those of
`Set.sups`.

## Main definitions

* `Team.flat`, `Team.ne`, `Team.nec`, `Team.poss`: the atoms, `NE` and modalities of BSML.
* `Team.biUnionHom`, `Team.possWitness`, `Team.necImage`, `Team.possLax`: the modal
  clauses of modal dependence and inclusion logic, and the quantifier clauses of QBSML.
* `Team.conj`, `Team.disj`, `Team.flatPair`: bilateral conjunction and split disjunction on
  pairs of support and anti-support properties, and the meaning of a classical formula.

## Main results

* `Team.flat_inter`, `Team.flat_sups_flat`, `Team.poss_flat`, `Team.nec_flat`,
  `Team.possWitness_flat`, `Team.possLax_flat`, `Team.necImage_flat`: `flat` commutes with each
  connective.
* `Team.poss_union`, `Team.nec_union`: the flat modalities send unions to split disjunctions.
* `Team.compl_flatPair`, `Team.conj_flatPair`, `Team.disj_flatPair`,
  `Team.map_poss_nec_flatPair`: each bilateral connective sends flat pairs to flat pairs, and so
  do the pairs of image modalities.

## Implementation notes

`Team.nec R` lifts a property of successor sets pointwise, and `Team.poss R P` is
`Team.nec R` of the upper closure of the non-empty teams in `P`, the teams with a non-empty part
in `P`. `Team.necImage R` is a preimage under the `SupBotHom` `Team.biUnionHom R`, so its closure
lemmas are lattice-general ones. Points are left abstract: worlds for BSML, world–assignment
indices for QBSML, assignments for first-order dependence logic; Aloni calls a team a "state".
The anti-support of `ne` is `{∅}`.

## References

* [aloni-2022] Aloni, Logic and Conversation: The Case of Free Choice
* [aloni-anttila-yang-2024] Aloni, Anttila and Yang, State-based Modal Logics for Free Choice
* [anttila-2021] Anttila, The Logic of Free Choice: Axiomatizations of State-based Modal
  Logics
* [anttila-2025] Anttila, Not Nothing: Nonemptiness in Team Semantics
* [anttila-haggblom-yang-2025] Anttila, Häggblom and Yang, Axiomatizing modal inclusion logic
  and its variants
* [vaananen-2007] Väänänen, Dependence Logic: A New Approach to Independence Friendly Logic
* [vaananen-2008] Väänänen, Modal Dependence Logic
-/

@[expose] public section

open scoped SetFamily

namespace Team

variable {α : Type*}

/-! ### Pointwise connectives -/

/-- `flat p` holds of the teams all of whose points satisfy `p`. Atoms, and every flat
connective, define such properties. -/
def flat (p : α → Prop) : TeamProperty α := {t | ∀ x ∈ t, p x}

/-- The non-emptiness atom `NE` holds of the non-empty teams. -/
def ne : TeamProperty α := {t | t.Nonempty}

/-- The flat necessity modality over successor sets `R` holds of a team when the successor set of
each of its points is in `P`. -/
def nec (R : α → Finset α) (P : TeamProperty α) : TeamProperty α :=
  flat fun x ↦ R x ∈ P

/-- The flat possibility modality holds of a team when each of its points has a non-empty set of
successors in `P`: it is `nec` of the teams with a non-empty part in `P`. -/
def poss (R : α → Finset α) (P : TeamProperty α) : TeamProperty α :=
  nec R ↑(upperClosure (P ∩ ne))

/-- The possibility modality of modal dependence logic holds of a team when a single team `Y` in
`P` contains a successor of each of its points ([vaananen-2008] clause (T8), p. 245). -/
def possWitness (R : α → Finset α) (P : TeamProperty α) : TeamProperty α :=
  {t | ∃ Y, (∀ x ∈ t, ∃ y ∈ Y, y ∈ R x) ∧ Y ∈ P}

variable {p q : α → Prop} {P : TeamProperty α} {R : α → Finset α} {t : Finset α}

@[simp] theorem mem_flat : t ∈ flat p ↔ ∀ x ∈ t, p x := Iff.rfl

@[simp] theorem mem_ne : t ∈ (ne : TeamProperty α) ↔ t.Nonempty := Iff.rfl

@[simp] theorem mem_nec : t ∈ nec R P ↔ ∀ x ∈ t, R x ∈ P := Iff.rfl

@[simp] theorem mem_poss : t ∈ poss R P ↔ ∀ x ∈ t, ∃ s ⊆ R x, s.Nonempty ∧ s ∈ P :=
  forall₂_congr fun _ _ ↦
    ⟨fun ⟨s, ⟨hP, hne⟩, hs⟩ ↦ ⟨s, hs, hne, hP⟩, fun ⟨s, hs, hne, hP⟩ ↦ ⟨s, ⟨hP, hne⟩, hs⟩⟩

@[simp] theorem mem_possWitness :
    t ∈ possWitness R P ↔ ∃ Y, (∀ x ∈ t, ∃ y ∈ Y, y ∈ R x) ∧ Y ∈ P := Iff.rfl

instance flat.instDecidableMem [DecidablePred p] (t : Finset α) : Decidable (t ∈ flat p) :=
  Finset.decidableDforallFinset

instance ne.instDecidableMem (t : Finset α) : Decidable (t ∈ (ne : TeamProperty α)) :=
  inferInstanceAs (Decidable t.Nonempty)

instance nec.instDecidableMem (R : α → Finset α) (P : TeamProperty α) [DecidablePred (· ∈ P)]
    (t : Finset α) : Decidable (t ∈ nec R P) :=
  inferInstanceAs (Decidable (∀ x ∈ t, R x ∈ P))

theorem isFlat_flat (p : α → Prop) : IsFlat (flat p) := fun t ↦ by simp

theorem ordConnected_ne : (ne : TeamProperty α).OrdConnected := by
  rw [Set.ordConnected_iff]
  intro s hs u _ _ t ht
  exact hs.mono ht.1

theorem isLowerSet_singleton_empty : IsLowerSet ({∅} : TeamProperty α) := by
  intro s t hts hs
  rw [Set.mem_singleton_iff] at hs ⊢
  exact Finset.subset_empty.mp (hs ▸ hts)

theorem ordConnected_singleton_empty : ({∅} : TeamProperty α).OrdConnected :=
  isLowerSet_singleton_empty.ordConnected

theorem isLowerSet_possWitness (R : α → Finset α) (P : TeamProperty α) :
    IsLowerSet (possWitness R P) := by
  rintro s t hts ⟨Y, hY, hYP⟩
  exact ⟨Y, fun x hx ↦ hY x (hts hx), hYP⟩

theorem empty_mem_possWitness (hP : ∅ ∈ P) : ∅ ∈ possWitness R P :=
  ⟨∅, fun _ hx ↦ absurd hx (Finset.notMem_empty _), hP⟩

theorem flat_inter (p q : α → Prop) : flat p ∩ flat q = flat fun x ↦ p x ∧ q x :=
  Set.ext fun _ ↦ by simp [flat, forall_and]

theorem exists_nonempty_subset_forall_iff (u : Finset α) (p : α → Prop) :
    (∃ t ⊆ u, t.Nonempty ∧ ∀ x ∈ t, p x) ↔ ∃ x ∈ u, p x where
  mp := fun ⟨_, htu, ⟨x, hx⟩, h⟩ ↦ ⟨x, htu hx, h x hx⟩
  mpr := fun ⟨x, hxu, hx⟩ ↦
    ⟨{x}, Finset.singleton_subset_iff.mpr hxu, Finset.singleton_nonempty x,
      fun _ hy ↦ Finset.mem_singleton.mp hy ▸ hx⟩

theorem poss_flat (R : α → Finset α) (p : α → Prop) :
    poss R (flat p) = flat fun x ↦ ∃ y ∈ R x, p y :=
  Set.ext fun _ ↦ mem_poss.trans (forall₂_congr fun x _ ↦ exists_nonempty_subset_forall_iff (R x) p)

theorem nec_flat (R : α → Finset α) (p : α → Prop) :
    nec R (flat p) = flat fun x ↦ ∀ y ∈ R x, p y := rfl

/-! ### Split and image connectives -/

variable [DecidableEq α] {Q : TeamProperty α}

/-- The union of the successor sets of a team's points, `t ↦ t.biUnion R`, as a `SupBotHom`. -/
def biUnionHom {β : Type*} [DecidableEq β] (R : α → Finset β) :
    SupBotHom (Finset α) (Finset β) where
  toFun t := t.biUnion R
  map_sup' _ _ := Finset.union_biUnion
  map_bot' := Finset.biUnion_empty

@[simp] theorem biUnionHom_apply {β : Type*} [DecidableEq β] (R : α → Finset β) (t : Finset α) :
    biUnionHom R t = t.biUnion R := rfl

/-- The necessity modality of modal dependence logic holds of a team when the union of the
successor sets of its points is in `P` ([vaananen-2008] clause (T9), p. 245). -/
def necImage (R : α → Finset α) (P : TeamProperty α) : TeamProperty α :=
  biUnionHom R ⁻¹' P

/-- The lax possibility modality of modal inclusion logic holds of a team when some set of
successors of its points is in `P` and contains a successor of each point
([anttila-haggblom-yang-2025] Definition 2.2). -/
def possLax (R : α → Finset α) (P : TeamProperty α) : TeamProperty α :=
  {t | ∃ S ⊆ t.biUnion R, (∀ x ∈ t, ∃ y ∈ S, y ∈ R x) ∧ S ∈ P}

@[simp] theorem mem_necImage : t ∈ necImage R P ↔ t.biUnion R ∈ P := Iff.rfl

@[simp] theorem mem_possLax :
    t ∈ possLax R P ↔ ∃ S ⊆ t.biUnion R, (∀ x ∈ t, ∃ y ∈ S, y ∈ R x) ∧ S ∈ P := Iff.rfl

instance poss.instDecidableMem (R : α → Finset α) (P : TeamProperty α)
    [DecidablePred (· ∈ P)] (t : Finset α) : Decidable (t ∈ poss R P) :=
  decidable_of_iff (∀ x ∈ t, ∃ s ∈ (R x).powerset, s.Nonempty ∧ s ∈ P) <| by
    simp only [mem_poss, Finset.mem_powerset]

instance possWitness.instDecidableMem [Fintype α] (R : α → Finset α) (P : TeamProperty α)
    [DecidablePred (· ∈ P)] (t : Finset α) : Decidable (t ∈ possWitness R P) :=
  inferInstanceAs (Decidable (∃ Y, (∀ x ∈ t, ∃ y ∈ Y, y ∈ R x) ∧ Y ∈ P))

instance necImage.instDecidableMem (R : α → Finset α) (P : TeamProperty α)
    [DecidablePred (· ∈ P)] (t : Finset α) : Decidable (t ∈ necImage R P) :=
  inferInstanceAs (Decidable (t.biUnion R ∈ P))

instance possLax.instDecidableMem [Fintype α] (R : α → Finset α) (P : TeamProperty α)
    [DecidablePred (· ∈ P)] (t : Finset α) : Decidable (t ∈ possLax R P) :=
  inferInstanceAs (Decidable (∃ S ⊆ t.biUnion R, (∀ x ∈ t, ∃ y ∈ S, y ∈ R x) ∧ S ∈ P))

/-! ### Flat properties -/

theorem isLowerSet_flat (p : α → Prop) : IsLowerSet (flat p) := (isFlat_flat p).isLowerSet

theorem supClosed_flat (p : α → Prop) : SupClosed (flat p) := (isFlat_flat p).supClosed

theorem empty_mem_flat (p : α → Prop) : ∅ ∈ flat p := (isFlat_flat p).empty_mem

theorem ordConnected_flat (p : α → Prop) : (flat p).OrdConnected := (isFlat_flat p).ordConnected

/-! ### The non-emptiness atom -/

theorem supClosed_ne : SupClosed (ne : TeamProperty α) := by
  intro s hs t _
  exact hs.mono Finset.subset_union_left

theorem supClosed_singleton_empty : SupClosed ({∅} : TeamProperty α) := by
  intro s hs t ht
  rw [Set.mem_singleton_iff] at hs ht ⊢
  rw [hs, ht]
  exact sup_idem _

/-! ### The modalities of dependence and inclusion logic -/

theorem _root_.SupClosed.possWitness (hP : SupClosed P) : SupClosed (possWitness R P) := by
  rintro s ⟨Y, hY, hYP⟩ t ⟨Z, hZ, hZP⟩
  refine ⟨Y ∪ Z, fun x hx ↦ ?_, hP hYP hZP⟩
  rcases Finset.mem_union.mp hx with h | h
  · exact (hY x h).imp fun _ ⟨hy, hr⟩ ↦ ⟨Finset.mem_union_left _ hy, hr⟩
  · exact (hZ x h).imp fun _ ⟨hz, hr⟩ ↦ ⟨Finset.mem_union_right _ hz, hr⟩

theorem _root_.IsLowerSet.necImage (hP : IsLowerSet P) : IsLowerSet (necImage R P) :=
  hP.preimage (OrderHomClass.mono (biUnionHom R))

theorem _root_.SupClosed.necImage (hP : SupClosed P) : SupClosed (necImage R P) :=
  hP.preimage (biUnionHom R)

theorem empty_mem_necImage (hP : ∅ ∈ P) : ∅ ∈ necImage R P :=
  show biUnionHom R ⊥ ∈ P from (map_bot (biUnionHom R)).symm ▸ hP

theorem _root_.IsLowerSet.possLax (hP : IsLowerSet P) : IsLowerSet (possLax R P) := by
  rintro s t hts ⟨S, -, hS, hSP⟩
  refine ⟨S.filter (· ∈ t.biUnion R), fun _ hy ↦ (Finset.mem_filter.mp hy).2,
    fun x hx ↦ ?_, hP (Finset.filter_subset _ _) hSP⟩
  exact (hS x (hts hx)).imp fun y ⟨hy, hr⟩ ↦
    ⟨Finset.mem_filter.mpr ⟨hy, Finset.mem_biUnion.mpr ⟨x, hx, hr⟩⟩, hr⟩

theorem _root_.SupClosed.possLax (hP : SupClosed P) : SupClosed (possLax R P) := by
  rintro s ⟨S, hSs, hS, hSP⟩ t ⟨T, hTt, hT, hTP⟩
  refine ⟨S ∪ T, ?_, fun x hx ↦ ?_, hP hSP hTP⟩
  · show S ∪ T ⊆ (s ∪ t).biUnion R
    rw [Finset.union_biUnion]
    exact Finset.union_subset_union hSs hTt
  · rcases Finset.mem_union.mp hx with h | h
    · exact (hS x h).imp fun _ ⟨hy, hr⟩ ↦ ⟨Finset.mem_union_left _ hy, hr⟩
    · exact (hT x h).imp fun _ ⟨hy, hr⟩ ↦ ⟨Finset.mem_union_right _ hy, hr⟩

theorem empty_mem_possLax (hP : ∅ ∈ P) : ∅ ∈ possLax R P :=
  ⟨∅, Finset.empty_subset _, fun _ hx ↦ absurd hx (Finset.notMem_empty _), hP⟩

/-! ### `flat` commutes with split disjunction ([anttila-2021] Proposition 2.2.16) -/

theorem mem_flat_sups_flat : t ∈ flat p ⊻ flat q ↔ ∀ x ∈ t, p x ∨ q x where
  mp := fun ⟨_, h₁, _, h₂, hu⟩ x hx ↦ by
    subst hu
    exact (Finset.mem_union.mp hx).imp (h₁ x) (h₂ x)
  mpr h := by
    classical
    exact ⟨t.filter p, fun x hx ↦ (Finset.mem_filter.mp hx).2, t.filter (¬ p ·),
      fun x hx ↦ (h x (Finset.mem_filter.mp hx).1).resolve_left (Finset.mem_filter.mp hx).2,
      Finset.filter_union_filter_not_eq _ _⟩

theorem flat_sups_flat (p q : α → Prop) : flat p ⊻ flat q = flat fun x ↦ p x ∨ q x :=
  Set.ext fun _ ↦ mem_flat_sups_flat

theorem nec_union (R : α → Finset α) (P Q : TeamProperty α) :
    nec R (P ∪ Q) = nec R P ⊻ nec R Q := by
  rw [nec, nec, nec, flat_sups_flat]; rfl

/-- The flat possibility modality turns a union into a split disjunction. This is the law
behind `◇(φ ⩔ ψ) ≡ ◇φ ∨ ◇ψ` in [aloni-anttila-yang-2024]. -/
theorem poss_union (R : α → Finset α) (P Q : TeamProperty α) :
    poss R (P ∪ Q) = poss R P ⊻ poss R Q := by
  rw [poss, poss, poss, Set.union_inter_distrib_right, upperClosure_union, UpperSet.coe_inf,
    nec_union]

/-! ### `flat` commutes with the image modalities

On flat properties the modalities of dependence and inclusion logic agree with the flat ones. -/

theorem mem_possWitness_flat : t ∈ possWitness R (flat p) ↔ ∀ x ∈ t, ∃ y ∈ R x, p y where
  mp := fun ⟨_, hY, hYp⟩ x hx ↦ (hY x hx).imp fun _ ⟨hyY, hyR⟩ ↦ ⟨hyR, hYp _ hyY⟩
  mpr h := by
    classical
    exact ⟨(t.biUnion R).filter p, fun x hx ↦ (h x hx).imp fun _ ⟨hyR, hy⟩ ↦
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨x, hx, hyR⟩, hy⟩, hyR⟩,
      fun _ hy ↦ (Finset.mem_filter.mp hy).2⟩

theorem possWitness_flat (R : α → Finset α) (p : α → Prop) :
    possWitness R (flat p) = flat fun x ↦ ∃ y ∈ R x, p y :=
  Set.ext fun _ ↦ mem_possWitness_flat

theorem mem_possLax_flat : t ∈ possLax R (flat p) ↔ ∀ x ∈ t, ∃ y ∈ R x, p y where
  mp := fun ⟨_, _, hS, hSp⟩ x hx ↦ (hS x hx).imp fun _ ⟨hyS, hyR⟩ ↦ ⟨hyR, hSp _ hyS⟩
  mpr h := by
    classical
    exact ⟨(t.biUnion R).filter p, Finset.filter_subset _ _, fun x hx ↦ (h x hx).imp
      fun _ ⟨hyR, hy⟩ ↦ ⟨Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨x, hx, hyR⟩, hy⟩, hyR⟩,
      fun _ hy ↦ (Finset.mem_filter.mp hy).2⟩

theorem possLax_flat (R : α → Finset α) (p : α → Prop) :
    possLax R (flat p) = flat fun x ↦ ∃ y ∈ R x, p y :=
  Set.ext fun _ ↦ mem_possLax_flat

theorem mem_necImage_flat : t ∈ necImage R (flat p) ↔ ∀ x ∈ t, ∀ y ∈ R x, p y := by
  simp only [mem_necImage, mem_flat, Finset.mem_biUnion, forall_exists_index, and_imp]
  exact ⟨fun h x hx y hy ↦ h y x hx hy, fun h y x hx hy ↦ h x hx y hy⟩

theorem necImage_flat (R : α → Finset α) (p : α → Prop) :
    necImage R (flat p) = flat fun x ↦ ∀ y ∈ R x, p y :=
  Set.ext fun _ ↦ mem_necImage_flat

/-! ### Bilateral connectives

A bilateral logic gives a formula a support and an anti-support property, a pair in
`TeamProperty α ⊙ TeamProperty α` whose negation `ᶜ` swaps the two. Conjunction intersects the
supports and splits the anti-supports, and disjunction is its De Morgan dual. A modality acts on
the two coordinates by a pair of operations (`Bilattice.Product.map`). A classical formula means
the flat pair of its truth, and each connective sends flat pairs to flat pairs. -/

open scoped Bilattice
open Bilattice.Product (map)

/-- A team supports `A ∧ B` when it supports both, and anti-supports it when it splits into a part
anti-supporting each. -/
def conj (A B : TeamProperty α ⊙ TeamProperty α) : TeamProperty α ⊙ TeamProperty α :=
  .mk (A.pro ∩ B.pro) (A.con ⊻ B.con)

/-- Split disjunction `A ∨ B`, the De Morgan dual `¬(¬A ∧ ¬B)` of conjunction. -/
def disj (A B : TeamProperty α ⊙ TeamProperty α) : TeamProperty α ⊙ TeamProperty α :=
  (conj Aᶜ Bᶜ)ᶜ

/-- The flat pair of `p` is supported by the teams throughout which `p` holds and anti-supported
by those throughout which it fails. -/
def flatPair (p : α → Prop) : TeamProperty α ⊙ TeamProperty α :=
  .mk (flat p) (flat fun x ↦ ¬ p x)

section Flat

omit [DecidableEq α]

variable (p : α → Prop) (R : α → Finset α)

@[simp] theorem pro_flatPair : (flatPair p).pro = flat p := rfl
@[simp] theorem con_flatPair : (flatPair p).con = flat fun x ↦ ¬ p x := rfl

theorem compl_flatPair : (flatPair p)ᶜ = flatPair fun x ↦ ¬ p x :=
  Bilattice.Product.ext rfl <| congrArg flat <| funext fun _ ↦ propext not_not.symm

theorem map_poss_nec_flatPair :
    (flatPair p).map (poss R) (nec R) = flatPair fun x ↦ ∃ y ∈ R x, p y :=
  Bilattice.Product.ext (poss_flat R p) <| (nec_flat R fun x ↦ ¬ p x).trans <| by
    simp only [con_flatPair, not_exists, not_and]

end Flat

section Bilateral

variable (A B : TeamProperty α ⊙ TeamProperty α) (p q : α → Prop) (R : α → Finset α)

@[simp] theorem pro_conj : (conj A B).pro = A.pro ∩ B.pro := rfl
@[simp] theorem con_conj : (conj A B).con = A.con ⊻ B.con := rfl
@[simp] theorem pro_disj : (disj A B).pro = A.pro ⊻ B.pro := rfl
@[simp] theorem con_disj : (disj A B).con = A.con ∩ B.con := rfl
@[simp] theorem compl_conj : (conj A B)ᶜ = disj Aᶜ Bᶜ := rfl
@[simp] theorem compl_disj : (disj A B)ᶜ = conj Aᶜ Bᶜ := rfl

theorem conj_flatPair : conj (flatPair p) (flatPair q) = flatPair fun x ↦ p x ∧ q x :=
  Bilattice.Product.ext (flat_inter p q) <|
    (flat_sups_flat (fun x ↦ ¬ p x) fun x ↦ ¬ q x).trans <| by
      simp only [con_flatPair, not_and_or]

theorem disj_flatPair : disj (flatPair p) (flatPair q) = flatPair fun x ↦ p x ∨ q x :=
  Bilattice.Product.ext (flat_sups_flat p q) <|
    (flat_inter (fun x ↦ ¬ p x) fun x ↦ ¬ q x).trans <| by simp only [con_flatPair, not_or]

theorem map_possWitness_necImage_flatPair :
    (flatPair p).map (possWitness R) (necImage R) = flatPair fun x ↦ ∃ y ∈ R x, p y :=
  Bilattice.Product.ext (possWitness_flat R p) <| (necImage_flat R fun x ↦ ¬ p x).trans <| by
    simp only [con_flatPair, not_exists, not_and]

theorem map_possLax_necImage_flatPair :
    (flatPair p).map (possLax R) (necImage R) = flatPair fun x ↦ ∃ y ∈ R x, p y :=
  Bilattice.Product.ext (possLax_flat R p) <| (necImage_flat R fun x ↦ ¬ p x).trans <| by
    simp only [con_flatPair, not_exists, not_and]

end Bilateral

end Team
