module

public import Linglib.Semantics.Quantification.Lattice
public import Linglib.Semantics.Quantification.Counting
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Order.Atoms
public import Mathlib.Data.Sym.Card
public import Mathlib.Order.Sym2
public import Mathlib.Data.Fintype.Fin

/-!
# Keenan and Stavi (1986): A Semantic Characterization of Natural Language Determiners

This file formalizes Keenan and Stavi's Conservativity Theorem: the possible determiner
denotations, the Boolean closure of the denotations of a few simple determiners, are exactly the
conservative functions, those with `f R T ↔ f R (R ∩ T)`. The generators are the Appendix's two
individual-anchored determiners `Sₐ` and `Eₐ`, *John's one or more* and *John's zero or more*
when `a` is all John possesses, here derived as restrictions of *some* and *every* by the
singleton property of `a` (`someOf`, `allOf`); every conservative function is the join of the
atoms `atom p q` at the pairs where it holds, the atoms of the algebra are exactly these
(`isAtom_iff`), each atom is a meet of generators and their complements, and so the Boolean
subalgebra the generators generate is the conservative algebra (`closure_generators`). The
algebra is complete and atomic (the instance is in `Quantification/Lattice.lean`), so it is
isomorphic to the power set of its atoms; sorting the individuals into three cells counts the
atoms, and with `n` individuals there are `2 ^ 3 ^ n` conservative functions among the
`2 ^ 2 ^ 2n` functions from properties to sets of properties (`card_consDet`, `card_gq`,
PROP 4), 512 among 65,536 for two individuals.

Section 3.3 characterizes the determiners of existential-*there* sentences as the existential
functions, `f R T ↔ f (R ∩ T) univ`: *at least n* is one, *every* and *the n* are not, and the
class is closed under the Boolean operations (PROP 13). Section 3.4 isolates the cardinal
functions, deciding by the number of individuals in restrictor and scope: they are closed under
the Boolean operations and, given two individuals, properly included in the existential
functions (PROP 14), which are
in turn isomorphic as a Boolean algebra to the type ⟨1⟩ quantifiers through `f ↦ f(1)`
(PROP 15, `existentialOrderIso`), so number `2 ^ 2 ^ n`; the cardinal functions are the sets of
cardinalities up to `n` (`cardinalOrderIso`), so number `2 ^ (n + 1)`, and *no ... but John* is
existential without being cardinal. Section 3.5 defines the logical determiners as the
permutation-invariant conservative functions (114); they depend only on the sizes of the
restrictor and of its meet with the scope, form the algebra of sets of nested pairs of
cardinalities (`logicalOrderIso`), and number `2 ^ ((n + 1)(n + 2)/2)` (PROP 19), 64 among the
512 conservative functions on two individuals. Footnote 10's characterization closes the
circle: on a finite universe the cardinal functions are exactly the existential logical ones
(`cardinalSubalgebra_eq_inf`).

## Implementation notes

Conservativity, the existential property and quantity invariance are the substrate's
`Conservative`, `Existential` and `QuantityInvariant`, the conservative algebra is `ConsDet`
with its `CompleteAtomicBooleanAlgebra` instance, and the counts are `Nat.card`s over a
`Fintype` universe derived from mathlib's representation theorem
`CompleteAtomicBooleanAlgebra.toSetOfIsAtom`. `Cardinal` is stated with `Nat.card`, which is by
definition the `Set.ncard` the counting quantifiers count with.
Canonical witnesses of each size are initial segments of a fixed enumeration (`segment`), which
nest, unlike arbitrarily chosen subsets. `BooleanSubalgebra.closure` is finitary, so
`closure_generators` carries `[Finite α]`; the paper closes under arbitrary meets and joins, and
on an infinite universe the finitary closure is strictly smaller than the conservative algebra.

## Errata

* PROP 14(c) and its gloss say that the cardinal functions are always a proper subset of the
  existential ones. On a universe of one individual the two classes coincide
  (`cardinalSubalgebra_eq_of_subsingleton`), so `cardinalSubalgebra_lt` assumes two
  individuals.

## TODO

* Footnote 10(b): on an infinite universe `CARD ⊊ E-Det ⊓ LOG`, witnessed by the paper's `f₀`.
* The (In)effability Theorems of Section 3.6, which quantify over the English determiner
  expressions.

## References

* [keenan-stavi-1986]
-/

@[expose] public section

namespace KeenanStavi1986

open Quantifier Quantifier.Det BooleanSubalgebra

variable {α : Type*}

/-! ### The Conservativity Theorem (Section 2.5 and the Appendix) -/

/-- `Sₐ` restricts *some* by the singleton property of `a`; it is the Appendix's denotation of
*John's one or more* when `a` is all John possesses. -/
def someOf (a : α) : Det α := adjRestrict Det.some {a}

@[simp] theorem someOf_apply (a : α) (R T : Set α) : someOf a R T ↔ a ∈ R ∧ a ∈ T :=
  ⟨fun ⟨_, ⟨hR, rfl⟩, hT⟩ ↦ ⟨hR, hT⟩, fun ⟨hR, hT⟩ ↦ ⟨a, ⟨hR, rfl⟩, hT⟩⟩

/-- `Eₐ` restricts *every* by the singleton property of `a`; it is the Appendix's denotation of
*John's zero or more*. -/
def allOf (a : α) : Det α := adjRestrict every {a}

@[simp] theorem allOf_apply (a : α) (R T : Set α) : allOf a R T ↔ (a ∈ R → a ∈ T) :=
  ⟨fun h hR ↦ h ⟨hR, rfl⟩, fun h _ ⟨hR, rfl⟩ ↦ h hR⟩

theorem conservative_someOf (a : α) : Conservative (someOf a) :=
  conservative_some.adjRestrict {a}

theorem conservative_allOf (a : α) : Conservative (allOf a) :=
  conservative_every.adjRestrict {a}

theorem existential_someOf (a : α) : Existential (someOf a) :=
  existential_some.adjRestrict {a}

/-- The generators of the conservative algebra are the `Sₐ` and `Eₐ` for every individual. -/
def generators (α : Type*) : Set (Det α) := Set.range someOf ∪ Set.range allOf

theorem conservative_of_mem_generators {q : Det α} (hq : q ∈ generators α) : Conservative q := by
  obtain ⟨a, rfl⟩ | ⟨a, rfl⟩ := hq
  exacts [conservative_someOf a, conservative_allOf a]

/-- The Appendix's atom `f_{pq}` of the conservative algebra holds at the restrictor `p` and
exactly the scopes meeting `p` in `q`. -/
def atom (p q : Set α) : Det α := fun R T ↦ R = p ∧ R ∩ T = q

theorem conservative_atom (p q : Set α) : Conservative (atom p q) := fun R T ↦ by
  show R = p ∧ R ∩ T = q ↔ R = p ∧ R ∩ (R ∩ T) = q
  rw [← Set.inter_assoc, Set.inter_self]

theorem atom_le_iff {f : Det α} (hf : Conservative f) {p q : Set α} (h : q ⊆ p) :
    atom p q ≤ f ↔ f p q :=
  ⟨fun hle ↦ hle p q ⟨rfl, Set.inter_eq_right.mpr h⟩, fun hpq R T ⟨hR, hT⟩ ↦ by
    subst hR; subst hT; exact (hf _ _).mpr hpq⟩

theorem isAtom_atom {p q : Set α} (h : q ⊆ p) :
    IsAtom (⟨atom p q, conservative_atom p q⟩ : ConsDet α) := by
  refine ⟨fun hbot ↦ ?_, fun b hb ↦ ?_⟩
  · exact (congrArg (fun f : ConsDet α ↦ f.1 p q) hbot).mp ⟨rfl, Set.inter_eq_right.mpr h⟩
  · by_contra hne
    obtain ⟨R, T, hRT⟩ : ∃ R T, b.1 R T := by
      by_contra hall
      push Not at hall
      exact hne (Subtype.ext (funext₂ fun R T ↦ propext ⟨hall R T, False.elim⟩))
    have hle : b.1 ≤ atom p q := hb.le
    obtain ⟨rfl, rfl⟩ := hle R T hRT
    refine hb.not_ge fun R' T' ⟨hR', hT'⟩ ↦ ?_
    subst hR'
    exact (b.2.iff_of_inter_eq hT').mpr hRT

/-- The atoms of the conservative algebra are exactly the `atom p q` with `q ⊆ p`
(the Appendix). -/
theorem isAtom_iff {f : ConsDet α} :
    IsAtom f ↔ ∃ p q, q ⊆ p ∧ f.1 = atom p q := by
  constructor
  · intro hf
    obtain ⟨R, T, hRT⟩ : ∃ R T, f.1 R T := by
      by_contra hall
      push Not at hall
      exact hf.1 (Subtype.ext (funext₂ fun R T ↦ propext ⟨hall R T, False.elim⟩))
    refine ⟨R, R ∩ T, Set.inter_subset_left, ?_⟩
    have hle : (⟨atom R (R ∩ T), conservative_atom R (R ∩ T)⟩ : ConsDet α) ≤ f :=
      (atom_le_iff f.2 Set.inter_subset_left).mpr ((f.2 R T).mp hRT)
    have hne : (⟨atom R (R ∩ T), conservative_atom R (R ∩ T)⟩ : ConsDet α) ≠ ⊥ := fun hbot ↦
      (congrArg (fun g : ConsDet α ↦ g.1 R (R ∩ T)) hbot).mp
        ⟨rfl, Set.inter_eq_right.mpr Set.inter_subset_left⟩
    exact congrArg Subtype.val ((hf.le_iff.mp hle).resolve_left hne).symm
  · rintro ⟨p, q, hqp, hf⟩
    have hfe : f = ⟨atom p q, conservative_atom p q⟩ := Subtype.ext hf
    exact hfe ▸ isAtom_atom hqp

theorem eq_iSup_atom {f : Det α} (hf : Conservative f) :
    f = ⨆ pq ∈ {pq : Set α × Set α | f pq.1 pq.2}, atom pq.1 pq.2 := by
  funext R T
  apply propext
  simp only [iSup_apply, iSup_Prop_eq, exists_prop, Set.mem_ofPred_eq, Prod.exists, atom]
  constructor
  · exact fun h ↦ ⟨R, R ∩ T, (hf R T).mp h, rfl, rfl⟩
  · rintro ⟨p, q, h, rfl, rfl⟩
    exact (hf _ _).mpr h

theorem atom_eq_iInf (p q : Set α) :
    atom p q = (⨅ a ∈ q, someOf a) ⊓ (⨅ a ∈ p \ q, (someOf a)ᶜ ⊓ (allOf a)ᶜ) ⊓
      ⨅ a ∈ pᶜ, (someOf a)ᶜ ⊓ allOf a := by
  funext R T
  apply propext
  simp only [atom, Pi.inf_apply, iInf_apply, iInf_Prop_eq, Pi.compl_apply, compl_iff_not,
    inf_Prop_eq, Set.mem_sdiff, Set.mem_compl_iff, someOf_apply, allOf_apply]
  constructor
  · rintro ⟨rfl, rfl⟩
    exact ⟨⟨fun _ h ↦ h, fun _ ⟨hR, hq⟩ ↦ ⟨hq, fun h ↦ hq ⟨hR, h hR⟩⟩⟩,
      fun _ hR ↦ ⟨fun h ↦ hR h.1, fun h ↦ absurd h hR⟩⟩
  · rintro ⟨⟨hq, hp⟩, hn⟩
    refine ⟨Set.ext fun a ↦ ?_, Set.ext fun a ↦ ?_⟩
    · by_cases hpa : a ∈ p
      · by_cases hqa : a ∈ q
        · exact iff_of_true (hq a hqa).1 hpa
        · exact iff_of_true (of_not_imp (hp a ⟨hpa, hqa⟩).2) hpa
      · exact iff_of_false (fun hR ↦ (hn a hpa).1 ⟨hR, (hn a hpa).2 hR⟩) hpa
    · by_cases hqa : a ∈ q
      · exact iff_of_true (hq a hqa) hqa
      · by_cases hpa : a ∈ p
        · exact iff_of_false (hp a ⟨hpa, hqa⟩).1 hqa
        · exact iff_of_false (hn a hpa).1 hqa

theorem atom_mem_closure [Finite α] (p q : Set α) :
    atom p q ∈ closure (generators α) := by
  rw [atom_eq_iInf]
  refine inf_mem (inf_mem (biInf_mem (Set.toFinite _) fun a _ ↦ ?_)
    (biInf_mem (Set.toFinite _) fun a _ ↦ ?_)) (biInf_mem (Set.toFinite _) fun a _ ↦ ?_)
  · exact subset_closure (Or.inl ⟨a, rfl⟩)
  · exact inf_mem (compl_mem (subset_closure (Or.inl ⟨a, rfl⟩)))
      (compl_mem (subset_closure (Or.inr ⟨a, rfl⟩)))
  · exact inf_mem (compl_mem (subset_closure (Or.inl ⟨a, rfl⟩))) (subset_closure (Or.inr ⟨a, rfl⟩))

theorem closure_generators [Finite α] : closure (generators α) = conservativeSubalgebra := by
  refine le_antisymm (closure_le.2 fun q hq ↦ conservative_of_mem_generators hq) fun f hf ↦ ?_
  rw [eq_iSup_atom (mem_conservativeSubalgebra.mp hf)]
  exact biSup_mem (Set.toFinite _) fun pq _ ↦ atom_mem_closure pq.1 pq.2

/-! ### Counting the conservative functions (Section 2.7 and the Appendix) -/

/-- The atoms are indexed by the restrictor–scope pairs with the scope inside the restrictor. -/
abbrev Nested (α : Type*) := {pq : Set α × Set α // pq.2 ⊆ pq.1}

theorem atom_injective : Function.Injective fun pq : Nested α ↦ atom pq.1.1 pq.1.2 := by
  rintro ⟨⟨p, q⟩, hpq⟩ ⟨⟨p', q'⟩, hpq'⟩ h
  have h' : atom p q = atom p' q' := h
  obtain ⟨rfl, hq⟩ : atom p' q' p q := h' ▸ ⟨rfl, Set.inter_eq_right.mpr hpq⟩
  have hqq : q = q' := by rw [← hq, Set.inter_eq_right.mpr hpq]
  exact Subtype.ext (Prod.ext rfl hqq)

/-- The paper's index pairs are exactly mathlib's atoms of the conservative algebra. -/
noncomputable def atomEquiv : Nested α ≃ {f : ConsDet α // IsAtom f} :=
  Equiv.ofBijective
    (fun pq ↦ ⟨⟨atom pq.1.1 pq.1.2, conservative_atom _ _⟩, isAtom_atom pq.2⟩)
    ⟨fun _ _ h ↦ atom_injective (congrArg (fun f ↦ f.1.1) h), fun f ↦ by
      obtain ⟨p, q, hqp, hf⟩ := isAtom_iff.mp f.2
      exact ⟨⟨(p, q), hqp⟩, Subtype.ext (Subtype.ext hf.symm)⟩⟩

open Classical in
/-- A pair `q ⊆ p` sorts each individual into one of three cells, in `q`, in `p` but not `q`,
or outside `p`, and any sorting arises (the Appendix's coding `g_pq`). -/
noncomputable def nestedEquivFin3 : Nested α ≃ (α → Fin 3) where
  toFun pq x := if x ∈ pq.1.2 then 2 else if x ∈ pq.1.1 then 1 else 0
  invFun c := ⟨({x | c x ≠ 0}, {x | c x = 2}), fun x hx ↦ by
    show c x ≠ 0
    rw [show c x = 2 from hx]
    decide⟩
  left_inv := fun ⟨⟨p, q⟩, h⟩ ↦ by
    refine Subtype.ext (Prod.ext (Set.ext fun x ↦ ?_) (Set.ext fun x ↦ ?_))
    · by_cases hq : x ∈ q
      · have hp : x ∈ p := h hq
        simp [hq, hp]
      · by_cases hp : x ∈ p <;> simp [hq, hp]
    · by_cases hq : x ∈ q
      · simp [hq]
      · by_cases hp : x ∈ p <;> simp +decide [hq, hp]
  right_inv c := funext fun x ↦ by
    dsimp only
    by_cases h2 : c x = 2
    · simp [h2]
    · by_cases h0 : c x = 0
      · simp [h0]
      · have h1 : c x = 1 := by omega
        simp +decide [h1]

theorem card_nested [Fintype α] : Nat.card (Nested α) = 3 ^ Fintype.card α := by
  rw [Nat.card_congr nestedEquivFin3, Nat.card_fun, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card, Fintype.card_fin]

theorem card_isAtom [Fintype α] :
    Nat.card {f : ConsDet α // IsAtom f} = 3 ^ Fintype.card α := by
  rw [← Nat.card_congr (atomEquiv (α := α)), card_nested]

theorem card_consDet [Fintype α] : Nat.card (ConsDet α) = 2 ^ 3 ^ Fintype.card α := by
  rw [Nat.card_congr CompleteAtomicBooleanAlgebra.toSetOfIsAtom.toEquiv]
  change Nat.card ({f : ConsDet α // IsAtom f} → Prop) = _
  rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Prop), Fintype.card_prop, card_isAtom]

theorem mk_consDet :
    _root_.Cardinal.mk (ConsDet α) =
      (2 : _root_.Cardinal) ^ (3 : _root_.Cardinal) ^ _root_.Cardinal.mk α := by
  rw [_root_.Cardinal.mk_congr CompleteAtomicBooleanAlgebra.toSetOfIsAtom.toEquiv]
  change _root_.Cardinal.mk (Set {f : ConsDet α // IsAtom f}) = _
  rw [_root_.Cardinal.mk_set, _root_.Cardinal.mk_congr (atomEquiv (α := α)).symm,
    _root_.Cardinal.mk_congr nestedEquivFin3, _root_.Cardinal.mk_arrow,
    _root_.Cardinal.mk_fin, _root_.Cardinal.lift_natCast, _root_.Cardinal.lift_uzero]
  norm_num

theorem card_gq [Fintype α] : Nat.card (Det α) = 2 ^ 2 ^ (2 * Fintype.card α) := by
  rw [Nat.card_fun, Nat.card_fun, Nat.card_eq_fintype_card (α := Prop), Fintype.card_prop,
    Nat.card_eq_fintype_card (α := Set α), Fintype.card_set, ← pow_mul, ← pow_add, ← two_mul]

/-! ### Canonical witnesses of each size

Initial segments of a fixed enumeration of the universe, nested by construction, standing in
for the paper's freely chosen sets of `k` individuals. -/

section Segment

variable [Fintype α]

/-- `segment k` is the set of the first `k` individuals under a fixed enumeration of the
universe. -/
def segment (k : ℕ) : Set α := {x | ((Fintype.equivFin α) x : ℕ) < k}

theorem segment_mono {k m : ℕ} (h : k ≤ m) : segment (α := α) k ⊆ segment m :=
  fun _ hx ↦ lt_of_lt_of_le hx h

theorem card_segment {k : ℕ} (hk : k ≤ Fintype.card α) : Nat.card (segment (α := α) k) = k := by
  have e : segment (α := α) k ≃ {i : Fin (Fintype.card α) // (i : ℕ) < k} :=
    (Fintype.equivFin α).subtypeEquiv fun x ↦ Iff.rfl
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype,
    Fin.card_filter_val_lt]
  omega

theorem card_segment_inter {m k : ℕ} (h : m ≤ k) (hm : m ≤ Fintype.card α) :
    Nat.card ↥(segment (α := α) k ∩ segment m) = m := by
  rw [Set.inter_eq_right.mpr (segment_mono h)]
  exact card_segment hm

theorem card_subtype_le_card (P : α → Prop) : Nat.card {x // P x} ≤ Fintype.card α :=
  (Nat.card_le_card_of_injective _ Subtype.val_injective).trans_eq Nat.card_eq_fintype_card

theorem card_inter_le_card_left (R T : Set α) : Nat.card ↥(R ∩ T) ≤ Nat.card R :=
  Nat.card_le_card_of_injective _ (Set.inclusion_injective Set.inter_subset_left)

end Segment

/-! ### Existential determiners (Section 3.3) -/

/-- The existential functions are closed under the Boolean operations (PROP 13). -/
def existentialSubalgebra : BooleanSubalgebra (Det α) where
  carrier := {f | Existential f}
  supClosed' _ hf _ hg R T := or_congr (hf R T) (hg R T)
  infClosed' _ hf _ hg R T := and_congr (hf R T) (hg R T)
  compl_mem' hf R T := not_congr (hf R T)
  bot_mem' _ _ := Iff.rfl

@[simp] theorem mem_existentialSubalgebra {f : Det α} :
    f ∈ existentialSubalgebra ↔ Existential f :=
  Iff.rfl

theorem existential_iSup {ι : Sort*} {f : ι → Det α} (hf : ∀ i, Existential (f i)) :
    Existential (⨆ i, f i) := fun R T ↦ by
  simp only [iSup_apply, iSup_Prop_eq]
  exact exists_congr fun i ↦ hf i R T

theorem existential_iInf {ι : Sort*} {f : ι → Det α} (hf : ∀ i, Existential (f i)) :
    Existential (⨅ i, f i) := fun R T ↦ by
  simp only [iInf_apply, iInf_Prop_eq]
  exact forall_congr' fun i ↦ hf i R T

theorem existentialSubalgebra_le :
    existentialSubalgebra ≤ (conservativeSubalgebra : BooleanSubalgebra (Det α)) :=
  fun _ hf ↦ hf.conservative

-- (99), (100)
theorem existential_atLeast (n : ℕ) : Existential (atLeast (α := α) n) := fun R T ↦ by
  simp only [atLeast_apply, Set.inter_univ]

-- Section 3.3
theorem not_existential_every [Nonempty α] : ¬ Existential (every : Det α) := fun h ↦ by
  obtain ⟨b⟩ := ‹Nonempty α›
  exact absurd ((h Set.univ {b}ᶜ).mpr fun _ _ ↦ trivial) fun h' ↦ h' (Set.mem_univ b) rfl

/-- *the n* is the universal on a restrictor of exactly `n` individuals ((43)); *both* is
`theN 2`. -/
def theN (n : ℕ) : Det α := every ⊓ fun R _ ↦ R.ncard = n

theorem theN_apply (n : ℕ) (R T : Set α) : theN n R T ↔ every R T ∧ R.ncard = n :=
  Iff.rfl

theorem theN_two_eq_both [Finite α] : theN 2 = (both : Det α) := by
  funext R T
  have hd := Set.ncard_inter_add_ncard_sdiff_eq_ncard R T
  have he : every R T ↔ (R \ T).ncard = 0 := by rw [every_eq_toDet_all]; rfl
  apply propext
  rw [theN_apply, he]
  change _ ↔ (R \ T).ncard = 0 ∧ (R ∩ T).ncard = 2
  omega

-- Section 3.3
theorem not_existential_theN [Fintype α] {n : ℕ} (hn : n < Fintype.card α) :
    ¬ Existential (theN (α := α) n) := fun h ↦ by
  have h1 : theN (α := α) n (Set.univ ∩ segment n) Set.univ := by
    rw [theN_apply, Set.univ_inter]
    exact ⟨fun _ _ ↦ trivial, card_segment hn.le⟩
  have hcard := ((theN_apply _ _ _).1 ((h Set.univ (segment n)).mpr h1)).2
  rw [Set.ncard_univ, Nat.card_eq_fintype_card] at hcard
  omega

/-- *no ... but J* holds when restrictor and scope meet in exactly the individual `a` ((42)). -/
def noBut (a : α) : Det α := fun R T ↦ R ∩ T = {a}

-- (103)
theorem existential_noBut (a : α) : Existential (noBut a) := fun R T ↦ by
  show R ∩ T = {a} ↔ R ∩ T ∩ Set.univ = {a}
  rw [Set.inter_univ]

/-- An existential function is determined by its set of properties `f(1)`, and the
correspondence is an isomorphism onto the type ⟨1⟩ quantifiers, the possible NP denotations
(PROP 15). -/
noncomputable def existentialOrderIso : existentialSubalgebra (α := α) ≃o Quantifier α :=
  Equiv.toOrderIso
    { toFun := fun f T ↦ f.1 Set.univ T
      invFun := fun g ↦ ⟨fun R T ↦ g (R ∩ T), fun R T ↦
        Iff.of_eq (congrArg g (Set.inter_univ _).symm)⟩
      left_inv := fun f ↦ Subtype.ext (funext₂ fun R T ↦ propext ((f.2 Set.univ (R ∩ T)).trans
        (by
          show f.1 (Set.univ ∩ (R ∩ T)) Set.univ ↔ f.1 R T
          rw [Set.univ_inter]
          exact (f.2 R T).symm)))
      right_inv := fun g ↦ funext fun T ↦ congrArg g (Set.univ_inter T) }
    (fun _ _ h T hT ↦ h Set.univ T hT) (fun _ _ h R T hx ↦ h _ hx)

theorem card_existential [Fintype α] :
    Nat.card (existentialSubalgebra (α := α)) = 2 ^ 2 ^ Fintype.card α := by
  rw [Nat.card_congr existentialOrderIso.toEquiv, Nat.card_fun,
    Nat.card_eq_fintype_card (α := Prop), Fintype.card_prop,
    Nat.card_eq_fintype_card (α := Set α), Fintype.card_set]

/-! ### Cardinal determiners (Section 3.4) -/

/-- A cardinal function decides by the number of individuals in restrictor and scope ((102)). -/
def Cardinal (f : Det α) : Prop :=
  ∀ R T R' T' : Set α, Nat.card ↥(R ∩ T) = Nat.card ↥(R' ∩ T') → (f R T ↔ f R' T')

/-- The cardinal functions are closed under the Boolean operations (PROP 14(a)). -/
def cardinalSubalgebra : BooleanSubalgebra (Det α) where
  carrier := {f | Cardinal f}
  supClosed' _ hf _ hg R T R' T' h := or_congr (hf R T R' T' h) (hg R T R' T' h)
  infClosed' _ hf _ hg R T R' T' h := and_congr (hf R T R' T' h) (hg R T R' T' h)
  compl_mem' hf R T R' T' h := not_congr (hf R T R' T' h)
  bot_mem' _ _ _ _ _ := Iff.rfl

@[simp] theorem mem_cardinalSubalgebra {f : Det α} : f ∈ cardinalSubalgebra ↔ Cardinal f :=
  Iff.rfl

theorem Cardinal.existential {f : Det α} (hf : Cardinal f) : Existential f := fun R T ↦
  hf R T _ _ (by rw [Set.inter_univ])

theorem Cardinal.quantityInvariant {f : Det α} (hf : Cardinal f) : QuantityInvariant f :=
  fun σ _ _ ↦ hf _ _ _ _ (Nat.card_congr (σ.subtypeEquiv fun _ ↦ Iff.rfl))

theorem cardinalSubalgebra_le :
    cardinalSubalgebra ≤ (existentialSubalgebra : BooleanSubalgebra (Det α)) :=
  fun _ hf ↦ Cardinal.existential hf

theorem cardinal_atLeast (n : ℕ) : Cardinal (atLeast (α := α) n) :=
  fun _ _ _ _ h ↦ Iff.of_eq (congrArg (n ≤ ·) h)

theorem cardinal_exactly (n : ℕ) : Cardinal (exactly (α := α) n) :=
  fun _ _ _ _ h ↦ Iff.of_eq (congrArg (· = n) h)

private theorem card_singleton_inter (c : α) : Nat.card ↥({c} ∩ {c} : Set α) = 1 := by
  rw [Set.inter_self]
  exact Nat.card_unique

theorem cardinal_some [Fintype α] : Cardinal (Det.some : Det α) := by
  rw [some_eq_atLeast_one]
  exact cardinal_atLeast 1

theorem not_cardinal_noBut {a b : α} (hab : a ≠ b) : ¬ Cardinal (noBut a) := fun h ↦ by
  have key : ({b} : Set α) = {a} := by
    have h1 : ({b} : Set α) ∩ {b} = {a} :=
      (h {a} {a} {b} {b} ((card_singleton_inter a).trans (card_singleton_inter b).symm)).mp
        (Set.inter_self _)
    rwa [Set.inter_self] at h1
  exact hab (Set.singleton_injective key).symm

theorem not_cardinal_someOf {a b : α} (hab : a ≠ b) : ¬ Cardinal (someOf a) := fun h ↦ by
  have key := (h {a} {a} {b} {b}
    ((card_singleton_inter a).trans (card_singleton_inter b).symm)).mp
    (someOf_apply a _ _ |>.mpr ⟨rfl, rfl⟩)
  rw [someOf_apply] at key
  exact hab key.1

theorem cardinalSubalgebra_lt [Nontrivial α] :
    cardinalSubalgebra < (existentialSubalgebra : BooleanSubalgebra (Det α)) := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne α
  refine cardinalSubalgebra_le.lt_of_ne fun h ↦ not_cardinal_noBut hab ?_
  rw [← mem_cardinalSubalgebra, h]
  exact existential_noBut a

private theorem mem_of_card_eq [Subsingleton α] {s t : Set α} (h : Nat.card s = Nat.card t)
    {x : α} (hx : x ∈ s) : x ∈ t := by
  have : Nonempty s := ⟨⟨x, hx⟩⟩
  have ht : 0 < Nat.card t := h ▸ Nat.card_pos
  obtain ⟨⟨y, hy⟩⟩ := (Nat.card_pos_iff.1 ht).1
  exact Subsingleton.elim y x ▸ hy

-- PROP 14(c) fails on one individual
theorem cardinalSubalgebra_eq_of_subsingleton [Subsingleton α] :
    cardinalSubalgebra = (existentialSubalgebra : BooleanSubalgebra (Det α)) := by
  refine cardinalSubalgebra_le.antisymm ?_
  rintro f hf R T R' T' h
  have e : R ∩ T = R' ∩ T' :=
    Set.Subset.antisymm (fun _ ↦ mem_of_card_eq h) fun _ ↦ mem_of_card_eq h.symm
  rw [hf R T, hf R' T', e]

open Classical in
/-- A cardinal function is a set `K` of cardinalities between `0` and `n`, holding at `(R, T)`
exactly when `|R ∩ T| ∈ K`, and the correspondence is an isomorphism onto the power set
((102), with PROP 14(b) the count). -/
noncomputable def cardinalOrderIso [Fintype α] :
    cardinalSubalgebra (α := α) ≃o Set (Fin (Fintype.card α + 1)) :=
  Equiv.toOrderIso
    { toFun := fun f ↦ {k | f.1 (segment k) (segment k)}
      invFun := fun K ↦ ⟨fun R T ↦
          (⟨Nat.card ↥(R ∩ T), Nat.lt_succ_of_le (card_subtype_le_card _)⟩ : Fin _) ∈ K,
        fun R T R' T' h ↦ iff_of_eq (congrArg (· ∈ K) (Fin.ext h))⟩
      left_inv := fun f ↦ Subtype.ext (funext₂ fun R T ↦ propext
        (f.2 _ _ R T (by rw [card_segment_inter le_rfl (card_subtype_le_card _)])))
      right_inv := fun K ↦ Set.ext fun k ↦ iff_of_eq (congrArg (· ∈ K) (Fin.ext (by
        show Nat.card ↥(segment (α := α) k ∩ segment k) = k
        rw [card_segment_inter le_rfl (Nat.lt_succ_iff.mp k.2)]))) }
    (fun _ _ h k hk ↦ h _ _ hk) (fun _ _ h R T hx ↦ h hx)

theorem card_cardinal [Fintype α] :
    Nat.card (cardinalSubalgebra (α := α)) = 2 ^ (Fintype.card α + 1) := by
  rw [Nat.card_congr cardinalOrderIso.toEquiv]
  change Nat.card (Fin (Fintype.card α + 1) → Prop) = _
  rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Prop), Fintype.card_prop,
    Nat.card_eq_fintype_card, Fintype.card_fin]

theorem isAtom_cardinal_iff [Fintype α] {f : cardinalSubalgebra (α := α)} :
    IsAtom f ↔ ∃ k : Fin (Fintype.card α + 1), f.1 = exactly (k : ℕ) := by
  rw [← OrderIso.isAtom_iff cardinalOrderIso f, Set.isAtom_iff]
  constructor
  · rintro ⟨k, hk⟩
    have hf : f = cardinalOrderIso.symm {k} := by
      rw [← hk, OrderIso.symm_apply_apply]
    refine ⟨k, ?_⟩
    rw [hf]
    funext R T
    apply propext
    classical
    show (⟨Nat.card ↥(R ∩ T), _⟩ : Fin _) ∈ ({k} : Set _) ↔ _
    rw [Set.mem_singleton_iff, Fin.ext_iff]
    exact Iff.rfl
  · rintro ⟨k, hf⟩
    refine ⟨k, ?_⟩
    ext k'
    classical
    show f.1 (segment (k' : ℕ)) (segment (k' : ℕ)) ↔ k' ∈ ({k} : Set _)
    rw [hf, Set.mem_singleton_iff, exactly_apply]
    change Nat.card ↥(segment (α := α) (k' : ℕ) ∩ segment (k' : ℕ)) = _ ↔ _
    rw [card_segment_inter le_rfl (Nat.lt_succ_iff.mp k'.2), Fin.ext_iff]

/-! ### Logical determiners (Section 3.5 and the Appendix) -/

/-- The quantity-invariant functions are closed under the Boolean operations (the Appendix's
PI subalgebra). -/
def quantityInvariantSubalgebra : BooleanSubalgebra (Det α) where
  carrier := {f | QuantityInvariant f}
  supClosed' _ hf _ hg := hf.sup hg
  infClosed' _ hf _ hg := hf.inf hg
  compl_mem' hf := hf.compl
  bot_mem' _ _ _ := Iff.rfl

@[simp] theorem mem_quantityInvariantSubalgebra {f : Det α} :
    f ∈ quantityInvariantSubalgebra ↔ QuantityInvariant f :=
  Iff.rfl

/-- LOG, the algebra of logical determiners, collects the permutation-invariant members of the
conservative algebra ((114)). -/
def logicalSubalgebra : BooleanSubalgebra (Det α) :=
  conservativeSubalgebra ⊓ quantityInvariantSubalgebra

@[simp] theorem mem_logicalSubalgebra {f : Det α} :
    f ∈ logicalSubalgebra ↔ Conservative f ∧ QuantityInvariant f :=
  Iff.rfl

theorem logical_every : (every : Det α) ∈ logicalSubalgebra :=
  ⟨conservative_every, quantityInvariant_every⟩

theorem not_cardinal_every [Nonempty α] : ¬ Cardinal (every : Det α) :=
  fun h ↦ not_existential_every h.existential

theorem cardinalSubalgebra_le_logical :
    cardinalSubalgebra ≤ (logicalSubalgebra : BooleanSubalgebra (Det α)) :=
  fun _ hf ↦ ⟨(Cardinal.existential hf).conservative, Cardinal.quantityInvariant hf⟩

-- Section 3.5
theorem cardinalSubalgebra_lt_logical [Nontrivial α] :
    cardinalSubalgebra < (logicalSubalgebra : BooleanSubalgebra (Det α)) := by
  refine cardinalSubalgebra_le_logical.lt_of_ne fun h ↦ not_cardinal_every (α := α) ?_
  rw [← mem_cardinalSubalgebra, h]
  exact logical_every

theorem logical_congr [Fintype α] {f : Det α} (hf : f ∈ logicalSubalgebra) {R T R' T' : Set α}
    (hR : Nat.card R = Nat.card R') (hRT : Nat.card ↥(R ∩ T) = Nat.card ↥(R' ∩ T')) :
    f R T ↔ f R' T' := by
  obtain ⟨hc, hq⟩ := hf
  refine Det.iff_of_ncard_eq hc hq ?_ hRT
  have d := Set.ncard_inter_add_ncard_sdiff_eq_ncard R T
  have d' := Set.ncard_inter_add_ncard_sdiff_eq_ncard R' T'
  change R.ncard = R'.ncard at hR
  change (R ∩ T).ncard = (R' ∩ T').ncard at hRT
  omega

/-- The logical atoms are indexed by nested pairs of cardinalities up to the universe size
(the Appendix's `F_{m',m}` index). -/
abbrev Triangle (n : ℕ) := {mm : Fin (n + 1) × Fin (n + 1) // mm.2 ≤ mm.1}

theorem card_triangle (n : ℕ) : Nat.card (Triangle n) = (n + 1) * (n + 2) / 2 := by
  have e : Triangle n ≃ {p : Fin (n + 1) × Fin (n + 1) // p.1 ≤ p.2} :=
    (Equiv.prodComm _ _).subtypeEquiv fun mm ↦ Iff.rfl
  rw [Nat.card_congr e, Nat.card_congr Sym2.sortEquiv.symm, Nat.card_eq_fintype_card,
    Sym2.card, Fintype.card_fin, Nat.choose_two_right]
  simp [Nat.mul_comm]

open Classical in
/-- A logical function is a set of nested pairs `(|R|, |R ∩ T|)`, read off the initial
segments, and any set of pairs arises; the correspondence is an isomorphism onto the power set
(the Appendix's representation of PI). -/
noncomputable def logicalOrderIso [Fintype α] :
    logicalSubalgebra (α := α) ≃o Set (Triangle (Fintype.card α)) :=
  Equiv.toOrderIso
    { toFun := fun f ↦ {mm | f.1 (segment mm.1.1) (segment mm.1.2)}
      invFun := fun S ↦ ⟨fun R T ↦
          (⟨(⟨Nat.card R, Nat.lt_succ_of_le (card_subtype_le_card _)⟩,
             ⟨Nat.card ↥(R ∩ T), Nat.lt_succ_of_le (card_subtype_le_card _)⟩),
            Fin.mk_le_mk.mpr (card_inter_le_card_left R T)⟩ : Triangle _) ∈ S,
        ⟨fun R T ↦ iff_of_eq (congrArg (· ∈ S) (Subtype.ext (Prod.ext rfl (Fin.ext
            (show Nat.card ↥(R ∩ T) = Nat.card ↥(R ∩ (R ∩ T)) by
              rw [← Set.inter_assoc, Set.inter_self]))))),
          fun σ _ _ ↦ iff_of_eq (congrArg (· ∈ S) (Subtype.ext (Prod.ext
            (Fin.ext (Nat.card_congr (σ.subtypeEquiv fun _ ↦ Iff.rfl)))
            (Fin.ext (Nat.card_congr (σ.subtypeEquiv fun _ ↦ Iff.rfl))))))⟩⟩
      left_inv := fun f ↦ Subtype.ext (funext₂ fun R T ↦ propext
        (logical_congr f.2 (card_segment (card_subtype_le_card _))
          (by rw [card_segment_inter (card_inter_le_card_left R T) (card_subtype_le_card _)])))
      right_inv := fun S ↦ Set.ext fun mm ↦ iff_of_eq (congrArg (· ∈ S) (Subtype.ext (Prod.ext
        (Fin.ext (by
          show Nat.card (segment (α := α) mm.1.1) = mm.1.1
          exact card_segment (Nat.lt_succ_iff.mp mm.1.1.2)))
        (Fin.ext (by
          show Nat.card ↥(segment (α := α) mm.1.1 ∩ segment mm.1.2) = mm.1.2
          exact card_segment_inter mm.2 (Nat.lt_succ_iff.mp mm.1.2.2))))))}
    (fun _ _ h mm hmm ↦ h _ _ hmm) (fun _ _ h R T hx ↦ h hx)

theorem card_logical [Fintype α] :
    Nat.card (logicalSubalgebra (α := α)) =
      2 ^ ((Fintype.card α + 1) * (Fintype.card α + 2) / 2) := by
  rw [Nat.card_congr logicalOrderIso.toEquiv]
  change Nat.card (Triangle (Fintype.card α) → Prop) = _
  rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Prop), Fintype.card_prop, card_triangle]

/-- *exactly m of the n* is the Appendix's atom `F_{n,m}` of the logical algebra. -/
def exactlyOfThe (m n : ℕ) : Det α := fun R T ↦ Nat.card R = n ∧ Nat.card ↥(R ∩ T) = m

theorem isAtom_logical_iff [Fintype α] {f : logicalSubalgebra (α := α)} :
    IsAtom f ↔ ∃ mm : Triangle (Fintype.card α), f.1 = exactlyOfThe mm.1.2 mm.1.1 := by
  rw [← OrderIso.isAtom_iff logicalOrderIso f, Set.isAtom_iff]
  constructor
  · rintro ⟨mm, hmm⟩
    have hf : f = logicalOrderIso.symm {mm} := by
      rw [← hmm, OrderIso.symm_apply_apply]
    refine ⟨mm, ?_⟩
    rw [hf]
    funext R T
    apply propext
    show (⟨(⟨Nat.card R, _⟩, ⟨Nat.card ↥(R ∩ T), _⟩), _⟩ : Triangle _) ∈ ({mm} : Set _) ↔ _
    rw [Set.mem_singleton_iff, Subtype.ext_iff, Prod.ext_iff, Fin.ext_iff, Fin.ext_iff]
    exact Iff.rfl
  · rintro ⟨mm, hf⟩
    refine ⟨mm, ?_⟩
    ext mm'
    show f.1 (segment (mm'.1.1 : ℕ)) (segment (mm'.1.2 : ℕ)) ↔ mm' ∈ ({mm} : Set _)
    rw [hf, Set.mem_singleton_iff]
    show Nat.card (segment (α := α) (mm'.1.1 : ℕ)) = (mm.1.1 : ℕ) ∧ _ ↔ _
    rw [card_segment (Nat.lt_succ_iff.mp mm'.1.1.2),
      card_segment_inter mm'.2 (Nat.lt_succ_iff.mp mm'.1.2.2),
      Subtype.ext_iff, Prod.ext_iff, Fin.ext_iff, Fin.ext_iff]

theorem cardinalSubalgebra_eq_inf [Fintype α] :
    cardinalSubalgebra =
      (existentialSubalgebra ⊓ logicalSubalgebra : BooleanSubalgebra (Det α)) := by
  refine le_antisymm (le_inf cardinalSubalgebra_le cardinalSubalgebra_le_logical) ?_
  rintro f ⟨hex, hlog⟩ R T R' T' h
  calc f R T
      ↔ f (R ∩ T) Set.univ := hex R T
    _ ↔ f (R' ∩ T') Set.univ := logical_congr hlog h (by rwa [Set.inter_univ, Set.inter_univ])
    _ ↔ f R' T' := (hex R' T').symm

/-! ### The paper's worked universes

Two individuals: 512 conservative functions among 65,536, of which 8 are cardinal and 64
logical; three individuals: 16 cardinal among 256 existential functions. -/

example : Nat.card (ConsDet (Fin 2)) = 512 := by
  rw [card_consDet, Fintype.card_fin]; norm_num

example : Nat.card (Det (Fin 2)) = 65536 := by
  rw [card_gq, Fintype.card_fin]; norm_num

example : Nat.card (cardinalSubalgebra (α := Fin 2)) = 8 := by
  rw [card_cardinal, Fintype.card_fin]; norm_num

example : Nat.card (logicalSubalgebra (α := Fin 2)) = 64 := by
  rw [card_logical, Fintype.card_fin]; norm_num

example : Nat.card (cardinalSubalgebra (α := Fin 3)) = 16 := by
  rw [card_cardinal, Fintype.card_fin]; norm_num

example : Nat.card (existentialSubalgebra (α := Fin 3)) = 256 := by
  rw [card_existential, Fintype.card_fin]; norm_num

end KeenanStavi1986
