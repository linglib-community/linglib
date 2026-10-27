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
conservative functions, those with `f R T ↔ f R (R ⊓ T)`. The generators are the Appendix's two
individual-anchored determiners `Sₐ` and `Eₐ`, *John's one or more* and *John's zero or more*
when `a` is all John possesses, here derived as restrictions of *some* and *every* by the
singleton property of `a` (`someOf`, `allOf`); every conservative function is the join of the
atoms `atom p q` at the pairs where it holds, the atoms of the algebra are exactly these
(`isAtom_iff`), each atom is a meet of generators and their complements, and so the Boolean
subalgebra the generators generate is the conservative algebra (`closure_generators`). The
algebra is complete and atomic (the instance is in `Quantification/Lattice.lean`), so it is
isomorphic to the power set of its atoms; sorting the individuals into three cells counts the
atoms, and with `n` individuals there are `2 ^ 3 ^ n` conservative functions among the
`2 ^ 2 ^ 2n` functions from properties to sets of properties (`card_consGQ`, `card_gq`,
PROP 4), 512 among 65,536 for two individuals.

Section 3.3 characterizes the determiners of existential-*there* sentences as the existential
functions, `f R T ↔ f (R ⊓ T) ⊤`: *at least n* is one, *every* and *the n* are not, and the
class is closed under the Boolean operations (PROP 13). Section 3.4 isolates the cardinal
functions, deciding by the number of individuals in restrictor and scope: they are closed under
the Boolean operations and properly included in the existential functions (PROP 14), which are
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
`Conservative`, `Existential` and `QuantityInvariant`, the conservative algebra is `ConsGQ`
with its `CompleteAtomicBooleanAlgebra` instance, and the counts are `Nat.card`s over a
`Fintype` universe derived from mathlib's representation theorem
`CompleteAtomicBooleanAlgebra.toSetOfIsAtom`. `Cardinal` is stated with `Nat.card`, which is by
definition the `Set.ncard` the counting quantifiers count with.
Canonical witnesses of each size are initial segments of a fixed enumeration (`segment`), which
nest, unlike arbitrarily chosen subsets. `BooleanSubalgebra.closure` is finitary, so
`closure_generators` carries `[Finite α]`; the paper closes under arbitrary meets and joins, and
on an infinite universe the finitary closure is strictly smaller than the conservative algebra.

## TODO

* Footnote 10(b): on an infinite universe `CARD ⊊ E-Det ⊓ LOG`, witnessed by the paper's `f₀`.
* The (In)effability Theorems of Section 3.6, which quantify over the English determiner
  expressions.

## References

* [keenan-stavi-1986]
-/

@[expose] public section

namespace KeenanStavi1986

open Quantifier Quantifier.GQ Quantifier.NP BooleanSubalgebra

variable {α : Type*}

/-! ### The Conservativity Theorem (Section 2.5 and the Appendix) -/

/-- `Sₐ` restricts *some* by the singleton property of `a`; it is the Appendix's denotation of
*John's one or more* when `a` is all John possesses. -/
def someOf (a : α) : GQ α := adjRestrict GQ.some (ident a)

@[simp] theorem someOf_apply (a : α) (R T : α → Prop) : someOf a R T ↔ R a ∧ T a :=
  ⟨fun ⟨_, ⟨hR, hx⟩, hT⟩ ↦ hx ▸ ⟨hR, hT⟩, fun ⟨hR, hT⟩ ↦ ⟨a, ⟨hR, rfl⟩, hT⟩⟩

/-- `Eₐ` restricts *every* by the singleton property of `a`; it is the Appendix's denotation of
*John's zero or more*. -/
def allOf (a : α) : GQ α := adjRestrict every (ident a)

@[simp] theorem allOf_apply (a : α) (R T : α → Prop) : allOf a R T ↔ (R a → T a) :=
  ⟨fun h hR ↦ h a ⟨hR, rfl⟩, fun h _ ⟨hR, hx⟩ ↦ hx.symm ▸ h (hx ▸ hR)⟩

theorem conservative_someOf (a : α) : Conservative (someOf a) :=
  Conservative.adjRestrict _ _ conservative_some

theorem conservative_allOf (a : α) : Conservative (allOf a) :=
  Conservative.adjRestrict _ _ conservative_every

theorem existential_someOf (a : α) : Existential (someOf a) :=
  Existential.adjRestrict existential_some _

/-- The generators of the conservative algebra are the `Sₐ` and `Eₐ` for every individual. -/
def generators (α : Type*) : Set (GQ α) := Set.range someOf ∪ Set.range allOf

theorem conservative_of_mem_generators {q : GQ α} (hq : q ∈ generators α) : Conservative q := by
  obtain ⟨a, rfl⟩ | ⟨a, rfl⟩ := hq
  exacts [conservative_someOf a, conservative_allOf a]

/-- The Appendix's atom `f_{pq}` of the conservative algebra holds at the restrictor `p` and
exactly the scopes meeting `p` in `q`. -/
def atom (p q : α → Prop) : GQ α := fun R T ↦ R = p ∧ R ⊓ T = q

theorem conservative_atom (p q : α → Prop) : Conservative (atom p q) := fun R T ↦ by
  show R = p ∧ R ⊓ T = q ↔ R = p ∧ R ⊓ (R ⊓ T) = q
  rw [← inf_assoc, inf_idem]

theorem atom_le_iff {f : GQ α} (hf : Conservative f) {p q : α → Prop} (h : q ≤ p) :
    atom p q ≤ f ↔ f p q :=
  ⟨fun hle ↦ hle p q ⟨rfl, inf_eq_right.mpr h⟩, fun hpq R T ⟨hR, hT⟩ ↦ by
    subst hR; subst hT; exact (hf _ _).mpr hpq⟩

theorem isAtom_atom {p q : α → Prop} (h : q ≤ p) :
    IsAtom (⟨atom p q, conservative_atom p q⟩ : ConsGQ α) := by
  refine ⟨fun hbot ↦ ?_, fun b hb ↦ ?_⟩
  · exact (congrArg (fun f : ConsGQ α ↦ f.1 p q) hbot).mp ⟨rfl, inf_eq_right.mpr h⟩
  · by_contra hne
    obtain ⟨R, T, hRT⟩ : ∃ R T, b.1 R T := by
      by_contra hall
      push Not at hall
      exact hne (Subtype.ext (funext₂ fun R T ↦ propext ⟨hall R T, False.elim⟩))
    have hle : b.1 ≤ atom p q := hb.le
    obtain ⟨rfl, rfl⟩ := hle R T hRT
    refine hb.not_ge fun R' T' ⟨hR', hT'⟩ ↦ ?_
    subst hR'
    exact (b.2.iff_of_inf_eq hT').mpr hRT

/-- The atoms of the conservative algebra are exactly the `atom p q` with `q ≤ p`
(the Appendix). -/
theorem isAtom_iff {f : ConsGQ α} :
    IsAtom f ↔ ∃ p q, q ≤ p ∧ f.1 = atom p q := by
  constructor
  · intro hf
    obtain ⟨R, T, hRT⟩ : ∃ R T, f.1 R T := by
      by_contra hall
      push Not at hall
      exact hf.1 (Subtype.ext (funext₂ fun R T ↦ propext ⟨hall R T, False.elim⟩))
    refine ⟨R, R ⊓ T, inf_le_left, ?_⟩
    have hle : (⟨atom R (R ⊓ T), conservative_atom R (R ⊓ T)⟩ : ConsGQ α) ≤ f :=
      (atom_le_iff f.2 inf_le_left).mpr ((f.2 R T).mp hRT)
    have hne : (⟨atom R (R ⊓ T), conservative_atom R (R ⊓ T)⟩ : ConsGQ α) ≠ ⊥ := fun hbot ↦
      (congrArg (fun g : ConsGQ α ↦ g.1 R (R ⊓ T)) hbot).mp ⟨rfl, inf_eq_right.mpr inf_le_left⟩
    exact congrArg Subtype.val ((hf.le_iff.mp hle).resolve_left hne).symm
  · rintro ⟨p, q, hqp, hf⟩
    have hfe : f = ⟨atom p q, conservative_atom p q⟩ := Subtype.ext hf
    exact hfe ▸ isAtom_atom hqp

theorem eq_iSup_atom {f : GQ α} (hf : Conservative f) :
    f = ⨆ pq ∈ {pq : (α → Prop) × (α → Prop) | f pq.1 pq.2}, atom pq.1 pq.2 := by
  funext R T
  apply propext
  simp only [iSup_apply, iSup_Prop_eq, exists_prop, Set.mem_ofPred_eq, Prod.exists, atom]
  constructor
  · exact fun h ↦ ⟨R, R ⊓ T, (hf R T).mp h, rfl, rfl⟩
  · rintro ⟨p, q, h, rfl, rfl⟩
    exact (hf _ _).mpr h

theorem atom_eq_iInf (p q : α → Prop) :
    atom p q = (⨅ a ∈ {a | q a}, someOf a) ⊓
      (⨅ a ∈ {a | p a ∧ ¬ q a}, (someOf a)ᶜ ⊓ (allOf a)ᶜ) ⊓
      ⨅ a ∈ {a | ¬ p a}, (someOf a)ᶜ ⊓ allOf a := by
  funext R T
  apply propext
  simp only [atom, Pi.inf_apply, iInf_apply, iInf_Prop_eq, Pi.compl_apply, compl_iff_not,
    inf_Prop_eq, Set.mem_ofPred_eq, someOf_apply, allOf_apply]
  constructor
  · rintro ⟨rfl, rfl⟩
    exact ⟨⟨fun _ h ↦ h, fun _ ⟨hR, hq⟩ ↦ ⟨hq, fun h ↦ hq ⟨hR, h hR⟩⟩⟩,
      fun _ hR ↦ ⟨fun h ↦ hR h.1, fun h ↦ absurd h hR⟩⟩
  · rintro ⟨⟨hq, hp⟩, hn⟩
    refine ⟨funext fun a ↦ propext ?_, funext fun a ↦ propext ?_⟩
    · by_cases hpa : p a
      · by_cases hqa : q a
        · exact iff_of_true (hq a hqa).1 hpa
        · exact iff_of_true (of_not_imp (hp a ⟨hpa, hqa⟩).2) hpa
      · exact iff_of_false (fun hR ↦ (hn a hpa).1 ⟨hR, (hn a hpa).2 hR⟩) hpa
    · by_cases hqa : q a
      · exact iff_of_true (hq a hqa) hqa
      · by_cases hpa : p a
        · exact iff_of_false (hp a ⟨hpa, hqa⟩).1 hqa
        · exact iff_of_false (hn a hpa).1 hqa

theorem atom_mem_closure [Finite α] (p q : α → Prop) :
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
abbrev Nested (α : Type*) := {pq : (α → Prop) × (α → Prop) // pq.2 ≤ pq.1}

theorem atom_injective : Function.Injective fun pq : Nested α ↦ atom pq.1.1 pq.1.2 := by
  rintro ⟨⟨p, q⟩, hpq⟩ ⟨⟨p', q'⟩, hpq'⟩ h
  have h' : atom p q = atom p' q' := h
  obtain ⟨rfl, hq⟩ : atom p' q' p q := h' ▸ ⟨rfl, inf_eq_right.mpr hpq⟩
  have hqq : q = q' := by rw [← hq, inf_eq_right.mpr hpq]
  exact Subtype.ext (Prod.ext rfl hqq)

/-- The paper's index pairs are exactly mathlib's atoms of the conservative algebra. -/
noncomputable def atomEquiv : Nested α ≃ {f : ConsGQ α // IsAtom f} :=
  Equiv.ofBijective
    (fun pq ↦ ⟨⟨atom pq.1.1 pq.1.2, conservative_atom _ _⟩, isAtom_atom pq.2⟩)
    ⟨fun _ _ h ↦ atom_injective (congrArg (fun f ↦ f.1.1) h), fun f ↦ by
      obtain ⟨p, q, hqp, hf⟩ := isAtom_iff.mp f.2
      exact ⟨⟨(p, q), hqp⟩, Subtype.ext (Subtype.ext hf.symm)⟩⟩

open Classical in
/-- A pair `q ≤ p` sorts each individual into one of three cells, in `q`, in `p` but not `q`,
or outside `p`, and any sorting arises (the Appendix's coding `g_pq`). -/
noncomputable def nestedEquivFin3 : Nested α ≃ (α → Fin 3) where
  toFun pq x := if pq.1.2 x then 2 else if pq.1.1 x then 1 else 0
  invFun c := ⟨(fun x ↦ c x ≠ 0, fun x ↦ c x = 2), fun x hx ↦ by
    show c x ≠ 0
    rw [show c x = 2 from hx]
    decide⟩
  left_inv := fun ⟨⟨p, q⟩, h⟩ ↦ by
    refine Subtype.ext (Prod.ext (funext fun x ↦ propext ?_) (funext fun x ↦ propext ?_))
    · by_cases hq : q x
      · have hp : p x := h x hq
        simp [hq, hp]
      · by_cases hp : p x <;> simp [hq, hp]
    · by_cases hq : q x
      · simp [hq]
      · by_cases hp : p x <;> simp +decide [hq, hp]
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
    Nat.card {f : ConsGQ α // IsAtom f} = 3 ^ Fintype.card α := by
  rw [← Nat.card_congr (atomEquiv (α := α)), card_nested]

theorem card_consGQ [Fintype α] : Nat.card (ConsGQ α) = 2 ^ 3 ^ Fintype.card α := by
  rw [Nat.card_congr CompleteAtomicBooleanAlgebra.toSetOfIsAtom.toEquiv]
  change Nat.card ({f : ConsGQ α // IsAtom f} → Prop) = _
  rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Prop), Fintype.card_prop, card_isAtom]

theorem mk_consGQ :
    _root_.Cardinal.mk (ConsGQ α) =
      (2 : _root_.Cardinal) ^ (3 : _root_.Cardinal) ^ _root_.Cardinal.mk α := by
  rw [_root_.Cardinal.mk_congr CompleteAtomicBooleanAlgebra.toSetOfIsAtom.toEquiv]
  change _root_.Cardinal.mk (Set {f : ConsGQ α // IsAtom f}) = _
  rw [_root_.Cardinal.mk_set, _root_.Cardinal.mk_congr (atomEquiv (α := α)).symm,
    _root_.Cardinal.mk_congr nestedEquivFin3, _root_.Cardinal.mk_arrow,
    _root_.Cardinal.mk_fin, _root_.Cardinal.lift_natCast, _root_.Cardinal.lift_uzero]
  norm_num

theorem card_gq [Fintype α] : Nat.card (GQ α) = 2 ^ 2 ^ (2 * Fintype.card α) := by
  rw [Nat.card_fun, Nat.card_fun, Nat.card_fun, Nat.card_eq_fintype_card (α := Prop),
    Fintype.card_prop, Nat.card_eq_fintype_card, ← pow_mul, ← pow_add, ← two_mul]

/-! ### Canonical witnesses of each size

Initial segments of a fixed enumeration of the universe, nested by construction, standing in
for the paper's freely chosen sets of `k` individuals. -/

section Segment

variable [Fintype α]

/-- `segment k` holds of the first `k` individuals under a fixed enumeration of the
universe. -/
def segment (k : ℕ) : α → Prop := fun x ↦ ((Fintype.equivFin α) x : ℕ) < k

theorem segment_mono {k m : ℕ} (h : k ≤ m) : segment (α := α) k ≤ segment m :=
  fun _ hx ↦ lt_of_lt_of_le hx h

theorem card_segment {k : ℕ} (hk : k ≤ Fintype.card α) :
    Nat.card {x : α // segment k x} = k := by
  have e : {x : α // segment k x} ≃ {i : Fin (Fintype.card α) // (i : ℕ) < k} :=
    (Fintype.equivFin α).subtypeEquiv fun x ↦ Iff.rfl
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype,
    Fin.card_filter_val_lt]
  omega

theorem card_segment_inter {m k : ℕ} (h : m ≤ k) (hm : m ≤ Fintype.card α) :
    Nat.card {x : α // segment k x ∧ segment m x} = m := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight fun x ↦
    and_iff_right_of_imp fun hx ↦ segment_mono h x hx)]
  exact card_segment hm

theorem card_subtype_le_card (P : α → Prop) : Nat.card {x // P x} ≤ Fintype.card α :=
  (Nat.card_le_card_of_injective _ Subtype.val_injective).trans_eq Nat.card_eq_fintype_card

theorem card_inter_le_card_left (R T : α → Prop) :
    Nat.card {x // R x ∧ T x} ≤ Nat.card {x // R x} :=
  Nat.card_le_card_of_injective _ (Subtype.impEmbedding _ _ fun _ hx ↦ hx.1).injective

end Segment

/-! ### Existential determiners (Section 3.3) -/

/-- The existential functions are closed under the Boolean operations (PROP 13). -/
def existentialSubalgebra : BooleanSubalgebra (GQ α) where
  carrier := {f | Existential f}
  supClosed' _ hf _ hg R T := or_congr (hf R T) (hg R T)
  infClosed' _ hf _ hg R T := and_congr (hf R T) (hg R T)
  compl_mem' hf R T := not_congr (hf R T)
  bot_mem' _ _ := Iff.rfl

@[simp] theorem mem_existentialSubalgebra {f : GQ α} :
    f ∈ existentialSubalgebra ↔ Existential f :=
  Iff.rfl

theorem existential_iSup {ι : Sort*} {f : ι → GQ α} (hf : ∀ i, Existential (f i)) :
    Existential (⨆ i, f i) := fun R T ↦ by
  simp only [iSup_apply, iSup_Prop_eq]
  exact exists_congr fun i ↦ hf i R T

theorem existential_iInf {ι : Sort*} {f : ι → GQ α} (hf : ∀ i, Existential (f i)) :
    Existential (⨅ i, f i) := fun R T ↦ by
  simp only [iInf_apply, iInf_Prop_eq]
  exact forall_congr' fun i ↦ hf i R T

theorem existentialSubalgebra_le :
    existentialSubalgebra ≤ (conservativeSubalgebra : BooleanSubalgebra (GQ α)) :=
  fun _ hf ↦ hf.conservative

-- (99), (100)
theorem existential_atLeast (n : ℕ) : Existential (atLeast (α := α) n) := fun R T ↦ by
  simp only [atLeast_apply, and_true]

-- Section 3.3
theorem not_existential_every [Nonempty α] : ¬ Existential (every : GQ α) := fun h ↦ by
  obtain ⟨b⟩ := ‹Nonempty α›
  exact absurd ((h (fun _ ↦ True) (· ≠ b)).mpr fun _ _ ↦ trivial) fun h' ↦ (h' b trivial) rfl

/-- *the n* is the universal on a restrictor of exactly `n` individuals ((43)); *both* is
`theN 2`. -/
def theN (n : ℕ) : GQ α := every ⊓ fun R _ ↦ {x | R x}.ncard = n

theorem theN_apply (n : ℕ) (R T : α → Prop) :
    theN n R T ↔ every R T ∧ {x | R x}.ncard = n :=
  Iff.rfl

theorem theN_two_eq_both [Finite α] : theN 2 = (both : GQ α) := by
  funext R T
  have hd : {x | R x ∧ T x}.ncard + {x | R x ∧ ¬ T x}.ncard = {x | R x}.ncard :=
    Set.ncard_inter_add_ncard_sdiff_eq_ncard _ _
  have he : every R T ↔ {x | R x ∧ ¬ T x}.ncard = 0 := by rw [every_eq_toGQ_all]; rfl
  apply propext
  rw [theN_apply, he]
  change _ ↔ {x | R x ∧ ¬ T x}.ncard = 0 ∧ {x | R x ∧ T x}.ncard = 2
  omega

-- Section 3.3
theorem not_existential_theN [Fintype α] {n : ℕ} (hn : n < Fintype.card α) :
    ¬ Existential (theN (α := α) n) := fun h ↦ by
  have h1 : theN (α := α) n (fun x ↦ True ∧ segment n x) (fun _ ↦ True) := by
    rw [theN_apply]
    refine ⟨fun _ _ ↦ trivial, ?_⟩
    simp only [true_and]
    exact card_segment hn.le
  have hcard := ((theN_apply _ _ _).1 ((h (fun _ ↦ True) (segment n)).mpr h1)).2
  rw [Set.ofPred_true, Set.ncard_univ, Nat.card_eq_fintype_card] at hcard
  omega

/-- *no ... but J* holds when restrictor and scope meet in exactly the individual `a` ((42)). -/
def noBut (a : α) : GQ α := fun R T ↦ R ⊓ T = ident a

-- (103)
theorem existential_noBut (a : α) : Existential (noBut a) := fun R T ↦ by
  show R ⊓ T = ident a ↔ (R ⊓ T) ⊓ (⊤ : α → Prop) = ident a
  rw [inf_top_eq]

/-- An existential function is determined by its set of properties `f(1)`, and the
correspondence is an isomorphism onto the type ⟨1⟩ quantifiers, the possible NP denotations
(PROP 15). -/
noncomputable def existentialOrderIso : existentialSubalgebra (α := α) ≃o NP α :=
  Equiv.toOrderIso
    { toFun := fun f T ↦ f.1 ⊤ T
      invFun := fun g ↦ ⟨fun R T ↦ g (R ⊓ T), fun R T ↦
        Iff.of_eq (congrArg g (inf_top_eq _).symm)⟩
      left_inv := fun f ↦ Subtype.ext (funext₂ fun R T ↦ propext ((f.2 ⊤ (R ⊓ T)).trans (by
        show f.1 (⊤ ⊓ (R ⊓ T)) ⊤ ↔ f.1 R T
        rw [top_inf_eq]
        exact (f.2 R T).symm)))
      right_inv := fun g ↦ funext fun T ↦ congrArg g (top_inf_eq T) }
    (fun _ _ h T hT ↦ h ⊤ T hT) (fun _ _ h R T hx ↦ h _ hx)

theorem card_existential [Fintype α] :
    Nat.card (existentialSubalgebra (α := α)) = 2 ^ 2 ^ Fintype.card α := by
  rw [Nat.card_congr existentialOrderIso.toEquiv, Nat.card_fun, Nat.card_fun,
    Nat.card_eq_fintype_card (α := Prop), Fintype.card_prop, Nat.card_eq_fintype_card]

/-! ### Cardinal determiners (Section 3.4) -/

/-- A cardinal function decides by the number of individuals in restrictor and scope ((102)). -/
def Cardinal (f : GQ α) : Prop :=
  ∀ R T R' T' : α → Prop,
    Nat.card {x // R x ∧ T x} = Nat.card {x // R' x ∧ T' x} → (f R T ↔ f R' T')

/-- The cardinal functions are closed under the Boolean operations (PROP 14(a)). -/
def cardinalSubalgebra : BooleanSubalgebra (GQ α) where
  carrier := {f | Cardinal f}
  supClosed' _ hf _ hg R T R' T' h := or_congr (hf R T R' T' h) (hg R T R' T' h)
  infClosed' _ hf _ hg R T R' T' h := and_congr (hf R T R' T' h) (hg R T R' T' h)
  compl_mem' hf R T R' T' h := not_congr (hf R T R' T' h)
  bot_mem' _ _ _ _ _ := Iff.rfl

@[simp] theorem mem_cardinalSubalgebra {f : GQ α} : f ∈ cardinalSubalgebra ↔ Cardinal f :=
  Iff.rfl

theorem Cardinal.existential {f : GQ α} (hf : Cardinal f) : Existential f := fun R T ↦
  hf R T _ _ (Nat.card_congr (Equiv.subtypeEquivRight fun _ ↦ (iff_of_eq (and_true _)).symm))

theorem Cardinal.quantityInvariant {f : GQ α} (hf : Cardinal f) : QuantityInvariant f :=
  fun A B A' B' σ hBij hA hB ↦ hf A B A' B'
    (Nat.card_congr (Equiv.subtypeEquiv (Equiv.ofBijective σ hBij) fun x ↦
      (and_congr (hA x) (hB x)).symm)).symm

theorem cardinalSubalgebra_le :
    cardinalSubalgebra ≤ (existentialSubalgebra : BooleanSubalgebra (GQ α)) :=
  fun _ hf ↦ Cardinal.existential hf

theorem cardinal_atLeast (n : ℕ) : Cardinal (atLeast (α := α) n) :=
  fun _ _ _ _ h ↦ Iff.of_eq (congrArg (n ≤ ·) h)

theorem cardinal_exactly (n : ℕ) : Cardinal (exactly (α := α) n) :=
  fun _ _ _ _ h ↦ Iff.of_eq (congrArg (· = n) h)

private theorem card_ident_inter (c : α) : Nat.card {x // ident c x ∧ ident c x} = 1 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight (q := fun x ↦ x = c) fun x ↦ by simp [ident])]
  exact Nat.card_unique

theorem cardinal_some [Fintype α] : Cardinal (GQ.some : GQ α) := by
  rw [some_eq_atLeast_one]
  exact cardinal_atLeast 1

theorem not_cardinal_noBut {a b : α} (hab : a ≠ b) : ¬ Cardinal (noBut a) := fun h ↦ by
  have hcards : Nat.card {x // ident a x ∧ ident a x} = Nat.card {x // ident b x ∧ ident b x} :=
    (card_ident_inter a).trans (card_ident_inter b).symm
  have key : ident b = ident a := by
    have h1 : ident b ⊓ ident b = ident a :=
      (h (ident a) (ident a) (ident b) (ident b) hcards).mp (inf_idem _)
    rwa [inf_idem] at h1
  exact hab (ident_injective key).symm

theorem not_cardinal_someOf {a b : α} (hab : a ≠ b) : ¬ Cardinal (someOf a) := fun h ↦ by
  have key := (h (ident a) (ident a) (ident b) (ident b)
    ((card_ident_inter a).trans (card_ident_inter b).symm)).mp
    (someOf_apply a _ _ |>.mpr ⟨rfl, rfl⟩)
  rw [someOf_apply] at key
  exact hab key.1

theorem cardinalSubalgebra_lt [Nontrivial α] :
    cardinalSubalgebra < (existentialSubalgebra : BooleanSubalgebra (GQ α)) := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne α
  refine cardinalSubalgebra_le.lt_of_ne fun h ↦ not_cardinal_noBut hab ?_
  rw [← mem_cardinalSubalgebra, h]
  exact existential_noBut a

open Classical in
/-- A cardinal function is a set `K` of cardinalities between `0` and `n`, holding at `(R, T)`
exactly when `|R ⊓ T| ∈ K`, and the correspondence is an isomorphism onto the power set
((102), with PROP 14(b) the count). -/
noncomputable def cardinalOrderIso [Fintype α] :
    cardinalSubalgebra (α := α) ≃o Set (Fin (Fintype.card α + 1)) :=
  Equiv.toOrderIso
    { toFun := fun f ↦ {k | f.1 (segment k) (segment k)}
      invFun := fun K ↦ ⟨fun R T ↦
          (⟨Nat.card {x // R x ∧ T x}, Nat.lt_succ_of_le (card_subtype_le_card _)⟩ : Fin _) ∈ K,
        fun R T R' T' h ↦ iff_of_eq (congrArg (· ∈ K) (Fin.ext h))⟩
      left_inv := fun f ↦ Subtype.ext (funext₂ fun R T ↦ propext
        (f.2 _ _ R T (by rw [card_segment_inter le_rfl (card_subtype_le_card _)])))
      right_inv := fun K ↦ Set.ext fun k ↦ iff_of_eq (congrArg (· ∈ K) (Fin.ext (by
        show Nat.card {x : α // segment k x ∧ segment k x} = k
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
    show (⟨Nat.card {x // R x ∧ T x}, _⟩ : Fin _) ∈ ({k} : Set _) ↔ _
    rw [Set.mem_singleton_iff, Fin.ext_iff]
    exact Iff.rfl
  · rintro ⟨k, hf⟩
    refine ⟨k, ?_⟩
    ext k'
    classical
    show f.1 (segment (k' : ℕ)) (segment (k' : ℕ)) ↔ k' ∈ ({k} : Set _)
    rw [hf, Set.mem_singleton_iff, exactly_apply]
    change Nat.card {x // segment (k' : ℕ) x ∧ segment (k' : ℕ) x} = _ ↔ _
    rw [card_segment_inter le_rfl (Nat.lt_succ_iff.mp k'.2), Fin.ext_iff]

/-! ### Logical determiners (Section 3.5 and the Appendix) -/

/-- The quantity-invariant functions are closed under the Boolean operations (the Appendix's
PI subalgebra). -/
def quantityInvariantSubalgebra : BooleanSubalgebra (GQ α) where
  carrier := {f | QuantityInvariant f}
  supClosed' f hf g hg := QuantityInvariant.sup f g hf hg
  infClosed' f hf g hg := QuantityInvariant.inf f g hf hg
  compl_mem' hf := QuantityInvariant.compl _ hf
  bot_mem' _ _ _ _ _ _ _ _ := Iff.rfl

@[simp] theorem mem_quantityInvariantSubalgebra {f : GQ α} :
    f ∈ quantityInvariantSubalgebra ↔ QuantityInvariant f :=
  Iff.rfl

/-- LOG, the algebra of logical determiners, collects the permutation-invariant members of the
conservative algebra ((114)). -/
def logicalSubalgebra : BooleanSubalgebra (GQ α) :=
  conservativeSubalgebra ⊓ quantityInvariantSubalgebra

@[simp] theorem mem_logicalSubalgebra {f : GQ α} :
    f ∈ logicalSubalgebra ↔ Conservative f ∧ QuantityInvariant f :=
  Iff.rfl

theorem logical_every : (every : GQ α) ∈ logicalSubalgebra :=
  ⟨conservative_every, quantityInvariant_every⟩

theorem not_cardinal_every [Nonempty α] : ¬ Cardinal (every : GQ α) :=
  fun h ↦ not_existential_every h.existential

theorem cardinalSubalgebra_le_logical :
    cardinalSubalgebra ≤ (logicalSubalgebra : BooleanSubalgebra (GQ α)) :=
  fun _ hf ↦ ⟨(Cardinal.existential hf).conservative, Cardinal.quantityInvariant hf⟩

-- Section 3.5
theorem cardinalSubalgebra_lt_logical [Nontrivial α] :
    cardinalSubalgebra < (logicalSubalgebra : BooleanSubalgebra (GQ α)) := by
  refine cardinalSubalgebra_le_logical.lt_of_ne fun h ↦ not_cardinal_every (α := α) ?_
  rw [← mem_cardinalSubalgebra, h]
  exact logical_every

theorem logical_congr [Fintype α] {f : GQ α} (hf : f ∈ logicalSubalgebra)
    {R T R' T' : α → Prop}
    (hR : Nat.card {x // R x} = Nat.card {x // R' x})
    (hRT : Nat.card {x // R x ∧ T x} = Nat.card {x // R' x ∧ T' x}) :
    f R T ↔ f R' T' := by
  obtain ⟨hc, hq⟩ := hf
  refine GQ.iff_of_ncard_eq hc hq ?_ hRT
  have d : {x | R x ∧ T x}.ncard + {x | R x ∧ ¬ T x}.ncard = {x | R x}.ncard :=
    Set.ncard_inter_add_ncard_sdiff_eq_ncard _ _
  have d' : {x | R' x ∧ T' x}.ncard + {x | R' x ∧ ¬ T' x}.ncard = {x | R' x}.ncard :=
    Set.ncard_inter_add_ncard_sdiff_eq_ncard _ _
  change {x | R x}.ncard = {x | R' x}.ncard at hR
  change {x | R x ∧ T x}.ncard = {x | R' x ∧ T' x}.ncard at hRT
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
/-- A logical function is a set of nested pairs `(|R|, |R ⊓ T|)`, read off the initial
segments, and any set of pairs arises; the correspondence is an isomorphism onto the power set
(the Appendix's representation of PI). -/
noncomputable def logicalOrderIso [Fintype α] :
    logicalSubalgebra (α := α) ≃o Set (Triangle (Fintype.card α)) :=
  Equiv.toOrderIso
    { toFun := fun f ↦ {mm | f.1 (segment mm.1.1) (segment mm.1.2)}
      invFun := fun S ↦ ⟨fun R T ↦
          (⟨(⟨Nat.card {x // R x}, Nat.lt_succ_of_le (card_subtype_le_card _)⟩,
             ⟨Nat.card {x // R x ∧ T x}, Nat.lt_succ_of_le (card_subtype_le_card _)⟩),
            Fin.mk_le_mk.mpr (card_inter_le_card_left R T)⟩ : Triangle _) ∈ S,
        ⟨fun R T ↦ iff_of_eq (congrArg (· ∈ S) (Subtype.ext (Prod.ext rfl (Fin.ext
            (Nat.card_congr (Equiv.subtypeEquivRight fun x ↦ by tauto)).symm)))),
          fun A B A' B' σ hBij hA hB ↦ iff_of_eq (congrArg (· ∈ S) (Subtype.ext (Prod.ext
            (Fin.ext (Nat.card_congr (Equiv.subtypeEquiv (Equiv.ofBijective σ hBij)
              fun x ↦ (hA x).symm)).symm)
            (Fin.ext (Nat.card_congr (Equiv.subtypeEquiv (Equiv.ofBijective σ hBij)
              fun x ↦ (and_congr (hA x) (hB x)).symm)).symm))))⟩⟩
      left_inv := fun f ↦ Subtype.ext (funext₂ fun R T ↦ propext
        (logical_congr f.2 (card_segment (card_subtype_le_card _))
          (by rw [card_segment_inter (card_inter_le_card_left R T) (card_subtype_le_card _)])))
      right_inv := fun S ↦ Set.ext fun mm ↦ iff_of_eq (congrArg (· ∈ S) (Subtype.ext (Prod.ext
        (Fin.ext (by
          show Nat.card {x : α // segment mm.1.1 x} = mm.1.1
          exact card_segment (Nat.lt_succ_iff.mp mm.1.1.2)))
        (Fin.ext (by
          show Nat.card {x : α // segment mm.1.1 x ∧ segment mm.1.2 x} = mm.1.2
          exact card_segment_inter mm.2 (Nat.lt_succ_iff.mp mm.1.2.2))))))}
    (fun _ _ h mm hmm ↦ h _ _ hmm) (fun _ _ h R T hx ↦ h hx)

theorem card_logical [Fintype α] :
    Nat.card (logicalSubalgebra (α := α)) =
      2 ^ ((Fintype.card α + 1) * (Fintype.card α + 2) / 2) := by
  rw [Nat.card_congr logicalOrderIso.toEquiv]
  change Nat.card (Triangle (Fintype.card α) → Prop) = _
  rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Prop), Fintype.card_prop, card_triangle]

/-- *exactly m of the n* is the Appendix's atom `F_{n,m}` of the logical algebra. -/
def exactlyOfThe (m n : ℕ) : GQ α := fun R T ↦
  Nat.card {x // R x} = n ∧ Nat.card {x // R x ∧ T x} = m

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
    show (⟨(⟨Nat.card {x // R x}, _⟩, ⟨Nat.card {x // R x ∧ T x}, _⟩), _⟩ : Triangle _)
      ∈ ({mm} : Set _) ↔ _
    rw [Set.mem_singleton_iff, Subtype.ext_iff, Prod.ext_iff, Fin.ext_iff, Fin.ext_iff]
    exact Iff.rfl
  · rintro ⟨mm, hf⟩
    refine ⟨mm, ?_⟩
    ext mm'
    show f.1 (segment (mm'.1.1 : ℕ)) (segment (mm'.1.2 : ℕ)) ↔ mm' ∈ ({mm} : Set _)
    rw [hf, Set.mem_singleton_iff]
    show Nat.card {x : α // segment (mm'.1.1 : ℕ) x} = (mm.1.1 : ℕ) ∧ _ ↔ _
    rw [card_segment (Nat.lt_succ_iff.mp mm'.1.1.2),
      card_segment_inter mm'.2 (Nat.lt_succ_iff.mp mm'.1.2.2),
      Subtype.ext_iff, Prod.ext_iff, Fin.ext_iff, Fin.ext_iff]

theorem cardinalSubalgebra_eq_inf [Fintype α] :
    cardinalSubalgebra =
      (existentialSubalgebra ⊓ logicalSubalgebra : BooleanSubalgebra (GQ α)) := by
  refine le_antisymm (le_inf cardinalSubalgebra_le cardinalSubalgebra_le_logical) ?_
  rintro f ⟨hex, hlog⟩ R T R' T' h
  calc f R T
      ↔ f (fun x ↦ R x ∧ T x) (fun _ ↦ True) := hex R T
    _ ↔ f (fun x ↦ R' x ∧ T' x) (fun _ ↦ True) :=
        logical_congr hlog h (by
          rw [Nat.card_congr (Equiv.subtypeEquivRight
              (q := fun x ↦ R x ∧ T x) fun x ↦ iff_of_eq (and_true _)),
            Nat.card_congr (Equiv.subtypeEquivRight
              (q := fun x ↦ R' x ∧ T' x) fun x ↦ iff_of_eq (and_true _))]
          exact h)
    _ ↔ f R' T' := (hex R' T').symm

/-! ### The paper's worked universes

Two individuals: 512 conservative functions among 65,536, of which 8 are cardinal and 64
logical; three individuals: 16 cardinal among 256 existential functions. -/

example : Nat.card (ConsGQ (Fin 2)) = 512 := by
  rw [card_consGQ, Fintype.card_fin]; norm_num

example : Nat.card (GQ (Fin 2)) = 65536 := by
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
