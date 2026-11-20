module

public import Linglib.Semantics.Composition.Interpret
public import Linglib.Semantics.Composition.Sorts
public import Linglib.Semantics.Plurality.Algebra
public import Linglib.Semantics.Reference.Kind
public import Studies.Krifka1989

/-!
# Krifka (2003): Bare NPs: Kind-referring, Indefinites, Both, or Neither?

A count noun relates a number `n` to the individuals that consist of `n` instances, so its
extension at a world is a family `ℕ → Set α`. Krifka takes the family to be an extensive
measure, as *gallon* is. For a region `P` and a measure `μ` the family is
`fun n ↦ P ∩ μ ⁻¹' {n}`, the measure construction of [krifka-1989]: its members are pairwise
disjoint (`pairwise_disjoint_inter_preimage`), and the sum of two individuals of `n` and of `m`
instances that do not overlap has `n + m` (`sup_mem_inter_preimage`).

We define the count noun of a set `D` of atoms on finite sets of atoms by
`ofAtoms D n = supClosure (singleton '' D) ∩ Finset.card ⁻¹' {n}`, the sums of members of `D`
that have `n` atoms. A number word fills the number argument, and the predicate `ofAtoms D n` is
quantized (`qua_ofAtoms`). The semantic plural binds the argument existentially, with no
condition that the number exceed one, so it is `⋃ n, ofAtoms D n`, which is Link's closure of
`D` under sum (`iUnion_ofAtoms`) and holds of a single member of `D`.

The definite article and the kind-forming operator ∩ take the largest member of an extension.
The predicate `ofAtoms D n` has one exactly when `D` has `n` members (`down_ofAtoms_dom`), and
the semantic plural exactly when `D` is nonempty and finite (`down_iUnion_ofAtoms_dom`), where
it is the sum of all of `D` (`isGreatest_iUnion_ofAtoms`).

Composition is type driven. Sisters combine by functional application, and two predicates of
individuals, which application does not combine, by existential closure `∃ x, P x ∧ V x`. A
count noun has type `⟨n,⟨e,t⟩⟩`, so it has no meaning with a verbal predicate
(`meanings_dogBarks`), while its plural is a predicate and has one (`meanings_dogsBark`). A
phrase moved over negation leaves a trace, and `meanings τ` are the meanings of a tree whose
traces have type `τ`. With a trace of its own type a moved phrase is interpreted where its trace
is, so a bare plural is closed existentially below negation (`meanings_overNegation_bare`). A
determiner phrase with a trace of individuals takes scope over negation
(`meanings_overNegation_a`).

## Implementation notes

* Individuals are finite sets of atoms, with `Finset.card` as the measure. Link's nonempty sets
  of atoms, `Mereology.Individual`, have a sum of any nonempty `D`, but their cardinality
  `Set.ncard` is `0` on infinite sets and so is no extensive measure, and
  `Set.encard` is not strictly monotone on them. With finite sets the
  semantic plural has a largest member only for a finite `D`.
* Existential closure is a mode of combination of two sisters, not a shift of one of them, so
  it is the same rule whether the nominal predicate is shifted to a quantifier or the verbal
  predicate to a function of nominal predicates.
* The paper's type-neutral trace is the trace of the type of the moved phrase, here `τ = ⟨e,t⟩`
  for a bare plural. With a trace of individuals the moved bare plural and the abstract are
  again two predicates, and existential closure applies above negation
  (`meanings_overNegation_bare_e`).
* A number word is a number, the specifier of a count noun, or a determiner, and the indefinite
  article is the determiner of the number one.

## TODO

* The definite article with a count noun, which fills the number argument with one, as a
  lexical item: it is partial, and the fragment here is total.
* Kind predication, where ∩ applies to the intension of a bare plural at an argument slot for
  individual concepts, and the property anaphora of reflexives and controlled subjects.
* The choice-function reading of *some*, the topic condition on kind reference, and singular
  definite generics.

## References

* [krifka-2003]
* [krifka-1989]
* [chierchia-1998]
* [partee-1987]
* [link-1983]
-/

@[expose] public section

namespace Krifka2003

open Mereology

/-! ### Count nouns as measure relations -/

section Measure

variable {α M : Type*} {P : Set α} {μ : α → M} {x y : α} {n m : M}

-- (53a)
theorem pairwise_disjoint_inter_preimage (P : Set α) (μ : α → M) :
    Pairwise (Function.onFun Disjoint fun n ↦ P ∩ μ ⁻¹' {n}) :=
  fun _ _ hnm ↦ Set.disjoint_left.2 fun _ hx hy ↦ hnm (hx.2.symm.trans hy.2)

-- (53b)
theorem sup_mem_inter_preimage [SemilatticeSup α] [AddCommMonoid M] [PartialOrder M]
    (hμ : IsExtensive μ) (hP : CUM P) (hx : x ∈ P ∩ μ ⁻¹' {n}) (hy : y ∈ P ∩ μ ⁻¹' {m})
    (hxy : ¬ Overlap x y) : x ⊔ y ∈ P ∩ μ ⁻¹' {n + m} :=
  ⟨hP hx.1 hy.1, (hμ.map_sup hxy).trans (congrArg₂ (· + ·) hx.2 hy.2)⟩

end Measure

section Atoms

variable {Atom : Type*} [DecidableEq Atom] {D : Set Atom} {x : Finset Atom} {n : ℕ} {a : Atom}

/-- (52a): The count noun of a set `D` of atoms relates `n` to the sums of members of `D` that
have `n` atoms. -/
def ofAtoms (D : Set Atom) (n : ℕ) : Set (Finset Atom) :=
  supClosure (({·} : Atom → Finset Atom) '' D) ∩ Finset.card ⁻¹' {n}

@[simp] theorem mem_ofAtoms : x ∈ ofAtoms D n ↔ (x.Nonempty ∧ ↑x ⊆ D) ∧ x.card = n :=
  and_congr_left' (mem_supClosure_image_singleton D x)

/-- The semantic plural of a count noun is Link's closure of its atoms under sum. -/
theorem iUnion_ofAtoms (D : Set Atom) :
    ⋃ n, ofAtoms D n = supClosure (({·} : Atom → Finset Atom) '' D) :=
  Krifka1989.iUnion_inter_preimage _ _

theorem ofAtoms_zero (D : Set Atom) : ofAtoms D 0 = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ hx ↦
    (mem_ofAtoms.1 hx).1.1.ne_empty (Finset.card_eq_zero.1 (mem_ofAtoms.1 hx).2)

-- (54a), (61)
theorem ofAtoms_one (D : Set Atom) : ofAtoms D 1 = ({·} : Atom → Finset Atom) '' D := by
  ext x
  simp only [mem_ofAtoms, Finset.card_eq_one, Set.mem_image]
  constructor
  · rintro ⟨⟨-, hD⟩, a, rfl⟩
    exact ⟨a, hD (Finset.mem_coe.2 (Finset.mem_singleton_self a)), rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨Finset.singleton_nonempty a, by simpa using ha⟩, a, rfl⟩

-- A count noun with its number argument filled is a measure phrase, (6) of [krifka-1989].
theorem qua_ofAtoms (D : Set Atom) (n : ℕ) : QUA (ofAtoms D n) :=
  qua_inter_preimage_of_strictMonoOn (Finset.card_strictMono.strictMonoOn _) n

theorem cum_iUnion_ofAtoms (D : Set Atom) : CUM (⋃ n, ofAtoms D n) := by
  rw [iUnion_ofAtoms]
  exact supClosed_supClosure

-- With one dog no individual consists of more than one, so a plural of more than one is empty.
theorem ofAtoms_singleton_of_one_lt (a : Atom) (hn : 1 < n) : ofAtoms {a} n = ∅ :=
  Set.eq_empty_of_forall_notMem fun x hx ↦ by
    obtain ⟨⟨-, hD⟩, rfl⟩ := mem_ofAtoms.1 hx
    exact hn.not_ge (Finset.card_le_one.2 fun b hb c hc ↦
      (Set.eq_of_mem_singleton (hD hb)).trans (Set.eq_of_mem_singleton (hD hc)).symm)

theorem isGreatest_ofAtoms :
    IsGreatest (ofAtoms D n) x ↔ (x.Nonempty ∧ ↑x = D) ∧ x.card = n := by
  constructor
  · rintro ⟨hx, hub⟩
    obtain ⟨⟨hne, hD⟩, hn⟩ := mem_ofAtoms.1 hx
    refine ⟨⟨hne, hD.antisymm fun a ha ↦ ?_⟩, hn⟩
    by_contra hax
    obtain ⟨b, hb⟩ := hne
    have hy : insert a (x.erase b) ∈ ofAtoms D n := mem_ofAtoms.2
      ⟨⟨Finset.insert_nonempty _ _, by
          rw [Finset.coe_insert, Set.insert_subset_iff]
          exact ⟨ha, fun c hc ↦ hD (Finset.mem_of_mem_erase hc)⟩⟩, by
        have := Finset.card_pos.2 ⟨b, hb⟩
        rw [Finset.card_insert_of_notMem fun h ↦ hax (Finset.mem_of_mem_erase h),
          Finset.card_erase_of_mem hb, ← hn]
        omega⟩
    exact hax (hub hy (Finset.mem_insert_self a _))
  · rintro ⟨⟨hne, rfl⟩, hn⟩
    exact ⟨mem_ofAtoms.2 ⟨⟨hne, subset_rfl⟩, hn⟩,
      fun y hy ↦ Finset.coe_subset.1 (mem_ofAtoms.1 hy).1.2⟩

theorem isGreatest_iUnion_ofAtoms :
    IsGreatest (⋃ n, ofAtoms D n) x ↔ x.Nonempty ∧ ↑x = D := by
  rw [iUnion_ofAtoms]
  constructor
  · rintro ⟨hx, hub⟩
    obtain ⟨hne, hD⟩ := (mem_supClosure_image_singleton D x).1 hx
    exact ⟨hne, hD.antisymm fun a ha ↦
      Finset.singleton_subset_iff.1 (hub (subset_supClosure ⟨a, ha, rfl⟩))⟩
  · rintro ⟨hne, rfl⟩
    exact ⟨(mem_supClosure_image_singleton _ x).2 ⟨hne, subset_rfl⟩,
      fun y hy ↦ Finset.coe_subset.1 ((mem_supClosure_image_singleton _ y).1 hy).2⟩

end Atoms

/-! ### The definite article and kind reference -/

section Kind

variable {Atom : Type*} [DecidableEq Atom] {D : Set Atom} {n : ℕ}

/-- ∩ is defined on a count noun with its number argument filled where there are exactly that
many instances. -/
theorem down_ofAtoms_dom : (Kind.down (ofAtoms D n)).Dom ↔ n ≠ 0 ∧ D.encard = n := by
  simp only [Kind.down_dom, isGreatest_ofAtoms]
  constructor
  · rintro ⟨x, ⟨hne, rfl⟩, rfl⟩
    exact ⟨hne.card_ne_zero, Set.encard_coe_eq_coe_finsetCard x⟩
  · rintro ⟨hn, h⟩
    have hfin := Set.finite_of_encard_eq_coe h
    have hc : hfin.toFinset.card = n := by
      have := hfin.encard_eq_coe_toFinset_card
      rw [h] at this
      exact_mod_cast this.symm
    exact ⟨hfin.toFinset, ⟨Finset.card_pos.1 (by omega), hfin.coe_toFinset⟩, hc⟩

-- (63b)
theorem down_iUnion_ofAtoms_dom :
    (Kind.down (⋃ n, ofAtoms D n)).Dom ↔ D.Nonempty ∧ D.Finite := by
  simp only [Kind.down_dom, isGreatest_iUnion_ofAtoms]
  exact ⟨fun ⟨x, hne, hx⟩ ↦ hx ▸ ⟨Finset.coe_nonempty.2 hne, x.finite_toSet⟩,
    fun ⟨hne, hfin⟩ ↦ ⟨hfin.toFinset, hfin.toFinset_nonempty.2 hne, hfin.coe_toFinset⟩⟩

end Kind

/-! ### Composition -/

section Composition

open Interpreter ManySorted PhraseStructure

/-- (51c): Existential closure combines two predicates of individuals, which application does
not combine. -/
inductive ExistentialClosure : Ty Base → Ty Base → Ty Base → Type
  /-- Existential closure. -/
  | ex : ExistentialClosure .et .et .t

/-- The meaning of existential closure. -/
@[simp] def ExistentialClosure.eval (D : Base → Type) :
    {l r u : Ty Base} → ExistentialClosure l r u → l.Dom D → r.Dom D → u.Dom D
  | _, _, _, .ex, P, V => ∃ x, P x ∧ V x

/-- Two predicates of individuals are closed existentially. -/
def ExistentialClosure.rules : (l r : Ty Base) → List (Σ u, ExistentialClosure l r u)
  | .fn .e .t, .fn .e .t => [⟨.t, .ex⟩]
  | _, _ => []

theorem ExistentialClosure.mem_rules {l r u : Ty Base} (m : ExistentialClosure l r u) :
    ⟨u, m⟩ ∈ ExistentialClosure.rules l r := by
  cases m
  simp [ExistentialClosure.rules]

/-- Existential closure, as a language over the types. -/
@[reducible] def existentialClosure : Language (Ty Base) :=
  .mk₂ (fun _ _ ↦ PEmpty) ExistentialClosure

instance (D : Base → Type) : existentialClosure.Structure (Ty.Dom D) :=
  .mk₂ nofun (ExistentialClosure.eval D)

instance : existentialClosure.LocallyFinite :=
  .mk₂ (fun _ ↦ []) ExistentialClosure.rules nofun ExistentialClosure.mem_rules

/-- (51): The rules of composition are functional application and existential closure. -/
abbrev grammar : Language (Ty Base) := application.sum existentialClosure

-- (69a)
theorem rules_et_et : Application.rules (.et : Ty Base) .et = [] := by decide

/-- The words of the fragment. -/
inductive Word
  /-- The count noun *dog*. -/
  | dog
  /-- The semantic plural *-s*. -/
  | s
  /-- The indefinite article. -/
  | a
  /-- A number word. -/
  | number (k : ℕ)
  /-- The verbal predicate *barking*. -/
  | barking
  /-- Negation. -/
  | not

/-- The lexical items by type: the count noun (52a), the semantic plural (59b), a number (54),
a number as a determiner (67), (72), the verbal predicate, and negation. -/
inductive Item : Ty Base → Type
  | dog : Item (.n ⇒ .et)
  | plural : Item ((.n ⇒ .et) ⇒ .et)
  | number (k : ℕ) : Item .n
  | determiner (k : ℕ) : Item ((.n ⇒ .et) ⇒ .ett)
  | barking : Item .et
  | not : Item (.t ⇒ .t)

/-- The items of each word: a number word is a number or a determiner, and the indefinite
article the determiner of the number one. -/
def items : Word → List (Σ a, Item a)
  | .dog => [⟨_, .dog⟩]
  | .s => [⟨_, .plural⟩]
  | .a => [⟨_, .determiner 1⟩]
  | .number k => [⟨_, .number k⟩, ⟨_, .determiner k⟩]
  | .barking => [⟨_, .barking⟩]
  | .not => [⟨_, .not⟩]

variable {E : Type} (R : ℕ → Set E) (V : Set E)

/-- The denotation of an item, for a count noun `R` and a verbal predicate `V`. -/
def Item.val : {a : Ty Base} → Item a → a.Dom (Base.Dom E Unit)
  | _, .dog => fun n x ↦ x ∈ R n
  | _, .plural => fun R x ↦ ∃ n, R n x
  | _, .number k => k
  | _, .determiner k => fun R P ↦ ∃ x, R k x ∧ P x
  | _, .barking => fun x ↦ x ∈ V
  | _, .not => fun p ↦ ¬ p

/-- The meanings of a tree whose traces have type `τ`. -/
def meanings (τ : Ty Base) (t : Tree Unit Word) :
    List (Σ a : Ty Base, (ℕ → τ.Dom (Base.Dom E Unit)) → a.Dom (Base.Dom E Unit)) :=
  t.interpret grammar (Base.Dom E Unit) (fun _ ↦ τ) (fun i _ ↦ i.val R V) items

/-- (69) *Dogs are barking*. -/
def dogsBark : Tree Unit Word := tree% [[dog s] barking]

/-- *Dog is barking*. -/
def dogBarks : Tree Unit Word := tree% [dog barking]

/-- A phrase moved over negation, `[X [λ₁ [not [t₁ barking]]]]`. -/
def overNegation (X : Tree Unit Word) : Tree Unit Word :=
  tree% [(X) [λ 1 [not [(.tr 1) barking]]]]

variable (τ : Ty Base)

-- (69)
theorem meanings_dogsBark :
    meanings R V τ dogsBark = [⟨.t, fun _ ↦ ∃ x, (∃ n, x ∈ R n) ∧ x ∈ V⟩] :=
  rfl

/-- A count noun is a function of numbers, so it has no meaning with a verbal predicate. -/
theorem meanings_dogBarks : meanings R V τ dogBarks = [] :=
  rfl

-- (68)
theorem meanings_aDogBarks :
    meanings R V τ (tree% [[a dog] barking]) = [⟨.t, fun _ ↦ ∃ x, x ∈ R 1 ∧ x ∈ V⟩] :=
  rfl

/-- (70): A bare plural moved over negation, with a trace of its own type, is closed
existentially below negation. -/
theorem meanings_overNegation_bare :
    meanings R V .et (overNegation (tree% [dog s])) =
      [⟨.t, fun _ ↦ ¬ ∃ x, (∃ n, x ∈ R n) ∧ x ∈ V⟩] :=
  rfl

theorem meanings_overNegation_bare_e :
    meanings R V .e (overNegation (tree% [dog s])) =
      [⟨.t, fun _ ↦ ∃ x, (∃ n, x ∈ R n) ∧ ¬ x ∈ V⟩] :=
  rfl

theorem meanings_overNegation_bare_ett :
    meanings R V .ett (overNegation (tree% [dog s])) = [] :=
  rfl

/-- (71): A determiner phrase moved over negation takes scope over it with a trace of
individuals and below it with a trace of quantifiers. -/
theorem meanings_overNegation_a :
    meanings R V .e (overNegation (tree% [a dog])) =
        [⟨.t, fun _ ↦ ∃ x, x ∈ R 1 ∧ ¬ x ∈ V⟩] ∧
      meanings R V .ett (overNegation (tree% [a dog])) =
        [⟨.t, fun _ ↦ ¬ ∃ x, x ∈ R 1 ∧ x ∈ V⟩] :=
  ⟨rfl, rfl⟩

-- (72), (73): a number word with a trace of individuals, as a specifier and as a determiner
theorem meanings_overNegation_number_e (k : ℕ) :
    meanings R V .e (overNegation (tree% [⟨.number k⟩ dog])) =
      [⟨.t, fun _ ↦ ∃ x, x ∈ R k ∧ ¬ x ∈ V⟩, ⟨.t, fun _ ↦ ∃ x, x ∈ R k ∧ ¬ x ∈ V⟩] :=
  rfl

-- a number word as a specifier, with a trace of its phrase's type
theorem meanings_overNegation_number_et (k : ℕ) :
    meanings R V .et (overNegation (tree% [⟨.number k⟩ dog])) =
      [⟨.t, fun _ ↦ ¬ ∃ x, x ∈ R k ∧ x ∈ V⟩] :=
  rfl

-- With one dog, and it barking, *Dogs aren't barking* is false.
theorem not_of_mem_meanings_overNegation_bare {Atom : Type} [DecidableEq Atom] {a : Atom}
    {V : Set (Finset Atom)} (ha : {a} ∈ V) {v : (ℕ → Finset Atom → Prop) → Prop}
    (hv : ⟨.t, v⟩ ∈ meanings (ofAtoms {a}) V .et (overNegation (tree% [dog s])))
    (g : ℕ → Finset Atom → Prop) : ¬ v g := by
  rw [meanings_overNegation_bare, List.mem_singleton, Sigma.mk.injEq] at hv
  obtain rfl := eq_of_heq hv.2
  exact not_not.2 ⟨{a}, ⟨1, by simp⟩, ha⟩

end Composition

end Krifka2003
