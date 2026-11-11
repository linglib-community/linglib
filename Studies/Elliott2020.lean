/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Data.Set.Monad
public import Linglib.Logic.Trivalent.Basic
public import Linglib.Logic.Assignment
public import Linglib.Semantics.Dynamic.State
public import Linglib.Semantics.Dynamic.Update
public import Linglib.Data.Examples.Elliott2020

/-!
# Elliott (2020): Towards a principled logic of anaphora

In Elliott's Dynamic Alternative Semantics a sentence maps a partial assignment to pairs of a
strong Kleene truth value and an output assignment. Each connective lifts its strong Kleene truth
function, passing assignments from left to right, and an existential is the positive closure of
the DPL existential, which keeps the true outputs and otherwise returns the input. The DPL
existential is a random reset bound to its scope, but positive closure is not a bind, so the
existential is not monadic in Charlow's sense. Negation swaps
the positive and negative outputs, so double negation and de Morgan's laws hold, bathroom
sentences and Stone disjunctions license anaphora, and updating a set of world–assignment pairs
makes a disjunction look externally static until one disjunct is ruled out.

## Implementation notes

* A sentence denotes a `StateSet D Trivalent`, a map from assignments to sets of truth value and
  output pairs (Def. A.1), as in the paper's appendix; there is no syntax. Its relation at
  `true` (`StateT.rel`) is the positive extension as a DPL relation. Atoms are monadic, and
  a constant atom is `pure` of its truth value.
* The existentials of Defs. 2.3 and 3.3 are one definition with a parameter; the destructive one
  overwrites a valued variable, and the guarded one is undefined there.
* Every output values what its input values (`Expanding`), for both existentials; the
  familiarity results rest on it.
* The dynamic Hurford constraint (70) is read as validity, over every model and input. Read
  pointwise, it would mark every disjunction with a bivalent first disjunct odd.

## TODO

The universal readings of App. B, by innocent inclusion over subdomain alternatives, are not
formalized.

## References

* [elliott-2020]
* [groenendijk-stokhof-1991]
* [charlow-2014]
* [beaver-2001]
* [van-den-berg-1996]
* [rothschild-2017]
* [stone-1992]
-/

@[expose] public section

attribute [local instance] Set.monad

namespace Elliott2020

open Trivalent (ofProp meetWeak)
open DynamicSemantics
open scoped SetRel

variable {D : Type}

/-! ### Dynamic propositions -/

/-- The State.Set applicative over partial assignments (Def. A.3). -/
abbrev StateSet (D : Type) := StateT (ℕ → Part D) Set

/-! ### Atomic sentences -/

open Classical in
/-- The value of `P n` at `g`, `∂ (n ∈ dom g) ∧ gₙ ∈ P`, with Beaver's ∂ and a weak Kleene
conjunction (Def. 2.2 and fn. 10). -/
noncomputable def valueAt (P : Set D) (g : ℕ → Part D) (n : ℕ) : Trivalent :=
  meetWeak ((ofProp (g n).Dom) ⊔ .undefined) (ofProp (∃ d ∈ g n, d ∈ P))

@[simp] theorem valueAt_of_eq_bot (P : Set D) {g : ℕ → Part D} {n : ℕ} (h : g n = ⊥) :
    valueAt P g n = .undefined := by
  simp [valueAt, h, Part.bot_eq_none, Part.not_none_dom, Part.notMem_none]

open Classical in
@[simp] theorem valueAt_of_mem (P : Set D) {g : ℕ → Part D} {n : ℕ} {d : D}
    (h : d ∈ g n) : valueAt P g n = ofProp (d ∈ P) := by
  simp [valueAt, Part.eq_some_iff.2 h]

/-- The updated register holds its new value. -/
private theorem mem_update_self (g : ℕ → Part D) (n : ℕ) (x : D) :
    x ∈ Function.update g n (Part.some x) n := by simp

/-- A monadic predicate of a variable (Def. 2.2). -/
noncomputable def atom (P : Set D) (n : ℕ) : StateSet D Trivalent := fun g ↦ {(valueAt P g n, g)}

open Classical in
/-- A monadic predicate of an individual constant (Def. 2.2), whose value does not depend on the
assignment. -/
noncomputable def atomConst (P : Set D) (c : D) : StateSet D Trivalent :=
  pure (ofProp (c ∈ P))

@[simp] theorem mem_atom {P : Set D} {n : ℕ} {g : ℕ → Part D}
    {p : Trivalent × (ℕ → Part D)} : p ∈ atom P n g ↔ p = (valueAt P g n, g) := Iff.rfl

open Classical in
@[simp] theorem mem_atomConst {P : Set D} {c : D} {g : ℕ → Part D}
    {p : Trivalent × (ℕ → Part D)} : p ∈ atomConst P c g ↔ p = (ofProp (c ∈ P), g) :=
  Iff.rfl

/-! ### Connectives

Each connective lifts its strong Kleene truth function, passing the output of its first argument
to its second (Def. 2.9); in the applicative a binary one is `η R ⊛ m ⊛ n` (Def. A.3). -/

/-- Negation lifts strong Kleene negation (Def. 2.4). -/
def neg (m : StateSet D Trivalent) : StateSet D Trivalent := compl <$> m

/-- Conjunction lifts strong Kleene conjunction (Def. 2.10). -/
def conj (m n : StateSet D Trivalent) : StateSet D Trivalent := (· ⊓ ·) <$> m <*> n

/-- Disjunction lifts strong Kleene disjunction (Def. 2.11). -/
def disj (m n : StateSet D Trivalent) : StateSet D Trivalent := (· ⊔ ·) <$> m <*> n

/-- Material implication lifts strong Kleene `¬t ∨ u` (§2.9). -/
def imp (m n : StateSet D Trivalent) : StateSet D Trivalent := (fun t u ↦ tᶜ ⊔ u) <$> m <*> n

/-- The applicative laws of Def. A.4 are those of `StateT` over `Set`. -/
example : LawfulApplicative (StateSet D) := inferInstance

/-! ### Extensions and truth -/

/-- `extension v m g` is the set of outputs of `m` at `g` tagged `v`; at `true`, `false` and
`undefined` these are the positive, negative and maybe extensions (Def. 2.5). -/
def extension (v : Trivalent) (m : StateSet D Trivalent) (g : ℕ → Part D) :
    Set (ℕ → Part D) :=
  {h | (v, h) ∈ m g}

@[simp] theorem mem_extension {v : Trivalent} {m : StateSet D Trivalent}
    {g h : ℕ → Part D} : h ∈ extension v m g ↔ (v, h) ∈ m g := Iff.rfl

/-- `m` is true at `g` when its positive extension is nonempty (Def. 2.6). -/
def IsTrue (m : StateSet D Trivalent) (g : ℕ → Part D) : Prop :=
  (extension .true m g).Nonempty

/-- `m` is false at `g` when it has no positive output and some negative one (Def. 2.6). -/
def IsFalse (m : StateSet D Trivalent) (g : ℕ → Part D) : Prop :=
  extension .true m g = ∅ ∧ (extension .false m g).Nonempty

/-- `m` is maybe at `g` when all its outputs are tagged maybe (Def. 2.6). -/
def IsIndet (m : StateSet D Trivalent) (g : ℕ → Part D) : Prop :=
  extension .true m g = ∅ ∧ extension .false m g = ∅ ∧ (extension .undefined m g).Nonempty

-- Def. 3.2
theorem isTrue_or_isFalse_iff {m : StateSet D Trivalent} {g : ℕ → Part D} :
    IsTrue m g ∨ IsFalse m g ↔
      (extension .true m g).Nonempty ∨ (extension .false m g).Nonempty := by
  rcases (extension .true m g).eq_empty_or_nonempty with h | h <;> simp [IsTrue, IsFalse, h]

theorem rel_neg (v : Trivalent) (m : StateSet D Trivalent) :
    StateT.rel (neg m) v = StateT.rel m (vᶜ) := by
  rw [neg, StateT.rel_map]
  ext p
  simp only [Set.mem_iUnion, exists_prop]
  exact ⟨fun ⟨t, ht, hp⟩ ↦ by rwa [← ht, Trivalent.compl_compl],
    fun hp ↦ ⟨vᶜ, Trivalent.compl_compl v, hp⟩⟩

theorem extension_neg (v : Trivalent) (m : StateSet D Trivalent) (g : ℕ → Part D) :
    extension v (neg m) g = extension (vᶜ) m g :=
  Set.ext fun h ↦ Set.ext_iff.1 (rel_neg v m) (g, h)

/-- Double negation is the identity (Obs. 2.2). -/
theorem neg_neg (m : StateSet D Trivalent) : neg (neg m) = m := by
  simp only [neg, Functor.map_map, Trivalent.compl_compl, id_map']

/-- de Morgan's law for disjunction (Obs. 2.6). -/
theorem neg_disj (m n : StateSet D Trivalent) : neg (disj m n) = conj (neg m) (neg n) := by
  simp only [neg, disj, conj, map_seq, seq_map_assoc, Functor.map_map,
    Function.comp_def, Trivalent.compl_sup]

/-- de Morgan's law for conjunction (Obs. 2.6). -/
theorem neg_conj (m n : StateSet D Trivalent) : neg (conj m n) = disj (neg m) (neg n) := by
  simp only [neg, disj, conj, map_seq, seq_map_assoc, Functor.map_map,
    Function.comp_def, Trivalent.compl_inf]

theorem imp_eq_disj_neg (m n : StateSet D Trivalent) : imp m n = disj (neg m) n := by
  simp only [imp, disj, neg, Functor.map_map]

/-! ### Existential quantification -/

/-- A DPL existential either overwrites a valued variable, as in Def. 2.3, or is undefined there,
as in Def. 3.3. -/
inductive Existential where
  /-- The existential of Def. 2.3 resets the variable whether or not it is valued. -/
  | destructive
  /-- The existential of Def. 3.3 resets only an unvalued variable. -/
  | guarded
  deriving DecidableEq, Repr

/-- When an existential may reset `n` at `g`. -/
def Existential.Fresh : Existential → (ℕ → Part D) → ℕ → Prop
  | .destructive, _, _ => True
  | .guarded, g, n => g n = ⊥

@[simp] theorem Existential.fresh_destructive (g : ℕ → Part D) (n : ℕ) :
    Existential.destructive.Fresh g n := trivial

@[simp] theorem Existential.fresh_guarded_iff (g : ℕ → Part D) (n : ℕ) :
    Existential.guarded.Fresh g n ↔ g n = ⊥ := Iff.rfl

/-- The DPL existential takes the union of `m` over the resets of `n` when it may reset `n`, and is
maybe otherwise (Defs. 2.3 and 3.3). -/
def dplExists (e : Existential) (n : ℕ) (m : StateSet D Trivalent) : StateSet D Trivalent := fun g ↦
  {p | e.Fresh g n ∧ ∃ x, p ∈ m (Function.update g n (Part.some x))} ∪
    {p | ¬ e.Fresh g n ∧ p = (.undefined, g)}

/-- Positive closure keeps the true outputs, or else returns the input tagged false or maybe
(Def. 2.7). -/
def positiveClosure (m : StateSet D Trivalent) : StateSet D Trivalent := fun g ↦
  {p | p.1 = .true ∧ p ∈ m g} ∪ {p | IsFalse m g ∧ p = (.false, g)} ∪
    {p | IsIndet m g ∧ p = (.undefined, g)}

/-- Existential quantification, the positive closure of the DPL existential (Def. 2.8). -/
def exists_ (e : Existential) (n : ℕ) (m : StateSet D Trivalent) : StateSet D Trivalent :=
  positiveClosure (dplExists e n m)

@[simp] theorem mem_dplExists {e : Existential} {n : ℕ} {m : StateSet D Trivalent}
    {g : ℕ → Part D} {p : Trivalent × (ℕ → Part D)} :
    p ∈ dplExists e n m g ↔
      (e.Fresh g n ∧ ∃ x, p ∈ m (Function.update g n (Part.some x))) ∨
        (¬ e.Fresh g n ∧ p = (.undefined, g)) :=
  Iff.rfl

@[simp] theorem mem_positiveClosure {m : StateSet D Trivalent} {g : ℕ → Part D}
    {p : Trivalent × (ℕ → Part D)} :
    p ∈ positiveClosure m g ↔ (p.1 = .true ∧ p ∈ m g) ∨ (IsFalse m g ∧ p = (.false, g)) ∨
      (IsIndet m g ∧ p = (.undefined, g)) := by
  simp only [positiveClosure, Set.mem_union, Set.mem_ofPred_eq, or_assoc]

-- (19a)
@[simp] theorem extension_true_positiveClosure (m : StateSet D Trivalent)
    (g : ℕ → Part D) :
    extension .true (positiveClosure m) g = extension .true m g := by
  ext h
  simp only [mem_extension, mem_positiveClosure, true_and, Prod.mk.injEq]
  exact ⟨by rintro (h | ⟨-, ⟨⟩, -⟩ | ⟨-, ⟨⟩, -⟩); exact h, Or.inl⟩

-- (19b)
theorem extension_false_positiveClosure (m : StateSet D Trivalent) (g : ℕ → Part D) :
    extension .false (positiveClosure m) g = {h | IsFalse m g ∧ h = g} := by
  ext h
  simp only [mem_extension, mem_positiveClosure, Prod.mk.injEq, Set.mem_ofPred_eq]
  constructor
  · rintro (⟨⟨⟩, -⟩ | ⟨hf, -, rfl⟩ | ⟨-, ⟨⟩, -⟩); exact ⟨hf, rfl⟩
  · rintro ⟨hf, rfl⟩; exact Or.inr (Or.inl ⟨hf, by simp⟩)

theorem dplExists_neg (e : Existential) (n : ℕ) (m : StateSet D Trivalent) :
    dplExists e n (neg m) = neg (dplExists e n m) := by
  funext g; ext ⟨v, h⟩
  simp only [mem_dplExists, neg, Set.mk_mem_stateT_map, Prod.mk.injEq]
  constructor
  · rintro (⟨hf, x, t, ht, rfl⟩ | ⟨hf, rfl, rfl⟩)
    · exact ⟨t, .inl ⟨hf, x, ht⟩, rfl⟩
    · exact ⟨.undefined, .inr ⟨hf, rfl, rfl⟩, rfl⟩
  · rintro ⟨t, (⟨hf, x, ht⟩ | ⟨hf, rfl, rfl⟩), rfl⟩
    · exact .inl ⟨hf, x, t, ht, rfl⟩
    · exact .inr ⟨hf, rfl, rfl⟩

theorem exists_guarded_of_ne_bot {n : ℕ} {m : StateSet D Trivalent} {g : ℕ → Part D}
    (hg : g n ≠ ⊥) : exists_ .guarded n m g = {(.undefined, g)} := by
  have heps : dplExists .guarded n m g = {(.undefined, g)} := by
    ext p; simp [mem_dplExists, hg]
  have hT : extension .true (dplExists .guarded n m) g = ∅ := by ext h; simp [heps]
  have hF : extension .false (dplExists .guarded n m) g = ∅ := by ext h; simp [heps]
  have hI : (extension .undefined (dplExists .guarded n m) g).Nonempty := ⟨g, by simp [heps]⟩
  ext ⟨v, h⟩
  rw [exists_, mem_positiveClosure, heps]
  simp only [IsFalse, IsIndet, hT, hF, hI, Set.not_nonempty_empty, Set.mem_singleton_iff,
    Prod.mk.injEq, and_true, true_and, false_and, false_or]
  exact ⟨by rintro (⟨rfl, ⟨⟩, -⟩ | h); exact h, Or.inr⟩

/-! ### The existential and bind

Charlow decomposes the DPL existential into bind applied to a set of alternatives; Elliott's
existential is not straightforwardly compatible with that decomposition (App. A). The DPL
existential decomposes, a random reset bound to its scope, but positive closure is not a bind. -/

/-- Random assignment, resetting `n` to any individual. -/
def reset (n : ℕ) : StateSet D PUnit := fun g ↦
  {q | ∃ x, q = ((), Function.update g n (Part.some x))}

theorem dplExists_destructive (n : ℕ) (m : StateSet D Trivalent) :
    dplExists .destructive n m = reset n >>= fun _ ↦ m := by
  funext g
  ext p
  simp only [mem_dplExists, Existential.fresh_destructive, true_and, not_true_eq_false,
    false_and, or_false, Set.mem_stateT_bind, reset, Set.mem_ofPred_eq]
  constructor
  · exact fun ⟨x, hx⟩ ↦ ⟨_, ⟨x, rfl⟩, hx⟩
  · rintro ⟨_, ⟨x, rfl⟩, hx⟩
    exact ⟨x, hx⟩

/-- Positive closure is not a bind, since a bind treats each output separately while closure drops
the false outputs exactly when a true one exists (App. A). -/
theorem not_exists_bind_eq_positiveClosure :
    ¬ ∃ k : Trivalent → StateSet D Trivalent, ∀ m, positiveClosure m = m >>= k := by
  rintro ⟨k, hk⟩
  have hk₀ : ((.false : Trivalent), (⊥ : ℕ → Part D)) ∈ k .false ⊥ := by
    have h := hk (pure .false)
    have : ((.false : Trivalent), (⊥ : ℕ → Part D)) ∈
        positiveClosure (pure .false) ⊥ := by
      rw [mem_positiveClosure]
      refine .inr (.inl ⟨⟨?_, ⊥, rfl⟩, rfl⟩)
      ext h
      simp [Set.mem_stateT_pure]
    rw [h] at this
    simpa using this
  let both : StateSet D Trivalent := fun g ↦ {(.true, g), (.false, g)}
  have hf : ((.false : Trivalent), (⊥ : ℕ → Part D)) ∉ positiveClosure both ⊥ := by
    simp [mem_positiveClosure, IsFalse, IsIndet, both, Set.eq_empty_iff_forall_notMem]
  exact hf (hk both ▸ Set.mem_stateT_bind _ _ _ _ |>.2 ⟨(.false, ⊥), by simp [both], hk₀⟩)

/-! ### Positive extensions and DPL

At `true` the relation a sentence induces (`StateT.rel`) is its positive extension, a DPL
relation between assignments. -/

-- (26a)
theorem rel_true_conj (m n : StateSet D Trivalent) :
    StateT.rel (conj m n) .true = StateT.rel m .true ○ StateT.rel n .true := by
  rw [conj, StateT.rel_map_seq]
  ext p
  simp only [Set.mem_iUnion, exists_prop, Trivalent.inf_eq_true_iff]
  exact ⟨fun ⟨_, _, ⟨rfl, rfl⟩, h⟩ ↦ h, fun h ↦ ⟨_, _, ⟨rfl, rfl⟩, h⟩⟩

-- (32b)
theorem rel_false_disj (m n : StateSet D Trivalent) :
    StateT.rel (disj m n) .false = StateT.rel m .false ○ StateT.rel n .false := by
  rw [disj, StateT.rel_map_seq]
  ext p
  simp only [Set.mem_iUnion, exists_prop, Trivalent.sup_eq_false_iff]
  exact ⟨fun ⟨_, _, ⟨rfl, rfl⟩, h⟩ ↦ h, fun h ↦ ⟨_, _, ⟨rfl, rfl⟩, h⟩⟩

-- (22a)
theorem isTest_rel_true_neg_exists (e : Existential) (n : ℕ) (m : StateSet D Trivalent) :
    Update.IsTest (StateT.rel (neg (exists_ e n m)) .true) := by
  rintro ⟨g, h⟩ hgh
  rw [rel_neg] at hgh
  have : h ∈ extension .false (exists_ e n m) g := hgh
  rw [exists_, extension_false_positiveClosure] at this
  exact this.2.symm

-- (18)
theorem not_isTest_rel_true_neg_dplExists [Nonempty D] :
    ¬ Update.IsTest (StateT.rel (neg (dplExists .destructive 1 (atom (∅ : Set D) 1))) .true) := by
  obtain ⟨x⟩ := ‹Nonempty D›
  intro h
  have hmem : ((⊥ : ℕ → Part D), Function.update (⊥ : ℕ → Part D) 1 (Part.some x)) ∈
      StateT.rel (neg (dplExists .destructive 1 (atom (∅ : Set D) 1))) .true := by
    rw [rel_neg]
    show (.false, _) ∈ dplExists _ _ _ _
    simp only [mem_dplExists]
    exact .inl ⟨trivial, x, by simp⟩
  have h1 : (⊥ : ℕ → Part D) = Function.update (⊥ : ℕ → Part D) 1 (Part.some x) := h hmem
  simpa using congrFun h1 1

/-! ### The extensions of the connectives -/

-- (32a)
theorem mem_extension_true_disj {m n : StateSet D Trivalent} {g i : ℕ → Part D} :
    i ∈ extension .true (disj m n) g ↔
      (∃ h ∈ extension .true m g, ∃ u, (u, i) ∈ n h) ∨
        ∃ t h, (t, h) ∈ m g ∧ i ∈ extension .true n h := by
  simp only [mem_extension, disj, Set.mk_mem_stateT_map_seq]
  grind [Trivalent.sup_eq_true_iff]

-- (32b)
theorem mem_extension_false_disj {m n : StateSet D Trivalent} {g i : ℕ → Part D} :
    i ∈ extension .false (disj m n) g ↔ ∃ h ∈ extension .false m g, i ∈ extension .false n h := by
  have : (g, i) ∈ StateT.rel (disj m n) .false ↔
      (g, i) ∈ StateT.rel m .false ○ StateT.rel n .false := by
    rw [rel_false_disj]
  simpa [SetRel.mem_comp] using this

-- (38a)
theorem mem_extension_true_imp {m n : StateSet D Trivalent} {g i : ℕ → Part D} :
    i ∈ extension .true (imp m n) g ↔
      (∃ h ∈ extension .false m g, ∃ u, (u, i) ∈ n h) ∨
        ∃ t h, (t, h) ∈ m g ∧ i ∈ extension .true n h := by
  simp only [mem_extension, imp, Set.mk_mem_stateT_map_seq]
  grind [Trivalent.sup_eq_true_iff, Trivalent.compl_eq_true_iff]

-- (26b)
theorem mem_extension_false_conj {m n : StateSet D Trivalent} {g i : ℕ → Part D} :
    i ∈ extension .false (conj m n) g ↔
      (∃ h ∈ extension .false m g, ∃ u, (u, i) ∈ n h) ∨
        ∃ t h, (t, h) ∈ m g ∧ i ∈ extension .false n h := by
  simp only [mem_extension, conj, Set.mk_mem_stateT_map_seq]
  grind [Trivalent.inf_eq_false_iff]

/-! ### Egli's theorem -/

theorem mem_extension_true_conj {m n : StateSet D Trivalent} {g i : ℕ → Part D} :
    i ∈ extension .true (conj m n) g ↔ ∃ h ∈ extension .true m g, i ∈ extension .true n h := by
  have : (g, i) ∈ StateT.rel (conj m n) .true ↔
      (g, i) ∈ StateT.rel m .true ○ StateT.rel n .true := by
    rw [rel_true_conj]
  simpa [SetRel.mem_comp] using this

/-- Egli's theorem for positive extensions, for either existential (Obs. 2.4). -/
theorem egli (e : Existential) (n : ℕ) (m k : StateSet D Trivalent) (g : ℕ → Part D) :
    extension .true (exists_ e n (conj m k)) g = extension .true (conj (exists_ e n m) k) g := by
  ext i
  rw [mem_extension_true_conj]
  simp only [exists_, extension_true_positiveClosure]
  constructor
  · intro hi
    rw [mem_extension, mem_dplExists] at hi
    rcases hi with ⟨hf, x, hx⟩ | ⟨-, hx⟩
    · rw [← mem_extension, mem_extension_true_conj] at hx
      obtain ⟨h, hm, hk⟩ := hx
      exact ⟨h, by rw [mem_extension, mem_dplExists]; exact .inl ⟨hf, x, hm⟩, hk⟩
    · simp at hx
  · rintro ⟨h, hm, hk⟩
    rw [mem_extension, mem_dplExists] at hm
    rcases hm with ⟨hf, x, hm⟩ | ⟨-, hm⟩
    · rw [mem_extension, mem_dplExists]
      exact .inl ⟨hf, x, by rw [← mem_extension, mem_extension_true_conj]; exact ⟨h, hm, hk⟩⟩
    · simp at hm


/-! ### Existentials over atoms -/

section Atoms

open Classical

variable (W B U : Set D) {e : Existential} {n : ℕ} {g : ℕ → Part D}

theorem mem_atom_update (x : D) {v : Trivalent} {h : ℕ → Part D} :
    (v, h) ∈ atom W n (Function.update g n (Part.some x)) ↔
      v = ofProp (x ∈ W) ∧ h = Function.update g n (Part.some x) := by
  rw [mem_atom, valueAt_of_mem W (mem_update_self g n x), Prod.mk.injEq]

theorem neg_atom (n : ℕ) : neg (atom W n) = atom Wᶜ n := by
  funext g
  have key : (valueAt W g n)ᶜ = valueAt Wᶜ g n := by
    rcases (g n).eq_none_or_eq_some with hg | ⟨d, hg⟩
    · simp [valueAt_of_eq_bot _ hg]
    · by_cases hd : d ∈ W <;> simp [valueAt_of_mem _ (Part.eq_some_iff.1 hg), hd]
  ext ⟨v, h⟩
  simp only [neg, Set.mk_mem_stateT_map, mem_atom, Prod.mk.injEq]
  exact ⟨by rintro ⟨t, ⟨rfl, rfl⟩, rfl⟩; exact ⟨key, rfl⟩,
    by rintro ⟨rfl, rfl⟩; exact ⟨_, ⟨rfl, rfl⟩, key.symm⟩⟩

-- (17a)
theorem extension_true_dplExists_atom (hf : e.Fresh g n) :
    extension .true (dplExists e n (atom W n)) g =
      {h | ∃ x ∈ W, h = Function.update g n (Part.some x)} := by
  ext h
  simp only [mem_extension, mem_dplExists, hf, true_and, not_true_eq_false, false_and,
    or_false, mem_atom_update, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, Trivalent.ofProp_eq_true_iff.1 hx.symm, rfl⟩
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, by simp [hx], rfl⟩

-- (17b)
theorem extension_false_dplExists_atom (hf : e.Fresh g n) :
    extension .false (dplExists e n (atom W n)) g =
      {h | ∃ x ∉ W, h = Function.update g n (Part.some x)} := by
  ext h
  simp only [mem_extension, mem_dplExists, hf, true_and, not_true_eq_false, false_and,
    or_false, mem_atom_update, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, Trivalent.ofProp_eq_false_iff.1 hx.symm, rfl⟩
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, by simp [hx], rfl⟩

theorem extension_indet_dplExists_atom (hf : e.Fresh g n) :
    extension .undefined (dplExists e n (atom W n)) g = ∅ := by
  ext h
  rw [mem_extension, mem_dplExists]
  simp only [hf, true_and, not_true_eq_false, false_and, or_false, Set.mem_empty_iff_false,
    iff_false, not_exists]
  intro x hx
  rw [mem_atom_update] at hx
  exact Trivalent.ofProp_ne_undefined hx.1.symm

-- (20a)
theorem extension_true_exists_atom (hf : e.Fresh g n) :
    extension .true (exists_ e n (atom W n)) g =
      {h | ∃ x ∈ W, h = Function.update g n (Part.some x)} := by
  rw [exists_, extension_true_positiveClosure, extension_true_dplExists_atom W hf]

theorem isFalse_dplExists_atom_iff [Nonempty D] (hf : e.Fresh g n) :
    IsFalse (dplExists e n (atom W n)) g ↔ W = ∅ := by
  rw [IsFalse, extension_true_dplExists_atom W hf, extension_false_dplExists_atom W hf]
  constructor
  · rintro ⟨hpos, -⟩
    exact Set.eq_empty_iff_forall_notMem.2 fun x hx ↦
      Set.eq_empty_iff_forall_notMem.1 hpos (Function.update g n (Part.some x)) ⟨x, hx, rfl⟩
  · intro hW
    obtain ⟨x⟩ := ‹Nonempty D›
    exact ⟨Set.eq_empty_iff_forall_notMem.2 fun _ ⟨x, hx, _⟩ ↦ by simp [hW] at hx,
      ⟨Function.update g n (Part.some x), x, by simp [hW], rfl⟩⟩

theorem extension_false_exists_atom [Nonempty D] (hf : e.Fresh g n) :
    extension .false (exists_ e n (atom W n)) g = {h | h = g ∧ W = ∅} := by
  rw [exists_, extension_false_positiveClosure]
  ext h
  simp only [Set.mem_ofPred_eq, isFalse_dplExists_atom_iff W hf, and_comm]

-- (22a)
theorem extension_true_neg_exists_atom [Nonempty D] (hf : e.Fresh g n) :
    extension .true (neg (exists_ e n (atom W n))) g = {h | h = g ∧ W = ∅} := by
  rw [extension_neg, Trivalent.compl_true, extension_false_exists_atom W hf]

-- (22b)
theorem extension_false_neg_exists_atom (hf : e.Fresh g n) :
    extension .false (neg (exists_ e n (atom W n))) g =
      {h | ∃ x ∈ W, h = Function.update g n (Part.some x)} := by
  rw [extension_neg, Trivalent.compl_false, extension_true_exists_atom W hf]

theorem extension_indet_neg_exists_atom (hf : e.Fresh g n) :
    extension .undefined (neg (exists_ e n (atom W n))) g = ∅ := by
  rw [extension_neg, Trivalent.compl_undefined, exists_]
  ext h
  simp only [mem_extension, mem_positiveClosure, Set.mem_empty_iff_false, iff_false,
    Prod.mk.injEq]
  rintro (⟨⟨⟩, -⟩ | ⟨-, ⟨⟩, -⟩ | ⟨⟨-, -, hne⟩, -, rfl⟩)
  rw [extension_indet_dplExists_atom W hf] at hne
  exact hne.ne_empty rfl

/-- The bathroom sentence `¬ ∃₁ B 1 ∨ U 1` is verified by the input when there is no bathroom, and
by the resets of 1 to bathrooms upstairs ((35)). -/
theorem extension_true_bathroom [Nonempty D] (hf : e.Fresh g 1) :
    extension .true (disj (neg (exists_ e 1 (atom B 1))) (atom U 1)) g =
      {h | h = g ∧ B = ∅} ∪ {h | ∃ x ∈ B, x ∈ U ∧ h = Function.update g 1 (Part.some x)} := by
  ext i
  rw [mem_extension_true_disj, extension_true_neg_exists_atom B hf, Set.mem_union]
  constructor
  · rintro (⟨h, ⟨rfl, hB⟩, u, hu⟩ | ⟨t, h, hm, hi⟩)
    · exact .inl ⟨(Prod.mk.inj (mem_atom.1 hu)).2, hB⟩
    · rcases t with _ | _ | _
      · have : h ∈ extension .false (neg (exists_ e 1 (atom B 1))) g := hm
        rw [extension_false_neg_exists_atom B hf] at this
        obtain ⟨x, hxB, rfl⟩ := this
        rw [mem_extension, mem_atom_update] at hi
        exact .inr ⟨x, hxB, Trivalent.ofProp_eq_true_iff.1 hi.1.symm, hi.2⟩
      · have : h ∈ extension .undefined (neg (exists_ e 1 (atom B 1))) g := hm
        rw [extension_indet_neg_exists_atom B hf] at this
        exact absurd this (Set.notMem_empty h)
      · have : h ∈ extension .true (neg (exists_ e 1 (atom B 1))) g := hm
        rw [extension_true_neg_exists_atom B hf] at this
        obtain ⟨rfl, hB⟩ := this
        exact .inl ⟨(Prod.mk.inj (mem_atom.1 hi)).2, hB⟩
  · rintro (⟨rfl, hB⟩ | ⟨x, hxB, hxU, rfl⟩)
    · exact .inl ⟨i, ⟨rfl, hB⟩, _, rfl⟩
    · refine .inr ⟨.false, Function.update g 1 (Part.some x), ?_, ?_⟩
      · show Function.update g 1 (Part.some x) ∈ extension .false (neg (exists_ e 1 (atom B 1))) g
        rw [extension_false_neg_exists_atom B hf]; exact ⟨x, hxB, rfl⟩
      · rw [mem_extension, mem_atom_update]; exact ⟨by simp [hxU], rfl⟩

theorem extension_false_bathroom (hf : e.Fresh g 1) :
    extension .false (disj (neg (exists_ e 1 (atom B 1))) (atom U 1)) g =
      {h | ∃ x ∈ B, x ∉ U ∧ h = Function.update g 1 (Part.some x)} := by
  ext i
  rw [mem_extension_false_disj, extension_false_neg_exists_atom B hf]
  constructor
  · rintro ⟨h, ⟨x, hxB, rfl⟩, hi⟩
    rw [mem_extension, mem_atom_update] at hi
    exact ⟨x, hxB, Trivalent.ofProp_eq_false_iff.1 hi.1.symm, hi.2⟩
  · rintro ⟨x, hxB, hxU, rfl⟩
    exact ⟨Function.update g 1 (Part.some x), ⟨x, hxB, rfl⟩,
      by rw [mem_extension, mem_atom_update]; simp [hxU]⟩

-- (42)
theorem extension_true_donkey [Nonempty D] (hf : e.Fresh g 1) :
    extension .true (imp (exists_ e 1 (atom B 1)) (atom U 1)) g =
      {h | h = g ∧ B = ∅} ∪ {h | ∃ x ∈ B, x ∈ U ∧ h = Function.update g 1 (Part.some x)} := by
  rw [imp_eq_disj_neg, extension_true_bathroom B U hf]

-- (43)
theorem extension_false_donkey (hf : e.Fresh g 1) :
    extension .false (imp (exists_ e 1 (atom B 1)) (atom U 1)) g =
      {h | ∃ x ∈ B, x ∉ U ∧ h = Function.update g 1 (Part.some x)} := by
  rw [imp_eq_disj_neg, extension_false_bathroom B U hf]

-- (27)
theorem extension_true_conj_atom_exists (P Q : Set D) (hg : g 1 = ⊥) :
    extension .true (conj (atom P 1) (exists_ e 1 (atom Q 1))) g = ∅ := by
  ext i
  simp only [Set.mem_empty_iff_false, iff_false]
  rw [mem_extension_true_conj]
  rintro ⟨h, hh, -⟩
  rw [mem_extension, mem_atom, valueAt_of_eq_bot P hg] at hh
  simp at hh

theorem extension_true_conj_exists_atom (P Q : Set D) (hf : e.Fresh g 1) :
    extension .true (conj (exists_ e 1 (atom P 1)) (atom Q 1)) g =
      {h | ∃ x ∈ P, x ∈ Q ∧ h = Function.update g 1 (Part.some x)} := by
  ext i
  rw [mem_extension_true_conj, extension_true_exists_atom P hf]
  constructor
  · rintro ⟨h, ⟨x, hxP, rfl⟩, hi⟩
    rw [mem_extension, mem_atom_update] at hi
    exact ⟨x, hxP, Trivalent.ofProp_eq_true_iff.1 hi.1.symm, hi.2⟩
  · rintro ⟨x, hxP, hxQ, rfl⟩
    exact ⟨Function.update g 1 (Part.some x), ⟨x, hxP, rfl⟩,
      by rw [mem_extension, mem_atom_update]; simp [hxQ]⟩

-- (30), (31)
theorem extension_false_conj_exists_atom [Nonempty D] (P Q : Set D) (hf : e.Fresh g 1) :
    extension .false (conj (exists_ e 1 (atom P 1)) (atom Q 1)) g =
      {h | h = g ∧ P = ∅} ∪ {h | ∃ x ∈ P, x ∉ Q ∧ h = Function.update g 1 (Part.some x)} := by
  have h := extension_neg .true (conj (exists_ e 1 (atom P 1)) (atom Q 1)) g
  rw [neg_conj, neg_atom, extension_true_bathroom P Qᶜ hf] at h
  exact h.symm

end Atoms

/-- Egli's theorem fails for negative extensions (Obs. 2.5). When everyone walked in and nobody sat
down, the input falsifies `∃₁ (W 1 ∧ S 1)` but only its resets falsify `∃₁ W 1 ∧ S 1`. -/
theorem not_egli_negative [Nonempty D] :
    extension .false (exists_ .destructive 1 (conj (atom (Set.univ : Set D) 1) (atom ∅ 1))) ⊥ ≠
      extension .false (conj (exists_ .destructive 1 (atom Set.univ 1)) (atom ∅ 1)) ⊥ := by
  obtain ⟨x⟩ := ‹Nonempty D›
  intro h
  have hl : (⊥ : ℕ → Part D) ∈ extension .false
      (exists_ .destructive 1 (conj (atom (Set.univ : Set D) 1) (atom ∅ 1))) ⊥ := by
    rw [exists_, extension_false_positiveClosure]
    refine ⟨⟨Set.eq_empty_iff_forall_notMem.2 fun i hi ↦ ?_,
      ⟨Function.update (⊥ : ℕ → Part D) 1 (Part.some x), ?_⟩⟩, rfl⟩
    · rw [mem_extension, mem_dplExists] at hi
      rcases hi with ⟨-, y, hy⟩ | ⟨h, -⟩
      · rw [← mem_extension, mem_extension_true_conj] at hy
        obtain ⟨j, hj, hk⟩ := hy
        rw [mem_extension, mem_atom_update] at hj
        rw [hj.2, mem_extension, mem_atom_update] at hk
        simp at hk
      · exact h trivial
    · rw [mem_extension, mem_dplExists]
      refine .inl ⟨trivial, x, ?_⟩
      rw [← mem_extension, mem_extension_false_conj]
      refine .inr ⟨.true, Function.update (⊥ : ℕ → Part D) 1 (Part.some x),
        by rw [mem_atom_update]; simp, ?_⟩
      rw [mem_extension, mem_atom_update]; simp
  rw [h, mem_extension_false_conj] at hl
  rcases hl with ⟨j, hj, -⟩ | ⟨t, j, hj, hk⟩
  · rw [extension_false_exists_atom _ (Existential.fresh_destructive _ _)] at hj
    exact (Set.univ_nonempty.ne_empty hj.2)
  · rw [mem_extension, mem_atom] at hk
    have hj' := (Prod.mk.inj hk).2
    subst hj'
    rw [exists_, mem_positiveClosure] at hj
    rcases hj with ⟨-, hj⟩ | ⟨⟨hT, -⟩, -⟩ | ⟨⟨hT, -⟩, -⟩
    · rw [mem_dplExists] at hj
      rcases hj with ⟨-, y, hy⟩ | ⟨h, -⟩
      · rw [mem_atom_update] at hy
        exact absurd (congrFun hy.2 1) (by simp)
      · exact h trivial
    all_goals
      rw [extension_true_dplExists_atom _ (Existential.fresh_destructive _ _)] at hT
      exact Set.eq_empty_iff_forall_notMem.1 hT (Function.update (⊥ : ℕ → Part D) 1 (Part.some x))
        ⟨x, trivial, rfl⟩


/-! ### Outputs value what their inputs value -/

/-- An assignment's relation to the assignments that value every variable it values. -/
def domainLE : SetRel (ℕ → Part D) (ℕ → Part D) :=
  {p | PFun.Dom p.1 ⊆ PFun.Dom p.2}

instance : (domainLE (D := D)).IsRefl := ⟨fun g ↦ show PFun.Dom g ⊆ PFun.Dom g from subset_rfl⟩

instance : (domainLE (D := D)).IsTrans := ⟨fun _ _ _ h₁ h₂ ↦ Set.Subset.trans (α := ℕ) h₁ h₂⟩

/-- Every output of `m` values the variables its input values. -/
def Expanding (m : StateSet D Trivalent) : Prop := ∀ t, StateT.rel m t ⊆ domainLE

theorem Expanding.domain_subset {m : StateSet D Trivalent} (hm : Expanding m)
    {g h : ℕ → Part D} {t : Trivalent} (hh : (t, h) ∈ m g) : PFun.Dom g ⊆ PFun.Dom h :=
  hm t (show (g, h) ∈ StateT.rel m t from hh)

theorem expanding_atom (P : Set D) (n : ℕ) : Expanding (atom P n) := by
  rintro t ⟨g, h⟩ (hm : (t, h) ∈ atom P n g)
  change PFun.Dom g ⊆ PFun.Dom h
  rw [(Prod.mk.inj (mem_atom.1 hm)).2]

theorem expanding_atomConst (P : Set D) (c : D) : Expanding (atomConst P c) := by
  rintro t ⟨g, h⟩ (hm : (t, h) ∈ atomConst P c g)
  change PFun.Dom g ⊆ PFun.Dom h
  rw [(Prod.mk.inj (mem_atomConst.1 hm)).2]

theorem Expanding.map {f : Trivalent → Trivalent} {m : StateSet D Trivalent} (hm : Expanding m) :
    Expanding (f <$> m) :=
  StateT.rel_map_subset hm f

theorem Expanding.map_seq {R : Trivalent → Trivalent → Trivalent} {m n : StateSet D Trivalent}
    (hm : Expanding m) (hn : Expanding n) : Expanding (R <$> m <*> n) :=
  StateT.rel_map_seq_subset hm hn R

theorem Expanding.neg {m : StateSet D Trivalent} (hm : Expanding m) : Expanding (neg m) := hm.map

theorem Expanding.conj {m n : StateSet D Trivalent} (hm : Expanding m) (hn : Expanding n) :
    Expanding (conj m n) := hm.map_seq hn

theorem Expanding.disj {m n : StateSet D Trivalent} (hm : Expanding m) (hn : Expanding n) :
    Expanding (disj m n) := hm.map_seq hn

theorem Expanding.imp {m n : StateSet D Trivalent} (hm : Expanding m) (hn : Expanding n) :
    Expanding (imp m n) := hm.map_seq hn

theorem Expanding.dplExists {e : Existential} {n : ℕ} {m : StateSet D Trivalent}
    (hm : Expanding m) : Expanding (dplExists e n m) := by
  rintro t ⟨g, h⟩ (hh : (t, h) ∈ Elliott2020.dplExists e n m g)
  change PFun.Dom g ⊆ PFun.Dom h
  rcases mem_dplExists.1 hh with ⟨-, x, hx⟩ | ⟨-, hx⟩
  · refine fun y hy ↦ hm.domain_subset hx ?_
    by_cases hyn : y = n
    · subst hyn
      exact Part.dom_iff_mem.mpr ⟨x, mem_update_self g y x⟩
    · show (Function.update g n (Part.some x) y).Dom
      rw [Function.update_of_ne hyn]
      exact hy
  · rw [(Prod.mk.inj hx).2]

theorem Expanding.positiveClosure {m : StateSet D Trivalent} (hm : Expanding m) :
    Expanding (positiveClosure m) := by
  rintro t ⟨g, h⟩ (hh : (t, h) ∈ Elliott2020.positiveClosure m g)
  change PFun.Dom g ⊆ PFun.Dom h
  rcases mem_positiveClosure.1 hh with ⟨-, hh⟩ | ⟨-, hh⟩ | ⟨-, hh⟩
  · exact hm.domain_subset hh
  all_goals rw [(Prod.mk.inj hh).2]

theorem Expanding.exists_ {e : Existential} {n : ℕ} {m : StateSet D Trivalent} (hm : Expanding m) :
    Expanding (exists_ e n m) := hm.dplExists.positiveClosure

theorem dom_of_mem_extension_true_exists {e : Existential} {n : ℕ} {m : StateSet D Trivalent}
    (hm : Expanding m) {g h : ℕ → Part D} (hh : h ∈ extension .true (exists_ e n m) g) :
    (h n).Dom := by
  rw [exists_, extension_true_positiveClosure, mem_extension, mem_dplExists] at hh
  rcases hh with ⟨-, x, hx⟩ | ⟨-, hx⟩
  · exact hm.domain_subset hx (Part.dom_iff_mem.mpr ⟨x, mem_update_self g n x⟩)
  · exact absurd (Prod.mk.inj hx).1 (by decide)

/-! ### The guarded existential and the dynamic Hurford constraint -/

-- fn. 26, (61)
theorem extension_true_conj_exists_guarded (L P : Set D) (g : ℕ → Part D) :
    extension .true (conj (exists_ .guarded 1 (atom L 1)) (exists_ .guarded 1 (atom P 1))) g =
      ∅ := by
  ext i
  simp only [Set.mem_empty_iff_false, iff_false]
  rw [mem_extension_true_conj]
  rintro ⟨h, hh, hi⟩
  rw [mem_extension, exists_guarded_of_ne_bot fun hb ↦ Part.eq_bot_iff_not_dom.1 hb
    (dom_of_mem_extension_true_exists (expanding_atom L 1) hh)] at hi
  simp at hi

/-- The dynamic Hurford constraint (70), read as validity, marks a disjunction of `φ` and `ψ` odd
when, in every model and at every input, `¬φ ∧ ψ` has no positive output, or `φ ∧ ¬ψ` has
none. -/
def HurfordOdd {M : Type*} (φ ψ : M → StateSet D Trivalent) : Prop :=
  (∀ x g, extension .true (conj (neg (φ x)) (ψ x)) g = ∅) ∨
    ∀ x g, extension .true (conj (φ x) (neg (ψ x))) g = ∅

theorem eq_and_isFalse_of_mem_extension_true_neg_exists {e : Existential} {n : ℕ}
    {m : StateSet D Trivalent} {g h : ℕ → Part D}
    (hh : h ∈ extension .true (neg (exists_ e n m)) g) :
    h = g ∧ IsFalse (dplExists e n m) g := by
  rw [extension_neg, Trivalent.compl_true, exists_, extension_false_positiveClosure] at hh
  exact ⟨hh.2, hh.1⟩

theorem fresh_of_isFalse_dplExists {e : Existential} {n : ℕ} {m : StateSet D Trivalent}
    {g : ℕ → Part D} (h : IsFalse (dplExists e n m) g) : e.Fresh g n := by
  by_contra hf
  obtain ⟨-, j, hj⟩ := h
  rw [mem_extension, mem_dplExists] at hj
  rcases hj with ⟨hf', -⟩ | ⟨-, hj⟩
  · exact hf hf'
  · exact absurd (Prod.mk.inj hj).1 (by decide)

-- (70), (65)
theorem hurfordOdd_someone_or_they :
    HurfordOdd (fun M : Set D × Set D ↦ exists_ .guarded 1 (atom M.1 1)) (fun M ↦ atom M.2 1) := by
  refine .inl fun M g ↦ ?_
  ext i
  simp only [Set.mem_empty_iff_false, iff_false]
  rw [mem_extension_true_conj]
  rintro ⟨h, hh, hi⟩
  obtain ⟨rfl, hF⟩ := eq_and_isFalse_of_mem_extension_true_neg_exists hh
  have hg : h 1 = ⊥ := fresh_of_isFalse_dplExists hF
  rw [mem_extension, mem_atom, valueAt_of_eq_bot _ hg] at hi
  simp at hi

-- (70)
theorem hurfordOdd_bathroom :
    HurfordOdd (fun M : Set D × Set D ↦ neg (exists_ .guarded 1 (atom M.1 1)))
      (fun M ↦ atom M.2 1) := by
  refine .inr fun M g ↦ ?_
  ext i
  simp only [Set.mem_empty_iff_false, iff_false]
  rw [mem_extension_true_conj]
  rintro ⟨h, hh, hi⟩
  obtain ⟨rfl, hF⟩ := eq_and_isFalse_of_mem_extension_true_neg_exists hh
  have hg : h 1 = ⊥ := fresh_of_isFalse_dplExists hF
  rw [extension_neg, mem_extension, mem_atom, valueAt_of_eq_bot _ hg] at hi
  simp at hi

-- (70), (65)
theorem not_hurfordOdd_someone_or_they_destructive :
    ¬ HurfordOdd (fun M : Set Bool × Set Bool ↦ exists_ .destructive 1 (atom M.1 1))
      (fun M ↦ atom M.2 1) := by
  rintro (h | h)
  · have := h (∅, Set.univ) (Function.update (⊥ : ℕ → Part Bool) 1 (Part.some true))
    refine (Set.eq_empty_iff_forall_notMem.1 this
      (Function.update (⊥ : ℕ → Part Bool) 1 (Part.some true))) ?_
    rw [mem_extension_true_conj]
    dsimp only
    refine ⟨Function.update (⊥ : ℕ → Part Bool) 1 (Part.some true), ?_, ?_⟩
    · rw [extension_true_neg_exists_atom _ (Existential.fresh_destructive _ _)]; exact ⟨rfl, rfl⟩
    · rw [mem_extension, mem_atom, valueAt_of_mem _ (mem_update_self ⊥ 1 true)]
      simp
  · have := h (Set.univ, ∅) ⊥
    refine (Set.eq_empty_iff_forall_notMem.1 this
      (Function.update (⊥ : ℕ → Part Bool) 1 (Part.some true))) ?_
    rw [mem_extension_true_conj]
    dsimp only
    refine ⟨Function.update (⊥ : ℕ → Part Bool) 1 (Part.some true), ?_, ?_⟩
    · rw [extension_true_exists_atom _ (Existential.fresh_destructive _ _)]
      exact ⟨true, trivial, rfl⟩
    · rw [extension_neg, mem_extension, mem_atom,
        valueAt_of_mem _ (mem_update_self ⊥ 1 true)]
      simp

-- (70)
theorem not_hurfordOdd_bathroom_destructive :
    ¬ HurfordOdd (fun M : Set Bool × Set Bool ↦ neg (exists_ .destructive 1 (atom M.1 1)))
      (fun M ↦ atom M.2 1) := by
  rintro (h | h)
  · have := h (Set.univ, Set.univ) ⊥
    refine (Set.eq_empty_iff_forall_notMem.1 this
      (Function.update (⊥ : ℕ → Part Bool) 1 (Part.some true))) ?_
    rw [mem_extension_true_conj, neg_neg]
    dsimp only
    refine ⟨Function.update (⊥ : ℕ → Part Bool) 1 (Part.some true), ?_, ?_⟩
    · rw [extension_true_exists_atom _ (Existential.fresh_destructive _ _)]
      exact ⟨true, trivial, rfl⟩
    · rw [mem_extension, mem_atom, valueAt_of_mem _ (mem_update_self ⊥ 1 true)]
      simp
  · have := h (∅, ∅) (Function.update (⊥ : ℕ → Part Bool) 1 (Part.some true))
    refine (Set.eq_empty_iff_forall_notMem.1 this
      (Function.update (⊥ : ℕ → Part Bool) 1 (Part.some true))) ?_
    rw [mem_extension_true_conj]
    dsimp only
    refine ⟨Function.update (⊥ : ℕ → Part Bool) 1 (Part.some true), ?_, ?_⟩
    · rw [extension_true_neg_exists_atom _ (Existential.fresh_destructive _ _)]; exact ⟨rfl, rfl⟩
    · rw [extension_neg, mem_extension, mem_atom,
        valueAt_of_mem _ (mem_update_self ⊥ 1 true)]
      simp

-- (70), (68)
theorem hurfordOdd_someone_or_someone_sitting [Nonempty D] (e : Existential) :
    HurfordOdd (fun M : Set D × Set D ↦ exists_ e 1 (atom M.1 1))
      (fun M ↦ exists_ e 2 (conj (atom M.1 2) (atom M.2 2))) := by
  refine .inl fun M g ↦ ?_
  ext i
  simp only [Set.mem_empty_iff_false, iff_false]
  rw [mem_extension_true_conj]
  rintro ⟨h, hh, hi⟩
  obtain ⟨rfl, hF⟩ := eq_and_isFalse_of_mem_extension_true_neg_exists hh
  have hA : M.1 = ∅ := (isFalse_dplExists_atom_iff M.1 (fresh_of_isFalse_dplExists hF)).1 hF
  rw [exists_, extension_true_positiveClosure, mem_extension, mem_dplExists] at hi
  rcases hi with ⟨-, x, hx⟩ | ⟨-, hx⟩
  · rw [← mem_extension, mem_extension_true_conj] at hx
    obtain ⟨j, hj, -⟩ := hx
    rw [mem_extension, mem_atom, valueAt_of_mem _ (mem_update_self h 2 x)] at hj
    simp [hA] at hj
  · exact absurd (Prod.mk.inj hx).1 (by decide)


/-! ### Information states and update

Information states are the substrate's `State W ℕ D`, sets of world–assignment points
(Def. 3.1); the initial state `⊤` pairs every world with the empty assignment. -/

variable {W : Type}

/-- Stalnaker's bridge requires a sentence to be true or false at every point of the state
(Def. 3.2). -/
def Defined (c : State W ℕ D) (φ : W → StateSet D Trivalent) : Prop :=
  ∀ p ∈ c, IsTrue (φ p.world) p.assignment ∨ IsFalse (φ p.world) p.assignment

/-- Update gathers the positive outputs at every point when the bridge holds, and is absurd
otherwise (Def. 3.2). -/
def update (c : State W ℕ D) (φ : W → StateSet D Trivalent) : State W ℕ D :=
  {p | Defined c φ ∧ ∃ q ∈ c, q.world = p.world ∧
    p.assignment ∈ extension .true (φ q.world) q.assignment}

theorem Existential.fresh_of_eq_bot {e : Existential} {g : ℕ → Part D} {n : ℕ}
    (h : g n = ⊥) : e.Fresh g n := by
  cases e
  · trivial
  · exact h

-- §3.5
theorem familiar_update_exists (e : Existential) (n : ℕ) (c : State W ℕ D)
    (φ : W → StateSet D Trivalent) (hφ : ∀ w, Expanding (φ w)) :
    State.Familiar (update c fun w ↦ exists_ e n (φ w)) n := by
  rintro ⟨w, h⟩ ⟨-, ⟨w', g⟩, -, rfl, hh⟩
  exact dom_of_mem_extension_true_exists (hφ _) hh

-- §3.5
theorem familiar_update {c : State W ℕ D} {n : ℕ} (h : State.Familiar c n)
    {φ : W → StateSet D Trivalent} (hφ : ∀ w, Expanding (φ w)) :
    State.Familiar (update c φ) n := by
  rintro ⟨w, i⟩ ⟨-, ⟨w', g⟩, hq, rfl, hi⟩
  exact (hφ w').domain_subset hi (h _ hq)

-- (11a)
theorem not_defined_initial_atom [Nonempty W] (P : W → Set D) :
    ¬ Defined (⊤ : State W ℕ D) fun w ↦ atom (P w) 1 := by
  obtain ⟨w⟩ := ‹Nonempty W›
  intro h
  rcases h ⟨w, ⊥⟩ (State.mem_top.2 fun _ ↦ rfl) with ⟨i, hi⟩ | ⟨-, i, hi⟩ <;>
    · rw [mem_extension, mem_atom, valueAt_of_eq_bot _ rfl] at hi
      simp at hi

section Bridge

open Classical

theorem conj_atom_atom (L H : Set D) (n : ℕ) : conj (atom L n) (atom H n) = atom (L ∩ H) n := by
  funext g
  have key : valueAt L g n ⊓ valueAt H g n = valueAt (L ∩ H) g n := by
    rcases (g n).eq_none_or_eq_some with hg | ⟨d, hg⟩
    · simp [valueAt_of_eq_bot _ hg]
    · simp only [valueAt_of_mem _ (Part.eq_some_iff.1 hg), Set.mem_inter_iff]
      by_cases hL : d ∈ L <;> by_cases hH : d ∈ H <;> simp [hL, hH]
  ext ⟨v, i⟩
  simp only [conj, Set.mk_mem_stateT_map_seq, mem_atom, Prod.mk.injEq]
  constructor
  · rintro ⟨t, h, ⟨rfl, rfl⟩, u, ⟨rfl, rfl⟩, rfl⟩
    exact ⟨key, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨_, _, ⟨rfl, rfl⟩, _, ⟨rfl, rfl⟩, key.symm⟩

theorem nonempty_exists_atom [Nonempty D] (e : Existential) (W : Set D) (n : ℕ)
    (g : ℕ → Part D) : (exists_ e n (atom W n) g).Nonempty := by
  by_cases hf : e.Fresh g n
  · rcases Set.eq_empty_or_nonempty W with hW | ⟨x, hx⟩
    · refine ⟨(.false, g), ?_⟩
      show g ∈ extension .false (exists_ e n (atom W n)) g
      rw [extension_false_exists_atom W hf]; exact ⟨rfl, hW⟩
    · refine ⟨(.true, Function.update g n (Part.some x)), ?_⟩
      show Function.update g n (Part.some x) ∈ extension .true (exists_ e n (atom W n)) g
      rw [extension_true_exists_atom W hf]; exact ⟨x, hx, rfl⟩
  · cases e
    · exact absurd trivial hf
    · rw [exists_guarded_of_ne_bot hf]; exact Set.singleton_nonempty _


variable {e : Existential} {g : ℕ → Part D}

theorem mem_atomConst_iff {P : Set D} {c : D} {v : Trivalent} {h : ℕ → Part D} :
    (v, h) ∈ atomConst P c g ↔ v = ofProp (c ∈ P) ∧ h = g := by
  rw [mem_atomConst, Prod.mk.injEq]

theorem isTrue_or_isFalse_neg_exists_atom [Nonempty D] (W : Set D) {n : ℕ} (hf : e.Fresh g n) :
    IsTrue (neg (exists_ e n (atom W n))) g ∨ IsFalse (neg (exists_ e n (atom W n))) g := by
  rcases Set.eq_empty_or_nonempty W with hW | ⟨x, hx⟩
  · exact .inl ⟨g, by rw [extension_true_neg_exists_atom W hf]; exact ⟨rfl, hW⟩⟩
  · refine .inr ⟨?_, Function.update g n (Part.some x),
      by rw [extension_false_neg_exists_atom W hf]; exact ⟨x, hx, rfl⟩⟩
    rw [extension_true_neg_exists_atom W hf]
    exact Set.eq_empty_iff_forall_notMem.2 fun h hh ↦ (Set.nonempty_of_mem hx).ne_empty hh.2

theorem isTrue_or_isFalse_conj_exists_atom [Nonempty D] (P Q : Set D) (hf : e.Fresh g 1) :
    IsTrue (conj (exists_ e 1 (atom P 1)) (atom Q 1)) g ∨
      IsFalse (conj (exists_ e 1 (atom P 1)) (atom Q 1)) g := by
  rw [isTrue_or_isFalse_iff, extension_true_conj_exists_atom P Q hf,
    extension_false_conj_exists_atom P Q hf]
  rcases P.eq_empty_or_nonempty with hP | ⟨x, hx⟩
  · exact .inr ⟨g, .inl ⟨rfl, hP⟩⟩
  · by_cases hQ : x ∈ Q
    exacts [.inl ⟨_, x, hx, hQ, rfl⟩, .inr ⟨_, .inr ⟨x, hx, hQ, rfl⟩⟩]

-- (10a)
theorem defined_initial_someone_and_they [Nonempty D] (P Q : W → Set D) :
    Defined (⊤ : State W ℕ D) fun w ↦ conj (exists_ e 1 (atom (P w) 1)) (atom (Q w) 1) :=
  fun _ hp ↦ isTrue_or_isFalse_conj_exists_atom _ _
    (Existential.fresh_of_eq_bot (State.mem_top.1 hp 1))

theorem isTrue_or_isFalse_bathroom [Nonempty D] (B U : Set D) (hf : e.Fresh g 1) :
    IsTrue (disj (neg (exists_ e 1 (atom B 1))) (atom U 1)) g ∨
      IsFalse (disj (neg (exists_ e 1 (atom B 1))) (atom U 1)) g := by
  rw [isTrue_or_isFalse_iff, extension_true_bathroom B U hf, extension_false_bathroom B U hf]
  rcases B.eq_empty_or_nonempty with hB | ⟨x, hx⟩
  · exact .inl ⟨g, .inl ⟨rfl, hB⟩⟩
  · by_cases hU : x ∈ U
    exacts [.inl ⟨_, .inr ⟨x, hx, hU, rfl⟩⟩, .inr ⟨_, x, hx, hU, rfl⟩]

-- (33)
theorem defined_initial_bathroom [Nonempty D] (B U : W → Set D) :
    Defined (⊤ : State W ℕ D) fun w ↦ disj (neg (exists_ e 1 (atom (B w) 1))) (atom (U w) 1) :=
  fun _ hp ↦ isTrue_or_isFalse_bathroom _ _ (Existential.fresh_of_eq_bot (State.mem_top.1 hp 1))

-- (4), (5)
theorem not_familiar_update_neg_exists [Nonempty D] (P : W → Set D) {w : W} (hw : P w = ∅) :
    ¬ State.Familiar (update (⊤ : State W ℕ D) fun w ↦ neg (exists_ e 1 (atom (P w) 1))) 1 := by
  intro hfam
  refine absurd (hfam ⟨w, ⊥⟩ ⟨fun p hp ↦ ?_, ⟨w, ⊥⟩, State.mem_top.2 fun _ ↦ rfl, rfl, ?_⟩)
    (by simp [Part.bot_eq_none, Part.not_none_dom])
  · exact isTrue_or_isFalse_neg_exists_atom _ (Existential.fresh_of_eq_bot (State.mem_top.1 hp 1))
  · show ⊥ ∈ extension .true (neg (exists_ e 1 (atom (P w) 1))) ⊥
    rw [extension_true_neg_exists_atom _ (Existential.fresh_of_eq_bot rfl)]; exact ⟨rfl, hw⟩

theorem isTrue_or_isFalse_disj_exists_atomConst [Nonempty D] (A P : Set D) (c : D)
    (hf : e.Fresh g 1) :
    IsTrue (disj (exists_ e 1 (atom A 1)) (atomConst P c)) g ∨
      IsFalse (disj (exists_ e 1 (atom A 1)) (atomConst P c)) g := by
  rcases Set.eq_empty_or_nonempty A with hA | ⟨x, hx⟩
  · by_cases hc : c ∈ P
    · refine .inl ⟨g, mem_extension_true_disj.2 (.inr ⟨.false, g, ?_, ?_⟩)⟩
      · show g ∈ extension .false (exists_ e 1 (atom A 1)) g
        rw [extension_false_exists_atom A hf]; exact ⟨rfl, hA⟩
      · rw [mem_extension, mem_atomConst_iff]; simp [hc]
    · refine .inr ⟨Set.eq_empty_iff_forall_notMem.2 fun i hi ↦ ?_, g, ?_⟩
      · rcases mem_extension_true_disj.1 hi with ⟨h, hh, -⟩ | ⟨t, h, -, hi⟩
        · rw [extension_true_exists_atom A hf] at hh
          obtain ⟨x, hx, -⟩ := hh
          simp [hA] at hx
        · rw [mem_extension, mem_atomConst_iff] at hi
          simp [hc] at hi
      · refine mem_extension_false_disj.2 ⟨g, ?_, ?_⟩
        · rw [extension_false_exists_atom A hf]; exact ⟨rfl, hA⟩
        · rw [mem_extension, mem_atomConst_iff]; simp [hc]
  · refine .inl ⟨Function.update g 1 (Part.some x),
      mem_extension_true_disj.2 (.inl ⟨Function.update g 1 (Part.some x), ?_, ofProp (c ∈ P), ?_⟩)⟩
    · rw [extension_true_exists_atom A hf]; exact ⟨x, hx, rfl⟩
    · exact mem_atomConst_iff.2 ⟨rfl, rfl⟩

/-- After *either someone₁ was in the audience, or the event was a disaster*, 1 need not be familiar
((54), (55)). -/
theorem not_familiar_update_disj [Nonempty D] (A Dis : W → Set D) (ev : D) {w : W}
    (hA : A w = ∅) (hDis : ev ∈ Dis w) :
    ¬ State.Familiar (update (⊤ : State W ℕ D)
      fun w ↦ disj (exists_ e 1 (atom (A w) 1)) (atomConst (Dis w) ev)) 1 := by
  intro hfam
  refine absurd (hfam ⟨w, ⊥⟩ ⟨fun p hp ↦ ?_, ⟨w, ⊥⟩, State.mem_top.2 fun _ ↦ rfl, rfl, ?_⟩)
    (by simp [Part.bot_eq_none, Part.not_none_dom])
  · exact isTrue_or_isFalse_disj_exists_atomConst _ _ _
      (Existential.fresh_of_eq_bot (State.mem_top.1 hp 1))
  · refine mem_extension_true_disj.2 (.inr ⟨.false, ⊥, ?_, ?_⟩)
    · show ⊥ ∈ extension .false (exists_ e 1 (atom (A w) 1)) ⊥
      rw [extension_false_exists_atom _ (Existential.fresh_of_eq_bot rfl)]; exact ⟨rfl, hA⟩
    · rw [mem_extension, mem_atomConst_iff]; simp [hDis]

/-- After the disjunction and *the event wasn't a disaster*, 1 is familiar ((48), (56)). -/
theorem familiar_update_update_disj (A Dis : W → Set D) (ev : D) :
    State.Familiar (update (update (⊤ : State W ℕ D)
      fun w ↦ disj (exists_ e 1 (atom (A w) 1)) (atomConst (Dis w) ev))
      fun w ↦ neg (atomConst (Dis w) ev)) 1 := by
  rintro ⟨w, i⟩ ⟨-, ⟨w', h⟩, ⟨-, ⟨w'', g⟩, -, hw, hh⟩, rfl, hi⟩
  dsimp only at hw hh hi
  subst hw
  rw [extension_neg, mem_extension, mem_atomConst_iff] at hi
  obtain ⟨hev, rfl⟩ := hi
  rcases mem_extension_true_disj.1 hh with ⟨j, hj, u, hu⟩ | ⟨t, j, -, hj⟩
  · obtain ⟨-, rfl⟩ := mem_atomConst_iff.1 hu
    exact dom_of_mem_extension_true_exists (expanding_atom _ 1) hj
  · rw [mem_extension, mem_atomConst_iff] at hj
    exact absurd (hev.trans hj.1.symm) (by decide)

theorem mem_update_update_disj [Nonempty D] (A Dis : W → Set D) (ev : D) {w : W} {x : D}
    (hx : x ∈ A w) (hev : ev ∉ Dis w) :
    (⟨w, Function.update (⊥ : ℕ → Part D) 1 (Part.some x)⟩ : Possibility W ℕ (Part D)) ∈
      update (update (⊤ : State W ℕ D)
      fun w ↦ disj (exists_ e 1 (atom (A w) 1)) (atomConst (Dis w) ev))
      fun w ↦ neg (atomConst (Dis w) ev) := by
  have hdef : Defined (⊤ : State W ℕ D)
      fun w ↦ disj (exists_ e 1 (atom (A w) 1)) (atomConst (Dis w) ev) := fun p hp ↦
    isTrue_or_isFalse_disj_exists_atomConst _ _ _
      (Existential.fresh_of_eq_bot (State.mem_top.1 hp 1))
  refine ⟨fun p _ ↦ ?_, ⟨w, Function.update (⊥ : ℕ → Part D) 1 (Part.some x)⟩,
    ⟨hdef, ⟨w, ⊥⟩, State.mem_top.2 fun _ ↦ rfl, rfl, ?_⟩, rfl, ?_⟩
  · by_cases hc : ev ∈ Dis p.world
    · exact .inr ⟨Set.eq_empty_iff_forall_notMem.2 fun i hi ↦ by
        rw [extension_neg, mem_extension, mem_atomConst_iff] at hi
        simp [hc] at hi, p.assignment, by
        rw [extension_neg, Trivalent.compl_false, mem_extension, mem_atomConst_iff]; simp [hc]⟩
    · exact .inl ⟨p.assignment, by
        rw [extension_neg, mem_extension, mem_atomConst_iff]; simp [hc]⟩
  · refine mem_extension_true_disj.2 (.inl ⟨_, ?_, _, mem_atomConst_iff.2 ⟨rfl, rfl⟩⟩)
    rw [extension_true_exists_atom _ (Existential.fresh_of_eq_bot rfl)]; exact ⟨x, hx, rfl⟩
  · rw [extension_neg, mem_extension, mem_atomConst_iff]; simp [hev]

/-- After a Stone disjunction such as *either a linguist is here, or a philosopher is* with one
index, 1 is familiar ((58)–(64)). -/
theorem familiar_update_stone (L P H : W → Set D) :
    State.Familiar (update (⊤ : State W ℕ D) fun w ↦
      disj (exists_ e 1 (conj (atom (L w) 1) (atom (H w) 1)))
        (exists_ e 1 (conj (atom (P w) 1) (atom (H w) 1)))) 1 := by
  rintro ⟨w, i⟩ ⟨-, ⟨w', g⟩, -, rfl, hi⟩
  have hexp := fun (Q : Set D) ↦ (expanding_atom Q 1).conj (expanding_atom (H w') 1)
  rcases mem_extension_true_disj.1 hi with ⟨h, hh, u, hu⟩ | ⟨t, h, -, hi⟩
  · exact (hexp (P w')).exists_.domain_subset hu (dom_of_mem_extension_true_exists (hexp _) hh)
  · exact dom_of_mem_extension_true_exists (hexp _) hi


theorem snd_eq_of_mem_exists_atom {W : Set D} {n : ℕ} (hW : W = ∅) (hf : e.Fresh g n)
    {p : Trivalent × (ℕ → Part D)} (hp : p ∈ exists_ e n (atom W n) g) : p.2 = g := by
  rw [exists_, mem_positiveClosure] at hp
  rcases hp with ⟨h1, hp⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩
  · obtain ⟨t, h⟩ := p
    dsimp only at h1
    subst h1
    have : h ∈ extension .true (dplExists e n (atom W n)) g := hp
    rw [extension_true_dplExists_atom W hf] at this
    obtain ⟨x, hx, -⟩ := this
    simp [hW] at hx
  all_goals rfl

theorem isTrue_or_isFalse_disj_exists_atom [Nonempty D] (A B : Set D) (hg : g 1 = ⊥) :
    IsTrue (disj (exists_ e 1 (atom A 1)) (exists_ e 1 (atom B 1))) g ∨
      IsFalse (disj (exists_ e 1 (atom A 1)) (exists_ e 1 (atom B 1))) g := by
  have hf : ∀ {e : Existential}, e.Fresh g 1 := Existential.fresh_of_eq_bot hg
  rcases Set.eq_empty_or_nonempty A with hA | ⟨x, hx⟩
  · rcases Set.eq_empty_or_nonempty B with hB | ⟨y, hy⟩
    · refine .inr ⟨Set.eq_empty_iff_forall_notMem.2 fun i hi ↦ ?_, g, ?_⟩
      · rcases mem_extension_true_disj.1 hi with ⟨h, hh, -⟩ | ⟨t, h, hh, hi'⟩
        · rw [extension_true_exists_atom A hf] at hh
          obtain ⟨x, hx, -⟩ := hh
          simp [hA] at hx
        · have hhg : h = g := snd_eq_of_mem_exists_atom hA hf hh
          subst hhg
          rw [extension_true_exists_atom B hf] at hi'
          obtain ⟨y, hy, -⟩ := hi'
          simp [hB] at hy
      · refine mem_extension_false_disj.2 ⟨g, ?_, ?_⟩
        · rw [extension_false_exists_atom A hf]; exact ⟨rfl, hA⟩
        · rw [extension_false_exists_atom B hf]; exact ⟨rfl, hB⟩
    · refine .inl ⟨Function.update g 1 (Part.some y),
        mem_extension_true_disj.2 (.inr ⟨.false, g, ?_, ?_⟩)⟩
      · show g ∈ extension .false (exists_ e 1 (atom A 1)) g
        rw [extension_false_exists_atom A hf]; exact ⟨rfl, hA⟩
      · rw [extension_true_exists_atom B hf]; exact ⟨y, hy, rfl⟩
  · obtain ⟨⟨u, i⟩, hu⟩ := nonempty_exists_atom e B 1 (Function.update g 1 (Part.some x))
    refine .inl ⟨i,
      mem_extension_true_disj.2 (.inl ⟨Function.update g 1 (Part.some x), ?_, u, hu⟩)⟩
    rw [extension_true_exists_atom A hf]; exact ⟨x, hx, rfl⟩

theorem exists_mem_update_stone [Nonempty D] (L P H : W → Set D) {w : W} {x : D}
    (hx : x ∈ L w ∩ H w) :
    ∃ i, (⟨w, i⟩ : Possibility W ℕ (Part D)) ∈ update (⊤ : State W ℕ D) fun w ↦
      disj (exists_ e 1 (conj (atom (L w) 1) (atom (H w) 1)))
        (exists_ e 1 (conj (atom (P w) 1) (atom (H w) 1))) := by
  simp only [conj_atom_atom]
  obtain ⟨⟨u, i⟩, hu⟩ :=
    nonempty_exists_atom e (P w ∩ H w) 1 (Function.update (⊥ : ℕ → Part D) 1 (Part.some x))
  refine ⟨i, fun p hp ↦ isTrue_or_isFalse_disj_exists_atom _ _ (State.mem_top.1 hp 1), ⟨w, ⊥⟩,
    State.mem_top.2 fun _ ↦ rfl, rfl, mem_extension_true_disj.2 (.inl ⟨_, ?_, u, hu⟩)⟩
  rw [extension_true_exists_atom _ (Existential.fresh_of_eq_bot rfl)]; exact ⟨x, hx, rfl⟩

end Bridge

end Elliott2020
