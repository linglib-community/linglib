module

public import Linglib.Core.Data.Fintype.Flat
public import Linglib.Data.Examples.Elliott2025
public import Linglib.Semantics.Mereology
public import Linglib.Semantics.Quantification.Lattice
public import Linglib.Semantics.Quantification.Individual
public import Studies.GroenendijkStokhof1984
public import Studies.KeenanStavi1986
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Minimal

/-!
# Elliott (2025): Determiners as predicates

Elliott proposes that a determiner denotes a predicate of groups of polarized individuals rather
than a relation between sets. Every individual `x` has a positive version `x⁺` and a negative
version `x⁻`, no group contains both, and a noun denotes its maximal groups: its extension divided
in every possible way into positive and negative individuals. *Exactly two* holds of the groups
with two positive individuals, and a sentence says that some group of the noun satisfies the
determiner while the scope holds of its positive and fails of its negative individuals. A group
records which members of the restrictor are outside the scope, so these truth conditions are
those of generalized quantifier theory, and the determiners expressible this way are exactly the
conservative ones.

## Implementation notes

A group is a function into `Flat Bool`, the paper's trivalent presentation: `⊥` for an absent
individual and `↑true`, `↑false` for the two polarities. Parthood is the pointwise flat order, so
no group contains both versions of an individual. Nouns, like determiners, are predicates of
groups, and the paper's covert existential determiner is `Quantifier.Det.some` at groups. The
paper's domain has no empty group; `PolarGroup α` has one, `⊥`, with which predicates match the
conservative quantifiers exactly and *all N* and *no N* are singletons even for an empty noun.
Restricting to `X ≠ ⊥` recovers the paper's count and its correspondence up to the empty
restrictor. Nouns and scopes are sets of individuals, the classical theory's pluralities are
nonempty `Finset`s, and a collective predicate is a set containing no atom.

## TODO

* The paper says that the ∆-operator of a collective predicate is true of no group of a singular
  noun, but it is true of the wholly negative group (`delta_collective_iff`); *some boy gathered*
  is false all the same, since *some* requires a positive atom.
* The plural numerals of the last section, which count the atoms inside a positive atom.

## References

* [elliott-2025]
* [barwise-cooper-1981]
* [keenan-stavi-1986]
* [link-1983]
* [link-1987]
* [rothstein-2017]
* [van-benthem-1986]
* [bylinina-nouwen-2018]
* [schwarzschild-2002b]
* [groenendijk-stokhof-1984]
-/

@[expose] public section

namespace Elliott2025

open Quantifier Quantifier.Det

variable {α : Type*}

/-! ### The classical predicative theory -/

section Classical

/-- On the classical predicative theory a determiner `D` is a predicate of pluralities, here
nonempty finite sets, and a sentence says that some plurality satisfying `D` consists of
`N`-individuals that each satisfy the scope `vp`. -/
def classicalSentence (D : Finset α → Prop) (N vp : Set α) : Prop :=
  ∃ X : Finset α, X.Nonempty ∧ D X ∧ (∀ x ∈ X, x ∈ N) ∧ ∀ x ∈ X, x ∈ vp

variable {N vp : Set α}

/-- Van Benthem's problem is that every part of a plurality that satisfies the scope satisfies it
too, so *less than `n` `N` `vp`* says only that some `N` satisfies `vp`. -/
theorem classical_lessThan_iff_some {n : ℕ} (hn : 1 < n) :
    classicalSentence (·.card < n) N vp ↔ Quantifier.Det.some N vp := by
  refine ⟨fun ⟨X, ⟨x, hx⟩, _, hN, hvp⟩ ↦ ⟨x, hN x hx, hvp x hx⟩, fun ⟨x, hN, hvp⟩ ↦ ?_⟩
  exact ⟨{x}, Finset.singleton_nonempty x, by simpa, by simpa, by simpa⟩

/-- The problem of *zero* is that every plurality has an atom, so *zero* is never satisfied. -/
theorem classical_zero_false : ¬ classicalSentence (·.card = 0) N vp :=
  fun ⟨_, hX, hcard, _⟩ ↦ hX.card_pos.ne' hcard

end Classical

/-! ### Groups of polarized individuals -/

/-- A group of polarized individuals sends an individual `x` to `↑true` when `x⁺` is a part of
it, to `↑false` when `x⁻` is, and to `⊥` when neither is; parthood is the pointwise order. -/
abbrev PolarGroup (α : Type*) := α → Flat Bool

namespace PolarGroup

variable (X : PolarGroup α)

/-- The positive atoms of a group are the individuals it contains positively. -/
def posAtoms : Set α := {x | X x = ↑true}

/-- The negative atoms of a group are the individuals it contains negatively. -/
def negAtoms : Set α := {x | X x = ↑false}

/-- The atoms of a group are the individuals it contains with either polarity. -/
def atoms : Set α := {x | X x ≠ ⊥}

/-- The atomic parts of a group are polarized individuals, `(x, true)` for `x⁺` and
`(x, false)` for `x⁻`. -/
def parts : Set (α × Bool) := {p | X p.1 = ↑p.2}

/-- The ∆-operator predicates `f` of a group distributively, requiring that `f` hold of `x` for
each atomic part `x⁺` and fail of `x` for each atomic part `x⁻`. -/
def delta (f : Set α) : Prop := ∀ p ∈ X.parts, (p.1 ∈ f ↔ p.2)

variable {X}

theorem le_iff_parts_subset {Y : PolarGroup α} : X ≤ Y ↔ X.parts ⊆ Y.parts := by
  refine ⟨fun h p hp ↦ Flat.coe_le_iff.1 (hp ▸ h p.1), fun h x ↦ ?_⟩
  cases hx : X x with
  | bot => exact bot_le
  | coe b => exact (h (show (x, b) ∈ X.parts from hx)).ge

theorem posAtoms_subset_atoms : X.posAtoms ⊆ X.atoms := fun x (hx : X x = _) ↦ by
  simp [atoms, hx]

theorem atoms_inter_posAtoms : X.atoms ∩ X.posAtoms = X.posAtoms :=
  Set.inter_eq_right.2 posAtoms_subset_atoms

theorem atoms_diff_posAtoms : X.atoms \ X.posAtoms = X.negAtoms := by
  ext x
  simp only [atoms, posAtoms, negAtoms, Set.mem_sdiff, Set.mem_ofPred_eq]
  cases X x with
  | bot => simp
  | coe b => cases b <;> simp

@[simp] theorem atoms_eq_empty_iff : X.atoms = ∅ ↔ X = ⊥ := by
  simp [atoms, Set.eq_empty_iff_forall_notMem, funext_iff]

end PolarGroup

/-- A set of polarized individuals is coherent when it contains no individual with both
polarities. -/
def Coherent (A : Set (α × Bool)) : Prop := ∀ x, ¬ ((x, true) ∈ A ∧ (x, false) ∈ A)

open Classical in
/-- Groups ordered by parthood are the coherent sets of polarized individuals ordered by
inclusion, the empty group corresponding to the empty set. -/
noncomputable def partsOrderIso : PolarGroup α ≃o {A : Set (α × Bool) // Coherent A} where
  toFun X := ⟨X.parts, fun x ⟨h₁, h₂⟩ ↦ by simp_all [PolarGroup.parts]⟩
  invFun A x := if (x, true) ∈ A.1 then ↑true else if (x, false) ∈ A.1 then ↑false else ⊥
  left_inv X := by
    funext x
    cases hx : X x with
    | bot => simp [PolarGroup.parts, hx]
    | coe b => cases b <;> simp [PolarGroup.parts, hx]
  right_inv A := Subtype.ext <| Set.ext fun ⟨x, b⟩ ↦ by
    have := A.2 x
    by_cases h₁ : (x, true) ∈ A.1 <;> by_cases h₂ : (x, false) ∈ A.1 <;> cases b <;>
      simp_all [PolarGroup.parts]
  map_rel_iff' := PolarGroup.le_iff_parts_subset.symm

open PolarGroup

/-- `polarize N vp` is the group of the `N`-individuals, each positive if it satisfies `vp` and
negative otherwise. -/
noncomputable def polarize (N vp : Set α) : PolarGroup α :=
  open Classical in fun x ↦ if x ∈ N then ↑(decide (x ∈ vp)) else ⊥

section Polarize

variable {N vp vp' : Set α} {X : PolarGroup α}

@[simp] theorem atoms_polarize : (polarize N vp).atoms = N := by
  ext x; by_cases h : x ∈ N <;> simp [polarize, atoms, h]

@[simp] theorem posAtoms_polarize : (polarize N vp).posAtoms = N ∩ vp := by
  ext x; by_cases h : x ∈ N <;> simp [polarize, posAtoms, h]

@[simp] theorem negAtoms_polarize : (polarize N vp).negAtoms = N \ vp := by
  ext x; by_cases h : x ∈ N <;> simp [polarize, negAtoms, h]

theorem polarize_eq_polarize_iff :
    polarize N vp = polarize N vp' ↔ ∀ x ∈ N, (x ∈ vp ↔ x ∈ vp') := by
  simp only [funext_iff, polarize]
  refine forall_congr' fun x ↦ ?_
  by_cases h : x ∈ N <;> simp [h, Flat.coe_inj]

theorem polarize_ne_bot_iff : polarize N vp ≠ ⊥ ↔ N.Nonempty := by
  rw [Ne, ← atoms_eq_empty_iff, atoms_polarize, Set.nonempty_iff_ne_empty]

theorem polarize_atoms_posAtoms (X : PolarGroup α) : polarize X.atoms X.posAtoms = X := by
  funext x
  cases h : X x with
  | bot => simp [polarize, atoms, h]
  | coe b => cases b <;> simp [polarize, atoms, posAtoms, h]

theorem delta_polarize_iff : (polarize N vp).delta vp' ↔ ∀ x ∈ N, (x ∈ vp' ↔ x ∈ vp) := by
  simp only [delta, parts, polarize, Set.mem_ofPred_eq, Prod.forall]
  refine forall_congr' fun x ↦ ?_
  by_cases h : x ∈ N <;> by_cases hv : x ∈ vp <;> simp [h, hv, Flat.coe_inj]

/-- The ∆-operator for `f` holds exactly of the parts of the group that polarizes every
individual by `f`. -/
theorem delta_iff_le : X.delta vp ↔ X ≤ polarize ⊤ vp := by
  rw [le_iff_parts_subset]
  refine forall₂_congr fun ⟨x, b⟩ _ ↦ ?_
  cases b <;> by_cases hv : x ∈ vp <;> simp [parts, polarize, hv]

end Polarize

/-- A noun holds of the maximal groups whose atoms all fall under it. -/
def noun (N : Set α) : PolarGroup α → Prop :=
  Maximal fun X : PolarGroup α ↦ X.atoms ⊆ N

section Noun

variable {N vp : Set α} {X : PolarGroup α}

theorem noun_iff : noun N X ↔ X.atoms = N := by
  classical
  refine ⟨fun ⟨hP, hmax⟩ ↦ Set.Subset.antisymm hP fun x hN ↦ by_contra fun hb ↦ ?_, fun h ↦ ?_⟩
  · have hb : X x = ⊥ := not_not.1 hb
    have hle : X ≤ Function.update X x ↑true := fun y ↦ by
      rcases eq_or_ne y x with rfl | hy <;> simp [*]
    have := hmax (y := Function.update X x ↑true) (fun y hy ↦ by
      rcases eq_or_ne y x with rfl | hyx
      · exact hN
      · exact hP (show y ∈ X.atoms by simpa [atoms, hyx] using hy)) hle x
    simp [hb] at this
  · exact ⟨h.le, fun Y hY hle x ↦ (Flat.eq_of_le (hle x) fun hy ↦ h.ge (hY hy)).ge⟩

theorem noun_polarize (N vp : Set α) : noun N (polarize N vp) := by
  simp [noun_iff]

/-- The groups of a noun are its extension polarized by every possible scope, one for each
division of the extension into positive and negative atoms. -/
theorem setOf_noun : {X | noun N X} = Set.range (polarize N) := by
  ext X
  refine ⟨fun h ↦ ⟨X.posAtoms, ?_⟩, fun ⟨S, hS⟩ ↦ hS ▸ noun_polarize N S⟩
  rw [← noun_iff.1 h, polarize_atoms_posAtoms]

theorem noun_iff_exists : noun N X ↔ ∃ S, polarize N S = X :=
  Set.ext_iff.1 setOf_noun X

theorem delta_iff_eq_polarize (hX : noun N X) : X.delta vp ↔ X = polarize N vp := by
  obtain ⟨S, rfl⟩ := noun_iff_exists.1 hX
  rw [delta_polarize_iff, polarize_eq_polarize_iff]
  exact forall₂_congr fun _ _ ↦ Iff.comm

end Noun

/-! ### Determiners as predicates -/

/-- A determiner denotes a predicate of groups. -/
abbrev Det (α : Type*) := PolarGroup α → Prop

namespace Det

/-- A bare numeral has an at-least meaning, so *two* holds of groups with at least two positive
atoms. -/
def atLeast (n : ℕ) : Det α := fun X ↦ n ≤ X.posAtoms.ncard

/-- *Exactly `n`* holds of groups with `n` positive atoms; *zero* is `exactly 0`. -/
def exactly (n : ℕ) : Det α := fun X ↦ X.posAtoms.ncard = n

/-- *Less than `n`* holds of groups with fewer than `n` positive atoms. -/
def lessThan (n : ℕ) : Det α := fun X ↦ X.posAtoms.ncard < n

/-- *All* holds of groups without negative atoms. -/
def all : Det α := fun X ↦ X.negAtoms = ∅

/-- *Some* holds of groups with a positive atom. -/
protected def some : Det α := fun X ↦ X.posAtoms ≠ ∅

/-- *Not all* is the negation of *all*. -/
def notAll : Det α := allᶜ

/-- *None* is the negation of *some*. -/
protected def none : Det α := Det.someᶜ

/-- *Most* holds of groups with more positive than negative atoms. -/
def most : Det α := fun X ↦ X.negAtoms.ncard < X.posAtoms.ncard

/-- A determiner denotation yields a predicate by applying it to the atoms and the positive
atoms of a group. -/
def ofGQ (Q : Quantifier.Det α) : Det α := fun X ↦ Q X.atoms X.posAtoms

end Det

/-- In a simple distributive sentence the determiner modifies the noun intersectively, and the
covert existential determiner `Quantifier.Det.some` relates the resulting predicate to the
∆-operator applied to the scope. -/
def sentence (D : Det α) (N vp : Set α) : Prop :=
  Quantifier.Det.some (Set.ofPred (D ⊓ noun N)) {X | X.delta vp}

/-- A determiner yields a determiner denotation through the truth conditions of its sentences. -/
def Det.toGQ (D : Det α) : Quantifier.Det α := sentence D

/-- A sentence holds when its determiner holds of the noun's extension polarized by the scope. -/
theorem sentence_iff (D : Det α) (N vp : Set α) : sentence D N vp ↔ D (polarize N vp) :=
  ⟨fun ⟨_, ⟨hD, hX⟩, hd⟩ ↦ (delta_iff_eq_polarize hX).1 hd ▸ hD,
    fun h ↦ ⟨_, ⟨h, noun_polarize N vp⟩, (delta_iff_eq_polarize (noun_polarize N vp)).2 rfl⟩⟩

/-! ### Upper bounds, existential entailment and *zero* -/

open Examples in
/-- With three boys, *less than three boys sneezed* is false if they all sneezed and true if none
did, as judged. -/
theorem lessThan_three_matches_judgments :
    (ex_10.readings.lookup "true in the context" = some .acceptable ↔
      sentence (Det.lessThan 3) (⊤ : Set (Fin 3)) ⊤) ∧
    (ex_12.readings.lookup "true in the context" = some .acceptable ↔
      sentence (Det.lessThan 3) (⊤ : Set (Fin 3)) ⊥) := by
  simp [sentence_iff, Det.lessThan, ex_10, ex_12]

open Examples in
theorem classical_lessThan_three_misses_judgments :
    ¬ (ex_10.readings.lookup "true in the context" = some .acceptable ↔
      classicalSentence (·.card < 3) (⊤ : Set (Fin 3)) ⊤) ∧
    ¬ (ex_12.readings.lookup "true in the context" = some .acceptable ↔
      classicalSentence (·.card < 3) (⊤ : Set (Fin 3)) ⊥) := by
  simp [classical_lessThan_iff_some, Quantifier.Det.some, ex_10, ex_12]

theorem exactly_zero_eq_none [Finite α] : (Det.exactly 0 : Det α) = Det.none := by
  funext X
  simp only [Det.exactly, Det.none, Det.some, Pi.compl_apply, compl_iff_not, not_not]
  exact propext (Set.ncard_eq_zero (s := X.posAtoms))

theorem all_eq_delta_top : (Det.all : Det α) = (·.delta ⊤) := by
  funext X
  simp only [Det.all, delta, parts, negAtoms, Set.eq_empty_iff_forall_notMem, Set.mem_ofPred_eq,
    Prod.forall, Set.top_eq_univ, Set.mem_univ, true_iff]
  exact propext ⟨fun h x b hx ↦ by cases b <;> simp_all, fun h x hx ↦ by simpa using h x false hx⟩

theorem none_eq_delta_bot : (Det.none : Det α) = (·.delta ⊥) := by
  funext X
  simp only [Det.none, Det.some, Pi.compl_apply, compl_iff_not, not_not, delta, parts, posAtoms,
    Set.eq_empty_iff_forall_notMem, Set.mem_ofPred_eq, Prod.forall, Set.bot_eq_empty,
    Set.mem_empty_iff_false, false_iff]
  exact propext ⟨fun h x b hx ↦ by cases b <;> simp_all, fun h x hx ↦ by simpa using h x true hx⟩

theorem lessThan_eq_compl (n : ℕ) : (Det.lessThan n : Det α) = (Det.atLeast n)ᶜ := by
  funext X
  simp [Det.lessThan, Det.atLeast]

/-! ### Predicates and determiner denotations -/

section Relational

variable {Q : Quantifier.Det α}

theorem toGQ_ofGQ (Q : Quantifier.Det α) (R S : Set α) :
    (Det.ofGQ Q).toGQ R S ↔ Q R (R ∩ S) := by
  rw [Det.toGQ, sentence_iff, Det.ofGQ, atoms_polarize, posAtoms_polarize]

/-- The round trip is the identity exactly on the conservative quantifiers. -/
theorem toGQ_ofGQ_eq_iff (Q : Quantifier.Det α) : (Det.ofGQ Q).toGQ = Q ↔ Conservative Q := by
  refine ⟨fun h R S ↦ by rw [← toGQ_ofGQ Q R S, h], fun hQ ↦ ?_⟩
  funext R S
  exact propext ((toGQ_ofGQ Q R S).trans (hQ R S).symm)

theorem toGQ_ofGQ_of_conservative (hQ : Conservative Q) : (Det.ofGQ Q).toGQ = Q :=
  (toGQ_ofGQ_eq_iff Q).2 hQ

theorem sentence_ofGQ (hQ : Conservative Q) (R S : Set α) :
    sentence (Det.ofGQ Q) R S ↔ Q R S :=
  (toGQ_ofGQ Q R S).trans (hQ R S).symm

/-- Every predicate yields a conservative quantifier, so conservativity is a consequence of the
theory rather than a constraint on it. -/
theorem conservative_toGQ (D : Det α) : Conservative D.toGQ := fun R S ↦ by
  simp only [Det.toGQ, sentence_iff]
  rw [(polarize_eq_polarize_iff (vp' := R ∩ S)).2 fun _ hx ↦ (and_iff_right hx).symm]

theorem ofGQ_toGQ (D : Det α) : Det.ofGQ D.toGQ = D := by
  funext X
  simp only [Det.ofGQ, Det.toGQ, sentence_iff, polarize_atoms_posAtoms]

theorem toGQ_compl (D : Det α) : Dᶜ.toGQ = D.toGQᶜ := by
  funext R S
  simp [Det.toGQ, sentence_iff]

/-- The predicates are order isomorphic to the conservative quantifiers. -/
noncomputable def consDetOrderIso : ConsDet α ≃o Det α :=
  Equiv.toOrderIso
    { toFun Q := Det.ofGQ Q.1
      invFun D := ⟨D.toGQ, conservative_toGQ D⟩
      left_inv Q := Subtype.ext (toGQ_ofGQ_of_conservative Q.2)
      right_inv := ofGQ_toGQ }
    (fun _ _ h _ ↦ h _ _)
    (fun {D₁ D₂} h R S hs ↦ (sentence_iff D₂ R S).2 (h _ ((sentence_iff D₁ R S).1 hs)))

/-- The isomorphism sends Keenan and Stavi's atom at a restrictor `p` and a scope `q` inside it
to the predicate of the single group `polarize p q`. -/
theorem ofGQ_atom {p q : Set α} (h : q ⊆ p) :
    Det.ofGQ (KeenanStavi1986.atom p q) = ident (polarize p q) := by
  funext X
  refine propext ⟨fun ⟨hp, hq⟩ ↦ ?_, ?_⟩
  · rw [atoms_inter_posAtoms] at hq
    rw [ident, ← hp, ← hq, polarize_atoms_posAtoms]
  · rintro rfl
    refine ⟨atoms_polarize, ?_⟩
    rw [atoms_polarize, posAtoms_polarize, ← Set.inter_assoc, Set.inter_self,
      Set.inter_eq_right.2 h]

/-- The Härtig quantifier says that restrictor and scope have equally many members. -/
noncomputable def hartig : Quantifier.Det α := fun A B ↦ A.ncard = B.ncard

theorem not_conservative_hartig [Finite α] [Nontrivial α] :
    ¬ Conservative (hartig : Quantifier.Det α) := by
  intro h
  obtain ⟨a, b, hab⟩ := exists_pair_ne α
  have h' := (h {a} {b}).1 (by simp [hartig])
  simp only [hartig] at h'
  rw [Set.singleton_inter_eq_empty.2 (Set.mem_singleton_iff.not.2 hab)] at h'
  simp at h'

theorem toGQ_ofGQ_hartig [Finite α] : (Det.ofGQ hartig).toGQ = (every : Quantifier.Det α) := by
  funext R S
  refine propext ((toGQ_ofGQ hartig R S).trans ⟨fun h x hR ↦ ?_, fun h ↦ ?_⟩)
  · exact ((Set.ext_iff.1 (Set.eq_of_subset_of_ncard_le Set.inter_subset_left h.le) x).2 hR).2
  · exact congrArg Set.ncard (Set.inter_eq_left.2 h).symm

/-! #### The determiners as quantifiers -/

theorem all_eq_ofGQ : (Det.all : Det α) = Det.ofGQ every := by
  funext X
  simp only [Det.all, Det.ofGQ, every, eq_iff_iff, Set.eq_empty_iff_forall_notMem, Set.subset_def]
  refine forall_congr' fun x ↦ ?_
  simp only [negAtoms, atoms, posAtoms, Set.mem_ofPred_eq]
  cases X x with
  | bot => simp
  | coe b => cases b <;> simp

theorem some_eq_ofGQ : (Det.some : Det α) = Det.ofGQ Quantifier.Det.some := by
  funext X
  simp only [Det.some, Det.ofGQ, Quantifier.Det.some, atoms_inter_posAtoms,
    Set.nonempty_iff_ne_empty]

theorem none_eq_ofGQ : (Det.none : Det α) = Det.ofGQ no := by
  rw [Det.none, some_eq_ofGQ]
  funext X
  simp [Det.ofGQ, no_iff_not_some]

theorem notAll_eq_ofGQ : (Det.notAll : Det α) = Det.ofGQ everyᶜ := by
  rw [Det.notAll, all_eq_ofGQ]
  rfl

theorem atLeast_eq_ofGQ (n : ℕ) :
    (Det.atLeast n : Det α) = Det.ofGQ (Quantifier.Det.atLeast n) := by
  funext X
  simp only [Det.atLeast, Det.ofGQ, atLeast_apply, atoms_inter_posAtoms]

theorem exactly_eq_ofGQ (n : ℕ) :
    (Det.exactly n : Det α) = Det.ofGQ (Quantifier.Det.exactly n) := by
  funext X
  simp only [Det.exactly, Det.ofGQ, exactly_apply, atoms_inter_posAtoms]

theorem most_eq_ofGQ : (Det.most : Det α) = Det.ofGQ Quantifier.Det.most := by
  funext X
  simp only [Det.most, Det.ofGQ, most_apply, atoms_inter_posAtoms, atoms_diff_posAtoms]

theorem toGQ_atLeast (n : ℕ) : (Det.atLeast n : Det α).toGQ = Quantifier.Det.atLeast n := by
  rw [atLeast_eq_ofGQ, toGQ_ofGQ_of_conservative (conservative_atLeast n)]

/-- *Exactly two boys sneezed* says that exactly two boys sneezed. -/
theorem toGQ_exactly (n : ℕ) : (Det.exactly n : Det α).toGQ = Quantifier.Det.exactly n := by
  rw [exactly_eq_ofGQ, toGQ_ofGQ_of_conservative (conservative_exactly n)]

/-- *Less than three boys sneezed* says that fewer than three boys sneezed, with no upper-bound
or existential-entailment problem. -/
theorem toGQ_lessThan (n : ℕ) :
    (Det.lessThan n : Det α).toGQ = (Quantifier.Det.atLeast n)ᶜ := by
  rw [lessThan_eq_compl, toGQ_compl, toGQ_atLeast]

/-- *Most boys sneezed* has the truth conditions of the relational *most*. -/
theorem toGQ_most : (Det.most : Det α).toGQ = Quantifier.Det.most := by
  rw [most_eq_ofGQ, toGQ_ofGQ_of_conservative conservative_most]

/-- *All boys sneezed* has universal truth conditions. -/
theorem toGQ_all : (Det.all : Det α).toGQ = every := by
  rw [all_eq_ofGQ, toGQ_ofGQ_of_conservative conservative_every]

theorem toGQ_some : (Det.some : Det α).toGQ = Quantifier.Det.some := by
  rw [some_eq_ofGQ, toGQ_ofGQ_of_conservative conservative_some]

theorem toGQ_none : (Det.none : Det α).toGQ = no := by
  rw [none_eq_ofGQ, toGQ_ofGQ_of_conservative conservative_no]

end Relational

/-! ### Counting the predicates -/

section Count

variable [Fintype α]

theorem card_polarGroup : Nat.card (PolarGroup α) = 3 ^ Fintype.card α := by
  rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Flat Bool), Fintype.card_flat,
    Nat.card_eq_fintype_card, Fintype.card_bool]

theorem card_ne_bot : Nat.card {X : PolarGroup α // X ≠ ⊥} = 3 ^ Fintype.card α - 1 := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, ← Nat.card_eq_fintype_card,
    card_polarGroup, Fintype.card_subtype_eq]

theorem card_det : Nat.card (Det α) = 2 ^ 3 ^ Fintype.card α := by
  rw [← Nat.card_congr consDetOrderIso.toEquiv, KeenanStavi1986.card_consDet]

/-- Without the empty group there are `2 ^ (3 ^ n - 1)` predicates of groups on `n`
individuals. -/
theorem card_predicates :
    Nat.card ({X : PolarGroup α // X ≠ ⊥} → Prop) = 2 ^ (3 ^ Fintype.card α - 1) := by
  rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Prop), Fintype.card_prop, card_ne_bot]

theorem card_predicates_lt_card_gq :
    Nat.card ({X : PolarGroup α // X ≠ ⊥} → Prop) < Nat.card (Quantifier.Det α) := by
  rw [card_predicates, KeenanStavi1986.card_gq, pow_mul]
  refine Nat.pow_lt_pow_right (by norm_num) ?_
  calc 3 ^ Fintype.card α - 1 < 3 ^ Fintype.card α := Nat.sub_lt (by positivity) one_pos
    _ ≤ (2 ^ 2) ^ Fintype.card α := Nat.pow_le_pow_left (by norm_num) _

example : Nat.card ({X : PolarGroup (Fin 2) // X ≠ ⊥} → Prop) = 256 := by
  rw [card_predicates, Fintype.card_fin]; norm_num

example : Nat.card ({X : PolarGroup (Fin 3) // X ≠ ⊥} → Prop) = 67108864 := by
  rw [card_predicates, Fintype.card_fin]; norm_num

example : Nat.card (Quantifier.Det (Fin 2)) = 65536 := by
  rw [KeenanStavi1986.card_gq, Fintype.card_fin]; norm_num

end Count

/-- Two conservative determiner denotations give predicates that agree on the nonempty groups
exactly when they agree on the nonempty restrictors. -/
theorem eqOn_ofGQ_iff {Q Q' : Quantifier.Det α} (hQ : Conservative Q) (hQ' : Conservative Q') :
    Set.EqOn (Det.ofGQ Q) (Det.ofGQ Q') {⊥}ᶜ ↔ Set.EqOn Q Q' {R | R.Nonempty} := by
  refine ⟨fun h R hR ↦ funext fun S ↦ ?_, fun h X hX ↦ congrFun (h ?_) _⟩
  · have := h (x := polarize R S) (polarize_ne_bot_iff.2 hR)
    simp only [Det.ofGQ, atoms_polarize, posAtoms_polarize] at this
    exact propext ((hQ R S).trans ((Iff.of_eq this).trans (hQ' R S).symm))
  · exact Set.nonempty_iff_ne_empty.2 fun h0 ↦ hX (atoms_eq_empty_iff.1 h0)

/-! ### Existential and distributive scope -/

section Scope

variable (N : Set α)

theorem all_inf_noun : Det.all ⊓ noun N = ident (polarize N ⊤) := by
  rw [all_eq_delta_top]
  funext X
  exact propext ⟨fun ⟨h, hX⟩ ↦ (delta_iff_eq_polarize hX).1 h,
    fun h ↦ h ▸ ⟨(delta_iff_eq_polarize (noun_polarize N ⊤)).2 rfl, noun_polarize N ⊤⟩⟩

theorem none_inf_noun : Det.none ⊓ noun N = ident (polarize N ⊥) := by
  rw [none_eq_delta_bot]
  funext X
  exact propext ⟨fun ⟨h, hX⟩ ↦ (delta_iff_eq_polarize hX).1 h,
    fun h ↦ h ▸ ⟨(delta_iff_eq_polarize (noun_polarize N ⊥)).2 rfl, noun_polarize N ⊥⟩⟩

/-- Existential raising of *all `N`* is the Montague individual of the noun's wholly positive
group, so it is scopeless and the universal force stays with the ∆-operator. -/
theorem all_scopeless :
    Quantifier.Det.some (Set.ofPred (Det.all ⊓ noun N)) = individual (polarize N ⊤) :=
  some_eq_individual_iff.2 (all_inf_noun N)

theorem none_scopeless :
    Quantifier.Det.some (Set.ofPred (Det.none ⊓ noun N)) = individual (polarize N ⊥) :=
  some_eq_individual_iff.2 (none_inf_noun N)

/-- *Exactly two* of three individuals holds of several groups, so its existential raising is no
individual and an exceptional scope reading is predicted. -/
theorem exactly_two_not_individual :
    ¬ ∃ X₀, Quantifier.Det.some (Set.ofPred (Det.exactly 2 ⊓ noun (⊤ : Set (Fin 3)))) =
      individual X₀ := by
  have mem {a b : Fin 3} (hab : a ≠ b) : (Det.exactly 2 ⊓ noun ⊤) (polarize ⊤ {a, b}) := by
    refine ⟨?_, noun_polarize _ _⟩
    rw [Det.exactly, posAtoms_polarize, Set.top_eq_univ, Set.univ_inter, Set.ncard_pair hab]
  rintro ⟨X₀, h⟩
  have eq {X} (hX : (Det.exactly 2 ⊓ noun ⊤) X) : X = X₀ :=
    Set.mem_singleton_iff.1 ((Set.ext_iff.1 (some_eq_individual_iff.1 h) X).1 hX)
  have h₁ := eq (mem (show (0 : Fin 3) ≠ 1 by decide))
  have h₂ := eq (mem (show (0 : Fin 3) ≠ 2 by decide))
  simpa using polarize_eq_polarize_iff.1 (h₁.trans h₂.symm) 1 trivial

end Scope

/-! ### Collective predicates -/

section Collective

open Mereology

variable {β : Type*} [PartialOrder β] {C N : Set β} {X : PolarGroup β}

theorem delta_collective_iff (hC : ∀ x ∈ C, ¬ Atom x) (hX : noun {x | Atom x ∧ x ∈ N} X) :
    X.delta C ↔ X.posAtoms = ∅ := by
  rw [noun_iff] at hX
  have hA {x : β} {b : Bool} (hx : X x = ↑b) : Atom x :=
    (Set.ext_iff.1 hX x |>.1 (show X x ≠ ⊥ by simp [hx])).1
  refine ⟨fun h ↦ Set.eq_empty_iff_forall_notMem.2 fun x hx ↦ hC x ((h (x, true) hx).2 rfl)
    (hA hx), fun h ⟨x, b⟩ hx ↦ ?_⟩
  cases b
  · simpa using fun hc ↦ hC x hc (hA hx)
  · exact absurd hx (Set.eq_empty_iff_forall_notMem.1 h x)

/-- *Some boy gathered* is false, since a positive atom would have to gather. -/
theorem not_some_singular_collective (hC : ∀ x ∈ C, ¬ Atom x) :
    ¬ sentence Det.some {x | Atom x ∧ x ∈ N} C := fun ⟨_, ⟨hs, hX⟩, hd⟩ ↦
  hs ((delta_collective_iff hC hX).1 hd)

end Collective

/-! ### Questions -/

section Questions

open GroenendijkStokhof1984

variable {E W : Type*} (G P : E → Set W) (w : W)

/-- Two indices give the same answer to *which `G` `P`?*, read de re at `w`, exactly when they
polarize the `G`-individuals alike, so the answers correspond to the groups of the noun. -/
theorem whichDeRe_eq_ker :
    whichDeRe G P w = Setoid.ker fun v ↦ polarize (extension G w) (extension P v) := by
  ext v u
  rw [whichDeRe_iff, Setoid.ker_def, polarize_eq_polarize_iff]
  rfl

theorem sentence_relevant (D : Det E) :
    (whichDeRe G P w).Decides {v | sentence D (extension G w) (extension P v)} := by
  rw [whichDeRe_eq_ker, Setoid.decides_iff]
  intro v u h
  simp only [Set.mem_ofPred_eq, sentence_iff, Setoid.ker_def.1 h]

/-- Every conservative determiner is relevant to the question. -/
theorem relevant_of_conservative {Q : Quantifier.Det E} (hQ : Conservative Q) :
    (whichDeRe G P w).Decides {v | Q (extension G w) (extension P v)} := by
  simpa only [sentence_ofGQ hQ] using sentence_relevant G P w (Det.ofGQ Q)

end Questions

end Elliott2025
