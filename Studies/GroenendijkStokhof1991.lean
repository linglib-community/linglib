module

public import Linglib.Logic.Assignment
public import Linglib.Logic.CylindricAlgebra
public import Linglib.Semantics.Dynamic.DPL.Context
public import Linglib.Semantics.Dynamic.DRS.Dynamics

/-!
# Groenendijk and Stokhof (1991): Dynamic Predicate Logic

This file formalizes the logical facts of Groenendijk and Stokhof's "Dynamic predicate
logic", in which a formula denotes a relation between assignments. The paper's semantics is
the update algebra of `Semantics/Dynamic/Update.lean`: conjunction is relational composition, the
existential is a random reset followed by its scope, and negation, implication, disjunction,
the universal, and closure are the tests of the conditions `neg`, `impl`, `disj`, `dforall`,
and `SetRel.dom`, which is the content of the paper's translation of discourse representation
theory. Only the quantifiers mention assignments, so the propositional laws are proved of
updates over any state type and the quantifier laws over any register structure.

The notions of section 3.2 come first: s-equivalence and p-equivalence, which equivalence
implies but which together do not imply it, and the tests, on which all three coincide.
Section 3.4 then supplies the laws. The connectives are definable from negation, conjunction,
and the existential but not conversely, since a negation is a test and an existential is one
only over a contradictory scope (`isTest_dexists_iff`); double negation, commutativity, and
idempotency of conjunction hold exactly of tests, while contraposition, currying, and the de
Morgan laws hold outright. An existential binds without limit to its right because composition
is associative (`scope_extension`), and it has universal force in an antecedent because
implication curries (`donkey_equivalence`). Section 3.5's dynamic entailment (`Entails`)
satisfies the deduction theorem and reduces s-entailment to entailment from the closed
premiss, and it is neither reflexive nor transitive, by the paper's own counterexamples. The
satisfaction set of an existential computed in the proof of Fact 19 is the cylindrification of
its scope's, in the cylindric set algebra of Henkin, Monk and Tarski; that is the substrate's
`dom_dexists`. The laws are then read off
for the formulas of `DPL/Syntax.lean` under their interpretation `DPL.Formula.eval`, and the
paper's opening contrast is computed: `∃x Px ∧ Qx` binds the last occurrence of `x`, while its
double negation and its alphabetic variant `∃y Py ∧ Qx` do not. Section 4.1's normal binding form
(`nbf`) is defined by structural recursion, Definition 24's rebracketing clauses being theorems
of it; a formula is equivalent to its normal binding form, which is scope-bound, so that the
dynamic truth conditions of any formula are the first-order satisfaction conditions of its
normal binding form (`mem_dom_eval_iff_realize_nbf`). Conversely, eliminating conjunction,
implication and the existential gives every formula a scope-bound equivalent in predicate logic
(`mem_dom_eval_staticForm_iff`). Section 4.2's translation of discourse representation structures
(`DRT.DRS.toDPL`, Definition 28) preserves meaning: a condition becomes the test of its
verification and a box denotes its box relation (`DRT.DRS.eval_toDPL`, Fact 25).

## Implementation notes

The paper quantifies over models; an `Update S` fixes one, so its equivalence is equality of
relations, its contradiction is `∅`, and its counterexamples are stated over assignments into
a domain with two individuals, `[Nontrivial E]`. Truth with respect to an assignment and the
satisfaction set are both `SetRel.dom`, and the production set is `SetRel.cod`. That conditions
are tests, that tests are closed under conjunction, and that a test's production set is its
satisfaction set are the substrate's `isTest_test`, `IsTest.comp`, and `IsTest.cod_eq_dom`;
that closure and negation are idempotent on tests is `dom_test`. The paper lists idempotency
of disjunction as unconditional, but a disjunction is a test by Definition 2, so `φ ∨ φ` is the
closure of `φ` (`disj_self`) and the law holds exactly of tests. Fact 5, that a condition is a
test, is the substrate's `DPL.Formula.isTest_eval`. Fact 6, that the tests are the conditions
and the contradictions, holds up to equivalence, a test being equivalent to the condition `¬¬φ`
(`neg_neg_eq_self_iff_isTest`), and not of the syntactic class itself: `x = y ∧ ∃x[x = y]` is a
test in every structure and has an active quantifier (`isTest_eval_equal_conj_ex_equal`).

## References

* [groenendijk-stokhof-1991]
* [henkin-monk-tarski-1971]
* [kamp-reyle-1993]

## TODO

The remaining laws of section 3.4 with side conditions (the leftward scope extension,
commutativity and idempotency of conjunction, contraposition, distribution), Facts 26 and 27 on
the translated conditions, and the translation to quantificational dynamic logic of section 4.3.
-/

@[expose] public section

namespace GroenendijkStokhof1991

open DynamicSemantics Update SetRel

/-- The test connectives of Definition 2 and the closure of Definition 17, as tests of the
substrate's conditions; conjunction is `○`. -/
local notation:max "∼" φ:max => test (neg φ)

local notation:max "◇" φ:max => test (dom φ)

local notation:25 φ:26 " ⇒ " ψ:25 => test (impl φ ψ)

local notation:30 φ:31 " ⋎ " ψ:30 => test (disj φ ψ)

variable {S : Type*} (φ ψ χ : Update S)

/-! ### Meaning, truth, and equivalence, section 3.2 -/

/-- A formula is valid if it is true, and contradictory if it is false, with respect to every
assignment (Definitions 4 and 5). -/
def Valid : Prop := ∀ g, g ∈ φ.dom

def Contradiction : Prop := ∀ g, g ∉ φ.dom

/-- Two formulas are s-equivalent if they have the same satisfaction set (Definition 7). -/
def SEquiv : Prop := φ.dom = ψ.dom

/-- Two formulas are p-equivalent if they have the same production set (Definition 10). -/
def PEquiv : Prop := φ.cod = ψ.cod

variable {φ ψ} in
theorem SEquiv.of_eq (h : φ = ψ) : SEquiv φ ψ := h ▸ rfl

variable {φ ψ} in
theorem PEquiv.of_eq (h : φ = ψ) : PEquiv φ ψ := h ▸ rfl

/-- s-equivalence and p-equivalence together do not give equivalence (Fact 3). -/
theorem exists_sEquiv_pEquiv_ne {E : Type*} [Nontrivial E] :
    ∃ φ ψ : Update (Assignment E), SEquiv φ ψ ∧ PEquiv φ ψ ∧ φ ≠ ψ := by
  have hself (g : Assignment E) : g ~[dexists 0 (test Set.univ)] g :=
    ⟨g, ⟨g 0, (Function.update_eq_self 0 g).symm⟩, rfl, trivial⟩
  refine ⟨test Set.univ, dexists 0 (test Set.univ), ?_, ?_, fun h ↦ ?_⟩
  · exact Set.ext fun g ↦ ⟨fun _ ↦ ⟨g, hself g⟩, fun _ ↦ ⟨g, rfl, trivial⟩⟩
  · exact Set.ext fun g ↦ ⟨fun _ ↦ ⟨g, hself g⟩, fun _ ↦ ⟨g, rfl, trivial⟩⟩
  · obtain ⟨a, b, hab⟩ := exists_pair_ne E
    have hb : (fun _ ↦ a) ~[dexists 0 (test Set.univ)] Function.update (fun _ ↦ a) 0 b :=
      ⟨_, ⟨b, rfl⟩, rfl, trivial⟩
    rw [← h] at hb
    exact hab (by simpa using congr_fun hb.1 0)

variable {φ ψ}

/-- On tests, equivalence, s-equivalence, and p-equivalence coincide (Fact 4). -/
theorem sEquiv_iff_eq_of_isTest (hφ : IsTest φ) (hψ : IsTest ψ) : SEquiv φ ψ ↔ φ = ψ :=
  ⟨fun h ↦ (hφ.eq_test_dom.trans (congrArg test h)).trans hψ.eq_test_dom.symm, .of_eq⟩

theorem pEquiv_iff_eq_of_isTest (hφ : IsTest φ) (hψ : IsTest ψ) : PEquiv φ ψ ↔ φ = ψ := by
  rw [PEquiv, hφ.cod_eq_dom, hψ.cod_eq_dom]
  exact sEquiv_iff_eq_of_isTest hφ hψ

variable (φ ψ)

/-! ### Some logical facts, section 3.4 -/

theorem impl_eq_neg_comp_neg : (φ ⇒ ψ) = ∼(φ ○ ∼ψ) :=
  congrArg test (impl_eq_neg_comp_test_neg φ ψ)

theorem disj_eq_neg_comp_neg_neg : (φ ⋎ ψ) = ∼(∼φ ○ ∼ψ) := by
  rw [test_comp_test, neg_test, neg_eq_compl_dom, neg_eq_compl_dom, Set.compl_inter,
    compl_compl, compl_compl, disj_eq_dom_union_dom]

theorem disj_eq_neg_impl : (φ ⋎ ψ) = (∼φ ⇒ ψ) := by
  simp only [impl_eq_core_dom, core_test, neg_eq_compl_dom, compl_compl, disj_eq_dom_union_dom]

theorem neg_comp : ∼(φ ○ ψ) = (φ ⇒ ∼ψ) := by
  simp only [impl_eq_core_dom, dom_test, neg_eq_compl_dom, core_compl, dom_comp]

/-! #### Closure and double negation, Definition 17 -/

theorem close_eq_neg_neg : ◇φ = ∼∼φ := by
  rw [neg_test, neg_eq_compl_dom, compl_compl]

theorem close_eq_self_iff_isTest : ◇φ = φ ↔ IsTest φ :=
  ⟨fun h ↦ h ▸ isTest_test _, fun h ↦ h.eq_test_dom.symm⟩

theorem neg_neg_eq_self_iff_isTest : ∼∼φ = φ ↔ IsTest φ :=
  close_eq_neg_neg φ ▸ close_eq_self_iff_isTest φ

theorem close_eq_close_iff_sEquiv : ◇φ = ◇ψ ↔ SEquiv φ ψ := test_inj

theorem neg_close : ∼◇φ = ∼φ := by
  rw [neg_test, neg_eq_compl_dom]

theorem sEquiv_neg_neg : SEquiv φ ∼∼φ := by
  rw [SEquiv, ← close_eq_neg_neg, dom_test]

theorem close_comp : ◇(φ ○ ψ) = ∼(φ ⇒ ∼ψ) := by
  rw [← neg_comp, ← close_eq_neg_neg]

theorem close_comp_close : (◇φ ○ ◇ψ) = ∼(∼φ ⋎ ∼ψ) := by
  rw [disj_eq_neg_comp_neg_neg, ← close_eq_neg_neg, ← close_eq_neg_neg, ← close_eq_neg_neg]
  exact ((close_eq_self_iff_isTest _).mpr ((isTest_test _).comp (isTest_test _))).symm

theorem close_impl : (◇φ ⇒ ψ) = (∼φ ⋎ ψ) := by
  rw [disj_eq_neg_impl, ← close_eq_neg_neg]

/-! #### Conjunction and disjunction -/

variable {φ ψ} in
theorem comp_comm_of_isTest (hφ : IsTest φ) (hψ : IsTest ψ) : φ ○ ψ = ψ ○ φ := by
  rw [hφ.eq_test_dom, hψ.eq_test_dom, test_comp_test, test_comp_test, Set.inter_comm]

variable {φ} in
theorem comp_self_of_isTest (hφ : IsTest φ) : φ ○ φ = φ := by
  rw [hφ.eq_test_dom, test_comp_test, Set.inter_self]

theorem disj_self : (φ ⋎ φ) = ◇φ := by
  rw [disj_eq_dom_union_dom, Set.union_self]

theorem disj_comm : (φ ⋎ ψ) = (ψ ⋎ φ) := by
  rw [disj_eq_dom_union_dom, disj_eq_dom_union_dom, Set.union_comm]

theorem disj_assoc : ((φ ⋎ ψ) ⋎ χ) = (φ ⋎ (ψ ⋎ χ)) := by
  simp only [disj_eq_dom_union_dom, dom_test, Set.union_assoc]

theorem close_comp_disj : ◇(φ ○ (ψ ⋎ χ)) = ((φ ○ ψ) ⋎ (φ ○ χ)) := by
  simp only [dom_comp, dom_test, disj_eq_dom_union_dom, preimage_union]

theorem disj_close_comp : (φ ⋎ (◇ψ ○ χ)) = ((φ ⋎ ψ) ○ (φ ⋎ χ)) := by
  simp only [test_comp_test, disj_eq_dom_union_dom, dom_comp, preimage_test,
    Set.union_inter_distrib_left]

/-! #### Implication -/

theorem neg_impl_comm : (∼φ ⇒ ψ) = (∼ψ ⇒ φ) := by
  rw [← disj_eq_neg_impl, ← disj_eq_neg_impl, disj_comm]

theorem close_impl_eq_neg_impl_neg : (◇φ ⇒ ψ) = (∼ψ ⇒ ∼φ) := by
  rw [close_impl, disj_comm, disj_eq_neg_impl]

theorem impl_close_right : (φ ⇒ ◇ψ) = (φ ⇒ ψ) := by
  rw [impl_eq_neg_comp_neg, neg_close, ← impl_eq_neg_comp_neg]

theorem impl_impl : (φ ⇒ (ψ ⇒ χ)) = ((φ ○ ψ) ⇒ χ) :=
  congrArg test (impl_comp φ ψ χ).symm

/-! #### Quantifiers and connectives

The existential is the random reset composed with its scope and the universal is implication
from the reset, so the quantifier laws are the propositional ones at the reset and hold over
any register structure. -/

section Quantifiers

variable {R S E : Type*} [RegisterStructure R S E] (x : R) (φ ψ : Update S)

theorem forall_eq_neg_exists_neg : test (dforall x φ) = ∼(dexists x ∼φ) :=
  impl_eq_neg_comp_neg _ _

theorem neg_exists_eq_forall_neg : ∼(dexists x φ) = test (dforall x ∼φ) :=
  neg_comp _ _

theorem close_exists : ◇(dexists x φ) = ∼(test (dforall x ∼φ)) := by
  rw [close_eq_neg_neg, neg_exists_eq_forall_neg]

theorem scope_extension : dexists x φ ○ ψ = dexists x (φ ○ ψ) :=
  comp_assoc ..

theorem donkey_equivalence : (dexists x φ ⇒ ψ) = test (dforall x (φ ⇒ ψ)) :=
  (impl_impl _ _ _).symm

end Quantifiers

/-! #### What the static constants cannot define -/

section Assignments

variable {E : Type*} (x : ℕ) (φ ψ : Update (Assignment E))

theorem isTest_dexists_iff [Nontrivial E] : IsTest (dexists x φ) ↔ Contradiction φ := by
  refine ⟨fun h g ⟨k, hφ⟩ ↦ ?_, fun hc ⟨_, _⟩ ⟨_, _, hφ⟩ ↦ (hc _ ⟨_, hφ⟩).elim⟩
  obtain ⟨e, he⟩ := exists_ne (g x)
  have hg (e' : E) : Function.update g x e' = k := h.eq ⟨g, ⟨g x, by simp⟩, hφ⟩
  exact he (by simpa using congr_fun ((hg e).trans (hg (g x)).symm) x)

theorem exists_eq_neg_forall_neg_iff [Nontrivial E] :
    dexists x φ = ∼(test (dforall x ∼φ)) ↔ Contradiction φ := by
  rw [← isTest_dexists_iff, ← close_exists, eq_comm, close_eq_self_iff_isTest]

theorem sEquiv_exists_neg_forall_neg : SEquiv (dexists x φ) ∼(test (dforall x ∼φ)) := by
  rw [SEquiv, ← close_exists, dom_test]

theorem comp_eq_neg_impl_neg_iff {S : Type*} (φ ψ : Update S) :
    φ ○ ψ = ∼(φ ⇒ ∼ψ) ↔ IsTest (φ ○ ψ) := by
  rw [← close_comp, eq_comm, close_eq_self_iff_isTest]

theorem sEquiv_comp_neg_impl_neg {S : Type*} (φ ψ : Update S) :
    SEquiv (φ ○ ψ) ∼(φ ⇒ ∼ψ) := by
  rw [SEquiv, ← close_comp, dom_test]

theorem neg_neg_exists_eq_iff [Nontrivial E] :
    ∼∼(dexists x φ) = dexists x φ ↔ Contradiction φ :=
  (neg_neg_eq_self_iff_isTest _).trans (isTest_dexists_iff x φ)

theorem dne_fails_anaphora [Nontrivial E] :
    ∃ (x : ℕ) (φ : Update (Assignment E)), ∼∼(dexists x φ) ≠ dexists x φ :=
  ⟨0, test Set.univ, fun h ↦
    (neg_neg_exists_eq_iff 0 _).mp h (fun _ ↦ Classical.arbitrary E) ⟨_, rfl, trivial⟩⟩

theorem not_sEquiv_comp_neg_disj_neg [Nontrivial E] :
    ∃ φ ψ : Update (Assignment E), ¬ SEquiv (φ ○ ψ) ∼(∼φ ⋎ ∼ψ) := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne E
  refine ⟨dexists 0 (test {g | g 0 = a}), test {g | g 0 = a}, fun h ↦ ?_⟩
  have hb : (fun _ ↦ b) ∈ (dexists 0 (test {g | g 0 = a}) ○ test {g | g 0 = a}).dom :=
    ⟨_, _, ⟨_, ⟨a, rfl⟩, rfl, by simp⟩, rfl, by simp⟩
  rw [h, dom_test, neg_test, disj_eq_dom_union_dom, dom_test, dom_test, neg_test] at hb
  exact hb (.inr fun hba ↦ hab (by simpa using hba.symm))

theorem not_sEquiv_impl_neg_disj [Nontrivial E] :
    ∃ φ ψ : Update (Assignment E), ¬ SEquiv (φ ⇒ ψ) (∼φ ⋎ ψ) := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne E
  refine ⟨dexists 0 (test {g | g 0 = a}), test {g | g 0 = a}, fun h ↦ ?_⟩
  have hb : (fun _ ↦ b) ∈ (dexists 0 (test {g | g 0 = a}) ⇒ test {g | g 0 = a}).dom := by
    rw [dom_test]
    rintro _ ⟨_, -, rfl, hd⟩
    exact ⟨_, rfl, hd⟩
  rw [h, dom_test] at hb
  obtain ⟨_, -, hn⟩ | ⟨_, rfl, hb⟩ := hb
  · exact hn ⟨_, _, ⟨a, rfl⟩, rfl, by simp⟩
  · exact hab (by simpa using hb.symm)

theorem comp_not_comm [Nontrivial E] : ∃ φ ψ : Update (Assignment E), φ ○ ψ ≠ ψ ○ φ := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne E
  refine ⟨dexists 0 (test Set.univ), test {g | g 0 = a}, fun h ↦ ?_⟩
  have hb : (fun _ ↦ b) ~[dexists 0 (test Set.univ) ○ test {g | g 0 = a}]
      Function.update (fun _ ↦ b) 0 a :=
    ⟨_, ⟨_, ⟨a, rfl⟩, rfl, trivial⟩, rfl, by simp⟩
  rw [h] at hb
  obtain ⟨_, ⟨rfl, hb⟩, -⟩ := hb
  exact hab (by simpa using hb.symm)

theorem comp_not_idem [Nontrivial E] : ∃ φ : Update (Assignment E), φ ○ φ ≠ φ := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne E
  refine ⟨test {g | g 0 = a} ○ dexists 0 (test {g | g 0 = b}), fun h ↦ ?_⟩
  have hb : (fun _ ↦ a) ~[test {g | g 0 = a} ○ dexists 0 (test {g | g 0 = b})]
      Function.update (fun _ ↦ a) 0 b :=
    ⟨_, ⟨rfl, rfl⟩, _, ⟨b, rfl⟩, rfl, by simp⟩
  rw [← h] at hb
  obtain ⟨_, ⟨_, -, _, -, rfl, hd⟩, _, ⟨rfl, hk⟩, -⟩ := hb
  exact hab (hk.symm.trans hd)

end Assignments

/-! ### Entailment, section 3.5 -/

/-- A premiss s-entails a conclusion if truth is preserved from one to the other
(Definition 18). -/
def SEntails : Prop := φ.dom ⊆ ψ.dom

/-- A premiss dynamically entails a conclusion if every output of the premiss is an input on
which the conclusion succeeds (Definition 20). -/
def Entails : Prop := φ.cod ⊆ ψ.dom

variable {φ ψ} in
/-- Meaning inclusion (Definition 19) implies s-entailment (Fact 10). -/
theorem SEntails.of_subset (h : φ ⊆ ψ) : SEntails φ ψ :=
  fun _ ⟨k, hk⟩ ↦ ⟨k, h hk⟩

/-- The deduction theorem (Fact 11) says that `φ ⊨ ψ` iff `φ → ψ` is valid. -/
theorem entails_iff_valid_impl : Entails φ ψ ↔ Valid (φ ⇒ ψ) := by
  simp only [Valid, dom_test]
  exact ⟨fun h _ _ hk ↦ h ⟨_, hk⟩, fun h _ ⟨g, hk⟩ ↦ h g hk⟩

/-- s-entailment is dynamic entailment from the closed premiss (Fact 12). -/
theorem sEntails_iff_entails_close : SEntails φ ψ ↔ Entails ◇φ ψ := by
  rw [Entails, cod_test, SEntails]

theorem entails_close_self : Entails ◇φ φ :=
  (sEntails_iff_entails_close φ φ).mp subset_rfl

theorem entails_neg_neg_self : Entails ∼∼φ φ :=
  close_eq_neg_neg φ ▸ entails_close_self φ

section Assignments

variable {E : Type*} (x : ℕ)

theorem entails_exists_atom (p : E → Prop) :
    Entails (dexists x (test {g : Assignment E | p (g x)})) (test {g | p (g x)}) := by
  rintro _ ⟨_, _, -, rfl, hp⟩
  exact ⟨_, rfl, hp⟩

/-- `Px ⊨ ∃xPx` as well, so the two entail each other yet are not equivalent, the atom being a
test and the existential not. Mutual entailment is weaker than equivalence. -/
theorem entails_atom_exists (p : E → Prop) :
    Entails (test {g : Assignment E | p (g x)}) (dexists x (test {g | p (g x)})) := by
  rintro _ ⟨h, rfl, hp⟩
  exact ⟨h, h, ⟨h x, (Function.update_eq_self x h).symm⟩, rfl, hp⟩

theorem not_sEntails_exists_atom [Nontrivial E] :
    ∃ p : E → Prop, ¬ SEntails (dexists 0 (test {g : Assignment E | p (g 0)}))
      (test {g | p (g 0)}) := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne E
  refine ⟨(· = a), fun h ↦ ?_⟩
  obtain ⟨_, rfl, hb⟩ := h (a := fun _ ↦ b) ⟨_, _, ⟨a, rfl⟩, rfl, by simp⟩
  exact hab (by simpa using hb.symm)

/-- Dynamic entailment is not reflexive, as `Px ∧ ∃xQx` shows (cf. Fact 15). -/
theorem not_entails_self [Nontrivial E] : ∃ φ : Update (Assignment E), ¬ Entails φ φ := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne E
  refine ⟨test {g | g 0 = a} ○ dexists 0 (test Set.univ), fun h ↦ ?_⟩
  have hb : (fun _ ↦ a) ~[test {g | g 0 = a} ○ dexists 0 (test Set.univ)]
      Function.update (fun _ ↦ a) 0 b :=
    ⟨_, ⟨rfl, rfl⟩, _, ⟨b, rfl⟩, rfl, trivial⟩
  obtain ⟨_, _, ⟨rfl, hb⟩, -⟩ := h ⟨_, hb⟩
  exact hab (by simpa using hb.symm)

/-- Dynamic entailment is not transitive, since `¬¬∃xPx ⊨ ∃xPx` and `∃xPx ⊨ Px` but `¬¬∃xPx ⊭ Px`
(cf. Fact 16). -/
theorem not_entails_trans [Nontrivial E] :
    ∃ p : E → Prop, ¬ Entails ∼∼(dexists 0 (test {g : Assignment E | p (g 0)}))
      (test {g | p (g 0)}) := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne E
  refine ⟨(· = a), fun h ↦ ?_⟩
  rw [← close_eq_neg_neg, ← sEntails_iff_entails_close] at h
  obtain ⟨_, rfl, hb⟩ := h (a := fun _ ↦ b) ⟨_, _, ⟨a, rfl⟩, rfl, by simp⟩
  exact hab (by simpa using hb.symm)

theorem not_entails_comp_exists [Nontrivial E] :
    ∃ p : E → Prop, ¬ Entails (dexists 0 (test {g : Assignment E | p (g 0)}) ○
      dexists 0 (test Set.univ)) (test {g | p (g 0)}) := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne E
  refine ⟨(· = a), fun h ↦ ?_⟩
  have hc : (fun _ ↦ b) ~[dexists 0 (test {g : Assignment E | g 0 = a}) ○
      dexists 0 (test Set.univ)] fun _ ↦ b :=
    ⟨_, ⟨_, ⟨a, rfl⟩, rfl, by simp⟩, _, ⟨b, by simp⟩, rfl, trivial⟩
  obtain ⟨_, rfl, hb⟩ := h ⟨_, hc⟩
  exact hab (by simpa using hb.symm)

end Assignments

/-- Definition 21's entailment fixing the variables in `X` holds when every output of the premiss
has an output of the conclusion that agrees with it on `X`. -/
def EntailsOn {V E : Type*} (X : Finset V) (D₁ D₂ : Update (V → E)) : Prop :=
  ∀ g ∈ D₁.cod, ∃ h, g ~[D₂] h ∧ Set.EqOn h g ↑X

theorem EntailsOn.entails {V E : Type*} {X : Finset V} {D₁ D₂ : Update (V → E)}
    (h : EntailsOn X D₁ D₂) : Entails D₁ D₂ :=
  fun g hg ↦ let ⟨k, hk, _⟩ := h g hg; ⟨k, hk⟩

/-! ### The normal binding form, section 4.1

Definition 24's recipe `b` brings every variable a quantifier binds into its scope: it
rebrackets a conjunction to the right, moves an existential out of a left conjunct, and does
the same for an antecedent, where the existential becomes a universal. -/

section NormalBindingForm

open FirstOrder DPL DPL.Formula

universe u v w

variable {L : Language.{u, v}} {V : Type w}

/-- The normal binding form of a conjunction whose conjuncts are in normal binding form. -/
def conjNbf : Formula L V → Formula L V → Formula L V
  | .conj χ₁ χ₂, ρ => conjNbf χ₁ (conjNbf χ₂ ρ)
  | .ex x χ, ρ => ∃[x] (conjNbf χ ρ)
  | φ, ρ => φ ⋏ ρ

/-- The normal binding form of an implication whose parts are in normal binding form. -/
def impNbf : Formula L V → Formula L V → Formula L V
  | .conj χ₁ χ₂, ρ => impNbf χ₁ (impNbf χ₂ ρ)
  | .ex x χ, ρ => ∀[x] (impNbf χ ρ)
  | φ, ρ => φ ⟿ ρ

/-- The normal binding form of a formula, Definition 24. -/
def nbf : Formula L V → Formula L V
  | .neg φ => ¬ᵈ(nbf φ)
  | .conj φ ψ => conjNbf (nbf φ) (nbf ψ)
  | .disj φ ψ => nbf φ ⋎ nbf ψ
  | .imp φ ψ => impNbf (nbf φ) (nbf ψ)
  | .ex x φ => ∃[x] (nbf φ)
  | .all x φ => ∀[x] (nbf φ)
  | φ => φ

/-- The formula with conjunction, implication, and the existential eliminated in favour of
negation, disjunction, and the universal, the `#φ` of Fact 22. -/
def staticForm : Formula L V → Formula L V
  | .neg φ => ¬ᵈ(staticForm φ)
  | .conj φ ψ => ¬ᵈ(¬ᵈ(staticForm φ) ⋎ ¬ᵈ(staticForm ψ))
  | .disj φ ψ => staticForm φ ⋎ staticForm ψ
  | .imp φ ψ => ¬ᵈ(staticForm φ) ⋎ staticForm ψ
  | .ex x φ => ¬ᵈ∀[x] ¬ᵈ(staticForm φ)
  | .all x φ => ∀[x] (staticForm φ)
  | φ => φ

variable (φ ψ χ ρ : Formula L V) (x : V)

theorem conjNbf_conjNbf : conjNbf (conjNbf φ ψ) ρ = conjNbf φ (conjNbf ψ ρ) := by
  induction φ generalizing ψ ρ <;> simp_all [conjNbf]

theorem impNbf_conjNbf : impNbf (conjNbf φ ψ) ρ = impNbf φ (impNbf ψ ρ) := by
  induction φ generalizing ψ ρ <;> simp_all [conjNbf, impNbf]

/-- Clauses 7(a) and 7(b) of Definition 24. -/
theorem nbf_conj_conj : nbf ((φ ⋏ ψ) ⋏ χ) = nbf (φ ⋏ (ψ ⋏ χ)) := by
  simp only [nbf, conjNbf_conjNbf]

theorem nbf_ex_conj : nbf ((∃[x] φ) ⋏ ψ) = ∃[x] (nbf (φ ⋏ ψ)) := by
  simp only [nbf, conjNbf]

/-- Clauses 8(a) and 8(b) of Definition 24. -/
theorem nbf_conj_imp : nbf ((φ ⋏ ψ) ⟿ χ) = nbf (φ ⟿ (ψ ⟿ χ)) := by
  simp only [nbf, impNbf_conjNbf]

theorem nbf_ex_imp : nbf ((∃[x] φ) ⟿ ψ) = ∀[x] (nbf (φ ⟿ ψ)) := by
  simp only [nbf, impNbf]

/-- In the paper's example, `[∃xPx ∧ ∃yQy] ∧ Rxy` has the normal binding form
`∃x[Px ∧ ∃y[Qy ∧ Rxy]]`. -/
example (P Q : L.Relations 1) (R : L.Relations 2) (y : V) :
    nbf (((∃[x] (rel P fun _ ↦ .var x)) ⋏ ∃[y] (rel Q fun _ ↦ .var y)) ⋏
        rel R ![.var x, .var y]) =
      ∃[x] (rel P (fun _ ↦ .var x) ⋏ ∃[y] (rel Q (fun _ ↦ .var y) ⋏ rel R ![.var x, .var y])) :=
  rfl

end NormalBindingForm

/-! ### The laws on formulas

The formulas of `DPL/Syntax.lean` are interpreted by `DPL.Formula.eval` in the update algebra, so
the laws above hold of them: two formulas are equivalent in a structure when their
interpretations are the same relation. -/

section Formulas

open FirstOrder DPL DPL.Formula CylindricAlgebra

universe u v w x

variable {L : Language.{u, v}} {V : Type w} [DecidableEq V] (M : Type x) [L.Structure M]
  (φ ψ χ : Formula L V) (x y : V)

theorem eval_imp_eq : (φ ⟿ ψ).eval M = (¬ᵈ(φ ⋏ ¬ᵈψ)).eval M :=
  impl_eq_neg_comp_neg _ _

theorem eval_disj_eq : (φ ⋎ ψ).eval M = (¬ᵈ(¬ᵈφ ⋏ ¬ᵈψ)).eval M :=
  disj_eq_neg_comp_neg_neg _ _

theorem eval_all_eq : (∀[x] φ).eval M = (¬ᵈ∃[x] ¬ᵈφ).eval M :=
  forall_eq_neg_exists_neg x _

theorem eval_neg_neg_eq_iff : (¬ᵈ¬ᵈφ).eval M = φ.eval M ↔ IsTest (φ.eval M) :=
  neg_neg_eq_self_iff_isTest _

theorem eval_ex_conj : ((∃[x] φ) ⋏ ψ).eval M = (∃[x] (φ ⋏ ψ)).eval M :=
  scope_extension x _ _

theorem eval_ex_imp : ((∃[x] φ) ⟿ ψ).eval M = (∀[x] (φ ⟿ ψ)).eval M :=
  donkey_equivalence x _ _

/-! #### Free variables, active quantifiers, and entailment

Facts 8 and 9 are the two halves of the typing of a formula by its context
(`DPL.Formula.hasContext_eval`): truth depends only on the free variables, and only the active
quantifier variables change. With them the properties entailment lacks in general are restored
under conditions on the two sets. -/

variable {M φ ψ χ} {g h : V → M}

/-- The truth of a formula depends only on its free variables (Fact 8). -/
theorem dependsOn_dom_eval : DependsOn (· ∈ (φ.eval M).dom) (↑φ.fv : Set V) := by
  rw [← context_I]
  exact (φ.hasContext_eval M).dependsOn_dom

/-- A formula changes the values of its active quantifier variables only (Fact 9). -/
theorem eqOn_of_eval (hgh : g ~[φ.eval M] h) : Set.EqOn g h (↑φ.aqv : Set V)ᶜ := by
  rw [← context_B]
  exact (φ.hasContext_eval M).blocks hgh

theorem mem_dom_eval_iff (hd : Disjoint φ.aqv ψ.fv) (hgh : g ~[φ.eval M] h) :
    g ∈ (ψ.eval M).dom ↔ h ∈ (ψ.eval M).dom :=
  (φ.hasContext_eval M).mem_dom_iff (ψ.hasContext_eval M) (by rwa [context_B, context_I]) hgh

/-- s-entailment and entailment coincide when the premiss binds nothing in the conclusion
(Fact 13). -/
theorem sEntails_iff_entails (hd : Disjoint φ.aqv ψ.fv) :
    SEntails (φ.eval M) (ψ.eval M) ↔ Entails (φ.eval M) (ψ.eval M) :=
  ⟨fun hs _ ⟨_, hgh⟩ ↦ (mem_dom_eval_iff hd hgh).mp (hs ⟨_, hgh⟩),
    fun he _ ⟨_, hgh⟩ ↦ (mem_dom_eval_iff hd hgh).mpr (he ⟨_, hgh⟩)⟩

/-- Meaning inclusion gives entailment when the premiss binds nothing in the conclusion
(Fact 14). -/
theorem entails_of_subset (hd : Disjoint φ.aqv ψ.fv) (hsub : φ.eval M ⊆ ψ.eval M) :
    Entails (φ.eval M) (ψ.eval M) :=
  (sEntails_iff_entails hd).mp (SEntails.of_subset hsub)

/-- A formula that binds none of its own free variables entails itself (Fact 15). -/
theorem entails_self (hd : Disjoint φ.aqv φ.fv) : Entails (φ.eval M) (φ.eval M) :=
  entails_of_subset hd subset_rfl

theorem entails_conj_right (hd : Disjoint ψ.aqv ψ.fv) :
    Entails ((φ ⋏ ψ).eval M) (ψ.eval M) := by
  rintro _ ⟨_, _, _, hkh⟩
  exact (mem_dom_eval_iff hd hkh).mp ⟨_, hkh⟩

/-- Entailment is transitive when the first step fixes the variables the middle formula binds in
the conclusion (Fact 16). -/
theorem EntailsOn.trans (h₁ : EntailsOn (ψ.aqv ∩ χ.fv) (φ.eval M) (ψ.eval M))
    (h₂ : Entails (ψ.eval M) (χ.eval M)) : Entails (φ.eval M) (χ.eval M) := by
  intro g hg
  obtain ⟨k, hgk, hX⟩ := h₁ g hg
  refine (dependsOn_dom_eval (φ := χ) fun v hv ↦ ?_).to_iff.mp (h₂ ⟨g, hgk⟩)
  by_cases hv' : v ∈ ψ.aqv
  · exact hX (by simp [hv', Finset.mem_coe.mp hv])
  · exact (eqOn_of_eval hgk (by simpa using hv')).symm

variable (M φ ψ χ)

/-! #### The normal binding form and predicate logic

A formula and its normal binding form have the same interpretation, the normal binding form is
scope-bound, and on a scope-bound formula dynamic truth is first-order satisfaction
(`DPL.Formula.IsScopeBound.mem_dom_eval_iff`, Fact 19). So the dynamic truth conditions of any
formula are the first-order ones of its normal binding form, and those of a formula built from
the static constants alone are its own. -/

theorem eval_conjNbf : (conjNbf φ ψ).eval M = φ.eval M ○ ψ.eval M := by
  induction φ generalizing ψ <;> simp_all [conjNbf, dexists, comp_assoc]

theorem eval_impNbf : (impNbf φ ψ).eval M = test (impl (φ.eval M) (ψ.eval M)) := by
  induction φ generalizing ψ <;> simp_all [impNbf, dexists, dforall, impl_comp]

/-- A formula is equivalent to its normal binding form (Fact 17). -/
theorem eval_nbf : (nbf φ).eval M = φ.eval M := by
  induction φ <;> simp_all [nbf, eval_conjNbf, eval_impNbf]

theorem isScopeBound_conjNbf (hφ : φ.IsScopeBound) (hψ : ψ.IsScopeBound) :
    (conjNbf φ ψ).IsScopeBound := by
  induction φ generalizing ψ <;> simp_all [conjNbf, IsScopeBound, aqv]

theorem isScopeBound_impNbf (hφ : φ.IsScopeBound) (hψ : ψ.IsScopeBound) :
    (impNbf φ ψ).IsScopeBound := by
  induction φ generalizing ψ <;> simp_all [impNbf, IsScopeBound, aqv]

/-- In a normal binding form every variable a quantifier binds is in its scope (Fact 18). -/
theorem isScopeBound_nbf : (nbf φ).IsScopeBound := by
  induction φ with
  | conj φ ψ ihφ ihψ => exact isScopeBound_conjNbf _ _ ihφ ihψ
  | imp φ ψ ihφ ihψ => exact isScopeBound_impNbf _ _ ihφ ihψ
  | _ => simp_all [nbf, IsScopeBound]

theorem mem_dom_eval_iff_realize_nbf {g : V → M} :
    g ∈ (φ.eval M).dom ↔ (nbf φ).toFormula.Realize g := by
  rw [← eval_nbf]
  exact (isScopeBound_nbf φ).mem_dom_eval_iff M

theorem isScopeBound_staticForm : (staticForm φ).IsScopeBound := by
  induction φ <;> simp_all [staticForm, IsScopeBound]

theorem realize_toFormula_staticForm {g : V → M} :
    (staticForm φ).toFormula.Realize g ↔ φ.toFormula.Realize g := by
  induction φ generalizing g <;>
    simp_all [staticForm, toFormula, imp_iff_not_or]

/-- Read in predicate logic, every formula is equivalent to its static form, whose dynamic truth
conditions are those same first-order ones (Fact 22). -/
theorem mem_dom_eval_staticForm_iff {g : V → M} :
    g ∈ ((staticForm φ).eval M).dom ↔ φ.toFormula.Realize g :=
  ((isScopeBound_staticForm φ).mem_dom_eval_iff M).trans (realize_toFormula_staticForm M φ)

/-- A scope-bound formula is valid in dynamic predicate logic iff it is in predicate logic
(Fact 23). -/
theorem valid_eval_iff (hφ : φ.IsScopeBound) :
    Valid (φ.eval M) ↔ ∀ g : V → M, φ.toFormula.Realize g :=
  forall_congr' fun _ ↦ hφ.mem_dom_eval_iff M

/-! #### Binding beyond scope

*A man walks in the park. He whistles*, `∃x Px ∧ Qx`: the existential binds the occurrence of
its variable in the second conjunct, outside its scope. Under a double negation it does not,
and neither does the existential of an alphabetic variant, so the three formulas below have
different truth conditions while the first and the third are alphabetic variants. -/

variable {M} (P Q : L.Relations 1) (g : V → M)

/-- The atomic formula `Px`. -/
abbrev atom (P : L.Relations 1) (x : V) : Formula L V := rel P fun _ ↦ .var x

theorem mem_dom_eval_ex_conj_atom :
    g ∈ (((∃[x] (atom P x)) ⋏ atom Q x).eval M).dom ↔
      ∃ d : M, Language.Structure.RelMap P (fun _ ↦ d) ∧ Language.Structure.RelMap Q fun _ ↦ d := by
  simp only [eval_conj, eval_ex, eval_rel, dom_comp, dom_test, mem_preimage, mem_dexists,
    mem_test]
  constructor
  · rintro ⟨_, hQ, d, rfl, hP⟩
    exact ⟨d, by simpa using hP, by simpa using hQ⟩
  · rintro ⟨d, hP, hQ⟩
    exact ⟨_, by simpa using hQ, d, rfl, by simpa using hP⟩

theorem mem_dom_eval_neg_neg_ex_conj_atom :
    g ∈ (((¬ᵈ¬ᵈ∃[x] (atom P x)) ⋏ atom Q x).eval M).dom ↔
      (∃ d : M, Language.Structure.RelMap P fun _ ↦ d) ∧
        Language.Structure.RelMap Q fun _ ↦ g x := by
  simp only [eval_conj, eval_neg, eval_ex, eval_rel, neg_eq_compl_dom, compl_compl,
    dom_comp, preimage_test, dom_test, dom_dexists, Set.mem_inter_iff, mem_cyl]
  simp

/-- `∃y Py ∧ Qx`, an alphabetic variant of `∃x Px ∧ Qx`, has the truth conditions of the doubly
negated formula. -/
theorem mem_dom_eval_ex_conj_atom_of_ne (hxy : x ≠ y) :
    g ∈ (((∃[y] (atom P y)) ⋏ atom Q x).eval M).dom ↔
      (∃ d : M, Language.Structure.RelMap P fun _ ↦ d) ∧
        Language.Structure.RelMap Q fun _ ↦ g x := by
  simp only [eval_conj, eval_ex, eval_rel, dom_comp, dom_test, mem_preimage, mem_dexists,
    mem_test]
  constructor
  · rintro ⟨_, hQ, d, rfl, hP⟩
    exact ⟨⟨d, by simpa using hP⟩, by simpa [Function.update_of_ne hxy] using hQ⟩
  · rintro ⟨⟨d, hP⟩, hQ⟩
    exact ⟨_, by simpa [Function.update_of_ne hxy] using hQ, d, rfl, by simpa using hP⟩

theorem not_isScopeBound_ex_conj_atom : ¬ ((∃[x] (atom P x)) ⋏ atom Q x).IsScopeBound := by
  simp [IsScopeBound, aqv, fv]

theorem isScopeBound_ex_conj_atom_of_ne (hxy : x ≠ y) :
    ((∃[y] (atom P y)) ⋏ atom Q x).IsScopeBound := by
  simp [IsScopeBound, aqv, fv, hxy.symm]

theorem isTest_eval_equal_conj_ex_equal (hxy : x ≠ y) :
    IsTest (((.var x ≐ .var y) ⋏ ∃[x] (.var x ≐ .var y) : Formula L V).eval M) := by
  rintro ⟨g, h⟩ ⟨_, ⟨rfl, hg⟩, hex⟩
  obtain ⟨e, rfl, he⟩ := mem_dexists.mp hex
  simp only [Set.mem_ofPred_eq, Language.Term.realize_var, RegisterStructure.extend_eq_update,
    Function.update_self, Function.update_of_ne hxy.symm] at he hg
  show g = Function.update g x e
  rw [he, ← hg, Function.update_eq_self]

end Formulas

/-! ### Discourse representation theory, section 4.2

Definition 28 translates a discourse representation structure into a formula: a box becomes the
existential closure, over its referents, of the conjunction of its translated conditions, and
a complex condition the corresponding connective over its translated sub-boxes. Fact 25 says
the translation preserves meaning: a condition becomes a test of its verification, and a box
denotes its box relation `DRT.DRS.toRel`. -/

section DRT

open FirstOrder DPL DPL.Formula DRT

universe u v w x

variable {L : Language.{u, v}} {V : Type w}

mutual
/-- The translation of a discourse representation structure, Definition 28. The order in which
the referents are closed is immaterial to the interpretation. -/
noncomputable def _root_.DRT.DRS.toDPL : DRS L V → Formula L V
  | ⟨U, cs⟩ => exs U.toList (conjs (DRT.Condition.toDPLList cs))
/-- The translation of a condition, Definition 28. -/
noncomputable def _root_.DRT.Condition.toDPL : Condition L V → Formula L V
  | .atom a => rel a.rel (Language.Term.var ∘ a.args)
  | .eq a b => .var a ≐ .var b
  | .neg K => ¬ᵈ(DRT.DRS.toDPL K)
  | .imp a c => DRT.DRS.toDPL a ⟿ DRT.DRS.toDPL c
  | .dis l r => DRT.DRS.toDPL l ⋎ DRT.DRS.toDPL r
/-- The translations of a list of conditions. -/
noncomputable def _root_.DRT.Condition.toDPLList : List (Condition L V) → List (Formula L V)
  | [] => []
  | c :: cs => DRT.Condition.toDPL c :: DRT.Condition.toDPLList cs
end

@[simp] theorem _root_.DRT.Condition.toDPLList_eq_map (cs : List (Condition L V)) :
    DRT.Condition.toDPLList cs = cs.map DRT.Condition.toDPL := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [DRT.Condition.toDPLList, ih]

theorem _root_.DRT.DRS.toDPL_eq (K : DRS L V) :
    K.toDPL = exs K.referents.toList (conjs (K.conditions.map DRT.Condition.toDPL)) := by
  cases K; simp [DRT.DRS.toDPL]

theorem _root_.DRT.Condition.toDPL_atom (a : Language.Atom L V) :
    (Condition.atom a).toDPL = rel a.rel (Language.Term.var ∘ a.args) := rfl

theorem _root_.DRT.Condition.toDPL_eq (a b : V) :
    (Condition.eq a b : Condition L V).toDPL = .var a ≐ .var b := rfl

theorem _root_.DRT.Condition.toDPL_neg (K : DRS L V) :
    (Condition.neg K).toDPL = ¬ᵈK.toDPL := rfl

theorem _root_.DRT.Condition.toDPL_imp (a c : DRS L V) :
    (Condition.imp a c).toDPL = a.toDPL ⟿ c.toDPL := rfl

theorem _root_.DRT.Condition.toDPL_dis (l r : DRS L V) :
    (Condition.dis l r).toDPL = l.toDPL ⋎ r.toDPL := rfl

variable [DecidableEq V] (M : Type x) [L.Structure M]

private theorem eval_toDPL_of_conditions (K : DRS L V)
    (h : ∀ c ∈ K.conditions, c.toDPL.eval M = test {f : V → M | VerifiesConditionTotal f c}) :
    K.toDPL.eval M = K.toRel := by
  ext ⟨g, k⟩
  rw [DRS.toDPL_eq, mem_eval_exs, eval_conjs_map M _ _ _ h]
  simp only [mem_test, Finset.mem_toList, DRS.toRel_iff, verifiesTotal_iff, Set.mem_ofPred_eq]
  exact ⟨fun ⟨_, hk, rfl, hv⟩ ↦ ⟨hk, hv⟩, fun ⟨hk, hv⟩ ↦ ⟨k, hk, rfl, hv⟩⟩

/-- The translation of a condition is the test of its verification (Fact 25 for conditions). -/
theorem _root_.DRT.Condition.eval_toDPL (c : Condition L V) :
    c.toDPL.eval M = test {f : V → M | VerifiesConditionTotal f c} := by
  induction c with
  | atom a =>
    rw [Condition.toDPL_atom, eval_rel]
    exact congrArg test (Set.ext fun f ↦ by simp [Function.comp_def, Language.Atom.Realize])
  | eq a b =>
    rw [Condition.toDPL_eq, eval_equal]
    exact congrArg test (Set.ext fun f ↦ by simp)
  | neg K ih =>
    rw [Condition.toDPL_neg, eval_neg, eval_toDPL_of_conditions M K ih]
    exact congrArg test (Set.ext fun f ↦ (verifies_neg_toRel K f).symm)
  | imp a c iha ihc =>
    rw [Condition.toDPL_imp, eval_imp, eval_toDPL_of_conditions M a iha,
      eval_toDPL_of_conditions M c ihc]
    exact congrArg test (Set.ext fun f ↦ (verifies_imp_toRel a c f).symm)
  | dis l r ihl ihr =>
    rw [Condition.toDPL_dis, eval_disj, eval_toDPL_of_conditions M l ihl,
      eval_toDPL_of_conditions M r ihr]
    exact congrArg test (Set.ext fun f ↦ (verifies_dis_toRel l r f).symm)

/-- The translation of a discourse representation structure denotes its box relation (Fact 25
for boxes). -/
theorem _root_.DRT.DRS.eval_toDPL (K : DRS L V) : K.toDPL.eval M = K.toRel :=
  eval_toDPL_of_conditions M K fun c _ ↦ c.eval_toDPL M

end DRT

end GroenendijkStokhof1991
