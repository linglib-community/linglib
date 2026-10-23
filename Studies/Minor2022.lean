module

public import Linglib.Data.Examples.Minor2022
public import Linglib.Semantics.Dynamic.RegisterStructure
public import Linglib.Semantics.Exhaustification.Excluder
public import Linglib.Semantics.Plurality.Cumulativity
public import Mathlib.Data.Set.Card

/-!
# Minor (2022): Dependent plurals and three levels of multiplicity

Minor analyses dependent plurals in a modified Plural Compositional DRT, where a state is a set of
assignments. A dref's value at an assignment can be a sum, the dref can take several values across
a state, and several values across states. The singular requires atomic values that are all the
same, the plural is vacuous, and a bare plural's multiplicity is Exh's negation of the singular.
Numerals count atoms at every assignment. Floating *all* splits a sum into its atoms across the
assignments of one state and floating *each* across singleton states, so *The girls were all
wearing hats* holds when each girl wore one hat and the hats differ, while *The girls were each
wearing hats* and *All the girls were wearing several hats* need more than one hat per girl.

## Main definitions

* `Minor2022.intro`: dref introduction (60), the strict lift of random assignment.
* `Minor2022.atomic`, `Minor2022.unique`, `Minor2022.cardinal`: the conditions (75), (77) and (78),
  each a property of the values of a dref across the state.
* `Minor2022.split`, `Minor2022.dist`, `Minor2022.distW`, `Minor2022.distS`: the split (90), the
  distributivity operator (94), and weak and strong distributivity (93).
* `Minor2022.sentence`: a subject over a distributivity operator over a verb and its object.

## Main results

* `Minor2022.singleton_mem_cumul_randomAssign_pair`: cumulative dref introduction splits an
  assignment where (60) cannot (fn. 28).
* `Minor2022.mem_atomic_inter_unique_iff`: the singular is atomicity of the sum of the values
  (§5.1).
* `Minor2022.acrossModels_ssubset_iff`: strict inclusion across models is Generalized Strength
  (89), the pointwise order on meanings.
* `Minor2022.exh_vp`: Exh with Generalized Strength (89) negates the singular alternative (115).
* `Minor2022.split_split`, `Minor2022.distW_distW`, `Minor2022.distW_distS`,
  `Minor2022.distS_distW`: the idempotence (92) and the stacking equivalences (98a), (98c), (98d).
* `Minor2022.cumulative_iff`, `Minor2022.dependent_iff`, `Minor2022.distW_cardinal_iff`,
  `Minor2022.distS_bare_iff`: the truth conditions (116), (129), (148) and (170).
* `Minor2022.singleton_mem_dom_distW_test_iff`: a singular restrictor under weak distributivity
  leaves the sum at most one atomic part, the global atomicity of §6.4.3.
* `Minor2022.judgments`: in the context of the girl-and-hat examples, the analysis predicts the
  judgments of (3), (4), (11a) and (13).

## Implementation notes

* Assignments come from any register structure and values from any partial order, whose atoms are
  `Mereology.Atom`. The examples take finite sets of atoms, whose sum is union.
* The event dref of event closure (72) is folded into a verb relating the values of the agent and
  the theme: in every derivation formalized here it is introduced together with the object.
* A model fixes the object noun and the verb. A meaning varying with the model is read as a set of
  model–input–output triples (`acrossModels`), whose strict inclusion is Generalized Strength
  (89), and Exh is `Exhaustification.exh` there.
* Exh is placed above the VP, the first site the paper considers for each sentence.
* *The girls* is the sum of the girls of the model, the value the maximization of fn. 45 (i)
  returns there. *All the girls* in (3) is weak distributivity over *the girls*, the
  distributivity a plural determiner places over its nuclear scope (108), without its two
  maximized drefs.

## TODO

* Quantificational determiners (105)–(109) with maximization (106), the conservativity argument
  for the Ban on Singular Licensors ((186)–(195)) beyond its global-atomicity lemma, modified
  numerals (§6.3.2, §6.3.3), the other sites of Exh, the discourse rule (200), and the
  Schein–Kratzer sentences of Appendix 2.
* The stacking equivalence (98b), which needs `dist (dist D) = dist D`.

## References

* [minor-2022]
* [brasoveanu-2008]
* [zweig-2009]
-/

@[expose] public section

namespace Minor2022

open DynamicSemantics DynamicSemantics.Update SetRel RegisterStructure Mereology
open scoped DynamicSemantics.Update

variable {R S E : Type*} [RegisterStructure R S E] {u u' : R} {I J : Set S} {i k : S}

/-! ### Dref introduction (§4.3) -/

/-- New dref introduction `[u]` (60) moves each assignment to a single `u`-variant. -/
def intro (u : R) : Update (Set S) := strictLift (randomAssign u)

theorem singleton_mem_intro_iff : {i} ~[intro u] J ↔ ∃ x, J = {extend i u x} := by
  simp only [intro, singleton_mem_strictLift_iff, mem_randomAssign]
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨_, ⟨x, rfl⟩, rfl⟩

/-- Introduction never enlarges a state (fn. 28). -/
theorem encard_le_of_mem_intro (h : I ~[intro u] J) : J.encard ≤ I.encard := by
  obtain ⟨f, -, rfl⟩ := h
  exact Set.encard_image_le f I

/-- The cumulative dref introduction of [brasoveanu-2008], (i) of fn. 28, can split one
assignment into two, which (60) cannot. -/
theorem singleton_mem_cumul_randomAssign_pair {x y : E} (hxy : x ≠ y) :
    {i} ~[cumul (randomAssign u)] {extend i u x, extend i u y} ∧
      ¬ {i} ~[intro u] {extend i u x, extend i u y} := by
  refine ⟨⟨fun k hk ↦ ⟨_, Set.mem_insert _ _, ?_⟩, fun j hj ↦ ⟨i, rfl, ?_⟩⟩, fun h ↦ ?_⟩
  · rw [Set.mem_singleton_iff.1 hk]
    exact ⟨x, rfl⟩
  · obtain rfl | rfl := hj
    exacts [⟨x, rfl⟩, ⟨y, rfl⟩]
  · obtain ⟨z, hz⟩ := singleton_mem_intro_iff.1 h
    have hx : extend i u x ∈ ({extend i u z} : Set S) := hz ▸ Set.mem_insert _ _
    have hy : extend i u y ∈ ({extend i u z} : Set S) := hz ▸ Set.mem_insert_of_mem _ rfl
    have hxy' : extend i u x = extend i u y :=
      (Set.mem_singleton_iff.1 hx).trans (Set.mem_singleton_iff.1 hy).symm
    exact hxy (by simpa only [val_extend_self] using congrArg (val u) hxy')

/-! ### Lexical relations (§4.4) -/

/-- A lexical relation `R{u}` (63) holds of a state when `u` has values there and they satisfy
it. -/
def lex (P : E → Prop) (u : R) : Condition (Set S) :=
  {I | (val u '' I).Nonempty ∧ val u '' I ⊆ {x | P x}}

/-- A two-place lexical relation `R{u, u'}` (63) holds of a state when the pairs of values of `u`
and `u'` exist and satisfy it. -/
def lex₂ (P : E → E → Prop) (u u' : R) : Condition (Set S) :=
  {I | ((fun i ↦ (val u i, val u' i)) '' I).Nonempty ∧
    (fun i ↦ (val u i, val u' i)) '' I ⊆ {p | P p.1 p.2}}

/-! ### The distributivity operator (94) -/

/-- The distributivity operator `dist` of [brasoveanu-2008] (94) updates the singleton state of
every assignment separately and glues the outputs. -/
def dist (D : Update (Set S)) : Update (Set S) :=
  {(I, J) | ∃ ρ : SetRel S (Set S), ρ.Nonempty ∧ ρ.dom = I ∧ ⋃₀ ρ.cod = J ∧
    ∀ p ∈ ρ, ({p.1}, p.2) ∈ D}

theorem dom_dist (D : Update (Set S)) :
    (dist D).dom = {I | I.Nonempty ∧ ∀ k ∈ I, {k} ∈ D.dom} := by
  ext I
  constructor
  · rintro ⟨J, ρ, ⟨⟨k, L⟩, hp⟩, rfl, -, hD⟩
    exact ⟨⟨k, L, hp⟩, fun k ⟨L, hk⟩ ↦ ⟨L, hD (k, L) hk⟩⟩
  · rintro ⟨⟨k, hk⟩, h⟩
    obtain ⟨L, hL⟩ := h k hk
    refine ⟨_, {p | p.1 ∈ I ∧ ({p.1}, p.2) ∈ D}, ⟨(k, L), hk, hL⟩, ?_, rfl, fun p hp ↦ hp.2⟩
    ext j
    exact ⟨fun ⟨_, hj, _⟩ ↦ hj, fun hj ↦ let ⟨L, hL⟩ := h j hj; ⟨L, hj, hL⟩⟩

/-! ### Models, Exh, and the VP (§5.3, §6) -/

/-- A model fixes the object noun and the verb of the derivations. -/
structure Model (E : Type*) where
  /-- The object noun, *boxes* or *hats*. -/
  noun : E → Prop
  /-- The verb, relating the value of its agent to that of its theme, its event folded in. -/
  verb : E → E → Prop

variable (u u') in
/-- The VP `[u']; [noun{u'}]; [verb{u, u'}]` of a verb and its object after event closure
((112), (134)). -/
def vp (M : Model E) : Update (Set S) := intro u' ○ test (lex M.noun u' ∩ lex₂ M.verb u u')

/-- A meaning that varies with the model, read as a set of model–input–output triples. Strict
inclusion of these sets is Generalized Strength (89), entailment in every model with the converse
failing in some. -/
def acrossModels {M : Type*} (D : M → Update (Set S)) : Set (M × (Set S × Set S)) :=
  {w | w.2 ∈ D w.1}

theorem acrossModels_subset_iff {M : Type*} {D D' : M → Update (Set S)} :
    acrossModels D ⊆ acrossModels D' ↔ D ≤ D' :=
  ⟨fun h m p hp ↦ h (a := (m, p)) hp, fun h w hw ↦ h w.1 hw⟩

/-- Strict inclusion across models is Generalized Strength (89), the pointwise order on meanings
as functions of the model. -/
theorem acrossModels_ssubset_iff {M : Type*} {D D' : M → Update (Set S)} :
    acrossModels D ⊂ acrossModels D' ↔ D < D' := by
  rw [Set.ssubset_def, acrossModels_subset_iff, acrossModels_subset_iff, lt_iff_le_not_ge]

/-- Adding a test that fails in some model gives a stronger meaning. -/
theorem comp_test_lt {M : Type*} {D : M → Update (Set S)} {C : Condition (Set S)} (m : M)
    (h : ¬ D m ⊆ D m ○ test C) : (fun m ↦ D m ○ test C) < D :=
  lt_of_le_not_ge (fun _ _ hp ↦ (mem_comp_test.1 hp).1) fun h' ↦ h (h' m)

/-- Exh against a stronger alternative that adds the test `C` adds the negated test. -/
theorem exh_acrossModels_comp_test {M : Type*} {D : M → Update (Set S)} {C : Condition (Set S)}
    (h : (fun m ↦ D m ○ test C) < D) :
    Exhaustification.exh {acrossModels fun m ↦ D m ○ test C} (acrossModels D) =
      acrossModels fun m ↦ D m ○ test Cᶜ := by
  have hns := (acrossModels_ssubset_iff.2 h).2
  ext ⟨m, I, J⟩
  simp only [Exhaustification.mem_exh, Set.mem_singleton_iff, forall_eq, acrossModels,
    Set.mem_ofPred_eq, mem_comp_test, Set.mem_compl_iff]
  exact ⟨fun ⟨hD, hC⟩ ↦ ⟨hD, fun hc ↦ hns (hC ⟨hD, hc⟩)⟩,
    fun ⟨hD, hc⟩ ↦ ⟨hD, fun h' ↦ absurd h'.2 hc⟩⟩

variable (u u') in
/-- A sentence whose subject's value satisfies `P`, over the distributivity operator `d` (`id` for
none) over a verb whose object meets `C`. -/
def sentence (P : E → Prop) (d : Update (Set S) → Update (Set S)) (M : Model E)
    (C : Condition (Set S)) : Update (Set S) :=
  intro u ○ test (lex P u) ○ d (vp u u' M ○ test C)

variable {P : E → Prop} {M : Model E} {C : Condition (Set S)} {D : Update (Set S)}

theorem singleton_mem_lex_iff {j : S} : {j} ∈ lex P u ↔ P (val u j) := by
  simp [lex]

theorem singleton_mem_lex₂_iff {P : E → E → Prop} {j : S} :
    {j} ∈ lex₂ P u u' ↔ P (val u j) (val u' j) := by
  simp [lex₂]

theorem singleton_mem_dom_intro_comp_iff :
    {i} ∈ (intro u ○ test C ○ D).dom ↔ ∃ x, {extend i u x} ∈ C ∧ {extend i u x} ∈ D.dom := by
  simp only [mem_dom, mem_comp, singleton_mem_intro_iff, mem_test_iff_left]
  constructor
  · rintro ⟨out, _, ⟨_, ⟨x, rfl⟩, rfl, hC⟩, hD⟩
    exact ⟨x, hC, out, hD⟩
  · rintro ⟨x, hC, out, hD⟩
    exact ⟨out, _, ⟨_, ⟨x, rfl⟩, rfl, hC⟩, hD⟩

theorem singleton_mem_dom_sentence_iff {d : Update (Set S) → Update (Set S)} :
    {i} ∈ (sentence u u' P d M C).dom ↔
      ∃ x, P x ∧ {extend i u x} ∈ (d (vp u u' M ○ test C)).dom := by
  simp only [sentence, singleton_mem_dom_intro_comp_iff, singleton_mem_lex_iff, val_extend_self]

theorem singleton_mem_dom_vp_iff (huu' : u ≠ u') :
    {k} ∈ (vp u u' M ○ test C).dom ↔
      ∃ y, M.noun y ∧ M.verb (val u k) y ∧ {extend k u' y} ∈ C := by
  simp only [vp, singleton_mem_dom_intro_comp_iff, Set.mem_inter_iff, singleton_mem_lex_iff,
    singleton_mem_lex₂_iff, val_extend_self, val_extend_of_ne _ _ _ _ huu', dom_test, and_assoc]

theorem image_mem_intro_iff {A : Set E} {K : Set S} :
    (extend k u ·) '' A ~[intro u'] K ↔
      ∃ b : E → E, K = (fun a ↦ extend (extend k u a) u' (b a)) '' A := by
  constructor
  · rintro ⟨f, hf, rfl⟩
    refine ⟨fun a ↦ val u' (f (extend k u a)), ?_⟩
    rw [Set.image_image]
    refine Set.image_congr fun a ha ↦ ?_
    obtain ⟨e, he⟩ := hf _ (Set.mem_image_of_mem _ ha)
    simp [he, val_extend_self]
  · rintro ⟨b, rfl⟩
    refine ⟨fun j ↦ extend j u' (b (val u j)), fun j _ ↦ ⟨_, rfl⟩, ?_⟩
    rw [Set.image_image]
    exact Set.image_congr fun a _ ↦ by simp [val_extend_self]

/-! ### Number and cardinality (§5.1) -/

/-- `unique{u}` (75b) holds when `u` takes one value across the state. -/
def unique (u : R) : Condition (Set S) := {I | (val u '' I).Subsingleton}

variable [PartialOrder E]

/-- `atom{u}` (75a) holds when the values of `u` are atoms. -/
def atomic (u : R) : Condition (Set S) := {I | val u '' I ⊆ {a | Atom a}}

/-- A cardinality condition holds when the number of atoms of each value of `u` satisfies `p`,
which is `= n` for the numeral `n` (77) and `> 1` for *several* (78). -/
def cardinal (p : ℕ → Prop) (u : R) : Condition (Set S) :=
  {I | val u '' I ⊆ {x | p (atomCount E x)}}

/-- An exhaustified bare plural (115) requires the values of `u` not to be atomic and unique,
negating the singular. -/
def bare (u : R) : Condition (Set S) := (atomic u ∩ unique u)ᶜ

/-- The singular (74) is state-level atomicity (§5.1): on a nonempty state whose values of `u`
are non-null, atomicity and uniqueness hold exactly when the values sum to an atom. -/
theorem mem_atomic_inter_unique_iff (hI : I.Nonempty) (hu : ∀ i ∈ I, ¬ IsBot (val u i)) :
    I ∈ atomic u ∩ unique u ↔ ∃ a, Atom a ∧ IsLUB (val u '' I) a := by
  refine ⟨fun ⟨hA, hU⟩ ↦ ?_, fun ⟨a, ha, hlub⟩ ↦ ?_⟩
  · obtain ⟨i, hi⟩ := hI
    refine ⟨val u i, hA (Set.mem_image_of_mem _ hi), ?_⟩
    rw [hU.eq_singleton_of_mem (Set.mem_image_of_mem _ hi)]
    exact isLUB_singleton
  · have h : val u '' I ⊆ {a} := by
      rintro _ ⟨i, hi, rfl⟩
      exact ha.eq (hlub.1 (Set.mem_image_of_mem _ hi)) (hu i hi)
    exact ⟨h.trans (Set.singleton_subset_iff.2 ha), Set.subsingleton_singleton.anti h⟩

theorem singleton_mem_atomic_inter_unique_iff : {i} ∈ atomic u ∩ unique u ↔ Atom (val u i) := by
  simp [atomic, unique]

variable (u u') in
/-- Exh above the VP negates the singular alternative (114), which some model separates from the
plural, so a bare plural object gets the condition (115). -/
theorem exh_vp {y : E} (hy : ¬ Atom y) (i : S) :
    Exhaustification.exh {acrossModels fun M : Model E ↦ vp u u' M ○ test (atomic u' ∩ unique u')}
      (acrossModels fun M : Model E ↦ vp u u' M) =
        acrossModels fun M : Model E ↦ vp u u' M ○ test (bare (S := S) u') := by
  refine exh_acrossModels_comp_test (comp_test_lt ⟨fun _ ↦ True, fun _ _ ↦ True⟩ fun h ↦ hy ?_)
  have hp : ({i}, {extend i u' y}) ∈ vp u u' ⟨fun _ ↦ True, fun _ _ ↦ True⟩ :=
    ⟨_, singleton_mem_intro_iff.2 ⟨y, rfl⟩, rfl, by simp [lex, lex₂]⟩
  have := (mem_comp_test.1 (h hp)).2.1
  simpa [atomic, val_extend_self] using this

/-! ### Weak and strong distributivity (§5.4) -/

/-- The split `⟨u⟩` (90) replaces each assignment by the `u`-variants giving `u` each atomic part
of its value. -/
def split (u : R) (I : Set S) : Set S := ⋃ i ∈ I, (extend i u ·) '' atomsBelow (val u i)

theorem mem_split {j : S} :
    j ∈ split u I ↔ ∃ k ∈ I, ∃ a ∈ atomsBelow (val u k), extend k u a = j := by
  simp [split]

theorem split_singleton : split u {i} = (extend i u ·) '' atomsBelow (val u i) := by
  simp [split]

theorem atom_of_mem_split {j : S} (h : j ∈ split u I) : Atom (val u j) := by
  obtain ⟨_, -, a, ha, rfl⟩ := mem_split.1 h
  rw [val_extend_self]
  exact ha.1

theorem image_val_split_singleton : val u '' split u {i} = atomsBelow (val u i) := by
  rw [split_singleton, Set.image_image]
  simp [val_extend_self]

theorem split_singleton_of_atom (h : Atom (val u i)) : split u {i} = {i} := by
  rw [split_singleton, atomsBelow_of_atom h, Set.image_singleton, extend_eq_self]

/-- Splitting twice splits once (92). -/
theorem split_split (u : R) (I : Set S) : split u (split u I) = split u I := by
  refine Set.Subset.antisymm (fun j hj ↦ ?_) fun j hj ↦
    mem_split.2 ⟨j, hj, val u j, ⟨atom_of_mem_split hj, le_rfl⟩, extend_eq_self ..⟩
  obtain ⟨k, hk, a, ha, rfl⟩ := mem_split.1 hj
  rwa [(atom_of_mem_split hk).eq ha.2 ha.1.not_isBot, extend_eq_self]

/-- Weak distributivity `dist_w` (93a) splits, then updates. -/
def distW (u : R) (D : Update (Set S)) : Update (Set S) := (split u).graph ○ D

/-- Strong distributivity `dist_s` (93b) splits, then updates every assignment separately. -/
def distS (u : R) (D : Update (Set S)) : Update (Set S) := (split u).graph ○ dist D

variable {D : Update (Set S)}

theorem mem_distW : I ~[distW u D] J ↔ split u I ~[D] J := by
  simp [distW]

theorem mem_distS : I ~[distS u D] J ↔ split u I ~[dist D] J := by
  simp [distS]

/-- Weak distributivity is idempotent (98a). -/
theorem distW_distW (u : R) (D : Update (Set S)) : distW u (distW u D) = distW u D := by
  ext ⟨I, J⟩
  simp only [mem_distW, split_split]

/-- Weak over strong distributivity is strong distributivity (98c). -/
theorem distW_distS (u : R) (D : Update (Set S)) : distW u (distS u D) = distS u D := by
  ext ⟨I, J⟩
  simp only [mem_distW, mem_distS, split_split]

/-- Strong over weak distributivity is strong distributivity (98d). -/
theorem distS_distW (u : R) (D : Update (Set S)) : distS u (distW u D) = distS u D := by
  ext ⟨I, J⟩
  simp only [mem_distS]
  have key {ρ : SetRel S (Set S)} (hdom : ρ.dom = split u I) {p : S × Set S} (hp : p ∈ ρ) :
      ({p.1}, p.2) ∈ distW u D ↔ ({p.1}, p.2) ∈ D := by
    have hp' : p.1 ∈ split u I := hdom ▸ (⟨p.2, hp⟩ : p.1 ∈ ρ.dom)
    rw [mem_distW, split_singleton_of_atom (atom_of_mem_split hp')]
  exact ⟨fun ⟨ρ, hne, hdom, hcod, hD⟩ ↦ ⟨ρ, hne, hdom, hcod, fun p hp ↦ (key hdom hp).1 (hD p hp)⟩,
    fun ⟨ρ, hne, hdom, hcod, hD⟩ ↦ ⟨ρ, hne, hdom, hcod, fun p hp ↦ (key hdom hp).2 (hD p hp)⟩⟩

theorem singleton_mem_dom_distS_iff :
    {k} ∈ (distS u D).dom ↔
      (atomsBelow (val u k)).Nonempty ∧ ∀ a ∈ atomsBelow (val u k), {extend k u a} ∈ D.dom := by
  simp only [mem_dom, mem_distS, ← mem_dom (R := dist D), dom_dist, Set.mem_ofPred_eq,
    split_singleton, Set.image_nonempty, Set.forall_mem_image]

/-- A singular restrictor under weak distributivity leaves the sum at most one atomic part, the
global atomicity that rules out a singular quantifier distributing weakly (§6.4.3). -/
theorem singleton_mem_dom_distW_test_iff :
    {k} ∈ (distW u (test (atomic u ∩ unique u))).dom ↔ (atomsBelow (val u k)).Subsingleton := by
  simp only [mem_dom, mem_distW, mem_test_iff_left, exists_eq_left', Set.mem_inter_iff, atomic,
    unique, Set.mem_ofPred_eq, image_val_split_singleton]
  exact ⟨And.right, fun h ↦ ⟨fun _ ha ↦ ha.1, h⟩⟩

theorem singleton_mem_dom_distS_test_iff :
    {k} ∈ (distS u (test (atomic u ∩ unique u))).dom ↔ (atomsBelow (val u k)).Nonempty := by
  rw [singleton_mem_dom_distS_iff]
  refine ⟨And.left, fun h ↦ ⟨h, fun a ha ↦ ⟨_, rfl, ?_⟩⟩⟩
  rw [singleton_mem_atomic_inter_unique_iff, val_extend_self]
  exact ha.1

/-! ### Truth conditions (§6) -/

theorem singleton_mem_dom_distW_intro_iff :
    {k} ∈ (distW u (intro u' ○ test C ○ D)).dom ↔
      ∃ b : E → E, (fun a ↦ extend (extend k u a) u' (b a)) '' atomsBelow (val u k) ∈ C ∧
        (fun a ↦ extend (extend k u a) u' (b a)) '' atomsBelow (val u k) ∈ D.dom := by
  simp only [mem_dom, mem_distW, mem_comp, split_singleton, image_mem_intro_iff,
    mem_test_iff_left]
  constructor
  · rintro ⟨out, _, ⟨_, ⟨b, rfl⟩, rfl, hC⟩, hD⟩
    exact ⟨b, hC, out, hD⟩
  · rintro ⟨b, hC, out, hD⟩
    exact ⟨out, _, ⟨_, ⟨b, rfl⟩, rfl, hC⟩, hD⟩

theorem singleton_mem_dom_distW_iff (huu' : u ≠ u') :
    {k} ∈ (distW u (vp u u' M ○ test C)).dom ↔
      ∃ b : E → E, (atomsBelow (val u k)).Nonempty ∧
        (∀ a ∈ atomsBelow (val u k), M.noun (b a) ∧ M.verb a (b a)) ∧
        (fun a ↦ extend (extend k u a) u' (b a)) '' atomsBelow (val u k) ∈ C := by
  rw [vp, singleton_mem_dom_distW_intro_iff]
  simp only [lex, lex₂, Set.mem_inter_iff, Set.mem_ofPred_eq, dom_test, Set.image_nonempty,
    Set.subset_def, Set.forall_mem_image, val_extend_self, val_extend_of_ne _ _ _ _ huu']
  exact exists_congr fun b ↦ ⟨fun ⟨⟨⟨hne, hn⟩, _, hv⟩, hC⟩ ↦ ⟨hne, fun a ha ↦ ⟨hn ha, hv ha⟩, hC⟩,
    fun ⟨hne, h, hC⟩ ↦ ⟨⟨⟨hne, fun a ha ↦ (h a ha).1⟩, hne, fun a ha ↦ (h a ha).2⟩, hC⟩⟩

variable (P M)

/-- On the cumulative reading (116) of *Three students carried boxes*, a sum satisfying the
subject carried a non-atomic sum of boxes. -/
theorem cumulative_iff (huu' : u ≠ u') :
    {i} ∈ (sentence u u' P id M (bare u')).dom ↔
      ∃ x, P x ∧ ∃ y, M.noun y ∧ M.verb x y ∧ ¬ Atom y := by
  simp only [singleton_mem_dom_sentence_iff, id, singleton_mem_dom_vp_iff huu', bare,
    Set.mem_compl_iff, singleton_mem_atomic_inter_unique_iff, val_extend_self]

/-- Without a distributivity operator a cardinality condition counts the whole object, as on the
cumulative reading of *The girls were wearing several hats* (4). -/
theorem cumulative_cardinal_iff (huu' : u ≠ u') (p : ℕ → Prop) :
    {i} ∈ (sentence u u' P id M (cardinal p u')).dom ↔
      ∃ x, P x ∧ ∃ y, M.noun y ∧ M.verb x y ∧ p (atomCount E y) := by
  rw [singleton_mem_dom_sentence_iff]
  simp only [id, singleton_mem_dom_vp_iff huu', val_extend_self, cardinal, Set.image_singleton,
    Set.singleton_subset_iff, Set.mem_ofPred_eq]

/-- On the dependent plural reading (129) of *Three students all carried boxes*, every atomic part
of the subject carried a sum of boxes, and the sums are not one and the same atom. -/
theorem dependent_iff (huu' : u ≠ u') :
    {i} ∈ (sentence u u' P (distW u) M (bare u')).dom ↔
      ∃ x, P x ∧ ∃ b : E → E, (atomsBelow x).Nonempty ∧
        (∀ a ∈ atomsBelow x, M.noun (b a) ∧ M.verb a (b a)) ∧
        ¬ ((∀ a ∈ atomsBelow x, Atom (b a)) ∧ (b '' atomsBelow x).Subsingleton) := by
  rw [singleton_mem_dom_sentence_iff]
  refine exists_congr fun x ↦ and_congr_right fun _ ↦ ?_
  rw [singleton_mem_dom_distW_iff huu', val_extend_self]
  refine exists_congr fun b ↦ and_congr_right fun _ ↦ and_congr_right fun _ ↦ ?_
  simp only [bare, atomic, unique, Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_ofPred_eq,
    Set.image_image, Set.image_subset_iff, val_extend_self]
  simp [Set.subset_def, val_extend_self]

/-- Under weak distributivity a cardinality condition counts at every atomic part of the
subject (148), the Ban on Numerals. -/
theorem distW_cardinal_iff (huu' : u ≠ u') (p : ℕ → Prop) :
    {i} ∈ (sentence u u' P (distW u) M (cardinal p u')).dom ↔
      ∃ x, P x ∧ (atomsBelow x).Nonempty ∧
        ∀ a ∈ atomsBelow x, ∃ y, M.noun y ∧ M.verb a y ∧ p (atomCount E y) := by
  rw [singleton_mem_dom_sentence_iff]
  refine exists_congr fun x ↦ and_congr_right fun _ ↦ ?_
  rw [singleton_mem_dom_distW_iff huu', val_extend_self]
  simp only [cardinal, Set.mem_ofPred_eq, Set.image_subset_iff]
  constructor
  · rintro ⟨b, hne, h, hp⟩
    exact ⟨hne, fun a ha ↦ ⟨b a, (h a ha).1, (h a ha).2, by simpa [val_extend_self] using hp ha⟩⟩
  · rintro ⟨hne, h⟩
    choose! b hb using h
    exact ⟨b, hne, fun a ha ↦ ⟨(hb a ha).1, (hb a ha).2.1⟩,
      fun a ha ↦ by simpa [val_extend_self] using (hb a ha).2.2⟩

/-- Under strong distributivity a bare plural is non-atomic at every atomic part of the subject
(170), the Ban on Singular Licensors. -/
theorem distS_bare_iff (huu' : u ≠ u') :
    {i} ∈ (sentence u u' P (distS u) M (bare u')).dom ↔
      ∃ x, P x ∧ (atomsBelow x).Nonempty ∧
        ∀ a ∈ atomsBelow x, ∃ y, M.noun y ∧ M.verb a y ∧ ¬ Atom y := by
  simp only [singleton_mem_dom_sentence_iff, singleton_mem_dom_distS_iff, val_extend_self,
    singleton_mem_dom_vp_iff huu', bare, Set.mem_compl_iff, singleton_mem_atomic_inter_unique_iff]

/-! ### The girls and their hats (§1, §2)

The examples (3), (4), (11a) and (13) are judged in a context where each girl wore a single hat
and no two girls the same hat. -/

/-- Three girls `0`, `1`, `2` and three hats `3`, `4`, `5`. -/
abbrev Thing := Fin 6

/-- The drefs of the subject and of the object. -/
inductive Dref where
  | subj
  | obj
  deriving DecidableEq

/-- Each girl wears her own hat, `0` the hat `3`, `1` the hat `4` and `2` the hat `5`. -/
def Wears (a b : Thing) : Prop := a.val < 3 ∧ b.val = a.val + 3

instance : DecidableRel Wears := fun _ _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- In the model of the context the object is *hats*, and *wear* is the cumulation of each
girl's wearing her own hat. -/
def hats : Model (Finset Thing) where
  noun y := y.Nonempty ∧ y ⊆ {3, 4, 5}
  verb := Plurality.Cumulativity.Cumulation (Relation.Map Wears ({·}) ({·}))

/-- *The girls*, whose value is the sum of the girls. -/
def theGirls (x : Finset Thing) : Prop := x = {0, 1, 2}

theorem hats_verb_iff {x y : Finset Thing} :
    hats.verb x y ↔ x.Nonempty ∧ (∀ a ∈ x, ∃ b ∈ y, Wears a b) ∧ ∀ b ∈ y, ∃ a ∈ x, Wears a b := by
  simp [hats, Plurality.Cumulativity.cumulation_map_singleton, Set.LiftRel]

theorem exists_eq_singleton_of_verb {g : Thing} {y : Finset Thing} (h : hats.verb {g} y) :
    ∃ b, y = {b} := by
  rw [hats_verb_iff] at h
  revert g y
  decide

variable (i : Dref → Finset Thing)

/-- In the context of the examples the analysis predicts their judgments. *The girls were
wearing several hats* (4) and *The girls were all wearing hats* (11a) are true, *All the girls
were wearing several hats* (3) and *The girls were each wearing hats* (13) false. They fill four
cells of Table 2, showing cumulation, the Ban on Numerals, co-distributivity with the Multiplicity
Condition, and the Ban on Singular Licensors. -/
theorem judgments :
    (Examples.ex_4.judgment = .acceptable ↔
      {i} ∈ (sentence Dref.subj Dref.obj theGirls id hats (cardinal (1 < ·) Dref.obj)).dom) ∧
    (Examples.ex_3.judgment = .acceptable ↔
      {i} ∈ (sentence Dref.subj Dref.obj theGirls (distW Dref.subj) hats
        (cardinal (1 < ·) Dref.obj)).dom) ∧
    (Examples.ex_11a.judgment = .acceptable ↔
      {i} ∈ (sentence Dref.subj Dref.obj theGirls (distW Dref.subj) hats (bare Dref.obj)).dom) ∧
    (Examples.ex_13.judgment = .acceptable ↔
      {i} ∈ (sentence Dref.subj Dref.obj theGirls (distS Dref.subj) hats (bare Dref.obj)).dom) := by
  have hne : Dref.subj ≠ Dref.obj := nofun
  have h0 : ({0} : Finset Thing) ∈ atomsBelow ({0, 1, 2} : Finset Thing) := by
    rw [atomsBelow_finset]
    exact ⟨0, by decide, rfl⟩
  refine ⟨iff_of_true rfl ?_, iff_of_false (by decide) ?_, iff_of_true rfl ?_,
    iff_of_false (by decide) ?_⟩
  · rw [cumulative_cardinal_iff _ _ hne]
    refine ⟨_, rfl, {3, 4, 5}, ⟨by decide, by decide⟩, hats_verb_iff.2 (by decide), ?_⟩
    rw [atomCount_finset]
    decide
  · rw [distW_cardinal_iff _ _ hne]
    rintro ⟨_, rfl, -, h⟩
    obtain ⟨y, -, hy, hc⟩ := h _ h0
    obtain ⟨b, rfl⟩ := exists_eq_singleton_of_verb hy
    simp [atomCount_finset] at hc
  · rw [dependent_iff _ _ hne]
    refine ⟨_, rfl, fun a ↦ a.image (· + 3), ⟨_, h0⟩, ?_, fun hs ↦ ?_⟩
    · rw [atomsBelow_finset, Set.forall_mem_image]
      intro g hg
      refine ⟨⟨by simp, ?_⟩, hats_verb_iff.2 ?_⟩ <;> revert g <;> decide
    · have h1 : ({1} : Finset Thing) ∈ atomsBelow ({0, 1, 2} : Finset Thing) := by
        rw [atomsBelow_finset]
        exact ⟨1, by decide, rfl⟩
      have := hs.2 (Set.mem_image_of_mem _ h0) (Set.mem_image_of_mem _ h1)
      revert this
      decide
  · rw [distS_bare_iff _ _ hne]
    rintro ⟨_, rfl, -, h⟩
    obtain ⟨y, -, hy, hat⟩ := h _ h0
    obtain ⟨b, rfl⟩ := exists_eq_singleton_of_verb hy
    exact hat (atom_iff_isAtom.2 (Finset.isAtom_singleton b))

end Minor2022
