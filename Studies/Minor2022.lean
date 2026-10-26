module

public import Linglib.Data.Examples.Minor2022
public import Linglib.Semantics.Dynamic.PCDRT
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
* `Minor2022.split`, `Minor2022.distW`, `Minor2022.distS`: the split (90), and weak and strong
  distributivity (93) over the distributivity operator (94), `Update.dist`.
* `Minor2022.sentence`: a subject over a distributivity operator over a verb and its object.
* `Minor2022.max`, `Minor2022.detPl`, `Minor2022.detSg`: maximization over assignments (106) and the
  plural and singular quantificational determiners (108), (109).

## Main results

* `Minor2022.exh_vp`: Exh with Generalized Strength (89) negates the singular alternative (115).
* `Minor2022.dependent_iff`: the truth conditions (129) of a bare plural under floating *all*.
* `Minor2022.detPl_most_iff`: the truth conditions of *most* with a bare plural object (131).
* `Minor2022.detSg_every_iff`: the truth conditions of *every* with a bare plural object (174).
* `Minor2022.judgments`: in the context of the girl-and-hat examples, the analysis predicts the
  judgments of (3), (4), (10b), (11a), (12b) and (13).

## Implementation notes

* Assignments come from any register structure and values from any partial order, whose atoms are
  `Mereology.Atom`. The examples take finite sets of atoms, whose sum is union.
* Every register content is an individual, so the lexical relations (63) are Plural CDRT's atomic
  conditions `PCDRT.atom` at the identity `PCDRT.ValueEmbedding`.
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

* The conservativity argument for the Ban on Singular Licensors ((186)–(195)) beyond its
  global-atomicity lemma, modified numerals (§6.3.2, §6.3.3), the other sites of Exh, the
  discourse rule (200), and the Schein–Kratzer sentences of Appendix 2.

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

/-- A lexical relation `R{u}` (63) is Plural CDRT's atomic condition, at registers whose every
content is an individual. -/
def lex (P : E → Prop) (u : R) : Condition (Set S) := PCDRT.atom (fun x ↦ P (x 0)) ![u]

/-- A two-place lexical relation `R{u, u'}` (63). -/
def lex₂ (P : E → E → Prop) (u u' : R) : Condition (Set S) :=
  PCDRT.atom (fun x ↦ P (x 0) (x 1)) ![u, u']

theorem mem_lex {P : E → Prop} :
    I ∈ lex P u ↔ (val u '' I).Nonempty ∧ val u '' I ⊆ {x | P x} := by
  rw [lex, PCDRT.mem_atom_vec1, PCDRT.value_eq_image]
  rfl

theorem mem_lex₂ {P : E → E → Prop} : I ∈ lex₂ P u u' ↔
    ((fun i ↦ (val u i, val u' i)) '' I).Nonempty ∧
      (fun i ↦ (val u i, val u' i)) '' I ⊆ {p | P p.1 p.2} := by
  rw [lex₂, PCDRT.mem_atom_vec2, PCDRT.dep_eq_image]
  rfl

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
  simp [mem_lex]

theorem singleton_mem_lex₂_iff {P : E → E → Prop} {j : S} :
    {j} ∈ lex₂ P u u' ↔ P (val u j) (val u' j) := by
  simp [mem_lex₂]

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

/-- On a nonempty state with non-null values of `u`, atomicity and uniqueness hold iff the values
sum to an atom, the singular (74) (§5.1). -/
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
    ⟨_, singleton_mem_intro_iff.2 ⟨y, rfl⟩, rfl, by simp [mem_lex, mem_lex₂]⟩
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

/-- Strong distributivity is idempotent (98b): on a split state every row is its own split, and
`Update.dist` is idempotent. -/
theorem distS_distS (u : R) (D : Update (Set S)) : distS u (distS u D) = distS u D := by
  ext ⟨I, J⟩
  simp only [mem_distS]
  rw [← dist_dist D]
  have key {ρ : SetRel S (Set S)} (hdom : ρ.dom = split u I) {p : S × Set S} (hp : p ∈ ρ) :
      ({p.1}, p.2) ∈ distS u D ↔ ({p.1}, p.2) ∈ dist D := by
    have hp' : p.1 ∈ split u I := hdom ▸ (⟨p.2, hp⟩ : p.1 ∈ ρ.dom)
    rw [mem_distS, split_singleton_of_atom (atom_of_mem_split hp')]
  exact ⟨fun ⟨ρ, hne, hdom, hcod, hD⟩ ↦ ⟨ρ, hne, hdom, hcod, fun p hp ↦ (key hdom hp).1 (hD p hp)⟩,
    fun ⟨ρ, hne, hdom, hcod, hD⟩ ↦ ⟨ρ, hne, hdom, hcod, fun p hp ↦ (key hdom hp).2 (hD p hp)⟩⟩

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

/-- A singular restrictor under weak distributivity leaves the sum at most one atomic part (§6.4.3).
-/
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
  simp only [mem_lex, mem_lex₂, Set.mem_inter_iff, Set.mem_ofPred_eq, dom_test, Set.image_nonempty,
    Set.subset_def, Set.forall_mem_image, val_extend_self, val_extend_of_ne _ _ _ _ huu']
  exact exists_congr fun b ↦ ⟨fun ⟨⟨⟨hne, hn⟩, _, hv⟩, hC⟩ ↦ ⟨hne, fun a ha ↦ ⟨hn ha, hv ha⟩, hC⟩,
    fun ⟨hne, h, hC⟩ ↦ ⟨⟨⟨hne, fun a ha ↦ (h a ha).1⟩, hne, fun a ha ↦ (h a ha).2⟩, hC⟩⟩

/-- Over a split state, the bare plural condition says the object is not one and the same atom at
every atomic part of the subject. -/
theorem image_mem_bare_iff {u u' : R} {k : S} {b : E → E} :
    (fun a ↦ extend (extend k u a) u' (b a)) '' atomsBelow (val u k) ∈ bare u' ↔
      ¬((∀ a ∈ atomsBelow (val u k), Atom (b a)) ∧ (b '' atomsBelow (val u k)).Subsingleton) := by
  simp only [bare, atomic, unique, Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_ofPred_eq,
    Set.image_image, Set.image_subset_iff, val_extend_self]
  simp [Set.subset_def, val_extend_self]

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

/-- On the dependent plural reading (129) of *Three students all carried boxes*, each student
carried some boxes, not all one and the same box. -/
theorem dependent_iff (huu' : u ≠ u') :
    {i} ∈ (sentence u u' P (distW u) M (bare u')).dom ↔
      ∃ x, P x ∧ ∃ b : E → E, (atomsBelow x).Nonempty ∧
        (∀ a ∈ atomsBelow x, M.noun (b a) ∧ M.verb a (b a)) ∧
        ¬ ((∀ a ∈ atomsBelow x, Atom (b a)) ∧ (b '' atomsBelow x).Subsingleton) := by
  rw [singleton_mem_dom_sentence_iff]
  refine exists_congr fun x ↦ and_congr_right fun _ ↦ ?_
  rw [singleton_mem_dom_distW_iff huu', val_extend_self]
  refine exists_congr fun b ↦ and_congr_right fun _ ↦ and_congr_right fun _ ↦ ?_
  simpa only [val_extend_self] using
    image_mem_bare_iff (u := u) (k := extend i u x) (u' := u') (b := b)

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

/-! ### Quantificational determiners (§5.4.4) -/

/-- Maximization `max_u` (106) at the level of assignments: `D` succeeds, and on no `u`-variant of
the input on which `D` succeeds does an assignment give `u` a value above its value in the input. -/
def max (u : R) (D : Update (Set S)) : Update (Set S) :=
  {(I, J) | I ~[D] J ∧ ∀ I', I ~[intro u] I' → I' ∈ D.dom →
    ∀ i ∈ I, ∀ i' ∈ I', i ~[randomAssign u] i' → val u i' ≤ val u i}

/-- `MOST{u', u}` (107a): at every assignment the value of `u` has more atoms than the part of the
value of `u'` outside it. -/
def most (u' u : R) : Condition (Set S) :=
  {I | I.Nonempty ∧ ∀ i ∈ I,
    (atomsBelow (val u' i) \ atomsBelow (val u i)).ncard < atomCount E (val u i)}

/-- `EVERY{u', u}` (107b): at every assignment the values of `u'` and `u` have as many atoms. -/
def every (u' u : R) : Condition (Set S) :=
  {I | I.Nonempty ∧ ∀ i ∈ I, atomCount E (val u' i) = atomCount E (val u i)}

/-- The externally static weak distributivity operator `dist'_w` (97a) tests that weak
distributivity can update the state. -/
def distW' (u : R) (D : Update (Set S)) : Update (Set S) := test (distW u D).dom

/-- The externally static strong distributivity operator `dist'_s` (97b). -/
def distS' (u : R) (D : Update (Set S)) : Update (Set S) := test (distS u D).dom

/-- The plural determiner (108): it introduces the maxset dref `u'` and the refset dref `u`,
relates them by the static determiner `q`, and maximizes `u'` over the restrictor and `u` over the
restrictor and the nuclear scope, both under weak distributivity. -/
def detPl (q : R → R → Condition (Set S)) (u' u : R) (P P' : R → Update (Set S)) :
    Update (Set S) :=
  intro u' ○ intro u ○ test (q u' u) ○ max u' (distW' u' (P u')) ○ max u (distW u (P u ○ P' u))

/-- The singular determiner (109), which maximizes under strong distributivity. -/
def detSg (q : R → R → Condition (Set S)) (u' u : R) (P P' : R → Update (Set S)) :
    Update (Set S) :=
  intro u' ○ intro u ○ test (q u' u) ○ max u' (distS' u' (P u')) ○ max u (distS u (P u ○ P' u))

/-- On a one-assignment state, maximization compares the value of `u` with those of its
`u`-variants on which the update succeeds. -/
theorem singleton_mem_max_iff {k : S} {J : Set S} :
    {k} ~[max u D] J ↔ {k} ~[D] J ∧ ∀ y, {extend k u y} ∈ D.dom → y ≤ val u k := by
  refine ⟨fun ⟨hD, hmax⟩ ↦ ⟨hD, fun y hy ↦ ?_⟩,
    fun ⟨hD, h⟩ ↦ ⟨hD, fun I' hI' hdom i hi i' hi' _ ↦ ?_⟩⟩
  · simpa [val_extend_self] using
      hmax _ (singleton_mem_intro_iff.2 ⟨y, rfl⟩) hy k rfl _ rfl ⟨y, rfl⟩
  · obtain ⟨y, rfl⟩ := singleton_mem_intro_iff.1 hI'
    rw [Set.mem_singleton_iff] at hi hi'
    subst hi hi'
    rw [val_extend_self]
    exact h y hdom

variable {u'' : R}

/-- The schema (105) at a one-assignment input: values `x'` of `u'` and `x` of `u` pass the test
`q`, `x'` is the greatest value of `u'` passing `T`, and `x` the greatest value of `u` on which `D`
succeeds. -/
theorem singleton_mem_dom_schema_iff {q T : Condition (Set S)} (h₁ : u' ≠ u) :
    {i} ∈ (intro u' ○ intro u ○ test q ○ max u' (test T) ○ max u D).dom ↔
      ∃ x' x, {extend (extend i u' x') u x} ∈ q ∧ {extend (extend i u' x') u x} ∈ T ∧
        (∀ y, {extend (extend (extend i u' x') u x) u' y} ∈ T → y ≤ x') ∧
        {extend (extend i u' x') u x} ∈ D.dom ∧
        ∀ y, {extend (extend (extend i u' x') u x) u y} ∈ D.dom → y ≤ x := by
  have hv' (x' x : E) : val u' (extend (extend i u' x') u x) = x' := by
    rw [val_extend_of_ne _ _ _ _ h₁, val_extend_self]
  constructor
  · rintro ⟨J, K, ⟨L, ⟨M, ⟨N, hiN, hNM⟩, rfl, hq⟩, hmax'⟩, hmax⟩
    obtain ⟨x', rfl⟩ := singleton_mem_intro_iff.1 hiN
    obtain ⟨x, rfl⟩ := singleton_mem_intro_iff.1 hNM
    obtain ⟨⟨rfl, hT⟩, hT'⟩ := singleton_mem_max_iff.1 hmax'
    obtain ⟨hD, hD'⟩ := singleton_mem_max_iff.1 hmax
    refine ⟨x', x, hq, hT, fun y hy ↦ ?_, ⟨J, hD⟩, fun y hy ↦ ?_⟩
    · simpa [hv'] using hT' y (by simpa using hy)
    · simpa [val_extend_self] using hD' y hy
  · rintro ⟨x', x, hq, hT, hT', ⟨J, hD⟩, hD'⟩
    refine ⟨J, _, ⟨_, ⟨_, ⟨_, singleton_mem_intro_iff.2 ⟨x', rfl⟩,
      singleton_mem_intro_iff.2 ⟨x, rfl⟩⟩, rfl, hq⟩, singleton_mem_max_iff.2 ⟨⟨rfl, hT⟩,
      fun y hy ↦ ?_⟩⟩, singleton_mem_max_iff.2 ⟨hD, fun y hy ↦ ?_⟩⟩
    · rw [hv']
      exact hT' y (by simpa using hy)
    · rw [val_extend_self]
      exact hD' y hy

theorem mem_dom_distW_test_comp {C : Condition (Set S)} :
    I ∈ (distW u (test C ○ D)).dom ↔ split u I ∈ C ∧ I ∈ (distW u D).dom := by
  simp only [mem_dom, mem_distW, mem_test_comp]
  exact ⟨fun ⟨J, hC, hD⟩ ↦ ⟨hC, J, hD⟩, fun ⟨hC, J, hD⟩ ↦ ⟨J, hC, hD⟩⟩

/-- A restrictor under weak distributivity holds of every atomic part of the value. -/
theorem singleton_mem_dom_distW_lex_iff {k : S} {P : E → Prop} :
    {k} ∈ (distW u (test (lex P u))).dom ↔
      (atomsBelow (val u k)).Nonempty ∧ ∀ a ∈ atomsBelow (val u k), P a := by
  simp only [mem_dom, mem_distW, mem_test_iff_left, exists_eq_left', mem_lex,
    image_val_split_singleton, Set.subset_def, Set.mem_ofPred_eq]

/-- A singular restrictor under strong distributivity holds of every atomic part of the value. -/
theorem singleton_mem_dom_distS_lex_iff {k : S} {P : E → Prop} :
    {k} ∈ (distS u (test (atomic u ∩ unique u ∩ lex P u))).dom ↔
      (atomsBelow (val u k)).Nonempty ∧ ∀ a ∈ atomsBelow (val u k), P a := by
  rw [singleton_mem_dom_distS_iff]
  refine and_congr_right fun _ ↦ forall₂_congr fun a ha ↦ ?_
  rw [dom_test, Set.mem_inter_iff, singleton_mem_atomic_inter_unique_iff, singleton_mem_lex_iff,
    val_extend_self]
  exact and_iff_right ha.1

/-- A restrictor and a nuclear scope with a bare plural object under weak distributivity: every
atomic part of the value satisfies the restrictor and `verb`s a sum of `noun`s, not one and the same
atom for all of them. -/
theorem singleton_mem_dom_distW_scope_iff {k : S} {P : E → Prop} (h : u ≠ u'') :
    {k} ∈ (distW u (test (lex P u) ○ (vp u u'' M ○ test (bare u'')))).dom ↔
      (atomsBelow (val u k)).Nonempty ∧ (∀ a ∈ atomsBelow (val u k), P a) ∧
        ∃ b : E → E, (∀ a ∈ atomsBelow (val u k), M.noun (b a) ∧ M.verb a (b a)) ∧
          ¬((∀ a ∈ atomsBelow (val u k), Atom (b a)) ∧
            (b '' atomsBelow (val u k)).Subsingleton) := by
  rw [mem_dom_distW_test_comp, singleton_mem_dom_distW_iff h]
  simp only [mem_lex, image_val_split_singleton, Set.subset_def, Set.mem_ofPred_eq,
    image_mem_bare_iff]
  exact ⟨fun ⟨⟨hne, hP⟩, b, _, hb, hbare⟩ ↦ ⟨hne, hP, b, hb, hbare⟩,
    fun ⟨hne, hP, b, hb, hbare⟩ ↦ ⟨⟨hne, hP⟩, b, hne, hb, hbare⟩⟩

/-- A singular restrictor and a nuclear scope with a bare plural object under strong
distributivity: every atomic part of the value satisfies the restrictor and `verb`s a non-atomic
sum of `noun`s. -/
theorem singleton_mem_dom_distS_scope_iff {k : S} {P : E → Prop} (h : u ≠ u'') :
    {k} ∈ (distS u (test (atomic u ∩ unique u ∩ lex P u) ○
      (vp u u'' M ○ test (bare u'')))).dom ↔
      (atomsBelow (val u k)).Nonempty ∧ ∀ a ∈ atomsBelow (val u k), P a ∧
        ∃ b, M.noun b ∧ M.verb a b ∧ ¬Atom b := by
  rw [singleton_mem_dom_distS_iff]
  refine and_congr_right fun _ ↦ forall₂_congr fun a ha ↦ ?_
  rw [dom_comp, preimage_test, Set.mem_inter_iff, Set.mem_inter_iff,
    singleton_mem_atomic_inter_unique_iff, singleton_mem_lex_iff, val_extend_self,
    singleton_mem_dom_vp_iff h, val_extend_self]
  simp only [bare, Set.mem_compl_iff, singleton_mem_atomic_inter_unique_iff, val_extend_self]
  exact ⟨fun ⟨⟨_, hP⟩, h⟩ ↦ ⟨hP, h⟩, fun ⟨hP, h⟩ ↦ ⟨⟨ha.1, hP⟩, h⟩⟩

/-- The plural determiner *most* over a restrictor `P` with a bare plural object (131), (137): the
greatest sum of `P`-atoms each of which `verb`s a sum of `noun`s, more than one overall, has more
atoms than the rest of the greatest sum of `P`-atoms (pp. 479–480). -/
theorem detPl_most_iff (h₁ : u' ≠ u) (h₂ : u ≠ u'') :
    {i} ∈ (detPl most u' u (fun v ↦ test (lex P v)) (fun v ↦ vp v u'' M ○ test (bare u''))).dom ↔
      ∃ x' x, IsGreatest {y | (atomsBelow y).Nonempty ∧ ∀ a ∈ atomsBelow y, P a} x' ∧
        IsGreatest {y | (atomsBelow y).Nonempty ∧ (∀ a ∈ atomsBelow y, P a) ∧
          ∃ b : E → E, (∀ a ∈ atomsBelow y, M.noun (b a) ∧ M.verb a (b a)) ∧
            ¬((∀ a ∈ atomsBelow y, Atom (b a)) ∧ (b '' atomsBelow y).Subsingleton)} x ∧
        (atomsBelow x' \ atomsBelow x).ncard < atomCount E x := by
  have hv' (x' x : E) : val u' (extend (extend i u' x') u x) = x' := by
    rw [val_extend_of_ne _ _ _ _ h₁, val_extend_self]
  simp only [detPl, distW']
  rw [singleton_mem_dom_schema_iff h₁]
  refine exists₂_congr fun x' x ↦ ?_
  simp only [singleton_mem_dom_distW_lex_iff, singleton_mem_dom_distW_scope_iff M h₂,
    val_extend_self, hv', most, Set.mem_ofPred_eq, Set.singleton_nonempty, Set.mem_singleton_iff,
    forall_eq, true_and, IsGreatest, upperBounds]
  exact ⟨fun ⟨hq, hR, hR', hC, hC'⟩ ↦ ⟨⟨hR, hR'⟩, ⟨hC, hC'⟩, hq⟩,
    fun ⟨⟨hR, hR'⟩, ⟨hC, hC'⟩, hq⟩ ↦ ⟨hq, hR, hR', hC, hC'⟩⟩

/-- The singular determiner *every* over a singular restrictor `P` with a bare plural object (174),
(177): the greatest sum of `P`-atoms each of which `verb`s a non-atomic sum of `noun`s has as many
atoms as the greatest sum of `P`-atoms, so every `P`-atom does (p. 491). -/
theorem detSg_every_iff (h₁ : u' ≠ u) (h₂ : u ≠ u'') :
    {i} ∈ (detSg every u' u (fun v ↦ test (atomic v ∩ unique v ∩ lex P v))
      (fun v ↦ vp v u'' M ○ test (bare u''))).dom ↔
      ∃ x' x, IsGreatest {y | (atomsBelow y).Nonempty ∧ ∀ a ∈ atomsBelow y, P a} x' ∧
        IsGreatest {y | (atomsBelow y).Nonempty ∧ ∀ a ∈ atomsBelow y, P a ∧
          ∃ b, M.noun b ∧ M.verb a b ∧ ¬Atom b} x ∧ atomCount E x' = atomCount E x := by
  have hv' (x' x : E) : val u' (extend (extend i u' x') u x) = x' := by
    rw [val_extend_of_ne _ _ _ _ h₁, val_extend_self]
  simp only [detSg, distS']
  rw [singleton_mem_dom_schema_iff h₁]
  refine exists₂_congr fun x' x ↦ ?_
  simp only [singleton_mem_dom_distS_lex_iff, singleton_mem_dom_distS_scope_iff M h₂,
    val_extend_self, hv', every, Set.mem_ofPred_eq, Set.singleton_nonempty, Set.mem_singleton_iff,
    forall_eq, true_and, IsGreatest, upperBounds]
  exact ⟨fun ⟨hq, hR, hR', hC, hC'⟩ ↦ ⟨⟨hR, hR'⟩, ⟨hC, hC'⟩, hq⟩,
    fun ⟨⟨hR, hR'⟩, ⟨hC, hC'⟩, hq⟩ ↦ ⟨hq, hR, hR', hC, hC'⟩⟩

/-! ### The girls and their hats (§1, §2)

The examples (3), (4), (10b), (11a), (12b) and (13) are judged in a context where each girl wore a
single hat and no two girls the same hat. -/

/-- Three girls `0`, `1`, `2` and three hats `3`, `4`, `5`. -/
abbrev Thing := Fin 6

/-- The drefs of the subject, of the object and of a determiner's maxset. -/
inductive Dref where
  | subj
  | obj
  | maxset
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

/-- The restrictor *girl(s)* of a determiner. -/
def girl (x : Finset Thing) : Prop := x.Nonempty ∧ x ⊆ {0, 1, 2}

private theorem le_of_forall_girl {y : Finset Thing} (h : ∀ a ∈ atomsBelow y, girl a) :
    y ≤ {0, 1, 2} := fun g hg ↦
  Finset.singleton_subset_iff.1 (h _ (by rw [atomsBelow_finset]; exact ⟨g, hg, rfl⟩)).2

theorem hats_verb_iff {x y : Finset Thing} :
    hats.verb x y ↔ x.Nonempty ∧ (∀ a ∈ x, ∃ b ∈ y, Wears a b) ∧ ∀ b ∈ y, ∃ a ∈ x, Wears a b := by
  simp [hats, Plurality.Cumulativity.cumulation_map_singleton, Set.LiftRel]

theorem exists_eq_singleton_of_verb {g : Thing} {y : Finset Thing} (h : hats.verb {g} y) :
    ∃ b, y = {b} := by
  rw [hats_verb_iff] at h
  revert g y
  decide

variable (i : Dref → Finset Thing)

/-- The analysis predicts the judgments of (4), (11a), (3), (13), (10b) and (12b). -/
theorem judgments :
    (Examples.ex_4.judgment = .acceptable ↔
      {i} ∈ (sentence Dref.subj Dref.obj theGirls id hats (cardinal (1 < ·) Dref.obj)).dom) ∧
    (Examples.ex_3.judgment = .acceptable ↔
      {i} ∈ (sentence Dref.subj Dref.obj theGirls (distW Dref.subj) hats
        (cardinal (1 < ·) Dref.obj)).dom) ∧
    (Examples.ex_11a.judgment = .acceptable ↔
      {i} ∈ (sentence Dref.subj Dref.obj theGirls (distW Dref.subj) hats (bare Dref.obj)).dom) ∧
    (Examples.ex_13.judgment = .acceptable ↔
      {i} ∈ (sentence Dref.subj Dref.obj theGirls (distS Dref.subj) hats (bare Dref.obj)).dom) ∧
    (Examples.ex_10b.judgment = .acceptable ↔
      {i} ∈ (detPl most Dref.maxset Dref.subj (fun v ↦ test (lex girl v))
        (fun v ↦ vp v Dref.obj hats ○ test (bare Dref.obj))).dom) ∧
    (Examples.ex_12b.judgment = .acceptable ↔
      {i} ∈ (detSg every Dref.maxset Dref.subj (fun v ↦ test (atomic v ∩ unique v ∩ lex girl v))
        (fun v ↦ vp v Dref.obj hats ○ test (bare Dref.obj))).dom) := by
  have hne : Dref.subj ≠ Dref.obj := nofun
  have hne' : Dref.maxset ≠ Dref.subj := nofun
  have h0 : ({0} : Finset Thing) ∈ atomsBelow ({0, 1, 2} : Finset Thing) := by
    rw [atomsBelow_finset]
    exact ⟨0, by decide, rfl⟩
  have hgirls : (atomsBelow ({0, 1, 2} : Finset Thing)).Nonempty ∧
      ∀ a ∈ atomsBelow ({0, 1, 2} : Finset Thing), girl a := by
    refine ⟨⟨_, h0⟩, ?_⟩
    rw [atomsBelow_finset, Set.forall_mem_image]
    exact fun g hg ↦ ⟨Finset.singleton_nonempty g, Finset.singleton_subset_iff.2 hg⟩
  refine ⟨iff_of_true rfl ?_, iff_of_false (by decide) ?_, iff_of_true rfl ?_,
    iff_of_false (by decide) ?_, iff_of_true rfl ?_, iff_of_false (by decide) ?_⟩
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
  · rw [detPl_most_iff girl hats hne' hne]
    refine ⟨_, _, ⟨hgirls, fun y hy ↦ le_of_forall_girl hy.2⟩,
      ⟨⟨hgirls.1, hgirls.2, fun a ↦ a.image (· + 3), ?_, fun hs ↦ ?_⟩,
        fun y hy ↦ le_of_forall_girl hy.2.1⟩, ?_⟩
    · rw [atomsBelow_finset, Set.forall_mem_image]
      intro g hg
      refine ⟨⟨by simp, ?_⟩, hats_verb_iff.2 ?_⟩ <;> revert g <;> decide
    · have h1 : ({1} : Finset Thing) ∈ atomsBelow ({0, 1, 2} : Finset Thing) := by
        rw [atomsBelow_finset]
        exact ⟨1, by decide, rfl⟩
      have := hs.2 (Set.mem_image_of_mem _ h0) (Set.mem_image_of_mem _ h1)
      revert this
      decide
    · simp [atomCount_finset]
  · rw [detSg_every_iff girl hats hne' hne]
    rintro ⟨-, x, -, ⟨⟨⟨a, ha⟩, h⟩, -⟩, -⟩
    obtain ⟨-, b, -, hb, hat⟩ := h a ha
    rw [atomsBelow_finset] at ha
    obtain ⟨g, -, rfl⟩ := ha
    obtain ⟨c, rfl⟩ := exists_eq_singleton_of_verb hb
    exact hat (atom_iff_isAtom.2 (Finset.isAtom_singleton c))

end Minor2022
