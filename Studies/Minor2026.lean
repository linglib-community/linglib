module

public import Linglib.Data.Examples.Minor2026
public import Linglib.Logic.Team.Atoms
public import Linglib.Morphology.DistributedMorphology.VocabularyInsertion.Basic
public import Studies.Magri2009
public import Studies.Minor2022

/-!
# Minor (2026): Atomic plurals

Bare plurals take narrowest scope (*Miles wants to meet policemen*), but in the scope of a plural
licensor they can scope out of an intensional context (*All the boys want to meet policemen*), as
Partee observed. Minor splits the singular into ATOM, atomicity at every assignment, and UNIQUE,
one value across the state. The plural form spells out either neither feature, a concept that
takes no scope, or ATOM alone, an atomic plural, which is an indefinite and can scope. Exh against
the singular leaves an atomic plural non-unique, which no state reached from one assignment
satisfies unless a weakly distributive licensor has split it. Minor's Plural Compositional Logic
is the static counterpart of the dynamic system of `Studies/Minor2022`: a formula holds of a state
where the corresponding update succeeds.

## Main definitions

* `Minor2026.NumFeature`, `Minor2026.Composes`, `Minor2026.exponents`: the features of the
  #-head (65), Complex Heads (69) and the exponents (66).
* `Minor2026.SemType.denote`, `Minor2026.NumFeature.denote`: the types of concepts and of
  predicates of referents, and the translations (65) between them.
* `Minor2026.want`: an attitude (100) distributing the worlds compatible with its experiencer's
  wishes.

## Main results

* `Minor2026.composes_heads`, `Minor2026.spellOut`: the atomic plural is a well-typed head
  spelled out as a plural, and `[#, UNIQUE]` is not well-typed (fn. 21).
* `Minor2026.denote_heads`: the singular head denotes the singular's atomicity and uniqueness,
  and the atomic plural's head atomicity alone.
* `Minor2026.exh_atomicPlural`, `Minor2026.disjoint_exhR_atomicPlural`: Exh negates the singular
  alternative of an atomic plural (87), mandatorily at single assignments (§6.2).
* `Minor2026.notMem_dom_sentence_atomicPlural`, `Minor2026.atomicPlural_distW_iff`: an atomic
  plural is contradictory without a weakly distributive licensor (88) and co-distributive under
  one (90).
* `Minor2026.notMem_dom_intro_test_of_injOn`: an atomic plural exhaustified relative to `w` fails
  wherever `w` tells the assignments apart, at a single assignment and under an attitude.
* `Minor2026.mem_dom_want_test_iff`: *want* with a flat complement quantifies over the worlds
  compatible with the experiencer's wishes.
* `Minor2026.wideScope_iff`: the wide-scope dependent plural (134), with each licensor's own
  atomic referent (§8).
* `Minor2026.partee`: Partee's generalization, the wide-scope readings of (93).

## Implementation notes

* Intensionalized uniqueness `unique_w(y)` (103b) is Väänänen's dependence atom
  `Team.dep (val w) (val y)`, which holds when assignments agreeing on the world `w` agree on `y`.
* Events are folded into the lexical relations, as in `Studies/Minor2022`, and the maximal sum of
  worlds compatible with the experiencer's wishes (100) is a function `bul` of the world and the
  experiencer.
* The exhaustified atomic plural is atomicity and non-uniqueness, the consequence (121) of its
  strengthened meaning that fn. 29 states.
* *All the boys* is weak distributivity over the sum of the boys, as in `Studies/Minor2022`.

## TODO

* The narrow-scope readings of (93), the singular and plural under *want* ((106), (114)), and the
  narrow-scope dependent plural (124), (132).
* The referent-set reformulation of §9, which drops the Minimal Context Conjecture (143).

## References

* [minor-2026]
* [minor-2022]
* [magri-2009]
* [vaananen-2007]
-/

@[expose] public section

namespace Minor2026

open DynamicSemantics DynamicSemantics.Update SetRel RegisterStructure Mereology Minor2022
open DistributedMorphology
open scoped DynamicSemantics.Update

/-! ### Decomposing number (§6.1) -/

/-- The features of the #-head (65), the category feature `#`, ATOM and UNIQUE. -/
inductive NumFeature where
  | num
  | atom
  | unique
  deriving DecidableEq

/-- The types the features of the #-head map between, concepts and predicates of referents. -/
inductive SemType where
  | concept
  | pred
  deriving DecidableEq

/-- The types of the translations (65), under which `#` maps concepts to concepts, ATOM concepts
to predicates, and UNIQUE predicates to predicates. -/
def NumFeature.sig : NumFeature → SemType × SemType
  | .num => (.concept, .concept)
  | .atom => (.concept, .pred)
  | .unique => (.pred, .pred)

/-- A sequence of features composes when each output type is the next input type, as Complex
Heads (69) requires. -/
def Composes (l : List NumFeature) : Prop := l.IsChain fun f g ↦ f.sig.2 = g.sig.1

instance : DecidablePred Composes := fun _ ↦ inferInstanceAs (Decidable (List.IsChain _ _))

/-- `[#, ATOM, UNIQUE]` and `[#, ATOM]` compose, and `[#, UNIQUE]` composes in neither order, so
the atomic plural is a possible head and `[#, UNIQUE]` is not (fn. 21). -/
theorem composes_heads :
    Composes [.num, .atom, .unique] ∧ Composes [.num, .atom] ∧
      ¬ Composes [.num, .unique] ∧ ¬ Composes [.unique, .num] := by
  decide

/-- The two exponents of the #-head of English count nouns. -/
inductive Exponent where
  | null
  | s
  deriving DecidableEq

/-- In the exponents (66) `/∅/` spells out `[#, ATOM, UNIQUE]` and `/s/` spells out `[#]`. -/
def exponents : List (VocabularyItem NumFeature Exponent) :=
  [.ofFeatures {.num, .atom, .unique} .null, .ofFeatures {.num} .s]

/-- By the Subset Principle (67) the singular form spells out only the full head (68), and the
atomic plural is spelled out by `/s/`, as the plain plural is (71), (73a). -/
theorem spellOut :
    subsetPrinciple exponents ({.num, .atom, .unique} : Finset NumFeature) = some .null ∧
      subsetPrinciple exponents ({.num, .atom} : Finset NumFeature) = some .s ∧
        subsetPrinciple exponents ({.num} : Finset NumFeature) = some .s := by
  decide

section Denotation

universe w

variable {R S E : Type w} [RegisterStructure R S E] [PartialOrder E]

/-- A concept, a type of (65), denotes the predicate of individuals of a noun, and a predicate of
referents denotes a condition on the values of a referent. -/
abbrev SemType.denote (R S E : Type w) : SemType → Type w
  | .concept => E → Prop
  | .pred => R → Condition (Set S)

/-- The translations (65) take `#` to the identity on concepts, ATOM to the instantiation of a
concept by a referent with atomic values, and UNIQUE to the addition of uniqueness to a predicate
of referents. -/
def NumFeature.denote : (f : NumFeature) → f.sig.1.denote R S E → f.sig.2.denote R S E
  | .num => id
  | .atom => fun P u ↦ lex P u ∩ atomic u
  | .unique => fun C u ↦ C u ∩ Minor2022.unique u

/-- The head `[#, ATOM, UNIQUE]` denotes instantiation with the singular's atomicity and
uniqueness (74), and the atomic plural `[#, ATOM]` the same without uniqueness. -/
theorem denote_heads (P : E → Prop) (u : R) :
    NumFeature.unique.denote (NumFeature.atom.denote (NumFeature.num.denote (R := R) (S := S) P))
        u = lex P u ∩ (atomic u ∩ unique u) ∧
      NumFeature.atom.denote (NumFeature.num.denote (R := R) (S := S) P) u =
        lex P u ∩ atomic u :=
  ⟨Set.inter_assoc .., rfl⟩

end Denotation

/-! ### Intensionalized uniqueness (§7.2) -/

variable {R S E : Type*} [RegisterStructure R S E] {u u' w w' x y : R} {H I J : Set S} {i k : S}
  {C : Condition (Set S)} {D : Update (Set S)}

/-- Introducing a referent other than `w` keeps `w` telling the assignments apart. -/
theorem injOn_of_mem_intro (hwy : w ≠ y) (hH : Set.InjOn (val w) H) (h : H ~[intro y] J) :
    Set.InjOn (val w) J := by
  obtain ⟨f, hf, rfl⟩ := h
  have hval (j) (hj : j ∈ H) : val w (f j) = val w j := by
    obtain ⟨e, he⟩ := hf j hj
    rw [he, val_extend_of_ne _ _ _ _ hwy]
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
  rw [hH ha hb ((hval a ha).symm.trans (hab.trans (hval b hb)))]

/-- A referent required not to be a function of `w` cannot be introduced where `w` tells the
assignments apart, so an exhaustified atomic plural fails there ((113)–(121)). -/
theorem notMem_dom_intro_test_of_injOn (hwy : w ≠ y) (hH : Set.InjOn (val w) H)
    (hC : C ⊆ (Team.dep (val w) (val y))ᶜ) : H ∉ (intro y ○ test C ○ D).dom := by
  rintro ⟨_, _, ⟨J, hJ, rfl, hJC⟩, -⟩
  exact hC hJC (Set.InjOn.factorsThrough_domRestrict (injOn_of_mem_intro hwy hH hJ))

/-- An atomic plural scoping over *want* without a licensor is contradictory ((117)–(121)), since
at a single assignment it is unique. -/
theorem notMem_dom_intro_test_singleton (hwy : w ≠ y) (hC : C ⊆ (Team.dep (val w) (val y))ᶜ) :
    {k} ∉ (intro y ○ test C ○ D).dom :=
  notMem_dom_intro_test_of_injOn hwy (Set.injOn_singleton _ _) hC

/-! ### Atomic plurals and Exh (§6.2) -/

variable {P : E → Prop} {M : Model E}

/-- From a single assignment a VP leads to a single assignment. -/
theorem subsingleton_of_mem_vp (hI : I.Subsingleton) (h : I ~[vp u u' M] J) : J.Subsingleton := by
  obtain ⟨K, ⟨f, -, rfl⟩, rfl, -⟩ := h
  exact hI.image f

variable [PartialOrder E]

variable (u u') in
/-- Two assignments differing at `u` can give an atomic plural object two atomic values. -/
theorem exists_mem_vp_atomic_not_unique {a b : E} (ha : Atom a) (hb : Atom b) (hab : a ≠ b)
    (i : S) : ∃ I J : Set S, (I, J) ∈ vp u u' ⟨fun _ ↦ True, fun _ _ ↦ True⟩ ○ test (atomic u') ∧
      J ∉ unique u' := by
  let f : S → S := fun r ↦ extend r u' (val u r)
  have hf (r : S) : val u' (f r) = val u r := val_extend_self ..
  have hne : (f '' {extend i u a, extend i u b}).Nonempty := ⟨_, _, Or.inl rfl, rfl⟩
  refine ⟨{extend i u a, extend i u b}, f '' {extend i u a, extend i u b},
    mem_comp_test.2 ⟨mem_comp_test.2 ⟨⟨f, fun r _ ↦ ⟨val u r, rfl⟩, rfl⟩,
      ⟨hne.image _, fun _ _ ↦ trivial⟩, hne.image _, fun _ _ ↦ trivial⟩, ?_⟩, fun hU ↦ hab ?_⟩
  · rintro _ ⟨_, ⟨r, rfl | rfl, rfl⟩, rfl⟩
    · simpa [hf, val_extend_self] using ha
    · simpa [hf, val_extend_self] using hb
  · have := hU ⟨f (extend i u a), ⟨_, Or.inl rfl, rfl⟩, rfl⟩
      ⟨f (extend i u b), ⟨_, Or.inr rfl, rfl⟩, rfl⟩
    simpa [hf, val_extend_self] using this

variable (u u') in
/-- Exh above a VP whose object is an atomic plural negates the singular alternative (79), which
some state of two assignments separates from it, and leaves non-uniqueness (87). -/
theorem exh_atomicPlural {a b : E} (ha : Atom a) (hb : Atom b) (hab : a ≠ b) (i : S) :
    Exhaustification.exh
        {acrossModels (S := S) fun M : Model E ↦ vp u u' M ○ test (atomic u') ○ test (unique u')}
        (acrossModels (S := S) fun M : Model E ↦ vp u u' M ○ test (atomic u')) =
      acrossModels (S := S) fun M : Model E ↦ vp u u' M ○ test (atomic u') ○ test (unique u')ᶜ := by
  obtain ⟨I, J, hp, hU⟩ := exists_mem_vp_atomic_not_unique u u' ha hb hab i
  exact exh_acrossModels_comp_test (comp_test_lt _ fun h ↦ hU (mem_comp_test.1 (h hp)).2)

variable (u u') in
/-- The non-uniqueness implicature of an atomic plural is mandatory (§6.2). At a single assignment
the singular alternative is equivalent to the atomic plural, so a relevance property obeying
[magri-2009]'s postulates keeps it relevant, and the exhaustified atomic plural is false at every
single assignment. -/
theorem disjoint_exhR_atomicPlural {a b : E} (ha : Atom a) (hb : Atom b) (hab : a ≠ b) (i : S)
    {Rel : Set (Model E × (Set S × Set S)) → Prop}
    (hR : Magri2009.IsRelevance {w | w.2.1.Subsingleton}
      (acrossModels fun M : Model E ↦ vp u u' M ○ test (atomic u')) Rel) :
    Disjoint (Magri2009.exhR Rel
        {acrossModels fun M : Model E ↦ vp u u' M ○ test (atomic u'),
          acrossModels fun M : Model E ↦ vp u u' M ○ test (atomic u') ○ test (unique u')}
        (acrossModels fun M : Model E ↦ vp u u' M ○ test (atomic u')))
      {w | w.2.1.Subsingleton} := by
  obtain ⟨I, J, hp, hU⟩ := exists_mem_vp_atomic_not_unique u u' ha hb hab i
  have hw : (⟨fun _ ↦ True, fun _ _ ↦ True⟩, I, J) ∉
      acrossModels fun M : Model E ↦ vp u u' M ○ test (atomic u') ○ test (unique u') :=
    fun h ↦ hU (mem_comp_test.1 h).2
  refine Magri2009.disjoint_exhR hR (.of_forall_subset_or_notMem (by simp) hp hw ?_) ?_
  · rintro _ (rfl | rfl)
    exacts [Or.inl subset_rfl, Or.inr hw]
  · ext ⟨m, I, J⟩
    simp only [acrossModels, Set.mem_inter_iff, Set.mem_ofPred_eq, mem_comp_test]
    refine ⟨fun ⟨⟨h, _⟩, hI⟩ ↦ ⟨h, hI⟩, fun ⟨⟨h, hA⟩, hI⟩ ↦ ⟨⟨⟨h, hA⟩, ?_⟩, hI⟩⟩
    exact ((subsingleton_of_mem_vp hI h).image _)

/-- Without a weakly distributive licensor an atomic plural is contradictory (88), since from a
single assignment the state stays a single assignment, where uniqueness holds. -/
theorem notMem_dom_sentence_atomicPlural (huu' : u ≠ u') :
    {i} ∉ (sentence u u' P id M (atomic u' ∩ (unique u')ᶜ)).dom := by
  rw [singleton_mem_dom_sentence_iff]
  simp [singleton_mem_dom_vp_iff huu', unique]

/-- Under a strongly distributive licensor an atomic plural is contradictory too, since every
singleton state makes it unique. -/
theorem notMem_dom_sentence_distS_atomicPlural (huu' : u ≠ u') :
    {i} ∉ (sentence u u' P (distS u) M (atomic u' ∩ (unique u')ᶜ)).dom := by
  rw [singleton_mem_dom_sentence_iff]
  rintro ⟨x, -, h⟩
  obtain ⟨⟨a, ha⟩, h⟩ := singleton_mem_dom_distS_iff.1 h
  obtain ⟨y, -, -, -, hU⟩ := (singleton_mem_dom_vp_iff huu').1 (h a ha)
  exact hU (by simp [unique])

/-- Under a weakly distributive licensor an atomic plural is co-distributive (90), every atomic
part of the subject having carried a single box, and not all of them the same one. -/
theorem atomicPlural_distW_iff (huu' : u ≠ u') :
    {i} ∈ (sentence u u' P (distW u) M (atomic u' ∩ (unique u')ᶜ)).dom ↔
      ∃ x, P x ∧ ∃ b : E → E, (atomsBelow x).Nonempty ∧
        (∀ a ∈ atomsBelow x, M.noun (b a) ∧ M.verb a (b a)) ∧
        (∀ a ∈ atomsBelow x, Atom (b a)) ∧ ¬ (b '' atomsBelow x).Subsingleton := by
  rw [singleton_mem_dom_sentence_iff]
  refine exists_congr fun x ↦ and_congr_right fun _ ↦ ?_
  rw [singleton_mem_dom_distW_iff huu', val_extend_self]
  refine exists_congr fun b ↦ and_congr_right fun _ ↦ and_congr_right fun _ ↦ ?_
  simp only [atomic, unique, Set.mem_compl_iff, Set.mem_inter_iff,
    Set.mem_ofPred_eq, Set.image_image, Set.image_subset_iff, val_extend_self]
  simp [Set.subset_def, val_extend_self]

/-! ### Attitudes and Partee's generalization (§7) -/

variable {bul : E → E → E}

variable (w w' x) in
/-- *want* (100) at world `w` with experiencer `x` gives the world referent `w'` the sum `bul` of
the worlds compatible with the experiencer's wishes, and weakly distributes `w'` over its
complement. -/
def want (bul : E → E → E) (D : Update (Set S)) : Update (Set S) :=
  intro w' ○ test {I | Set.EqOn (val w') (fun i ↦ bul (val w i) (val x i)) I} ○ distW w' D

/-- A split tells its assignments apart by the referent it splits. -/
theorem injOn_val_split : Set.InjOn (val u) (split u {k}) := by
  rw [split_singleton]
  rintro _ ⟨a, -, rfl⟩ _ ⟨b, -, rfl⟩ h
  simp only [val_extend_self] at h
  rw [h]

/-- An atomic plural under *want* alone is contradictory ((115), (116)), since the attitude tells
the assignments of its complement apart by their worlds. -/
theorem notMem_dom_want_atomicPlural (hw'y : w' ≠ y) (hC : C ⊆ (Team.dep (val w') (val y))ᶜ) :
    {k} ∉ (want w w' x bul (intro y ○ test C ○ D)).dom := by
  rintro ⟨out, _, ⟨_, hK, rfl, -⟩, hD⟩
  obtain ⟨e, rfl⟩ := singleton_mem_intro_iff.1 hK
  exact notMem_dom_intro_test_of_injOn hw'y injOn_val_split hC ⟨out, mem_distW.1 hD⟩

/-- With a flat complement *want* is Hintikka's, holding of a state exactly when the complement
holds at every world compatible with each experiencer's wishes. -/
theorem mem_dom_want_test_iff (hxw' : x ≠ w') (hww' : w ≠ w') {Q : Set S} :
    J ∈ (want w w' x bul (test (𝒫 Q))).dom ↔
      ∀ j ∈ J, ∀ v ∈ atomsBelow (bul (val w j) (val x j)), extend j w' v ∈ Q := by
  let g : S → S := fun j ↦ extend j w' (bul (val w j) (val x j))
  have hg (j : S) : val w' (g j) = bul (val w j) (val x j) := val_extend_self ..
  constructor
  · rintro ⟨out, _, ⟨_, ⟨f, hf, rfl⟩, rfl, hT⟩, hD⟩
    have hfg (j) (hj : j ∈ J) : f j = g j := by
      obtain ⟨e, he⟩ := hf j hj
      have := hT ⟨j, hj, rfl⟩
      simp only [he, val_extend_self, val_extend_of_ne _ _ _ _ hww',
        val_extend_of_ne _ _ _ _ hxw'] at this
      rw [he, this]
    obtain ⟨-, hQ⟩ := mem_test_iff_left.1 (mem_distW.1 hD)
    intro j hj v hv
    have := hQ (mem_split.2 ⟨f j, ⟨j, hj, rfl⟩, v, by rwa [hfg j hj, hg], rfl⟩)
    rwa [hfg j hj, extend_idem] at this
  · intro h
    refine ⟨_, _, ⟨_, ⟨g, fun j _ ↦ ⟨_, rfl⟩, rfl⟩, rfl, ?_⟩, mem_distW.2
      (mem_test_iff_left.2 ⟨rfl, fun z hz ↦ ?_⟩)⟩
    · rintro _ ⟨j, -, rfl⟩
      simp [g, val_extend_self, val_extend_of_ne _ _ _ _ hww', val_extend_of_ne _ _ _ _ hxw']
    · obtain ⟨_, ⟨j, hj, rfl⟩, v, hv, rfl⟩ := mem_split.1 hz
      rw [hg] at hv
      simpa [g, extend_idem] using h j hj v hv

/-- A model of the attitude sentences (93) fixes Miles, the sum of the boys, *policeman* at a
world, the worlds compatible with an experiencer's wishes at a world, and *meet* at a world. -/
structure IModel (E : Type*) where
  /-- Miles. -/
  miles : E
  /-- The sum of the boys. -/
  boys : E
  /-- Instantiation of *policeman* at a world. -/
  inst : E → E → Prop
  /-- The sum of the worlds compatible with an experiencer's wishes at a world. -/
  bul : E → E → E
  /-- *meet* at a world, between an agent and a theme. -/
  meet : E → E → E → Prop

variable (w w' x y) in
/-- On the wide-scope reading of *[subject] want(s) to meet [object]* the object introduces `y`
under the condition `C` above the attitude, below the subject's distributivity operator `d`. -/
def wide (M : IModel E) (P : E → Prop) (d : Update (Set S) → Update (Set S))
    (C : Condition (Set S)) : Update (Set S) :=
  intro x ○ test (lex P x) ○ d (intro y ○ test (lex₂ M.inst w y ∩ C) ○
    want w w' x M.bul (test (𝒫 {j | M.meet (val w' j) (val x j) (val y j)})))

/-- Without a weakly distributive licensor an atomic plural takes no wide scope over *want*
((117)–(121)), so the wide-scope reading of *Miles wants to meet policemen* is contradictory. -/
theorem notMem_dom_wide_atomicPlural (hwy : w ≠ y) (M : IModel E) (P : E → Prop) :
    {i} ∉ (wide w w' x y M P id (atomic y ∩ (Team.dep (val w) (val y))ᶜ)).dom := by
  rw [wide, singleton_mem_dom_intro_comp_iff]
  rintro ⟨s, -, h⟩
  exact notMem_dom_intro_test_singleton hwy (fun _ hJ ↦ hJ.2.2) h

/-- On the wide-scope dependent plural reading (133), (134) of *All the boys want to meet
policemen*, every atomic part `a` of the subject has an atomic policeman `b a` whom it meets at
every world compatible with its wishes, and the policemen are not all the same. That each is
atomic is Minor's new prediction (§8). -/
theorem wideScope_iff (hxy : x ≠ y) (hwx : w ≠ x) (hwy : w ≠ y) (hxw' : x ≠ w') (hww' : w ≠ w')
    (hyw' : y ≠ w') (M : IModel E) (P : E → Prop) :
    {i} ∈ (wide w w' x y M P (distW x) (atomic y ∩ (Team.dep (val w) (val y))ᶜ)).dom ↔
      ∃ s, P s ∧ ∃ b : E → E,
        (∀ a ∈ atomsBelow s, M.inst (val w i) (b a) ∧ Atom (b a) ∧
          ∀ v ∈ atomsBelow (M.bul (val w i) a), M.meet v a (b a)) ∧
        ¬ (b '' atomsBelow s).Subsingleton := by
  rw [wide, singleton_mem_dom_intro_comp_iff]
  refine exists_congr fun s ↦ ?_
  rw [singleton_mem_lex_iff, val_extend_self]
  refine and_congr_right fun _ ↦ ?_
  rw [singleton_mem_dom_distW_intro_iff, val_extend_self]
  refine exists_congr fun b ↦ ?_
  rw [mem_dom_want_test_iff hxw' hww']
  have hw : (val w '' ((fun a ↦ extend (extend (extend i x s) x a) y (b a)) ''
      atomsBelow s)).Subsingleton := by
    rintro _ ⟨_, ⟨a, -, rfl⟩, rfl⟩ _ ⟨_, ⟨a', -, rfl⟩, rfl⟩
    simp [val_extend_of_ne _ _ _ _ hwy, val_extend_of_ne _ _ _ _ hwx]
  simp only [Set.mem_inter_iff, Set.mem_compl_iff, Team.dep, Set.mem_ofPred_eq,
    Set.factorsThrough_domRestrict_iff_of_subsingleton hw,
    lex₂, atomic, Set.mem_ofPred_eq, Set.image_image, Set.forall_mem_image,
    Set.image_nonempty, Set.subset_def, val_extend_self,
    val_extend_of_ne _ _ _ _ hwy, val_extend_of_ne _ _ _ _ hwx, val_extend_of_ne _ _ _ _ hxy,
    val_extend_of_ne _ _ _ _ hxw', val_extend_of_ne _ _ _ _ hyw']
  constructor
  · rintro ⟨⟨⟨-, hi⟩, ha, hs⟩, hm⟩
    exact ⟨fun a h ↦ ⟨hi h, ha h, hm h⟩, hs⟩
  · rintro ⟨h, hs⟩
    exact ⟨⟨⟨(Set.not_subsingleton_iff.1 hs).nonempty.of_image, fun a ha ↦ (h a ha).1⟩,
      fun a ha ↦ (h a ha).2.1, hs⟩, fun a ha ↦ (h a ha).2.2⟩

/-! ### Partee's paradigm (93) -/

/-- The actual world `0`, the worlds `1` and `2`, the boys `3` and `4`, of whom `3` is Miles, and
the policemen `5` and `6`. -/
abbrev Thing := Fin 7

/-- The drefs of the attitude sentences, the actual world, the subject, the object, and the
worlds of the attitude. -/
inductive Dref where
  | world
  | subj
  | obj
  | bul
  deriving DecidableEq

/-- In this model each boy wants to meet a policeman of his own, the boy `a` wishing to be in the
world `a - 2` and to meet the policeman `a + 2` there. -/
def model : IModel (Finset Thing) where
  miles := {3}
  boys := {3, 4}
  inst _ p := p.Nonempty ∧ p ⊆ {5, 6}
  bul _ a := a.image (· - 2)
  meet v a p := v = a.image (· - 2) ∧ p = a.image (· + 2)

/-- Partee's generalization (36) says that a bare plural scopes over *want* exactly when a weakly
distributive licensor scopes over it. The wide-scope readings of (93) are available exactly when
their logical forms are satisfiable. The singular's (109) and the dependent plural's (133) are, in
a model where each boy wants to meet a policeman of his own, and the plain plural's (117) is in
no model. -/
theorem partee :
    (Examples.ex_93a.readings.lookup "∃ > want" = some .acceptable ↔
      ∃ (M : IModel (Finset Thing)) (i : Dref → Finset Thing), {i} ∈ (wide Dref.world Dref.bul
        Dref.subj Dref.obj M (· = M.miles) id
          (atomic Dref.obj ∩ Team.dep (val Dref.world) (val Dref.obj))).dom) ∧
    (Examples.ex_93b.readings.lookup "∃ > want" = some .acceptable ↔
      ∃ (M : IModel (Finset Thing)) (i : Dref → Finset Thing), {i} ∈ (wide Dref.world Dref.bul
        Dref.subj Dref.obj M (· = M.miles) id
          (atomic Dref.obj ∩ (Team.dep (val Dref.world) (val Dref.obj))ᶜ)).dom) ∧
    (Examples.ex_93c.readings.lookup "∃ > want" = some .acceptable ↔
      ∃ (M : IModel (Finset Thing)) (i : Dref → Finset Thing), {i} ∈ (wide Dref.world Dref.bul
        Dref.subj Dref.obj M (· = M.boys) (distW Dref.subj)
          (atomic Dref.obj ∩ (Team.dep (val Dref.world) (val Dref.obj))ᶜ)).dom) := by
  refine ⟨iff_of_true (by decide) ⟨model, fun _ ↦ ∅, ?_⟩,
    iff_of_false (by decide) fun ⟨M, i, h⟩ ↦ notMem_dom_wide_atomicPlural (by decide) M _ h,
    iff_of_true (by decide) ⟨model, fun _ ↦ ∅, ?_⟩⟩
  · rw [wide, singleton_mem_dom_intro_comp_iff]
    refine ⟨{3}, by simp [singleton_mem_lex_iff, model], ?_⟩
    rw [id, singleton_mem_dom_intro_comp_iff]
    refine ⟨{5}, ⟨by simp [singleton_mem_lex₂_iff, model], ?_, Team.singleton_mem_dep _⟩, ?_⟩
    · simp [atomic, atom_iff_isAtom]
    · rw [mem_dom_want_test_iff (by decide) (by decide)]
      simp [model, atomsBelow_finset]
  · rw [wideScope_iff (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    have h₃ : ({3} : Finset Thing) ∈ atomsBelow ({3, 4} : Finset Thing) := by
      rw [atomsBelow_finset]
      exact ⟨3, by decide, rfl⟩
    have h₄ : ({4} : Finset Thing) ∈ atomsBelow ({3, 4} : Finset Thing) := by
      rw [atomsBelow_finset]
      exact ⟨4, by decide, rfl⟩
    refine ⟨_, rfl, fun a ↦ a.image (· + 2), ?_, fun hs ↦ ?_⟩
    · simp only [atomsBelow_finset, Set.forall_mem_image, Finset.mem_coe, atom_iff_isAtom,
        Finset.isAtom_iff, model]
      decide
    · have := hs (Set.mem_image_of_mem _ h₃) (Set.mem_image_of_mem _ h₄)
      revert this
      decide

end Minor2026
