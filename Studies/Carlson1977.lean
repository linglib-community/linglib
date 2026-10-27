module

public import Mathlib.Basic.Rel
public import Linglib.Semantics.Quantification.Individual

/-!
# Carlson (1977): A unified analysis of the English bare plural

[carlson-1977] argues that the English bare plural is unambiguous. Its existential use is not
the plural of *a*: it takes only opaque readings (§1.2), only narrow scope with negation and
other quantifiers (§1.3), and even narrower scope than *a* allows, as in (30) *Dogs were
everywhere* against the bizarre (29) *A dog was everywhere* (differentiated scope, §1.4). Its
existential and generic uses are in complementary distribution, fixed by the predicate (§2). The
analysis of §4 treats the bare plural as the proper name of a kind, translated as
[montague-1973] translates a proper name, `λP P{d}` (`Quantifier.NP.individual`), and puts the
existential in the predicate. Of the two classes of predicates that [milsark-1974] and
[siegel-1976] isolate, Milsark's properties and states, a property is predicated of an
individual and a state of one of its stages, a temporally and spatially bounded realization of
it: *Dogs are intelligent* is `I(d)` and *Dogs are sick* is `∃y[R(y, d) ∧ sick'(y)]`, the image
of the state under the realization relation `R` (`SetRel.image`).

Three consequences are derived. The scope facts force the analysis: by
`Quantifier.NP.exists_eq_individual_iff` a noun-phrase denotation that commutes with negation and
with universal quantification is a proper name, and an existential over a noun commutes with both
exactly when the noun has one member (`some_scopeless_iff`). Differentiated scope follows from
the ontology: a particular individual "can only be in one place at a time" (`SpatiallyBounded`),
so neither *Jake is everywhere* nor *Some dog is everywhere* can be true, (135a, b)
(`not_everywhere`, `not_some_everywhere`), while a kind whose stages are those of its instances
is everywhere when its instances are spread over the places, (135c) (`everywhere_iff`). And
states inherit along the instance relation where properties do not: *Dogs are sitting on my
lawn* and *All dogs are mammals* give *Mammals are sitting on my lawn*, (119)
(`mem_image_of_mem_image`), while *Dogs are good pets* does not give *Mammals are good pets*,
(120), so a property of dogs that mammals lack is no state.

## Implementation notes

* Stages and individuals are distinct types. The paper gives them one type, noting that they
  should be distinguished "at some level" and leaving the matter open (p. 450).
* Particular individuals and kinds are both individuals, and nothing records which is which:
  spatial boundedness, "the main difference between kinds and individuals" (p. 451), is a
  property an individual has or lacks in a model.
* The link between a kind and its instances `inst` is stated in two directions, as hypotheses.
  That every stage of a kind is a stage of one of its instances is stated on p. 452; that a stage
  of an instance is a stage of its kind is inferred from "If there are some of a kind present,
  then this counts as the presence of that kind" (p. 451). A stage of a kind is a stage of one
  instance, where p. 451 has "one or more of that kind".
* *be everywhere* is evaluated at a time, and `Place` is the relevant places, the restrictor
  `Place'` of the paper's formula (p. 454), so `[Nontrivial Place]` says there are two of them.
* The progressive, which "turns a 'property' into a 'state'" (p. 450), is the same image under
  `R`; its formula on p. 450 prints the arguments of `R` in the opposite order from p. 449 and is
  not transcribed. The habitual *Dogs run*, `run'(d)`, is a property of the kind, and its
  relation to the state `run'` is left open, as in the paper.
* The negation of (134), the universal of (22) and (23), the conjunction of (58) and (59), and the
  belief of (132), read as universal quantification over doxastic alternatives, are all instances
  of the two clauses of `Quantifier.NP.exists_eq_individual_iff`. Montague's intension operator
  is not modelled.

## TODO

* The anaphora facts of §1.5 and §2.2 need a dynamic layer.

## References

* [carlson-1977]
* [milsark-1974]
* [siegel-1976]
* [montague-1973]
-/

@[expose] public section

namespace Carlson1977

open SetRel Quantifier

variable {Stage Ind Place Time : Type*}

/-! ### Stages and individuals -/

/-- A model of the ontology of §4.2: stages, each at a place and a time, and the relation of a
stage to the individuals it realizes. -/
structure Model (Stage Ind Place Time : Type*) where
  /-- `s ~[R] x`: the stage `s` realizes the individual `x`, the paper's `R(s, x)`. -/
  R : SetRel Stage Ind
  /-- The place of a stage. -/
  place : Stage → Place
  /-- The time of a stage. -/
  time : Stage → Time

namespace Model

variable (M : Model Stage Ind Place Time)

/-- The stages at the place `p` at the time `t`, those of which the paper's `At(z, p)` holds. -/
def located (p : Place) (t : Time) : Set Stage := {s | M.place s = p ∧ M.time s = t}

/-- The places an individual occupies at the time `t`, those of its stages then. Its stages are
`M.R.preimage {x}`, the paper's `λx R(x, j)` (p. 449). -/
def placesAt (x : Ind) (t : Time) : Set Place :=
  M.place '' (M.R.preimage {x} ∩ {s | M.time s = t})

/-- An individual is spatially bounded when it "can only be in one place at a time" (p. 451), as
particular individuals are and kinds are not. -/
def SpatiallyBounded (x : Ind) : Prop := ∀ t, (M.placesAt x t).Subsingleton

/-- *be everywhere* at the time `t`, `λx ∀y[Place'(y) → ∃z[R(z, x) ∧ At(z, y)]]` (p. 454): for
every place, the state of being there holds of `x`. -/
def Everywhere (t : Time) (x : Ind) : Prop := ∀ p, x ∈ M.R.image (M.located p t)

variable {M} {x k k' : Ind} {t : Time}

theorem everywhere_iff_placesAt_eq_univ : M.Everywhere t x ↔ M.placesAt x t = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  exact forall_congr' fun p ↦ ⟨fun ⟨s, ⟨hp, ht⟩, hs⟩ ↦ ⟨s, ⟨⟨x, rfl, hs⟩, ht⟩, hp⟩,
    fun ⟨s, ⟨⟨_, rfl, hs⟩, ht⟩, hp⟩ ↦ ⟨s, ⟨hp, ht⟩, hs⟩⟩

/-- (135a) *Jake is everywhere* is false: an individual that can only be in one place at a time
is not everywhere, given two places. -/
theorem not_everywhere [Nontrivial Place] (hx : M.SpatiallyBounded x) (t : Time) :
    ¬ M.Everywhere t x := fun h ↦
  not_subsingleton Place <| Set.subsingleton_univ_iff.1 <|
    everywhere_iff_placesAt_eq_univ.1 h ▸ hx t

/-- (135b) *Some dog is everywhere* is false when every dog is spatially bounded, since the
existential over dogs scopes over the universal over places. -/
theorem not_some_everywhere [Nontrivial Place] {N : Ind → Prop}
    (hN : ∀ x, N x → M.SpatiallyBounded x) (t : Time) : ¬ GQ.some N (M.Everywhere t) :=
  fun ⟨x, hx, h⟩ ↦ not_everywhere (hN x hx) t h

/-! ### Kinds and their instances -/

variable {inst : SetRel Ind Ind}

theorem image_image_subset (h : M.R ○ inst ⊆ M.R) (P : Set Stage) :
    inst.image (M.R.image P) ⊆ M.R.image P := by
  rw [← image_comp]
  exact image_subset_image_left h

theorem mem_image_iff (h : M.R ○ inst ⊆ M.R) (hk : ∀ ⦃s⦄, s ~[M.R] k → s ~[M.R ○ inst] k)
    (P : Set Stage) : k ∈ M.R.image P ↔ k ∈ inst.image (M.R.image P) := by
  rw [← image_comp]
  exact ⟨fun ⟨s, hs, hsk⟩ ↦ ⟨s, hs, hk hsk⟩, fun ⟨s, hs, hsk⟩ ↦ ⟨s, hs, h hsk⟩⟩

/-- A state passes from a kind to any kind containing all its instances, so *Dogs are sitting on my
lawn* yields *Mammals are sitting on my lawn* (119). -/
theorem mem_image_of_mem_image (h : M.R ○ inst ⊆ M.R)
    (hk : ∀ ⦃s⦄, s ~[M.R] k → s ~[M.R ○ inst] k) (hsub : ∀ ⦃x⦄, x ~[inst] k → x ~[inst] k')
    {P : Set Stage} (hP : k ∈ M.R.image P) : k' ∈ M.R.image P := by
  obtain ⟨x, hx, hxk⟩ := (mem_image_iff h hk P).1 hP
  exact image_image_subset h P ⟨x, hx, hsub hxk⟩

/-- A kind is everywhere iff some instance is at each place, as in *Dogs are everywhere* (135c). -/
theorem everywhere_iff (h : M.R ○ inst ⊆ M.R) (hk : ∀ ⦃s⦄, s ~[M.R] k → s ~[M.R ○ inst] k) :
    M.Everywhere t k ↔ ∀ p, ∃ x ∈ M.R.image (M.located p t), x ~[inst] k := by
  simp only [Everywhere, mem_image_iff h hk, SetRel.mem_image]

end Model

/-! ### Scope

A proper name commutes with negation and with universal quantification, and by
`Quantifier.NP.exists_eq_individual_iff` nothing else does. *Cats are here and cats are not here*,
(134), is a contradiction because `λx ¬∃y[R(y, x) ∧ Here'(y)](c)` is `¬∃y[R(y, c) ∧ Here'(y)]`
(p. 453), the name commuting with the negation; *Everyone read books on caterpillars*, (23), has
one reading because the name commutes with the universal. *Buildings will collapse in Berlin
tomorrow, and will burn in Boston the day after*, (59), means (58) because the name commutes with
the conjunction of two states, each with its own existential over stages: the predicate is
`R.image P ∩ R.image Q`, which only contains `R.image (P ∩ Q)`. -/

theorem some_scopeless_iff {E : Type*} {N : E → Prop} :
    ((∀ P, GQ.some N Pᶜ ↔ ¬ GQ.some N P) ∧
      ∀ S : Set (E → Prop), GQ.some N (sInf S) ↔ ∀ P ∈ S, GQ.some N P) ↔
      ∃ a, N = ident a := by
  simp only [← NP.exists_eq_individual_iff, NP.some_eq_individual_iff]

/-! ### A model

Two dogs, each with one stage at its own place, and the kinds dogs and mammals, both realized by
the stages of their instances. Dogs are everywhere while neither dog is, and a property that
dogs have and mammals lack is no state. -/

/-- The dogs of the model. -/
inductive Dog where
  | rex
  | fido
  deriving DecidableEq

instance : Nontrivial Dog := ⟨⟨.rex, .fido, nofun⟩⟩

/-- The individuals of the model: two kinds and two dogs. -/
inductive Individual where
  | dogs
  | mammals
  | dog (d : Dog)
  deriving DecidableEq

/-- `x ~[ofKind] k`: each dog is of both kinds. -/
def ofKind : SetRel Individual Individual :=
  {p | ∃ d, p.1 = .dog d ∧ (p.2 = .dogs ∨ p.2 = .mammals)}

/-- The model: each dog's one stage is at that dog's place, and it realizes the dog and both
kinds. -/
def model : Model Dog Individual Dog Unit where
  R := {p | p.2 = .dog p.1 ∨ p.2 = .dogs ∨ p.2 = .mammals}
  place := id
  time := fun _ ↦ ()

theorem model_comp_subset : model.R ○ ofKind ⊆ model.R := by
  rintro ⟨s, k⟩ ⟨x, -, d, rfl, hk⟩
  exact Or.inr hk

theorem model_stages_of_kind {k : Individual} (hk : k = .dogs ∨ k = .mammals) :
    ∀ ⦃s⦄, s ~[model.R] k → s ~[model.R ○ ofKind] k :=
  fun s _ ↦ ⟨.dog s, Or.inl rfl, s, rfl, hk⟩

-- (135c)
theorem model_everywhere_dogs : model.Everywhere () .dogs :=
  fun p ↦ ⟨p, ⟨rfl, rfl⟩, Or.inr (Or.inl rfl)⟩

theorem model_spatiallyBounded (d : Dog) : model.SpatiallyBounded (.dog d) := by
  rintro _ _ ⟨s, ⟨⟨_, rfl, hs⟩, -⟩, rfl⟩ _ ⟨s', ⟨⟨_, rfl, hs'⟩, -⟩, rfl⟩
  simp only [model, Set.mem_ofPred_eq, Individual.dog.injEq, reduceCtorEq, or_false] at hs hs'
  exact hs.symm.trans hs'

/-- The kind dogs is not spatially bounded. -/
example : ¬ model.SpatiallyBounded .dogs :=
  fun h ↦ Model.not_everywhere h () model_everywhere_dogs

/-- (135b) in the model: no dog is everywhere. -/
example : ¬ GQ.some (· ~[ofKind] .dogs) (model.Everywhere ()) :=
  Model.not_some_everywhere (by rintro _ ⟨d, rfl, -⟩; exact model_spatiallyBounded d) ()

/-- (120) in the model: a property that dogs have and mammals lack, such as being good pets, is
not the image of any property of stages. -/
example : {Individual.dogs} ∉ Set.range model.R.image := by
  rintro ⟨P, hP⟩
  have hd : Individual.dogs ∈ model.R.image P := hP ▸ rfl
  have := Model.mem_image_of_mem_image (k' := .mammals) model_comp_subset
    (model_stages_of_kind (.inl rfl)) (fun _ ⟨d, hx, _⟩ ↦ ⟨d, hx, .inr rfl⟩) hd
  rw [hP] at this
  cases this

end Carlson1977
