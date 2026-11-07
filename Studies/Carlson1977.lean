module

public import Mathlib.Basic.Rel
public import Linglib.Data.Examples.Carlson1977
public import Linglib.Logic.Modal.Defs
public import Linglib.Semantics.Quantification.Individual

/-!
# Carlson (1977): A unified analysis of the English bare plural

Carlson's bare plural is the proper name of a kind, an individual realized by stages, temporally and
spatially bounded portions of its existence, among them the stages of its instances. Milsark's
properties hold of the kind and his states of its stages, so a state holds of a kind exactly when
[it holds of some of its instances](##Model.mem_image_iff), and it [passes to any kind containing
them](##Model.mem_image_of_mem_image). That existential lies in the predicate and takes narrowest
scope: only a name [commutes with negation and universal quantification](##some_scopeless_iff),
belief that a kind is present [is belief that some instance is](##Model.box_mem_image_iff), and a
kind, unlike a particular individual, [can be everywhere](##Model.everywhere_iff).

## Implementation notes

* Stages and individuals are distinct types, which the paper leaves open.
* Kinds and particular individuals are both individuals; spatial boundedness, which separates
  them, is a property an individual has or lacks in a model.
* Belief is necessity along a doxastic accessibility relation. Only the properties of stages vary
  with the world; the realization relation and the name of a kind are rigid.

## Errata

* The progressive, p. 450, prints `R(x, y)`, its arguments reversed from pp. 449 and 451.
* The translation of (135c), p. 454, prints `R(x, d)` with `x` free, for `R(z, d)`.

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
open scoped ModalLogic

variable {Stage Ind Place Time : Type*}

/-! ### Stages and individuals -/

/-- A model of the ontology: stages, each at a place and a time, and the relation of a stage to the
individuals it realizes. -/
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

/-- The places an individual occupies at the time `t`, those of its stages `M.R.preimage {x}`
then. -/
def placesAt (x : Ind) (t : Time) : Set Place :=
  M.place '' (M.R.preimage {x} ∩ {s | M.time s = t})

/-- An individual is spatially bounded when it "can only be in one place at a time" (p. 451), as
particular individuals are and kinds are not. -/
def SpatiallyBounded (x : Ind) : Prop := ∀ t, (M.placesAt x t).Subsingleton

/-- *be everywhere* at the time `t`, `λx ∀y[Place'(y) → ∃z[R(z, x) ∧ At(z, y)]]` (p. 454), `Place`
being the relevant places. -/
def Everywhere (t : Time) (x : Ind) : Prop := ∀ p, x ∈ M.R.image (M.located p t)

variable {M} {x k k' : Ind} {t : Time}

theorem everywhere_iff_placesAt_eq_univ : M.Everywhere t x ↔ M.placesAt x t = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  exact forall_congr' fun p ↦ ⟨fun ⟨s, ⟨hp, ht⟩, hs⟩ ↦ ⟨s, ⟨⟨x, rfl, hs⟩, ht⟩, hp⟩,
    fun ⟨s, ⟨⟨_, rfl, hs⟩, ht⟩, hp⟩ ↦ ⟨s, ⟨hp, ht⟩, hs⟩⟩

-- (135a), p. 454
theorem not_everywhere [Nontrivial Place] (hx : M.SpatiallyBounded x) (t : Time) :
    ¬ M.Everywhere t x := fun h ↦
  not_subsingleton Place <| Set.subsingleton_univ_iff.1 <|
    everywhere_iff_placesAt_eq_univ.1 h ▸ hx t

-- (135b), p. 454: the existential over dogs scopes over the universal over places
theorem not_some_everywhere [Nontrivial Place] {N : Set Ind}
    (hN : ∀ x ∈ N, M.SpatiallyBounded x) (t : Time) : ¬ Det.some N {x | M.Everywhere t x} :=
  fun ⟨x, hx, h⟩ ↦ not_everywhere (hN x hx) t h

/-! ### Kinds and their instances

`x ~[inst] k` says that `x` is an instance of the kind `k`. Two hypotheses link their stages: a
stage of an instance is a stage of the kind, since "If there are some of a kind present, then this
counts as the presence of that kind" (p. 451), and a stage of the kind is a stage of some instance
(p. 452). -/

variable {inst : SetRel Ind Ind}

/-- A state holds of a kind exactly when it holds of some of its instances, so *Dogs are sick*
means *Some dogs are sick*, the existential coming from the predicate (p. 451). -/
theorem mem_image_iff (h : M.R ○ inst ⊆ M.R) (hk : ∀ ⦃s⦄, s ~[M.R] k → s ~[M.R ○ inst] k)
    (P : Set Stage) : k ∈ M.R.image P ↔ Det.some {x | x ~[inst] k} (M.R.image P) :=
  ⟨fun ⟨s, hs, hsk⟩ ↦ let ⟨x, hsx, hxk⟩ := hk hsk; ⟨x, hxk, s, hs, hsx⟩,
    fun ⟨x, hxk, s, hs, hsx⟩ ↦ ⟨s, hs, h ⟨x, hsx, hxk⟩⟩⟩

/-- A state passes from a kind to any kind containing its instances, so *Dogs are sitting on my
lawn* and *All dogs are mammals* give *Mammals are sitting on my lawn* (119). -/
theorem mem_image_of_mem_image (h : M.R ○ inst ⊆ M.R)
    (hk : ∀ ⦃s⦄, s ~[M.R] k → s ~[M.R ○ inst] k) (hsub : ∀ ⦃x⦄, x ~[inst] k → x ~[inst] k')
    {P : Set Stage} (hP : k ∈ M.R.image P) : k' ∈ M.R.image P :=
  let ⟨x, hxk, s, hs, hsx⟩ := (mem_image_iff h hk P).1 hP
  ⟨s, hs, h ⟨x, hsx, hsub hxk⟩⟩

/-- A kind is everywhere exactly when at every place some of its instances are there, the
universal over places outscoping the existential in *Dogs are everywhere* (135c). -/
theorem everywhere_iff (h : M.R ○ inst ⊆ M.R) (hk : ∀ ⦃s⦄, s ~[M.R] k → s ~[M.R ○ inst] k) :
    M.Everywhere t k ↔ ∀ p, Det.some {x | x ~[inst] k} (M.R.image (M.located p t)) :=
  forall_congr' fun _ ↦ mem_image_iff h hk _

/-! ### Opacity

Belief is necessity along a doxastic accessibility `B`, and a state varies with the world, holding
at `v` of the stages `P v`. *Max believes some dogs are here* (131) has a transparent reading,
`Det.some N {x | □[B] (fun v ↦ x ∈ M.R.image (P v)) w}`, and an opaque one,
`□[B] (fun v ↦ Det.some N (M.R.image (P v))) w`. *Max believes dogs are here* (132) is the name of
the kind applied to the property of being believed to have a stage here, which by the rigidity of
the name is belief that the kind has a stage here (p. 452). -/

/-- Belief that a kind is in a state is belief that some of its instances are, so *Max believes dogs
are here* has the opaque reading of *Max believes some dogs are here* (p. 452). -/
theorem box_mem_image_iff {W : Type*} (h : M.R ○ inst ⊆ M.R)
    (hk : ∀ ⦃s⦄, s ~[M.R] k → s ~[M.R ○ inst] k) (B : SetRel W W) (P : W → Set Stage) (w : W) :
    □[B] (fun v ↦ k ∈ M.R.image (P v)) w ↔
      □[B] (fun v ↦ Det.some {x | x ~[inst] k} (M.R.image (P v))) w :=
  forall₂_congr fun v _ ↦ mem_image_iff h hk (P v)

end Model

/-! ### Scope

A proper name commutes with negation and with universal quantification, and by
`Quantifier.exists_eq_individual_iff` nothing else does. *Cats are here and cats are not here*,
(134), is a contradiction because `λx ¬∃y[R(y, x) ∧ Here'(y)](c)` is `¬∃y[R(y, c) ∧ Here'(y)]`
(p. 453), the name commuting with the negation; *Everyone read books on caterpillars*, (23), has
one reading because the name commutes with the universal. *Buildings will collapse in Berlin
tomorrow, and will burn in Boston the day after*, (59), means (58) because the name commutes with
the conjunction of two states, each with its own existential over stages: the predicate is
`R.image P ∩ R.image Q`, which only contains `R.image (P ∩ Q)`. -/

/-- An existential over a noun commutes with negation and with universal quantification exactly
when the noun has one member. -/
theorem some_scopeless_iff {E : Type*} {N : Set E} :
    ((∀ P, Det.some N Pᶜ ↔ ¬ Det.some N P) ∧
      ∀ S : Set (Set E), Det.some N (⋂₀ S) ↔ ∀ P ∈ S, Det.some N P) ↔ ∃ a, N = {a} := by
  simp only [← Quantifier.exists_eq_individual_iff, Quantifier.some_eq_individual_iff]

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

theorem model_everywhere_dogs : model.Everywhere () .dogs :=
  fun p ↦ ⟨p, ⟨rfl, rfl⟩, Or.inr (Or.inl rfl)⟩

theorem model_spatiallyBounded (d : Dog) : model.SpatiallyBounded (.dog d) := by
  rintro _ _ ⟨s, ⟨⟨_, rfl, hs⟩, -⟩, rfl⟩ _ ⟨s', ⟨⟨_, rfl, hs'⟩, -⟩, rfl⟩
  simp only [model, Set.mem_ofPred_eq, Individual.dog.injEq, reduceCtorEq, or_false] at hs hs'
  exact hs.symm.trans hs'

/-- The kind dogs is not spatially bounded. -/
example : ¬ model.SpatiallyBounded .dogs :=
  fun h ↦ Model.not_everywhere h () model_everywhere_dogs

/-- (120) in the model: a property that dogs have and mammals lack, such as being good pets, is
not the image of any property of stages. -/
example : {Individual.dogs} ∉ Set.range model.R.image := by
  rintro ⟨P, hP⟩
  have hd : Individual.dogs ∈ model.R.image P := hP ▸ rfl
  have := Model.mem_image_of_mem_image (k' := .mammals) model_comp_subset
    (model_stages_of_kind (.inl rfl)) (fun _ ⟨d, hx, _⟩ ↦ ⟨d, hx, .inr rfl⟩) hd
  rw [hP] at this
  cases this

-- (132), p. 452: in each of Max's alternatives, the worlds `d`, the stage of the dog `d` is here,
-- so he believes dogs are here but believes of no dog that it is here
theorem model_believes_not_transparent :
    □[⊤] (fun d : Dog ↦ Individual.dogs ∈ model.R.image {d}) Dog.rex ∧
      ¬ Det.some {x | x ~[ofKind] .dogs}
        {x | □[⊤] (fun d : Dog ↦ x ∈ model.R.image {d}) Dog.rex} := by
  refine ⟨fun d _ ↦ ⟨d, rfl, .inr (.inl rfl)⟩, ?_⟩
  rintro ⟨_, ⟨d, rfl, -⟩, hd⟩
  obtain ⟨d', hd'⟩ := exists_ne d
  obtain ⟨_, rfl, h⟩ := hd d' (Set.mem_univ _)
  simp only [model, Set.mem_ofPred_eq, Individual.dog.injEq, reduceCtorEq, or_false] at h
  exact hd' h.symm

/-! ### The paper's judgments -/

-- (119), (120), p. 445: the state passes from dogs to mammals, the property of being good pets
-- need not
theorem judgments_119_120 :
    ((∀ P, Individual.dogs ∈ model.R.image P → Individual.mammals ∈ model.R.image P) ↔
        Examples.ex_119.judgment = .acceptable) ∧
      ((∀ Q : Set Individual, .dogs ∈ Q → .mammals ∈ Q) ↔
        Examples.ex_120.judgment = .acceptable) :=
  ⟨iff_of_true (fun _ ↦ Model.mem_image_of_mem_image (k' := .mammals) model_comp_subset
      (model_stages_of_kind (.inl rfl)) fun _ ⟨d, hx, _⟩ ↦ ⟨d, hx, .inr rfl⟩) rfl,
    iff_of_false (fun h ↦ nomatch h {.dogs} rfl) (by decide)⟩

-- (131), (132), p. 452: the two readings of (131) differ, and the translation of (132) has the
-- opaque one and not the transparent one
theorem readings_131_132 :
    (□[⊤] (fun d ↦ Det.some {x | x ~[ofKind] .dogs} (model.R.image {d})) Dog.rex ∧
        ¬ Det.some {x | x ~[ofKind] .dogs}
          {x | □[⊤] (fun d : Dog ↦ x ∈ model.R.image {d}) Dog.rex} ↔
      Examples.ex_131.readings = [("transparent", .acceptable), ("opaque", .acceptable)]) ∧
    ((□[⊤] (fun d : Dog ↦ Individual.dogs ∈ model.R.image {d}) Dog.rex ↔
        □[⊤] (fun d ↦ Det.some {x | x ~[ofKind] .dogs} (model.R.image {d})) Dog.rex) ↔
      Examples.ex_132.readings.lookup "opaque" = some .acceptable) ∧
    ((□[⊤] (fun d : Dog ↦ Individual.dogs ∈ model.R.image {d}) Dog.rex →
        Det.some {x | x ~[ofKind] .dogs}
          {x | □[⊤] (fun d : Dog ↦ x ∈ model.R.image {d}) Dog.rex}) ↔
      Examples.ex_132.readings.lookup "transparent" = some .acceptable) := by
  have hop := Model.box_mem_image_iff model_comp_subset (model_stages_of_kind (.inl rfl))
    ⊤ (fun d : Dog ↦ {d}) Dog.rex
  obtain ⟨hb, htr⟩ := model_believes_not_transparent
  exact ⟨iff_of_true ⟨hop.1 hb, htr⟩ rfl, iff_of_true hop rfl,
    iff_of_false (fun h ↦ htr (h hb)) (by decide)⟩

-- (135), pp. 453-454: the dog rex is a particular individual, as Jake is
theorem verdicts_135 :
    (model.Everywhere () (.dog .rex) ↔ Examples.ex_135a.verdict = some true) ∧
      (Det.some {x | x ~[ofKind] .dogs} {x | model.Everywhere () x} ↔
        Examples.ex_135b.verdict = some true) ∧
      (model.Everywhere () .dogs ↔ Examples.ex_135c.verdict = some true) :=
  ⟨iff_of_false (Model.not_everywhere (model_spatiallyBounded .rex) ()) (by decide),
    iff_of_false (Model.not_some_everywhere
      (by rintro _ ⟨d, rfl, -⟩; exact model_spatiallyBounded d) ()) (by decide),
    iff_of_true model_everywhere_dogs rfl⟩

end Carlson1977
