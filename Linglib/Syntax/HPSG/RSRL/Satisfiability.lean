/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.HPSG.RSRL.Subinterpretation
public import Mathlib.Logic.Small.Basic

/-!
# Satisfiability and entailment in RSRL

A theory is *satisfiable over* a grammar `G` when some entity of some well-typed model of `G` is
described by every description of the theory, and `G` *entails* a description when the
description describes every entity of every well-typed model of `G`. A grammar licenses a
configuration when the theory of the configuration is satisfiable over it, and predicts a
generalization when it entails it.

Both notions quantify over the models in the universe of the signature. This loses nothing:
satisfaction at an entity depends only on its components, which are reached by paths and so form
a set no larger than the signature, and a model can be cut down to them
(`HPSG.RSRL.Interpretation.exists_small_embedding`). A model in any universe therefore witnesses
satisfiability (`HPSG.RSRL.Grammar.isSatisfiable_of_models`), and an entailed description holds
in the models of every universe (`HPSG.RSRL.Grammar.Entails.mem_denotation`).

A model is *exhaustive* when it realizes every theory that is satisfiable over the grammar.

## Implementation notes

The models are well-typed, as the interpretations of [richter-2024] are by definition; here
well-typedness is a predicate on interpretations, since a worked example interprets part of a
feature structure, so the two notions name it. They do not require the models to be
sort-resolved: the sort hierarchies of the fragments are partial, as those of their sources are,
and an entity may bear a sort whose subsorts the fragment does not list.

`FirstOrder.Language.Theory.IsSatisfiable` and `FirstOrder.Language.Theory.ModelsBoundedFormula`
are the first-order notions, which fix a universe in the same way and remove the choice with the
Löwenheim–Skolem theorem. Here the quantifiers of a formula range over the components of the
described entity, so the generated sub-interpretation does that work.

## References

* [richter-2000]
* [richter-2024]
-/

@[expose] public section

namespace HPSG.RSRL

universe u v

variable {Srt : Type u} [PartialOrder Srt] {Sig : Signature Srt} {U : Type v}

namespace Interpretation

variable (I : Interpretation Sig U) {V : Type*}

/-! ### Transport along a bijection -/

/-- The interpretation on `V` that a bijection with the universe of `I` carries over. -/
def map (e : U ≃ V) : Interpretation Sig V where
  S v := I.S (e.symm v)
  A α v := (I.A α (e.symm v)).map e
  R ρ := {xs | e.symm ∘ xs ∈ I.R ρ}

/-- The inverse of the bijection embeds the transported interpretation in the original. -/
def mapEmbedding (e : U ≃ V) : Embedding (I.map e) I where
  toEmbedding := e.symm.toEmbedding
  map_S' _ := rfl
  map_A' α v := by simp [map, Option.map_map]
  map_R' _ _ := Iff.rfl

@[simp] theorem coe_mapEmbedding (e : U ≃ V) : ⇑(I.mapEmbedding e) = e.symm := rfl

/-! ### Small models -/

/-- The components of an entity form a set no larger than the signature, since each is reached
by a path. -/
instance small_isComponentOf (r : U) : Small.{u} {v // I.IsComponentOf r v} :=
  small_of_surjective (α := {p : Path Sig // (I.eval r p).isSome})
    (f := fun p ↦ ⟨(I.eval r p.1).get p.2,
      reaches_toPartialMoore_iff.1 ⟨p.1, Option.some_get p.2 |>.symm⟩⟩)
    fun ⟨v, hv⟩ ↦
      let ⟨p, hp⟩ := reaches_toPartialMoore_iff.2 hv
      ⟨⟨p, by rw [eval, hp]; rfl⟩, Subtype.ext (by simp [eval, hp])⟩

variable {I} in
/-- Every entity of an interpretation is the image of an entity of an interpretation in the
universe of the signature that embeds in it. -/
theorem exists_small_embedding (r : U) :
    ∃ (V : Type u) (J : Interpretation Sig V) (f : Embedding J I) (r' : V), f r' = r :=
  ⟨_, (I.generated r).map (equivShrink _),
    (I.generatedEmbedding r).comp ((I.generated r).mapEmbedding (equivShrink _)),
    equivShrink _ ⟨r, .refl⟩, by simp⟩

end Interpretation

namespace Grammar

variable {G H : Grammar Sig} {θ θ' : Set (Description Sig)} {d : Description Sig}

/-! ### Satisfiability -/

/-- A theory is satisfiable over a grammar when, in some well-typed model of the grammar, some
entity is described by every description of the theory. -/
def IsSatisfiable (G : Grammar Sig) (θ : Set (Description Sig)) : Prop :=
  ∃ (U : Type u) (I : Interpretation Sig U),
    I.IsWellTyped ∧ I.Models G ∧ (I.theoryDenotation θ).Nonempty

/-- A well-typed model in any universe with an entity that a theory describes shows the theory
satisfiable. -/
theorem isSatisfiable_of_models {I : Interpretation Sig U} (hw : I.IsWellTyped)
    (hI : I.Models G) (hθ : (I.theoryDenotation θ).Nonempty) : G.IsSatisfiable θ :=
  let ⟨r, hr⟩ := hθ
  let ⟨V, J, f, r', hr'⟩ := Interpretation.exists_small_embedding r
  ⟨V, J, Interpretation.HomClass.isWellTyped f hw, f.models hI,
    r', f.apply_mem_theoryDenotation.1 (hr' ▸ hr)⟩

theorem IsSatisfiable.mono (h : H.IsSatisfiable θ') (hG : G ⊆ H) (hθ : θ ⊆ θ') :
    G.IsSatisfiable θ :=
  let ⟨U, I, hw, hI, r, hr⟩ := h
  ⟨U, I, hw, hI.mono hG, r, fun d hd ↦ hr d (hθ hd)⟩

/-- The descriptions that state a list of atoms are satisfiable together when the atoms hold of
one entity of a well-typed model. -/
theorem isSatisfiable_image_toDescription_iff {as : List (PathAtom Sig)} :
    G.IsSatisfiable (PathAtom.toDescription '' {a | a ∈ as}) ↔
      ∃ (U : Type u) (I : Interpretation Sig U), I.IsWellTyped ∧ I.Models G ∧
        ∃ r, ∀ a ∈ as, a.Holds I r := by
  simp only [IsSatisfiable, Set.Nonempty, Interpretation.mem_theoryDenotation,
    Set.forall_mem_image, Set.mem_ofPred_eq, Interpretation.mem_denotation_iff,
    PathAtom.toDescription_toFormula, Interpretation.satisfies_toFormula_pathAtom]

/-! ### Entailment -/

/-- A grammar entails a description when the description describes every entity of every
well-typed model of the grammar. -/
def Entails (G : Grammar Sig) (d : Description Sig) : Prop :=
  ∀ ⦃U : Type u⦄ (I : Interpretation Sig U), I.IsWellTyped → I.Models G → ∀ r, r ∈ I.denotation d

/-- A description that a grammar entails describes every entity of its well-typed models in
every universe. -/
theorem Entails.mem_denotation (h : G.Entails d) {I : Interpretation Sig U}
    (hw : I.IsWellTyped) (hI : I.Models G) (r : U) : r ∈ I.denotation d :=
  let ⟨_, J, f, r', hr'⟩ := Interpretation.exists_small_embedding r
  hr' ▸ f.apply_mem_denotation.2
    (h J (Interpretation.HomClass.isWellTyped f hw) (f.models hI) r')

theorem entails_of_mem (h : d ∈ G) : G.Entails d :=
  fun _ _ _ hI r g ↦ hI d h g r

theorem Entails.mono (h : G.Entails d) (hG : G ⊆ H) : H.Entails d :=
  fun _ I hw hI ↦ h I hw (hI.mono hG)

/-- A grammar that entails every principle of another entails what the other entails. -/
theorem Entails.trans (hG : ∀ e ∈ H, G.Entails e) (h : H.Entails d) : G.Entails d :=
  fun _ I hw hI ↦ h I hw fun e he g r ↦ hG e he I hw hI r g

/-- A grammar entails a constraint exactly when the atoms of the constraint hold of every entity
of its sort in every well-typed model. -/
theorem entails_toDescription_iff {c : Constraint Sig} :
    G.Entails c.toDescription ↔ ∀ ⦃U : Type u⦄ (I : Interpretation Sig U),
      I.IsWellTyped → I.Models G → ∀ r, I.S r ≤ c.sort → ∀ a ∈ c.atoms, a.Holds I r := by
  simp only [Entails, Interpretation.mem_denotation_iff, Constraint.toDescription_toFormula,
    Interpretation.satisfies_toFormula]

/-- The atoms of a constraint that a grammar entails hold of every entity of its sort in the
well-typed models of every universe. -/
theorem Entails.holds {c : Constraint Sig} (h : G.Entails c.toDescription)
    {I : Interpretation Sig U} (hw : I.IsWellTyped) (hI : I.Models G) {r : U}
    (hr : I.S r ≤ c.sort) {a : PathAtom Sig} (ha : a ∈ c.atoms) : a.Holds I r :=
  Interpretation.satisfies_toFormula.1
    (Interpretation.mem_denotation_iff.1 (h.mem_denotation hw hI r)) hr a ha

/-- A satisfiable theory stays satisfiable when a description that the grammar entails is added
to it. -/
theorem IsSatisfiable.insert (hθ : G.IsSatisfiable θ) (h : G.Entails d) :
    G.IsSatisfiable (insert d θ) :=
  let ⟨U, I, hw, hI, r, hr⟩ := hθ
  ⟨U, I, hw, hI, r, fun e he ↦ he.elim (fun he ↦ he ▸ h I hw hI r) (hr e)⟩

end Grammar

/-! ### Exhaustive models -/

namespace Interpretation

variable (I : Interpretation Sig U) {G : Grammar Sig}

/-- A model of a grammar is exhaustive when every theory that is satisfiable over the grammar
describes one of its entities ([richter-2024], Definition 19). -/
structure IsExhaustive (G : Grammar Sig) : Prop where
  /-- An exhaustive model is a model. -/
  models : I.Models G
  /-- A satisfiable theory describes an entity of an exhaustive model. -/
  nonempty_theoryDenotation (θ : Set (Description Sig)) :
    G.IsSatisfiable θ → (I.theoryDenotation θ).Nonempty

variable {I}

/-- A model of a grammar into which an exhaustive model embeds is exhaustive. -/
theorem Embedding.isExhaustive {V : Type*} {J : Interpretation Sig V} (f : Embedding I J)
    (hI : I.IsExhaustive G) (hJ : J.Models G) : J.IsExhaustive G :=
  ⟨hJ, fun θ hθ ↦
    let ⟨r, hr⟩ := hI.nonempty_theoryDenotation θ hθ
    ⟨f r, f.apply_mem_theoryDenotation.2 hr⟩⟩

end Interpretation

end HPSG.RSRL
