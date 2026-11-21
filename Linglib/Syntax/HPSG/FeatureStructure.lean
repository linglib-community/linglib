module

public import Linglib.Syntax.HPSG.Interpretation
public import Mathlib.Computability.DFA

/-!
# Feature structures and subsumption

An interpretation with a distinguished entity `u` is a feature structure: its nodes are the
components of `u`, each with a sort, and each attribute is a partial function on them. Read as a
machine, it is a partial deterministic automaton over the attributes that starts at `u`
(`HPSG.RSRL.Interpretation.toDFA`), and the value of a path at `u` is the state the automaton
reaches on it (`HPSG.RSRL.Interpretation.eval_toDFA`).

One feature structure subsumes another, `I.Subsumes J u v`, when a map of the components of `u`
sends `u` to `v`, sends each entity to one of an at least as specific sort, and preserves each
attribute where it is defined: the second carries all the information of the first. Subsumption
is reflexive and transitive, and a homomorphism of interpretations is a subsumption that also
keeps sorts and reflects attributes (`HPSG.RSRL.Interpretation.Hom.subsumes`).

The abstract feature structure of `u`, `I.abs u`, records the sort at the end of each path
defined at `u` and which pairs of paths lead to the same entity. Abstract feature structures are
partially ordered by information, a greater one defining more paths, with more specific sorts,
and identifying more of them, and subsumption is that order
(`HPSG.RSRL.Interpretation.subsumes_iff_abs_le`). Entities that subsume each other have the same
abstract feature structure (`HPSG.RSRL.Interpretation.abs_eq_iff`), whether or not they are the
same entity, and two entities are unifiable when their abstract feature structures have a common
upper bound.

## Implementation notes

A subsumption may make a sort more specific and may meet attributes its source lacks, so it
orders feature structures by information. A homomorphism (`HPSG.RSRL.Interpretation.Hom`) keeps
the sort and has an attribute defined on an image exactly when it is defined on the source, so
it preserves the satisfaction of descriptions. The two are kept apart.

In the sort hierarchy of a signature the more specific sort is the lesser. The order of abstract
feature structures has more information greater, as the orders of feature bundles and of flat
slots do, so that an inclusion of information reverses the order of the sorts.

The states of the automaton are `Option U`, with `none` the value of an undefined path, since
mathlib's `DFA` has a total transition function.

## References

* [kasper-rounds-1990]
* [carpenter-1992]
-/

@[expose] public section

namespace HPSG.RSRL

universe u v w

variable {Srt : Type u} [PartialOrder Srt] {Sig : Signature Srt} {U : Type v} {V : Type w}
  {W : Type*}

namespace Interpretation

variable (I : Interpretation Sig U) (J : Interpretation Sig V) (K : Interpretation Sig W)

/-! ### The automaton of an entity -/

/-- The partial deterministic automaton of the entity `u`: it starts at `u`, follows an
attribute where the attribute is defined, and accepts the paths that are defined at `u`. -/
def toDFA (u : U) : DFA Sig.Attr (Option U) where
  step s α := s.bind (I.A α)
  start := some u
  accept := {s | s.isSome}

@[simp] theorem toDFA_step (u : U) (s : Option U) (α : Sig.Attr) :
    (I.toDFA u).step s α = s.bind (I.A α) := rfl

@[simp] theorem toDFA_start (u : U) : (I.toDFA u).start = some u := rfl

variable {I J K} {u : U} {v : V} {w : W}

/-- Following a path from an entity is running the entity's automaton on it. -/
theorem eval_toDFA (g : ℕ → U) (u : U) (p : Path Sig) :
    (I.toDFA u).eval p = I.termDenot g (.path p) u := by
  induction p using List.reverseRecOn with
  | nil => rfl
  | append_singleton p α ih =>
    rw [DFA.eval_append_singleton, toDFA_step, ih, Term.path_concat, termDenot_feat]

/-- The components of an entity are the states its automaton reaches. -/
theorem isComponentOf_iff_exists_eval {q : U} :
    I.IsComponentOf u q ↔ ∃ p : Path Sig, (I.toDFA u).eval p = some q := by
  simp only [eval_toDFA fun _ ↦ u]
  exact isComponentOf_iff_exists_path _

/-! ### Subsumption -/

variable (I J) in
/-- The feature structure of `u` in `I` subsumes that of `v` in `J` when a map of the components
of `u` sends `u` to `v`, sends each entity to one of an at least as specific sort, and preserves
each attribute where it is defined ([carpenter-1992], Definition 3.4). -/
def Subsumes (u : U) (v : V) : Prop :=
  ∃ h : U → V, h u = v ∧ (∀ q, I.IsComponentOf u q → J.S (h q) ≤ I.S q) ∧
    ∀ α q q', I.IsComponentOf u q → I.A α q = some q' → J.A α (h q) = some (h q')

private theorem isComponentOf_map {h : U → V}
    (hA : ∀ α q q', I.IsComponentOf u q → I.A α q = some q' → J.A α (h q) = some (h q')) {q : U}
    (hq : I.IsComponentOf u q) : J.IsComponentOf (h u) (h q) := by
  induction hq with
  | refl => exact .refl
  | tail hq hs ih =>
    obtain ⟨α, hα⟩ := hs
    exact ih.tail ⟨α, hA α _ _ hq hα⟩

private theorem eval_map {h : U → V}
    (hA : ∀ α q q', I.IsComponentOf u q → I.A α q = some q' → J.A α (h q) = some (h q'))
    (p : Path Sig) : ∀ {q : U}, (I.toDFA u).eval p = some q →
      (J.toDFA (h u)).eval p = some (h q) := by
  induction p using List.reverseRecOn with
  | nil =>
    intro q hq
    obtain rfl : u = q := Option.some.inj hq
    rfl
  | append_singleton p α ih =>
    intro q' hq'
    rw [DFA.eval_append_singleton, toDFA_step] at hq' ⊢
    obtain ⟨q, hq, hα⟩ := Option.bind_eq_some_iff.1 hq'
    rw [ih hq]
    exact hA α q q' (isComponentOf_iff_exists_eval.2 ⟨p, hq⟩) hα

theorem Subsumes.refl (I : Interpretation Sig U) (u : U) : I.Subsumes I u u :=
  ⟨id, rfl, fun _ _ ↦ le_rfl, fun _ _ _ _ h ↦ h⟩

theorem Subsumes.trans (h₁ : I.Subsumes J u v) (h₂ : J.Subsumes K v w) : I.Subsumes K u w := by
  obtain ⟨f, rfl, hS, hA⟩ := h₁
  obtain ⟨g, rfl, hS', hA'⟩ := h₂
  exact ⟨g ∘ f, rfl, fun q hq ↦ (hS' _ (isComponentOf_map hA hq)).trans (hS q hq),
    fun α q q' hq hα ↦ hA' α _ _ (isComponentOf_map hA hq) (hA α q q' hq hα)⟩

/-- A homomorphism, which keeps sorts and reflects attributes, is a subsumption. -/
theorem Hom.subsumes (f : Hom I J) (u : U) : I.Subsumes J u (f u) :=
  ⟨f, rfl, fun q _ ↦ (HomClass.map_S f q).le, fun α q q' _ hα ↦ by
    rw [HomClass.map_A, hα]; rfl⟩

end Interpretation

/-! ### Abstract feature structures -/

/-- An abstract feature structure gives the sort at the end of each defined path and the pairs of
paths that lead to the same entity ([carpenter-1992], Definition 3.8). -/
@[ext] structure AbstractFeatureStructure (Sig : Signature Srt) where
  /-- The sort at the end of a path, where the path is defined. -/
  sort : Path Sig → Option Srt
  /-- Two paths lead to the same entity. -/
  Equiv : Path Sig → Path Sig → Prop

namespace AbstractFeatureStructure

/-- An abstract feature structure is below another when the second defines every path the first
does, with an at least as specific sort, and identifies every two paths the first does. -/
instance : PartialOrder (AbstractFeatureStructure Sig) where
  le F G := (∀ p σ, F.sort p = some σ → ∃ τ, G.sort p = some τ ∧ τ ≤ σ) ∧
    ∀ p p', F.Equiv p p' → G.Equiv p p'
  le_refl _ := ⟨fun _ σ h ↦ ⟨σ, h, le_rfl⟩, fun _ _ h ↦ h⟩
  le_trans _ _ _ h₁ h₂ := ⟨fun p σ h ↦
    let ⟨τ, hτ, hle⟩ := h₁.1 p σ h
    let ⟨ρ, hρ, hle'⟩ := h₂.1 p τ hτ
    ⟨ρ, hρ, hle'.trans hle⟩, fun p p' h ↦ h₂.2 p p' (h₁.2 p p' h)⟩
  le_antisymm F G h₁ h₂ := by
    ext p q
    · constructor
      · intro hp
        obtain ⟨τ, hτ, hle⟩ := h₁.1 p q hp
        obtain ⟨σ, hσ, hle'⟩ := h₂.1 p τ hτ
        obtain rfl : σ = q := Option.some.inj (hσ.symm.trans hp)
        rw [hτ, le_antisymm hle hle']
      · intro hp
        obtain ⟨τ, hτ, hle⟩ := h₂.1 p q hp
        obtain ⟨σ, hσ, hle'⟩ := h₁.1 p τ hτ
        obtain rfl : σ = q := Option.some.inj (hσ.symm.trans hp)
        rw [hτ, le_antisymm hle hle']
    · exact ⟨h₁.2 p q, h₂.2 p q⟩

theorem le_def {F G : AbstractFeatureStructure Sig} :
    F ≤ G ↔ (∀ p σ, F.sort p = some σ → ∃ τ, G.sort p = some τ ∧ τ ≤ σ) ∧
      ∀ p p', F.Equiv p p' → G.Equiv p p' := Iff.rfl

end AbstractFeatureStructure

namespace Interpretation

variable (I : Interpretation Sig U) {J : Interpretation Sig V}

/-- The abstract feature structure of an entity: the sort its automaton reaches on each path,
and the pairs of paths on which it reaches the same entity. -/
def abs (u : U) : AbstractFeatureStructure Sig where
  sort p := ((I.toDFA u).eval p).map I.S
  Equiv p p' := ∃ q, (I.toDFA u).eval p = some q ∧ (I.toDFA u).eval p' = some q

variable {I} {u : U} {v : V}

/-- Subsumption depends only on the abstract feature structures ([carpenter-1992],
Theorem 3.9). -/
theorem subsumes_iff_abs_le : I.Subsumes J u v ↔ I.abs u ≤ J.abs v := by
  constructor
  · rintro ⟨h, rfl, hS, hA⟩
    refine ⟨fun p σ hp ↦ ?_, fun p p' ⟨q, hq, hq'⟩ ↦ ⟨h q, eval_map hA p hq, eval_map hA p' hq'⟩⟩
    obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.1 hp
    exact ⟨J.S (h q), by simp [abs, eval_map hA p hq],
      hS q (isComponentOf_iff_exists_eval.2 ⟨p, hq⟩)⟩
  · rintro ⟨hsort, hequiv⟩
    classical
    have key : ∀ p q, (I.toDFA u).eval p = some q → ∃ q', (J.toDFA v).eval p = some q' ∧
        J.S q' ≤ I.S q := fun p q hq ↦ by
      obtain ⟨τ, hτ, hle⟩ := hsort p (I.S q) (by simp [abs, hq])
      obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.1 hτ
      exact ⟨q', hq', hle⟩
    let h : U → V := fun q ↦
      if hq : ∃ p, (I.toDFA u).eval p = some q then (key _ q hq.choose_spec).choose else v
    have hh : ∀ p q, (I.toDFA u).eval p = some q → (J.toDFA v).eval p = some (h q) := by
      intro p q hq
      have hex : ∃ p, (I.toDFA u).eval p = some q := ⟨p, hq⟩
      obtain ⟨q'', h₁, h₂⟩ := hequiv hex.choose p ⟨q, hex.choose_spec, hq⟩
      have h₃ := (key _ q hex.choose_spec).choose_spec.1
      simp only [h, hex, ↓reduceDIte]
      exact h₂.trans (h₁.symm.trans h₃)
    refine ⟨h, Option.some.inj ((hh [] u rfl).symm.trans rfl), fun q hq ↦ ?_,
      fun α q q' hq hα ↦ ?_⟩
    · obtain ⟨p, hp⟩ := isComponentOf_iff_exists_eval.1 hq
      obtain ⟨q', hq', hle⟩ := key p q hp
      rwa [Option.some.inj ((hh p q hp).symm.trans hq')]
    · obtain ⟨p, hp⟩ := isComponentOf_iff_exists_eval.1 hq
      have h₁ := hh (p ++ [α]) q' (by rw [DFA.eval_append_singleton, toDFA_step, hp]; exact hα)
      rwa [DFA.eval_append_singleton, toDFA_step, hh p q hp] at h₁

/-- Entities have the same abstract feature structure exactly when they subsume each other. -/
theorem abs_eq_iff : I.abs u = J.abs v ↔ I.Subsumes J u v ∧ J.Subsumes I v u := by
  rw [subsumes_iff_abs_le, subsumes_iff_abs_le, le_antisymm_iff]

end Interpretation

end HPSG.RSRL
