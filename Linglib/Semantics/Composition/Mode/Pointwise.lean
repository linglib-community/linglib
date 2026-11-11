module

public import Linglib.Semantics.Composition.Mode.Combine
public import Linglib.Semantics.Composition.Constituency

/-!
# The pointwise grammar of an effect

A grammar is pointwise at an effect when its inventory has Structured App and no other meta-mode
there: the grammars in which every constituent is evaluated at an assignment, or denotes a set of
alternatives, are essentially of this kind. Two daughters that carry the effect then [combine by
Structured App alone](##Interpreter.Mode.Within.exists_eq_ap), [the search lists for them the
Structured Apps of what it lists for their results](##Interpreter.Ty.combineWithin_pointwise),
and over a lexicon whose every item carries the effect [a tree has its values in the structure on
computations](##PhraseStructure.Tree.values_effectDrivenWithin_pointwise). Structured App is
[evaluation at one datum](##Interpreter.Mode.eval_ap_R) at reading, where the structure on
computations [is the structure on functions of the
datum](##Interpreter.effectGrammar.pointwise_R), [Hamblin's
rule](##Interpreter.Mode.eval_ap_S) at indeterminacy and [Rooth's](##Interpreter.Mode.eval_ap_F)
at alternatives.

## Main definitions

* `Interpreter.MetaMode.pointwise`: the inventory with Structured App alone at the effects of a
  given kind, and every meta-mode at the others.
* `Interpreter.effectGrammar.pointwise`: the structure of the effect-driven grammar on the
  computations of an applicative effect.

## Implementation notes

An inventory is pointwise at some effects and has every meta-mode at the others, where each of
the two grammars above has one effect. The tree-level statement is for a lexicon whose every
item carries the effect, so it does not cover a tree with an operator that takes a computation
as its argument, as a closure operator does. It is for a grammar with no type shifts. A type
shift on a computation, such as abstraction over an index, is not the shift on its result mapped
over the effect, and the effect-driven grammar has no meta-mode that maps one.

## References

* [bumford-charlow-2026]
* [heim-kratzer-1998]
* [hamblin-1973b]
* [rooth-1985]
-/

@[expose] public section

open ManySorted

namespace Interpreter

variable {B : Type}

/-- The inventory of the grammar that is pointwise at the effects satisfying `P`: at those
effects it has Structured App and no other meta-mode, and at the others every meta-mode. -/
def MetaMode.pointwise (P : Eff B → Prop) : MetaMode → Eff B → Prop := fun k f ↦ P f → k = .ap

instance (P : Eff B → Prop) [DecidablePred P] (k : MetaMode) (f : Eff B) :
    Decidable (MetaMode.pointwise P k f) :=
  inferInstanceAs (Decidable (P f → k = .ap))

namespace Mode

variable {Rule : Ty B → Ty B → Ty B → Type} {P : Eff B → Prop} {f : Eff B} {l r : Ty B}

/-- In a grammar pointwise at `f`, with no basic rule for two daughters carrying `f`, the two
combine by Structured App alone, of a mode of the grammar for the types of their results. -/
theorem Within.exists_eq_ap (hf : P f)
    [hR : ∀ u : Ty B, IsEmpty (Rule (.comp f l) (.comp f r) u)] :
    ∀ {u : Ty B} (m : Mode Rule (.comp f l) (.comp f r) u), m.Within (MetaMode.pointwise P) →
      ∃ (u' : Ty B) (ha : f.IsApplicative) (m' : Mode Rule l r u'),
        m'.Within (MetaMode.pointwise P) ∧
          (⟨u, m⟩ : Sigma (Mode Rule (.comp f l) (.comp f r))) = ⟨.comp f u', .ap m' ha⟩
  | _, .basic b, _ => isEmptyElim b
  | _, .mapR _, h => absurd (h.1 hf) (by decide)
  | _, .mapL _, h => absurd (h.1 hf) (by decide)
  | _, .ap m ha, h => ⟨_, ha, m, h.2, rfl⟩
  | _, .join m _, h => by
    obtain ⟨u', _, m', _, he⟩ := Within.exists_eq_ap hf m h.2
    obtain ⟨rfl, -⟩ := Ty.comp.inj (congrArg Sigma.fst he)
    exact absurd (h.1 hf) (by decide)
  | _, .lower m, h => by
    obtain ⟨u', _, m', _, he⟩ := Within.exists_eq_ap hf m h.2
    obtain ⟨rfl, -⟩ := Ty.comp.inj (congrArg Sigma.fst he)
    exact absurd (h.1 hf) (by decide)

/-- In a grammar pointwise at `f`, with no basic rule for daughters of types `.comp f l` and
`.comp f r`, the modes listed for them are `.ap m` for the modes `m` listed for `l` and `r`, in
the same order. -/
theorem _root_.Interpreter.Ty.combineWithin_pointwise [DecidableEq B] [DecidablePred P]
    {find : (l r : Ty B) → List (Sigma (Rule l r))} (hf : P f) [ha : f.IsApplicative]
    (hfind : find (.comp f l) (.comp f r) = []) :
    Ty.combineWithin (MetaMode.pointwise P) find (.comp f l) (.comp f r) =
      (Ty.combineWithin (MetaMode.pointwise P) find l r).map fun p ↦
        ⟨.comp f p.1, .ap p.2 ha⟩ := by
  have hk {k : MetaMode} (h : k ≠ .ap) : ¬ MetaMode.pointwise P k f := fun h' ↦ h (h' hf)
  have hap : MetaMode.pointwise P .ap f := fun _ ↦ rfl
  rw [Ty.combineWithin, Ty.combineWith_eq_combineStep, Ty.combineStep, hfind]
  cases f <;>
    simp only [List.map_nil, List.nil_append, List.append_nil, hk (by decide : MetaMode.map ≠ .ap),
      hap, ha, ↓reduceIte, ↓reduceDIte]
  all_goals
    rw [List.flatMap_map, List.map_eq_flatMap]
    exact List.flatMap_congr fun p hp ↦ Mode.filter_within_closure_eq_singleton
      ⟨hap, Ty.within_of_mem_combineWithin hp⟩ (hk (by decide)) (hk (by decide))

variable {G : Language (Ty B)} {D : B → Type} [M : G.Structure (Ty.Dom D)] {u : Ty B}

/-- Structured App at reading evaluates the two daughters at one datum, as Heim and Kratzer's
rules do at one assignment. -/
theorem eval_ap_R {i : Ty B} (m : Mode G.Binary l r u) (a : (Ty.comp (.R i) l).Dom D)
    (b : (Ty.comp (.R i) r).Dom D) :
    (Mode.ap (f := .R i) m).eval D a b = fun j ↦ m.eval D (a j) (b j) := rfl

/-- Structured App at indeterminacy combines each alternative of one daughter with each of the
other: Hamblin's rule. -/
theorem eval_ap_S (m : Mode G.Binary l r u) (a : (Ty.comp .S l).Dom D)
    (b : (Ty.comp .S r).Dom D) :
    (Mode.ap (f := .S) m).eval D a b = Set.image2 (m.eval D) a b :=
  (Set.image2_eq_seq _ a b).symm

/-- Structured App at alternatives combines the ordinary values, and each alternative of one
daughter with each of the other: Rooth's rule. -/
theorem eval_ap_F (m : Mode G.Binary l r u) (a : (Ty.comp .F l).Dom D)
    (b : (Ty.comp .F r).Dom D) :
    (Mode.ap (f := .F) m).eval D a b = WithAlternatives.map₂ (m.eval D) a b :=
  (WithAlternatives.map₂_eq_seq _ a b).symm

end Mode

theorem binary_effectDrivenWithin_pointwise [DecidableEq B] {P : Eff B → Prop} [DecidablePred P]
    {G : Language (Ty B)} [G.LocallyFinite] {N : Type} {f : Eff B} (hf : P f)
    [ha : f.IsApplicative] {l r : Ty B}
    [∀ u : Ty B, IsEmpty (G.Binary (.comp f l) (.comp f r) u)] :
    (effectDrivenWithin (MetaMode.pointwise P) G : Interpreter (effectGrammar G) N).binary
        (.comp f l) (.comp f r) =
      ((effectDrivenWithin (MetaMode.pointwise P) G : Interpreter (effectGrammar G) N).binary
        l r).map fun p ↦ ⟨.comp f p.1, .ap p.2 ha⟩ :=
  Ty.combineWithin_pointwise hf (List.eq_nil_iff_forall_not_mem.2 fun p _ ↦ isEmptyElim p.2)

/-! ### The pointwise grammar as a grammar on computations -/

namespace Eff

variable {D : B → Type}

/-- The computation of the arguments of a shape from a computation of each, the effects of the
earlier arguments first. -/
def sequence (f : Eff B) [h : f.IsApplicative] :
    (σ : Signature (Ty B)) → σ.Interpret (fun a ↦ (Ty.comp f a).Dom D) →
      Obj D f (σ.Interpret (Ty.Dom D))
  | .nil, _ => pure f h PUnit.unit
  | .of _, x => x
  | .prod σ τ, x => seq f h (map f Prod.mk (sequence f σ x.1)) (sequence f τ x.2)

end Eff

/-- The structure of the effect-driven grammar on the computations of an applicative effect: a
mode means Structured App of it, and any other symbol applies its function to the computed
arguments. For reading these are the values that depend on the datum read, and for indeterminacy
the sets of values. -/
@[instance_reducible] def effectGrammar.pointwise {G : Language (Ty B)} {D : B → Type}
    [M : G.Structure (Ty.Dom D)] (f : Eff B) [h : f.IsApplicative] :
    (effectGrammar G).Structure fun a ↦ (Ty.comp f a).Dom D :=
  Language.Structure.withBinary
    ⟨fun g x ↦ Eff.map f (M.funMap g) (Eff.sequence f _ x)⟩
    fun m x y ↦ (Mode.ap m h).eval D x y

/-- At reading, the computation of the arguments of a shape is the arguments at each datum. -/
theorem Eff.sequence_R {D : B → Type} (i : Ty B) :
    ∀ (σ : Signature (Ty B)) (x : σ.Interpret fun a ↦ (Ty.comp (.R i) a).Dom D),
      Eff.sequence (.R i) σ x = fun j ↦ Signature.Interpret.app x j
  | .nil, _ => rfl
  | .of _, _ => rfl
  | .prod σ τ, x => by
    rw [Eff.sequence, Eff.sequence_R i σ, Eff.sequence_R i τ]
    rfl

/-- At reading, the structure on computations is the structure of the effect-driven grammar on
the values that depend on the datum read, in which Heim and Kratzer's sisters combine at one
assignment. -/
theorem effectGrammar.pointwise_R {G : Language (Ty B)} {D : B → Type}
    [M : G.Structure (Ty.Dom D)] (i : Ty B) :
    effectGrammar.pointwise (G := G) (D := D) (.R i) =
      (effectGrammar.structure (G := G) (D := D)).pi (i.Dom D) := by
  refine congrArg Language.Structure.mk ?_
  funext σ _ g x
  match σ, g with
  | .prod (.of _) (.of _), _ => rfl
  | .nil, g | .of _, g | .prod .nil _, g | .prod (.prod _ _) _, g | .prod (.of _) .nil, g
  | .prod (.of _) (.prod _ _), g =>
    exact congrArg (Eff.map (.R i) (M.funMap g)) (Eff.sequence_R i _ x)

end Interpreter

namespace PhraseStructure.Tree

open ManySorted.Language Interpreter

variable {B : Type} [DecidableEq B] {P : Eff B → Prop} [DecidablePred P] {G : Language (Ty B)}
  [G.LocallyFinite] {D : B → Type} [M : G.Structure (Ty.Dom D)] {C Lx : Type}
  {W W' : Ty B → Type} {f : Eff B}

/-- In a grammar pointwise at `f`, with no type shift and no basic rule for two daughters that
carry `f`, the values of a tree over a lexicon whose items all carry `f` are its values in
`effectGrammar.pointwise f` over the results of the items. -/
theorem values_effectDrivenWithin_pointwise [∀ a b : Ty B, IsEmpty (G.Unary a b)]
    [∀ l r u : Ty B, IsEmpty (G.Binary (.comp f l) (.comp f r) u)] (hf : P f)
    [ha : f.IsApplicative]
    {ρ : ∀ {a : Ty B}, W a → (Ty.comp f a).Dom D} {ρ' : ∀ {a : Ty B}, W' a → a.Dom D}
    {lex : Lx ⊕ ℕ → List (Sigma W)} {lex' : Lx ⊕ ℕ → List (Sigma W')}
    (hlex : ∀ x, (lex' x).map (fun p ↦ (⟨p.1, ρ' p.2⟩ : Sigma (Ty.Dom D))) =
      (lex x).map fun p ↦ ⟨.comp f p.1, ρ p.2⟩)
    (t : Tree C Lx) :
    t.values (effectDrivenWithin (MetaMode.pointwise P) G) effectGrammar.structure ρ' lex' =
      (t.values (effectDrivenWithin (MetaMode.pointwise P) G) (effectGrammar.pointwise f)
        ρ lex).map fun d ↦ ⟨.comp f d.1, d.2⟩ := by
  have hU (a : Ty B) : Language.LocallyFinite.unaryRules (L := G) a = [] :=
    List.eq_nil_iff_forall_not_mem.2 fun p _ ↦ isEmptyElim p.2
  refine values_eq_map_of_types (Ty.comp f) (fun _ ↦ True) hlex (fun _ _ _ ↦ trivial)
    (fun _ _ _ _ ↦ by simp [effectDrivenWithin, hU]) (fun _ _ _ _ _ ↦ trivial)
    (fun _ _ _ _ _ _ ↦ ?_) (fun _ _ _ _ _ _ ↦ trivial) t
  rw [binary_effectDrivenWithin_pointwise hf, List.map_map]
  rfl

end PhraseStructure.Tree
