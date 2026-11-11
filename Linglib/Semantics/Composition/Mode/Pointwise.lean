module

public import Linglib.Semantics.Composition.Mode.Combine
public import Linglib.Semantics.Composition.Constituency

/-!
# The pointwise grammar of an effect

In Heim and Kratzer's grammar every constituent is evaluated at an assignment, and in a Hamblin
grammar every constituent denotes a set of alternatives; two sisters are combined at one
assignment, or alternative by alternative. Bumford and Charlow read these as the grammar that has,
at the effect in question, Structured App and no other meta-mode. In such a grammar two daughters
carrying the effect [combine by Structured App alone](##Interpreter.Mode.Within.exists_eq_ap), so
[the search lists for them the Structured Apps of what it lists for their
results](##Interpreter.Ty.combineWithin_pointwise), and over a lexicon whose every item carries
the effect [a tree is interpreted in the structure on
computations](##PhraseStructure.Tree.values_effectDrivenWithin_pointwise). Structured App is the
pointwise rule of the effect: [evaluation at one datum](##Interpreter.Mode.eval_ap_R) for
reading, [Hamblin's rule](##Interpreter.Mode.eval_ap_S) for indeterminacy, and
[Rooth's](##Interpreter.Mode.eval_ap_F) for alternatives.

## Main definitions

* `Interpreter.MetaMode.pointwise`: the inventory with Structured App alone at the effects of a
  given kind, and every meta-mode at the others.
* `Interpreter.effectGrammar.pointwise`: the structure of the effect-driven grammar on the
  computations of an applicative effect.

## Implementation notes

The tree-level statement is for a grammar with no type shifts. A type shift on a computation,
such as abstraction over an index, is not the shift on its result mapped over the effect, and
the effect-driven grammar has no meta-mode that maps one.

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
    (hR : ∀ {u : Ty B}, Rule (.comp f l) (.comp f r) u → False) :
    ∀ {u : Ty B} (m : Mode Rule (.comp f l) (.comp f r) u), m.Within (MetaMode.pointwise P) →
      ∃ (u' : Ty B) (ha : f.IsApplicative) (m' : Mode Rule l r u'),
        m'.Within (MetaMode.pointwise P) ∧
          (⟨u, m⟩ : Sigma (Mode Rule (.comp f l) (.comp f r))) = ⟨.comp f u', .ap ha m'⟩
  | _, .basic b, _ => (hR b).elim
  | _, .mapR _, h => absurd (h.1 hf) (by decide)
  | _, .mapL _, h => absurd (h.1 hf) (by decide)
  | _, .ap ha m, h => ⟨_, ha, m, h.2, rfl⟩
  | _, .join _ m, h => by
    obtain ⟨u', _, m', _, he⟩ := Within.exists_eq_ap hf hR m h.2
    obtain ⟨rfl, -⟩ := Ty.comp.inj (congrArg Sigma.fst he)
    exact absurd (h.1 hf) (by decide)
  | _, .lower m, h => by
    obtain ⟨u', _, m', _, he⟩ := Within.exists_eq_ap hf hR m h.2
    obtain ⟨rfl, -⟩ := Ty.comp.inj (congrArg Sigma.fst he)
    exact absurd (h.1 hf) (by decide)

/-- **The pointwise node.** In a grammar pointwise at `f`, with no basic rule for two daughters
carrying `f`, the search lists for the two the Structured Apps of the modes it lists for the
types of their results, in the same order. -/
theorem _root_.Interpreter.Ty.combineWithin_pointwise [DecidableEq B] [DecidablePred P]
    {find : (l r : Ty B) → List (Sigma (Rule l r))} (hf : P f) (ha : f.IsApplicative)
    (hfind : find (.comp f l) (.comp f r) = []) :
    Ty.combineWithin (MetaMode.pointwise P) find (.comp f l) (.comp f r) =
      (Ty.combineWithin (MetaMode.pointwise P) find l r).map fun p ↦
        ⟨.comp f p.1, .ap ha p.2⟩ := by
  have hk {k : MetaMode} (h : k ≠ .ap) : ¬ MetaMode.pointwise P k f := fun h' ↦ h (h' hf)
  have hap : MetaMode.pointwise P .ap f := fun _ ↦ rfl
  rw [Ty.combineWithin, Ty.combineWith_eq_combineStep, Ty.combineStep, hfind]
  cases f <;>
    simp only [List.map_nil, List.nil_append, List.append_nil, hk (by decide : MetaMode.map ≠ .ap),
      hap, ha, ↓reduceIte, ↓reduceDIte]
  all_goals
    rw [List.flatMap_map, List.map_eq_flatMap]
    exact List.flatMap_congr fun p hp ↦ Mode.filter_within_closure
      ⟨hap, Ty.within_of_mem_combineWithin hp⟩ (hk (by decide)) (hk (by decide))

/-- In a grammar pointwise at `f`, with no basic rule for two daughters carrying `f`, a mode is
listed for the two exactly when it is Structured App of a mode listed for the types of their
results. -/
theorem _root_.Interpreter.Ty.mem_combineWithin_pointwise [DecidableEq B] [DecidablePred P]
    {find : (l r : Ty B) → List (Sigma (Rule l r))} (hf : P f) (ha : f.IsApplicative)
    (hfind : find (.comp f l) (.comp f r) = [])
    {m : Sigma (Mode Rule (.comp f l) (.comp f r))} :
    m ∈ Ty.combineWithin (MetaMode.pointwise P) find (.comp f l) (.comp f r) ↔
      ∃ m' ∈ Ty.combineWithin (MetaMode.pointwise P) find l r,
        m = ⟨.comp f m'.1, .ap ha m'.2⟩ := by
  rw [Ty.combineWithin_pointwise hf ha hfind, List.mem_map]
  exact exists_congr fun _ ↦ and_congr_right fun _ ↦ eq_comm

variable {G : Language (Ty B)} {D : B → Type} [M : G.Structure (Ty.Dom D)] {u : Ty B}

/-- Structured App at reading evaluates the two daughters at one datum, as Heim and Kratzer's
rules do at one assignment. -/
theorem eval_ap_R {i : Ty B} (m : Mode G.Binary l r u) (a : (Ty.comp (.R i) l).Dom D)
    (b : (Ty.comp (.R i) r).Dom D) :
    (Mode.ap (f := .R i) trivial m).eval D a b = fun j ↦ m.eval D (a j) (b j) := rfl

/-- Structured App at indeterminacy combines each alternative of one daughter with each of the
other: Hamblin's rule. -/
theorem eval_ap_S (m : Mode G.Binary l r u) (a : (Ty.comp .S l).Dom D)
    (b : (Ty.comp .S r).Dom D) :
    (Mode.ap (f := .S) trivial m).eval D a b = Set.image2 (m.eval D) a b :=
  (Set.image2_eq_seq _ a b).symm

/-- Structured App at alternatives combines the ordinary values, and each alternative of one
daughter with each of the other: Rooth's rule. -/
theorem eval_ap_F (m : Mode G.Binary l r u) (a : (Ty.comp .F l).Dom D)
    (b : (Ty.comp .F r).Dom D) :
    (Mode.ap (f := .F) trivial m).eval D a b = WithAlternatives.map₂ (m.eval D) a b :=
  (WithAlternatives.map₂_eq_seq _ a b).symm

end Mode

/-- At two daughters carrying `f`, with no basic rule for them, the interpreter of a grammar
pointwise at `f` admits the Structured Apps of the modes it admits for the types of their
results. -/
theorem binary_effectDrivenWithin_pointwise [DecidableEq B] {P : Eff B → Prop} [DecidablePred P]
    {G : Language (Ty B)} [G.LocallyFinite] {N : Type} {f : Eff B} (hf : P f)
    (ha : f.IsApplicative) {l r : Ty B}
    (hG : ∀ {u : Ty B}, G.Binary (.comp f l) (.comp f r) u → False) :
    (effectDrivenWithin (MetaMode.pointwise P) G : Interpreter (effectGrammar G) N).binary
        (.comp f l) (.comp f r) =
      ((effectDrivenWithin (MetaMode.pointwise P) G : Interpreter (effectGrammar G) N).binary
        l r).map fun p ↦ ⟨.comp f p.1, .ap ha p.2⟩ :=
  Ty.combineWithin_pointwise hf ha (List.eq_nil_iff_forall_not_mem.2 fun p _ ↦ hG p.2)

/-! ### The pointwise grammar as a grammar on computations -/

namespace Eff

variable {D : B → Type}

/-- Computations of the arguments of a shape as one computation of the arguments, the effects of
the earlier arguments first. -/
def sequence (f : Eff B) (h : f.IsApplicative) :
    (σ : Signature (Ty B)) → σ.Interpret (fun a ↦ (Ty.comp f a).Dom D) →
      Obj D f (σ.Interpret (Ty.Dom D))
  | .nil, _ => pure f h PUnit.unit
  | .of _, x => x
  | .prod σ τ, x => seq f h (map f Prod.mk (sequence f h σ x.1)) (sequence f h τ x.2)

end Eff

/-- The structure of the effect-driven grammar on the computations of an applicative effect: a
mode means Structured App of it, and any other symbol applies its function to the computed
arguments. For reading these are the values that depend on the datum read, and for indeterminacy
the sets of values. -/
@[instance_reducible] def effectGrammar.pointwise {G : Language (Ty B)} {D : B → Type}
    [M : G.Structure (Ty.Dom D)] (f : Eff B) (h : f.IsApplicative) :
    (effectGrammar G).Structure fun a ↦ (Ty.comp f a).Dom D :=
  Language.Structure.withBinary
    ⟨fun g x ↦ Eff.map f (M.funMap g) (Eff.sequence f h _ x)⟩
    fun m x y ↦ (Mode.ap h m).eval D x y

end Interpreter

namespace PhraseStructure.Tree

open ManySorted.Language Interpreter

variable {B : Type} [DecidableEq B] {P : Eff B → Prop} [DecidablePred P] {G : Language (Ty B)}
  [G.LocallyFinite] {D : B → Type} [M : G.Structure (Ty.Dom D)] {C Lx : Type}
  {W W' : Ty B → Type} {f : Eff B}

/-- **A pointwise grammar is the grammar on computations.** Take a grammar pointwise at `f`, with
no type shifts and no basic rule for two daughters carrying `f`, and a lexicon whose every item
carries `f`. The values of a tree are then its values over the results of the items in the
structure on computations, where every node means Structured App of the mode that combines the
results: the effects of the words are merged into one layer at each node. -/
theorem values_effectDrivenWithin_pointwise [∀ a b : Ty B, IsEmpty (G.Unary a b)] (hf : P f)
    (ha : f.IsApplicative)
    (hG : ∀ {l r u : Ty B}, G.Binary (.comp f l) (.comp f r) u → False)
    {ρ : ∀ {a : Ty B}, W a → (Ty.comp f a).Dom D} {ρ' : ∀ {a : Ty B}, W' a → a.Dom D}
    {lex : Lx ⊕ ℕ → List (Sigma W)} {lex' : Lx ⊕ ℕ → List (Sigma W')}
    (hlex : ∀ x, (lex' x).map (fun p ↦ (⟨p.1, ρ' p.2⟩ : Sigma (Ty.Dom D))) =
      (lex x).map fun p ↦ ⟨.comp f p.1, ρ p.2⟩)
    (t : Tree C Lx) :
    t.values (effectDrivenWithin (MetaMode.pointwise P) G) effectGrammar.structure ρ' lex' =
      (t.values (effectDrivenWithin (MetaMode.pointwise P) G) (effectGrammar.pointwise f ha)
        ρ lex).map fun d ↦ ⟨.comp f d.1, d.2⟩ := by
  rw [values_eq_fold, values_eq_fold]
  refine RoseTree.rel_fold
    (fun (X : List (Sigma (Ty.Dom D))) (Y : List (Σ a : Ty B, (Ty.comp f a).Dom D)) ↦
      X = Y.map fun d ↦ ⟨.comp f d.1, d.2⟩) (fun l Xs Ys h ↦ ?_) t
  match l, Xs, Ys, h with
  | .terminal _ w, [], [], _ =>
    show (lex' _).map _ = ((lex _).map _).map _
    rw [List.map_map]
    exact hlex _
  | .trace n _, [], [], _ =>
    show (lex' _).map _ = ((lex _).map _).map _
    rw [List.map_map]
    exact hlex _
  | .bind n _, [_], [Y], .cons rfl .nil =>
    have hnil {α β : Type} (l : List α) : l.flatMap (fun _ ↦ ([] : List β)) = [] :=
      List.flatMap_eq_nil_iff.2 fun _ _ ↦ rfl
    have hU (a : Ty B) : Language.LocallyFinite.unaryRules (L := G) a = [] :=
      List.eq_nil_iff_forall_not_mem.2 fun p _ ↦ isEmptyElim p.2
    simp [nodeValues, unaryValues, effectDrivenWithin, hU, hnil]
  | .phrase _ _, [_], [Y], .cons h .nil => exact h
  | .phrase _ _, [_, _], [Y₁, Y₂], .cons rfl (.cons rfl .nil) =>
    simp only [nodeValues, binaryValues, List.flatMap_map, List.map_flatMap]
    refine List.flatMap_congr fun ⟨a, x⟩ _ ↦ List.flatMap_congr fun ⟨b, y⟩ _ ↦ ?_
    rw [binary_effectDrivenWithin_pointwise hf ha hG, List.map_map, List.map_map]
    rfl
  | .terminal _ _, _ :: _, _ :: _, _ | .trace _ _, _ :: _, _ :: _, _ | .bind _ _, [], [], _
  | .bind _ _, _ :: _ :: _, _ :: _ :: _, _ | .phrase _ _, [], [], _
  | .phrase _ _, _ :: _ :: _ :: _, _ :: _ :: _ :: _, _ => rfl

end PhraseStructure.Tree
