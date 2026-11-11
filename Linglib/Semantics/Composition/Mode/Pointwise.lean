module

public import Linglib.Semantics.Composition.Mode.Combine

/-!
# The pointwise grammar of an effect

In Heim and Kratzer's grammar every constituent is evaluated at an assignment, and in a Hamblin
grammar every constituent denotes a set of alternatives; two sisters are combined at one
assignment, or alternative by alternative. Bumford and Charlow read these as the grammar that has,
at the effect in question, Structured App and no other meta-mode. In such a grammar two daughters
carrying the effect [combine by Structured App alone](##Interpreter.Mode.Within.exists_eq_ap),
so [the ways they combine are the ways their results
do](##Interpreter.Ty.mem_combineWithin_pointwise), and Structured App is the pointwise rule of
the effect: [evaluation at one
datum](##Interpreter.Mode.eval_ap_R) for reading, [Hamblin's
rule](##Interpreter.Mode.eval_ap_S) for indeterminacy, and [Rooth's](##Interpreter.Mode.eval_ap_F)
for alternatives.

## Main definitions

* `Interpreter.MetaMode.pointwise`: the inventory with Structured App alone at the effects of a
  given kind, and every meta-mode at the others.

## Implementation notes

A pointwise grammar also has every lexical item carry the effect. That is a condition on a
lexicon and is not stated here; `Interpreter.Mode.Within.exists_eq_ap` is about two daughters that
do carry it.

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

/-- In a grammar pointwise at `f`, with no basic rule for two daughters carrying `f`, the modes
the search lists for the two are the Structured Apps of the modes it lists for the types of their
results. -/
theorem _root_.Interpreter.Ty.mem_combineWithin_pointwise [DecidableEq B] [DecidablePred P]
    {find : (l r : Ty B) → List (Sigma (Rule l r))}
    (hfind : ∀ {l r u : Ty B} (b : Rule l r u), (⟨u, b⟩ : Sigma (Rule l r)) ∈ find l r)
    (hf : P f) (ha : f.IsApplicative)
    (hR : ∀ {u : Ty B}, Rule (.comp f l) (.comp f r) u → False)
    {m : Sigma (Mode Rule (.comp f l) (.comp f r))} :
    m ∈ Ty.combineWithin (MetaMode.pointwise P) find (.comp f l) (.comp f r) ↔
      ∃ m' ∈ Ty.combineWithin (MetaMode.pointwise P) find l r,
        m = ⟨.comp f m'.1, .ap ha m'.2⟩ := by
  have key {l r : Ty B} {m : Sigma (Mode Rule l r)} :=
    Ty.mem_combineWithin (inv := MetaMode.pointwise P) (find := find) (fun b ↦ hfind b)
      (l := l) (r := r) (m := m)
  obtain ⟨u, m⟩ := m
  refine key.trans ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨u', _, m', hm', he⟩ := Within.exists_eq_ap hf hR m h
    exact ⟨⟨u', m'⟩, key.2 hm', he⟩
  · rintro ⟨m', hm', he⟩
    cases he
    exact ⟨fun _ ↦ rfl, key.1 hm'⟩

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

end Interpreter
