module

public import Linglib.Semantics.Composition.Effect
public import Linglib.Semantics.Composition.Basic

/-!
# The effect-driven grammar

Bumford and Charlow's grammar takes whatever basic modes of combination a theory has and closes
them under meta-modes, each lifting a mode through an effect by the structure the effect has: Map
Left and Map Right by its map, Structured App and the Unit modes where it is applicative, Join
where it is a monad, Co-unit and Eject for the adjunction of storing and reading, and Lower for a
continuation at its own result type. The types of two daughters decide which modes combine them,
and `Ty.combine` is their procedure for listing them. Daughters of types without effects
combine by a basic mode only, so [over a lexicon without effects the grammar gives the values of
the rules it started from](##Interpreter.values_effectDriven_of_effectFree).

## Main definitions

* `Interpreter.Mode`: the basic modes closed under the meta-modes.
* `Interpreter.Mode.eval`: the meaning of a mode, by the operations of the effects.
* `Interpreter.Ty.combine`: the modes their `combine` finds for two types.
* `Interpreter.Ty.Evaluated`: the types with no continuation still to be closed.
* `Interpreter.effectGrammar`: the grammar whose binary rules are the modes over a grammar's
  rules, with its structure.
* `Interpreter.effectDriven`: their interpreter, which admits every mode `Ty.combine` finds
  and at an island only those with an evaluated result.
* `Interpreter.Ty.EffectFree`, `ManySorted.Language.EffectFree`: the types with no effect in
  them, and the grammars whose rules keep to those types.

## Implementation notes

`Ty.combine` follows Bumford and Charlow's `combine` rule for rule and in its order. Like
theirs, it applies Join and Lower once to each way of combining two daughters, so it does not
list every mode: one that joins twice is a mode of the grammar that it does not find. The two
Eject rules do not make their types smaller. An Eject leaves a computation where there was an
arrow, so neither applies twice to one daughter, and the recursion is on a bound, three steps for
each unit of size.

## TODO

* That `Ty.combineAux` is the same at every bound from `3 * (l.size + r.size) + 3` on is not
  proved.
* A statement of what `Ty.combine` does find, every mode in which no Join or Lower is applied to
  a Join or a Lower, is not proved.

## References

* [bumford-charlow-2026]
-/

@[expose] public section

open ManySorted

namespace Interpreter

variable {B : Type}

/-- The modes of combination: a theory's basic modes closed under the meta-modes. -/
inductive Mode (Rule : Ty B → Ty B → Ty B → Type) : Ty B → Ty B → Ty B → Type
  /-- A basic mode. -/
  | basic {l r u : Ty B} (b : Rule l r u) : Mode Rule l r u
  /-- Map Right: a mode under the effect of the right daughter. -/
  | mapR {f : Eff B} {l r u : Ty B} (m : Mode Rule l r u) : Mode Rule l (.comp f r) (.comp f u)
  /-- Map Left: a mode under the effect of the left daughter. -/
  | mapL {f : Eff B} {l r u : Ty B} (m : Mode Rule l r u) : Mode Rule (.comp f l) r (.comp f u)
  /-- Structured App: a mode on the results of two daughters with one applicative effect. -/
  | ap {f : Eff B} {l r u : Ty B} (h : f.IsApplicative) (m : Mode Rule l r u) :
      Mode Rule (.comp f l) (.comp f r) (.comp f u)
  /-- Unit Right: a left daughter expecting a computation is given a pure one. -/
  | unitR {f : Eff B} {l l' r u : Ty B} (h : f.IsApplicative) (m : Mode Rule (l ⇒ l') r u) :
      Mode Rule (.comp f l ⇒ l') r u
  /-- Unit Left: a right daughter expecting a computation is given a pure one. -/
  | unitL {f : Eff B} {l r r' u : Ty B} (h : f.IsApplicative) (m : Mode Rule l (r ⇒ r') u) :
      Mode Rule l (.comp f r ⇒ r') u
  /-- Co-unit: what the left daughter stores is given to what the right daughter reads. -/
  | counit {i l r u : Ty B} (m : Mode Rule l r u) : Mode Rule (.comp (.W i) l) (.comp (.R i) r) u
  /-- Eject Right: reading is ejected from a right daughter that is a function into a reader. -/
  | ejectR {i l r r' u : Ty B} (m : Mode Rule l (.comp (.R i) (r ⇒ r')) u) :
      Mode Rule l (r ⇒ .comp (.R i) r') u
  /-- Eject Left: reading is ejected from a left daughter that is a function into a reader. -/
  | ejectL {i l l' r u : Ty B} (m : Mode Rule (.comp (.R i) (l ⇒ l')) r u) :
      Mode Rule (l ⇒ .comp (.R i) l') r u
  /-- Join: two layers of one monadic effect in the result are flattened. -/
  | join {f : Eff B} {l r u : Ty B} (h : f.IsApplicative)
      (m : Mode Rule l r (.comp f (.comp f u))) : Mode Rule l r (.comp f u)
  /-- Lower: a continuation at its own result type in the result is run at the identity. -/
  | lower {l r u : Ty B} (m : Mode Rule l r (.comp (.C u) u)) : Mode Rule l r u

namespace Mode

variable {Rule : Ty B → Ty B → Ty B → Type}

/-- The meaning of a mode over a grammar's rules, from a structure for the grammar: each
meta-mode is the operation of its effect. -/
def eval {G : Language (Ty B)} (D : B → Type) [M : G.Structure (Ty.Dom D)] :
    {l r u : Ty B} → Mode G.Binary l r u → l.Dom D → r.Dom D → u.Dom D
  | _, _, _, .basic b, x, y => M.funMap b (x, y)
  | _, _, _, .mapR (f := f) m, a, b => Eff.map f (fun y ↦ m.eval D a y) b
  | _, _, _, .mapL (f := f) m, a, b => Eff.map f (fun x ↦ m.eval D x b) a
  | _, _, _, .ap (f := f) h m, a, b =>
    Eff.seq f h (Eff.map f (fun x y ↦ m.eval D x y) a) b
  | _, _, _, .unitR (f := f) h m, a, b => m.eval D (fun x ↦ a (Eff.pure f h x)) b
  | _, _, _, .unitL (f := f) h m, a, b => m.eval D a fun y ↦ b (Eff.pure f h y)
  | _, _, _, .counit (i := i) m, a, b =>
    Eff.counit (Eff.map (.W i) (fun x ↦ Eff.map (.R i) (fun y ↦ m.eval D x y) b) a)
  | _, _, _, .ejectR m, a, b => m.eval D a (Eff.eject b)
  | _, _, _, .ejectL m, a, b => m.eval D (Eff.eject a) b
  | _, _, _, .join (f := f) h m, a, b => Eff.join f h (m.eval D a b)
  | _, _, _, .lower m, a, b => Eff.lower (m.eval D a b)

end Mode

section Combine

variable [DecidableEq B] {Rule : Ty B → Ty B → Ty B → Type}
  (find : (l r : Ty B) → List (Σ u, Rule l r u))

/-- The Join of a mode whose result has two layers of one monadic effect. -/
def Mode.joins {l r : Ty B} : (Σ u, Mode Rule l r u) → List (Σ u, Mode Rule l r u)
  | ⟨.comp f (.comp g a), m⟩ =>
    if h : g = f then
      if ha : f.IsApplicative then [⟨.comp f a, .join ha (h ▸ m)⟩] else []
    else []
  | _ => []

/-- The Lower of a mode whose result is a continuation at its own result type. -/
def Mode.lowers {l r : Ty B} : (Σ u, Mode Rule l r u) → List (Σ u, Mode Rule l r u)
  | ⟨.comp (.C o) a, m⟩ => if h : o = a then [⟨a, .lower (h ▸ m)⟩] else []
  | _ => []

/-- `Ty.combine` to a bound on the depth of its recursion. Every rule but the two Ejects recurses
on smaller types, and an Eject turns an arrow into a computation, so at most one Eject on each
daughter comes between two rules that shrink a type. -/
def Ty.combineAux : ℕ → (l r : Ty B) → List (Σ u, Mode Rule l r u)
  | 0, _, _ => []
  | k + 1, l, r =>
    (((find l r).map fun p ↦ (⟨p.1, .basic p.2⟩ : Σ u, Mode Rule l r u)) ++
      (match r with
        | .comp f y => (Ty.combineAux k l y).map fun p ↦ ⟨.comp f p.1, .mapR p.2⟩
        | _ => []) ++
      (match l with
        | .comp f x => (Ty.combineAux k x r).map fun p ↦ ⟨.comp f p.1, .mapL p.2⟩
        | _ => []) ++
      (match l, r with
        | .comp f x, .comp g y =>
          if h : g = f then
            if ha : f.IsApplicative then
              (Ty.combineAux k x y).map fun p ↦ ⟨.comp f p.1, by subst h; exact .ap ha p.2⟩
            else []
          else []
        | _, _ => []) ++
      (match l with
        | .fn (.comp f x) x' =>
          if ha : f.IsApplicative then
            (Ty.combineAux k (x ⇒ x') r).map fun p ↦ ⟨p.1, .unitR ha p.2⟩
          else []
        | _ => []) ++
      (match r with
        | .fn (.comp f y) y' =>
          if ha : f.IsApplicative then
            (Ty.combineAux k l (y ⇒ y')).map fun p ↦ ⟨p.1, .unitL ha p.2⟩
          else []
        | _ => []) ++
      (match l, r with
        | .comp (.W i) x, .comp (.R j) y =>
          if h : j = i then (Ty.combineAux k x y).map fun p ↦ ⟨p.1, h ▸ .counit p.2⟩ else []
        | _, _ => []) ++
      (match r with
        | .fn x (.comp (.R i) y) =>
          (Ty.combineAux k l (.comp (.R i) (x ⇒ y))).map fun p ↦ ⟨p.1, .ejectR p.2⟩
        | _ => []) ++
      (match l with
        | .fn x (.comp (.R i) y) =>
          (Ty.combineAux k (.comp (.R i) (x ⇒ y)) r).map fun p ↦ ⟨p.1, .ejectL p.2⟩
        | _ => [])).flatMap fun p ↦ p :: (Mode.joins p ++ Mode.lowers p)

/-- The modes Bumford and Charlow's `combine` finds for a left daughter of type `l` and a right
daughter of type `r`: each way of peeling effects off the two types down to a basic rule, and
its Join and its Lower where the result allows one. -/
def Ty.combine (l r : Ty B) : List (Σ u, Mode Rule l r u) :=
  Ty.combineAux find (3 * (l.size + r.size) + 3) l r

end Combine

/-- A type is evaluated when no continuation in it is still to be closed. -/
def Ty.Evaluated : Ty B → Prop
  | .comp (.C _) _ => False
  | .comp .S a | .comp (.R _) a | .comp (.W _) a | .comp .M a => a.Evaluated
  | .fn _ b => b.Evaluated
  | .t | .base _ => True

instance Ty.decidableEvaluated : (a : Ty B) → Decidable a.Evaluated
  | .comp (.C _) _ => isFalse id
  | .comp .S a | .comp (.R _) a | .comp (.W _) a | .comp .M a => decidableEvaluated a
  | .fn _ b => decidableEvaluated b
  | .t | .base _ => isTrue trivial

/-- The effect-driven grammar over a grammar: its type shifts, and the modes over its rules. -/
def effectGrammar (G : Language (Ty B)) : Language (Ty B) := .mk₂ G.Unary (Mode G.Binary)

/-- The structure of the effect-driven grammar over a grammar, from a structure for the
grammar: a type shift means what it does there, and a mode what the effects make of the rules. -/
instance effectGrammar.structure {G : Language (Ty B)} {D : B → Type}
    [M : G.Structure (Ty.Dom D)] : (effectGrammar G).Structure (Ty.Dom D) :=
  .mk₂ (fun s x ↦ M.funMap s x) fun m ↦ m.eval D

/-- Bumford and Charlow's effect-driven interpreter over a grammar: a node admits the type
shifts of the grammar and every mode that `Ty.combine` finds for its daughters, and an island
only the modes whose result is evaluated. -/
def effectDriven [DecidableEq B] (G : Language (Ty B)) [G.LocallyFinite] :
    Interpreter (effectGrammar G) Node where
  unary _ := Language.LocallyFinite.unaryRules (L := G)
  binary
    | .island, l, r =>
      (Ty.combine (Language.LocallyFinite.binaryRules (L := G)) l r).filter (·.1.Evaluated)
    | _, l, r => Ty.combine (Language.LocallyFinite.binaryRules (L := G)) l r

/-! ### Conservativity over the types without effects -/

/-- A type with no effect anywhere in it. -/
def Ty.EffectFree : Ty B → Prop
  | .t | .base _ => True
  | .fn a b => a.EffectFree ∧ b.EffectFree
  | .comp _ _ => False

/-- A type without effects has no continuation to close. -/
theorem Ty.EffectFree.evaluated : ∀ {a : Ty B}, a.EffectFree → a.Evaluated
  | .t, _ | .base _, _ => trivial
  | .fn _ _, h => h.2.evaluated

/-- A grammar keeps to the types without effects when its rules give daughters of such types a
mother of one. -/
structure _root_.ManySorted.Language.EffectFree (G : Language (Ty B)) : Prop where
  /-- The type shifts. -/
  unary {a b : Ty B} : G.Unary a b → a.EffectFree → b.EffectFree
  /-- The modes of combination. -/
  binary {l r u : Ty B} : G.Binary l r u → l.EffectFree → r.EffectFree → u.EffectFree

/-- Daughters of types without effects combine by a basic mode only: every meta-mode needs an
effect in a daughter, or a basic mode whose result has one. -/
theorem Mode.exists_eq_basic {Rule : Ty B → Ty B → Ty B → Type}
    (hR : ∀ {l r u : Ty B}, Rule l r u → l.EffectFree → r.EffectFree → u.EffectFree) :
    ∀ {l r u : Ty B} (m : Mode Rule l r u), l.EffectFree → r.EffectFree → ∃ b, m = .basic b
  | _, _, _, .basic b, _, _ => ⟨b, rfl⟩
  | _, _, _, .mapR _, _, hr => hr.elim
  | _, _, _, .mapL _, hl, _ => hl.elim
  | _, _, _, .ap _ _, hl, _ => hl.elim
  | _, _, _, .unitR _ _, hl, _ => hl.1.elim
  | _, _, _, .unitL _ _, _, hr => hr.1.elim
  | _, _, _, .counit _, hl, _ => hl.elim
  | _, _, _, .ejectR _, _, hr => hr.2.elim
  | _, _, _, .ejectL _, hl, _ => hl.2.elim
  | _, _, _, .join _ m, hl, hr => by
    obtain ⟨b, rfl⟩ := Mode.exists_eq_basic hR m hl hr
    exact (hR b hl hr).elim
  | _, _, _, .lower m, hl, hr => by
    obtain ⟨b, rfl⟩ := Mode.exists_eq_basic hR m hl hr
    exact (hR b hl hr).elim

/-- For daughters of types without effects `Ty.combine` finds the basic rules and nothing
else. -/
theorem Ty.combine_of_effectFree [DecidableEq B] {Rule : Ty B → Ty B → Ty B → Type}
    {find : (l r : Ty B) → List (Σ u, Rule l r u)}
    (hR : ∀ {l r u : Ty B}, Rule l r u → l.EffectFree → r.EffectFree → u.EffectFree)
    {l r : Ty B} (hl : l.EffectFree) (hr : r.EffectFree) :
    Ty.combine find l r = (find l r).map fun p ↦ ⟨p.1, .basic p.2⟩ := by
  have hj (p : Σ u, Rule l r u) : (⟨p.1, .basic p.2⟩ : Σ u, Mode Rule l r u) ::
      (Mode.joins ⟨p.1, .basic p.2⟩ ++ Mode.lowers ⟨p.1, .basic p.2⟩) = [⟨p.1, .basic p.2⟩] := by
    obtain ⟨u, b⟩ := p
    have hu := hR b hl hr
    rcases u with _ | _ | _ | _
    · rfl
    · rfl
    · rfl
    · exact hu.elim
  have hbasic : ((find l r).map fun p ↦ (⟨p.1, .basic p.2⟩ : Σ u, Mode Rule l r u)).flatMap
      (fun p ↦ p :: (Mode.joins p ++ Mode.lowers p)) =
      (find l r).map fun p ↦ ⟨p.1, .basic p.2⟩ := by
    rw [List.flatMap_map]
    simp only [hj]
    exact List.map_eq_flatMap.symm
  rw [← hbasic]
  unfold Ty.combine
  rw [show 3 * (l.size + r.size) + 3 = (3 * (l.size + r.size) + 2) + 1 from rfl]
  generalize 3 * (l.size + r.size) + 2 = k
  rw [Ty.combineAux]
  congr 1
  all_goals simp_all
  all_goals
    intros; intro h; subst h
    first
    | exact hl.elim | exact hr.elim | exact hl.1.elim | exact hl.2.elim
    | exact hr.1.elim | exact hr.2.elim

/-- Over a lexicon whose items have types without effects, the values a grammar that keeps to
such types gives a bare structure have types without effects. -/
theorem EffectFree.of_mem_values {G : Language (Ty B)} [G.LocallyFinite] (hG : G.EffectFree)
    {D : Ty B → Type} (M : G.Structure D) {Lx : Type} {W : Ty B → Type}
    (ρ : ∀ {a : Ty B}, W a → D a) {lex : Lx → List (Σ a, W a)}
    (hlex : ∀ x, ∀ p ∈ lex x, p.1.EffectFree) :
    ∀ (s : Skeleton Node Lx), ∀ d ∈ (typeDriven G).values M ρ lex s, d.1.EffectFree
  | .leaf x, d, hd => by
    rw [values_leaf] at hd
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hd
    exact hlex x p hp
  | .unary n s, d, hd => by
    rw [values_unary] at hd
    obtain ⟨e, he, hd⟩ := List.mem_flatMap.1 hd
    obtain ⟨r, -, rfl⟩ := List.mem_map.1 hd
    exact hG.unary r.2 (EffectFree.of_mem_values hG M ρ hlex s e he)
  | .binary n s₁ s₂, d, hd => by
    rw [values_binary] at hd
    obtain ⟨e₁, he₁, hd⟩ := List.mem_flatMap.1 hd
    obtain ⟨e₂, he₂, hd⟩ := List.mem_flatMap.1 hd
    obtain ⟨m, -, rfl⟩ := List.mem_map.1 hd
    exact hG.binary m.2 (EffectFree.of_mem_values hG M ρ hlex s₁ e₁ he₁)
      (EffectFree.of_mem_values hG M ρ hlex s₂ e₂ he₂)

/-- **The effect-driven grammar is conservative.** Over a lexicon whose items have types without
effects, the effect-driven interpreter over a grammar that keeps to such types gives each bare
structure the values the grammar's own type-driven interpreter gives it, in the same order: the
meta-modes add no reading, and remove none. -/
theorem values_effectDriven_of_effectFree [DecidableEq B] {G : Language (Ty B)}
    [G.LocallyFinite] (hG : G.EffectFree) {D : B → Type} [M : G.Structure (Ty.Dom D)]
    {Lx : Type} {W : Ty B → Type} (ρ : ∀ {a : Ty B}, W a → a.Dom D)
    {lex : Lx → List (Σ a, W a)} (hlex : ∀ x, ∀ p ∈ lex x, p.1.EffectFree) :
    ∀ s : Skeleton Node Lx, (effectDriven G).values effectGrammar.structure ρ lex s =
      (typeDriven G).values M ρ lex s
  | .leaf x => by rw [values_leaf, values_leaf]
  | .unary n s => by
    rw [values_unary, values_unary, values_effectDriven_of_effectFree hG ρ hlex s]
    rfl
  | .binary n s₁ s₂ => by
    rw [values_binary, values_binary, values_effectDriven_of_effectFree hG ρ hlex s₁,
      values_effectDriven_of_effectFree hG ρ hlex s₂]
    refine List.flatMap_congr fun d₁ h₁ ↦ List.flatMap_congr fun d₂ h₂ ↦ ?_
    have hl := EffectFree.of_mem_values hG M ρ hlex s₁ d₁ h₁
    have hr := EffectFree.of_mem_values hG M ρ hlex s₂ d₂ h₂
    have hc : (effectDriven G).binary n d₁.1 d₂.1 =
        (Language.LocallyFinite.binaryRules (L := G) d₁.1 d₂.1).map
          fun p ↦ ⟨p.1, .basic p.2⟩ := by
      cases n with
      | island =>
        simp only [effectDriven, Ty.combine_of_effectFree hG.binary hl hr]
        refine List.filter_eq_self.2 fun p hp ↦ ?_
        obtain ⟨q, -, rfl⟩ := List.mem_map.1 hp
        exact decide_eq_true (hG.binary q.2 hl hr).evaluated
      | branch => simp only [effectDriven, Ty.combine_of_effectFree hG.binary hl hr]
      | index k => simp only [effectDriven, Ty.combine_of_effectFree hG.binary hl hr]
    rw [hc, List.map_map]
    rfl

end Interpreter
