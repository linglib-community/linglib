module

public import Linglib.Semantics.Composition.Mode.Basic
public import Linglib.Semantics.Composition.Rules
public import Mathlib.Logic.Relator

/-!
# Relations lifted through types and effects

A relation between two families of base domains extends to every type: at the truth values it is
equivalence, at a function type it relates functions that take related arguments to related
values, and at a computation type it is the relation its effect lifts. Each operation of an effect
respects the lifted relations, so [every mode does](##Interpreter.Mode.rel_eval), and the
relation is a [logical relation between the two structures of the effect-driven
grammar](##Interpreter.effectGrammar.isLogicalRel): related lexicons give every derivation
related values.

## Main definitions

* `Interpreter.Ty.LiftRel`, `Interpreter.Eff.LiftRel`: a relation between base domains, at a type
  and through an effect.
* `Interpreter.Eff.rel_map` and its siblings: each operation of an effect respects the relations.

## TODO

The basic lemma of logical relations is the statement that terms stay inside a substructure, at
the product of two structures. The many-sorted layer has neither products nor substructures.

## References

* [bumford-charlow-2026]
-/

@[expose] public section

open ManySorted

namespace Interpreter

open Relator

variable {B : Type} {D D' : B → Type}

/-- The datum of an effect: what a reader reads, a store holds, or a continuation returns. -/
abbrev Eff.Datum (D : B → Type) : Eff B → Type
  | .R i | .W i | .C i => i.Dom D
  | .S | .M | .F => Unit

/-- A relation between results through an effect, given a relation between its data:
alternatives matched on each side, readers that agree at related data, stored pairs related in
both parts, continuations that agree at related continuations, partial values defined together
and then related, and focused values related with their alternatives matched on each side. -/
def Eff.RelWith : (f : Eff B) → (f.Datum D → f.Datum D' → Prop) → {α β : Type} →
    (α → β → Prop) → Eff.Obj D f α → Eff.Obj D' f β → Prop
  | .S, _, _, _, q => fun s s' ↦ (∀ a ∈ s, ∃ b ∈ s', q a b) ∧ ∀ b ∈ s', ∃ a ∈ s, q a b
  | .R _, rd, _, _, q => LiftFun rd q
  | .W _, rd, _, _, q => fun x y ↦ q x.1 y.1 ∧ rd x.2 y.2
  | .C _, rd, _, _, q => LiftFun (LiftFun q rd) rd
  | .M, _, _, _, q => fun x y ↦ (x.Dom ↔ y.Dom) ∧ ∀ hx hy, q (x.get hx) (y.get hy)
  | .F, _, _, _, q => fun x y ↦ q x.ordinary y.ordinary ∧
    (∀ a ∈ x.alternatives, ∃ b ∈ y.alternatives, q a b) ∧
      ∀ b ∈ y.alternatives, ∃ a ∈ x.alternatives, q a b

mutual

/-- A relation between two families of base domains, at a type. -/
def Ty.LiftRel (r : ∀ b, D b → D' b → Prop) (a : Ty B) : a.Dom D → a.Dom D' → Prop :=
  match a with
  | .t => Iff
  | .base b => r b
  | .fn a b => LiftFun (Ty.LiftRel r a) (Ty.LiftRel r b)
  | .comp f a => Eff.RelWith f (Eff.DatumRel r f) (Ty.LiftRel r a)
termination_by structural a

/-- A relation between two families of base domains, at the datum of an effect. -/
def Eff.DatumRel (r : ∀ b, D b → D' b → Prop) (f : Eff B) : f.Datum D → f.Datum D' → Prop :=
  match f with
  | .R i | .W i | .C i => Ty.LiftRel r i
  | .S | .M | .F => fun _ _ ↦ True
termination_by structural f

end

/-- A relation between results, through an effect. -/
abbrev Eff.LiftRel (r : ∀ b, D b → D' b → Prop) (f : Eff B) {α β : Type} (R : α → β → Prop) :
    Eff.Obj D f α → Eff.Obj D' f β → Prop :=
  Eff.RelWith f (Eff.DatumRel r f) R

namespace Eff

variable {r : ∀ b, D b → D' b → Prop} {α α' β β' : Type} {R : α → α' → Prop}
  {S : β → β' → Prop}

theorem rel_map (f : Eff B) :
    LiftFun (LiftFun R S) (LiftFun (LiftRel r f R) (LiftRel r f S)) (map f) (map f) := by
  intro g g' hg x x' hx
  cases f with
  | S =>
    refine ⟨?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩
      obtain ⟨b, hb, hab⟩ := hx.1 a ha
      exact ⟨g' b, ⟨b, hb, rfl⟩, hg hab⟩
    · rintro _ ⟨b, hb, rfl⟩
      obtain ⟨a, ha, hab⟩ := hx.2 b hb
      exact ⟨g a, ⟨a, ha, rfl⟩, hg hab⟩
  | R i => exact fun _ _ hi ↦ hg (hx hi)
  | W o => exact ⟨hg hx.1, hx.2⟩
  | C o => exact fun _ _ hc ↦ hx fun _ _ hab ↦ hc (hg hab)
  | M => exact ⟨hx.1, fun hx₁ hx₂ ↦ hg (hx.2 hx₁ hx₂)⟩
  | F =>
    refine ⟨hg hx.1, fun _ hy ↦ ?_, fun _ hy ↦ ?_⟩
    · obtain ⟨a, ha, rfl⟩ := WithAlternatives.mem_alternatives_map.1 hy
      obtain ⟨b, hb, hab⟩ := hx.2.1 a ha
      exact ⟨g' b, WithAlternatives.mem_alternatives_map.2 ⟨b, hb, rfl⟩, hg hab⟩
    · obtain ⟨b, hb, rfl⟩ := WithAlternatives.mem_alternatives_map.1 hy
      obtain ⟨a, ha, hab⟩ := hx.2.2 b hb
      exact ⟨g a, WithAlternatives.mem_alternatives_map.2 ⟨a, ha, rfl⟩, hg hab⟩

theorem rel_pure (f : Eff B) (h : f.IsApplicative) :
    LiftFun R (LiftRel r f R) (pure f h) (pure f h) := by
  intro a b hab
  cases f with
  | S => exact ⟨fun _ ha ↦ ⟨b, rfl, ha ▸ hab⟩, fun _ hb ↦ ⟨a, rfl, hb ▸ hab⟩⟩
  | R i => exact fun _ _ _ ↦ hab
  | W o => obtain ⟨rfl⟩ := h; exact ⟨hab, Iff.rfl⟩
  | C o => exact fun _ _ hc ↦ hc hab
  | M => exact ⟨Iff.rfl, fun _ _ ↦ hab⟩
  | F => exact ⟨hab, fun _ ha ↦ ⟨b, rfl, ha ▸ hab⟩, fun _ hb ↦ ⟨a, rfl, hb ▸ hab⟩⟩

theorem rel_seq (f : Eff B) (h : f.IsApplicative) :
    LiftFun (LiftRel r f (LiftFun R S)) (LiftFun (LiftRel r f R) (LiftRel r f S))
      (seq f h) (seq f h) := by
  intro g g' hg x x' hx
  cases f with
  | S =>
    refine ⟨?_, ?_⟩
    · rintro _ ⟨k, hk, a, ha, rfl⟩
      obtain ⟨k', hk', hkk⟩ := hg.1 k hk
      obtain ⟨b, hb, hab⟩ := hx.1 a ha
      exact ⟨k' b, ⟨k', hk', b, hb, rfl⟩, hkk hab⟩
    · rintro _ ⟨k', hk', b, hb, rfl⟩
      obtain ⟨k, hk, hkk⟩ := hg.2 k' hk'
      obtain ⟨a, ha, hab⟩ := hx.2 b hb
      exact ⟨k a, ⟨k, hk, a, ha, rfl⟩, hkk hab⟩
  | R i => exact fun _ _ hi ↦ hg hi (hx hi)
  | W o => obtain ⟨rfl⟩ := h; exact ⟨hg.1 hx.1, and_congr hg.2 hx.2⟩
  | C o => exact fun _ _ hc ↦ hg fun _ _ hk ↦ hx fun _ _ hab ↦ hc (hk hab)
  | M =>
    exact ⟨⟨fun ⟨h₁, h₂⟩ ↦ ⟨hg.1.1 h₁, hx.1.1 h₂⟩, fun ⟨h₁, h₂⟩ ↦ ⟨hg.1.2 h₁, hx.1.2 h₂⟩⟩,
      fun ⟨h₁, h₂⟩ ⟨h₁', h₂'⟩ ↦ hg.2 h₁ h₁' (hx.2 h₂ h₂')⟩
  | F =>
    refine ⟨hg.1 hx.1, fun _ hy ↦ ?_, fun _ hy ↦ ?_⟩
    · obtain ⟨k, hk, a, ha, rfl⟩ := WithAlternatives.mem_alternatives_seq.1 hy
      obtain ⟨k', hk', hkk⟩ := hg.2.1 k hk
      obtain ⟨b, hb, hab⟩ := hx.2.1 a ha
      exact ⟨k' b, WithAlternatives.mem_alternatives_seq.2 ⟨k', hk', b, hb, rfl⟩, hkk hab⟩
    · obtain ⟨k', hk', b, hb, rfl⟩ := WithAlternatives.mem_alternatives_seq.1 hy
      obtain ⟨k, hk, hkk⟩ := hg.2.2 k' hk'
      obtain ⟨a, ha, hab⟩ := hx.2.2 b hb
      exact ⟨k a, WithAlternatives.mem_alternatives_seq.2 ⟨k, hk, a, ha, rfl⟩, hkk hab⟩

theorem rel_join (f : Eff B) (h : f.IsApplicative) :
    LiftFun (LiftRel r f (LiftRel r f R)) (LiftRel r f R) (join f h) (join f h) := by
  intro x x' hx
  cases f with
  | S =>
    refine ⟨?_, ?_⟩
    · rintro a ⟨s, hs, ha⟩
      obtain ⟨s', hs', hss⟩ := hx.1 s hs
      obtain ⟨b, hb, hab⟩ := hss.1 a ha
      exact ⟨b, ⟨s', hs', hb⟩, hab⟩
    · rintro b ⟨s', hs', hb⟩
      obtain ⟨s, hs, hss⟩ := hx.2 s' hs'
      obtain ⟨a, ha, hab⟩ := hss.2 b hb
      exact ⟨a, ⟨s, hs, ha⟩, hab⟩
  | R i => exact fun _ _ hi ↦ hx hi hi
  | W o => obtain ⟨rfl⟩ := h; exact ⟨hx.1.1, and_congr hx.2 hx.1.2⟩
  | C o => exact fun _ _ hc ↦ hx fun _ _ hm ↦ hm hc
  | M =>
    exact ⟨⟨fun ⟨h₁, h₂⟩ ↦ ⟨hx.1.1 h₁, (hx.2 h₁ _).1.1 h₂⟩,
        fun ⟨h₁, h₂⟩ ↦ ⟨hx.1.2 h₁, (hx.2 _ h₁).1.2 h₂⟩⟩,
      fun ⟨h₁, h₂⟩ ⟨h₁', h₂'⟩ ↦ (hx.2 h₁ h₁').2 h₂ h₂'⟩
  | F =>
    refine ⟨hx.1.1, fun a hy ↦ ?_, fun b hy ↦ ?_⟩
    · obtain ⟨s, hs, ha⟩ := WithAlternatives.mem_alternatives_bind.1 hy
      obtain ⟨s', hs', hss⟩ := hx.2.1 s hs
      obtain ⟨b, hb, hab⟩ := hss.2.1 a ha
      exact ⟨b, WithAlternatives.mem_alternatives_bind.2 ⟨s', hs', hb⟩, hab⟩
    · obtain ⟨s', hs', hb⟩ := WithAlternatives.mem_alternatives_bind.1 hy
      obtain ⟨s, hs, hss⟩ := hx.2.2 s' hs'
      obtain ⟨a, ha, hab⟩ := hss.2.2 b hb
      exact ⟨a, WithAlternatives.mem_alternatives_bind.2 ⟨s, hs, ha⟩, hab⟩

theorem rel_counit {i : Ty B} :
    LiftFun (LiftRel r (.W i) (LiftRel r (.R i) R)) R counit counit :=
  fun _ _ hx ↦ hx.1 hx.2

theorem rel_eject {i : Ty B} :
    LiftFun (LiftFun R (LiftRel r (.R i) S)) (LiftRel r (.R i) (LiftFun R S)) eject eject :=
  fun _ _ hk _ _ hi _ _ hab ↦ hk hab hi

theorem rel_lower {o : Ty B} :
    LiftFun (LiftRel r (.C o) (Ty.LiftRel r o)) (Ty.LiftRel r o) lower lower :=
  fun _ _ hm ↦ hm fun _ _ h ↦ h

end Eff

variable {r : ∀ b, D b → D' b → Prop} {G : Language (Ty B)}
  [M : G.Structure (Ty.Dom D)] [M' : G.Structure (Ty.Dom D')]

/-- Where the rules of a grammar respect a relation between base domains, every mode over them
does. -/
theorem Mode.rel_eval
    (hG : ∀ {l r' u : Ty B} (b : G.Binary l r' u), LiftFun (Ty.LiftRel r l)
      (LiftFun (Ty.LiftRel r r') (Ty.LiftRel r u))
      (fun x y ↦ M.funMap b (x, y)) fun x y ↦ M'.funMap b (x, y)) :
    ∀ {l r' u : Ty B} (m : Mode G.Binary l r' u),
      LiftFun (Ty.LiftRel r l) (LiftFun (Ty.LiftRel r r') (Ty.LiftRel r u)) (m.eval D)
        (m.eval D')
  | _, _, _, .basic b => hG b
  | _, _, _, .mapR (f := f) m => fun _ _ ha _ _ hb ↦
    Eff.rel_map f (fun _ _ hy ↦ Mode.rel_eval hG m ha hy) hb
  | _, _, _, .mapL (f := f) m => fun _ _ ha _ _ hb ↦
    Eff.rel_map (R := Ty.LiftRel r _) (S := Ty.LiftRel r _) f
      (fun _ _ hx ↦ Mode.rel_eval hG m hx hb) ha
  | _, _, _, .ap (f := f) m h => fun _ _ ha _ _ hb ↦
    Eff.rel_seq (R := Ty.LiftRel r _) (S := Ty.LiftRel r _) f h
      (Eff.rel_map (R := Ty.LiftRel r _) (S := LiftFun (Ty.LiftRel r _) (Ty.LiftRel r _)) f
        (fun _ _ hx _ _ hy ↦ Mode.rel_eval hG m hx hy) ha) hb
  | _, _, _, .unitR (f := f) m h => fun _ _ ha _ _ hb ↦
    Mode.rel_eval hG m (fun _ _ hx ↦ ha (Eff.rel_pure f h hx)) hb
  | _, _, _, .unitL (f := f) m h => fun _ _ ha _ _ hb ↦
    Mode.rel_eval hG m ha fun _ _ hy ↦ hb (Eff.rel_pure f h hy)
  | _, _, _, .counit (i := i) m => fun _ _ ha _ _ hb ↦
    Eff.rel_counit (Eff.rel_map (.W i)
      (fun _ _ hx ↦ Eff.rel_map (.R i) (fun _ _ hy ↦ Mode.rel_eval hG m hx hy) hb) ha)
  | _, _, _, .ejectR m => fun _ _ ha _ _ hb ↦ Mode.rel_eval hG m ha (Eff.rel_eject hb)
  | _, _, _, .ejectL m => fun _ _ ha _ _ hb ↦ Mode.rel_eval hG m (Eff.rel_eject ha) hb
  | _, _, _, .join (f := f) m h => fun _ _ ha _ _ hb ↦
    (Mode.eval_join (D := D) m _ _).symm ▸ (Mode.eval_join (D := D') m _ _).symm ▸
      Eff.rel_join f h (Mode.rel_eval hG m ha hb)
  | _, _, _, .lower m => fun _ _ ha _ _ hb ↦ Eff.rel_lower (Mode.rel_eval hG m ha hb)

omit M M' in
theorem Application.rel_eval : ∀ {l r' u : Ty B} (b : Application l r' u),
    LiftFun (Ty.LiftRel r l) (LiftFun (Ty.LiftRel r r') (Ty.LiftRel r u))
      (Application.eval D b) (Application.eval D' b)
  | _, _, _, .fa => fun _ _ hf _ _ hx ↦ hf hx
  | _, _, _, .ba => fun _ _ hx _ _ hf ↦ hf hx

omit M M' in
theorem PredicateModification.rel_eval : ∀ {l r' u : Ty B} (b : PredicateModification l r' u),
    LiftFun (Ty.LiftRel r l) (LiftFun (Ty.LiftRel r r') (Ty.LiftRel r u))
      (PredicateModification.eval D b) (PredicateModification.eval D' b)
  | _, _, _, .pm => fun _ _ hp _ _ hq _ _ hx ↦ and_congr (hp hx) (hq hx)

omit M M' in
theorem EventIdentification.rel_eval {x s : Ty B} :
    ∀ {l r' u : Ty B} (b : EventIdentification x s l r' u),
      LiftFun (Ty.LiftRel r l) (LiftFun (Ty.LiftRel r r') (Ty.LiftRel r u))
        (EventIdentification.eval D b) (EventIdentification.eval D' b)
  | _, _, _, .left => fun _ _ hf _ _ hg _ _ hx _ _ he ↦ and_congr (hf hx he) (hg he)
  | _, _, _, .right => fun _ _ hg _ _ hf _ _ hx _ _ he ↦ and_congr (hf hx he) (hg he)

omit M M' in
/-- Functional application on two families of domains is logically related by any relation
between the base domains. -/
theorem application.isLogicalRel :
    (inferInstance : (application (B := B)).Structure (Ty.Dom D)).IsLogicalRel
      (inferInstance : (application (B := B)).Structure (Ty.Dom D'))
      (Ty.LiftRel r) :=
  .mk₂ nofun fun m _ _ _ _ hx hy ↦ Application.rel_eval m hx hy

/-- A logical relation between two structures for a grammar, lifted from a relation between base
domains, is one between the two structures of the effect-driven grammar over it, so related
lexicons give every derivation related values. -/
theorem effectGrammar.isLogicalRel (h : M.IsLogicalRel M' (Ty.LiftRel r)) :
    (effectGrammar.structure (G := G) (M := M)).IsLogicalRel
      (effectGrammar.structure (G := G) (M := M')) (Ty.LiftRel r) :=
  h.withBinary fun m _ _ _ _ hx hy ↦
    Mode.rel_eval (fun b _ _ hx _ _ hy ↦ h.funMap b ⟨hx, hy⟩) m hx hy

end Interpreter
