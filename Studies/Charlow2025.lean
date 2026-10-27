module

public import Linglib.Core.Order.Bilattice.Product
public import Studies.GroenendijkStokhof1991

/-!
# Charlow (2025): Staged updates

This file formalizes the lifted interpretations of [charlow-2025-staged-updates]. A dynamic
substrate whose negation is externally static, [groenendijk-stokhof-1991]'s DPL, is lifted into
a richer type by an embedding, a retraction and a negation obeying three laws, and the lifted
interpretation they determine validates double-negation elimination and is conservative over
the substrate (Facts 1 and 2). Every lawful lift of one substrate factors through a canonical
form, a substrate value with a parity bit (Fact 4), which the canonical lift, an update tagged
with one bit, realizes exactly (Fact 3). Over DPL the file gives four lifts:
[krahmer-muskens-1995]'s pairs of an update and its negation, [gotham-2019-ac22]'s
decomposition into a static closure and a dynamic tautology, whose involution law holds only on
the image of the lifted interpretation, the paper's staged updates, a static proposition beside
a dynamic tautology, and the canonical lift.

## Implementation notes

* The data of a lift and its laws are separate classes, after `Monad` and `LawfulMonad`, so the
  decomposed lift carries the data while its involution law is refuted on the whole carrier and
  proved on the image.
* Fact 4 is stated as factorization through the canonical form rather than as the paper's
  bijection between images; the corollary that lawful lifts lower alike follows from it.
* Fact 3 takes the paper's right identity for conjunction as a hypothesis.

## References

* [charlow-2025-staged-updates]
* [groenendijk-stokhof-1991]
* [krahmer-muskens-1995]
* [gotham-2019-ac22]
-/

@[expose] public section

namespace Charlow2025

open DynamicSemantics

/-! ### Substrates, lifts and interpretations (Definitions 3 and 4) -/

/-- A dynamic substrate, the paper's δ: a carrier with conjunction and negation. -/
class Substrate (δ : Type*) where
  conj : δ → δ → δ
  neg : δ → δ

/-- The language: atoms, bare existentials, conjunction and negation; `∃x φ` abbreviates
`∃x ∧ φ`. -/
inductive Formula (Atom : Type*) where
  | atom : Atom → Formula Atom
  | exi : ℕ → Formula Atom
  | conj : Formula Atom → Formula Atom → Formula Atom
  | neg : Formula Atom → Formula Atom
  deriving Repr

/-- The signatures of a lift of a substrate into `Δ`: `up` into the lifted type, `down` out of
it, and the lifted negation. -/
class Lift (δ : outParam Type*) (Δ : Type*) [Substrate δ] where
  up : δ → Δ
  down : Δ → δ
  neg : Δ → Δ

/-- The laws of a lift: Emb, `down ∘ up = id`; Inv, the lifted negation is an involution; and
Neg, conjugating the lifted negation by the lift recovers the substrate negation. -/
class LawfulLift (δ : outParam Type*) (Δ : Type*) [Substrate δ] [self : Lift δ Δ] : Prop where
  down_up : ∀ m : δ, self.down (self.up m) = m
  neg_neg : ∀ M : Δ, self.neg (self.neg M) = M
  down_neg_up : ∀ m : δ, self.down (self.neg (self.up m)) = Substrate.neg m

section Interpretation

variable {Atom δ Δ : Type*} [Substrate δ]

/-- The substrate interpretation `[·]`, from the primitive meanings of atoms and existentials. -/
def interp (ia : Atom → δ) (ie : ℕ → δ) : Formula Atom → δ
  | .atom a => ia a
  | .exi n => ie n
  | .conj φ ψ => Substrate.conj (interp ia ie φ) (interp ia ie ψ)
  | .neg φ => Substrate.neg (interp ia ie φ)

variable [self : Lift δ Δ]

/-- The lifted interpretation `⟨·⟩`: primitives lift, conjuncts lower, sequence and lift again,
and negation is the lifted negation. -/
def liftInterp (ia : Atom → δ) (ie : ℕ → δ) : Formula Atom → Δ
  | .atom a => self.up (ia a)
  | .exi n => self.up (ie n)
  | .conj φ ψ =>
    self.up (Substrate.conj (self.down (liftInterp ia ie φ)) (self.down (liftInterp ia ie ψ)))
  | .neg φ => self.neg (liftInterp ia ie φ)

variable [LawfulLift δ Δ] (ia : Atom → δ) (ie : ℕ → δ)

/-! ### Facts 1 and 2 -/

-- Fact 1
theorem liftInterp_neg_neg (φ : Formula Atom) :
    liftInterp (Δ := Δ) ia ie (.neg (.neg φ)) = liftInterp ia ie φ :=
  LawfulLift.neg_neg (liftInterp ia ie φ)

/-- A formula without negation. -/
inductive NegFree : Formula Atom → Prop where
  | atom (a : Atom) : NegFree (.atom a)
  | exi (n : ℕ) : NegFree (.exi n)
  | conj {φ ψ : Formula Atom} : NegFree φ → NegFree ψ → NegFree (.conj φ ψ)

/-- A formula without a doubly negated subformula. -/
inductive DoubleNegFree : Formula Atom → Prop where
  | atom (a : Atom) : DoubleNegFree (.atom a)
  | exi (n : ℕ) : DoubleNegFree (.exi n)
  | conj {φ ψ : Formula Atom} : DoubleNegFree φ → DoubleNegFree ψ → DoubleNegFree (.conj φ ψ)
  | neg_atom (a : Atom) : DoubleNegFree (.neg (.atom a))
  | neg_exi (n : ℕ) : DoubleNegFree (.neg (.exi n))
  | neg_conj {φ ψ : Formula Atom} :
    DoubleNegFree φ → DoubleNegFree ψ → DoubleNegFree (.neg (.conj φ ψ))

-- Fact 2
theorem liftInterp_eq_up_interp_of_negFree {φ : Formula Atom} (h : NegFree φ) :
    liftInterp (Δ := Δ) ia ie φ = self.up (interp ia ie φ) := by
  induction h with
  | atom _ => rfl
  | exi _ => rfl
  | conj _ _ ihφ ihψ =>
    show self.up (Substrate.conj (self.down (liftInterp ia ie _))
      (self.down (liftInterp ia ie _))) = _
    rw [ihφ, ihψ, LawfulLift.down_up, LawfulLift.down_up]
    rfl

-- Fact 2
theorem down_liftInterp_eq_interp_of_doubleNegFree {φ : Formula Atom} (h : DoubleNegFree φ) :
    self.down (liftInterp ia ie φ) = interp ia ie φ := by
  induction h with
  | atom _ => exact LawfulLift.down_up _
  | exi _ => exact LawfulLift.down_up _
  | conj _ _ ihφ ihψ =>
    show self.down (self.up (Substrate.conj (self.down (liftInterp ia ie _))
      (self.down (liftInterp ia ie _)))) = _
    rw [LawfulLift.down_up, ihφ, ihψ]
    rfl
  | neg_atom _ => exact LawfulLift.down_neg_up _
  | neg_exi _ => exact LawfulLift.down_neg_up _
  | neg_conj _ _ ihφ ihψ =>
    show self.down (self.neg (self.up (Substrate.conj (self.down (liftInterp ia ie _))
      (self.down (liftInterp ia ie _))))) = _
    rw [LawfulLift.down_neg_up, ihφ, ihψ]
    rfl

end Interpretation

/-! ### The canonical form and Fact 4 -/

section Canonical

variable {Atom δ : Type*} [Substrate δ] (ia : Atom → δ) (ie : ℕ → δ)

/-- The canonical form of a formula's lifted meaning: a substrate value with a parity bit,
`Sum.inl` for an even and `Sum.inr` for an odd number of residual negations; it depends on the
substrate alone. -/
def canonicalize : Formula Atom → δ ⊕ δ
  | .atom a => .inl (ia a)
  | .exi n => .inl (ie n)
  | .conj φ ψ =>
    .inl (Substrate.conj ((canonicalize φ).elim id Substrate.neg)
      ((canonicalize ψ).elim id Substrate.neg))
  | .neg φ => (canonicalize φ).swap

theorem canonicalize_of_negFree {φ : Formula Atom} (h : NegFree φ) :
    canonicalize ia ie φ = .inl (interp ia ie φ) := by
  induction h with
  | atom _ => rfl
  | exi _ => rfl
  | conj _ _ ihφ ihψ => simp only [canonicalize, ihφ, ihψ, Sum.elim_inl, id]; rfl

theorem canonicalize_eq (φ : Formula Atom) :
    ∃ ψ, canonicalize ia ie φ = .inl (interp ia ie ψ) ∨
      canonicalize ia ie φ = .inr (interp ia ie ψ) := by
  induction φ with
  | atom a => exact ⟨.atom a, .inl rfl⟩
  | exi n => exact ⟨.exi n, .inl rfl⟩
  | conj φ ψ ihφ ihψ =>
    have elim : ∀ {χ : Formula Atom}, (∃ χ', canonicalize ia ie χ = .inl (interp ia ie χ') ∨
        canonicalize ia ie χ = .inr (interp ia ie χ')) →
        ∃ χ', (canonicalize ia ie χ).elim id Substrate.neg = interp ia ie χ' := by
      rintro χ ⟨χ', h | h⟩ <;> rw [h]
      · exact ⟨χ', rfl⟩
      · exact ⟨.neg χ', rfl⟩
    obtain ⟨φ', hφ⟩ := elim ihφ
    obtain ⟨ψ', hψ⟩ := elim ihψ
    exact ⟨.conj φ' ψ', .inl (by simp only [canonicalize, hφ, hψ]; rfl)⟩
  | neg φ ih =>
    obtain ⟨φ', h | h⟩ := ih
    · exact ⟨φ', .inr (by simp [canonicalize, h])⟩
    · exact ⟨φ', .inl (by simp [canonicalize, h])⟩

variable (Δ : Type*) [self : Lift δ Δ]

/-- Encoding a canonical form into a lift: a positive value lifts, a negative one lifts and is
negated. -/
def encodeCanonical : δ ⊕ δ → Δ
  | .inl m => self.up m
  | .inr m => self.neg (self.up m)

variable [LawfulLift δ Δ]

theorem down_encodeCanonical (s : δ ⊕ δ) :
    self.down (encodeCanonical Δ s) = s.elim id Substrate.neg := by
  cases s with
  | inl m => exact LawfulLift.down_up m
  | inr m => exact LawfulLift.down_neg_up m

theorem encodeCanonical_swap (s : δ ⊕ δ) :
    encodeCanonical Δ s.swap = self.neg (encodeCanonical Δ s) := by
  cases s with
  | inl m => rfl
  | inr m =>
    show self.up m = self.neg (self.neg (self.up m))
    rw [LawfulLift.neg_neg]

-- Fact 4
theorem liftInterp_eq_encodeCanonical (φ : Formula Atom) :
    liftInterp (Δ := Δ) ia ie φ = encodeCanonical Δ (canonicalize ia ie φ) := by
  induction φ with
  | atom a => rfl
  | exi n => rfl
  | conj φ ψ ihφ ihψ =>
    show self.up (Substrate.conj (self.down (liftInterp ia ie φ))
      (self.down (liftInterp ia ie ψ))) = _
    rw [ihφ, ihψ, down_encodeCanonical, down_encodeCanonical]
    rfl
  | neg φ ih =>
    show self.neg (liftInterp ia ie φ) = _
    rw [ih]
    exact (encodeCanonical_swap Δ _).symm

theorem liftInterp_eq_of_canonicalize_eq {φ ψ : Formula Atom}
    (h : canonicalize ia ie φ = canonicalize ia ie ψ) :
    liftInterp (Δ := Δ) ia ie φ = liftInterp ia ie ψ := by
  rw [liftInterp_eq_encodeCanonical, liftInterp_eq_encodeCanonical, h]

-- Fact 4
theorem down_liftInterp_eq_down_liftInterp (Δ' : Type*) [Lift δ Δ'] [LawfulLift δ Δ']
    (φ : Formula Atom) :
    Lift.down (liftInterp (Δ := Δ) ia ie φ) = Lift.down (liftInterp (Δ := Δ') ia ie φ) := by
  rw [liftInterp_eq_encodeCanonical, liftInterp_eq_encodeCanonical, down_encodeCanonical,
    down_encodeCanonical]

end Canonical

/-! ### Program disjunction and truth (Definitions 2, 5 and 6) -/

/-- A substrate with the union of two updates, the externally dynamic program disjunction. -/
class ProgramDisj (δ : Type*) [Substrate δ] where
  pdisj : δ → δ → δ

/-- A substrate whose meanings have propositional content over indices `i`, the indices where
they succeed, and can be restricted to a proposition. -/
class Truth (δ : Type*) (i : outParam Type*) [Substrate δ] where
  truth : δ → i → Prop
  restrict : δ → (i → Prop) → δ

/-! ### DPL as a substrate -/

section DPL

variable {E : Type*}

instance : Substrate (Update (Assignment E)) where
  conj := SetRel.comp
  neg φ := Update.test (Update.neg φ)

/-- Program disjunction on DPL relations is the union of the outputs. -/
instance : ProgramDisj (Update (Assignment E)) where
  pdisj φ ψ := φ ∪ ψ

instance : Truth (Update (Assignment E)) (ℕ → E) where
  truth φ g := g ∈ φ.dom
  restrict m p := {q | p q.1 ∧ q ∈ m}

private theorem rel_ext {φ ψ : Update (Assignment E)} (h : ∀ g k, (g, k) ∈ φ ↔ (g, k) ∈ ψ) :
    φ = ψ :=
  Set.ext λ ⟨g, k⟩ => h g k

end DPL

/-! ### Instance 1: two-dimensional DPL

[krahmer-muskens-1995]'s pairs of an update and its anti-extension, recast as a lift on the
diagonal product `δ ⊙ δ`: `up` pairs an update with its substrate negation, `down` forgets the
anti-extension, and the lifted negation is the product's swap `ᶜ`. -/

section TwoDimensional

open Bilattice Product

variable {δ : Type*} [Substrate δ]

instance : Lift δ (δ ⊙ δ) where
  up m := mk m (Substrate.neg m)
  down M := M.pro
  neg M := Mᶜ

instance : LawfulLift δ (δ ⊙ δ) where
  down_up _ := rfl
  neg_neg _ := rfl
  down_neg_up _ := rfl

end TwoDimensional

/-! ### Instance 2: decomposed updates -/

/-- [gotham-2019-ac22]'s decomposition, recast as a lift: `up` pairs an update's static closure,
its double negation, with the dynamic tautology `m ∪ ¬m`, `down` conjoins the two and the lifted
negation negates the at-issue coordinate. -/
structure Decomposed (δ : Type*) where
  atIssue : δ
  tautology : δ

namespace Decomposed

variable {δ : Type*} [Substrate δ] [ProgramDisj δ]

instance : Lift δ (Decomposed δ) where
  up m := ⟨Substrate.neg (Substrate.neg m), ProgramDisj.pdisj m (Substrate.neg m)⟩
  down M := Substrate.conj M.atIssue M.tautology
  neg M := ⟨Substrate.neg M.atIssue, M.tautology⟩

variable {E : Type*}

theorem down_up (m : Update (Assignment E)) :
    Lift.down (Lift.up (Δ := Decomposed (Update (Assignment E))) m) = m :=
  rel_ext λ g h => by
    constructor
    · rintro ⟨k, ⟨rfl, hnn⟩, hm | ⟨rfl, hno⟩⟩
      · exact hm
      · exact absurd ⟨g, rfl, hno⟩ hnn
    · exact λ hm => ⟨g, ⟨rfl, λ ⟨_, e, hno⟩ => hno ⟨h, e ▸ hm⟩⟩, .inl hm⟩

theorem down_neg_up (m : Update (Assignment E)) :
    Lift.down (Lift.neg (Lift.up (Δ := Decomposed (Update (Assignment E))) m)) =
      Update.test (Update.neg m) :=
  rel_ext λ g h => by
    constructor
    · rintro ⟨k, ⟨rfl, h3⟩, hm | hneg⟩
      · exact absurd ⟨g, rfl, λ ⟨_, e, hno⟩ => hno ⟨h, e ▸ hm⟩⟩ h3
      · exact hneg
    · rintro ⟨rfl, hno⟩
      exact ⟨g, ⟨rfl, λ ⟨_, e, hnn⟩ => hnn ⟨_, rfl, e ▸ hno⟩⟩, .inr ⟨rfl, hno⟩⟩

theorem not_neg_neg [Nontrivial E] :
    ∃ M : Decomposed (Update (Assignment E)), Lift.neg (Lift.neg M) ≠ M := by
  obtain ⟨x, φ, h⟩ := GroenendijkStokhof1991.dne_fails_anaphora (E := E)
  exact ⟨⟨Update.dexists x φ, Update.dexists x φ⟩, λ e => h (congrArg atIssue e)⟩

theorem exists_atIssue_eq_neg {Atom : Type*} (ia : Atom → Update (Assignment E))
    (ie : ℕ → Update (Assignment E)) (φ : Formula Atom) :
    ∃ X, (liftInterp (Δ := Decomposed (Update (Assignment E))) ia ie φ).atIssue =
      Update.test (Update.neg X) := by
  induction φ with
  | atom a => exact ⟨_, rfl⟩
  | exi n => exact ⟨_, rfl⟩
  | conj φ ψ _ _ => exact ⟨_, rfl⟩
  | neg φ _ => exact ⟨_, rfl⟩

theorem neg_neg_liftInterp {Atom : Type*} (ia : Atom → Update (Assignment E))
    (ie : ℕ → Update (Assignment E)) (φ : Formula Atom) :
    Lift.neg (Lift.neg (liftInterp (Δ := Decomposed (Update (Assignment E))) ia ie φ)) =
      liftInterp ia ie φ := by
  obtain ⟨X, hX⟩ := exists_atIssue_eq_neg ia ie φ
  generalize liftInterp (Δ := Decomposed (Update (Assignment E))) ia ie φ = M at hX ⊢
  cases M with
  | mk t n =>
    simp only at hX
    subst hX
    show Decomposed.mk
      (Update.test (Update.neg (Update.test (Update.neg (Update.test (Update.neg X)))))) n = _
    rw [(GroenendijkStokhof1991.neg_neg_eq_self_iff_isTest _).2 (Update.isTest_test _)]

end Decomposed

/-! ### Instance 3: staged updates -/

/-- A staged update: the static proposition of an update beside the dynamic tautology `m ∪ ¬m`;
`down` restricts the tautology to the proposition and the lifted negation complements the
proposition. -/
structure Staged (δ i : Type*) where
  staticContent : i → Prop
  update : δ

namespace Staged

variable {δ i : Type*} [Substrate δ] [ProgramDisj δ] [Truth δ i]

instance : Lift δ (Staged δ i) where
  up m := ⟨Truth.truth m, ProgramDisj.pdisj m (Substrate.neg m)⟩
  down M := Truth.restrict M.update M.staticContent
  neg M := ⟨λ x => ¬ M.staticContent x, M.update⟩

variable {E : Type*}

/-- Over DPL the staged lift obeys all three laws. -/
instance : LawfulLift (Update (Assignment E)) (Staged (Update (Assignment E)) (ℕ → E)) where
  down_up m := rel_ext λ g h => by
    constructor
    · rintro ⟨⟨j, hj⟩, hm | ⟨rfl, hno⟩⟩
      · exact hm
      · exact absurd ⟨j, hj⟩ hno
    · exact λ hm => And.intro ⟨h, hm⟩ (Or.inl hm)
  neg_neg M := by
    cases M with
    | mk p m =>
      show Staged.mk (λ x => ¬ ¬ p x) m = _
      simp only [not_not]
  down_neg_up m := rel_ext λ g h => by
    constructor
    · rintro ⟨hno, hm | hneg⟩
      · exact absurd ⟨h, hm⟩ hno
      · exact hneg
    · rintro ⟨rfl, hno⟩
      exact And.intro hno (Or.inr ⟨rfl, hno⟩)

end Staged

/-! ### Instance 4: the canonical lift and Fact 3 -/

/-- The canonical lift: an update tagged with a bit that says whether to negate it on lowering;
the lifted negation toggles the bit. -/
structure Canonical (δ : Type*) where
  flag : Bool
  update : δ

namespace Canonical

variable {δ : Type*} [Substrate δ]

instance : Lift δ (Canonical δ) where
  up m := ⟨true, m⟩
  down M := if M.flag then M.update else Substrate.neg M.update
  neg M := ⟨!M.flag, M.update⟩

instance : LawfulLift δ (Canonical δ) where
  down_up _ := rfl
  neg_neg M := by
    cases M with
    | mk b _ => cases b <;> rfl
  down_neg_up _ := rfl

variable {Atom : Type*} (ia : Atom → δ) (ie : ℕ → δ)

-- Fact 3
theorem liftInterp_eq (φ : Formula Atom) :
    ∃ (b : Bool) (ψ : Formula Atom),
      liftInterp (Δ := Canonical δ) ia ie φ = ⟨b, interp ia ie ψ⟩ := by
  obtain ⟨ψ, h | h⟩ := canonicalize_eq ia ie φ
  · exact ⟨true, ψ, by rw [liftInterp_eq_encodeCanonical, h]; rfl⟩
  · exact ⟨false, ψ, by rw [liftInterp_eq_encodeCanonical, h]; rfl⟩

/-- The paper's `φ̃`: every negation conjoined with a right identity `one`, so that no double
negation remains. -/
def guard (one : Formula Atom) : Formula Atom → Formula Atom
  | .atom a => .atom a
  | .exi n => .exi n
  | .conj φ ψ => .conj (guard one φ) (guard one ψ)
  | .neg φ => .conj (.neg (guard one φ)) one

variable {one : Formula Atom} (hone : NegFree one)
  (hid : ∀ m, Substrate.conj m (interp ia ie one) = m)

include hone hid in
theorem canonicalize_guard (φ : Formula Atom) :
    canonicalize ia ie (guard one φ) = .inl (interp ia ie φ) := by
  induction φ with
  | atom a => rfl
  | exi n => rfl
  | conj φ ψ ihφ ihψ => simp only [guard, canonicalize, ihφ, ihψ, Sum.elim_inl, id]; rfl
  | neg φ ih =>
    simp only [guard, canonicalize, ih, canonicalize_of_negFree ia ie hone, Sum.swap_inl,
      Sum.elim_inr, Sum.elim_inl, id, hid]
    rfl

include hone hid in
-- Fact 3
theorem exists_liftInterp_eq (b : Bool) (ψ : Formula Atom) :
    ∃ φ, liftInterp (Δ := Canonical δ) ia ie φ = ⟨b, interp ia ie ψ⟩ := by
  cases b
  · refine ⟨.neg (guard one ψ), ?_⟩
    rw [liftInterp_eq_encodeCanonical]
    show encodeCanonical _ (canonicalize ia ie (guard one ψ)).swap = _
    rw [canonicalize_guard ia ie hone hid]
    rfl
  · exact ⟨guard one ψ, by
      rw [liftInterp_eq_encodeCanonical, canonicalize_guard ia ie hone hid]; rfl⟩

end Canonical

end Charlow2025
