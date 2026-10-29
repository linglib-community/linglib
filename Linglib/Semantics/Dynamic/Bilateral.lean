module

public import Linglib.Semantics.Dynamic.State
public import Linglib.Semantics.Dynamic.Update
public import Mathlib.Algebra.Group.Defs

/-!
# Bilateral Update Semantics

Bilateral Update Semantics (BUS, [elliott-sudo-2025]'s formulation, with
[krahmer-muskens-1995]'s bilateral DRT as ancestor): update semantics
where each sentence carries a positive and a negative update dimension,
validating Double Negation Elimination (negation swaps the dimensions)
and cross-disjunct anaphora.

States are Heimian (the paper's Def. 3.1): sets of world-assignment
pairs whose assignments are partial (`Flat E`-valued), the carrier of `State.lean`'s
information states. `⊥` is the paper's `∗`, so definedness is
per-possibility and need not be uniform, which the paper's separation of
assertability (54) from Heimian familiarity needs. Subsistence (Def. 3.3,
after [groenendijk-stokhof-veltman-1996]), familiarity (Def. 3.2) and random
assignment (43) are `State.lean`'s.

## Main definitions

- `BilateralDen` with `atom`, `pred1`, `pred2`, `neg` (`~`), `conj`
  (`⊙`, (61)), `disj` (`⊕`, (64)), `exists_` ((44)–(45)), `forall_`.
- `unknownUpdate` (`s[φ]?`, (53)) and `assertable` ((54)).
- `supports`, `entails` (`⊨ᵇ`): subsistence-based support.

## Main results

- `neg_neg`: DNE is definitional.
- `partition`, `partition_assertable`: every possibility subsists
  positively, subsists negatively, or is unknown.
- `de_morgan_disj`, `de_morgan_conj`: de Morgan's laws in both dimensions,
  unlike in standard dynamic semantics.
- `egli`: Egli's positive equivalence, the positive half of Egli's theorem,
  definitionally.

## Implementation notes

Descent requires the larger point to *extend* the assignment, per
[groenendijk-stokhof-veltman-1996]; [elliott-sudo-2025]'s Def. 3.3
phrases the clause as domain inclusion, and their examples do not
discriminate. The paper overloads `≺` for possibility-in-state and
state-in-state subsistence (their fn. on (73)); here both are the
lower closure — membership for points, `≤` of closures for states.

## References

* [P. D. Elliott and Y. Sudo, *Free choice with anaphora* (2025)][elliott-sudo-2025]
* [E. Krahmer and R. Muskens, *Negation and disjunction in discourse representation theory*
  (1995)][krahmer-muskens-1995]
* [J. Groenendijk, M. Stokhof and F. Veltman, *Coreference and modality*
  (1996)][groenendijk-stokhof-veltman-1996]
-/

@[expose] public section

open DynamicSemantics

variable {W V E : Type*}

/-! ### Bilateral denotations -/

/-- A bilateral denotation: a positive dimension `s[φ]⁺` (what survives
assertion) and a negative dimension `s[φ]⁻` (what survives denial).
Standard dynamic semantics has only the former; the latter is what makes
DNE and cross-disjunct anaphora work. -/
@[ext] structure BilateralDen (W V E : Type*) where
  /-- Positive update: the result of asserting the sentence. -/
  positive : Set (Possibility W V (Flat E)) → Set (Possibility W V (Flat E))
  /-- Negative update: the result of denying the sentence. -/
  negative : Set (Possibility W V (Flat E)) → Set (Possibility W V (Flat E))

namespace BilateralDen

variable {φ ψ : BilateralDen W V E} {s : Set (Possibility W V (Flat E))}
  {p : Possibility W V (Flat E)}

/-- Worldly atom: keep the possibilities where the proposition holds
(positively) or fails (negatively). -/
def atom (pred : W → Prop) : BilateralDen W V E where
  positive s := {p ∈ s | pred p.world}
  negative s := {p ∈ s | ¬ pred p.world}

/-- Unary atomic predication at `t`. Atoms are *partial*: a possibility
where `t` is undefined survives in neither dimension
([elliott-sudo-2025]'s definedness clause for atomic sentences). -/
def pred1 (P : E → W → Prop) (t : V) : BilateralDen W V E where
  positive s := {p ∈ s | ∃ e : E, p.assignment t = ↑e ∧ P e p.world}
  negative s := {p ∈ s | ∃ e : E, p.assignment t = ↑e ∧ ¬ P e p.world}

/-- Binary atomic predication at `t₁`, `t₂`; partial like `pred1`. -/
def pred2 (P : E → E → W → Prop) (t₁ t₂ : V) : BilateralDen W V E where
  positive s := {p ∈ s | ∃ e₁ : E, p.assignment t₁ = ↑e₁ ∧
    ∃ e₂ : E, p.assignment t₂ = ↑e₂ ∧ P e₁ e₂ p.world}
  negative s := {p ∈ s | ∃ e₁ : E, p.assignment t₁ = ↑e₁ ∧
    ∃ e₂ : E, p.assignment t₂ = ↑e₂ ∧ ¬ P e₁ e₂ p.world}

/-- Negation swaps the dimensions: `s[¬φ]⁺ = s[φ]⁻` and `s[¬φ]⁻ = s[φ]⁺`.
Negation does not "push in" — this is the key insight of bilateralism. -/
def neg (φ : BilateralDen W V E) : BilateralDen W V E where
  positive := φ.negative
  negative := φ.positive

@[inherit_doc] scoped prefix:max "~" => neg

/-- Double negation is the identity, definitionally. -/
@[simp] theorem neg_neg (φ : BilateralDen W V E) : ~~φ = φ := rfl

instance : InvolutiveNeg (BilateralDen W V E) where
  neg := neg
  neg_neg := neg_neg

/-! ### The unknown update and assertability -/

/-- The *unknown* update `s[φ]?` ([elliott-sudo-2025], (53)): the
possibilities of `s` that subsist in neither dimension — the dynamic
analogue of the third Strong Kleene truth value. -/
def unknownUpdate (φ : BilateralDen W V E)
    (s : Set (Possibility W V (Flat E))) : Set (Possibility W V (Flat E)) :=
  {p ∈ s | p ∉ lowerClosure (φ.positive s) ∧ p ∉ lowerClosure (φ.negative s)}

/-- Assertability ([elliott-sudo-2025], (54)): the unknown update is
empty — every possibility is accounted for by one of the dimensions.
Strictly weaker than Heimian familiarity. -/
def assertable (φ : BilateralDen W V E)
    (c : Set (Possibility W V (Flat E))) : Prop :=
  φ.unknownUpdate c = ∅

theorem unknownUpdate_neg (φ : BilateralDen W V E) (s) :
    (~φ).unknownUpdate s = φ.unknownUpdate s := by
  ext p
  simp only [unknownUpdate, neg, Set.mem_ofPred_eq,
    and_comm (a := p ∉ lowerClosure (φ.negative s))]

theorem unknownUpdate_atom (pred : W → Prop) (s) :
    (atom pred (V := V) (E := E)).unknownUpdate s = ∅ := by
  ext p
  simp only [unknownUpdate, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
    iff_false, not_and]
  intro hp hpos hneg
  by_cases h : pred p.world
  · exact hpos (subset_lowerClosure ⟨hp, h⟩)
  · exact hneg (subset_lowerClosure ⟨hp, h⟩)

/-- Every possibility subsists positively, subsists negatively, or is
unknown. -/
theorem partition (φ : BilateralDen W V E) (hp : p ∈ s) :
    p ∈ lowerClosure (φ.positive s) ∨ p ∈ lowerClosure (φ.negative s) ∨ p ∈ φ.unknownUpdate s := by
  by_cases h1 : p ∈ lowerClosure (φ.positive s)
  · exact Or.inl h1
  · by_cases h2 : p ∈ lowerClosure (φ.negative s)
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr ⟨hp, h1, h2⟩)

/-- Under assertability, every possibility subsists in one of the
dimensions. -/
theorem partition_assertable (h : φ.assertable s) (hp : p ∈ s) :
    p ∈ lowerClosure (φ.positive s) ∨ p ∈ lowerClosure (φ.negative s) := by
  rcases partition φ hp with h1 | h2 | h3
  · exact Or.inl h1
  · exact Or.inr h2
  · rw [assertable] at h
    exact absurd (h ▸ h3) (Set.notMem_empty p)

/-! ### Connectives -/

/-- Conjunction ([elliott-sudo-2025], (61)): the positive update
sequences the positive dimensions (the one verifying Strong Kleene cell);
the negative update is the union of the dynamic falsifications, one per
falsifying cell. -/
def conj (φ ψ : BilateralDen W V E) : BilateralDen W V E where
  positive s := ψ.positive (φ.positive s)
  negative s :=
    ψ.positive (φ.negative s) ∪ ψ.negative (φ.negative s)
      ∪ ψ.unknownUpdate (φ.negative s) ∪ ψ.negative (φ.positive s)
      ∪ ψ.negative (φ.unknownUpdate s)

@[inherit_doc] scoped infixl:65 " ⊙ " => conj

/-- Disjunction ([elliott-sudo-2025], (64)): verification via the first
disjunct (the `s[φ]⁺` row) or via the second (the `[ψ]⁺` column); denial
is sequential. The state-passing `ψ.positive (φ.negative s)` term is what
makes bathroom disjunctions work: by DNE, `s[¬∃xP(x)]⁻ = s[∃xP(x)]⁺`
introduces the referent for the second disjunct. -/
def disj (φ ψ : BilateralDen W V E) : BilateralDen W V E where
  positive s :=
    ψ.positive (φ.positive s) ∪ ψ.negative (φ.positive s)
      ∪ ψ.unknownUpdate (φ.positive s) ∪ ψ.positive (φ.negative s)
      ∪ ψ.positive (φ.unknownUpdate s)
  negative s := ψ.negative (φ.negative s)

@[inherit_doc] scoped infixl:60 " ⊕ " => disj

theorem conj_assoc_positive (φ ψ χ : BilateralDen W V E) (s) :
    ((φ ⊙ ψ) ⊙ χ).positive s = (φ ⊙ (ψ ⊙ χ)).positive s := rfl

/-- De Morgan: `¬(φ ∨ ψ)` is `¬φ ∧ ¬ψ`, in both dimensions. -/
theorem de_morgan_disj (φ ψ : BilateralDen W V E) : ~(φ ⊕ ψ) = (~φ) ⊙ (~ψ) := by
  refine BilateralDen.ext rfl (funext fun s ↦ ?_)
  show ψ.positive (φ.positive s) ∪ ψ.negative (φ.positive s)
      ∪ ψ.unknownUpdate (φ.positive s) ∪ ψ.positive (φ.negative s)
      ∪ ψ.positive (φ.unknownUpdate s)
    = ψ.negative (φ.positive s) ∪ ψ.positive (φ.positive s)
      ∪ (~ψ).unknownUpdate (φ.positive s) ∪ ψ.positive (φ.negative s)
      ∪ ψ.positive ((~φ).unknownUpdate s)
  rw [unknownUpdate_neg φ s, unknownUpdate_neg ψ (φ.positive s),
    Set.union_comm (ψ.negative (φ.positive s)) (ψ.positive (φ.positive s))]

/-- De Morgan: `¬(φ ∧ ψ)` is `¬φ ∨ ¬ψ`, in both dimensions. -/
theorem de_morgan_conj (φ ψ : BilateralDen W V E) : ~(φ ⊙ ψ) = (~φ) ⊕ (~ψ) := by
  refine BilateralDen.ext (funext fun s ↦ ?_) rfl
  show ψ.positive (φ.negative s) ∪ ψ.negative (φ.negative s)
      ∪ ψ.unknownUpdate (φ.negative s) ∪ ψ.negative (φ.positive s)
      ∪ ψ.negative (φ.unknownUpdate s)
    = ψ.negative (φ.negative s) ∪ ψ.positive (φ.negative s)
      ∪ (~ψ).unknownUpdate (φ.negative s) ∪ ψ.negative (φ.positive s)
      ∪ ψ.negative ((~φ).unknownUpdate s)
  rw [unknownUpdate_neg φ s, unknownUpdate_neg ψ (φ.negative s),
    Set.union_comm (ψ.negative (φ.negative s)) (ψ.positive (φ.negative s))]

/-! ### Quantifiers -/

section Quantifiers
variable [DecidableEq V]

/-- Existential quantification ([elliott-sudo-2025], (44)–(45)): the
positive update introduces the referent by random assignment and asserts
the scope; the negative update merely removes possibilities — it retains
those of `s` whose world falsifies the existential classically, and
introduces no anaphoric information. -/
def exists_ (x : V) (φ : BilateralDen W V E) : BilateralDen W V E where
  positive s := φ.positive (State.randomAssign s x)
  negative s :=
    {p ∈ s | p.world ∉ Possibility.world '' φ.positive (State.randomAssign s x) ∧
      p.world ∈ Possibility.world '' φ.negative (State.randomAssign s x)}

/-- Universal quantification, by de Morgan duality: `∀x φ = ¬∃x ¬φ`. -/
def forall_ (x : V) (φ : BilateralDen W V E) : BilateralDen W V E :=
  ~(exists_ x (~φ))

/-- Egli's positive equivalence ([elliott-sudo-2025], (59)), definitionally:
an existential scoping over a conjunction binds into the second conjunct,
`(∃x φ) ∧ ψ` and `∃x (φ ∧ ψ)` having the same positive update. This is only
the positive half of Egli's theorem: the negative updates differ in general
((62)), since a denied existential introduces no referent and a denied
conjunction can. -/
theorem egli (x : V) (φ ψ : BilateralDen W V E) (s) :
    ((exists_ x φ) ⊙ ψ).positive s = (exists_ x (φ ⊙ ψ)).positive s := rfl

end Quantifiers

/-! ### Support and entailment -/

/-- Bilateral support: the positive update is consistent and the state
subsists in it. -/
def supports (s : Set (Possibility W V (Flat E)))
    (φ : BilateralDen W V E) : Prop :=
  (φ.positive s).Nonempty ∧ lowerClosure s ≤ lowerClosure (φ.positive s)

/-- Bilateral entailment: every consistent positive update of `φ`
supports `ψ`. -/
def entails (φ ψ : BilateralDen W V E) : Prop :=
  ∀ s : Set (Possibility W V (Flat E)),
    (φ.positive s).Nonempty → supports (φ.positive s) ψ

@[inherit_doc] scoped notation:50 φ " ⊨ᵇ " ψ => entails φ ψ

/-! ### Structural lemmas -/

theorem atom_complementary (pred : W → Prop) (s : Set (Possibility W V (Flat E))) :
    (atom pred (E := E)).positive s ∪ (atom pred).negative s = s := by
  ext p
  simp only [atom, Set.mem_union, Set.mem_ofPred_eq]
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  · intro h
    by_cases hp : pred p.world
    · exact Or.inl ⟨h, hp⟩
    · exact Or.inr ⟨h, hp⟩

theorem atom_disjoint (pred : W → Prop) (s : Set (Possibility W V (Flat E))) :
    (atom pred (E := E)).positive s ∩ (atom pred).negative s = ∅ := by
  ext p
  exact ⟨fun ⟨⟨_, hp⟩, ⟨_, hnp⟩⟩ => absurd hp hnp, False.elim⟩

theorem atom_positive_monotone (pred : W → Prop) :
    Monotone (atom pred (V := V) (E := E)).positive :=
  CCP.monotone_up _

theorem atom_negative_monotone (pred : W → Prop) :
    Monotone (atom pred (V := V) (E := E)).negative :=
  CCP.monotone_up _

theorem atom_positive_eliminative (pred : W → Prop) :
    CCP.IsEliminative (atom pred (V := V) (E := E)).positive :=
  (CCP.isClassical_up _).1

theorem atom_negative_eliminative (pred : W → Prop) :
    CCP.IsEliminative (atom pred (V := V) (E := E)).negative :=
  (CCP.isClassical_up _).1

theorem pred1_positive_monotone (P : E → W → Prop) (t : V) :
    Monotone (pred1 P t (W := W)).positive :=
  CCP.monotone_up _

theorem pred1_negative_monotone (P : E → W → Prop) (t : V) :
    Monotone (pred1 P t (W := W)).negative :=
  CCP.monotone_up _

theorem pred1_positive_eliminative (P : E → W → Prop) (t : V) :
    CCP.IsEliminative (pred1 P t (W := W)).positive :=
  (CCP.isClassical_up _).1

theorem pred1_negative_eliminative (P : E → W → Prop) (t : V) :
    CCP.IsEliminative (pred1 P t (W := W)).negative :=
  (CCP.isClassical_up _).1

theorem pred2_positive_eliminative (P : E → E → W → Prop) (t₁ t₂ : V) :
    CCP.IsEliminative (pred2 P t₁ t₂ (W := W)).positive :=
  (CCP.isClassical_up _).1

theorem pred2_negative_eliminative (P : E → E → W → Prop) (t₁ t₂ : V) :
    CCP.IsEliminative (pred2 P t₁ t₂ (W := W)).negative :=
  (CCP.isClassical_up _).1

end BilateralDen
