/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.Reference.Context.Basic
public import Linglib.Logic.Assignment
public import Linglib.Data.Examples.Schlenker2004a
public import Studies.Kaplan1989

/-!
# Schlenker (2004a): Context of Thought and Context of Utterance

This file formalizes the two-context logic of [schlenker-2004a]. A sentence is evaluated
against a Context of Utterance, the point at which a thought is expressed, and a Context of
Thought, the point at which it originates. Tenses and pronouns are sorted variables: the
assignment gives their value, and the Context of Utterance fixes the domain that value must lie
in, on pain of referential failure (`Term.sorted`, `Term.Defined`). Every other indexical is a
function of the Context of Thought (`Term.indexical`, `Term.value`). The Context of Utterance
therefore enters the definedness conditions and never the truth conditions, which is the
paper's Elimination of the Context of Utterance: `Formula.Realize` takes the Context of Thought
alone, and replacing the sorted variables by simple ones (`Formula.strip`) preserves truth
(`realize_strip`) and removes every source of failure (`defined_strip`).

Free Indirect Discourse and the Historical Present are the two ways in which exactly one of the
two contexts is the actual one. In *Tomorrow was Monday* (1), a past tense under an adverbial of
the Context of Thought is defined only when the thought precedes the utterance
(`defined_lamPast_iff`), so against a single context the sentence is contradictory
(`not_defined_lamPast_self`) and the two contexts must differ (`ne_of_defined_lamPast`). In
*Fifty eight years ago ... the Germans attack Vercors* (2), a present tense under the adverbial
is defined only when the Context of Utterance lies fifty-eight years before the Context of
Thought (`defined_lamPres_iff`), and a first person pronoun in the same passage makes that past
context improper (`not_proper_of_defined_lamPres`).

## Implementation notes

* The appendix's sole world term `actually`, the world of the Context of Thought, is built into
  the atomic clauses; the paper's two predicate arities are `Formula.atom₀` and
  `Formula.atom₁`, with the predicates given as Lean propositions.
* Truth is the paper's pair of predicates: `Formula.Defined` is the negation of *weird* and
  `Formula.Realize` is *true*, read with the junk-value convention where the paper leaves truth
  undefined. A λ-abstraction whose argument fails is weird, which the appendix leaves implicit.
* The rows of `Data/Examples/Schlenker2004a.json` are the paper's (1) and (2); the schemas
  `Formula.lamPast` and `Formula.lamPres` are their logical forms with the predicate left open.
  Banfield's Priority of SPEAKER and the interpretation of gender features are discussed in the
  paper without a formal proposal and are not formalized.

## References

* [schlenker-2004a]
* [banfield-1982]
* [kaplan-1989]
-/

@[expose] public section

namespace Schlenker2004a

open Kaplan
open scoped Assignment

/-! ### Terms -/

/-- A term of the two-context logic over contexts `C`, valued in `α`. A simple variable and a
multiply sorted variable both take their value from the assignment; the sorted variable is in
addition restricted to a domain fixed by the Context of Utterance, outside which it fails to
refer. An indexical is a function of the Context of Thought. -/
inductive Term (C : Type*) (α : Type*)
  | var (k : ℕ)
  | sorted (k : ℕ) (domain : C → α → Prop)
  | indexical (f : C → α)

namespace Term

variable {C α : Type*} {s : Assignment α} {cu ct : C} {k : ℕ} {D : C → α → Prop} {f : C → α}

/-- The value of a term: the assignment's value at a variable, the Context of Thought's at an
indexical. The Context of Utterance plays no role. -/
def value : Term C α → Assignment α → C → α
  | var k, s, _ => s k
  | sorted k _, s, _ => s k
  | indexical f, _, ct => f ct

/-- A term is defined unless it is a sorted variable whose value lies outside its domain at
the Context of Utterance. The Context of Thought plays no role. -/
def Defined : Term C α → Assignment α → C → Prop
  | sorted k D, s, cu => D cu (s k)
  | _, _, _ => True

/-- Replace a sorted variable by the simple variable of the same index. -/
def strip : Term C α → Term C α
  | sorted k _ => var k
  | t => t

/-- A name: the indexical constant at `a`. -/
def name (a : α) : Term C α := indexical λ _ => a

@[simp] theorem value_var : (var k : Term C α).value s ct = s k := rfl
@[simp] theorem value_sorted : (sorted k D).value s ct = s k := rfl
@[simp] theorem value_indexical : (indexical f).value s ct = f ct := rfl
@[simp] theorem value_name (a : α) : (name a : Term C α).value s ct = a := rfl
@[simp] theorem defined_var : (var k : Term C α).Defined s cu := trivial
@[simp] theorem defined_sorted : (sorted k D).Defined s cu ↔ D cu (s k) := Iff.rfl
@[simp] theorem defined_indexical : (indexical f).Defined s cu := trivial
@[simp] theorem defined_name (a : α) : (name a : Term C α).Defined s cu := trivial

@[simp] theorem value_strip (t : Term C α) : t.strip.value s ct = t.value s ct := by
  cases t <;> rfl

@[simp] theorem defined_strip (t : Term C α) : t.strip.Defined s cu := by
  cases t <;> trivial

end Term

variable {W E P T : Type*} {sE : Assignment E} {sT : Assignment T} {c cu ct : Context W E P T}
  {k : ℕ}

/-! ### The lexicon of (20) and (21)

Pronouns and tenses are sorted variables whose domains are read off the Context of Utterance;
the remaining indexicals are functions of the Context of Thought. -/

namespace Term

/-- First person: an individual variable restricted to the speaker of the Context of
Utterance. -/
def I (k : ℕ) : Term (Context W E P T) E := sorted k λ cu e => e = cu.agent

/-- Second person: an individual variable restricted to the addressee of the Context of
Utterance. -/
def you (k : ℕ) : Term (Context W E P T) E := sorted k λ cu e => e = cu.addressee

/-- Third person of a `gender`: an individual variable restricted to the individuals of that
gender, at the time and in the world of the Context of Utterance, who are neither its speaker
nor its addressee. -/
def third (gender : E → T → W → Prop) (k : ℕ) : Term (Context W E P T) E :=
  sorted k λ cu e => gender e cu.time cu.world ∧ e ≠ cu.agent ∧ e ≠ cu.addressee

/-- Present tense: a time variable restricted to the time of the Context of Utterance. -/
def pres (k : ℕ) : Term (Context W E P T) T := sorted k λ cu t => t = cu.time

/-- Past tense: a time variable restricted to the times before the Context of Utterance. -/
def past [LT T] (k : ℕ) : Term (Context W E P T) T := sorted k λ cu t => t < cu.time

/-- A time indexical: `f` applied to the time of the Context of Thought. *Now* is the identity,
*tomorrow* the day successor, *fifty eight years ago* the subtraction of fifty-eight years. -/
def timeIndexical (f : T → T) : Term (Context W E P T) T := indexical λ ct => f ct.time

@[simp] theorem defined_I : (I k : Term (Context W E P T) E).Defined sE c ↔ sE k = c.agent :=
  Iff.rfl

@[simp] theorem defined_you :
    (you k : Term (Context W E P T) E).Defined sE c ↔ sE k = c.addressee :=
  Iff.rfl

@[simp] theorem defined_third (gender : E → T → W → Prop) :
    (third gender k).Defined sE c ↔
      gender (sE k) c.time c.world ∧ sE k ≠ c.agent ∧ sE k ≠ c.addressee :=
  Iff.rfl

@[simp] theorem defined_pres : (pres k : Term (Context W E P T) T).Defined sT c ↔ sT k = c.time :=
  Iff.rfl

@[simp] theorem defined_past [LT T] :
    (past k : Term (Context W E P T) T).Defined sT c ↔ sT k < c.time :=
  Iff.rfl

@[simp] theorem defined_timeIndexical (f : T → T) :
    (timeIndexical f : Term (Context W E P T) T).Defined sT c :=
  trivial

@[simp] theorem value_I : (I k : Term (Context W E P T) E).value sE c = sE k := rfl
@[simp] theorem value_you : (you k : Term (Context W E P T) E).value sE c = sE k := rfl
@[simp] theorem value_third (gender : E → T → W → Prop) : (third gender k).value sE c = sE k := rfl
@[simp] theorem value_pres : (pres k : Term (Context W E P T) T).value sT c = sT k := rfl
@[simp] theorem value_past [LT T] : (past k : Term (Context W E P T) T).value sT c = sT k := rfl

@[simp] theorem value_timeIndexical (f : T → T) :
    (timeIndexical f : Term (Context W E P T) T).value sT c = f c.time :=
  rfl

end Term

/-! ### Formulas -/

/-- A formula of the two-context logic: atomic predications of the paper's two arities, whose
world argument is *actually*; λ-abstraction over an individual or a time variable applied to a
term; and the Boolean connectives. -/
inductive Formula (W E P T : Type*)
  | atom₀ (R : T → W → Prop) (t : Term (Context W E P T) T)
  | atom₁ (Q : E → T → W → Prop) (i : Term (Context W E P T) E) (t : Term (Context W E P T) T)
  | lamE (i : Term (Context W E P T) E) (k : ℕ) (φ : Formula W E P T)
  | lamT (t : Term (Context W E P T) T) (k : ℕ) (φ : Formula W E P T)
  | not (φ : Formula W E P T)
  | and (φ ψ : Formula W E P T)
  | or (φ ψ : Formula W E P T)

namespace Formula

/-- Truth at an assignment and a Context of Thought. The Context of Utterance plays no role:
this signature is the paper's Elimination of the Context of Utterance. -/
def Realize : Formula W E P T → Assignment E → Assignment T → Context W E P T → Prop
  | atom₀ R t, _, sT, ct => R (t.value sT ct) ct.world
  | atom₁ Q i t, sE, sT, ct => Q (i.value sE ct) (t.value sT ct) ct.world
  | lamE i k φ, sE, sT, ct => φ.Realize (sE[k ↦ i.value sE ct]) sT ct
  | lamT t k φ, sE, sT, ct => φ.Realize sE (sT[k ↦ t.value sT ct]) ct
  | not φ, sE, sT, ct => ¬ φ.Realize sE sT ct
  | and φ ψ, sE, sT, ct => φ.Realize sE sT ct ∧ ψ.Realize sE sT ct
  | or φ ψ, sE, sT, ct => φ.Realize sE sT ct ∨ ψ.Realize sE sT ct

/-- Definedness, the negation of the paper's *weird*, at an assignment, a Context of Utterance
and a Context of Thought: every sorted variable, under the values the abstractions bind, lies
in its domain at the Context of Utterance. -/
def Defined : Formula W E P T → Assignment E → Assignment T →
    Context W E P T → Context W E P T → Prop
  | atom₀ _ t, _, sT, cu, _ => t.Defined sT cu
  | atom₁ _ i t, sE, sT, cu, _ => i.Defined sE cu ∧ t.Defined sT cu
  | lamE i k φ, sE, sT, cu, ct => i.Defined sE cu ∧ φ.Defined (sE[k ↦ i.value sE ct]) sT cu ct
  | lamT t k φ, sE, sT, cu, ct => t.Defined sT cu ∧ φ.Defined sE (sT[k ↦ t.value sT ct]) cu ct
  | not φ, sE, sT, cu, ct => φ.Defined sE sT cu ct
  | and φ ψ, sE, sT, cu, ct => φ.Defined sE sT cu ct ∧ ψ.Defined sE sT cu ct
  | or φ ψ, sE, sT, cu, ct => φ.Defined sE sT cu ct ∧ ψ.Defined sE sT cu ct

/-- The stripped formula `φ*` of (23): every sorted variable replaced by the simple variable
of its index. -/
def strip : Formula W E P T → Formula W E P T
  | atom₀ R t => atom₀ R t.strip
  | atom₁ Q i t => atom₁ Q i.strip t.strip
  | lamE i k φ => lamE i.strip k φ.strip
  | lamT t k φ => lamT t.strip k φ.strip
  | not φ => not φ.strip
  | and φ ψ => and φ.strip ψ.strip
  | or φ ψ => or φ.strip ψ.strip

/-- A stripped formula never fails to refer. -/
theorem defined_strip (φ : Formula W E P T) (sE : Assignment E) (sT : Assignment T) :
    φ.strip.Defined sE sT cu ct := by
  induction φ generalizing sE sT <;> simp_all [strip, Defined]

/-- Stripping the Context of Utterance preserves truth (23). -/
theorem realize_strip (φ : Formula W E P T) (sE : Assignment E) (sT : Assignment T) :
    φ.strip.Realize sE sT ct ↔ φ.Realize sE sT ct := by
  induction φ generalizing sE sT <;> simp_all [strip, Realize]

-- (28c)
theorem not_defined_lamT_and_past_pres [Preorder T] (t : Term (Context W E P T) T)
    (R R' : T → W → Prop) :
    ¬ (lamT t k (.and (.atom₀ R (.past k)) (.atom₀ R' (.pres k)))).Defined sE sT cu ct := by
  simp only [Defined, Term.defined_past, Term.defined_pres, Function.update_self]
  rintro ⟨-, hlt, heq⟩
  exact lt_irrefl _ (heq ▸ hlt)

/-! ### Free Indirect Discourse: a past tense under an adverbial of the Context of Thought -/

variable {f : T → T} {R : T → W → Prop}

/-- The logical form of (1), *Tomorrow was Monday* (`Examples.ex1`), and of the appendix's
*Now it was raining*: a time indexical `f` of the Context of Thought abstracted over the time
argument of a past-tense predication. -/
def lamPast [LT T] (f : T → T) (R : T → W → Prop) (k : ℕ) : Formula W E P T :=
  .lamT (.timeIndexical f) k (.atom₀ R (.past k))

/-- (1) is defined exactly when the adverbial's time precedes the Context of Utterance. -/
@[simp] theorem defined_lamPast_iff [LT T] :
    (lamPast f R k).Defined sE sT cu ct ↔ f ct.time < cu.time := by
  simp [lamPast, Defined]

-- (1)
@[simp] theorem realize_lamPast_iff [LT T] :
    (lamPast f R k).Realize sE sT ct ↔ R (f ct.time) ct.world := by
  simp [lamPast, Realize]

/-- (9b): against a single context, a past tense under *now* or *tomorrow* is contradictory. -/
theorem not_defined_lamPast_self [Preorder T] (hf : ∀ t, t ≤ f t) :
    ¬ (lamPast f R k).Defined sE sT c c := by
  rw [defined_lamPast_iff]
  exact not_lt_of_ge (hf c.time)

/-- If (1) is defined, the Context of Utterance differs from the Context of Thought. -/
theorem ne_of_defined_lamPast [Preorder T] (hf : ∀ t, t ≤ f t)
    (hd : (lamPast f R k).Defined sE sT cu ct) : cu ≠ ct := by
  rintro rfl
  exact not_defined_lamPast_self hf hd

/-! ### The Historical Present: a present tense under an adverbial of the Context of Thought -/

variable {Q : E → T → W → Prop} {i : Term (Context W E P T) E}

/-- The logical form of (2), *Fifty eight years ago ... the Germans attack Vercors*
(`Examples.ex2`): a time indexical `f` of the Context of Thought abstracted over the time
argument of a present-tense predication of the individual term `i`. -/
def lamPres (f : T → T) (Q : E → T → W → Prop) (i : Term (Context W E P T) E) (k : ℕ) :
    Formula W E P T :=
  .lamT (.timeIndexical f) k (.atom₁ Q i (.pres k))

/-- (29c): (2) is defined exactly when the individual term is and the Context of Utterance is
at the adverbial's time. -/
@[simp] theorem defined_lamPres_iff :
    (lamPres f Q i k).Defined sE sT cu ct ↔ i.Defined sE cu ∧ f ct.time = cu.time := by
  simp [lamPres, Defined]

-- (29c), (2)
@[simp] theorem realize_lamPres_iff :
    (lamPres f Q i k).Realize sE sT ct ↔ Q (i.value sE ct) (f ct.time) ct.world := by
  simp [lamPres, Realize]

theorem not_defined_lamPres_name_self (hf : ∀ t, f t ≠ t) (a : E) :
    ¬ (lamPres f Q (.name a) k).Defined sE sT c c := by
  simpa using hf c.time

/-- A first person pronoun in the Historical Present makes the context improper in the sense of
[kaplan-1989] when its speaker is not alive at its time (31). -/
theorem not_proper_of_defined_lamPres (alive : E → T → W → Prop) {j : ℕ}
    (hd : (lamPres f Q (.I j) k).Defined sE sT cu ct) (h : ¬ alive (sE j) cu.time cu.world)
    (located : E → P → T → W → Prop) : ¬ Kaplan1989.Proper (alive · cu.time ·) located cu := by
  rw [(defined_lamPres_iff.1 hd).1] at h
  exact fun hp ↦ h hp.1

end Formula

end Schlenker2004a
