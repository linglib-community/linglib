module

public import Linglib.Semantics.Dynamic.Consequence
public import Mathlib.Data.Stream.Init
public import Mathlib.Data.List.Basic
public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.TypeStar

/-!
# Dekker (2012): Dynamic Semantics

This file formalizes Predicate Logic with Anaphora, the system of [dekker-1994] as consolidated
in [dekker-2012]: a Tarskian satisfaction semantics for a first-order language with pronouns,
in which the dynamics of anaphora lives in one extra parameter, the sequence of witnesses,
rather than in the notion of content. A pronoun is an index into that sequence, an
existential prepends its witness to it, the second conjunct of a conjunction is evaluated
after the first conjunct's witnesses, and negation quantifies witnesses away, Definition 4.
The domain and range of a formula, Definition 3, count the witnesses it contributes and
demands, and satisfaction reads the sequence no further than their sum. Implication then
reads the antecedent's existentials universally, Observation 3, the discourse (9) and the
donkey sentence (12) come out equivalent to their pronoun-free renderings, and on
pronoun-free formulas truth obeys the classical clauses, Observation 4. Conjunction is
neither idempotent nor commutative, Observation 9, with the book's example (14) as witness.
Dynamic entailment, Definition 6, passes the premises' witnesses to the conclusion: it is
classical on pronoun-free conclusions, Observation 10, validates Heim's inference (15) and the
deduction theorem, Observation 11, and though neither reflexive nor monotone it obeys the
acute identity and monotonicity rules of Observation 12 once pronouns are updated for the
witnesses that intervene, Definition 7. Chapter 3 lifts the system to worlds with witnesses as
individual concepts: contents, updates and support are each defined recursively,
Definitions 1 to 3 of that chapter, and coincide, Observation 15 reducing contents to
satisfaction world by world, Observation 16 making an update the intersection with the
content and Observation 17 making support inclusion in it, so that supported updates never
corrupt a hearer's information, Observation 18.

## Implementation notes

The book's witness sequences are finite and long enough for the formula; here a sequence is
a `Stream'`, and `sat_congr` shows that satisfaction reads only its first `domain + range`
entries, so length bookkeeping disappears while the finite blocks of witnesses a formula
contributes stay lists of the right length. Pronoun `pron i` is the book's `pᵢ₊₁`, the `i`-th
most recent witness. Relation and constant symbols are strings interpreted by the model.
Observations 5 to 8, the α-conversion and binding algorithm that eliminate pronouns, and the
cut rule of Observation 13 are not formalized; neither are the conceptual covers of
Chapter 3 nor Chapter 4.

## TODO

Observation 12's monotonicity rule inserts a premise `χ` before the last `j` premises and
updates only the conclusion's pronouns, leaving those premises to be read against `χ`'s
witnesses instead of the ones they had; with `∃x Px, Q p₁ ⊨ Q p₁` and `χ = ∃y Ry` the rule so
stated fails, since the middle premise now says `Q` of `χ`'s witness. `entails_update_of_entails`
states the rule with those premises updated as well, which the proof of the book's rule
needs; the end-of-sequence case `j = 0` is unaffected.

## References

* [dekker-2012]
* [dekker-1994]
* [groenendijk-stokhof-1991]
* [heim-1982]
* [stalnaker-1978]
-/

@[expose] public section

namespace Dekker2012

variable {E : Type*}

/-! ### Syntax -/

/-- A term, Definition 2: an individual constant, a variable, or the pronoun `pron i`, the
book's `pᵢ₊₁`, referring to the `i`-th most recently introduced witness. -/
inductive Term where
  | const : String → Term
  | var : ℕ → Term
  | pron : ℕ → Term
  deriving DecidableEq, Repr

/-- The pronominal demand of a term: `pron i` needs `i + 1` witnesses before it. -/
def Term.range : Term → ℕ
  | .pron i => i + 1
  | _ => 0

/-- Formulas, Definition 2: atoms, negation, existential quantification and conjunction. -/
inductive Formula where
  /-- An atomic formula, a relation symbol applied to terms. -/
  | atom : String → List Term → Formula
  /-- Negation. -/
  | neg : Formula → Formula
  /-- Existential quantification over a variable. -/
  | exists_ : ℕ → Formula → Formula
  /-- Conjunction, the dynamic connective. -/
  | conj : Formula → Formula → Formula
  deriving DecidableEq, Repr

namespace Formula

@[inherit_doc] scoped infixr:35 " ⋀ " => conj
@[inherit_doc] scoped prefix:40 "∼" => neg

/-- Material implication, `¬(φ ∧ ¬ψ)`. -/
def impl (φ ψ : Formula) : Formula := ∼(φ ⋀ ∼ψ)

@[inherit_doc] scoped infixr:25 " ⟶ " => impl

/-- Universal quantification, `¬∃x¬φ`. -/
def forall_ (x : ℕ) (φ : Formula) : Formula := ∼(exists_ x (∼φ))

/-- The domain `n(φ)`, Definition 3: the number of witnesses the formula contributes, its
existentials outside any negation. -/
def domain : Formula → ℕ
  | atom _ _ => 0
  | neg _ => 0
  | exists_ _ φ => φ.domain + 1
  | conj φ ψ => φ.domain + ψ.domain

/-- The range `r(φ)`, Definition 3: the number of witnesses the formula demands from the
discourse before it, a second conjunct's demand being met first by the first conjunct's
contribution. -/
def range : Formula → ℕ
  | atom _ ts => ts.foldr (λ t m => max t.range m) 0
  | neg φ => φ.range
  | exists_ _ φ => φ.range
  | conj φ ψ => max φ.range (ψ.range - φ.domain)

/-- The pronoun-free formulas, those of ordinary predicate logic. -/
def PronounFree : Formula → Prop
  | atom _ ts => ∀ t ∈ ts, ∀ i, t ≠ .pron i
  | neg φ => φ.PronounFree
  | exists_ _ φ => φ.PronounFree
  | conj φ ψ => φ.PronounFree ∧ ψ.PronounFree

theorem range_le_of_mem {ts : List Term} {t : Term} (h : t ∈ ts) (R : String) :
    t.range ≤ (atom R ts).range := by
  induction ts with
  | nil => exact absurd h List.not_mem_nil
  | cons u us ih =>
    rcases List.mem_cons.1 h with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

theorem range_eq_zero_of_pronounFree : ∀ {φ : Formula}, φ.PronounFree → φ.range = 0
  | atom _ ts, h => by
    induction ts with
    | nil => rfl
    | cons t us ih =>
      have ht : t.range = 0 := by
        cases t with
        | pron i => exact absurd rfl (h _ List.mem_cons_self i)
        | _ => rfl
      simp only [range, List.foldr_cons] at ih ⊢
      rw [ht, ih λ u hu => h u (List.mem_cons_of_mem _ hu), max_self]
  | neg φ, h => range_eq_zero_of_pronounFree (φ := φ) h
  | exists_ _ φ, h => range_eq_zero_of_pronounFree (φ := φ) h
  | conj φ ψ, h => by
    simp only [range, range_eq_zero_of_pronounFree h.1, range_eq_zero_of_pronounFree h.2,
      Nat.zero_sub, max_self]

end Formula

/-! ### Witness sequences -/

theorem get_append_stream_of_lt : ∀ (l : List E) (s : Stream' E) {i : ℕ} (h : i < l.length),
    (l ++ₛ s).get i = l[i]
  | [], _, _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, _, 0, _ => rfl
  | _ :: l, s, _ + 1, h => get_append_stream_of_lt l s (Nat.lt_of_succ_lt_succ h)

theorem get_append_stream_of_le : ∀ (l : List E) (s : Stream' E) {i : ℕ}, l.length ≤ i →
    (l ++ₛ s).get i = s.get (i - l.length)
  | [], _, _, _ => rfl
  | _ :: _, _, 0, h => absurd h (Nat.not_succ_le_zero _)
  | _ :: l, s, i + 1, h => by
    rw [List.length_cons, Nat.add_sub_add_right]
    exact get_append_stream_of_le l s (Nat.le_of_succ_le_succ h)

theorem drop_append_stream_of_length {l : List E} {n : ℕ} (h : l.length = n) (s : Stream' E) :
    Stream'.drop n (l ++ₛ s) = s :=
  h ▸ Stream'.drop_append_stream l s

/-! ### Satisfaction and truth -/

/-- A model: interpretations of the individual constants and the relation symbols. -/
structure Model (E : Type*) where
  const : String → E
  interp : String → List E → Prop

/-- Term evaluation, Definition 4: a variable from the assignment, a pronoun from the witness
sequence. -/
def Term.eval (M : Model E) (g : ℕ → E) (e : Stream' E) : Term → E
  | .const c => M.const c
  | .var x => g x
  | .pron i => e.get i

namespace Formula

/-- Satisfaction `M, g, ê ⊨ φ`, Definition 4. A negation has no witnesses for its scope, the
witness of an existential heads the sequence, and a conjunction's first conjunct is read
after the second's witnesses. -/
def sat (M : Model E) (g : ℕ → E) (e : Stream' E) : Formula → Prop
  | atom R ts => M.interp R (ts.map (Term.eval M g e))
  | neg φ => ¬ ∃ c : List E, c.length = φ.domain ∧ sat M g (c ++ₛ e) φ
  | exists_ x φ => sat M (Function.update g x e.head) e.tail φ
  | conj φ ψ => sat M g (e.drop ψ.domain) φ ∧ sat M g e ψ

/-- Truth, Definition 4: some witnesses for the formula's contribution satisfy it. -/
def IsTrue (M : Model E) (g : ℕ → E) (e : Stream' E) (φ : Formula) : Prop :=
  ∃ c : List E, c.length = φ.domain ∧ sat M g (c ++ₛ e) φ

/-- Sameness of meaning, `φ ⇔ ψ`: the same satisfaction against every model, assignment and
sequence. -/
def Equiv (φ ψ : Formula) : Prop :=
  ∀ {E : Type} (M : Model E) (g : ℕ → E) (e : Stream' E), sat M g e φ ↔ sat M g e ψ

variable (M : Model E)

theorem sat_congr : ∀ (φ : Formula) {g : ℕ → E} {e e' : Stream' E},
    (∀ i < φ.domain + φ.range, e.get i = e'.get i) → (sat M g e φ ↔ sat M g e' φ)
  | atom R ts, g, e, e', h => by
    simp only [sat]
    have : ts.map (Term.eval M g e) = ts.map (Term.eval M g e') :=
      List.map_congr_left λ t ht => by
        cases t with
        | pron i =>
          exact h i (by
            have := range_le_of_mem ht R
            simp only [Term.range] at this
            simp only [domain]; omega)
        | _ => rfl
    rw [this]
  | neg φ, g, e, e', h => by
    simp only [sat]
    refine not_congr (exists_congr λ c => and_congr_right λ hc => sat_congr φ λ i hi => ?_)
    by_cases hic : i < c.length
    · rw [get_append_stream_of_lt _ _ hic, get_append_stream_of_lt _ _ hic]
    · rw [get_append_stream_of_le _ _ (not_lt.1 hic), get_append_stream_of_le _ _ (not_lt.1 hic)]
      exact h _ (by simp only [domain, range] at hi ⊢; omega)
  | exists_ x φ, g, e, e', h => by
    simp only [sat]
    rw [show e.head = e'.head from h 0 (by simp only [domain]; omega)]
    exact sat_congr φ λ i hi => h (i + 1) (by simp only [domain, range] at hi ⊢; omega)
  | conj φ ψ, g, e, e', h => by
    simp only [sat]
    have hφ := le_max_left φ.range (ψ.range - φ.domain)
    have hψ := le_max_right φ.range (ψ.range - φ.domain)
    refine and_congr (sat_congr φ λ i hi => ?_) (sat_congr ψ λ i hi => h i ?_)
    · rw [Stream'.get_drop, Stream'.get_drop]
      exact h _ (by simp only [domain, range] at hi ⊢; omega)
    · simp only [domain, range] at hi ⊢; omega

-- Observation 3
theorem sat_impl (g : ℕ → E) (e : Stream' E) (φ ψ : Formula) :
    sat M g e (φ ⟶ ψ) ↔
      ∀ c : List E, c.length = φ.domain → sat M g (c ++ₛ e) φ →
        ∃ a : List E, a.length = ψ.domain ∧ sat M g (a ++ₛ (c ++ₛ e)) ψ := by
  simp only [impl, sat, domain, Nat.add_zero, Stream'.drop_zero, not_exists, not_and, not_forall,
    not_not, exists_prop]

theorem sat_forall (g : ℕ → E) (e : Stream' E) (x : ℕ) (φ : Formula) :
    sat M g e (forall_ x φ) ↔ ∀ b, IsTrue M (Function.update g x b) e φ := by
  simp only [forall_, sat, domain, Nat.zero_add, not_exists, not_and, not_forall, not_not,
    exists_prop, IsTrue]
  constructor
  · intro h b
    simpa [Stream'.cons_append_stream] using h [b] rfl
  · intro h c hc
    obtain ⟨b, rfl⟩ := List.length_eq_one_iff.1 hc
    simpa [Stream'.cons_append_stream] using h b

theorem isTrue_of_domain_eq_zero (g : ℕ → E) (e : Stream' E) {φ : Formula} (h : φ.domain = 0) :
    IsTrue M g e φ ↔ sat M g e φ := by
  simp [IsTrue, h]

/-! ### The pronoun-free fragment, Observation 4

On pronoun-free formulas truth obeys the classical clauses and ignores the sequence. -/

theorem isTrue_neg (g : ℕ → E) (e : Stream' E) (φ : Formula) :
    IsTrue M g e (∼φ) ↔ ¬ IsTrue M g e φ := by
  simp [IsTrue, sat, domain]

theorem isTrue_exists (g : ℕ → E) (e : Stream' E) (x : ℕ) (φ : Formula) :
    IsTrue M g e (exists_ x φ) ↔ ∃ b, IsTrue M (Function.update g x b) e φ := by
  constructor
  · rintro ⟨c, hc, h⟩
    obtain ⟨b, c', rfl⟩ := List.exists_of_length_succ c hc
    exact ⟨b, c', by simpa [domain] using hc, by simpa [sat, Stream'.cons_append_stream] using h⟩
  · rintro ⟨b, c, hc, h⟩
    exact ⟨b :: c, by simp [hc, domain], by simpa [sat, Stream'.cons_append_stream] using h⟩

theorem isTrue_conj_iff (g : ℕ → E) (e : Stream' E) (φ ψ : Formula) :
    IsTrue M g e (φ ⋀ ψ) ↔ ∃ b : List E, b.length = φ.domain ∧ sat M g (b ++ₛ e) φ ∧
      ∃ a : List E, a.length = ψ.domain ∧ sat M g (a ++ₛ (b ++ₛ e)) ψ := by
  constructor
  · rintro ⟨c, hc, hφ, hψ⟩
    have ht : (c.take ψ.domain).length = ψ.domain := by
      simp only [domain] at hc; simp [List.length_take, hc]
    rw [← List.take_append_drop ψ.domain c, Stream'.append_append_stream] at hφ hψ
    rw [drop_append_stream_of_length ht] at hφ
    exact ⟨c.drop ψ.domain, by simp only [domain] at hc; simp [List.length_drop, hc], hφ,
      c.take ψ.domain, ht, hψ⟩
  · rintro ⟨b, hb, hφ, a, ha, hψ⟩
    refine ⟨a ++ b, by simp [domain, hb, ha, Nat.add_comm], ?_, ?_⟩
    · rw [Stream'.append_append_stream, drop_append_stream_of_length ha]; exact hφ
    · rw [Stream'.append_append_stream]; exact hψ

theorem sat_append_congr_of_pronounFree {ψ : Formula} (hψ : ψ.PronounFree) (g : ℕ → E)
    {a : List E} (ha : a.length = ψ.domain) (e e' : Stream' E) :
    sat M g (a ++ₛ e) ψ ↔ sat M g (a ++ₛ e') ψ :=
  sat_congr M ψ λ i hi => by
    rw [range_eq_zero_of_pronounFree hψ, Nat.add_zero, ← ha] at hi
    rw [get_append_stream_of_lt _ _ hi, get_append_stream_of_lt _ _ hi]

theorem isTrue_congr {φ : Formula} (hφ : φ.PronounFree) (g : ℕ → E) (e e' : Stream' E) :
    IsTrue M g e φ ↔ IsTrue M g e' φ :=
  exists_congr λ _ => and_congr_right λ hc => sat_append_congr_of_pronounFree M hφ g hc e e'

theorem isTrue_conj (g : ℕ → E) (e : Stream' E) (φ : Formula) {ψ : Formula}
    (hψ : ψ.PronounFree) : IsTrue M g e (φ ⋀ ψ) ↔ IsTrue M g e φ ∧ IsTrue M g e ψ := by
  rw [isTrue_conj_iff]
  constructor
  · rintro ⟨b, hb, hφ, a, ha, hψ'⟩
    exact ⟨⟨b, hb, hφ⟩, a, ha, (sat_append_congr_of_pronounFree M hψ g ha _ e).1 hψ'⟩
  · rintro ⟨⟨b, hb, hφ⟩, a, ha, hψ'⟩
    exact ⟨b, hb, hφ, a, ha, (sat_append_congr_of_pronounFree M hψ g ha e _).1 hψ'⟩

end Formula

/-! ### Examples -/

open Formula

-- (6)
theorem example6 (M : Model E) (g : ℕ → E) (e : Stream' E) :
    sat M g e (exists_ 0 (atom "BG" [.var 0]) ⋀ atom "S" [.pron 0]) ↔
      M.interp "BG" [e.get 0] ∧ M.interp "S" [e.get 0] := by
  simp [sat, domain, Term.eval]

-- (9)
theorem example9 :
    Equiv ((exists_ 0 (atom "M" [.var 0] ⋀ atom "W" [.var 0]) ⋀ exists_ 1 (atom "D" [.var 1])) ⋀
        (atom "F" [.pron 0, .pron 1] ⋀ atom "C" [.pron 1, .pron 0]))
      (exists_ 1 (exists_ 0 (((atom "M" [.var 0] ⋀ atom "W" [.var 0]) ⋀ atom "D" [.var 1]) ⋀
        (atom "F" [.var 1, .var 0] ⋀ atom "C" [.var 0, .var 1])))) := by
  intro E M g e
  simp [sat, domain, Term.eval, Stream'.get_drop]

-- (12)
theorem sat_donkey_antecedent (M : Model E) (g : ℕ → E) (e : Stream' E) :
    sat M g e (exists_ 0 (atom "F" [.var 0] ⋀
        exists_ 1 (atom "D" [.var 1] ⋀ atom "O" [.var 0, .var 1]))) ↔
      M.interp "F" [e.get 0] ∧ M.interp "D" [e.get 1] ∧ M.interp "O" [e.get 0, e.get 1] := by
  simp [sat, domain, Term.eval]

-- (12)
theorem example12 :
    Equiv (exists_ 0 (atom "F" [.var 0] ⋀ exists_ 1 (atom "D" [.var 1] ⋀
          atom "O" [.var 0, .var 1])) ⟶ atom "B" [.pron 0, .pron 1])
      (forall_ 0 (forall_ 1 ((atom "F" [.var 0] ⋀ (atom "D" [.var 1] ⋀
          atom "O" [.var 0, .var 1])) ⟶ atom "B" [.var 0, .var 1]))) := by
  intro E M g e
  rw [sat_impl, sat_forall]
  constructor
  · intro h b₀
    rw [isTrue_of_domain_eq_zero M _ _ rfl, sat_forall]
    intro b₁
    rw [isTrue_of_domain_eq_zero M _ _ rfl, sat_impl]
    intro c hc hP
    obtain rfl : c = [] := List.length_eq_zero_iff.1 hc
    obtain ⟨a, ha, hB⟩ := h [b₀, b₁] rfl (by
      rw [sat_donkey_antecedent]
      simpa [sat, Term.eval, Function.update_apply, Stream'.cons_append_stream, Stream'.cons,
        Stream'.get] using hP)
    obtain rfl : a = [] := List.length_eq_zero_iff.1 ha
    refine ⟨[], rfl, ?_⟩
    simpa [sat, Term.eval, Function.update_apply, Stream'.cons_append_stream, Stream'.cons,
      Stream'.get] using hB
  · intro h c hc hA
    obtain ⟨b₀, b₁, rfl⟩ := List.length_eq_two.1 hc
    rw [sat_donkey_antecedent] at hA
    simp only [Stream'.cons_append_stream, Stream'.cons, Stream'.get] at hA
    have h₁ := h b₀
    rw [isTrue_of_domain_eq_zero M _ _ rfl, sat_forall] at h₁
    have h₂ := h₁ b₁
    rw [isTrue_of_domain_eq_zero M _ _ rfl, sat_impl] at h₂
    obtain ⟨a, ha, hB⟩ := h₂ [] rfl (by simpa [sat, Term.eval, Function.update_apply] using hA)
    obtain rfl : a = [] := List.length_eq_zero_iff.1 ha
    refine ⟨[], rfl, ?_⟩
    simpa [sat, Term.eval, Function.update_apply, Stream'.cons_append_stream, Stream'.cons,
      Stream'.get] using hB

/-! ### Non-idempotence and non-commutativity, Observation 9 -/

/-- The two-element model of the counterexamples: `W`, `P` and `Q` hold of `0`, and `S`
relates `1` to `0`. -/
private def counterModel : Model (Fin 2) where
  const _ := 0
  interp
    | "W", [x] => x = 0
    | "S", [x, y] => x = 1 ∧ y = 0
    | "P", [x] => x = 0
    | "Q", [x] => x = 0
    | _, _ => False

/-- The sequence `0, 1, 1, …` of the counterexamples. -/
private def counterSeq : Stream' (Fin 2) := λ i => if i = 0 then 0 else 1

-- (14)
theorem not_idempotent :
    let φ := exists_ 1 (atom "W" [.var 1] ⋀ atom "S" [.pron 0, .var 1])
    ¬ Equiv (φ ⋀ φ) φ := by
  intro φ h
  have := h counterModel (λ _ => 0) counterSeq
  simp [φ, sat, domain, Term.eval, counterModel, counterSeq, Stream'.drop, Stream'.get,
    Stream'.head, Stream'.tail] at this

theorem not_commutative :
    ¬ Equiv (exists_ 0 (atom "P" [.var 0]) ⋀ atom "Q" [.pron 0])
      (atom "Q" [.pron 0] ⋀ exists_ 0 (atom "P" [.var 0])) := by
  intro h
  have := h counterModel (λ _ => 0) counterSeq
  simp [sat, domain, Term.eval, counterModel, counterSeq, Stream'.drop, Stream'.get,
    Stream'.head] at this

/-! ### Entailment -/

namespace Formula

/-- Dynamic entailment, Definition 6, with the premises read as one conjunction: every
witness sequence for the premises extends to one for the conclusion. -/
def Entails (φ ψ : Formula) : Prop :=
  ∀ {E : Type} (M : Model E) (g : ℕ → E) (e : Stream' E) (c : List E), c.length = φ.domain →
    sat M g (c ++ₛ e) φ → ∃ a : List E, a.length = ψ.domain ∧ sat M g (a ++ₛ (c ++ₛ e)) ψ

@[inherit_doc] scoped infix:50 " ⊨ " => Entails

-- Observation 10
theorem entails_iff_of_pronounFree {φ ψ : Formula} (hψ : ψ.PronounFree) :
    φ ⊨ ψ ↔ ∀ {E : Type} (M : Model E) (g : ℕ → E) (e : Stream' E),
      IsTrue M g e φ → IsTrue M g e ψ :=
  ⟨λ h _ M g e ⟨c, hc, hsat⟩ => (isTrue_congr M hψ g _ e).1 (h M g e c hc hsat),
    λ h _ M g e c hc hsat => (isTrue_congr M hψ g e _).1 (h M g e ⟨c, hc, hsat⟩)⟩

-- Observation 11
theorem entails_conj_iff (φ χ ψ : Formula) : (φ ⋀ χ) ⊨ ψ ↔ φ ⊨ (χ ⟶ ψ) := by
  constructor
  · intro h E M g e c hc hφ
    refine ⟨[], rfl, ?_⟩
    rw [Stream'.nil_append_stream, sat_impl]
    intro c' hc' hχ
    obtain ⟨a, ha, hψ⟩ := h M g e (c' ++ c) (by simp [domain, hc, hc', Nat.add_comm]) (by
      rw [sat, Stream'.append_append_stream, drop_append_stream_of_length hc']
      exact ⟨hφ, hχ⟩)
    rw [Stream'.append_append_stream] at hψ
    exact ⟨a, ha, hψ⟩
  · intro h E M g e c hc hsat
    rw [sat] at hsat
    obtain ⟨hφ, hχ⟩ := hsat
    have ht : (c.take χ.domain).length = χ.domain := by
      simp only [domain] at hc; simp [List.length_take, hc]
    rw [← List.take_append_drop χ.domain c, Stream'.append_append_stream] at hφ hχ ⊢
    rw [drop_append_stream_of_length ht] at hφ
    obtain ⟨a, ha, himpl⟩ := h M g e (c.drop χ.domain)
      (by simp only [domain] at hc; simp [List.length_drop, hc]) hφ
    obtain rfl : a = [] := List.length_eq_zero_iff.1 ha
    rw [Stream'.nil_append_stream, sat_impl] at himpl
    exact himpl _ ht hχ

-- (15)
theorem heim :
    ((exists_ 0 (atom "M" [.var 0] ⋀ atom "A" [.var 0]) ⟶ ∼(atom "R" [.pron 0])) ⋀
      exists_ 0 (atom "M" [.var 0] ⋀ atom "A" [.var 0])) ⊨ (∼(atom "R" [.pron 0])) := by
  intro E M g e c hc h
  obtain ⟨b, rfl⟩ := List.length_eq_one_iff.1 hc
  rw [sat, show (exists_ 0 (atom "M" [.var 0] ⋀ atom "A" [.var 0])).domain = [b].length from rfl,
    Stream'.drop_append_stream, sat_impl] at h
  obtain ⟨h₁, h₂⟩ := h
  obtain ⟨a, ha, hR⟩ := h₁ [b] rfl h₂
  obtain rfl : a = [] := List.length_eq_zero_iff.1 ha
  exact ⟨[], rfl, hR⟩

/-! ### Acute structural rules, Observation 12 -/

/-- Pronoun update `[n⁺ⱼ]`, Definition 7: pronouns reaching past the `j` most recent witnesses
skip `n` further ones. -/
def Term.update (n j : ℕ) : Term → Term
  | .pron i => if j ≤ i then .pron (i + n) else .pron i
  | t => t

/-- Pronoun update of a formula, Definition 7: in a conjunction the second conjunct's
break-even point moves past the first conjunct's witnesses. -/
def update (n j : ℕ) : Formula → Formula
  | atom R ts => atom R (ts.map (Term.update n j))
  | neg φ => neg (φ.update n j)
  | exists_ x φ => exists_ x (φ.update n j)
  | conj φ ψ => conj (φ.update n j) (ψ.update n (j + φ.domain))

@[simp] theorem domain_update (n j : ℕ) : ∀ φ : Formula, (φ.update n j).domain = φ.domain
  | atom _ _ => rfl
  | neg _ => rfl
  | exists_ _ φ => by simp only [update, domain, domain_update]
  | conj φ ψ => by simp only [update, domain, domain_update]

theorem sat_update (M : Model E) : ∀ (φ : Formula) (n j : ℕ) {g : ℕ → E}
    {c c' d : List E} {e : Stream' E}, c.length = φ.domain → c'.length = j → d.length = n →
    (sat M g (c ++ₛ (c' ++ₛ (d ++ₛ e))) (φ.update n j) ↔ sat M g (c ++ₛ (c' ++ₛ e)) φ)
  | atom R ts, n, j, g, c, c', d, e, hc, hc', hd => by
    obtain rfl : c = [] := List.length_eq_zero_iff.1 hc
    simp only [update, sat, Stream'.nil_append_stream, List.map_map]
    have : ts.map (Term.eval M g (c' ++ₛ (d ++ₛ e)) ∘ Term.update n j) =
        ts.map (Term.eval M g (c' ++ₛ e)) :=
      List.map_congr_left λ t _ => by
        cases t with
        | pron i =>
          simp only [Function.comp, Term.update]
          split_ifs with hji
          · simp only [Term.eval]
            rw [get_append_stream_of_le _ _ (by omega), get_append_stream_of_le _ _ (by omega),
              get_append_stream_of_le _ _ (by omega)]
            congr 1; omega
          · simp only [Term.eval]
            rw [get_append_stream_of_lt _ _ (by omega), get_append_stream_of_lt _ _ (by omega)]
        | _ => rfl
    rw [this]
  | neg φ, n, j, g, c, c', d, e, hc, hc', hd => by
    obtain rfl : c = [] := List.length_eq_zero_iff.1 hc
    simp only [update, sat, Stream'.nil_append_stream, domain_update]
    exact not_congr (exists_congr λ c₁ => and_congr_right λ hc₁ => sat_update M φ n j hc₁ hc' hd)
  | exists_ x φ, n, j, g, c, c', d, e, hc, hc', hd => by
    obtain ⟨b, c₁, rfl⟩ := List.exists_of_length_succ c hc
    simp only [update, sat, Stream'.cons_append_stream, Stream'.head_cons, Stream'.tail_cons]
    exact sat_update M φ n j (by simpa [domain] using hc) hc' hd
  | conj φ ψ, n, j, g, c, c', d, e, hc, hc', hd => by
    have ht : (c.take ψ.domain).length = ψ.domain := by
      simp only [domain] at hc; simp [List.length_take, hc]
    have hdr : (c.drop ψ.domain).length = φ.domain := by
      simp only [domain] at hc; simp [List.length_drop, hc]
    rw [← List.take_append_drop ψ.domain c]
    simp only [update, sat, domain_update, Stream'.append_append_stream,
      drop_append_stream_of_length ht]
    refine and_congr (sat_update M φ n j hdr hc' hd) ?_
    rw [← Stream'.append_append_stream (c.drop ψ.domain) c',
      ← Stream'.append_append_stream (c.drop ψ.domain) c']
    exact sat_update M ψ n (j + φ.domain) ht (by simp [hdr, hc', Nat.add_comm]) hd

-- Observation 12
theorem entails_update_self (φ : Formula) : φ ⊨ φ.update φ.domain 0 := by
  intro E M g e c hc hsat
  refine ⟨c, by rw [domain_update, hc], ?_⟩
  have := sat_update M φ φ.domain 0 (g := g) (c := c) (c' := []) (d := c) (e := e) hc rfl hc
  rw [Stream'.nil_append_stream, Stream'.nil_append_stream] at this
  exact this.2 hsat

/-- An extra premise preserves a conclusion once later pronouns are updated for its witnesses, which
is acute monotonicity (Observation 12). -/
theorem entails_update_of_entails {φ φ' ψ : Formula} (h : (φ ⋀ φ') ⊨ ψ) (χ : Formula) :
    ((φ ⋀ χ) ⋀ φ'.update χ.domain 0) ⊨ ψ.update χ.domain φ'.domain := by
  intro E M g e c hc hsat
  have h₁ : (c.take φ'.domain).length = φ'.domain := by
    simp only [domain, domain_update] at hc; simp [List.length_take, hc]
  have h₂ : ((c.drop φ'.domain).take χ.domain).length = χ.domain := by
    simp only [domain, domain_update] at hc; simp [List.length_take, List.length_drop, hc]
  have h₃ : ((c.drop φ'.domain).drop χ.domain).length = φ.domain := by
    simp only [domain, domain_update] at hc; simp [List.length_drop, hc]; omega
  rw [← List.take_append_drop φ'.domain c, ← List.take_append_drop χ.domain (c.drop φ'.domain)]
    at hsat ⊢
  simp only [sat, domain_update, Stream'.append_append_stream] at hsat
  rw [drop_append_stream_of_length h₁, drop_append_stream_of_length h₂] at hsat
  obtain ⟨⟨hφ, hχ⟩, hφ'⟩ := hsat
  have key := sat_update M φ' χ.domain 0 (g := g) (c := c.take φ'.domain) (c' := [])
    (d := (c.drop φ'.domain).take χ.domain) (e := (c.drop φ'.domain).drop χ.domain ++ₛ e)
    h₁ rfl h₂
  rw [Stream'.nil_append_stream, Stream'.nil_append_stream] at key
  replace hφ' := key.1 hφ'
  obtain ⟨a, ha, hψ⟩ := h M g e (c.take φ'.domain ++ (c.drop φ'.domain).drop χ.domain)
    (by rw [List.length_append, h₁, h₃, domain, Nat.add_comm]) (by
      rw [sat, Stream'.append_append_stream, drop_append_stream_of_length h₁]
      exact ⟨hφ, hφ'⟩)
  refine ⟨a, by rw [domain_update, ha], ?_⟩
  rw [Stream'.append_append_stream] at hψ
  simp only [Stream'.append_append_stream]
  exact (sat_update M ψ χ.domain φ'.domain ha h₁ h₂).2 hψ

end Formula

/-! ### Contents, update and support, Chapter 3 -/

section Intensional

variable {W : Type*}

/-- Contents, Definition 1 of Chapter 3: the worlds at which the formula is satisfied against
an assignment and a sequence of witness concepts, functions from worlds to individuals. -/
def content (M : W → Model E) (g : ℕ → W → E) (γ : Stream' (W → E)) : Formula → Set W
  | .atom R ts => {w | (M w).interp R (ts.map (Term.eval (M w) (λ x => g x w) (γ.map (· w))))}
  | .neg φ => {w | ¬ ∃ c : List (W → E), c.length = φ.domain ∧ w ∈ content M g (c ++ₛ γ) φ}
  | .exists_ x φ => content M (Function.update g x γ.head) γ.tail φ
  | .conj φ ψ => content M g (γ.drop ψ.domain) φ ∩ content M g γ ψ

/-- Update, Definition 2 of Chapter 3: an atom keeps the worlds satisfying it, a negation
removes the worlds any witnesses for its scope would keep, an existential updates with its
scope under the witness concept, and a conjunction composes. -/
def update (M : W → Model E) (g : ℕ → W → E) (γ : Stream' (W → E)) (τ : Set W) :
    Formula → Set W
  | .atom R ts =>
    {w ∈ τ | (M w).interp R (ts.map (Term.eval (M w) (λ x => g x w) (γ.map (· w))))}
  | .neg φ => {w ∈ τ | ¬ ∃ c : List (W → E), c.length = φ.domain ∧ w ∈ update M g (c ++ₛ γ) τ φ}
  | .exists_ x φ => update M (Function.update g x γ.head) γ.tail τ φ
  | .conj φ ψ => update M g γ (update M g (γ.drop ψ.domain) τ φ) ψ

/-- Support, Definition 3 of Chapter 3: an atom is supported throughout the state, a negation
when no consistent substate supports its scope under any witnesses, an existential through its
scope under the witness concept, and a conjunction conjunct by conjunct. -/
def Supports (M : W → Model E) (g : ℕ → W → E) (γ : Stream' (W → E)) (σ : Set W) :
    Formula → Prop
  | .atom R ts => ∀ w ∈ σ, (M w).interp R (ts.map (Term.eval (M w) (λ x => g x w) (γ.map (· w))))
  | .neg φ => ¬ ∃ ρ, ρ.Nonempty ∧ ρ ⊆ σ ∧
      ∃ c : List (W → E), c.length = φ.domain ∧ Supports M g (c ++ₛ γ) ρ φ
  | .exists_ x φ => Supports M (Function.update g x γ.head) γ.tail σ φ
  | .conj φ ψ => Supports M g (γ.drop ψ.domain) σ φ ∧ Supports M g γ σ ψ

variable (M : W → Model E)

private theorem update_apply_world (g : ℕ → W → E) (x : ℕ) (b : W → E) (w : W) :
    (λ y => Function.update g x b y w) = Function.update (λ y => g y w) x (b w) := by
  funext y; simp only [Function.update_apply]; split_ifs <;> rfl

-- Observation 15
theorem content_eq : ∀ (φ : Formula) (g : ℕ → W → E) (γ : Stream' (W → E)),
    content M g γ φ = {w | Formula.sat (M w) (λ x => g x w) (γ.map (· w)) φ}
  | .atom _ _, _, _ => rfl
  | .neg φ, g, γ => by
    ext w
    simp only [content, Set.mem_ofPred_eq, Formula.sat, content_eq φ, Stream'.map_append_stream]
    refine not_congr ⟨λ ⟨c, hc, h⟩ => ⟨c.map (· w), by simp [hc], h⟩,
      λ ⟨c, hc, h⟩ => ⟨c.map (λ b _ => b), by simp [hc], ?_⟩⟩
    simpa [List.map_map, Function.comp_def] using h
  | .exists_ x φ, g, γ => by
    ext w
    simp only [content, content_eq φ, Set.mem_ofPred_eq, Formula.sat, update_apply_world,
      Stream'.head_map, Stream'.map_tail]
  | .conj φ ψ, g, γ => by
    ext w
    simp only [content, content_eq φ, content_eq ψ, Set.mem_inter_iff, Set.mem_ofPred_eq,
      Formula.sat, Stream'.drop_map]

-- Observation 16
theorem update_eq : ∀ (φ : Formula) (g : ℕ → W → E) (γ : Stream' (W → E)) (τ : Set W),
    update M g γ τ φ = DynamicSemantics.CCP.up (content M g γ φ) τ
  | .atom _ _, _, _, _ => rfl
  | .neg φ, g, γ, τ => by
    ext w
    simp only [update, content, DynamicSemantics.CCP.up, Set.mem_inter_iff, Set.mem_ofPred_eq,
      update_eq φ]
    exact ⟨λ ⟨hw, h⟩ => ⟨hw, λ ⟨c, hc, hm⟩ => h ⟨c, hc, hw, hm⟩⟩,
      λ ⟨hw, h⟩ => ⟨hw, λ ⟨c, hc, _, hm⟩ => h ⟨c, hc, hm⟩⟩⟩
  | .exists_ x φ, g, γ, τ => update_eq φ _ _ τ
  | .conj φ ψ, g, γ, τ => by
    simp only [update, content, update_eq φ, update_eq ψ, DynamicSemantics.CCP.up,
      Set.inter_assoc]

-- Observation 17
theorem supports_iff : ∀ (φ : Formula) (g : ℕ → W → E) (γ : Stream' (W → E)) (σ : Set W),
    Supports M g γ σ φ ↔ σ ⊆ content M g γ φ
  | .atom _ _, _, _, _ => Iff.rfl
  | .neg φ, g, γ, σ => by
    simp only [Supports, content, supports_iff φ, Set.subset_def, Set.mem_ofPred_eq]
    constructor
    · intro h w hw ⟨c, hc, hmem⟩
      exact h ⟨{w}, Set.singleton_nonempty w, Set.singleton_subset_iff.2 hw, c, hc,
        λ v hv => (Set.mem_singleton_iff.1 hv).symm ▸ hmem⟩
    · rintro h ⟨ρ, ⟨w, hw⟩, hρ, c, hc, hsup⟩
      exact h w (hρ w hw) ⟨c, hc, hsup w hw⟩
  | .exists_ x φ, g, γ, σ => supports_iff φ _ _ σ
  | .conj φ ψ, g, γ, σ => by
    simp only [Supports, content, supports_iff φ, supports_iff ψ, Set.subset_inter_iff]

-- Observation 17
theorem supports_iff_update_eq (φ : Formula) (g : ℕ → W → E) (γ : Stream' (W → E))
    (σ : Set W) : Supports M g γ σ φ ↔ update M g γ σ φ = σ := by
  rw [supports_iff, update_eq]
  exact DynamicSemantics.CCP.isFixedPt_up_iff.symm

theorem supports_neg_iff (φ : Formula) (g : ℕ → W → E) (γ : Stream' (W → E)) (σ : Set W) :
    Supports M g γ σ (.neg φ) ↔
      ∀ c : List (W → E), c.length = φ.domain → update M g (c ++ₛ γ) σ φ = ∅ := by
  simp only [supports_iff, content, update_eq, DynamicSemantics.CCP.up, Set.subset_def,
    Set.mem_ofPred_eq, Set.eq_empty_iff_forall_notMem, Set.mem_inter_iff, not_and, not_exists]
  exact ⟨λ h c hc w hw => h w hw c hc, λ h w hw c hc => h c hc w hw⟩

-- Observation 18
theorem inter_subset_update {φ : Formula} {g : ℕ → W → E} {γ : Stream' (W → E)} {σ : Set W}
    (h : Supports M g γ σ φ) (τ : Set W) : σ ∩ τ ⊆ update M g γ τ φ := by
  rw [update_eq, DynamicSemantics.CCP.up, Set.inter_comm]
  exact Set.inter_subset_inter_right τ ((supports_iff M φ g γ σ).1 h)

end Intensional

end Dekker2012
