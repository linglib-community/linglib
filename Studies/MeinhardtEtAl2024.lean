/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Computability.Mealy
public import Linglib.Phonology.Subregular.ISL
public import Linglib.Phonology.Subregular.OSL
public import Linglib.Core.Computability.Subsequential
public import Linglib.Phonology.Subregular.Dependence
public import Linglib.Core.Computability.Bimachine
public import Studies.LamontOHaraSmith2019
public import Studies.McCollumEtAl2020

/-!
# Meinhardt, Mai, Baković and McCollum (2024): Weak determinism and the computational consequences of interaction

Weak determinism is tightened here by a condition on interaction: a change at a target may be
licensed by one side of it, never by the two sides at once. The condition is one shape read twice,
on the states of a bimachine and on the contexts of a function, and [the two
readings agree](##MeinhardtEtAl2024.isNonInteractingBimachineComputable_iff); on a machine it says
that [the output is a union of one change rule per
side](##MeinhardtEtAl2024.isNonInteracting_iff_exists_rules). Bidirectional ATR harmony in Maasai
[meets it](##MeinhardtEtAl2024.maasai_isNonInteractingBimachineComputable), although [its targets
flip from arbitrarily far on either side](##MeinhardtEtAl2024.maasai_twoSidedUnboundedDependence),
while Tutrugbu's conditional blocking and unbounded tonal plateauing are unbounded circumambient
and fail it. Plateauing is weakly deterministic in Heinz and Lai's sense all the same, [so their
class is not contained in this
one](##MeinhardtEtAl2024.exists_isWeaklyDeterministic_not_isNonInteractingBimachineComputable).

## Implementation notes

* The alphabet has four symbols carrying the dominant–recessive distinction. The bidirectional map
  is modelled directly, raising a recessive vowel when a dominant one occurs anywhere, rather than
  as a two-pass composition; the opaque low vowel, the re-paired low vowel, glide effects, and the
  Turkana half of the paper are not represented.
* Bimachines here read no end markers, unlike those of the paper's figures, and their class is
  letter-to-letter, so every output keeps the origin of its input. The paper's cells emit words, and
  it places a bounded two-sided rule in the class by moving outputs between cells; [that rule is
  outside the class here](##MeinhardtEtAl2024.not_isNonInteractingBimachineComputable_boundedRule).
  Word-valued cells, on the other hand, admit [a map that is unbounded
  circumambient](##MeinhardtEtAl2024.exists_isNonInteracting_isUnboundedCircumambient).

## Errata

* Def. 3(a) and Def. 6 quantify over every output, not every change. As printed, Def. 6 fails at
  line (d) of the paper's own Maasai machine in Fig. 8, where a recessive vowel with `q1` on both
  sides stays itself and moving either state alone to `q2` changes it, and [no machine of the kind
  here computes Maasai under it](##MeinhardtEtAl2024.run_ne_maasai_of_forall_output_iff). Both are
  read here over changes, as Def. 5 and the paper's prose ("licensed") read them.

## TODO

* Word-valued cells do not exclude Tutrugbu or plateauing through `IsUnboundedCircumambient` alone.
  Their flank witnesses have a filler run, which a pumping argument should exploit.

## References

* [meinhardt-mai-bakovic-mccollum-2024]
* [heinz-lai-2013]
* [chandlee-eyraud-heinz-2015]
* [wilson-2006]
* [mccollum-bakovic-mai-meinhardt-2020]
* [lamont-ohara-smith-2019]
-/

@[expose] public section

namespace MeinhardtEtAl2024

open Subregular

/-- A minimal alphabet captures the dominance-vs-recessive distinction that drives Maasai ATR
harmony (p. 1203). Four symbols stand in for the relevant phonological contrasts.

* `recL` — a recessive [-ATR] vowel (e.g., /ɪ/, /ʊ/), surfacing as
  [-ATR] absent harmony and raising to [+ATR] under spread.
* `recH` — a recessive vowel surfacing [+ATR] (e.g., /i/, /u/), the
  raised form of `recL`, and transparent to further spread.
* `dom` — a dominant vowel, underlyingly specified [+ATR] and the trigger
  of spreading (the paper's load-bearing distinction).
* `a` — the opaque /a/. Blocks spread.

Consonants are omitted as they are transparent to the harmony. -/
inductive Seg
  | recL
  | recH
  | dom
  | a
  deriving DecidableEq, Repr, Fintype

/-- **OSL rule encoding rightward [+ATR] spreading from a dominant root.**

With k = 2 the output decision at each position depends on the
**single immediately preceding output symbol**, as in the canonical OSL fragment of
phonological maps of Chandlee, Eyraud and Heinz. The rule emits as follows.

* Current input is `dom` → emit `recH` (dominant always surfaces as
  [+ATR]).
* Current input is `a` → emit `a` (opaque, blocks spread; the next
  position's output context will be `a`, not a +ATR vowel).
* Current input is `recH` → emit `recH` (already +ATR, passes through).
* Current input is `recL` and previous output was `recH` → emit `recH`
  (spread continues).
* Current input is `recL` otherwise → emit `recL` (no spread to here).

Single-direction iterative spreading patterns are OSL but not ISL, after Chandlee, Eyraud and
Heinz, because the output decision depends on the
*output* history (how far spread has propagated) rather than the *input*
history alone: the residuals factor through no window of the input
(`rightwardATR_osl_residual_not_factorsThrough_rtake`), so the map fails their tail condition
for ISL, not only membership in the prefix-preserving class of `Subregular.ISL`. -/
def rightwardATR_osl : OSLRule 2 Seg Seg where
  windowOutput outputWindow currentInput :=
    match currentInput, outputWindow with
    | .a, _ => [.a]
    | .dom, _ => [.recH]
    | .recH, _ => [.recH]
    | .recL, .recH :: _ => [.recH]
    | .recL, _ => [.recL]

/-- The dominant root triggers spread to the following recessive vowel (Ex 1a-i, rightward
half), in a toy encoding of the rightward portion of /kɪ-√noŋ-ʊ/ → [ki-√noŋ-u] as input
`[dom, recL]` and output `[recH, recH]`. -/
example : rightwardATR_osl.apply [.dom, .recL] = [.recH, .recH] := by decide

/-- Spread continues across multiple recessive vowels (Ex 1a-ii, rightward half). -/
example : rightwardATR_osl.apply [.dom, .recL, .recL] = [.recH, .recH, .recH] := by
  decide

/-- The opaque /a/ blocks rightward spread, so recessive vowels after it remain [-ATR]. -/
example : rightwardATR_osl.apply [.dom, .a, .recL] = [.recH, .a, .recL] := by
  decide

/-- Without a dominant trigger, a string of recessive vowels passes through unchanged. -/
example : rightwardATR_osl.apply [.recL, .recL] = [.recL, .recL] := by decide

theorem rightwardATR_osl_isLeftOutputStrictlyLocal :
    IsLeftOutputStrictlyLocal 2 rightwardATR_osl.apply :=
  rightwardATR_osl.isLeftOutputStrictlyLocal_apply

private theorem rightwardATR_osl_apply_dom_replicate (n : ℕ) :
    rightwardATR_osl.apply (.dom :: List.replicate n .recL) = List.replicate (n + 1) .recH := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ', ← List.cons_append, OSLRule.apply_append_singleton, ih,
      List.replicate_succ' (n := n + 1), List.replicate_succ', List.rtake_concat_succ,
      List.rtake_zero, List.nil_append]
    rfl

private theorem rightwardATR_osl_apply_replicate (n : ℕ) :
    rightwardATR_osl.apply (List.replicate n .recL) = List.replicate n .recL := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ', OSLRule.apply_append_singleton, ih]
    cases n with
    | zero => rfl
    | succ m =>
      rw [List.replicate_succ', List.rtake_concat_succ, List.rtake_zero, List.nil_append]
      rfl

theorem rightwardATR_osl_residual_not_factorsThrough_rtake (k : ℕ) :
    ¬ rightwardATR_osl.apply.residual.FactorsThrough fun u ↦ u.rtake (k - 1) := fun h ↦ by
  have hpre := rightwardATR_osl_isLeftOutputStrictlyLocal.isPrefix
  have hw : ∀ s : Seg, (s :: List.replicate (k - 1) .recL).rtake (k - 1) =
      List.replicate (k - 1) .recL := fun s ↦ by
    simpa using List.rtake_append_length (l₁ := [s]) (l₂ := List.replicate (k - 1) Seg.recL)
  have e := congrFun (h (a := .dom :: List.replicate (k - 1) .recL)
    (b := .recL :: List.replicate (k - 1) .recL) (by simp only [hw])) [.recL]
  rw [Function.residual_eq_drop (hpre _), Function.residual_eq_drop (hpre _)] at e
  simp only [List.cons_append, ← List.replicate_succ',
    rightwardATR_osl_apply_dom_replicate, ← List.replicate_succ,
    rightwardATR_osl_apply_replicate, List.length_replicate, List.drop_replicate,
    Nat.add_sub_cancel_left] at e
  exact absurd e (by decide)

theorem rightwardATR_osl_not_isLeftInputStrictlyLocal (k : ℕ) :
    ¬ IsLeftInputStrictlyLocal k rightwardATR_osl.apply := fun h ↦
  rightwardATR_osl_residual_not_factorsThrough_rtake k h.factorsThrough_residual

theorem rightwardATR_osl_isLeftSubsequential :
    IsLeftSubsequential rightwardATR_osl.apply :=
  rightwardATR_osl_isLeftOutputStrictlyLocal.isLeftSubsequential

/-! ### Weak determinism -/

section WeakDeterminism

variable {L R α β : Type*}

/-- The value of `c` at `(l, a, r)` is licensed by one side alone: fixing the symbol and one of the
two contexts fixes it. This is the disjunction of Def. 6, for any function of a left context, a
symbol and a right context. -/
def OneSidedAt (c : L → α → R → β) (l : L) (a : α) (r : R) : Prop :=
  (∀ r', c l a r' = c l a r) ∨ ∀ l', c l' a r = c l a r

/-- The output of the symbol `a` of the word `p ++ a :: s`. -/
def contextOutput (f : List α → List α) (p : List α) (a : α) (s : List α) : Option α :=
  (f (p ++ a :: s))[p.length]?

/-- `f` is semiambient (Def. 3(a), read over changes) when each change it makes at a symbol is
licensed by the context on one side alone. -/
def IsSemiambient (f : List α → List α) : Prop :=
  ∀ p a s, contextOutput f p a s ≠ some a → OneSidedAt (contextOutput f) p a s

/-- A bimachine is non-interacting (Def. 6, read over changes) when each cell that changes its
symbol is licensed by one state alone. -/
def IsNonInteracting (B : Bimachine L R α α) : Prop :=
  ∀ l a r, B.output l a r ≠ [a] → OneSidedAt B.output l a r

/-- `f` is computed by a finite non-interacting letter-to-letter bimachine. -/
def IsNonInteractingBimachineComputable (f : List α → List α) : Prop :=
  ∃ (L : Type) (_ : Fintype L) (R : Type) (_ : Fintype R) (B : Bimachine L R α α),
    B.IsLetterToLetter ∧ IsNonInteracting B ∧ B.run = f

private theorem exists_rule {ι : Type*} (out : ι → List α) (a : α) :
    ∃ y, (y ≠ a → ∀ i, out i = [y]) ∧ (y = a → ∀ y', y' ≠ a → ¬ ∀ i, out i = [y']) := by
  by_cases h : ∃ y, y ≠ a ∧ ∀ i, out i = [y]
  · obtain ⟨y, hy, hi⟩ := h
    exact ⟨y, fun _ ↦ hi, fun e ↦ absurd e hy⟩
  · exact ⟨a, fun h' ↦ absurd rfl h', fun _ y' hy' hi ↦ h ⟨y', hy', hi⟩⟩

/-- A letter-to-letter bimachine is non-interacting exactly when its output is the union of one
change rule per side, which agree where both fire. This is the machine-level content of Def. 5,
whose alignment with Def. 6 the paper claims with the proof deferred (p. 1221, fn. 20). -/
theorem isNonInteracting_iff_exists_rules [DecidableEq α] {B : Bimachine L R α α} :
    B.IsLetterToLetter ∧ IsNonInteracting B ↔
      ∃ (ruleL : L → α → α) (ruleR : R → α → α), ∀ l a r,
        (ruleL l a ≠ a → ruleR r a ≠ a → ruleL l a = ruleR r a) ∧
          B.output l a r = [if ruleL l a = a then ruleR r a else ruleL l a] := by
  constructor
  · rintro ⟨⟨w⟩, hB⟩
    choose ruleL hL hL' using fun l a ↦ exists_rule (B.output l a) a
    choose ruleR hR hR' using fun r a ↦ exists_rule (B.output · a r) a
    refine ⟨ruleL, ruleR, fun l a r ↦
      ⟨fun hl hr ↦ by simpa using (hL l a hl r).symm.trans (hR r a hr l), ?_⟩⟩
    by_cases hl : ruleL l a = a
    · rw [ite_eq_left hl]
      by_cases hr : ruleR r a = a
      · rw [hr]
        by_contra hne
        have hc : w.cell l a r ≠ a := fun e ↦ hne (by rw [w.output_eq, e])
        rcases hB l a r hne with h | h
        · exact hL' l a hl _ hc fun r' ↦ (h r').trans (w.output_eq l a r)
        · exact hR' r a hr _ hc fun l' ↦ (h l').trans (w.output_eq l a r)
      · exact hR r a hr l
    · rw [ite_eq_right hl]
      exact hL l a hl r
  · rintro ⟨ruleL, ruleR, h⟩
    refine ⟨⟨⟨fun l a r ↦ if ruleL l a = a then ruleR r a else ruleL l a,
      fun l a r ↦ (h l a r).2⟩⟩, fun l a r hne ↦ ?_⟩
    by_cases hl : ruleL l a = a
    · have hr : ruleR r a ≠ a := fun hr ↦ hne (by rw [(h l a r).2, ite_eq_left hl, hr])
      refine .inr fun l' ↦ ?_
      rw [(h l' a r).2, (h l a r).2, ite_eq_left hl]
      split_ifs with hl'
      · rfl
      · rw [(h l' a r).1 hl' hr]
    · exact .inl fun r' ↦ by rw [(h l a r').2, (h l a r).2, ite_eq_right hl, ite_eq_right hl]

/-- The reachable part of a bimachine. -/
private def trim (B : Bimachine L R α β) :
    Bimachine (Set.range B.lState) (Set.range B.rState) α β where
  lInit := ⟨B.lInit, [], rfl⟩
  lStep l a := ⟨B.lStep l a, by
    obtain ⟨_, p, rfl⟩ := l
    exact ⟨p ++ [a], by simp [Bimachine.lState_append]⟩⟩
  rInit := ⟨B.rInit, [], rfl⟩
  rStep r a := ⟨B.rStep r a, by
    obtain ⟨_, s, rfl⟩ := r
    exact ⟨a :: s, rfl⟩⟩
  output l a r := B.output l a r

private theorem coe_rState_trim (B : Bimachine L R α β) (s : List α) :
    ((trim B).rState s : R) = B.rState s := by
  induction s with
  | nil => rfl
  | cons a s ih => exact congrArg (B.rStep · a) ih

private theorem run_trim (B : Bimachine L R α β) : (trim B).run = B.run := by
  have h : ∀ (xs : List α) (l : Set.range B.lState), (trim B).runFrom l xs = B.runFrom l xs := by
    intro xs
    induction xs with
    | nil => exact fun _ ↦ rfl
    | cons a xs ih =>
      intro l
      rw [Bimachine.runFrom_cons, Bimachine.runFrom_cons, ih]
      exact congrArg (B.output l a · ++ B.runFrom (B.lStep l a) xs) (coe_rState_trim B xs)
  exact funext fun xs ↦ h xs _

private theorem contextOutput_run {B : Bimachine L R α α} (w : B.LetterToLetter) (p : List α)
    (a : α) (s : List α) :
    contextOutput B.run p a s = some (w.cell (B.lState p) a (B.rState s)) := by
  simp [contextOutput, w.getElem?_run]

/-- A function computed by a finite letter-to-letter bimachine is semiambient exactly when some
such machine is non-interacting. So the condition on machines is one on functions, the
identification of semiambience with weak determinism the paper states (p. 1202). -/
theorem isNonInteractingBimachineComputable_iff {f : List α → List α} :
    IsNonInteractingBimachineComputable f ↔
      IsLengthPreservingBimachineComputable f ∧ IsSemiambient f := by
  constructor
  · rintro ⟨L, _, R, _, B, ⟨w⟩, hB, rfl⟩
    refine ⟨⟨L, ‹_›, R, ‹_›, B, ⟨w⟩, rfl⟩, fun p a s hc ↦ ?_⟩
    rw [contextOutput_run w, ne_eq, Option.some_inj] at hc
    rcases hB _ a _ (by rwa [w.output_eq, ne_eq, List.singleton_inj]) with h | h
    · exact .inl fun s' ↦ by simp only [contextOutput_run w, Option.some_inj, w.cell_inj, h]
    · exact .inr fun p' ↦ by simp only [contextOutput_run w, Option.some_inj, w.cell_inj, h]
  · rintro ⟨⟨L, _, R, _, B, ⟨w⟩, rfl⟩, hf⟩
    refine ⟨Set.range B.lState, Fintype.ofFinite _, Set.range B.rState, Fintype.ofFinite _, trim B,
      ⟨⟨fun l a r ↦ w.cell l a r, fun _ _ _ ↦ w.output_eq _ _ _⟩⟩, ?_, run_trim B⟩
    rintro ⟨_, p, rfl⟩ a ⟨_, s, rfl⟩ hne
    have hc : contextOutput B.run p a s ≠ some a := by
      rw [contextOutput_run w, ne_eq, Option.some_inj]
      exact fun e ↦ hne (by simpa [trim, e] using w.output_eq (B.lState p) a (B.rState s))
    rcases hf p a s hc with h | h
    · refine .inl ?_
      rintro ⟨_, s', rfl⟩
      have := h s'
      simp only [contextOutput_run w, Option.some_inj, w.cell_inj] at this
      exact this
    · refine .inr ?_
      rintro ⟨_, p', rfl⟩
      have := h p'
      simp only [contextOutput_run w, Option.some_inj, w.cell_inj] at this
      exact this

private theorem contextOutput_take_drop (f : List α → List α) {w : List α} {i : ℕ} {a : α}
    (h : w[i]? = some a) : contextOutput f (w.take i) a (w.drop (i + 1)) = (f w)[i]? := by
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp h
  rw [contextOutput, ← List.drop_eq_getElem_cons hi, List.take_append_drop, List.length_take,
    Nat.min_eq_left hi.le]

theorem not_isSemiambient_of_isUnboundedCircumambient {f : List α → List α}
    (hf : IsUnboundedCircumambient f) : ¬ IsSemiambient f := fun hs ↦ by
  obtain ⟨base, i, hi, hchange, hw⟩ := hf 0
  obtain ⟨uL, hL, hrevL⟩ := hw .left
  obtain ⟨uR, hR, hrevR⟩ := hw .right
  have ha : base[i]? = some base[i] := List.getElem?_eq_getElem hi
  have hc : contextOutput f (base.take i) base[i] (base.drop (i + 1)) ≠ some base[i] := by
    rwa [contextOutput_take_drop f ha, ← ha]
  rcases hs _ _ _ hc with h | h
  · have := h (uR.drop (i + 1))
    rw [contextOutput_take_drop f ha, List.take_eq_take_of_le hR.2 (by omega),
      contextOutput_take_drop f (hR.getElem?_eq.trans ha)] at this
    exact hchange (this.symm.trans hrevR)
  · have := h (uL.take i)
    rw [contextOutput_take_drop f ha, List.drop_eq_drop_of_le hL.2 (by omega),
      contextOutput_take_drop f (hL.getElem?_eq.trans ha)] at this
    exact hchange (this.symm.trans hrevL)

theorem not_isNonInteractingBimachineComputable_of_isUnboundedCircumambient {f : List α → List α}
    (hf : IsUnboundedCircumambient f) : ¬ IsNonInteractingBimachineComputable f := fun h ↦
  not_isSemiambient_of_isUnboundedCircumambient hf (isNonInteractingBimachineComputable_iff.mp h).2

theorem isNonInteractingBimachineComputable_of_isMealyComputable {f : List α → List α}
    (hf : IsMealyComputable f) : IsNonInteractingBimachineComputable f :=
  have ⟨σ, _, T, hT⟩ := hf
  ⟨σ, ‹_›, Unit, inferInstance, T.toBimachine, ⟨⟨fun l a _ ↦ T.output l a, fun _ _ _ ↦ rfl⟩⟩,
    fun _ _ _ _ ↦ .inl fun _ ↦ rfl, T.toBimachine_run.trans hT⟩

end WeakDeterminism

/-! ### Bidirectional Maasai harmony

Maasai dominant-recessive ATR harmony spreads [+ATR] from a dominant root to recessive
vowels on *both* sides. Modelled here in its non-opaque core: a recessive `recL` raises
to `recH` iff the word contains a dominant vowel anywhere. This is a union of two independent
spreading passes, so it is semiambient, although a recessive's surface ATR co-varies with
information unboundedly far on either side. -/

/-- Bidirectional dominant-recessive harmony in its non-opaque core, under which a recessive
raises iff the word has a dominant trigger anywhere. -/
def maasai (xs : List Seg) : List Seg :=
  xs.map fun s ↦ if Seg.dom ∈ xs ∧ s = .recL then .recH else s

/-- The non-interacting bimachine, whose state on each side tracks a dominant seen on that
side, raising a recessive if *either* side has one as a union of one-sided rules. -/
def maasaiBM : Bimachine Bool Bool Seg Seg :=
  .ofFlags (· == .dom) (· == .dom) fun l s r ↦
    if (l = true ∨ r = true) ∧ s = .recL then .recH else s

theorem maasaiBM_isNonInteracting : IsNonInteracting maasaiBM :=
  (isNonInteracting_iff_exists_rules.mpr ⟨fun l s ↦ if l = true ∧ s = .recL then .recH else s,
    fun r s ↦ if r = true ∧ s = .recL then .recH else s, by decide⟩).2

private theorem dom_mem_iff {xs : List Seg} {i : ℕ} (h : xs[i]? = some .recL) :
    Seg.dom ∈ xs ↔ Seg.dom ∈ xs.take i ∨ Seg.dom ∈ xs.drop (i + 1) := by
  obtain ⟨hi, hs⟩ := List.getElem?_eq_some_iff.mp h
  conv_lhs => rw [← List.take_append_drop i xs, List.drop_eq_getElem_cons hi, hs]
  simp

theorem maasaiBM_run : maasaiBM.run = maasai := by
  funext xs
  refine List.ext_getElem? fun i ↦ ?_
  rw [maasaiBM, Bimachine.getElem?_ofFlags_run, maasai, List.getElem?_map]
  cases h : xs[i]? with
  | none => rfl
  | some s =>
    cases s
    · simp [dom_mem_iff h]
    all_goals simp

/-- Maasai harmony, in its non-opaque core, is computed by a non-interacting bimachine (Fig. 8). -/
theorem maasai_isNonInteractingBimachineComputable : IsNonInteractingBimachineComputable maasai :=
  ⟨Bool, inferInstance, Bool, inferInstance, maasaiBM, ⟨Bimachine.ofFlags_letterToLetter _ _ _⟩,
    maasaiBM_isNonInteracting, maasaiBM_run⟩

/-- Def. 6 as printed, over every output rather than every change, admits no bimachine for Maasai:
the output of a lone recessive vowel would be fixed by one side, yet a dominant vowel on either
side raises it. -/
theorem run_ne_maasai_of_forall_output_iff {L R : Type*} (B : Bimachine L R Seg Seg)
    (h : ∀ l x r y, B.output l x r = y ↔
      (∀ r', B.output l x r' = y) ∨ ∀ l', B.output l' x r = y) : B.run ≠ maasai := fun hB ↦ by
  have hone : B.output B.lInit .recL B.rInit = [.recL] := by
    simpa [Bimachine.run, maasai] using congrFun hB [Seg.recL]
  rcases (h _ _ _ _).mp hone with hr | hl
  · have := congrFun hB [Seg.recL, Seg.dom]
    simp [Bimachine.run, hr, maasai] at this
  · have := congrArg List.getLast? (congrFun hB [Seg.dom, Seg.recL])
    simp [Bimachine.run, hl, maasai] at this

theorem maasai_twoSidedUnboundedDependence : TwoSidedUnboundedDependence maasai := by
  refine .of_flanks (fill := Seg.recL) (xOn := Seg.recL) (yOn := Seg.recL)
    (xOff := Seg.dom) (yOff := Seg.dom)
    (n := fun d ↦ 2 * d + 1) (t := fun d ↦ d + 1)
    (fun d ↦ by omega) (fun d ↦ by omega) (fun d ↦ ?_) (fun d ↦ ?_) <;>
  · have hb : Seg.dom ∉ flankWord Seg.recL Seg.recL Seg.recL (2 * d + 1) := by
      simp [flankWord, List.mem_replicate]
    have hp : ∀ y, Seg.dom ∈ flankWord Seg.dom Seg.recL y (2 * d + 1) := fun y ↦ by
      simp [flankWord]
    have hp' : ∀ x, Seg.dom ∈ flankWord x Seg.recL Seg.dom (2 * d + 1) := fun x ↦ by
      simp [flankWord]
    simp [maasai, getElem?_flankWord_mid (show 0 < d + 1 by omega)
      (show d + 1 ≤ 2 * d + 1 by omega), hb, hp, hp']

-- Def. 3
theorem maasai_isSemiambient : IsSemiambient maasai :=
  (isNonInteractingBimachineComputable_iff.mp maasai_isNonInteractingBimachineComputable).2

theorem maasai_not_isUnboundedCircumambient : ¬ IsUnboundedCircumambient maasai := fun h ↦
  not_isSemiambient_of_isUnboundedCircumambient h maasai_isSemiambient

theorem maasai_not_leftSubsequential : ¬ IsLeftSubsequential maasai :=
  maasai_twoSidedUnboundedDependence.not_isSubsequential (fun _ ↦ by simp [maasai]) .left

/-! ### Tutrugbu

Tutrugbu's conditional blocking, the paper's (3), is unbounded circumambient (Def. 2), so it is not
semiambient and no non-interacting bimachine computes it. -/

-- Def. 3
theorem tutrugbu_not_isSemiambient : ¬ IsSemiambient McCollumEtAl2020.tutrugbu.map :=
  not_isSemiambient_of_isUnboundedCircumambient McCollumEtAl2020.tutrugbu_isUnboundedCircumambient

theorem tutrugbu_not_isNonInteractingBimachineComputable :
    ¬ IsNonInteractingBimachineComputable McCollumEtAl2020.tutrugbu.map :=
  not_isNonInteractingBimachineComputable_of_isUnboundedCircumambient
    McCollumEtAl2020.tutrugbu_isUnboundedCircumambient

/-! ### Unbounded tonal plateauing

Plateauing, the paper's (2), is unbounded circumambient (Def. 2), so no non-interacting bimachine
computes it. Yet it is weakly deterministic in Heinz and Lai's sense, by the phonotactic code of
Lamont, O'Hara and Smith that §5.2 and Fig. 12 take up: their first pass is length- and
alphabet-preserving and still tells the second pass what lies beyond its reach. -/

theorem utp_not_isNonInteractingBimachineComputable :
    ¬ IsNonInteractingBimachineComputable Tone.utp.map :=
  not_isNonInteractingBimachineComputable_of_isUnboundedCircumambient
    Tone.utp.isUnboundedCircumambient

theorem exists_isWeaklyDeterministic_not_isNonInteractingBimachineComputable :
    ∃ f : List Tone.AssociationState → List Tone.AssociationState,
      IsWeaklyDeterministic f ∧ ¬ IsNonInteractingBimachineComputable f :=
  ⟨Tone.utp.map, LamontOHaraSmith2019.utp_isWeaklyDeterministic,
    utp_not_isNonInteractingBimachineComputable⟩

/-! ### A bounded two-sided rule

The rule `A → B / C __ D` of p. 1220, with `A` the recessive, `B` its raised form and `C`, `D` the
dominant vowel. The paper's cells move its output to the cell of `D` or of `C`; a cell emitting one
letter must decide at `A`, from both sides. -/

/-- The rule, given the symbol before the word. -/
def boundedRule : Option Seg → List Seg → List Seg
  | _, [] => []
  | _, [x] => [x]
  | p, x :: y :: xs =>
    (if p = some .dom ∧ x = .recL ∧ y = .dom then .recH else x) :: boundedRule (some x) (y :: xs)

/-- The transducer holding back one symbol, which it settles on reading the next. -/
private def boundedRuleT : SubsequentialTransducer (Option Seg × Option Seg) Seg Seg where
  start := (none, none)
  step s x := (s.2.or s.1, some x)
  output s x := match s with
    | (_, none) => []
    | (p, some y) => [if p = some .dom ∧ y = .recL ∧ x = .dom then .recH else y]
  finalOutput s := s.2.toList

private theorem run_boundedRuleT : boundedRuleT.run = boundedRule none := by
  have h : ∀ (xs : List Seg) (p : Option Seg) (x : Seg),
      boundedRuleT.runFrom (p, some x) xs = boundedRule p (x :: xs) := by
    intro xs
    induction xs with
    | nil => exact fun _ _ ↦ rfl
    | cons y xs ih =>
      intro p x
      rw [SubsequentialTransducer.runFrom_cons]
      exact congrArg _ (ih (some x) y)
  funext xs
  cases xs with
  | nil => rfl
  | cons x xs => exact h xs none x

example : boundedRule none [.dom, .recL, .dom] = [.dom, .recH, .dom] := by decide

example : boundedRule none [.recL, .recL, .dom] = [.recL, .recL, .dom] := by decide

theorem isLeftSubsequential_boundedRule : IsLeftSubsequential (boundedRule none) :=
  run_boundedRuleT ▸ boundedRuleT.isLeftSubsequential

-- p. 1220
theorem not_isNonInteractingBimachineComputable_boundedRule :
    ¬ IsNonInteractingBimachineComputable (boundedRule none) := fun h ↦ by
  rcases (isNonInteractingBimachineComputable_iff.mp h).2 [.dom] .recL [.dom] (by decide) with h | h
  · exact absurd (h []) (by decide)
  · exact absurd (h []) (by decide)

/-! ### Word-valued cells

The letter-to-letter restriction is what makes unbounded circumambience an exclusion. A machine
that may emit words can delete one marker and double a later one, moving the run between them one
cell left. Each of those two changes is licensed by one side, yet a target in the run changes only
given both markers. -/

/-- Two markers `s`, `t` and two letters `o`, `i`. -/
inductive ShiftSym
  | s | t | o | i
  deriving DecidableEq, Repr, Fintype

section WordValued

open ShiftSym

/-- Each state is the nearest marker on its side. A cell deletes an `s` whose next marker is `t` and
doubles a `t` whose previous marker is `s`. -/
def shiftBM : Bimachine (Option ShiftSym) (Option ShiftSym) ShiftSym ShiftSym where
  lInit := none
  lStep l x := match x with
    | s => some s
    | t => some t
    | _ => l
  rInit := none
  rStep r x := match x with
    | s => some s
    | t => some t
    | _ => r
  output l x r := match x with
    | s => if r = some t then [] else [s]
    | t => if l = some s then [t, t] else [t]
    | x => [x]

theorem isNonInteracting_shiftBM : IsNonInteracting shiftBM := fun _ x _ hne ↦ by
  cases x
  · exact .inr fun _ ↦ rfl
  · exact .inl fun _ ↦ rfl
  · exact absurd rfl hne
  · exact absurd rfl hne

private theorem length_runFrom_shiftBM (l : Option ShiftSym) (xs : List ShiftSym) :
    (shiftBM.runFrom l xs).length =
      xs.length + if l = some s ∧ shiftBM.rState xs = some t then 1 else 0 := by
  induction xs generalizing l with
  | nil => simp [shiftBM]
  | cons x xs ih =>
    rw [Bimachine.runFrom_cons, List.length_append, ih, Bimachine.rState_cons]
    cases x <;> simp only [shiftBM] <;> split_ifs <;> simp_all <;> omega

/-- The letters between markers, which pass through unchanged and leave both states alone. -/
private def NoMarker (xs : List ShiftSym) : Prop := ∀ x ∈ xs, x = o ∨ x = i

private theorem shiftBM_append {xs : List ShiftSym} (hxs : NoMarker xs)
    (l : Option ShiftSym) (ys : List ShiftSym) :
    shiftBM.rState (xs ++ ys) = shiftBM.rState ys ∧
      shiftBM.runFrom l (xs ++ ys) = xs ++ shiftBM.runFrom l ys := by
  induction xs generalizing l with
  | nil => exact ⟨rfl, rfl⟩
  | cons x xs ih =>
    have ih' := ih (fun y hy ↦ hxs y (List.mem_cons_of_mem x hy))
    rcases hxs x List.mem_cons_self with rfl | rfl <;>
      exact ⟨(ih' l).1, congrArg (_ :: ·) (ih' l).2⟩

private theorem run_shiftBM_cons {m : List ShiftSym} (hm : NoMarker m) (x y : ShiftSym) :
    shiftBM.run (x :: (m ++ [y])) = shiftBM.output none x (shiftBM.rState [y]) ++
      (m ++ shiftBM.runFrom (shiftBM.lStep none x) [y]) := by
  rw [Bimachine.run, Bimachine.runFrom_cons, (shiftBM_append hm none [y]).1,
    (shiftBM_append hm _ [y]).2]
  rfl

private theorem run_shiftBM_s_t {m : List ShiftSym} (hm : NoMarker m) :
    shiftBM.run (s :: (m ++ [t])) = m ++ [t, t] :=
  run_shiftBM_cons hm s t

private theorem run_shiftBM_o_t {m : List ShiftSym} (hm : NoMarker m) :
    shiftBM.run (o :: (m ++ [t])) = o :: (m ++ [t]) :=
  run_shiftBM_cons hm o t

private theorem run_shiftBM_s_o {m : List ShiftSym} (hm : NoMarker m) :
    shiftBM.run (s :: (m ++ [o])) = s :: (m ++ [o]) :=
  run_shiftBM_cons hm s o

/-- The run at margin `d`: `i` just past the target, far from both markers. -/
private def shiftRun (d : ℕ) : List ShiftSym :=
  List.replicate (d + 1) o ++ i :: List.replicate (d + 1) o

private theorem noMarker_shiftRun (d : ℕ) : NoMarker (shiftRun d) := fun x hx ↦ by
  simp only [shiftRun, List.mem_append, List.mem_cons, List.mem_replicate] at hx
  rcases hx with ⟨-, h⟩ | h | ⟨-, h⟩ <;> simp [h]

private theorem length_shiftRun (d : ℕ) : (shiftRun d).length = 2 * d + 3 := by
  simp [shiftRun]; omega

private theorem getElem?_shiftRun_append (d : ℕ) (ys : List ShiftSym) :
    (shiftRun d ++ ys)[d]? = some o := by
  rw [List.getElem?_append_left (by rw [length_shiftRun]; omega)]
  simp [shiftRun, List.getElem?_append]

/-- Word-valued cells do not exclude unbounded circumambience: this length-preserving machine
licenses each change by one side, and its target needs both. -/
theorem exists_isNonInteracting_isUnboundedCircumambient :
    ∃ (L R : Type) (_ : Fintype L) (_ : Fintype R) (B : Bimachine L R ShiftSym ShiftSym),
      IsNonInteracting B ∧ (∀ w, (B.run w).length = w.length) ∧ IsUnboundedCircumambient B.run := by
  refine ⟨_, _, inferInstance, inferInstance, shiftBM, isNonInteracting_shiftBM,
    fun w ↦ by simpa [Bimachine.run, shiftBM] using length_runFrom_shiftBM none w, fun d ↦ ?_⟩
  have hm := noMarker_shiftRun d
  have hbase : (s :: (shiftRun d ++ [t]))[d + 1]? = some o := getElem?_shiftRun_append d _
  refine ⟨s :: (shiftRun d ++ [t]), d + 1, by simp [length_shiftRun]; omega, ?_, fun e ↦ ?_⟩
  · rw [hbase, run_shiftBM_s_t hm, List.getElem?_append_left (by rw [length_shiftRun]; omega)]
    simp [shiftRun]
  · cases e
    · exact ⟨o :: (shiftRun d ++ [t]), ⟨by simp, by simp⟩, by
        rw [hbase, run_shiftBM_o_t hm]; exact getElem?_shiftRun_append d _⟩
    · refine ⟨s :: (shiftRun d ++ [o]), ⟨by simp, ?_⟩, by
        rw [hbase, run_shiftBM_s_o hm]; exact getElem?_shiftRun_append d _⟩
      simp only [Edge.window_right, show d + 1 + d + 1 = (2 * d + 1) + 1 by omega,
        List.take_succ_cons,
        List.take_append_of_le_length (show 2 * d + 1 ≤ (shiftRun d).length by
          rw [length_shiftRun]; omega)]

end WordValued

end MeinhardtEtAl2024
