module

public import Linglib.Syntax.Minimalist.SyntacticObject.Build
public import Linglib.Syntax.Minimalist.SyntacticObject.Phase

/-!
# Pietraszko (2026): In Defense of the Clause-Internal Phase

This file formalizes the argument of [pietraszko-2026] that VoiceP in Zimbabwean Ndebele is
a phase, from its opacity to A-movement and φ-agreement rather than from footprints of
successive-cyclic movement. A subject may move to Spec,TP and control agreement on T (5), or
stay in situ under default agreement (6); of the three sources of a missing probe–goal
relation (8), the account is locality: T always bears EPP and φ, VoiceP is a phase under the
strong Phase Impenetrability Condition of [chomsky-2000], and Voice bears EPP optionally (9),
(10). A subject that reaches Spec,VoiceP is visible to every head above and, operations being
obligatory when possible with an unchecked EPP tolerated as in [preminger-2014], moves on to
Spec,TP; a subject left in the phase's complement is invisible to them all. Hence movement and
agreement go together (11)–(14) (`simple_clause`); auxiliary constructions agree on every head
or on none and admit no intermediate landing site (16)–(21) (`auxV_uniform`,
`auxV_no_partial`); a reduced clause whose highest head is Asp lets Asp attract the subject on
its own (34)–(42) (`reduced_clause`); a subject that leaves its VoiceP has agreed with T on the
way (25)–(28) (`agrees_of_lt_landing`); and hyperraising yields the four subject positions of
(77) from the EPP of the phase heads alone, the VP-internal one included (69), (76)
(`hyperraising_sites`). The general form is phase-delimited movement (79): movement within a
phase is obligatory (`phase_internal_obligatory`), and a phase head without EPP freezes the
subject below it (`cross_phasal_frozen`). The account with an optional [EPP, φ] on T of
[carstens-mletshe-2015] admits the unattested partial patterns (30), (31) and default
agreement on a T the subject has crossed (25) (`optional_T_overgenerates`), where the phasal
account excludes them.

## Implementation notes

A clause is the list of heads above the subject's base position, bottom-up, each with its
category and whether it bears EPP, a φ-probe, and heads a phase; one bottom-up pass computes
the subject's landing site and the heads it is accessible to: an EPP head attracts an
accessible subject to its specifier and a phase head without EPP freezes it in its complement
(`stateAt`, `landing`, `Accessible`). The rival account is the same derivation with Voice
non-phasal and [EPP, φ] optional on T and Asp. The expletive-pro account of [halpert-2015]
(§3.2), the antifocus account of [zeller-2015] (§4), the modification of [henderson-2006],
object dislocation (55) and the information-structural properties of the two orders are prose.
The trees the derivation builds (`treeAt`) tie the spine to the substrate's phases: on them the
spine's accessibility is [chomsky-2000]'s condition (`simple_accessible_iff`,
`auxV_accessible_iff`, `reduced_accessible_iff`), and [chomsky-2001]'s would let T reach a subject
left in VoiceP (`nextPhase_overgenerates`).

## References

* [pietraszko-2026]
* [chomsky-2000]
* [chomsky-2001]
* [preminger-2014]
* [carstens-mletshe-2015]
* [halpert-2015]
* [zeller-2015]
* [henderson-2006]
-/

@[expose] public section

namespace Pietraszko2026

open Minimalist

/-! ### Clauses and the derivation (§2.2) -/

/-- A head of the clausal spine, as subject movement sees it, has a category and records whether
it bears EPP, a φ-probe, and heads a phase. -/
structure Head where
  cat : Cat
  epp : Bool
  phi : Bool
  phase : Bool
  deriving DecidableEq, Repr

/-- A clause is the list of heads above the subject's base position, bottom-up. -/
abbrev Spine := List Head

/-- The derivational state of the subject records its height, 0 in situ and `i + 1` in the
specifier of the head at index `i`, and whether it is frozen in a phase's complement. -/
structure State where
  height : ℕ
  frozen : Bool
  deriving DecidableEq, Repr

/-- When the head at index `i` is merged, an EPP head attracts an accessible subject to its
specifier, a phase head without EPP freezes an accessible subject in its complement, and
otherwise the subject stays where it is. -/
def step (i : ℕ) (h : Head) (s : State) : State :=
  if s.frozen then s else if h.epp then ⟨i + 1, false⟩ else if h.phase then ⟨s.height, true⟩
  else s

/-- The state after merging the first `n` heads. -/
def stateAt (sp : Spine) : ℕ → State
  | 0 => ⟨0, false⟩
  | n + 1 =>
    match sp[n]? with
    | some h => step n h (stateAt sp n)
    | none => stateAt sp n

/-- The subject's landing site is its height once the clause is built. -/
def landing (sp : Spine) : ℕ := (stateAt sp sp.length).height

/-- The subject is accessible to the head at index `i` when it is not frozen as that head is
merged. -/
def Accessible (sp : Spine) (i : ℕ) : Prop := (stateAt sp i).frozen = false

instance (sp : Spine) (i : ℕ) : Decidable (Accessible sp i) := inferInstanceAs (Decidable (_ = _))

/-- The head at index `i` agrees with the subject when it bears a φ-probe and the subject is
accessible to it. -/
def Agrees (sp : Spine) (i : ℕ) : Prop :=
  match sp[i]? with
  | some h => h.phi = true ∧ Accessible sp i
  | none => False

instance (sp : Spine) (i : ℕ) : Decidable (Agrees sp i) := by
  unfold Agrees; cases sp[i]? <;> infer_instance

/-! ### The heads of Ndebele -/

/-- T, with EPP and φ. -/
def T : Head := ⟨.T, true, true, false⟩

/-- Asp, with EPP and φ (§2.4, §3.1.3). -/
def Asp : Head := ⟨.Asp, true, true, false⟩

/-- Voice, a phase head, with EPP `e` (§2.2). -/
def Voice (e : Bool) : Head := ⟨.Voice, e, false, true⟩

/-- C, a phase head, with EPP `e` (§4). -/
def C (e : Bool) : Head := ⟨.C, e, false, true⟩

/-- The matrix V of a raising verb, with EPP (§4). -/
def raisingV : Head := ⟨.V, true, false, false⟩

/-- A simple clause (9), (10). -/
def simple (e : Bool) : Spine := [Voice e, T]

/-- An auxiliary construction (17), (19): Asp and T above Voice. -/
def auxV (e : Bool) : Spine := [Voice e, Asp, T]

/-- A reduced clause (40): Asp is the highest head. -/
def reduced (e : Bool) : Spine := [Voice e, Asp]

/-- Hyperraising (77): the embedded Voice and T, C, the matrix raising verb, and the matrix
Voice and T. -/
def hyperraising (e₁ e₂ e₃ : Bool) : Spine := [Voice e₃, T, C e₂, raisingV, Voice e₁, T]

/-! ### Predictions (§2.3, §2.4, §3.1.3, §4) -/

/-- Prediction 1 (11)–(14): the subject moves to Spec,TP exactly when T agrees with it, both
exactly when Voice bears EPP. -/
theorem simple_clause (e : Bool) :
    (landing (simple e) = 2 ↔ e) ∧ (Agrees (simple e) 1 ↔ e) ∧ (landing (simple e) = 0 ↔ ¬ e) := by
  cases e <;> decide

/-- Prediction 2 (16)–(20): in an auxiliary construction every head above Voice agrees with the
subject or none does. -/
theorem auxV_uniform (e : Bool) :
    (Agrees (auxV e) 1 ∧ Agrees (auxV e) 2) ∨ (¬ Agrees (auxV e) 1 ∧ ¬ Agrees (auxV e) 2) := by
  cases e <;> decide

/-- (21): the subject is in situ or in Spec,TP, never in an intermediate specifier. -/
theorem auxV_no_partial (e : Bool) : landing (auxV e) = 0 ∨ landing (auxV e) = 3 := by
  cases e <;> decide

/-- Reduced clauses (41), (42): with Asp the highest head, the subject lands in Spec,AspP
exactly when Voice bears EPP, and Asp agrees with it exactly then. -/
theorem reduced_clause (e : Bool) :
    (landing (reduced e) = 2 ↔ e) ∧ (Agrees (reduced e) 1 ↔ e) := by
  cases e <;> decide

/-- Hyperraising (77): the subject stays in situ when the embedded Voice lacks EPP, stops in
the embedded Spec,TP when C lacks EPP, in the matrix VP when the matrix Voice lacks EPP (69),
(76), and reaches the matrix Spec,TP otherwise. -/
theorem hyperraising_sites (e₁ e₂ e₃ : Bool) :
    landing (hyperraising e₁ e₂ e₃)
      = if ¬ e₃ then 0 else if ¬ e₂ then 2 else if ¬ e₁ then 4 else 6 := by
  cases e₁ <;> cases e₂ <;> cases e₃ <;> decide

/-! ### Phase-delimited movement (79) -/

theorem stateAt_succ_of_getElem? {sp : Spine} {n : ℕ} {h : Head} (hn : sp[n]? = some h) :
    stateAt sp (n + 1) = step n h (stateAt sp n) := by
  simp [stateAt, hn]

/-- A frozen subject stays frozen at the same height. -/
theorem frozen_stateAt_succ {sp : Spine} {n : ℕ} (hf : (stateAt sp n).frozen = true) :
    stateAt sp (n + 1) = stateAt sp n := by
  simp only [stateAt]
  cases sp[n]? <;> simp [step, hf]

theorem frozen_stateAt_of_le {sp : Spine} {m n : ℕ} (hmn : m ≤ n)
    (hf : (stateAt sp m).frozen = true) : stateAt sp n = stateAt sp m := by
  induction n with
  | zero => rw [Nat.le_zero.1 hmn]
  | succ n ih =>
    rcases Nat.le_succ_iff.1 hmn with hmn | rfl
    · rw [frozen_stateAt_succ (by rw [ih hmn]; exact hf), ih hmn]
    · rfl

theorem height_step_le {i : ℕ} {h : Head} {s : State} (hs : s.height ≤ i) :
    (step i h s).height ≤ i + 1 := by
  unfold step
  by_cases hf : s.frozen = true <;> by_cases he : h.epp = true <;>
    by_cases hp : h.phase = true <;> simp [hf, he, hp] <;> omega

theorem height_le_height_step {i : ℕ} {h : Head} {s : State} (hs : s.height ≤ i) :
    s.height ≤ (step i h s).height := by
  unfold step
  by_cases hf : s.frozen = true <;> by_cases he : h.epp = true <;>
    by_cases hp : h.phase = true <;> simp [hf, he, hp] <;> omega

/-- The subject never sits above the heads merged so far. -/
theorem height_stateAt_le (sp : Spine) (n : ℕ) : (stateAt sp n).height ≤ n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    simp only [stateAt]
    cases sp[n]? with
    | none => exact ih.trans (Nat.le_succ n)
    | some h => exact height_step_le ih

/-- The subject never moves down. -/
theorem height_stateAt_mono (sp : Spine) {m n : ℕ} (hmn : m ≤ n) :
    (stateAt sp m).height ≤ (stateAt sp n).height := by
  induction n with
  | zero => rw [Nat.le_zero.1 hmn]
  | succ n ih =>
    rcases Nat.le_succ_iff.1 hmn with hmn | rfl
    · refine Nat.le_trans (ih hmn) ?_
      simp only [stateAt]
      cases sp[n]? with
      | none => exact le_rfl
      | some h => exact height_le_height_step (height_stateAt_le sp n)
    · exact le_rfl

/-- Phase-internal movement is obligatory (79i): a head bearing EPP attracts the subject
whenever it is accessible, so the subject lands at least in its specifier. -/
theorem phase_internal_obligatory {sp : Spine} {i : ℕ} {h : Head} (hi : sp[i]? = some h)
    (he : h.epp = true) (ha : Accessible sp i) : i + 1 ≤ landing sp := by
  obtain ⟨hlen, -⟩ := List.getElem?_eq_some_iff.1 hi
  have hstep : stateAt sp (i + 1) = ⟨i + 1, false⟩ := by
    rw [stateAt_succ_of_getElem? hi, step, ite_eq_right (by simpa [Accessible] using ha),
      ite_eq_left he]
  calc i + 1 = (stateAt sp (i + 1)).height := by rw [hstep]
    _ ≤ landing sp := height_stateAt_mono sp hlen

/-- Cross-phasal movement needs EPP on the phase head (79ii): a phase head without EPP freezes
an accessible subject in its complement, so the subject lands below it and no higher head can
reach it. -/
theorem cross_phasal_frozen {sp : Spine} {i : ℕ} {h : Head} (hi : sp[i]? = some h)
    (hp : h.phase = true) (he : h.epp = false) (ha : Accessible sp i) :
    landing sp ≤ i ∧ ∀ j, i < j → ¬ Accessible sp j := by
  have hstep : stateAt sp (i + 1) = ⟨(stateAt sp i).height, true⟩ := by
    rw [stateAt_succ_of_getElem? hi, step, ite_eq_right (by simpa [Accessible] using ha),
      ite_eq_right (by simp [he]), ite_eq_left hp]
  obtain ⟨hlen, -⟩ := List.getElem?_eq_some_iff.1 hi
  refine ⟨?_, fun j hij hj ↦ ?_⟩
  · rw [landing, frozen_stateAt_of_le hlen (by rw [hstep]), hstep]
    exact height_stateAt_le sp i
  · have := frozen_stateAt_of_le (m := i + 1) hij (by rw [hstep])
    simp [Accessible, this, hstep] at hj

/-- Movement past a φ-bearing head requires agreement with it (25)–(28): a subject that
lands above a head was accessible to it. -/
theorem agrees_of_lt_landing {sp : Spine} {i : ℕ} {h : Head} (hi : sp[i]? = some h)
    (hphi : h.phi = true) (hlt : i < landing sp) : Agrees sp i := by
  have ha : Accessible sp i := by
    by_contra hna
    have hf : (stateAt sp i).frozen = true := by simpa [Accessible] using hna
    obtain ⟨hlen, -⟩ := List.getElem?_eq_some_iff.1 hi
    have := height_stateAt_le sp i
    rw [landing, frozen_stateAt_of_le hlen.le hf] at hlt
    omega
  simp [Agrees, hi, hphi, ha]

/-! ### The optional [EPP, φ] on T (§3.1) -/

/-- The account of [carstens-mletshe-2015]: Voice is not a phase and each inflectional head
bears [EPP, φ] optionally, Asp with `a` and T with `t`. -/
def optionalT (a t : Bool) : Spine :=
  [⟨.Voice, false, false, false⟩, ⟨.Asp, a, a, false⟩, ⟨.T, t, t, false⟩]

/-- On that account an embedded T may lack [EPP, φ] below C and a raising verb, the configuration
of raising to object. -/
def optionalTRaising (t : Bool) : Spine :=
  [⟨.Voice, false, false, false⟩, ⟨.T, t, t, false⟩, ⟨.C, true, false, true⟩, raisingV]

/-- The optional-probe account overgenerates: Asp alone may attract and agree with the subject
(30), T alone may (31), and the subject may raise to object across a non-agreeing T (25),
the patterns the phasal account excludes. -/
theorem optional_T_overgenerates :
    (landing (optionalT true false) = 2 ∧ Agrees (optionalT true false) 1 ∧
      ¬ Agrees (optionalT true false) 2) ∧
    (landing (optionalT false true) = 3 ∧ ¬ Agrees (optionalT false true) 1 ∧
      Agrees (optionalT false true) 2) ∧
    (landing (optionalTRaising false) = 4 ∧ ¬ Agrees (optionalTRaising false) 1) := by
  decide

/-! ### The trees the derivation builds -/

/-- The object. -/
def obj : LexicalItem.Token := ⟨.of .D [] "obj", 0⟩

/-- The subject. -/
def subj : LexicalItem.Token := ⟨.of .D [] "subj", 1⟩

/-- The verb. -/
def V : LexicalItem.Token := ⟨.of .V [.D] "V", 2⟩

/-- The head that introduces the subject, below Voice (fn. 3). -/
def v : LexicalItem.Token := ⟨.of .v [.V, .D] "v", 3⟩

/-- The head at index `i` of a spine, selecting the category of the head below it. -/
def tokOf (sp : Spine) (i : ℕ) (hd : Head) : LexicalItem.Token :=
  ⟨.of hd.cat [if i = 0 then .v else ((sp[i - 1]?).map Head.cat).getD .v], 10 + i⟩

/-- The phase heads of a spine. -/
def phaseHeads (sp : Spine) : List LexicalItem.Token :=
  (sp.zipIdx.filter (·.1.phase)).map fun x ↦ tokOf sp x.2 x.1

/-- The copy of the subject at height `j`, when it is pronounced at height `k`. -/
def copyAt (k j : ℕ) : LinearizedSyntacticObject := if j = k then .leaf subj else .traceOf subj

/-- Once the first `n` heads are merged, the tree has the subject pronounced at its height then,
with deleted copies at its base and in every specifier it passed through. -/
def treeAt (sp : Spine) (n : ℕ) : LinearizedSyntacticObject :=
  let k := (stateAt sp n).height
  (sp.take n).zipIdx.foldl (fun t x ↦
    let hp : LinearizedSyntacticObject := .leaf (tokOf sp x.2 x.1) * t
    if x.1.epp ∧ x.2 + 1 ≤ k then copyAt k (x.2 + 1) * hp else hp)
    (copyAt k 0 * (v * (V * obj)))

/-- The subject is accessible under the condition `s` to the head at index `i`, merged on the tree
built so far. -/
def TreeAccessible (s : Impenetrability) (sp : Spine) (i : ℕ) : Prop :=
  ∀ hd ∈ sp[i]?, ((.leaf (tokOf sp i hd) * treeAt sp i : LinearizedSyntacticObject) :
    SyntacticObject).Accessible (phaseHeads sp) s (tokOf sp i hd) subj

instance (s : Impenetrability) (sp : Spine) (i : ℕ) : Decidable (TreeAccessible s sp i) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))

/-- In simple clauses (9)–(14) the subject is accessible to a head exactly when it is under
[chomsky-2000]'s condition on the tree the derivation has built. -/
theorem simple_accessible_iff (e : Bool) :
    ∀ i < 2, Accessible (simple e) i ↔ TreeAccessible .phase (simple e) i := by
  cases e <;> decide

/-- The same in auxiliary constructions (16)–(21). -/
theorem auxV_accessible_iff (e : Bool) :
    ∀ i < 3, Accessible (auxV e) i ↔ TreeAccessible .phase (auxV e) i := by
  cases e <;> decide

/-- The same in reduced clauses (34)–(42). -/
theorem reduced_accessible_iff (e : Bool) :
    ∀ i < 2, Accessible (reduced e) i ↔ TreeAccessible .phase (reduced e) i := by
  cases e <;> decide

/-- Under [chomsky-2001]'s condition T would reach a subject left in the complement of Voice and
agree with it, against the default agreement of (6) and (11). -/
theorem nextPhase_overgenerates :
    ¬ TreeAccessible .phase (simple false) 1 ∧ TreeAccessible .nextPhase (simple false) 1 := by
  decide

end Pietraszko2026
