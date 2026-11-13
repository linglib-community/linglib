module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Tactic.NormNum
public import Linglib.Semantics.Aspect.Viewpoint
public import Linglib.Semantics.Events.Closure
public import Linglib.Semantics.Events.Lifespan
public import Studies.Kratzer1998
public import Studies.White2014
public import Linglib.Fragments.English.Verbs.Attitude
public import Linglib.Fragments.English.Verbs.Implicative
public import Linglib.Data.Examples.Williams2025
public import Linglib.Data.StructureDataset.Williams2025

/-!
# Williams (2025): the presuppositions of *forget*

Williams accounts for when the complement of *forget* carries a covert modal. *Forget* presupposes,
after Bondarenko, that the event of its complement started before the forgetting. A gerund or a
perfect infinitive places its event before the attitude holder's subjective now, so that this is the
complement's truth; a plain infinitive places it within the subjective now, a contradiction, and a
plan modal heads it as a last resort. So the modal heads [just the plain
infinitives](##forall_needsMod_den_iff), [not every non-finite complement as White's
does](##mca_overgenerates), and the [contradiction tests](##contradiction_rows), the [*began*
tests](##began_rows) and the [five-language survey](##table1_rows) follow.

## Implementation notes

* The paper's complements are Champollion's continuations, from a predicate of events to a
  proposition at a time (28). Each one the paper builds closes a predicate of events against the
  continuation, and the only continuations applied are the trivial one of Krifka's closure (27) and
  equality with the embedded event in (28b), so a complement here is the predicate of events itself
  (`Complement`), and closure binds its event (`Complement.closure`, through `Event.closure`).
* mathlib orders intervals by inclusion: the paper's `τ(e) ⊆ t` is `(τ e) ≤ t`, its `t' < t` in
  (30a) and (30b) is `t'.Precedes t`, the `t ≤ t'` of (37) is `t.snd ≤ t'.fst`, and `LB` is `.fst`.
* A non-finite complement is an AspP under the heads of (29), the past tense of the gerund and the
  perfect, each relating the reference time above it to the one below (`Head.rel`), and (30a) and
  (30b) print the two relations alike (`den`). The perfect is Kratzer's,
  `Kratzer1998.AspectHead.perfect`, strict precedence, not the `ViewpointType.perfect` relation,
  whose intervals may touch, and under any heads a complement closes to it (`closure_den_cons`).
  The paper gives no structure for the perfect gerund of (8) and (10), here the gerund's past over
  the perfect. Plain infinitives are simultaneous with the matrix reference time, after Wurmbrand.
* Pre-existence is `Event.PreExists` of `Semantics/Events/Lifespan.lean`, shared with
  `Studies/Bondarenko2020`, at the subjective now of the derivations (32), (34) and (36), here the
  run time of the forgetting (`PreEx`). The contradiction of (36) holds whatever the predicate, so a
  form needs the modal when no predicate of events meets pre-existence under it (`lf`), and with
  dense time every other form has predicates that do (`forall_needsMod_den_iff`).
* (28a) closes the forgetting inside the verb, and the paper leaves open how a presupposition that
  depends on the forgetting projects through that closure; presuppositions here are those of a
  forgetting (`Presupposes`). The assertion of (28a), that the attitude holder does not believe the
  complement, plays no part in the argument and is not formalized; neither is the necessity and
  sufficiency presupposition (5b), which the paper leaves to future work, nor the implicative
  entailment of *forgot to*, after Karttunen, which it sets aside (fn. 1).
* The continuations *but he did not have to* and *but he didn't* of §3.1 deny that the action was
  planned, in the sense of the modal (37) (`Planned`), and that it occurred (`Event.closure`).
  Over a plain infinitive the modal, which the paper adapts from Copley, is the prospective over
  the worlds of the plan (`mod_aspP_iff`), built as `Aspect.modalOfRel` builds the imperfective.
  The scenarios count days in `ℚ`, Monday `1`, Tuesday `2` and Wednesday `3`, so that a perfect
  gerund has room between the event and the forgetting.
* The English fragment has an implicative *forget* taking an infinitive and a factive one taking a
  finite clause or a gerund, `English.Verbs.forget` and `English.Verbs.forget_rog`; Williams'
  uniformity hypothesis takes them to be one verb.

## TODO

* The finite complements of (4), (11a) and (18), which the paper leaves to future work, and the
  English ban on perfect infinitives with *forget* of fn. 5.

## References

* [williams-2025]
* [white-2014]
* [kiparsky-kiparsky-1970]
* [bondarenko-2020]
* [champollion-2015]
* [krifka-1989]
* [kratzer-1998]
* [wurmbrand-2014]
* [copley-2002]
* [karttunen-1971]
-/

@[expose] public section

namespace Williams2025

open Event (τ)

variable {W T E : Type*} [LinearOrder T] [Event.TemporalTrace E (NonemptyInterval T)]

/-! ### Complements -/

/-- A complement gives the events it describes at a reference time in a world. -/
abbrev Complement (W E T : Type*) [LinearOrder T] := W → NonemptyInterval T → E → Prop

/-- The closure (27) of a complement binds its event. -/
def Complement.closure (C : Complement W E T) : W → Set (NonemptyInterval T) :=
  fun w ↦ {t | Event.closure (fun v ↦ C v t) w}

/-- In AspP, (26), perfective aspect locates the event within the reference time. -/
def aspP (P : W → E → Prop) : Complement W E T :=
  fun w t e ↦ (τ e) ≤ t ∧ P w e

theorem closure_aspP (P : W → E → Prop) : (aspP P).closure = Aspect.PRFV P := rfl

/-- The heads of (29) above the AspP of a non-finite complement. -/
inductive Head where
  /-- The past tense of a gerund. -/
  | past
  /-- The perfect. -/
  | perf
  deriving DecidableEq

/-- The relation a head imposes between the reference time `t` above it and the reference time `t'`
of its complement: the past tense of the gerund, (30a), puts `t'` before `t`, and so does the
perfect, (30b), which the paper takes from Kratzer. -/
def Head.rel : Head → NonemptyInterval T → NonemptyInterval T → Prop
  | .past, t, t' => t'.Precedes t
  | .perf, t, t' => Kratzer1998.AspectHead.perfect.rel t t'

-- (30a), (30b): both heads are anterior
theorem Head.rel_iff (h : Head) {t t' : NonemptyInterval T} : h.rel t t' ↔ t'.Precedes t := by
  cases h <;> exact .rfl

/-- A head over a complement holds at the reference time `t` where the complement holds at a
reference time the head relates to `t`. -/
def Head.denote (h : Head) (C : Complement W E T) : Complement W E T :=
  fun w t e ↦ ∃ t', h.rel t t' ∧ C w t' e

/-- The non-finite complement whose AspP is under the heads `hs`, outermost first, (30): the plain
infinitive `den []`, the gerund `den [.past]`, the perfect infinitive `den [.perf]` and the perfect
gerund `den [.past, .perf]`. -/
def den (hs : List Head) (P : W → E → Prop) : Complement W E T :=
  hs.foldr Head.denote (aspP P)

/-- Under the plan modal, (37), the plan state `s` is the complement's event, and in every world of
its plan the complement holds at a time from `t` on. -/
def mod (plan : E → NonemptyInterval T → W → Set W) (C : Complement W E T) :
    Complement W E T :=
  fun w t s ↦ ∀ w' ∈ plan s t w, ∃ t', t.snd ≤ t'.fst ∧ C.closure w' t'

variable {P : W → E → Prop} {C : Complement W E T}
  {plan : E → NonemptyInterval T → W → Set W} {h : Head} {hs : List Head} {w : W}
  {t : NonemptyInterval T} {e : E}

@[simp] theorem den_nil (P : W → E → Prop) : den [] P = (aspP P : Complement W E T) := rfl

@[simp] theorem den_cons : den (h :: hs) P = h.denote (den hs P : Complement W E T) := rfl

theorem pred_of_den (hd : den hs P w t e) : P w e := by
  induction hs generalizing t with
  | nil => exact hd.2
  | cons _ _ ih =>
    obtain ⟨_, -, hd⟩ := hd
    exact ih hd

theorem snd_le_of_den (hd : den hs P w t e) : (τ e).snd ≤ t.snd := by
  induction hs generalizing t with
  | nil => exact hd.1.2
  | cons h _ ih =>
    obtain ⟨_, ht, hd⟩ := hd
    exact (ih hd).trans ((h.rel_iff.1 ht).le.trans t.fst_le_snd)

-- (32), (34)
theorem precedes_of_den_cons (hd : den (h :: hs) P w t e) : (τ e).Precedes t :=
  let ⟨_, ht, hd⟩ := hd
  (snd_le_of_den hd).trans_lt (h.rel_iff.1 ht)

-- (32), (34): with dense time, a complement under any heads closes to Kratzer's perfect, its event
-- over by the reference time
theorem closure_den_cons [DenselyOrdered T] (h : Head) (hs : List Head) (P : W → E → Prop) :
    (den (h :: hs) P).closure = Kratzer1998.AspectHead.perfect.denote P := by
  ext w t
  refine ⟨fun ⟨e, hd⟩ ↦ ⟨e, precedes_of_den_cons hd, pred_of_den hd⟩, ?_⟩
  rintro ⟨e, he, hP⟩
  refine ⟨e, ?_⟩
  replace he : (τ e).Precedes t := he
  induction hs generalizing h t with
  | nil => exact ⟨τ e, h.rel_iff.2 he, le_rfl, hP⟩
  | cons h' _ ih =>
    obtain ⟨m, hm, hmt⟩ := exists_between he
    exact ⟨.pure m, h.rel_iff.2 hmt, ih h' (.pure m) hm⟩

/-! ### Pre-existence -/

/-- Pre-existence, (28b), holds at the forgetting `e` when the complement describes an event at the
subjective now, the run time of `e`, that starts before `e` does. -/
def PreEx (C : Complement W E T) (e : E) (w : W) : Prop :=
  Event.PreExists τ (C w (τ e)) (τ e)

theorem PreEx.closure (h : PreEx C e w) : C.closure w (τ e) :=
  Event.PreExists.exists h

-- (32), (34): the presupposition of an anterior complement is its truth at the subjective now
theorem preEx_den_cons_iff :
    PreEx (den (h :: hs) P) e w ↔ (den (h :: hs) P).closure w (τ e) :=
  Event.preExists_iff_exists_of_precedes fun _ ↦ precedes_of_den_cons

-- (36)
theorem not_preEx_aspP : ¬ PreEx (aspP P) e w :=
  Event.not_preExists_of_le fun _ h ↦ h.1

-- (39), (40)
theorem preEx_mod_iff :
    PreEx (mod plan C) e w ↔ ∃ s, mod plan C w (τ e) s ∧ (τ s).fst < (τ e).fst :=
  Event.preExists_iff

-- (37): over a plain infinitive the plan modal is the prospective over the plan state's modal
-- domain, as the imperfective is inclusion over its own
theorem mod_aspP_iff {s : E} : mod plan (aspP P) w t s ↔ t ∈ Aspect.modalOfRel
    (fun w t ↦ plan s t w) Aspect.ViewpointType.prospective.ttTSitRelation P w :=
  ⟨fun h w' hw ↦ let ⟨_, ht, e, he, hP⟩ := h w' hw; ⟨e, ht.trans he.1, hP⟩,
    fun h w' hw ↦ let ⟨e, he, hP⟩ := h w' hw; ⟨τ e, he, e, le_rfl, hP⟩⟩

/-! ### The modal as a last resort, (15) -/

/-- A complement needs the modal when it contradicts pre-existence at every forgetting, so that
without the modal the sentence is a presupposition failure (§5). -/
def NeedsMod (C : Complement W E T) : Prop :=
  ∀ e w, ¬ PreEx C e w

theorem needsMod_aspP (P : W → E → Prop) : NeedsMod (aspP P) :=
  fun _ _ ↦ not_preEx_aspP

/-- The selectivity of modal insertion, (15): whatever its predicate, a non-finite complement needs
the modal exactly when it is a plain infinitive. -/
theorem forall_needsMod_den_iff [DenselyOrdered T] [Nonempty W]
    (hE : ∃ e f : E, (τ e).Precedes (τ f)) :
    (∀ P : W → E → Prop, NeedsMod (den hs P)) ↔ hs = [] := by
  refine ⟨fun H ↦ ?_, fun h P ↦ by subst h; exact needsMod_aspP P⟩
  obtain _ | ⟨_, _⟩ := hs
  · rfl
  obtain ⟨e, f, hef⟩ := hE
  refine (H (fun _ x ↦ x = e) f (Classical.arbitrary W) (preEx_den_cons_iff.2 ?_)).elim
  rw [closure_den_cons]
  exact ⟨e, hef, rfl⟩

open Classical in
/-- At LF the modal heads the complement of *forget* as a last resort, where its form contradicts
pre-existence whatever its predicate (§5). -/
noncomputable def lf (plan : E → NonemptyInterval T → W → Set W) (hs : List Head)
    (P : W → E → Prop) : Complement W E T :=
  if ∀ P' : W → E → Prop, NeedsMod (den hs P') then mod plan (den hs P) else den hs P

@[simp] theorem lf_nil : lf plan [] P = mod plan (aspP P) := by
  simp [lf, needsMod_aspP]

theorem lf_cons [DenselyOrdered T] [Nonempty W] (hE : ∃ e f : E, (τ e).Precedes (τ f)) :
    lf plan (h :: hs) P = den (h :: hs) P := by
  have : ¬ ∀ P' : W → E → Prop, NeedsMod (den (h :: hs) P') :=
    (forall_needsMod_den_iff hE).not.2 (List.cons_ne_nil h hs)
  simp only [lf, this, ↓reduceIte]

/-! ### Against the Modalized Complement Analysis, §3.1 -/

/-- The frame of a non-finite complement: a gerund under the gerund's past tense, an infinitive
otherwise. -/
def frame : List Head → ArgumentFrame
  | .past :: _ => .gerund
  | _ => .infinitival

/-- [white-2014] modalizes every non-finite complement of *forget*, the infinitive of its
implicative entry and the gerund of its factive one alike, but only the plain infinitive needs the
modal. -/
theorem mca_overgenerates [DenselyOrdered T] [Nonempty W]
    (hE : ∃ e f : E, (τ e).Precedes (τ f)) :
    (∃ fr ∈ English.Verbs.forget.valency.frames, frame [] ≤ fr) ∧
      (∃ fr ∈ English.Verbs.forget_rog.valency.frames, frame [.past] ≤ fr) ∧
      (∀ hs, White2014.Modalized (frame hs)) ∧
      ∀ hs, (∀ P : W → E → Prop, NeedsMod (den hs P)) ↔ hs = [] :=
  ⟨by decide, by decide, fun _ ↦ by unfold frame; split <;> decide,
    fun _ ↦ forall_needsMod_den_iff hE⟩

/-! ### What a forgetting presupposes -/

variable (W E) in
/-- *Forget* with a complement of the form `hs` presupposes `q` when every forgetting meeting
pre-existence makes `q` true, whatever the predicate and the plans. -/
def Presupposes (hs : List Head)
    (q : (W → E → Prop) → (E → NonemptyInterval T → W → Set W) → W → Prop) : Prop :=
  ∀ P plan e w, PreEx (lf plan hs P) e w → q P plan w

/-- Some state plans the predicate, which *…but he did not have to stop by the flower shop*
denies. -/
def Planned (P : W → E → Prop) (plan : E → NonemptyInterval T → W → Set W) (w : W) : Prop :=
  ∃ t, (mod plan (aspP P)).closure w t

-- (5a), (12a)
theorem presupposes_nil_planned : Presupposes W E [] Planned :=
  fun _ _ e _ h ↦ by rw [lf_nil] at h; exact ⟨τ e, h.closure⟩

-- (9a), (10a), (14a): an anterior complement presupposes that an event of its predicate occurs,
-- which *…but he didn't stop by the flower shop* denies
theorem presupposes_cons_closure [DenselyOrdered T] [Nonempty W]
    (hE : ∃ e f : E, (τ e).Precedes (τ f)) :
    Presupposes W E (h :: hs) fun P _ ↦ Event.closure P := by
  intro P plan e w hp
  rw [lf_cons hE, preEx_den_cons_iff, closure_den_cons] at hp
  obtain ⟨e', -, he'⟩ := hp
  exact ⟨e', he'⟩

private theorem exists_precedes_rat :
    ∃ e f : NonemptyInterval ℚ, (τ e).Precedes (τ f) :=
  ⟨.pure 0, .pure 1, show (0 : ℚ) < 1 by norm_num⟩

-- (7a), (8a), (13a): John stopped by on day `0` and forgot on day `1`, in the world `true`, whose
-- states all plan the world `false`, where nobody stops by
theorem not_presupposes_cons_planned :
    ¬ Presupposes Bool (NonemptyInterval ℚ) (h :: hs) Planned := by
  intro H
  obtain ⟨_, _, hs'⟩ := H (fun w e ↦ w = true ∧ e = .pure 0) (fun _ _ _ ↦ {false}) (.pure 1) true
    (by
      rw [lf_cons exists_precedes_rat, preEx_den_cons_iff, closure_den_cons]
      exact ⟨.pure 0, show (0 : ℚ) < 1 by norm_num, rfl, rfl⟩)
  obtain ⟨_, -, hf, -⟩ := mod_aspP_iff.1 hs' false rfl
  exact Bool.false_ne_true hf

-- (2): John was told on day `0` to stop by, forgot on day `1` in the world `false` and stops by on
-- day `2` in the plan world `true`
theorem not_presupposes_nil_closure :
    ¬ Presupposes Bool (NonemptyInterval ℚ) [] fun P _ ↦ Event.closure P := by
  intro H
  obtain ⟨_, hf, -⟩ := H (fun w e ↦ w = true ∧ e = .pure 2) (fun _ _ _ ↦ {true}) (.pure 1) false
    (by
      rw [lf_nil, preEx_mod_iff]
      exact ⟨.pure 0, mod_aspP_iff.2 fun _ hw ↦ ⟨.pure 2, show (1 : ℚ) ≤ 2 by norm_num, hw, rfl⟩,
        show (0 : ℚ) < 1 by norm_num⟩)
  exact Bool.false_ne_true hf

local notation "Presupposes'" => Presupposes Bool (NonemptyInterval ℚ)

/-- The contradiction tests of §3.1: continuing with a denial that John had to stop by, or that he
stopped by, is a contradiction exactly when the sentence presupposes it, as the gerunds and the
perfect infinitive presuppose the stopping and the plain infinitive the plan. -/
theorem contradiction_rows :
    (Presupposes' [.past] Planned ↔ Examples.ex_7a.judgment = .unacceptable) ∧
      (Presupposes' [.past, .perf] Planned ↔ Examples.ex_8a.judgment = .unacceptable) ∧
      (Presupposes' [.past] (fun P _ ↦ Event.closure P) ↔ Examples.ex_9a.judgment = .unacceptable) ∧
      (Presupposes' [.past, .perf] (fun P _ ↦ Event.closure P) ↔
        Examples.ex_10a.judgment = .unacceptable) ∧
      (Presupposes' [] Planned ↔ Examples.ex_12a.judgment = .unacceptable) ∧
      (Presupposes' [.perf] Planned ↔ Examples.ex_13a.judgment = .unacceptable) ∧
      (Presupposes' [.perf] (fun P _ ↦ Event.closure P) ↔
        Examples.ex_14a.judgment = .unacceptable) :=
  ⟨iff_of_false not_presupposes_cons_planned (by decide),
    iff_of_false not_presupposes_cons_planned (by decide),
    iff_of_true (presupposes_cons_closure exists_precedes_rat) (by decide),
    iff_of_true (presupposes_cons_closure exists_precedes_rat) (by decide),
    iff_of_true presupposes_nil_planned (by decide),
    iff_of_false not_presupposes_cons_planned (by decide),
    iff_of_true (presupposes_cons_closure exists_precedes_rat) (by decide)⟩

/-! ### The *began* tests, (19) to (21) -/

-- (19), (20)
theorem preEx_lf_cons_eq_iff [DenselyOrdered T] [Nonempty W]
    (hE : ∃ e f : E, (τ e).Precedes (τ f)) {e₀ f : E} :
    PreEx (lf plan (h :: hs) fun (_ : W) e ↦ e = e₀) f w ↔ (τ e₀).Precedes (τ f) := by
  rw [lf_cons hE, preEx_den_cons_iff, closure_den_cons]
  exact ⟨fun ⟨_, he, h⟩ ↦ h ▸ he, fun he ↦ ⟨e₀, he, rfl⟩⟩

/-- In (21) Mary's twin tells her on day `d` to call her back, starting the plan state `.pure d`,
whose plan is the world `true`, where Mary calls on day `4`; every other state plans the world
`false`, where she does not call. -/
def twinPlan (d : ℚ) : NonemptyInterval ℚ → NonemptyInterval ℚ → Bool → Set Bool :=
  fun s _ _ ↦ {w | w = true ↔ s = .pure d}

-- (21)
theorem preEx_twin_iff {d : ℚ} :
    PreEx (lf (twinPlan d) [] fun w e ↦ w = true ∧ e = .pure 4) (.pure 2) false ↔ d < 2 := by
  rw [lf_nil, preEx_mod_iff]
  refine ⟨fun ⟨s, hs, hlt⟩ ↦ ?_, fun hd ↦ ⟨.pure d, mod_aspP_iff.2 fun _ hw ↦
    ⟨.pure 4, show (2 : ℚ) ≤ 4 by norm_num, hw.2 rfl, rfl⟩, hd⟩⟩
  obtain rfl : s = .pure d := by
    by_contra hne
    obtain ⟨_, -, hf, -⟩ := mod_aspP_iff.1 hs false (by simp [twinPlan, hne])
    exact Bool.false_ne_true hf
  exact hlt

/-- The *began* tests: Mary's forgetting on Tuesday presupposes that the call, under the gerund (19)
and the perfect infinitive (20), or the plan her twin started, under the plain infinitive (21),
began before it, on Monday and not on Wednesday. -/
theorem began_rows {plan : NonemptyInterval ℚ → NonemptyInterval ℚ → Bool → Set Bool} {w : Bool} :
    (PreEx (lf plan [.past] fun _ e ↦ e = .pure 1) (.pure 2) w ↔
        Examples.ex_19a.judgment = .acceptable) ∧
      (PreEx (lf plan [.past] fun _ e ↦ e = .pure 3) (.pure 2) w ↔
        Examples.ex_19b.judgment = .acceptable) ∧
      (PreEx (lf plan [.perf] fun _ e ↦ e = .pure 1) (.pure 2) w ↔
        Examples.ex_20a.judgment = .acceptable) ∧
      (PreEx (lf plan [.perf] fun _ e ↦ e = .pure 3) (.pure 2) w ↔
        Examples.ex_20b.judgment = .acceptable) ∧
      (PreEx (lf (twinPlan 1) [] fun w e ↦ w = true ∧ e = .pure 4) (.pure 2) false ↔
        Examples.ex_21a.judgment = .acceptable) ∧
      (PreEx (lf (twinPlan 3) [] fun w e ↦ w = true ∧ e = .pure 4) (.pure 2) false ↔
        Examples.ex_21b.judgment = .acceptable) := by
  simp only [preEx_lf_cons_eq_iff exists_precedes_rat, preEx_twin_iff]
  refine ⟨iff_of_true ?_ (by decide), iff_of_false ?_ (by decide), iff_of_true ?_ (by decide),
    iff_of_false ?_ (by decide), iff_of_true ?_ (by decide), iff_of_false ?_ (by decide)⟩ <;>
    first
    | exact show (1 : ℚ) < 2 by norm_num
    | exact show ¬ (3 : ℚ) < 2 by norm_num

/-! ### The survey, Table 1 -/

open CLDF.StructureDataset (Coded) in
/-- The columns of Table 1, each with the complement form it names, (29). -/
def table1Columns :
    List (List Head × (StructureDataset.Row → List (Coded StructureDataset.Modalization))) :=
  [([], (·.plainInfinitive)), ([.perf], (·.perfectInfinitive)), ([.past], (·.clausalGerund))]

/-- Table 1: in each of the five languages the presupposition of *forget* with a non-finite
complement is modalized exactly when the complement needs the modal. -/
theorem table1_rows [DenselyOrdered T] [Nonempty W] (hE : ∃ e f : E, (τ e).Precedes (τ f)) :
    ∀ r ∈ StructureDataset.table1, ∀ x ∈ table1Columns, ∀ c ∈ x.2 r,
      (c.code = .modalized ↔ ∀ P : W → E → Prop, NeedsMod (den x.1 P)) := by
  simp only [forall_needsMod_den_iff hE]
  decide

/-! ### Variants of pre-existence -/

/-- Pre-existence as (28b) prints it, with the time of the complement bound existentially. -/
def PreExPrinted (C : Complement W E T) (e : E) (w : W) : Prop :=
  ∃ t, Event.PreExists τ (C w t) (τ e)

-- (28b): as printed, a plain infinitive presupposes that an event of its predicate started first
theorem preExPrinted_aspP_iff : PreExPrinted (aspP P) e w ↔ Event.PreExists τ (P w) (τ e) := by
  simp only [PreExPrinted, Event.preExists_iff, aspP]
  exact ⟨fun ⟨_, e', ⟨_, hP⟩, hlt⟩ ↦ ⟨e', hP, hlt⟩,
    fun ⟨e', hP, hlt⟩ ↦ ⟨τ e', e', ⟨le_rfl, hP⟩, hlt⟩⟩

-- (37): a state with an empty plan meets pre-existence under the modal
theorem preEx_mod_of_plan_eq_empty {s : E} (hs : plan s (τ e) w = ∅)
    (hlt : (τ s).fst < (τ e).fst) : PreEx (mod plan C) e w :=
  preEx_mod_iff.2 ⟨s, fun _ hw ↦ by simp [hs] at hw, hlt⟩

end Williams2025
