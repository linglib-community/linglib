module

public import Linglib.Core.Order.Interval.Basic
public import Linglib.Semantics.Reference.Context.Index
public import Linglib.Semantics.Tense.Embedding
public import Linglib.Semantics.Tense.Perspective

/-!
# Heim (1994): Comments on Abusch's Theory of Tense

This file formalizes the implementation that [heim-1994-comments] gives [abusch-1997]'s
sequence-of-tense analysis: tenses are time variables whose distinctive content is a
presupposition, attitude verbs quantify over the world–time pairs compatible with the holder's
beliefs, and the Upper Limit Constraint is the presupposition (16) that no tense denotes a
time after the local evaluation time, the distinguished variable `0` rebound by the abstractor
in Comp. `LF` is the fragment of the paper's logical forms and `Def` its presuppositions under
the tense entries (4) of Sections 1 and 2, so that the calculations of Section 2 are theorems:
the presuppositions of the de dicto past under a past (20), of the simultaneous (29) and free
(30) construals of *John believed that Bill was asleep*, and the four presuppositions of the
double-access (38) through res-movement and time-concepts (33), with the consequence that
the res concept must overlap the utterance time and so cannot be backshifting. Section 3's
zero affixes `<` and `¬<` carry the ordering presuppositions instead, `Def'`, and the Tense
Licensing Condition `TLC` with the definition (67) of "in the domain of" licenses (50), (51),
(56), (63) and (65) and excludes (57), (62) and (66).

## Implementation notes

* Times are nonempty intervals, so that `<` is `NonemptyInterval.Precedes`, `o` is
  `NonemptyInterval.Overlaps` and "does not follow" is `NotAfter`, the library's
  `Tense.upperLimitConstraint` as a perspectival presupposition on intervals.
* Predicates carry their subjects, de dicto descriptions are atomic and always defined, and
  the presuppositions of the nuclear scopes of `woll` and of res-moved `believe` project
  universally, the law the paper invokes for `some` and `believe`. The time-concept is
  supplied by the context, as in footnote 26.
* Relative clauses and the extensional NP argument of (59)–(60) are outside the fragment, so
  (52) is taken without its relative clause and the contrast between the definitions (53) and
  (61) of "in the domain of" is carried by the res-moved (62)–(66).

## References

* [heim-1994-comments]
* [abusch-1997]
-/

@[expose] public section

namespace Heim1994a

open NonemptyInterval

variable {T : Type*} [LinearOrder T]

/-! ### Times -/

/-- `t` does not follow `t₀`, the relation `¬>` of (16). -/
def NotAfter (t t₀ : NonemptyInterval T) : Prop := ¬ t₀.Precedes t

theorem notAfter_iff_presup (t t₀ : NonemptyInterval T) :
    NotAfter t t₀ ↔
      Tense.Perspective.Presup (Allen.ofPosition Tense.upperLimitConstraint) t₀ t := by
  simp [NotAfter, Tense.upperLimitConstraint, Tense.denote_future]

theorem notAfter_self (t : NonemptyInterval T) : NotAfter t t := precedes_irrefl t

theorem notAfter_of_precedes {t t₀ : NonemptyInterval T} (h : t.Precedes t₀) : NotAfter t t₀ :=
  precedes_asymm h

theorem notAfter_of_overlaps {t t₀ : NonemptyInterval T} (h : t.Overlaps t₀) : NotAfter t t₀ :=
  λ h' => precedes_not_overlaps h' (overlaps_symm h)

/-! ### Logical forms -/

/-- Time variables; `0` is the distinguished evaluation-time variable of Section 1. -/
abbrev Var := ℕ

/-- Assignments of times to variables. -/
abbrev Assignment (T : Type*) [LinearOrder T] := Var → NonemptyInterval T

/-- What occupies a tense position: a tense morpheme (1), the infinitival marker bound from
Comp (12), (25), or the trace of a res-moved tense (32). -/
inductive TenseNode
  | PAST (i : Var)
  | PRES (i : Var)
  | INF (i : Var)
  | trace (i : Var)
  deriving DecidableEq

/-- The variable a tense position denotes (1). -/
def TenseNode.var : TenseNode → Var
  | PAST i | PRES i | INF i | trace i => i

/-- The zero affixes of Section 3, `<` (past) and `¬<` (non-past). -/
inductive Affix
  | past
  | nonpast
  deriving DecidableEq

/-- Logical forms: a predicate with its event-time argument and affix; a de dicto description
binding a variable, as *his 40th birthday λ2* in (20); `x believe [λ0 φ]` (10); `x believe
t_res [λj λ0 φ]` with a res-moved tense (32); and `woll [λ0 φ]` (25). -/
inductive LF (V D A : Type*)
  | pred (v : V) (τ : TenseNode) (a : Affix)
  | bind (d : D) (j : Var) (φ : LF V D A)
  | believe (x : A) (τ : TenseNode) (a : Affix) (φ : LF V D A)
  | believeRes (x : A) (τ : TenseNode) (a : Affix) (res : TenseNode) (j : Var) (φ : LF V D A)
  | woll (τ : TenseNode) (a : Affix) (φ : LF V D A)

/-- A model: the extensions of the predicates (3), the values of the de dicto descriptions,
and the world–time pairs compatible with a holder's beliefs at a world and time (9). -/
structure Model (V D A W T : Type*) [LinearOrder T] where
  ext : V → NonemptyInterval T → W → Prop
  desc : D → W → NonemptyInterval T
  dox : A → W → NonemptyInterval T → Set (Kaplan.Index W (NonemptyInterval T))

/-- A context: its world and utterance time and the suitable time-concept it supplies (33), a
function from world–time pairs to times. -/
structure Context (W T : Type*) [LinearOrder T] where
  world : W
  time : NonemptyInterval T
  concept : Kaplan.Index W (NonemptyInterval T) → NonemptyInterval T

variable {V D A W : Type*} (M : Model V D A W T) (c : Context W T)

/-! ### Sections 1 and 2: the tense entries (4) and the Upper Limit Constraint -/

/-- The lexical presuppositions (4) of the tense morphemes, precedence of and overlap with
the utterance time, together with the Upper Limit Constraint (18) on every tense position. -/
def TenseNode.Def (c : Context W T) (g : Assignment T) : TenseNode → Prop
  | PAST i => (g i).Precedes c.time ∧ NotAfter (g i) (g 0)
  | PRES i => (g i).Overlaps c.time ∧ NotAfter (g i) (g 0)
  | INF i => NotAfter (g i) (g 0)
  | trace i => NotAfter (g i) (g 0)

/-- Definedness: the presuppositions of a logical form at an assignment and world. Attitude
verbs project the presuppositions of their complement to every doxastic alternative (21), a
res-moved tense is the context's concept at the holder's world and time (33), and `woll`
projects to every later time. -/
def Def : LF V D A → Assignment T → W → Prop
  | .pred _ τ _, g, _ => τ.Def c g
  | .bind d j φ, g, w => Def φ (Function.update g j (M.desc d w)) w
  | .believe x τ _ φ, g, w =>
    τ.Def c g ∧ ∀ s ∈ M.dox x w (g τ.var), Def φ (Function.update g 0 s.time) s.world
  | .believeRes x τ _ res j φ, g, w =>
    τ.Def c g ∧ res.Def c g ∧ c.concept ⟨w, g τ.var⟩ = g res.var ∧
      ∀ s ∈ M.dox x w (g τ.var),
        Def φ (Function.update (Function.update g 0 s.time) j (c.concept s)) s.world
  | .woll τ _ φ, g, w => τ.Def c g ∧ ∀ t, (g τ.var).Precedes t → Def φ (Function.update g 0 t) w

/-- Truth: (3), (9), (26) and (33). -/
def Sat : LF V D A → Assignment T → W → Prop
  | .pred v τ _, g, w => M.ext v (g τ.var) w
  | .bind d j φ, g, w => Sat φ (Function.update g j (M.desc d w)) w
  | .believe x τ _ φ, g, w => ∀ s ∈ M.dox x w (g τ.var), Sat φ (Function.update g 0 s.time) s.world
  | .believeRes x τ _ _ j φ, g, w =>
    ∀ s ∈ M.dox x w (g τ.var),
      Sat φ (Function.update (Function.update g 0 s.time) j (c.concept s)) s.world
  | .woll τ _ φ, g, w => ∃ t, (g τ.var).Precedes t ∧ Sat φ (Function.update g 0 t) w

variable (x : A) (v : V) (d : D) (g : Assignment T) (w : W)

/-- The de dicto past under a past (20) presupposes that the described time precedes the utterance
time and follows no doxastic alternative's time. -/
theorem def_bind_past :
    Def M c (.believe x (.PAST 1) .past (.bind d 2 (.pred v (.PAST 2) .nonpast))) g w ↔
      (TenseNode.PAST 1).Def c g ∧ ∀ s ∈ M.dox x w (g 1),
        (M.desc d s.world).Precedes c.time ∧ NotAfter (M.desc d s.world) s.time := by
  simp [Def, TenseNode.Def, TenseNode.var, Function.update_of_ne]

/-- (29) presupposes only that every doxastic alternative time precedes the utterance time (footnote
23). -/
theorem def_simultaneous :
    Def M c (.believe x (.PAST 1) .past (.pred v (.PAST 0) .nonpast)) g w ↔
      (TenseNode.PAST 1).Def c g ∧ ∀ s ∈ M.dox x w (g 1), s.time.Precedes c.time := by
  simp [Def, TenseNode.Def, TenseNode.var, NotAfter, precedes_irrefl]

/-- With the lower past coindexed with the matrix tense, (30) presupposes that the holder located
himself at or after the matrix time. -/
theorem def_free_coindexed :
    Def M c (.believe x (.PAST 1) .past (.pred v (.PAST 1) .nonpast)) g w ↔
      (TenseNode.PAST 1).Def c g ∧
        ∀ s ∈ M.dox x w (g 1), (g 1).Precedes c.time ∧ NotAfter (g 1) s.time := by
  simp [Def, TenseNode.Def, TenseNode.var, Function.update_of_ne]

/-- Under res-movement (32), the concept yields the res at the holder's world and time and follows
no alternative's time. -/
theorem def_res :
    Def M c (.believeRes x (.PAST 1) .past (.PAST 2) 3 (.pred v (.trace 3) .nonpast)) g w ↔
      (TenseNode.PAST 1).Def c g ∧ (TenseNode.PAST 2).Def c g ∧ c.concept ⟨w, g 1⟩ = g 2 ∧
        ∀ s ∈ M.dox x w (g 1), NotAfter (c.concept s) s.time := by
  simp [Def, TenseNode.Def, TenseNode.var, Function.update_of_ne]

/-- A concept that locates a later time at some alternative, as "the next time the lights go
out" does, fails the presupposition of (32). -/
theorem not_def_res_of_precedes {s : Kaplan.Index W (NonemptyInterval T)}
    (hs : s ∈ M.dox x w (g 1))
    (h : s.time.Precedes (c.concept s)) :
    ¬ Def M c (.believeRes x (.PAST 1) .past (.PAST 2) 3 (.pred v (.trace 3) .nonpast)) g w :=
  λ hd => ((def_res M c x v g w).1 hd).2.2.2 s hs h

/-- The double-access LF (38): a present under a past through res-movement. -/
def doubleAccess : LF V D A :=
  .believeRes x (.PAST 1) .past (.PRES 2) 3 (.pred v (.trace 3) .nonpast)

/-- (38) presupposes that the believing time precedes the utterance time, the res overlaps it, and
the concept yields the res and follows no alternative's time. -/
theorem def_doubleAccess (h0 : g 0 = c.time) :
    Def M c (doubleAccess x v) g w ↔
      (g 1).Precedes c.time ∧ (g 2).Overlaps c.time ∧
        (∀ s ∈ M.dox x w (g 1), NotAfter (c.concept s) s.time) ∧ c.concept ⟨w, g 1⟩ = g 2 := by
  simp only [doubleAccess, Def, TenseNode.Def, TenseNode.var, h0,
    Function.update_of_ne (show (0 : ℕ) ≠ 3 by decide), Function.update_self]
  exact ⟨λ ⟨⟨h₁, _⟩, ⟨h₂, _⟩, h₄, h₃⟩ => ⟨h₁, h₂, h₃, h₄⟩,
    λ ⟨h₁, h₂, h₃, h₄⟩ => ⟨⟨h₁, notAfter_of_precedes h₁⟩, ⟨h₂, notAfter_of_overlaps h₂⟩, h₄, h₃⟩⟩

/-- Under (38), the concept at the holder's world and time overlaps the utterance time. -/
theorem overlaps_of_def_doubleAccess (h0 : g 0 = c.time) (h : Def M c (doubleAccess x v) g w) :
    (c.concept ⟨w, g 1⟩).Overlaps c.time := by
  obtain ⟨_, h₂, _, h₄⟩ := (def_doubleAccess M c x v g w h0).1 h
  exact h₄ ▸ h₂

theorem snd_lt_of_def_doubleAccess (h0 : g 0 = c.time) (h : Def M c (doubleAccess x v) g w) :
    (g 1).snd < (c.concept ⟨w, g 1⟩).snd :=
  lt_of_lt_of_le ((def_doubleAccess M c x v g w h0).1 h).1
    (overlaps_of_def_doubleAccess M c x v g w h0 h).2

/-- (38) cannot report a belief under a backshifting concept such as *a year ago*. -/
theorem not_def_doubleAccess_of_backshifting (h0 : g 0 = c.time)
    (hf : ∀ s, (c.concept s).Precedes s.time) : ¬ Def M c (doubleAccess x v) g w := λ h =>
  precedes_not_overlaps (precedes_trans (hf ⟨w, g 1⟩) ((def_doubleAccess M c x v g w h0).1 h).1)
    (overlaps_of_def_doubleAccess M c x v g w h0 h)

/-! ### Section 3: the affixes and the Tense Licensing Condition -/

/-- The presuppositions of the affixed predicates (46)–(48): the event time precedes, or does
not precede, the evaluation time. -/
def Affix.Def (g : Assignment T) (t : NonemptyInterval T) : Affix → Prop
  | past => t.Precedes (g 0)
  | nonpast => ¬ t.Precedes (g 0)

/-- The tense entries of Section 3: PAST a bare variable (1a), PRES with the presupposition
(64) of overlapping the evaluation time, and the Upper Limit Constraint on every position. -/
def TenseNode.Def' (g : Assignment T) : TenseNode → Prop
  | PAST i => NotAfter (g i) (g 0)
  | PRES i => (g i).Overlaps (g 0) ∧ NotAfter (g i) (g 0)
  | INF i => NotAfter (g i) (g 0)
  | trace i => NotAfter (g i) (g 0)

/-- Definedness under the entries of Section 3, every predicate affixed. -/
def Def' : LF V D A → Assignment T → W → Prop
  | .pred _ τ a, g, _ => τ.Def' g ∧ a.Def g (g τ.var)
  | .bind d j φ, g, w => Def' φ (Function.update g j (M.desc d w)) w
  | .believe x τ a φ, g, w =>
    τ.Def' g ∧ a.Def g (g τ.var) ∧
      ∀ s ∈ M.dox x w (g τ.var), Def' φ (Function.update g 0 s.time) s.world
  | .believeRes x τ a res j φ, g, w =>
    τ.Def' g ∧ a.Def g (g τ.var) ∧ res.Def' g ∧ c.concept ⟨w, g τ.var⟩ = g res.var ∧
      ∀ s ∈ M.dox x w (g τ.var),
        Def' φ (Function.update (Function.update g 0 s.time) j (c.concept s)) s.world
  | .woll τ a φ, g, w =>
    τ.Def' g ∧ a.Def g (g τ.var) ∧ ∀ t, (g τ.var).Precedes t → Def' φ (Function.update g 0 t) w

/-- Whether a tense is licensed at a position, (49) with (67): a PAST must have its host
predicate `<`-affixed or sit inside an intensional argument of a `<`-affixed predicate
(`above`), a PRES must have neither. -/
def TenseNode.Licensed (host : Affix) (above : Bool) : TenseNode → Prop
  | PAST _ => host = .past ∨ above = true
  | PRES _ => host = .nonpast ∧ above = false
  | INF _ => True
  | trace _ => True

/-- The affix of the predicate whose event-time argument is the trace of variable `j`, the
host of a res-moved tense under (67). -/
def traceHost (j : Var) : LF V D A → Option Affix
  | .pred _ (.trace i) a => if i = j then some a else none
  | .pred _ _ _ => none
  | .bind _ _ φ => traceHost j φ
  | .believe _ (.trace i) a φ => if i = j then some a else traceHost j φ
  | .believe _ _ _ φ => traceHost j φ
  | .believeRes _ (.trace i) a _ _ φ => if i = j then some a else traceHost j φ
  | .believeRes _ _ _ _ _ φ => traceHost j φ
  | .woll (.trace i) a φ => if i = j then some a else traceHost j φ
  | .woll _ _ φ => traceHost j φ

/-- The Tense Licensing Condition (49) under the definition (67) of "in the domain of":
`above` records whether the position is contained in an intensional argument, the complement
of an attitude verb or of `woll`, of a `<`-affixed predicate; a res-moved tense is licensed
through the host of its trace, its own position being an extensional argument. -/
def TLC : Bool → LF V D A → Prop
  | above, .pred _ τ a => τ.Licensed a above
  | above, .bind _ _ φ => TLC above φ
  | above, .believe _ τ a φ => τ.Licensed a above ∧ TLC (above || decide (a = .past)) φ
  | above, .believeRes _ τ a res j φ =>
    τ.Licensed a above ∧ (∃ h, traceHost j φ = some h ∧ res.Licensed h above) ∧
      TLC (above || decide (a = .past)) φ
  | above, .woll τ a φ => τ.Licensed a above ∧ TLC (above || decide (a = .past)) φ

theorem precedes_of_tlc {i : Var} {a : Affix} (h : TLC false (.pred v (.PAST i) a : LF V D A))
    (hd : Def' M c (.pred v (.PAST i) a) g w) : (g i).Precedes (g 0) := by
  rcases h with h | h
  · subst h; exact hd.2
  · exact absurd h Bool.false_ne_true

/-- (50): *John PAST₁ <-cry* is licensed. -/
theorem tlc_cry : TLC false (LF.pred v (.PAST 1) .past : LF V D A) := Or.inl rfl

/-- (51): *he PAST₁ <-decide [λ0 PRO to₀ ¬<-tell [λ0 they PAST₀ ¬<-be having ...]]*, the
lower PAST licensed non-locally by *<-decide*. -/
theorem tlc_decide (y : A) (having : V) :
    TLC false (.believe x (.PAST 1) .past (.believe y (.INF 0) .nonpast
      (.pred having (.PAST 0) .nonpast)) : LF V D A) :=
  ⟨Or.inl rfl, trivial, Or.inr rfl⟩

/-- (52) without its relative clause satisfies the TLC, the PAST of *woll* licensed by *<-say*
across the non-past future. -/
theorem tlc_say (buy : V) :
    TLC false (.believe x (.PAST 1) .past (.woll (.PAST 0) .nonpast
      (.pred buy (.INF 0) .nonpast)) : LF V D A) :=
  ⟨Or.inl rfl, Or.inr rfl, trivial⟩

/-- (56): the simultaneous LF of (28) with its affixes, *John PAST₁ <-believe [λ0 Bill PAST₀
¬<-be asleep]*, is licensed. -/
theorem tlc_simultaneous :
    TLC false (.believe x (.PAST 1) .past (.pred v (.PAST 0) .nonpast) : LF V D A) :=
  ⟨Or.inl rfl, Or.inr rfl⟩

/-- Under the entries of Section 3, (56) presupposes only that the believing time precedes
the utterance time: the presupposition of footnote 23 is gone. -/
theorem def'_simultaneous (h0 : g 0 = c.time) :
    Def' M c (.believe x (.PAST 1) .past (.pred v (.PAST 0) .nonpast)) g w ↔
      (g 1).Precedes c.time := by
  simp only [Def', TenseNode.Def', TenseNode.var, Affix.Def, h0, Function.update_self]
  exact ⟨λ h => h.2.1,
    λ h => ⟨notAfter_of_precedes h, h, λ _ _ => ⟨notAfter_self _, precedes_irrefl _⟩⟩⟩

/-- (57): a present bound from Comp under a `<`-affixed attitude verb violates clause (ii). -/
theorem not_tlc_present_under_past :
    ¬ TLC false (.believe x (.PAST 1) .past (.pred v (.PRES 0) .nonpast) : LF V D A) :=
  λ h => Bool.noConfusion h.2.2

/-- The res-moved LFs of (36) and (28) with their affixes, (62), (63), (65), (66): the res
tense `res` and the affix `a` of the embedded predicate hosting its trace. -/
def resMoved (res : TenseNode) (a : Affix) : LF V D A :=
  .believeRes x (.PAST 1) .past res 3 (.pred v (.trace 3) a)

/-- (63) is licensed: the res-moved PRES is in the domain of *¬<-be pregnant* alone. -/
theorem tlc_63 : TLC false (resMoved x v (.PRES 2) .nonpast : LF V D A) :=
  ⟨Or.inl rfl, ⟨.nonpast, rfl, rfl, rfl⟩, trivial⟩

/-- (62) is excluded: the res-moved PRES is in the domain of *<-be pregnant*. -/
theorem not_tlc_62 : ¬ TLC false (resMoved x v (.PRES 2) .past : LF V D A) := by
  rintro ⟨_, ⟨h, hh, hl⟩, _⟩
  cases Option.some.inj (hh : some Affix.past = some h)
  exact absurd hl.1 (by decide)

/-- (65) is licensed: the back-shifted reading, the res-moved PAST hosted by *<-be asleep*. -/
theorem tlc_65 : TLC false (resMoved x v (.PAST 2) .past : LF V D A) :=
  ⟨Or.inl rfl, ⟨.past, rfl, Or.inl rfl⟩, trivial⟩

/-- (66) is excluded: the res-moved PAST is in the domain of no `<`-affixed predicate. -/
theorem not_tlc_66 : ¬ TLC false (resMoved x v (.PAST 2) .nonpast : LF V D A) := by
  rintro ⟨_, ⟨h, hh, hl⟩, _⟩
  cases Option.some.inj (hh : some Affix.nonpast = some h)
  rcases hl with hl | hl
  · exact absurd hl (by decide)
  · exact Bool.false_ne_true hl

/-- (63) presupposes a past belief, the res overlap (64) and identity (33), and that the concept
neither follows nor precedes each alternative's time. -/
theorem def'_63 (h0 : g 0 = c.time) :
    Def' M c (resMoved x v (.PRES 2) .nonpast) g w ↔
      (g 1).Precedes c.time ∧ (g 2).Overlaps c.time ∧ c.concept ⟨w, g 1⟩ = g 2 ∧
        ∀ s ∈ M.dox x w (g 1),
          NotAfter (c.concept s) s.time ∧ ¬ (c.concept s).Precedes s.time := by
  simp only [resMoved, Def', TenseNode.Def', TenseNode.var, Affix.Def, h0,
    Function.update_of_ne (show (0 : ℕ) ≠ 3 by decide), Function.update_self]
  exact ⟨λ ⟨_, h₁, ⟨h₂, _⟩, h₄, h₆⟩ => ⟨h₁, h₂, h₄, h₆⟩,
    λ ⟨h₁, h₂, h₄, h₆⟩ => ⟨notAfter_of_precedes h₁, h₁, ⟨h₂, notAfter_of_overlaps h₂⟩, h₄, h₆⟩⟩

end Heim1994a
