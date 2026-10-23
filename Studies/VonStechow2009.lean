module

public import Linglib.Semantics.Tense.Quantificational
public import Linglib.Semantics.Aspect.Viewpoint
public import Linglib.Semantics.Mereology
public import Studies.BeaverCondoravdi2003
public import Linglib.Data.Examples.VonStechow2009
public import Mathlib.Order.Cover

/-!
# von Stechow (2009): Tenses in compositional semantics

Von Stechow gives English tense a compositional semantics. The Present denotes the speech time;
the Past is indefinite, an existential quantifier over the times before its local evaluation
time, and so is the auxiliary *have*; *will* is its mirror image and *be* passes its time on.
Against Partee's referential Past, the indefinite Past restricted to the times the speaker has
in mind gives the truth conditions of her stove sentence and, unlike the referential one, lets
negation and quantifiers scope over tense. Relative-clause tenses are bound pronouns, attitude
complements are properties of times, and *before* and *after* take the earliest time of their
clause. Along the way he argues that achievements need moments but not discrete time.

A time is a moment, a point of a linear order, or an interval of moments, mathlib's
`NonemptyInterval`, whose `≤` is the subinterval relation. A tense is possibility `◇` along its
cell read as a relation (`Semantics/Tense/Quantificational.lean`), so `◇[toSetRel ⟦past⟧] P s`
says that `P` held at some time before `s`.

## Main statements

* `not_dowtyAchievement`, `achievement_rat`: Dowty's interval semantics for achievements is
  unsatisfiable in dense time, von Stechow's moment semantics is not.
* `not_perfAdv_yesterday`: the present perfect with *yesterday* is contradictory.
* `every_sunday`: *John worked on every Sunday* is true on the reading restricted to past
  Sundays, and false on both unrestricted scopings, of a calendar where John works on Sundays.
* `restrictedPast_Iic_iff_prfv`: the Past restricted to the subintervals of a past time is the
  perfective at that time.
* `exists_not_prfv_past`: *It didn't rain today* is too weak on the referential analysis.
* `anaphoric_report_iff`: on the anaphoric analysis *At five Mary thought it was six* ascribes
  inconsistent beliefs to Mary.
* `before_earliest_iff_beforeEver`, `after_earliest_iff_after`: *before* and *after* the earliest
  time of the clause are Anscombe's *before ever* and *after*.

## Implementation notes

The tense entries, relative clauses, attitudes and adjunct clauses are stated on moments, the
arguments about the perfective, frame adverbials and the extended now on intervals, where
*before* is `NonemptyInterval.Precedes`; *on* and *in* are `≤`, *at* is equality. The
referential Past (47), which von Stechow takes from Heim, is the presupposition
`Perspective.Presup ⟦past⟧`; the Perfective (50) and the extended-now perfect (28) are
`Aspect.PRFV` and `Aspect.PERF`, and quantization (12) is Krifka's `Mereology.QUA`. The printed
restricted Past (53) compares the quantified time with the speech time where its λ-bound
argument is meant, as (57) shows; the printed EARLIEST (91) requires the earliest time to
precede every time of the clause, itself included, and is read as `IsLeast`. Doxastic
alternatives are relations on worlds indexed by times, or on world–time pairs. Feature
transmission, PRO movement, the deletion of tenses under tenses, the progressive and the
operators THR, ST and EV are not formalized. The examples are the rows of
`Data.Examples.VonStechow2009`.

## References

* [von-stechow-2009]
* [dowty-1979]
* [krifka-1989]
* [partee-1973]
* [heim-1994-comments]
* [lewis-1979-attitudes]
* [beaver-condoravdi-2003]
* [anscombe-1964]
-/

@[expose] public section

namespace VonStechow2009

open Semantics Tense Aspect ModalLogic
open scoped SetRel
open Kaplan (Index)

variable {T : Type*} [LinearOrder T] {s : T} {P : T → Prop}

/-! ### Achievements -/

section Achievements

variable {φ : T → Prop} {t : NonemptyInterval T}

/-- Dowty's semantics for an achievement such as *find* (10) holds of an interval at whose left
bound `φ` fails and at whose right bound it holds, no proper subinterval being such a change. -/
def DowtyAchievement (φ : T → Prop) (t : NonemptyInterval T) : Prop :=
  ¬ φ t.fst ∧ φ t.snd ∧ ¬ ∃ t' < t, ¬ φ t'.fst ∧ φ t'.snd

/-- An interval satisfying Dowty's semantics consists of two adjacent moments (footnote 7). -/
theorem dowtyAchievement_iff : DowtyAchievement φ t ↔ ¬ φ t.fst ∧ φ t.snd ∧ t.fst ⋖ t.snd := by
  constructor
  · rintro ⟨h₁, h₂, h₃⟩
    refine ⟨h₁, h₂, lt_of_le_of_ne t.fst_le_snd fun h ↦ h₁ (h ▸ h₂), fun m hm hm' ↦ h₃ ?_⟩
    by_cases hφ : φ m
    · exact ⟨⟨(t.fst, m), hm.le⟩, lt_of_le_of_ne ⟨le_rfl, hm'.le⟩
        fun h ↦ hm'.ne (congrArg (·.snd) h), h₁, hφ⟩
    · exact ⟨⟨(m, t.snd), hm'.le⟩, lt_of_le_of_ne ⟨hm.le, le_rfl⟩
        fun h ↦ hm.ne' (congrArg (·.fst) h), hφ, h₂⟩
  · rintro ⟨h₁, h₂, hcov⟩
    refine ⟨h₁, h₂, fun ⟨t', hlt, h₁', h₂'⟩ ↦ hlt.ne ?_⟩
    have hle := NonemptyInterval.le_def.1 hlt.le
    have hlt' : t'.fst < t'.snd := lt_of_le_of_ne t'.fst_le_snd fun h ↦ h₁' (h ▸ h₂')
    refine NonemptyInterval.ext (Prod.ext ?_ ?_)
    · exact (hle.1.lt_or_eq.resolve_left fun h ↦ hcov.2 h (hlt'.trans_le hle.2)).symm
    · exact hle.2.lt_or_eq.resolve_left fun h ↦ hcov.2 (hle.1.trans_lt hlt') h

/-- In dense time no interval satisfies Dowty's semantics (footnote 7). -/
theorem not_dowtyAchievement [DenselyOrdered T] (φ : T → Prop) (t : NonemptyInterval T) :
    ¬ DowtyAchievement φ t := fun h ↦
  have hcov := (dowtyAchievement_iff.1 h).2.2
  let ⟨_, h₁, h₂⟩ := exists_between hcov.lt
  hcov.2 h₁ h₂

/-- Von Stechow's semantics for an achievement (11) holds at a moment where `φ` holds, approached
from the left by a stretch where it fails. -/
def Achievement (φ : T → Prop) (m : T) : Prop :=
  (∃ n₁ < m, ¬ φ n₁ ∧ ∀ n₂, n₁ < n₂ → n₂ < m → ¬ φ n₂) ∧ φ m

/-- Von Stechow's semantics is satisfiable in the rationals. -/
theorem achievement_rat : Achievement (fun q : ℚ ↦ 0 ≤ q) 0 :=
  ⟨⟨-1, by norm_num, by norm_num, fun _ _ h ↦ not_le.2 h⟩, le_rfl⟩

/-- A predicate true only of moments is quantized (12). -/
theorem qua_of_isPoint (Q : NonemptyInterval T → Prop) (h : ∀ t, Q t → t.IsPoint) :
    Mereology.QUA Q := by
  intro a ha b hb hab hle
  obtain ⟨h₁, h₂⟩ := NonemptyInterval.le_def.1 hle
  have ha' : a.fst = a.snd := h a ha
  have hb' : b.fst = b.snd := h b hb
  exact hab (NonemptyInterval.ext (Prod.ext
    (le_antisymm (ha'.le.trans (h₂.trans hb'.symm.le)) h₁)
    (le_antisymm h₂ (hb'.symm.le.trans (h₁.trans ha'.le)))))

end Achievements

/-! ### Tenses and auxiliaries -/

/-- The pluperfect *John had called* (27) places the calling before the speech time. -/
theorem pluperfect_before_speech
    (h : ◇[toSetRel ⟦past⟧] (◇[toSetRel ⟦past⟧] P) s) : ∃ t < s, P t := by
  simpa using diamond_diamond_toSetRel h

/-- Without a restriction on *have*, the future perfect *John will have left at six* (55) can
place the leaving before the speech time. -/
theorem exists_future_perfect_before_speech :
    ∃ (s six : ℤ) (leave : ℤ → Prop),
      ◇[toSetRel ⟦future⟧] (fun t ↦ t = six ∧ ◇[toSetRel ⟦past⟧] leave t) s ∧
        ∀ t, leave t → t < s :=
  ⟨0, 6, (· = -1), by simp, fun _ ht ↦ by omega⟩

/-- With the content of *will* added to the restriction of *have* (57), the future perfect places
the leaving after the speech time. -/
theorem future_perfect_after_speech {six : T}
    (h : ◇[toSetRel ⟦future⟧]
      (fun t ↦ t = six ∧ ◇[toSetRel ⟦past⟧] (fun t' ↦ s < t' ∧ P t') t) s) :
    ∃ t', s < t' ∧ P t' :=
  let ⟨_, _, _, t', _, hs, hP⟩ := h; ⟨t', hs, hP⟩

/-! ### Temporal adverbials -/

/-- The extended-now perfect (28) at the speech time is the perfect of `Aspect`. -/
theorem xn_iff_perf {W : Type*} (p : W → Set (NonemptyInterval T)) (w : W) :
    .pure s ∈ perfect p w ↔ (w, s) ∈ PERF p := by
  rw [perf_eq_atPoint_perfect]; rfl

/-- In *John has called yesterday* (42, `Examples.ex_42`) *yesterday* modifies the extended-now
interval, which ends at the speech time, so the sentence is contradictory unless the speech time
is on yesterday. -/
theorem not_perfAdv_yesterday {W : Type*} (call : W → Set (NonemptyInterval T))
    (yesterday : NonemptyInterval T) (w : W) (hs : s ∉ yesterday) :
    (w, s) ∉ PERF (Set.Iic yesterday ∩ call ·) := fun h ↦
  let ⟨t, ⟨hle, _⟩, e⟩ := mem_perf.1 h
  let ⟨h₁, h₂⟩ := NonemptyInterval.le_def.1 hle
  hs (NonemptyInterval.mem_def.2 ⟨h₁.trans (t.fst_le_snd.trans e.le), e ▸ h₂⟩)

/-- The sentence *Mary had left at six* (43) has a reference-time reading that can hold while its
event-time reading fails. -/
theorem reference_time_reading_not_event_time_reading :
    ∃ (s six : ℤ) (leave : ℤ → Prop),
      ◇[toSetRel ⟦past⟧] (fun t ↦ t = six ∧ ◇[toSetRel ⟦past⟧] leave t) s ∧
        ¬ ◇[toSetRel ⟦past⟧]
          (fun t ↦ ◇[toSetRel ⟦past⟧] (fun t' ↦ t' = six ∧ leave t') t) s :=
  ⟨10, 6, (· = 5), by simp, by simp⟩

theorem event_time_reading_not_reference_time_reading :
    ∃ (s six : ℤ) (leave : ℤ → Prop),
      ◇[toSetRel ⟦past⟧]
          (fun t ↦ ◇[toSetRel ⟦past⟧] (fun t' ↦ t' = six ∧ leave t') t) s ∧
        ¬ ◇[toSetRel ⟦past⟧] (fun t ↦ t = six ∧ ◇[toSetRel ⟦past⟧] leave t) s :=
  ⟨10, 6, (· = 6), ⟨7, by simp, 6, by simp, rfl, rfl⟩, by simp⟩

section Quantified

variable (sunday work : NonemptyInterval T → Prop) {σ : NonemptyInterval T}

/-- *John worked on every Sunday* with the quantifier under the Past (44a) entails a past time
on every Sunday. -/
theorem past_time_on_every_sunday
    (h : ◇[Perspective.toSetRel ⟦past⟧] (fun t ↦ ∀ t', sunday t' → t ≤ t' ∧ work t) σ) :
    ∃ t, ∀ t', sunday t' → t ≤ t' :=
  let ⟨t, _, h⟩ := h; ⟨t, fun t' ht' ↦ (h t' ht').1⟩

/-- With the quantifier over the Past (44b) it entails that every Sunday contains a past time. -/
theorem every_sunday_contains_past_time
    (h : ∀ t', sunday t' → ◇[Perspective.toSetRel ⟦past⟧] (fun t ↦ t ≤ t' ∧ work t) σ) :
    ∀ t', sunday t' → ∃ t, t.Precedes σ ∧ t ≤ t' :=
  fun t' ht' ↦ let ⟨t, hts, h⟩ := h t' ht'; ⟨t, Perspective.presup_past.1 hts, h.1⟩

end Quantified

/-- A Sunday is the day starting at a multiple of seven. -/
def sunday (t : NonemptyInterval ℕ) : Prop := t.fst % 7 = 0 ∧ t.snd = t.fst + 1

/-- If John works every Sunday, *John worked on every Sunday* said on day ten is true on reading
(45) and false on (44a) and (44b). -/
theorem every_sunday :
    (∀ t', sunday t' ∧ t'.Precedes (.pure 10) →
      ◇[Perspective.toSetRel ⟦past⟧] (fun t ↦ t ≤ t' ∧ sunday t) (.pure 10)) ∧
    ¬ ◇[Perspective.toSetRel ⟦past⟧]
      (fun t ↦ ∀ t', sunday t' → t ≤ t' ∧ sunday t) (.pure 10) ∧
    ¬ ∀ t', sunday t' →
      ◇[Perspective.toSetRel ⟦past⟧] (fun t ↦ t ≤ t' ∧ sunday t) (.pure 10) := by
  refine ⟨fun t' ⟨h, hs⟩ ↦ ⟨t', Perspective.presup_past.2 hs, le_rfl, h⟩, ?_, fun h ↦ ?_⟩
  · rintro ⟨t, -, h⟩
    have h₀ := NonemptyInterval.le_def.1 (h ⟨(0, 1), by decide⟩ ⟨rfl, rfl⟩).1
    have h₇ := NonemptyInterval.le_def.1 (h ⟨(7, 8), by decide⟩ ⟨rfl, rfl⟩).1
    have := t.fst_le_snd
    simp only at h₀ h₇
    omega
  · obtain ⟨t, hs, hle, -⟩ := h ⟨(14, 15), by decide⟩ ⟨rfl, rfl⟩
    have hp : t.snd < 10 := Perspective.presup_past.1 hs
    have h₁₄ := NonemptyInterval.le_def.1 hle
    have := t.fst_le_snd
    simp only at h₁₄
    omega

/-! ### Partee's stove, the Perfective and the restricted Past -/

section Partee

variable {W : Type*} (turnOff rain : W → NonemptyInterval T → Prop) (w : W)
  {σ t₅ today : NonemptyInterval T}
  {K : Set (NonemptyInterval T)} {Q : NonemptyInterval T → Prop}

/-- The contextually restricted Past (53) holds of a predicate at `σ` when some interval of the
domain `K` before `σ` satisfies it. -/
def RestrictedPast (K : Set (NonemptyInterval T)) (Q : NonemptyInterval T → Prop)
    (σ : NonemptyInterval T) : Prop :=
  ◇[Perspective.toSetRel ⟦past⟧] (fun t ↦ t ∈ K ∧ Q t) σ

/-- Restricted to subintervals of a time the referential Past (47) admits, the indefinite Past is
the Perfective (50), so (52) and (54) agree. -/
theorem restrictedPast_Iic_iff_prfv (h : Perspective.Presup ⟦past⟧ σ t₅) :
    RestrictedPast (Set.Iic t₅) (turnOff w) σ ↔ t₅ ∈ PRFV turnOff w :=
  ⟨fun ⟨t, _, ht, hQ⟩ ↦ ⟨t, ht, hQ⟩, fun ⟨t, ht, hQ⟩ ↦ ⟨t, Perspective.presup_past.2
    (NonemptyInterval.precedes_of_le_of_precedes ht (Perspective.presup_past.1 h)), ht, hQ⟩⟩

/-- The negation of the unrestricted Past (46b) entails that of the restricted Past (54). -/
theorem not_restrictedPast_of_not_past (h : ¬ ◇[Perspective.toSetRel ⟦past⟧] Q σ) :
    ¬ RestrictedPast K Q σ :=
  fun ⟨t, hts, _, hQ⟩ ↦ h ⟨t, hts, hQ⟩

/-- The converse fails, so (46b) is too strong, as when the stove was turned off before the
interval the speaker has in mind. -/
theorem exists_not_restrictedPast_past :
    ∃ (σ : NonemptyInterval ℤ) (K : Set (NonemptyInterval ℤ)) (Q : NonemptyInterval ℤ → Prop),
      ¬ RestrictedPast K Q σ ∧ ◇[Perspective.toSetRel ⟦past⟧] Q σ := by
  refine ⟨.pure 10, Set.Iic ⟨(5, 6), by decide⟩, (· = .pure 1), ?_, .pure 1, by decide, rfl⟩
  rintro ⟨t, -, hK, rfl⟩
  exact absurd (NonemptyInterval.le_def.1 hK).1 (by decide)

/-- The sentence *It didn't rain today* with negation over the indefinite Past (58) entails its
Perfective analysis (59) at any past reference time today. -/
theorem not_prfv_of_not_past (h : ¬ ◇[Perspective.toSetRel ⟦past⟧]
      (fun t ↦ t ≤ today ∧ rain w t) σ)
    (h₅ : Perspective.Presup ⟦past⟧ σ t₅) (h₅' : t₅ ≤ today) : t₅ ∉ PRFV rain w :=
  fun ⟨t, ht, hr⟩ ↦ h ⟨t, Perspective.presup_past.2
    (NonemptyInterval.precedes_of_le_of_precedes ht (Perspective.presup_past.1 h₅)),
    ht.trans h₅', hr⟩

/-- The referential analysis (59) is too weak, since a short reference time leaves room for rain
elsewhere in today. -/
theorem exists_not_prfv_past :
    ∃ (σ t₅ today : NonemptyInterval ℤ) (rain : Unit → NonemptyInterval ℤ → Prop),
      (Perspective.Presup ⟦past⟧ σ t₅ ∧ t₅ ≤ today ∧ t₅ ∉ PRFV rain ()) ∧
        ◇[Perspective.toSetRel ⟦past⟧] (fun t ↦ t ≤ today ∧ rain () t) σ := by
  refine ⟨.pure 20, ⟨(0, 1), by decide⟩, ⟨(0, 10), by decide⟩, fun _ t ↦ t = .pure 5,
    ⟨by decide, by decide, ?_⟩, .pure 5, by decide, by decide, rfl⟩
  rintro ⟨t, ht, rfl⟩
  exact absurd (NonemptyInterval.le_def.1 ht).2 (by decide)

/-- With the reference time as long as possible, containing every past subinterval of today,
the referential analysis (59) is the indefinite one (58). -/
theorem not_prfv_iff_not_past (hmax : ∀ t ≤ today, t.Precedes σ → t ≤ t₅)
    (h₅ : Perspective.Presup ⟦past⟧ σ t₅) (h₅' : t₅ ≤ today) :
    t₅ ∉ PRFV rain w ↔ ¬ ◇[Perspective.toSetRel ⟦past⟧] (fun t ↦ t ≤ today ∧ rain w t) σ :=
  ⟨fun h ⟨t, ht, hle, hr⟩ ↦ h ⟨t, hmax t hle (Perspective.presup_past.1 ht), hr⟩,
    fun h ↦ not_prfv_of_not_past rain w h h₅ h₅'⟩

end Partee

/-! ### Quantifiers and tense -/

section Scope

variable {X : Type*} (boot : X → Prop) (polish : X → T → Prop)

/-- *John polished every boot* with the Past over the quantifier entails the reading with the
quantifier over the Past (61). -/
theorem forall_past_of_past_forall
    (h : ◇[toSetRel ⟦past⟧] (fun t ↦ ∀ x, boot x → polish x t) s) :
    ∀ x, boot x → ◇[toSetRel ⟦past⟧] (polish x) s :=
  fun x hx ↦ let ⟨t, hts, h⟩ := h; ⟨t, hts, h x hx⟩

theorem exists_forall_past_not_past_forall :
    ∃ (s : ℤ) (boot : Bool → Prop) (polish : Bool → ℤ → Prop),
      (∀ x, boot x → ◇[toSetRel ⟦past⟧] (polish x) s) ∧
        ¬ ◇[toSetRel ⟦past⟧] (fun t ↦ ∀ x, boot x → polish x t) s :=
  ⟨5, fun _ ↦ True, fun b t ↦ t = if b then 1 else 2,
    fun b _ ↦ ⟨if b then 1 else 2, by cases b <;> decide, rfl⟩,
    fun ⟨t, _, h⟩ ↦ by have := h true trivial; have := h false trivial; simp_all⟩

omit [LinearOrder T] in
theorem not_forall_referential {t₅ : T} {x y : X} (hx : boot x) (hy : boot y)
    (hsep : ∀ t, polish x t → ¬ polish y t) : ¬ ∀ z, boot z → polish z t₅ :=
  fun h ↦ hsep t₅ (h x hx) (h y hy)

end Scope

/-! ### Tense in relative clauses -/

section Relative

variable {X : Type*} (fish : X → Prop) (alive buy : X → T → Prop)

/-- In the simultaneous reading (66) of *Mary will buy a fish that is alive* the relative-clause
pronoun is bound by *will*, so the fish is alive at the buying. -/
def Simultaneous (s : T) : Prop :=
  ◇[toSetRel ⟦future⟧] (fun t ↦ ∃ x, fish x ∧ alive x t ∧ buy x t) s

/-- In the deictic reading (67) the pronoun is bound by the matrix Present, so the fish is alive
now. -/
def Deictic (s : T) : Prop :=
  ◇[toSetRel ⟦future⟧] (fun t ↦ ∃ x, fish x ∧ alive x s ∧ buy x t) s

theorem exists_simultaneous_not_deictic :
    ∃ (s : ℤ) (fish : Unit → Prop) (alive buy : Unit → ℤ → Prop),
      Simultaneous fish alive buy s ∧ ¬ Deictic fish alive buy s :=
  ⟨0, fun _ ↦ True, fun _ t ↦ t = 1, fun _ t ↦ t = 1, ⟨1, by decide, (), trivial, rfl, rfl⟩,
    fun ⟨_, _, _, _, h, _⟩ ↦ by simp at h⟩

theorem exists_deictic_not_simultaneous :
    ∃ (s : ℤ) (fish : Unit → Prop) (alive buy : Unit → ℤ → Prop),
      Deictic fish alive buy s ∧ ¬ Simultaneous fish alive buy s :=
  ⟨0, fun _ ↦ True, fun _ t ↦ t = 0, fun _ t ↦ t = 1, ⟨1, by decide, (), trivial, rfl, rfl⟩,
    fun ⟨_, _, _, _, h, h'⟩ ↦ by simp_all⟩

end Relative

/-! ### Tense under attitudes -/

section Attitudes

variable {W : Type*}

/-- On the anaphoric analysis (77), *At five o'clock Mary thought it was six o'clock* holds exactly
when Mary's beliefs at five are inconsistent. -/
theorem anaphoric_report_iff (Dox : T → SetRel W W) {five six : T} (hne : five ≠ six) (w : W) :
    ◇[toSetRel ⟦past⟧] (fun t ↦ t = five ∧ □[Dox t] (fun _ ↦ t = six) w) s ↔
      five < s ∧ ∀ w', ¬ w ~[Dox five] w' := by
  simp only [diamond_toSetRel_past]
  constructor
  · rintro ⟨_, hs, rfl, hb⟩
    exact ⟨hs, fun w' hw' ↦ hne (hb w' hw')⟩
  · rintro ⟨hs, he⟩
    exact ⟨five, hs, rfl, fun w' hw' ↦ absurd hw' (he w')⟩

/-- With the complement a property of times (78), (79), Mary at five consistently locates herself
at six. -/
theorem exists_lewis_report :
    ∃ Dox : SetRel (Index Unit ℤ) (Index Unit ℤ), (∃ i, ((), 5) ~[Dox] i) ∧
      ◇[toSetRel ⟦past⟧] (fun t ↦ t = 5 ∧ □[Dox] (fun i ↦ i.time = 6) ((), t)) 7 :=
  ⟨{p | p.2.time = 6}, ⟨((), 6), rfl⟩, 5, by decide, rfl, fun _ h ↦ h⟩

/-- In (82) *would* binds the relative-clause tense, so the fish may be alive only after the speech
time. -/
theorem exists_bound_relative_after_speech :
    ∃ (Dox : SetRel (Index Unit ℤ) (Index Unit ℤ)) (fish : Unit → Prop)
      (alive buy : Unit → ℤ → Prop),
      ◇[toSetRel ⟦past⟧] (fun t₀ ↦ □[Dox] (fun i ↦ ◇[toSetRel ⟦future⟧]
        (fun t₃ ↦ ∃ x, fish x ∧ alive x t₃ ∧ buy x t₃) i.time) ((), t₀)) 0 ∧
        ∀ x t, alive x t → 0 < t := by
  refine ⟨{p | p.2 = ((), -1)}, fun _ ↦ True, fun _ t ↦ t = 5, fun _ t ↦ t = 5,
    ⟨-1, by decide, fun i hi ↦ ?_⟩, fun _ t ht ↦ by omega⟩
  obtain rfl : i = ((), -1) := hi
  exact ⟨5, by decide, (), trivial, rfl, rfl⟩

end Attitudes

/-! ### Before- and after-clauses -/

section Before

variable {W : Type*} (leave arrive : T → Prop)

/-- With trivial historical alternatives, the *before* of [beaver-condoravdi-2003] makes *Mary left
before John arrived* (92) mean that Mary left before John's earliest past arrival. -/
theorem before_iff_earliest (alt : HistoricalAlternatives W T) (w : W)
    (h : ∀ t, alt ⟨w, t⟩ = {w}) :
    BeaverCondoravdi2003.before {i : Index W T | i.time < s ∧ leave i.time}
        {i : Index W T | i.time < s ∧ arrive i.time} alt w ↔
      ∃ t₁, (t₁ < s ∧ leave t₁) ∧ ∃ m, IsLeast {t₂ | t₂ < s ∧ arrive t₂} m ∧ t₁ < m := by
  rw [BeaverCondoravdi2003.before, BeaverCondoravdi2003.connective_iff_uniform_of_eq_singleton h]
  simp only [BeaverCondoravdi2003.uniform, Set.mem_ofPred_eq, Kaplan.Index.time_mk]

/-- With *will* in the adjunct (84e), the relevant times have no earliest member in dense time, so
EARLIEST is undefined. -/
theorem not_exists_earliest_will [DenselyOrdered T] :
    ¬ ∃ m, IsLeast {t | s < t ∧ ∃ t', t < t' ∧ leave t'} m := by
  rintro ⟨m, ⟨hsm, t', hmt, hl⟩, hmin⟩
  obtain ⟨c, hsc, hcm⟩ := exists_between hsm
  exact absurd (hmin ⟨hsc, t', hcm.trans hmt, hl⟩) (not_le.2 hcm)

/-- When the clause has an earliest time, *before* the earliest time is the *before ever* of
[anscombe-1964], the universal *before* that von Stechow attributes to her. -/
theorem before_earliest_iff_beforeEver {A B : Set T} {m : T} (hm : IsLeast B m) :
    (∃ t ∈ A, t < m) ↔ Tense.beforeEver (NonemptyInterval.pure '' A)
      (NonemptyInterval.pure '' B) := by
  rw [Anscombe1964.beforeEver_iff_lt_least (lb := m)]
  · simp [Tense.timeTrace_image]
  · simpa [Tense.timeTrace_image] using hm

/-- And *after* the earliest time is the existential *after* of [anscombe-1964]. -/
theorem after_earliest_iff_after {A B : Set T} {m : T} (hm : IsLeast B m) :
    (∃ t ∈ A, m < t) ↔
      Anscombe1964.Anscombe.after (NonemptyInterval.pure '' A) (NonemptyInterval.pure '' B) := by
  rw [Anscombe1964.after_iff_least_lt (lb := m)]
  · simp [Tense.timeTrace_image]
  · simpa [Tense.timeTrace_image] using hm

end Before

end VonStechow2009
