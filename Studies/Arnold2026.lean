module

public import Studies.KonnellyCowper2020
public import Linglib.Data.Examples.Arnold2026
public import Linglib.Discourse.CommonGround
public import Mathlib.Order.UpperLower.Closure

/-!
# Arnold 2026: two kinds of singular *they*

Arnold distinguishes two uses of singular *they* by what each asks of the common ground, the
propositions the interlocutors accept, which grows as the discourse goes on. Underspecified
*they*, attested since Middle English, asks for a common ground that has not grown past a
threshold varying across speakers and situations, an upper set in the order of filters; personal
*they*, mainstream since about 2018, asks for a common ground that accepts the referent's
pronouns as *they/them*, a principal lower set (`Kind.condition`). The two kinds share their form
and their lack of a gender feature, so Konnelly and Cowper's grammar, which reads only the
antecedent, does not separate them, and where it admits *they* for a specific referent whose
pronouns are not *they/them*, the two accounts part ways.

## Main definitions

* `Arnold2026.Kind`, `Arnold2026.Kind.condition`: the two kinds and the common grounds each
  kind is used in.

## Main results

* `Arnold2026.disjoint_condition_iff`: the kinds share no common ground unless the one accepting
  just the they/them fact counts as underspecified.
* `Arnold2026.antitone_mem_condition_underspecified`: as a discourse asserts more,
  underspecified *they* is lost and not regained, as in the student story
  (`Arnold2026.story_they_lost`).
* `Arnold2026.stage2_they_needs_ungendered_entry`, `Arnold2026.stage3_they_counterexample`: at
  Konnelly and Cowper's second stage personal *they* needs an ad hoc entry, and at their third
  stage the grammar admits a use neither kind licenses.
* `Arnold2026.mem_condition_iff_of_agrees`: an example meets its kind's condition exactly when
  the paper does not flag it as a would-be counterexample.

## Implementation notes

The representation of the referent is the common ground of `Discourse/CommonGround.lean`, a
filter on worlds, so a finer common ground is a more elaborated representation; which accepted
propositions bear on the referent is left to the threshold. The paper describes the context of
an example only as an underspecified or an elaborated representation, and by whether the
referent's pronouns are known to be *they/them*. A common ground agrees with a row when it has
the properties the row states (`Agrees`), and the examples are tested on every agreeing one.

## References

* [arnold-2026]
* [konnelly-cowper-2020]
* [balhorn-2004]
* [stalnaker-1978]
-/

@[expose] public section

namespace Arnold2026

open KonnellyCowper2020 Filter HasCommonGround HasAssertion

/-- The two kinds of singular *they*. -/
inductive Kind
  | underspecified
  | personal
  deriving DecidableEq, Repr

variable {W : Type*} (U : UpperSet (Filter W)) (P : Set W)

/-- The common grounds a kind of *they* is used in, given the threshold `U` of common grounds
that count as underspecified and the proposition `P` that the referent's pronouns are
*they/them*. Underspecified *they* asks for a common ground in `U`, personal *they* for one that
accepts `P`. -/
def Kind.condition : Kind → Set (Filter W)
  | .underspecified => U
  | .personal => Set.Iic (𝓟 P)

variable {U P} {c : Filter W}

@[simp]
theorem mem_condition_underspecified : c ∈ Kind.underspecified.condition U P ↔ c ∈ U :=
  Iff.rfl

@[simp]
theorem mem_condition_personal : c ∈ Kind.personal.condition U P ↔ P ∈ c :=
  le_principal_iff

theorem isUpperSet_condition_underspecified : IsUpperSet (Kind.underspecified.condition U P) :=
  U.upper

theorem isLowerSet_condition_personal : IsLowerSet (Kind.personal.condition U P) :=
  isLowerSet_Iic _

/-- The two kinds share no common ground unless accepting just the they/them fact counts as
underspecified (§3, §4.1). -/
theorem disjoint_condition_iff :
    Disjoint (Kind.underspecified.condition U P) (Kind.personal.condition U P) ↔ 𝓟 P ∉ U := by
  change Disjoint (U : Set (Filter W)) (Set.Iic (𝓟 P)) ↔ _
  rw [← LowerSet.coe_Iic, ← lowerClosure_singleton, U.upper.disjoint_lowerClosure_right,
    Set.disjoint_singleton_right, SetLike.mem_coe]

/-! ### Discourses -/

variable {ι : Type*} [Preorder ι] {d : ι → Filter W}

/-- As a discourse asserts more, underspecified *they* is lost and not regained (§2). -/
theorem antitone_mem_condition_underspecified (hd : Antitone d) :
    Antitone fun i ↦ d i ∈ Kind.underspecified.condition U P :=
  (Set.monotone_mem.2 isUpperSet_condition_underspecified).comp_antitone hd

theorem monotone_mem_condition_personal (hd : Antitone d) :
    Monotone fun i ↦ d i ∈ Kind.personal.condition U P :=
  (Set.antitone_mem.2 isLowerSet_condition_personal).comp hd

/-- A fact the student story of §2 can establish is that the referent is a student, that their
pronouns are *they/them*, or one of the details that emerge about them. -/
inductive StoryFact
  | student
  | theyThem
  | detail (n : ℕ)

/-- The proposition that a fact holds, at the worlds that settle which facts hold. -/
def holds (f : StoryFact) : Set (Set StoryFact) := {w | f ∈ w}

/-- After `n` steps the story has asserted that the referent is a student and the first `n`
details. -/
def story (n : ℕ) : List (Set (Set StoryFact)) :=
  holds .student :: (List.range n).map (holds ∘ .detail)

/-- The common ground after `n` steps of the story, told from scratch. -/
def storyGround (n : ℕ) : Filter (Set StoryFact) :=
  commonGround (play (initial : Filter (Set StoryFact)) (story n))

theorem storyGround_eq (n : ℕ) : storyGround n = 𝓟 (⋂ p ∈ story n, p) :=
  commonGround_play_initial _

theorem antitone_storyGround : Antitone storyGround :=
  antitone_commonGround_play _ fun _ _ h ↦
    List.cons_subset_cons _ (List.map_subset _ (List.range_subset.2 h))

/-- The teller counts a common ground as underspecified while it accepts nothing beyond what
follows from the referent's being a student. -/
def storyThreshold : UpperSet (Filter (Set StoryFact)) := UpperSet.Ici (𝓟 (holds .student))

/-- In the story of §2, underspecified *they* is licensed at the outset, and once a detail is
asserted no kind of *they* is. -/
theorem story_they_lost :
    storyGround 0 ∈ Kind.underspecified.condition storyThreshold (holds .theyThem) ∧
      ∀ n, 0 < n → ∀ k : Kind, storyGround n ∉ k.condition storyThreshold (holds .theyThem) := by
  have h1 : storyGround 1 ∉ Kind.underspecified.condition storyThreshold (holds .theyThem) :=
    fun h ↦ by
      have := principal_mono.1 (UpperSet.mem_Ici_iff.1 h |>.trans_eq (storyGround_eq 1))
      simpa [story, holds] using this (show {StoryFact.student} ∈ holds .student from rfl)
  refine ⟨by simp [storyGround_eq, story, storyThreshold], fun n hn k ↦ ?_⟩
  cases k
  · exact fun h ↦ h1 (antitone_mem_condition_underspecified antitone_storyGround hn h)
  · rw [mem_condition_personal, storyGround_eq, mem_principal]
    intro h
    have hw : {f | f ≠ StoryFact.theyThem} ∈ ⋂ p ∈ story n, p := by simp [story, holds]
    simpa [holds] using h hw

/-! ### The grammatical account

Konnelly and Cowper's grammar reads only the antecedent, so it admits *they* or not whichever
kind the speaker intends (§5). -/

/-- At Konnelly and Cowper's second stage, personal *they* for a gendered singular referential
antecedent needs a homophonous ungendered entry (§5). -/
theorem stage2_they_needs_ungendered_entry {a : Antecedent} {g : KonnellyCowper2020.Gender}
    (hs : a.number = .singular) (hq : a.det = .referential) (hl : a.lexical = some (.gender g)) :
    "they" ∉ forms .two a ∧ "they" ∈ forms .two { a with lexical := none } :=
  have hi : ¬ Antecedent.Inanimate { a with lexical := none } := nofun
  ⟨they_not_mem_forms_of_lexical rfl hs hq hl,
    they_mem_forms (.inl ((none_mem_genders_two_iff hi).2 rfl)) hi⟩

/-- *My mother*, a lexically gendered noun for a referent of known gender outside a quantifier,
as in Konnelly and Cowper's (26). -/
def myMother : Antecedent := ⟨.singular, .referential, some (.gender .fem), some .fem⟩

/-- The third-stage grammar admits *my mother … they* (§6.2), though in some common grounds neither
kind's condition holds, a would-be counterexample. -/
theorem stage3_they_counterexample (hU : c ∉ U) (hP : P ∉ c) :
    "they" ∈ forms .three myMother ∧ ∀ k : Kind, c ∉ k.condition U P :=
  ⟨stage3_they nofun, by rintro (_ | _) <;> simpa⟩

/-! ### The examples -/

/-- The kind of *they* a row records. -/
def Kind.ofRow? (e : Datum) : Option Kind :=
  e.parse? "kind" [("underspecified", .underspecified), ("personal", .personal)]

variable (U P) in
/-- A common ground agrees with a row when, if the row describes the representation, it counts
as underspecified exactly if the row calls the representation underspecified, and when it
accepts the they/them fact if the row records those pronouns. -/
def Agrees (e : Datum) (c : Filter W) : Prop :=
  (∀ v ∈ e.feature? "representation", c ∈ U ↔ v = "underspecified") ∧
    (e.feature? "pronouns" = some "they/them" → P ∈ c)

private theorem rows_underspecified : ∀ e ∈ Examples.all, Kind.ofRow? e = some .underspecified →
    (e.feature? "representation").isSome ∧
      (e.feature? "representation" = some "underspecified" ↔
        e.feature? "counterexample" = none) := by
  decide +kernel

private theorem rows_personal : ∀ e ∈ Examples.all, Kind.ofRow? e = some .personal →
    e.feature? "pronouns" = some "they/them" ∧ e.feature? "counterexample" = none := by
  decide +kernel

/-- An example meets the condition of its kind in every common ground agreeing with it exactly
when the paper does not flag it as a would-be counterexample, the stage-3 *my mother … they*
of §6.2. -/
theorem mem_condition_iff_of_agrees {e : Datum} (he : e ∈ Examples.all) {k : Kind}
    (hk : Kind.ofRow? e = some k) (hc : Agrees U P e c) :
    c ∈ k.condition U P ↔ e.feature? "counterexample" = none := by
  cases k with
  | underspecified =>
    obtain ⟨hs, hiff⟩ := rows_underspecified e he hk
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hs
    rw [mem_condition_underspecified, hc.1 v hv, ← hiff, hv, Option.some_inj]
  | personal =>
    obtain ⟨hp, hn⟩ := rows_personal e he hk
    simpa [hn] using hc.2 hp

end Arnold2026
