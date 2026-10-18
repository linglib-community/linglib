module

public import Studies.KonnellyCowper2020
public import Linglib.Data.Examples.Arnold2026
public import Mathlib.Order.UpperLower.Closure

/-!
# Arnold 2026: two kinds of singular *they*

Arnold distinguishes two uses of singular *they* by what each asks of the discourse
representation of its referent, the set of facts the discourse has established about it, more
elaborated as it grows. Underspecified *they*, attested since Middle English, asks for a
representation below a threshold that varies across speakers and situations, a lower set;
personal *they*, mainstream since about 2018, asks for a representation that establishes the
referent's pronouns as *they/them*, an upper set (`Kind.condition`). The two kinds share their
form and their lack of a gender feature, so Konnelly and Cowper's grammar, which reads only the
antecedent, does not separate them, and where it admits *they* for a specific referent whose
pronouns are not *they/them*, the two accounts part ways.

## Main definitions

* `Arnold2026.Kind`, `Arnold2026.Kind.condition`: the two kinds and the representations each
  kind is used with.

## Main results

* `Arnold2026.disjoint_condition_iff`: the kinds share no context unless the they/them fact
  alone leaves a representation below the threshold.
* `Arnold2026.antitone_mem_condition_underspecified`: as a discourse adds facts, underspecified
  *they* is lost and not regained, as in the student story (`Arnold2026.story_they_lost`).
* `Arnold2026.stage2_they_needs_ungendered_entry`, `Arnold2026.stage3_they_counterexample`: at
  Konnelly and Cowper's second stage personal *they* needs an ad hoc entry, and at their third
  stage the grammar admits a use neither kind licenses.
* `Arnold2026.mem_condition_iff_of_agrees`: an example meets its kind's condition exactly when
  the paper does not flag it as a would-be counterexample.

## Implementation notes

The paper describes the context of an example only as an underspecified or an elaborated
representation, and by whether the referent's pronouns are known to be *they/them*. A
representation agrees with a row when it has the properties the row states (`Agrees`), and the
examples are tested on every agreeing representation.

## References

* [arnold-2026]
* [konnelly-cowper-2020]
* [balhorn-2004]
-/

@[expose] public section

namespace Arnold2026

open KonnellyCowper2020

/-- The two kinds of singular *they*. -/
inductive Kind
  | underspecified
  | personal
  deriving DecidableEq, Repr

variable {F : Type*} (U : LowerSet (Set F)) (p : F)

/-- The representations a kind of *they* is used with, given the threshold `U` below which a
representation, the set of facts established about the referent, counts as underspecified, and
the fact `p` that the referent's pronouns are *they/them*. Underspecified *they* asks for a
representation below the threshold, personal *they* for one that establishes `p`. -/
def Kind.condition : Kind → Set (Set F)
  | .underspecified => U
  | .personal => Set.Ici {p}

variable {U p} {r : Set F}

@[simp]
theorem mem_condition_underspecified : r ∈ Kind.underspecified.condition U p ↔ r ∈ U :=
  Iff.rfl

@[simp]
theorem mem_condition_personal : r ∈ Kind.personal.condition U p ↔ p ∈ r :=
  Set.singleton_subset_iff

theorem isLowerSet_condition_underspecified : IsLowerSet (Kind.underspecified.condition U p) :=
  U.lower

theorem isUpperSet_condition_personal : IsUpperSet (Kind.personal.condition U p) :=
  isUpperSet_Ici _

/-- The two kinds share no context unless the they/them fact alone leaves a representation below
the threshold, since knowing someone's pronouns is itself a detail of their representation
(§3, §4.1). -/
theorem disjoint_condition_iff :
    Disjoint (Kind.underspecified.condition U p) (Kind.personal.condition U p) ↔ {p} ∉ U := by
  change Disjoint (U : Set (Set F)) (Set.Ici {p}) ↔ _
  rw [← UpperSet.coe_Ici, ← upperClosure_singleton, U.lower.disjoint_upperClosure_right,
    Set.disjoint_singleton_right, SetLike.mem_coe]

/-! ### Discourses -/

variable {ι : Type*} [Preorder ι] {d : ι → Set F}

/-- Along a discourse that only adds facts, underspecified *they* is lost and not regained. A
speaker may use *they* for a neighbor who plays a passing role, but not once the story has built
a detailed picture of them (§2). -/
theorem antitone_mem_condition_underspecified (hd : Monotone d) :
    Antitone fun i ↦ d i ∈ Kind.underspecified.condition U p :=
  (Set.antitone_mem.2 isLowerSet_condition_underspecified).comp_monotone hd

/-- Along a discourse that only adds facts, personal *they*, once licensed, stays licensed. -/
theorem monotone_mem_condition_personal (hd : Monotone d) :
    Monotone fun i ↦ d i ∈ Kind.personal.condition U p :=
  (Set.monotone_mem.2 isUpperSet_condition_personal).comp hd

/-- A fact the student story of §2 can establish is that the referent is a student, that their
pronouns are *they/them*, or one of the details that emerge about them. -/
inductive StoryFact
  | student
  | theyThem
  | detail (n : ℕ)

/-- After `n` steps the story has established that the referent is a student and the first `n`
details. -/
def story (n : ℕ) : Set StoryFact := insert .student (.detail '' Set.Iio n)

theorem monotone_story : Monotone story := fun _ _ h ↦
  Set.insert_subset_insert (Set.image_mono (Set.Iio_subset_Iio h))

/-- The teller counts a representation as underspecified while it establishes at most that the
referent is a student. -/
def storyThreshold : LowerSet (Set StoryFact) := LowerSet.Iic {.student}

/-- The teller of §2 began a story with *they* for a student and shifted to *she* as details
emerged. Underspecified *they* is licensed at the outset, and once a detail is established no
kind of *they* is, then or later. -/
theorem story_they_lost :
    story 0 ∈ Kind.underspecified.condition storyThreshold .theyThem ∧
      ∀ n, 0 < n → ∀ k : Kind, story n ∉ k.condition storyThreshold .theyThem := by
  have h1 : story 1 ∉ Kind.underspecified.condition storyThreshold .theyThem := fun h ↦ by
    simpa using h (Set.mem_insert_of_mem _ ⟨0, Nat.zero_lt_one, rfl⟩)
  refine ⟨by simp [story, storyThreshold], fun n hn k ↦ ?_⟩
  cases k
  · exact fun h ↦ h1 (antitone_mem_condition_underspecified monotone_story hn h)
  · simp [story]

/-! ### The grammatical account

Konnelly and Cowper's grammar reads only the antecedent, so it admits *they* or not whichever
kind the speaker intends (§5). -/

/-- At Konnelly and Cowper's second stage a singular antecedent outside a quantifier whose entry
bears a gender does not take *they*, so personal *they* for such a referent needs a homophonous
entry without the gender, their ad hoc ungendered *Mary* (§5). -/
theorem stage2_they_needs_ungendered_entry {a : Antecedent} {g : Gender}
    (hs : a.singular = true) (hq : a.quantified = false) (hl : a.lexical = some (.gender g)) :
    "they" ∉ forms .two a ∧ "they" ∈ forms .two { a with lexical := none } :=
  ⟨they_not_mem_forms_of_lexical rfl hs hq hl,
    they_mem_forms (Or.inl (by simp [Stage.genders, Stage.genderContrastivity,
      Stage.insertionObligatory, Antecedent.inanimate, Antecedent.lexicalGender])) rfl⟩

/-- *My mother*, a lexically gendered noun for a referent of known gender outside a quantifier,
as in Konnelly and Cowper's (26). -/
def myMother : Antecedent := ⟨true, some (.gender .fem), some .fem, false⟩

/-- The third-stage grammar admits *my mother … they* (§6.2), but on a representation above the
threshold that does not establish the they/them fact neither kind's condition holds, so such a
production would be a counterexample to the proposal. -/
theorem stage3_they_counterexample (hU : r ∉ U) (hp : p ∉ r) :
    "they" ∈ forms .three myMother ∧ ∀ k : Kind, r ∉ k.condition U p :=
  ⟨stage3_they rfl, by rintro (_ | _) <;> simpa⟩

/-! ### The examples -/

/-- The kind of *they* a row records. -/
def Kind.ofRow? (e : Datum) : Option Kind :=
  e.parse? "kind" [("underspecified", .underspecified), ("personal", .personal)]

variable (U p) in
/-- A representation agrees with a row when it lies below the threshold if the row calls the
representation underspecified, not below it if the row calls it elaborated, and establishes the
they/them fact if the row records those pronouns. -/
def Agrees (e : Datum) (r : Set F) : Prop :=
  (e.feature? "representation" = some "underspecified" → r ∈ U) ∧
    (e.feature? "representation" = some "elaborated" → r ∉ U) ∧
    (e.feature? "pronouns" = some "they/them" → p ∈ r)

/-- Each underspecified row states an underspecified representation, or an elaborated one where
the paper flags the row, and each personal row records the they/them pronouns and is not
flagged. -/
private theorem rows_described : ∀ e ∈ Examples.all, ∀ k ∈ (Kind.ofRow? e).toList,
    (k = .underspecified → e.feature? "representation" =
      some (if e.feature? "counterexample" = none then "underspecified" else "elaborated")) ∧
    (k = .personal →
      e.feature? "pronouns" = some "they/them" ∧ e.feature? "counterexample" = none) := by
  decide +kernel

/-- An example meets the condition of its kind on every representation agreeing with it exactly
when the paper does not flag it as a would-be counterexample, the stage-3 *my mother … they*
of §6.2. -/
theorem mem_condition_iff_of_agrees {e : Datum} (he : e ∈ Examples.all) {k : Kind}
    (hk : Kind.ofRow? e = some k) (hr : Agrees U p e r) :
    r ∈ k.condition U p ↔ e.feature? "counterexample" = none := by
  obtain ⟨hu, hp⟩ := rows_described e he k (by simp [hk])
  cases k with
  | underspecified =>
    by_cases hc : e.feature? "counterexample" = none
    · simpa [hc] using hr.1 (by simpa [hc] using hu rfl)
    · simpa [hc] using hr.2.1 (by simpa [hc] using hu rfl)
  | personal => simpa [(hp rfl).2] using hr.2.2 (hp rfl).1

end Arnold2026
