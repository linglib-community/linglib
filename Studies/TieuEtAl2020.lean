module

public import Linglib.Semantics.Exhaustification.InnocentExclusion
public import Linglib.Semantics.Homogeneity.Usable
public import Linglib.Semantics.Plurality.Multiplicity
public import Linglib.Fragments.English.Nouns
public import Linglib.Logic.Trivalent.Supervaluation
public import Linglib.Data.Examples.TieuEtAl2020
public import Linglib.Data.Examples.Readers

/-!
# Tieu, Bill, Romoli and Crain (2020): Testing theories of plural meanings

A bare plural in a positive sentence conveys *more than one*, the multiplicity inference, and
under negation, in the antecedent of a conditional and in a question it conveys no more than the
singular does. With the number of giraffes Emily fed as the world, *Emily fed giraffes* has a weak
reading `weak`, the inclusive reading `Number.inclusive`, and a strong reading `strong`, the
exclusive reading `Number.exclusive` of the English plural. Three accounts say which is heard.

The ambiguity account of Farkas and de Swart gives the sentence both readings and selects, among
those consistent with the context, the one that entails the other. The implicature account of
Spector and of Zweig gives it the weak reading and exhaustifies it against the alternative
`singular`, the exclusive reading of the English singular. The homogeneity account of Križ gives it
the trivalent value `homogeneous`, true where both readings are true, false where both are false
and undefined elsewhere.

The readings are ordered `strong ⊆ weak` and `singular ⊆ weak`, and the accounts agree wherever
the environment respects or reverses that order: unembedded, all three yield `strong`
(`multiplicity_positive`), and under an antitone environment the weak reading is the least reading
(`isLeast_of_antitone`) and entails its alternative, which is then not excluded
(`exhIE_of_antitone`). They differ where exactly one giraffe was fed (`singular_context`): on the
implicature account the positive sentence is true unexhaustified and false exhaustified and the
negative one is false, on the ambiguity account both are false, and on the homogeneity account
both are undefined. Only the implicature account relates the inference to the *not all* inference
of *some*, both being `weak` exhaustified against a singleton alternative
(`exhIE_weak_singleton`).

## Implementation notes

The worlds are the number of giraffes fed, so a reading is a set of natural numbers, negation is
complementation and a downward-entailing environment is an antitone map on readings. The
implicature account is innocent exclusion with one alternative; the versions of the account differ
in how they derive the alternative and agree on the result. *Emily fed some of the `k` giraffes*
has the literal meaning `weak` and the alternative `{k}`. The Strongest Meaning Hypothesis is
`IsLeast` over the readings consistent with the context. The homogeneity value is the
supervaluation of the two readings, and the pragmatic use of an undefined sentence is
`Homogeneity.usable` relative to the issue of whether Emily fed more than one.

Of the experiments, only the modal responses of the ternary judgment task enter: adults gave the
positive plural in a singular context the intermediate reward and the negative plural the minimal
one, `reward_of_singular_context`. The acceptance rates of the truth-value judgment tasks, the
comparison of children with adults and the correlation within children of the multiplicity
inference with the *not all* inference are not formalized.

## References

* [tieu-etal-2020]
* [farkas-de-swart-2010]
* [spector-2007b]
* [zweig-2009]
* [kriz-2017]
* [kriz-2015]
* [fox-2007]
-/

@[expose] public section

namespace TieuEtAl2020

open Exhaustification Trivalent Homogeneity

/-! ### Readings of the plural -/

/-- The weak reading is the inclusive one: one or more. -/
def weak : Set ℕ := Number.inclusive

/-- The strong reading is the exclusive reading of the English plural, the multiplicity
inference. -/
def strong : Set ℕ := Number.exclusive English.Nouns.numberSystem .plural

/-- The singular alternative is the exclusive reading of the English singular. -/
def singular : Set ℕ := Number.exclusive English.Nouns.numberSystem .singular

variable {n : ℕ}

@[simp] theorem exclusive_plural : Number.exclusive English.Nouns.numberSystem .plural = strong :=
  rfl

@[simp] theorem exclusive_singular :
    Number.exclusive English.Nouns.numberSystem .singular = singular :=
  rfl

theorem exclusive_subset_weak (v : Number) :
    Number.exclusive English.Nouns.numberSystem v ⊆ weak :=
  Number.exclusive_subset_inclusive _ v

@[simp] theorem mem_weak : n ∈ weak ↔ 1 ≤ n := Number.mem_inclusive

@[simp] theorem singular_eq : singular = {1} := by
  ext k
  simp [singular, Number.exclusive, Number.ofCard_eq_iff (v := .singular) (by decide),
    Number.exactCard, English.Nouns.numberSystem, eq_comm]

@[simp] theorem mem_strong : n ∈ strong ↔ 2 ≤ n := by
  simp only [strong, Number.exclusive, Set.mem_image, Set.mem_preimage, Set.mem_singleton_iff,
    Number.ofCard_eq_plural_iff_forall, English.Nouns.numberSystem]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq,
    Number.exactCard, ne_eq, Option.some.injEq, reduceCtorEq, not_false_eq_true, and_true]
  refine ⟨fun ⟨p, hp, hk⟩ ↦ hk ▸ ?_, fun hk ↦ ⟨⟨n, by omega⟩, fun h ↦ ?_, rfl⟩⟩
  · exact lt_of_le_of_ne p.pos fun h ↦ hp (PNat.coe_eq_one_iff.1 h.symm).symm
  · have := congrArg PNat.val h
    simp only [PNat.val_ofNat, PNat.mk_coe] at this
    omega

theorem strong_eq : strong = {n | 2 ≤ n} := Set.ext fun _ ↦ mem_strong

theorem strong_subset_weak : strong ⊆ weak := exclusive_subset_weak _

theorem singular_subset_weak : singular ⊆ weak := exclusive_subset_weak _

theorem weak_sdiff_singular : weak \ singular = strong := by
  ext n
  simp only [Set.mem_sdiff, mem_weak, singular_eq, Set.mem_singleton_iff, mem_strong]
  omega

/-! ### The implicature approach -/

/-- Exhaustifying *one or more* against *exactly `m`* excludes `m`: the multiplicity inference
when `m` is one, and the *not all* inference of *some of the `m` giraffes*. -/
theorem exhIE_weak_singleton (m : ℕ) : exhIE {weak, {m}} weak = weak \ {m} :=
  exhIE_pair_sdiff (φ := weak) ⟨m + 1, mem_weak.2 (Nat.le_add_left 1 m), m.succ_ne_self⟩

theorem exhIE_weak_singleton_one : exhIE {weak, {1}} weak = strong :=
  (exhIE_weak_singleton 1).trans (singular_eq ▸ weak_sdiff_singular)

-- (13)–(15)
theorem exhIE_weak : exhIE {weak, singular} weak = strong := by
  have h := Number.exhIE_inclusive English.Nouns.numberSystem
  have hs : {v | v ∈ English.Nouns.numberSystem ∧ v.IsDeterminate} = {Number.singular} := by
    ext v
    cases v <;> simp [English.Nouns.numberSystem, Number.IsDeterminate, Number.exactCard]
  rwa [hs, Set.image_singleton] at h

/-- In a downward-entailing environment an alternative stronger than the weak reading is entailed
by it, so exhaustification adds nothing. -/
theorem exhIE_of_antitone {W : Type*} {f : Set ℕ → Set W} (hf : Antitone f) {a : Set ℕ}
    (ha : a ⊆ weak) : exhIE {f weak, f a} (f weak) = f weak :=
  exhIE_eq_self_of_forall _ _ <| by
    rintro _ (rfl | rfl) -
    exacts [subset_rfl, hf ha]

-- (16), (17)
theorem exhIE_compl_weak : exhIE {weakᶜ, singularᶜ} weakᶜ = weakᶜ :=
  exhIE_of_antitone compl_anti singular_subset_weak

-- (18)
theorem one_mem_compl_exhIE_weak : 1 ∈ (exhIE {weak, singular} weak)ᶜ := by
  rw [exhIE_weak]
  simp

/-! ### The ambiguity approach

The Strongest Meaning Hypothesis prefers, among the readings of a plural sentence consistent with
the context, the one entailing the others. -/

-- (5)
theorem isLeast_of_monotone {W : Type*} {f : Set ℕ → Set W} (hf : Monotone f) :
    IsLeast {f weak, f strong} (f strong) :=
  ⟨Set.mem_insert_of_mem _ rfl, by
    rintro _ (rfl | rfl)
    exacts [hf strong_subset_weak, le_rfl]⟩

-- (6)
theorem isLeast_of_antitone {W : Type*} {f : Set ℕ → Set W} (hf : Antitone f) :
    IsLeast {f weak, f strong} (f weak) :=
  ⟨Set.mem_insert _ _, by
    rintro _ (rfl | rfl)
    exacts [le_rfl, hf strong_subset_weak]⟩

-- (8)
theorem isLeast_compl_strong_of_singular :
    IsLeast {p ∈ ({weakᶜ, strongᶜ} : Set (Set ℕ)) | (p ∩ singular).Nonempty} strongᶜ := by
  refine ⟨⟨by simp, 1, by simp, by simp⟩, ?_⟩
  rintro _ ⟨rfl | rfl, hp⟩
  · obtain ⟨n, hn, hn1⟩ := hp
    rw [singular_eq] at hn1
    obtain rfl := hn1
    exact absurd (mem_weak.2 le_rfl) hn
  · exact le_rfl

/-! ### The homogeneity approach -/

/-- The plural sentence is true where its weak and strong readings are both true, false where both
are false and undefined elsewhere. -/
noncomputable def homogeneous (n : ℕ) : Trivalent := supervaluationOn {weak, strong} (n ∈ ·)

theorem homogeneous_eq_true_iff : homogeneous n = .true ↔ 2 ≤ n := by
  simp only [homogeneous, supervaluationOn_eq_true_iff, Set.mem_insert_iff,
    Set.mem_singleton_iff, forall_eq_or_imp, forall_eq, mem_weak, mem_strong]
  omega

theorem homogeneous_eq_false_iff : homogeneous n = .false ↔ n = 0 := by
  simp only [homogeneous, supervaluationOn_eq_false_iff, Set.mem_insert_iff,
    Set.mem_singleton_iff, forall_eq_or_imp, forall_eq, mem_weak, mem_strong,
    Set.insert_nonempty, true_and]
  omega

theorem homogeneous_eq_undefined_iff : homogeneous n = .undefined ↔ n ∈ singular := by
  rw [eq_undefined_iff, Ne, Ne, homogeneous_eq_true_iff, homogeneous_eq_false_iff, singular_eq,
    Set.mem_singleton_iff]
  omega

/-- Feeding more giraffes never lowers the value of the plural sentence. -/
noncomputable def homogeneousHom : ℕ →o Trivalent where
  toFun := homogeneous
  monotone' m n h := by
    rcases trichotomy (homogeneous m) with hm | hm | hm
    · rw [hm]
      exact bot_le
    · rcases trichotomy (homogeneous n) with hn | hn | hn
      · rw [homogeneous_eq_undefined_iff, singular_eq] at hm
        rw [homogeneous_eq_false_iff] at hn
        obtain rfl : m = 1 := hm
        omega
      · rw [hm, hn]
      · rw [hn]
        exact le_top
    · rw [homogeneous_eq_true_iff.2 ((homogeneous_eq_true_iff.1 hm).trans h)]
      exact le_top

@[simp] theorem coe_homogeneousHom : ⇑homogeneousHom = homogeneous := rfl

-- (23), (24)
theorem compl_homogeneous (n : ℕ) :
    (homogeneous n)ᶜ = supervaluationOn {weakᶜ, strongᶜ} (n ∈ ·) := by
  refine eq_of_eq_true_iff_of_eq_false_iff ?_ ?_
  · simp only [compl_eq_true_iff, homogeneous_eq_false_iff, supervaluationOn_eq_true_iff,
      Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq,
      Set.mem_compl_iff, mem_weak, mem_strong]
    omega
  · simp only [compl_eq_false_iff, homogeneous_eq_true_iff, supervaluationOn_eq_false_iff,
      Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq,
      Set.mem_compl_iff, mem_weak, mem_strong, Set.insert_nonempty, true_and]
    omega

-- (25), (26): usable when all that matters is whether Emily fed more than one
theorem usable_compl_homogeneous_one :
    usable (Setoid.ker (· ∈ strong)) (fun n ↦ (homogeneous n)ᶜ) 1 := by
  refine ⟨⟨0, ?_, compl_eq_true_iff.2 (homogeneous_eq_false_iff.2 rfl)⟩, ?_⟩
  · show (1 ∈ strong) = (0 ∈ strong)
    simp
  · rintro ⟨a, b, hab, ha, hb⟩
    obtain rfl := homogeneous_eq_false_iff.1 (compl_eq_true_iff.1 ha)
    have hb' : b ∈ strong := mem_strong.2 (homogeneous_eq_true_iff.1 (compl_eq_false_iff.1 hb))
    have h0 : (0 ∈ strong) = (b ∈ strong) := hab
    exact absurd (h0 ▸ hb') (by simp)

theorem not_usable_compl_homogeneous_one :
    ¬ usable (Setoid.ker (· ∈ weak)) (fun n ↦ (homogeneous n)ᶜ) 1 := by
  rintro ⟨⟨m, hm, ht⟩, -⟩
  obtain rfl := homogeneous_eq_false_iff.1 (compl_eq_true_iff.1 ht)
  have h0 : (1 ∈ weak) = (0 ∈ weak) := hm
  simp at h0

/-! ### Predictions -/

theorem multiplicity_positive :
    exhIE {weak, singular} weak = strong ∧ IsLeast {weak, strong} strong ∧
      {n | homogeneous n = .true} = strong :=
  ⟨exhIE_weak, isLeast_of_monotone monotone_id,
    Set.ext fun _ ↦ homogeneous_eq_true_iff.trans mem_strong.symm⟩

theorem multiplicity_negative :
    exhIE {weakᶜ, singularᶜ} weakᶜ = weakᶜ ∧ IsLeast {weakᶜ, strongᶜ} weakᶜ ∧
      {n | (homogeneous n)ᶜ = .true} = weakᶜ := by
  refine ⟨exhIE_compl_weak, isLeast_of_antitone compl_anti, Set.ext fun n ↦ ?_⟩
  rw [Set.mem_ofPred_eq, compl_eq_true_iff, homogeneous_eq_false_iff]
  simp

/-- Where Emily fed exactly one giraffe the implicature approach treats the positive and negative
sentences asymmetrically, and the ambiguity and homogeneity approaches do not. -/
theorem singular_context :
    (1 ∈ weak ∧ 1 ∉ exhIE {weak, singular} weak ∧
        1 ∉ exhIE {weakᶜ, singularᶜ} weakᶜ) ∧
      (1 ∉ strong ∧ 1 ∉ weakᶜ) ∧
      (homogeneous 1 = .undefined ∧ (homogeneous 1)ᶜ = .undefined) := by
  rw [exhIE_weak, exhIE_compl_weak, compl_eq_undefined_iff, homogeneous_eq_undefined_iff]
  simp

/-! ### The examples -/

/-- The numbers fed, among `k` giraffes, of which a paraphrase holds. -/
def paraphrase (k : ℕ) : Examples.Reading → Set ℕ
  | .moreThanOne => strong
  | .notMoreThanOne => strongᶜ
  | .notASingle => weakᶜ
  | .notAll => weak \ {k}

/-- The alternative that an inference excludes, among `k` giraffes. -/
def alternative (k : ℕ) : Examples.Inference → Set ℕ
  | .multiplicity => singular
  | .scalar => {k}

theorem strong_compl_ne_weak_compl : strongᶜ ≠ weakᶜ := fun h ↦
  absurd (h ▸ (by simp : (1 : ℕ) ∈ strongᶜ)) (by simp)

/-- A sentence is paraphrased by its exhaustified meaning and by no other paraphrase the paper
considers. -/
theorem reading_iff (k : ℕ) :
    ∀ e ∈ Examples.all, ∀ i, Examples.inference e = some i → ∀ r,
      (Examples.polarity e = some .positive →
        (Examples.reading e r = some .acceptable →
            paraphrase k r = exhIE {weak, alternative k i} weak) ∧
          (Examples.reading e r = some .unacceptable →
            paraphrase k r ≠ exhIE {weak, alternative k i} weak)) ∧
      (Examples.polarity e = some .negative →
        (Examples.reading e r = some .acceptable →
            paraphrase k r = exhIE {weakᶜ, (alternative k i)ᶜ} weakᶜ) ∧
          (Examples.reading e r = some .unacceptable →
            paraphrase k r ≠ exhIE {weakᶜ, (alternative k i)ᶜ} weakᶜ)) := by
  intro e he i hi r
  simp only [Examples.all, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;> cases i <;>
    first
    | exact absurd hi (by decide)
    | (refine ⟨fun hp ↦ ?_, fun hp ↦ ?_⟩ <;>
        first
        | exact absurd hp (by decide)
        | (cases r <;> refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩ <;>
            first
            | exact absurd h (by decide)
            | exact exhIE_weak.symm
            | exact (exhIE_weak_singleton k).symm
            | exact exhIE_compl_weak.symm
            | exact fun h ↦ strong_compl_ne_weak_compl (h.trans exhIE_compl_weak)))

/-- Adults reward a sentence said of Emily feeding exactly one giraffe as the implicature approach
values it: the intermediate reward where it is true unexhaustified and false exhaustified, the
minimal reward where it is false. -/
theorem reward_of_singular_context :
    ∀ e ∈ Examples.all, e.nat? "n_acted_on" = some 1 →
      (Examples.polarity e = some .positive →
        (Examples.reward e = some .intermediate →
            1 ∈ weak ∧ 1 ∉ exhIE {weak, singular} weak) ∧
          (Examples.reward e = some .minimal → 1 ∉ weak)) ∧
      (Examples.polarity e = some .negative →
        (Examples.reward e = some .intermediate →
            1 ∈ weakᶜ ∧ 1 ∉ exhIE {weakᶜ, singularᶜ} weakᶜ) ∧
          (Examples.reward e = some .minimal → 1 ∉ weakᶜ)) := by
  intro e he hn
  simp only [Examples.all, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;>
    first
    | exact absurd hn (by decide)
    | (refine ⟨fun hp ↦ ?_, fun hp ↦ ?_⟩ <;>
        first
        | exact absurd hp (by decide)
        | (refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩ <;>
            first
            | exact absurd h (by decide)
            | exact ⟨singular_context.1.1, singular_context.1.2.1⟩
            | exact singular_context.2.1.2))

end TieuEtAl2020
