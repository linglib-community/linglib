module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Order.Setoid.Partition
public import Mathlib.Order.Closure
public import Linglib.Semantics.Questions.Exhaustivity
public import Linglib.Data.Examples.George2011

/-!
# George (2011): Question Embedding and the Semantics of Answers

George builds a question from an abstract, the extension at each world of a property of the
things a *wh*-phrase ranges over. The question operator gives its mention-some answers and,
composed with an exhaustivity operator, its strongly exhaustive answers, the fibers of the abstract;
a responsive predicate holds of a question when it holds of some answer. Against weak
exhaustivity, the strongly exhaustive answers of a question and its negation coincide because
complementation is a bijection of extensions, and knowing one settles the other only for an agent
who knows the domain, so *Maggie knows who was admitted but not who wasn't* is consistent on strong
readings. Against reducibility, question-embedding *know* depends on belief as well as knowledge,
and George's twin relations theory derives both uses of a responsive predicate from a pair of an
existential and a universal relation to propositions.

## Main statements

* `classes_partition_mentionSome`: the cells of the partition are the strongly exhaustive answers
  other than the contradiction.
* `negation_generalization`, `restricted_compl_subsingleton_iff`: a question and its negation have
  the same strongly exhaustive answers, and with a restrictor outside the negation knowing one
  settles the other exactly when the domain is known.
* `reducible_iff_exists`, `reducible_embed`: a reducible predicate is one computed from the answers
  and the propositions it holds of, as every reductive account is.
* `TwinRelations.exists_proposition_of_question`, `TwinRelations.question_of_forall_proposition`,
  `TwinRelations.question_singleton`: the linking results of the twin relations theory.
* `Newspaper.know_not_reducible`, `know_question_stronglyExhaustive_iff`: *know* is not reducible,
  but on strongly exhaustive answers it is knowing the true answer.
* `rows_predicted`: the dissertation's truth judgments in its scenarios.

## Implementation notes

Abstracts are functions `W → Set τ` from worlds to extensions, and answer sets are
`Set (Set W)`. George takes knowledge and belief as primitives; the scenarios model belief by
doxastic states and knowledge as true belief, and only factivity is used in general. His
*ignorare* (101b) drops the existential conjunct that the twin relations rule yields, so the two
agree on nonempty answer sets. In the admission scenarios the fourth candidate is Wesley of (16),
and Rupert's state is Maggie's: the scenarios differ in their questions.

## References

* [george-2011]
* [groenendijk-stokhof-1984]
* [heim-1994]
* [karttunen-1977]
* [lahiri-2002]
* [sharvit-2002]
-/

@[expose] public section

namespace George2011

open Question

variable {W τ E : Type*}

/-! ### Answer sets from abstracts -/

/-- The question operator `Q` (113) gives the mention-some answers of an abstract, one for each
value. -/
def mentionSome (α : W → Set τ) : Set (Set W) := Set.range fun β ↦ {w | β ∈ α w}

/-- The strongly exhaustive answers are `Q` applied to the abstract composed with the
exhaustivity operator `X` (111), so they are the fibers of the abstract, and an extension no world
realizes contributes the contradiction. -/
def stronglyExhaustive (α : W → Set τ) : Set (Set W) := Set.range fun S ↦ α ⁻¹' {S}

variable (α : W → Set τ) (w : W)

theorem mem_mentionSome {p : Set W} : p ∈ mentionSome α ↔ ∃ β, {w | β ∈ α w} = p :=
  Set.mem_range

theorem mem_stronglyExhaustive {p : Set W} : p ∈ stronglyExhaustive α ↔ ∃ S, α ⁻¹' {S} = p :=
  Set.mem_range

/-- Groenendijk and Stokhof's true strongly exhaustive answer, George's (125), is the worlds where
the abstract has the same extension. -/
theorem strongAnswer_mentionSome : strongAnswer (mentionSome α) w = α ⁻¹' {α w} := by
  ext v
  simp only [mem_strongAnswer, mentionSome, Set.forall_mem_range, Set.mem_ofPred_eq,
    Set.mem_preimage, Set.mem_singleton_iff, Set.ext_iff]
  exact forall_congr' fun _ ↦ Iff.comm

/-- The weakly exhaustive answer (130) is the worlds whose extension includes this one's. -/
theorem weakAnswer_mentionSome : weakAnswer (mentionSome α) w = α ⁻¹' Set.Ici (α w) := by
  ext v
  simp [mentionSome, Set.subset_def]

theorem strongAnswer_mentionSome_mem : strongAnswer (mentionSome α) w ∈ stronglyExhaustive α :=
  ⟨α w, (strongAnswer_mentionSome α w).symm⟩

/-- Only one strongly exhaustive answer is true at a world (p. 41). -/
theorem trueAnswers_stronglyExhaustive :
    trueAnswers (stronglyExhaustive α) w = {strongAnswer (mentionSome α) w} := by
  ext p
  simp only [mem_trueAnswers, mem_stronglyExhaustive, Set.mem_singleton_iff,
    strongAnswer_mentionSome]
  constructor
  · rintro ⟨⟨S, rfl⟩, hw⟩
    rw [show S = α w from hw.symm]
  · rintro rfl
    exact ⟨⟨α w, rfl⟩, rfl⟩

/-- The partition (129) relates the worlds where the abstract has the same extension, so its
cells partition the worlds (p. 70). -/
theorem partition_mentionSome : partition (mentionSome α) = Setoid.ker α := by
  ext v w
  rw [← Setoid.mem_cell, ← strongAnswer_eq_cell, strongAnswer_mentionSome]
  rfl

/-- The cells of the partition (129) are the strongly exhaustive answers other than the
contradiction (footnote 24). -/
theorem classes_partition_mentionSome :
    (partition (mentionSome α)).classes = stronglyExhaustive α \ {∅} := by
  ext C
  simp only [classes_partition, Set.mem_range, strongAnswer_mentionSome, Set.mem_sdiff,
    mem_stronglyExhaustive, Set.mem_singleton_iff]
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨⟨α w, rfl⟩, Set.nonempty_iff_ne_empty.1 ⟨w, rfl⟩⟩
  · rintro ⟨⟨S, rfl⟩, hne⟩
    obtain ⟨w, hw⟩ := Set.nonempty_iff_ne_empty.2 hne
    exact ⟨w, by rw [show α w = S from hw]⟩

theorem stronglyExhaustive_nonempty : (stronglyExhaustive α).Nonempty := ⟨_, ∅, rfl⟩

theorem mentionSome_nonempty_iff : (mentionSome α).Nonempty ↔ Nonempty τ :=
  Set.range_nonempty_iff_nonempty

theorem classes_ker_subset_stronglyExhaustive : (Setoid.ker α).classes ⊆ stronglyExhaustive α :=
  Setoid.classes_ker_subset_fiber_set α

/-- The contradiction is a strongly exhaustive answer exactly when some extension is realized
in no world, the dissertation's (128). -/
theorem empty_mem_stronglyExhaustive_iff :
    ∅ ∈ stronglyExhaustive α ↔ ¬ Function.Surjective α := by
  simp only [mem_stronglyExhaustive, Function.Surjective, not_forall, Set.preimage_eq_empty_iff,
    Set.disjoint_singleton_left, Set.mem_range, not_exists]

/-- The weakly exhaustive answers (131) are the weak answers of the worlds. -/
def weaklyExhaustive : Set (Set W) := Set.range (weakAnswer (mentionSome α))

/-- A world's weakly exhaustive answer is the least true member of (131), not its only one. -/
theorem isStrongestTrueAnswer_weaklyExhaustive :
    IsStrongestTrueAnswer (weaklyExhaustive α) w (weakAnswer (mentionSome α) w) :=
  ⟨⟨⟨w, rfl⟩, self_mem_weakAnswer _ w⟩, by
    rintro _ ⟨⟨v, rfl⟩, hv⟩
    simp only [weakAnswer_mentionSome, Set.mem_preimage, Set.mem_Ici] at hv ⊢
    exact Set.preimage_mono (Set.Ici_subset_Ici.2 hv)⟩

/-- The weak answers true at `w` are those of the worlds with smaller extensions, so a world has
several true weakly exhaustive answers (p. 76). -/
theorem weakAnswer_mem_trueAnswers_weaklyExhaustive_iff (v : W) :
    weakAnswer (mentionSome α) v ∈ trueAnswers (weaklyExhaustive α) w ↔ α v ⊆ α w := by
  simp [weaklyExhaustive, weakAnswer_mentionSome]

/-! ### Negation: (9) -/

theorem stronglyExhaustive_comp {τ' : Type*} {f : Set τ → Set τ'} (hf : f.Bijective) :
    stronglyExhaustive (f ∘ α) = stronglyExhaustive α := by
  unfold stronglyExhaustive
  rw [← hf.surjective.range_comp (fun T ↦ (f ∘ α) ⁻¹' {T})]
  congr with S x
  simp [hf.injective.eq_iff]

/-- With negation outscoping any restrictor, a question and its negation have the same strongly
exhaustive answers (9). -/
theorem negation_generalization :
    stronglyExhaustive (fun w ↦ (α w)ᶜ) = stronglyExhaustive α :=
  stronglyExhaustive_comp α compl_involutive.bijective

/-! ### Partial answers: (116)–(118) -/

/-- The generalized partial answers (116) close an answer set under arbitrary disjunction, which
is a closure operator (117a)–(117c). -/
def part : ClosureOperator (Set (Set W)) :=
  ClosureOperator.ofPred (fun P ↦ Set.sUnion '' 𝒫 P) (fun P ↦ ∀ T ⊆ P, ⋃₀ T ∈ P)
    (fun P p hp ↦ ⟨{p}, Set.singleton_subset_iff.2 hp, Set.sUnion_singleton p⟩)
    (fun P T hT ↦ ⟨{s ∈ P | s ⊆ ⋃₀ T}, fun _ hs ↦ hs.1, Set.Subset.antisymm
      (Set.sUnion_subset fun _ hs ↦ hs.2) fun w ⟨t, ht, hw⟩ ↦ by
        obtain ⟨S, hS, rfl⟩ := hT ht
        obtain ⟨s, hs, hws⟩ := hw
        exact ⟨s, ⟨hS hs, (Set.subset_sUnion_of_mem hs).trans (Set.subset_sUnion_of_mem ht)⟩,
          hws⟩⟩)
    fun _ Q hPQ hQ _ ⟨T, hT, hTq⟩ ↦ hTq ▸ hQ T (hT.trans hPQ)

theorem mem_part {P : Set (Set W)} {q : Set W} : q ∈ part P ↔ ∃ T ⊆ P, ⋃₀ T = q := Iff.rfl

/-- Every mention-some answer is a partial answer to the strongly exhaustive answers (117d). -/
theorem mentionSome_subset_part : mentionSome α ⊆ part (stronglyExhaustive α) := by
  rintro p ⟨β, rfl⟩
  refine mem_part.2 ⟨(fun S ↦ α ⁻¹' {S}) '' {S | β ∈ S}, Set.image_subset_range _ _, ?_⟩
  ext w
  simp [Set.sUnion_image]

theorem empty_mem_part (P : Set (Set W)) : ∅ ∈ part P :=
  mem_part.2 ⟨∅, Set.empty_subset _, Set.sUnion_empty⟩

theorem sUnion_mem_part (P : Set (Set W)) : ⋃₀ P ∈ part P := mem_part.2 ⟨P, le_rfl, rfl⟩

/-- The disjunction of all strongly exhaustive answers is the tautology (123b). -/
theorem sUnion_stronglyExhaustive : ⋃₀ stronglyExhaustive α = Set.univ :=
  Set.eq_univ_of_forall fun w ↦ ⟨_, ⟨α w, rfl⟩, rfl⟩

/-! ### Information states knowing a strongly exhaustive answer -/

section State

variable {α} {σ : Set W}

theorem supported_stronglyExhaustive_nonempty_iff :
    (supported (stronglyExhaustive α) σ).Nonempty ↔ (α '' σ).Subsingleton := by
  constructor
  · rintro ⟨_, ⟨S, rfl⟩, hσ⟩ _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    exact (hσ hu).trans (hσ hv).symm
  · intro h
    rcases σ.eq_empty_or_nonempty with rfl | ⟨u, hu⟩
    · exact ⟨α ⁻¹' {∅}, ⟨∅, rfl⟩, Set.empty_subset _⟩
    · exact ⟨α ⁻¹' {α u}, ⟨α u, rfl⟩, fun v hv ↦ h ⟨v, hv, rfl⟩ ⟨u, hu, rfl⟩⟩

/-- With the actual world in the state, supporting a strongly exhaustive answer is entailing
the true one (p. 41). -/
theorem supported_stronglyExhaustive_nonempty_iff_subset (hw : w ∈ σ) :
    (supported (stronglyExhaustive α) σ).Nonempty ↔ σ ⊆ strongAnswer (mentionSome α) w := by
  rw [strongAnswer_mentionSome]
  constructor
  · rintro ⟨_, ⟨S, rfl⟩, hσ⟩
    rwa [show S = α w from (hσ hw).symm] at hσ
  · exact fun h ↦ ⟨_, ⟨α w, rfl⟩, h⟩

/-- With the restrictor `D` outside the negation and `A ⊆ D` settled, the negated question is
settled exactly when the domain is (p. 86). -/
theorem restricted_compl_subsingleton_iff {A D : W → Set τ} (hAD : ∀ w, A w ⊆ D w)
    (hA : (A '' σ).Subsingleton) :
    ((fun w ↦ D w \ A w) '' σ).Subsingleton ↔ (D '' σ).Subsingleton := by
  constructor
  · rintro h _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    have h₁ : D u \ A u = D v \ A v := h ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
    have h₂ : A u = A v := hA ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
    rw [← Set.union_sdiff_cancel (hAD u), ← Set.union_sdiff_cancel (hAD v), h₁, h₂]
  · rintro h _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    have h₁ : D u = D v := h ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
    have h₂ : A u = A v := hA ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
    simp only [h₁, h₂]

end State

/-! ### Embedding and reducibility -/

/-- By the embedding rule (51) a responsive predicate holds of a question when it holds of some
answer. -/
def embed (R : Set W → E → Prop) (P : Set (Set W)) (x : E) : Prop := ∃ p ∈ P, R p x

/-- A predicate has the reducibility property (9) of chapter 4 when the questions it relates an
individual to are a function of the propositions it relates it to. -/
def Reducible (R : Set W → E → Prop) (RQ : Set (Set W) → E → Prop) : Prop :=
  (fun x ↦ {P | RQ P x}).FactorsThrough fun x ↦ {p | R p x}

section Reducible

variable {R : Set W → E → Prop} {RQ : Set (Set W) → E → Prop}

theorem reducible_iff :
    Reducible R RQ ↔ ∀ a b, (∀ p, R p a ↔ R p b) → ∀ P, RQ P a ↔ RQ P b := by
  simp [Reducible, Function.FactorsThrough, Set.ext_iff]

/-- A question relation computed from the answer set and the propositions an individual is
related to is reducible, as every reductive account's is (p. 117). -/
theorem reducible_of_profile (Φ : Set (Set W) → Set (Set W) → Prop) :
    Reducible R fun P x ↦ Φ P {p | R p x} :=
  fun _ _ h ↦ by simp only [h]

theorem reducible_iff_exists :
    Reducible R RQ ↔ ∃ Φ : Set (Set W) → Set (Set W) → Prop, ∀ P x, RQ P x ↔ Φ P {p | R p x} := by
  rw [Reducible, Function.factorsThrough_iff]
  constructor
  · rintro ⟨e, he⟩
    exact ⟨fun P S ↦ P ∈ e S, fun P x ↦ by simpa using congrArg (P ∈ ·) (congrFun he x)⟩
  · rintro ⟨Φ, hΦ⟩
    exact ⟨fun S ↦ {P | Φ P S}, funext fun x ↦ Set.ext fun P ↦ hΦ P x⟩

/-- Existential quantification over any selection of answers is reducible (p. 118), including
the baseline rule and Lahiri's quantification over true answers. -/
theorem reducible_embed (f : Set (Set W) → Set (Set W)) : Reducible R fun P x ↦ embed R (f P) x :=
  reducible_of_profile fun P S ↦ ∃ p ∈ f P, p ∈ S

/-- Checking the predicate against "the answer" is reducible (p. 119), whichever answer operator
picks it. -/
theorem reducible_answer (ans : Set (Set W) → Set W) : Reducible R fun P x ↦ R (ans P) x :=
  reducible_of_profile fun P S ↦ ans P ∈ S

end Reducible

/-! ### Twin relations: §4.5.3 -/

/-- On the twin relations theory a responsive predicate's lexical entry is a pair of relations,
one that some answer must bear and one that every answer must bear (p. 158). -/
structure TwinRelations (W E : Type*) where
  existential : Set W → E → Prop
  universal : Set W → E → Prop

namespace TwinRelations

variable (R : TwinRelations W E) {P : Set (Set W)} {p : Set W} {x : E}

/-- The question-embedding use (85b) relates an individual to an answer set every answer of which
bears the universal relation and some answer the existential one. -/
def question (P : Set (Set W)) (x : E) : Prop :=
  (∀ p ∈ P, R.universal p x) ∧ ∃ p ∈ P, R.existential p x

/-- The propositional use (85a) requires both relations. -/
def proposition (p : Set W) (x : E) : Prop := R.existential p x ∧ R.universal p x

/-- Relating an individual to an answer set relates it to one of the answers (102). -/
theorem exists_proposition_of_question (h : R.question P x) : ∃ p ∈ P, R.proposition p x :=
  let ⟨hall, p, hp, hex⟩ := h
  ⟨p, hp, hex, hall p hp⟩

/-- Relating an individual to every answer of a nonempty answer set relates it to the set (103). -/
theorem question_of_forall_proposition (hP : P.Nonempty) (h : ∀ p ∈ P, R.proposition p x) :
    R.question P x :=
  ⟨fun p hp ↦ (h p hp).2, let ⟨p, hp⟩ := hP; ⟨p, hp, (h p hp).1⟩⟩

/-- On a singleton the question-embedding use is the propositional use, so a clause can be
embedded as the singleton of its proposition (§4.5.3.6). -/
@[simp] theorem question_singleton : R.question {p} x ↔ R.proposition p x := by
  simp [question, proposition, and_comm]

/-- A trivial universal relation, as for *be certain* (98)–(99), gives back the embedding rule. -/
theorem question_of_universal_true {S : Set W → E → Prop} :
    (⟨S, fun _ _ ↦ True⟩ : TwinRelations W E).question P x ↔ embed S P x := by
  simp [question, embed]

/-- A predicate with all its content in the universal relation, like Italian *ignorare* (100)–(101),
denies the embedding rule on nonempty answer sets. -/
theorem question_of_existential_true {S : Set W → E → Prop} (hP : P.Nonempty) :
    (⟨fun _ _ ↦ True, fun p x ↦ ¬ S p x⟩ : TwinRelations W E).question P x ↔ ¬ embed S P x := by
  simp only [question, embed, and_true, not_exists, not_and]
  exact and_iff_left_of_imp fun _ ↦ hP

/-- *know* (86) has knowledge as its existential relation and the truth of what is believed as its
universal one. -/
def know (knows believes : Set W → E → Prop) (w : W) : TwinRelations W E :=
  ⟨knows, fun p x ↦ believes p x → w ∈ p⟩

/-- Knowing a question is knowing some answer and believing no false one (71). -/
theorem know_question {knows believes : Set W → E → Prop} {w : W} :
    (know knows believes w).question P x ↔
      (∀ p ∈ P, believes p x → w ∈ p) ∧ ∃ p ∈ P, knows p x := Iff.rfl

/-- As knowledge entails truth, the propositional use of *know* is knowledge (84). -/
theorem know_proposition {knows believes : Set W → E → Prop} {w : W}
    (hT : ∀ p x, knows p x → w ∈ p) :
    (know knows believes w).proposition p x ↔ knows p x :=
  ⟨And.left, fun h ↦ ⟨h, fun _ ↦ hT p x h⟩⟩

/-- *forgot* (96) has forgetting as its existential relation and the forgetting of whatever was
known as its universal one. -/
def forgot (forgot knew : Set W → E → Prop) : TwinRelations W E :=
  ⟨forgot, fun p x ↦ knew p x → forgot p x⟩

end TwinRelations

/-- For a consistent believer, knowing the question (71) is knowing the true strongly exhaustive
answer (pp. 154, 163). -/
theorem know_question_stronglyExhaustive_iff {σ : E → Set W} (hσ : ∀ x, (σ x).Nonempty) (x : E) :
    (TwinRelations.know (fun p x ↦ σ x ⊆ p ∧ w ∈ p) (fun p x ↦ σ x ⊆ p) w).question
        (stronglyExhaustive α) x ↔
      σ x ⊆ strongAnswer (mentionSome α) w := by
  rw [TwinRelations.know_question, strongAnswer_mentionSome]
  constructor
  · rintro ⟨-, _, ⟨S, rfl⟩, hσx, hw⟩
    rwa [show S = α w from hw.symm] at hσx
  · intro h
    refine ⟨fun _ ⟨S, hS⟩ hb ↦ ?_, _, ⟨α w, rfl⟩, h, rfl⟩
    obtain ⟨u, hu⟩ := hσ x
    subst hS
    exact (h hu).symm.trans (hb hu)

/-! ### The newspaper scenario (35)–(36): *know* is not reducible -/

namespace Newspaper

/-- A world records whether Rupert can buy a newspaper at PaperWorld and at Newstopia. -/
abbrev World := Bool × Bool

/-- The two agents, Janna and Red. -/
inductive Agent
  | janna | red
  deriving DecidableEq

/-- Each agent's state is the worlds compatible with what they believe; Janna believes the
PaperWorld answer, Red also the Newstopia one (35). -/
def state : Agent → Set World
  | .janna => {w | w.1 = true}
  | .red => {w | w.1 = true ∧ w.2 = true}

/-- Newspapers are sold at PaperWorld only. -/
def actual : World := (true, false)

/-- *Where can Rupert buy a newspaper* (37) is the abstract giving the shops that sell, `false`
for PaperWorld and `true` for Newstopia. -/
def sells (w : World) : Set Bool := {s | if s then w.2 else w.1}

/-- An agent believes what their state entails. -/
def believes (p : Set World) (a : Agent) : Prop := state a ⊆ p

/-- Knowledge as true belief, the propositional relation the scenario holds fixed. -/
def knows (p : Set World) (a : Agent) : Prop := believes p a ∧ actual ∈ p

/-- The question-embedding *know* of (71) and (86). -/
abbrev know : TwinRelations World Agent := TwinRelations.know knows believes actual

theorem mentionSome_sells :
    mentionSome sells = {{w | w.1 = true}, {w | w.2 = true}} := by
  ext p
  simp only [mem_mentionSome, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨_ | _, rfl⟩ <;> simp [sells]
  · rintro (rfl | rfl)
    · exact ⟨false, by simp [sells]⟩
    · exact ⟨true, by simp [sells]⟩

/-- Red and Janna know the same propositions (35a), (35c). -/
theorem knows_janna_iff_red (p : Set World) : knows p .janna ↔ knows p .red := by
  simp only [knows, believes, state, Set.subset_def, Set.mem_ofPred_eq, and_imp, Prod.forall,
    actual]
  constructor
  · rintro ⟨h, ha⟩
    exact ⟨fun a b hab _ ↦ h a b hab, ha⟩
  · rintro ⟨h, ha⟩
    refine ⟨fun a b hab ↦ ?_, ha⟩
    cases b
    · exact hab ▸ ha
    · exact h a true hab rfl

/-- (33) is true. -/
theorem janna_knows : know.question (mentionSome sells) .janna := by
  rw [mentionSome_sells, TwinRelations.know_question]
  refine ⟨fun p hp hb ↦ hb rfl, {w | w.1 = true}, Set.mem_insert _ _, fun _ h ↦ h, rfl⟩

/-- (34) is untrue, since Red believes the false Newstopia answer. -/
theorem red_not_knows : ¬ know.question (mentionSome sells) .red := by
  rw [mentionSome_sells, TwinRelations.know_question]
  rintro ⟨h, -⟩
  exact Bool.false_ne_true (h {w | w.2 = true} (Set.mem_insert_of_mem _ rfl) fun _ hw ↦ hw.2)

/-- Two agents with the same propositional knowledge differ on the question, so *know* is not
reducible (§4.3.1). -/
theorem know_not_reducible : ¬ Reducible knows know.question := fun h ↦
  red_not_knows ((reducible_iff.1 h _ _ knows_janna_iff_red _).1 janna_knows)

end Newspaper

/-! ### Admissions: §3.1 -/

namespace Admissions

/-- A candidate's status. -/
inductive Status
  | notApplicant | admitted | rejected | waitlisted
  deriving DecidableEq

/-- A world assigns a status to each of four candidates, Riley, Adam, Robin and Wesley in Maggie's
scenario and Anne, Red, Alex and Jonathan in Rupert's. -/
abbrev World := Fin 4 → Status

/-- *applicant*, the restrictor of *who* in (14b)/(15b). -/
def applicant (w : World) : Set (Fin 4) := {x | w x ≠ .notApplicant}

/-- The admitted candidates. -/
def admitted (w : World) : Set (Fin 4) := {x | w x = .admitted}

/-- The rejected candidates. -/
def rejected (w : World) : Set (Fin 4) := {x | w x = .rejected}

/-- *Which applicants were admitted* (14b), with the restrictor outside the negation. -/
def admittedApplicant (w : World) : Set (Fin 4) := applicant w ∩ admitted w

/-- *Which applicants weren't admitted* (15b). -/
def notAdmittedApplicant (w : World) : Set (Fin 4) := applicant w \ admitted w

/-- The state of someone sent the complete list of admitted candidates, the first two. -/
def listed : Set World := {w | ∀ x, w x = .admitted ↔ x = 0 ∨ x = 1}

instance : DecidablePred (· ∈ listed) := fun w ↦
  inferInstanceAs (Decidable (∀ x, w x = .admitted ↔ x = 0 ∨ x = 1))

instance (w : World) : DecidablePred (· ∈ applicant w) := fun x ↦
  inferInstanceAs (Decidable (w x ≠ .notApplicant))

instance (w : World) : DecidablePred (· ∈ admitted w) := fun x ↦
  inferInstanceAs (Decidable (w x = .admitted))

instance (w : World) : DecidablePred (· ∈ rejected w) := fun x ↦
  inferInstanceAs (Decidable (w x = .rejected))

instance (w : World) : DecidablePred (· ∈ notAdmittedApplicant w) := fun x ↦
  inferInstanceAs (Decidable (x ∈ applicant w ∧ x ∉ admitted w))

theorem admitted_subset_applicant (w : World) : admitted w ⊆ applicant w :=
  fun _ hx h ↦ Status.noConfusion (hx.symm.trans h)

theorem admittedApplicant_eq (w : World) : admittedApplicant w = admitted w :=
  Set.inter_eq_right.2 (admitted_subset_applicant w)

theorem admitted_image_subsingleton : (admitted '' listed).Subsingleton := by
  rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
  exact Set.ext fun x ↦ (hu x).trans (hv x).symm

private def robinRejected : World := ![.admitted, .admitted, .rejected, .notApplicant]

private def robinAbsent : World := ![.admitted, .admitted, .notApplicant, .notApplicant]

theorem applicant_image_not_subsingleton : ¬ (applicant '' listed).Subsingleton := fun h ↦
  have h₁ : applicant robinRejected = applicant robinAbsent :=
    h ⟨robinRejected, by decide, rfl⟩ ⟨robinAbsent, by decide, rfl⟩
  absurd (h₁ ▸ (by decide : (2 : Fin 4) ∈ applicant robinRejected)) (by decide)

/-- (12) is true on the strongly exhaustive reading. -/
theorem maggie_knows_admitted :
    (supported (stronglyExhaustive admittedApplicant) listed).Nonempty := by
  rw [supported_stronglyExhaustive_nonempty_iff, funext admittedApplicant_eq]
  exact admitted_image_subsingleton

/-- (13) is false on the strongly exhaustive reading, by domain uncertainty. -/
theorem maggie_not_knows_notAdmitted :
    ¬ (supported (stronglyExhaustive notAdmittedApplicant) listed).Nonempty := fun h ↦
  applicant_image_not_subsingleton
    ((restricted_compl_subsingleton_iff admitted_subset_applicant admitted_image_subsingleton).1
      (supported_stronglyExhaustive_nonempty_iff.1 h))

/-- Nor any mention-some answer (p. 86). -/
theorem maggie_not_knows_notAdmitted_mentionSome :
    ¬ (supported (mentionSome notAdmittedApplicant) listed).Nonempty := by
  rintro ⟨_, ⟨x, rfl⟩, h⟩
  have hx : x ∈ notAdmittedApplicant robinAbsent := h (show robinAbsent ∈ listed by decide)
  exact absurd hx (by clear h hx; revert x; decide)

theorem rupert_knows_admitted : (supported (stronglyExhaustive admitted) listed).Nonempty :=
  supported_stronglyExhaustive_nonempty_iff.2 admitted_image_subsingleton

/-- Read as complementation, *which weren't admitted* is known too, by (9). -/
theorem rupert_knows_compl_admitted :
    (supported (stronglyExhaustive fun w ↦ (admitted w)ᶜ) listed).Nonempty :=
  negation_generalization admitted ▸ rupert_knows_admitted

private def jonathanRejected : World := ![.admitted, .admitted, .waitlisted, .rejected]

private def jonathanWaitlisted : World := ![.admitted, .admitted, .waitlisted, .waitlisted]

/-- Read as *were rejected*, *which weren't admitted* is not known, the complementation failure
of (17)–(20). -/
theorem rupert_not_knows_rejected :
    ¬ (supported (stronglyExhaustive rejected) listed).Nonempty := fun h ↦
  have h₁ : rejected jonathanRejected = rejected jonathanWaitlisted :=
    supported_stronglyExhaustive_nonempty_iff.1 h ⟨jonathanRejected, by decide, rfl⟩
      ⟨jonathanWaitlisted, by decide, rfl⟩
  absurd (h₁ ▸ (by decide : (3 : Fin 4) ∈ rejected jonathanRejected)) (by decide)

end Admissions

/-! ### Spector's spies (20)–(22), §4.2.3 -/

namespace Spies

/-- A world says which of Alex's four colleagues (Faith, William, Andrew, Robin) are spies. -/
abbrev World := Fin 4 → Bool

/-- *Which of his colleagues are spies*. -/
def spy (w : World) : Set (Fin 4) := {x | w x = true}

/-- In the actual world of (20) Faith and William are the spies. -/
def actual : World := ![true, true, false, false]

/-- Alex believes all four are spies. -/
def alex : Set World := {w | ∀ x, w x = true}

/-- Alex knows what his state entails and is true. -/
def knows (p : Set World) : Prop := alex ⊆ p ∧ actual ∈ p

/-- (21d) is false on the strongly exhaustive reading, since Alex knows no strongly exhaustive
answer. -/
theorem not_knows_stronglyExhaustive : ¬ ∃ p ∈ stronglyExhaustive spy, knows p := by
  rintro ⟨_, ⟨S, rfl⟩, hσ, hw⟩
  have h₁ : spy (fun _ ↦ true) = S := hσ fun _ ↦ rfl
  have h₂ : spy actual = S := hw
  exact absurd (congrArg (2 ∈ ·) (h₁.trans h₂.symm)) (by simp [spy, actual])

/-- Yet Alex knows the weakly exhaustive answer (21b), so a weakly exhaustive *know* wrongly
makes (21d) true. -/
theorem knows_weakAnswer : knows (weakAnswer (mentionSome spy) actual) := by
  rw [weakAnswer_mentionSome]
  exact ⟨fun w hw x _ ↦ hw x, Set.mem_Ici.2 le_rfl⟩

/-- Spector's repair, (71) over the mention-some answers, makes (21d) false, since Alex believes
the false answer that Andrew is a spy. -/
theorem not_know_question_mentionSome :
    ¬ (TwinRelations.know (fun p _ ↦ knows p) (fun p _ ↦ alex ⊆ p) actual).question
      (mentionSome spy) () := by
  rw [TwinRelations.know_question]
  rintro ⟨h, -⟩
  exact absurd (h _ ⟨2, rfl⟩ fun w hw ↦ hw 2) (by simp [spy, actual])

end Spies

/-! ### *forgot*, (44)–(46) -/

namespace Forgot

/-- A world records whether Rupert can buy a newspaper at PaperWorld and at Cellulose City. -/
abbrev World := Bool × Bool

/-- The two agents, Janna and Red. -/
inductive Agent
  | janna | red
  deriving DecidableEq

/-- Both agents once knew the PaperWorld answer, and Red also the Cellulose City one (45). -/
def past : Agent → Set World
  | .janna => {w | w.1 = true}
  | .red => {w | w.1 = true ∧ w.2 = true}

/-- Janna now knows nothing about newspapers and Red still knows the Cellulose City answer. -/
def present : Agent → Set World
  | .janna => Set.univ
  | .red => {w | w.2 = true}

/-- An agent knew what their past state entailed. -/
def knew (p : Set World) (a : Agent) : Prop := past a ⊆ p

/-- An agent forgot what they knew and no longer know. -/
def forgot (p : Set World) (a : Agent) : Prop := knew p a ∧ ¬ present a ⊆ p

/-- *Where could Rupert buy a newspaper*, `false` for PaperWorld and `true` for Cellulose City. -/
def sells (w : World) : Set Bool := {s | if s then w.2 else w.1}

/-- *forgot* as a twin relations pair. -/
abbrev forgotEntry : TwinRelations World Agent := TwinRelations.forgot forgot knew

theorem mentionSome_sells : mentionSome sells = {{w | w.1 = true}, {w | w.2 = true}} := by
  ext p
  simp only [mem_mentionSome, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨_ | _, rfl⟩ <;> simp [sells]
  · rintro (rfl | rfl)
    · exact ⟨false, by simp [sells]⟩
    · exact ⟨true, by simp [sells]⟩

/-- (44a) is true. -/
theorem janna_forgot : forgotEntry.question (mentionSome sells) .janna := by
  rw [mentionSome_sells]
  refine ⟨fun p hp hk ↦ ⟨hk, fun h ↦ ?_⟩, {w | w.1 = true}, Set.mem_insert _ _,
    fun _ h ↦ h, fun h ↦ Bool.false_ne_true (h (Set.mem_univ (false, true)))⟩
  rcases Set.mem_insert_iff.1 hp with rfl | rfl
  · exact Bool.false_ne_true (h (Set.mem_univ (false, true)))
  · exact Bool.false_ne_true (hk (show (true, false) ∈ past .janna from rfl))

/-- (44b) is untrue, since Red still knows the Cellulose City answer. -/
theorem red_not_forgot : ¬ forgotEntry.question (mentionSome sells) .red := by
  rw [mentionSome_sells]
  rintro ⟨h, -⟩
  exact (h {w | w.2 = true} (Set.mem_insert_of_mem _ rfl) fun _ hw ↦ hw.2).2 fun _ hw ↦ hw

/-- In a state model Red has also forgotten the conjunction (47c), so the scenario is not a
counterexample to reducibility, as George anticipates (p. 138). -/
theorem forgot_ne : ¬ ∀ p, forgot p .janna ↔ forgot p .red := fun h ↦
  have hred : forgot {w | w.1 = true ∧ w.2 = true} .red :=
    ⟨fun _ hw ↦ hw, fun h ↦ Bool.false_ne_true (h (show (false, true) ∈ present .red from rfl)).1⟩
  Bool.false_ne_true (((h _).2 hred).1 (show (true, false) ∈ past .janna from rfl)).2

end Forgot

/-! ### The dissertation's judgments -/

/-- The sentences whose truth in their scenarios the file settles. -/
inductive Sentence
  | admittedKnown | notAdmittedKnown | admittedButNot | fourStudents | jannaNewspaper
  | redNewspaper
  deriving DecidableEq, Repr

open Admissions Newspaper in
/-- What each sentence claims in its scenario, on the readings the dissertation assigns. -/
def Verdict : Sentence → Prop
  | .admittedKnown => (supported (stronglyExhaustive admittedApplicant) listed).Nonempty
  | .notAdmittedKnown => (supported (stronglyExhaustive notAdmittedApplicant) listed).Nonempty
  | .admittedButNot => (supported (stronglyExhaustive admittedApplicant) listed).Nonempty ∧
      ¬ (supported (stronglyExhaustive notAdmittedApplicant) listed).Nonempty
  | .fourStudents => (supported (stronglyExhaustive admitted) listed).Nonempty ∧
      ¬ (supported (stronglyExhaustive rejected) listed).Nonempty
  | .jannaNewspaper => know.question (mentionSome sells) .janna
  | .redNewspaper => know.question (mentionSome sells) .red

/-- A row's sentence and whether the dissertation judges it true. -/
structure Row where
  sentence : Sentence
  holds : Bool
  deriving DecidableEq, Repr

/-- The sentence and truth judgment recorded in a datum. -/
def Row.ofDatum (ex : Datum) : Option Row := do
  let sentence ← ex.parse? "sentence" [("admittedKnown", Sentence.admittedKnown),
    ("notAdmittedKnown", .notAdmittedKnown), ("admittedButNot", .admittedButNot),
    ("fourStudents", .fourStudents), ("jannaNewspaper", .jannaNewspaper),
    ("redNewspaper", .redNewspaper)]
  let holds ← ex.parse? "holds" [("yes", true), ("no", false)]
  pure ⟨sentence, holds⟩

/-- The rows of the dissertation's judgments. -/
def rows : List Row := Examples.all.filterMap Row.ofDatum

theorem rows_eq : rows = [⟨.admittedKnown, true⟩, ⟨.notAdmittedKnown, false⟩,
    ⟨.admittedButNot, true⟩, ⟨.fourStudents, true⟩, ⟨.jannaNewspaper, true⟩,
    ⟨.redNewspaper, false⟩] := by
  decide

theorem rows_predicted : ∀ r ∈ rows, (r.holds = true ↔ Verdict r.sentence) := by
  simp only [rows_eq, List.forall_mem_cons, List.mem_nil_iff, false_implies, implies_true,
    and_true, true_iff, false_iff, Bool.false_eq_true, Verdict]
  exact ⟨Admissions.maggie_knows_admitted, Admissions.maggie_not_knows_notAdmitted,
    ⟨Admissions.maggie_knows_admitted, Admissions.maggie_not_knows_notAdmitted⟩,
    ⟨Admissions.rupert_knows_admitted, Admissions.rupert_not_knows_rejected⟩,
    Newspaper.janna_knows, Newspaper.red_not_knows⟩

end George2011
