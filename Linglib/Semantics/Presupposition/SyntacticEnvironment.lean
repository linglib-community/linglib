module

public import Linglib.Semantics.Presupposition.Formula
public import Linglib.Semantics.Presupposition.Occurrence

/-!
# Syntactic environments

A syntactic environment `a _ b` is a formula with a gap, in Schlenker's sense. It is represented by
the steps from the gap to the root, innermost first (`SyntacticEnvironment`): the argument of a
negation, or the first or the second argument of a binary connective whose other argument is given.
Filling the gap gives a formula (`SyntacticEnvironment.fill`), and the environment's meaning is the
function from the gap's truth set to the formula's (`SyntacticEnvironment.truth`). The triggers of a
formula are listed with their environments by `Formula.triggers`.

The incremental theories of projection consult every good final of the initial string up to a
trigger: `SameInitialString K K'` holds when `K'` keeps the material of `K` before the gap and
replaces what follows it. For the first argument of a conjunction or a disjunction the connective
itself follows the gap in the string, so it may be replaced too, while *if* precedes its
antecedent.

Kalomoiros checks the constraint at every parsing point after a trigger: `AgreeUpTo n K K'` holds
when `K'` keeps the material before the gap and the first `n` items after it, counting the
connective after a first argument and the second argument as one item each. At the first point it
admits every good final (`SyntacticEnvironment.agreeUpTo_zero_iff`), and from the last point on only
the environment itself (`SyntacticEnvironment.agreeUpTo_iff_eq`). The continuations at a parsing
point `n : ℕ∞` are the truth functions of these finals, the sentence's own at `⊤`
(`SyntacticEnvironment.continuations`); a later parsing point consults fewer of them
(`SyntacticEnvironment.antitone_continuations`). With them the triggers of a formula are occurrences
in the sense of `Presupposition.Occurrence` (`Formula.occurrences`).

Karttunen's local context of a gap (`SyntacticEnvironment.localContext`) is recovered from the
good finals: some good final makes the formula's truth value at a world depend on the gap iff the
world is in the local context (`SyntacticEnvironment.exists_dependsAt_iff`), and the filtering
evaluation is defined at a world iff every trigger's presupposition holds there whenever the world
is in the trigger's local context (`Formula.middleKleene_ne_zero_iff`).

## Main definitions

* `Presupposition.SyntacticEnvironment`: a formula with a gap.
* `Presupposition.SyntacticEnvironment.fill`, `Presupposition.SyntacticEnvironment.truth`: filling
  the gap, and the meaning as a function of the gap's.
* `Presupposition.Formula.triggers`: the triggers of a formula with their environments.
* `Presupposition.SyntacticEnvironment.SameInitialString`: the environments of the good finals.
* `Presupposition.SyntacticEnvironment.AgreeUpTo`: the environments of the good finals at a parsing
  point.
* `Presupposition.SyntacticEnvironment.continuations`: the continuations at a parsing point.
* `Presupposition.Formula.occurrences`: the triggers of a formula as occurrences.
* `Presupposition.SyntacticEnvironment.localContext`: Karttunen's local context of the gap.

## References

* [schlenker-2009]
* [kalomoiros-2023]
* [karttunen-1974-presupposition]
* [peters-1979]
-/

@[expose] public section

namespace Presupposition

variable {Atom W : Type*}

/-- One step from a gap to the root is the argument of a negation, or the first (`left`) or second
(`right`) argument of a binary connective whose other argument is given. -/
inductive SyntacticEnvironment.Step (Atom : Type*) where
  | not
  | left (c : Connective) (G : Formula Atom)
  | right (c : Connective) (F : Formula Atom)
  deriving DecidableEq

/-- A syntactic environment `a _ b` is a formula with a gap, given as the steps from the gap to
the root, innermost first. -/
abbrev SyntacticEnvironment (Atom : Type*) := List (SyntacticEnvironment.Step Atom)

namespace SyntacticEnvironment

namespace Step

/-- Fill the gap of a step. -/
def fill : Step Atom → Formula Atom → Formula Atom
  | not, X => .not X
  | left c G, X => .bin c X G
  | right c F, X => .bin c F X

/-- The meaning of a step as a function of the gap's truth set. -/
def truth (I : Atom → Set W) : Step Atom → Set W → Set W
  | not, d => dᶜ
  | left c G, d => {w | c.eval (w ∈ d) (w ∈ G.truth I)}
  | right c F, d => {w | c.eval (w ∈ F.truth I) (w ∈ d)}

/-- In [karttunen-1974-presupposition]'s local context of the gap of a step in the context `C`,
the second argument of a binary connective is evaluated in `C` updated as
`Connective.localContext` prescribes, and any other gap in `C` itself. -/
def localContext (I : Atom → Set W) : Step Atom → Set W → Set W
  | right c F, C => c.localContext C (F.truth I)
  | _, C => C

theorem truth_fill (I : Atom → Set W) (s : Step Atom) (X : Formula Atom) :
    (s.fill X).truth I = s.truth I (X.truth I) := by
  cases s <;> rfl

theorem localContext_eq_inter (I : Atom → Set W) (s : Step Atom) (C : Set W) :
    s.localContext I C = C ∩ s.localContext I Set.univ := by
  cases s with
  | right c F => cases c <;> simp [localContext, Connective.localContext]
  | _ => simp [localContext]

end Step

/-- Fill the gap of an environment. -/
def fill : SyntacticEnvironment Atom → Formula Atom → Formula Atom
  | [], X => X
  | s :: K, X => fill K (s.fill X)

/-- The meaning of an environment as a function of the gap's truth set. -/
def truth (I : Atom → Set W) : SyntacticEnvironment Atom → Set W → Set W
  | [], d => d
  | s :: K, d => truth I K (s.truth I d)

/-- [karttunen-1974-presupposition]'s local context of the gap of an environment, computed from
the root. -/
def localContext (I : Atom → Set W) (K : SyntacticEnvironment Atom) (C : Set W) : Set W :=
  K.foldr (fun s C ↦ s.localContext I C) C

@[simp] theorem fill_nil (X : Formula Atom) : fill [] X = X := rfl

@[simp] theorem fill_cons (s : Step Atom) (K : SyntacticEnvironment Atom) (X : Formula Atom) :
    fill (s :: K) X = fill K (s.fill X) := rfl

theorem fill_append (K K' : SyntacticEnvironment Atom) (X : Formula Atom) :
    fill (K ++ K') X = fill K' (fill K X) := by
  induction K generalizing X with
  | nil => rfl
  | cons s K ih => exact ih _

theorem truth_append (I : Atom → Set W) (K K' : SyntacticEnvironment Atom) (d : Set W) :
    truth I (K ++ K') d = truth I K' (truth I K d) := by
  induction K generalizing d with
  | nil => rfl
  | cons s K ih => exact ih _

theorem truth_fill (I : Atom → Set W) (K : SyntacticEnvironment Atom) (X : Formula Atom) :
    (K.fill X).truth I = K.truth I (X.truth I) := by
  induction K generalizing X with
  | nil => rfl
  | cons s K ih => rw [fill_cons, ih, Step.truth_fill]; rfl

@[simp] theorem localContext_nil (I : Atom → Set W) (C : Set W) :
    localContext I [] C = C := rfl

@[simp] theorem localContext_cons (I : Atom → Set W) (s : Step Atom)
    (K : SyntacticEnvironment Atom) (C : Set W) :
    localContext I (s :: K) C = s.localContext I (localContext I K C) := rfl

theorem localContext_append (I : Atom → Set W) (K K' : SyntacticEnvironment Atom) (C : Set W) :
    localContext I (K ++ K') C = localContext I K (localContext I K' C) :=
  List.foldr_append

theorem localContext_eq_inter (I : Atom → Set W) (K : SyntacticEnvironment Atom) (C : Set W) :
    localContext I K C = C ∩ localContext I K Set.univ := by
  induction K with
  | nil => simp
  | cons s K ih =>
    rw [localContext_cons, localContext_cons, Step.localContext_eq_inter, ih,
      Step.localContext_eq_inter I s (localContext I K Set.univ), Set.inter_assoc]

/-! ### The string of an environment -/

namespace Step

/-- The string of a step: the tokens before its gap and the tokens after it. -/
def yield : Step Atom → List (Token Atom) × List (Token Atom)
  | .not => ([.lparen, .not], [.rparen])
  | .left c G => (.lparen :: Token.lead c, Token.sep c :: (G.yield ++ [.rparen]))
  | .right c F => (.lparen :: (Token.lead c ++ (F.yield ++ [Token.sep c])), [.rparen])

theorem yield_fill (s : Step Atom) (X : Formula Atom) :
    (s.fill X).yield = s.yield.1 ++ (X.yield ++ s.yield.2) := by
  cases s <;> simp [fill, yield, Formula.yield]

/-- Two steps have the same initial string when the tokens before their gaps agree. -/
def SameInitialString (s s' : Step Atom) : Prop := s.yield.1 = s'.yield.1

theorem sameInitialString_not_iff {s : Step Atom} : Step.not.SameInitialString s ↔ s = .not := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ rfl⟩
  cases s with
  | not => rfl
  | left c G => cases c <;> simp [SameInitialString, yield, Token.lead] at h
  | right c F =>
    cases c <;> simp [SameInitialString, yield, Token.lead] at h <;>
      exact absurd h.symm (Formula.yield_append_ne_not F _ _)

theorem sameInitialString_right_iff {c : Connective} {F : Formula Atom} {s : Step Atom} :
    (Step.right c F).SameInitialString s ↔ s = .right c F := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ rfl⟩
  cases c <;> cases s <;> (try cases ‹Connective›) <;>
    simp only [SameInitialString, yield, Token.lead, Token.sep, List.cons_append, List.nil_append,
      List.cons.injEq, reduceCtorEq, true_and, false_and, and_false, Step.right.injEq,
      List.append_eq_nil_iff, List.cons_ne_nil] at h ⊢
  all_goals first
    | exact absurd h (Formula.yield_append_ne_not _ _ _)
    | exact absurd h (Formula.yield_append_ne_conn _ _ _ _)
    | exact absurd h.symm (Formula.yield_append_ne_conn _ _ _ _)
    | exact (Formula.yield_append_inj h).1.symm
    | (obtain ⟨rfl, h'⟩ := Formula.yield_append_inj h; simp_all)

/-- The steps with the initial string of a first argument are the first arguments of a connective
that is *if* exactly when the step's is, *if* preceding its antecedent. -/
theorem sameInitialString_left_iff {c : Connective} {G : Formula Atom} {s : Step Atom} :
    (Step.left c G).SameInitialString s ↔ ∃ c' G', s = .left c' G' ∧ (c = .cond ↔ c' = .cond) := by
  refine ⟨fun h ↦ ?_, fun ⟨c', G', he, hc⟩ ↦ he ▸ ?_⟩
  · cases s with
    | not => cases c <;> simp [SameInitialString, yield, Token.lead] at h
    | right c' F =>
      cases c <;> cases c' <;> simp [SameInitialString, yield, Token.lead] at h <;>
        exact absurd h.symm (Formula.yield_append_ne_conn _ _ _ _)
    | left c' G' =>
      exact ⟨c', G', rfl, by cases c <;> cases c' <;> simp_all [SameInitialString, yield, Token.lead]⟩
  · cases c <;> cases c' <;> simp_all [SameInitialString, yield, Token.lead]

end Step

/-- The string of an environment: the tokens before its gap and the tokens after it. -/
def yield : SyntacticEnvironment Atom → List (Token Atom) × List (Token Atom)
  | [] => ([], [])
  | s :: K => ((yield K).1 ++ s.yield.1, s.yield.2 ++ (yield K).2)

@[simp] theorem yield_nil : yield ([] : SyntacticEnvironment Atom) = ([], []) := rfl

@[simp] theorem yield_cons (s : Step Atom) (K : SyntacticEnvironment Atom) :
    yield (s :: K) = ((yield K).1 ++ s.yield.1, s.yield.2 ++ (yield K).2) := rfl

theorem yield_append (K M : SyntacticEnvironment Atom) :
    yield (K ++ M) = ((yield M).1 ++ (yield K).1, (yield K).2 ++ (yield M).2) := by
  induction K with
  | nil => simp
  | cons s K ih => simp [ih]

theorem yield_fill (K : SyntacticEnvironment Atom) (X : Formula Atom) :
    (K.fill X).yield = (yield K).1 ++ (X.yield ++ (yield K).2) := by
  induction K generalizing X with
  | nil => simp [fill]
  | cons s K ih => simp [fill, ih, Step.yield_fill]

/-- No formula's string begins the string before a gap, which leaves a bracket open. -/
theorem yield_fst_ne (K : SyntacticEnvironment Atom) (F : Formula Atom) (r : List (Token Atom)) :
    (yield K).1 ≠ F.yield ++ r := by
  intro h
  obtain ⟨-, h'⟩ := Formula.yield_append_inj (r := []) (r' := r ++ (F.yield ++ (yield K).2))
    (F := K.fill F) (F' := F) (by rw [yield_fill, h]; simp)
  exact Formula.yield_ne_nil F (List.append_eq_nil_iff.1 (List.append_eq_nil_iff.1 h'.symm).2).1

/-- The string before a gap is empty or opens with a bracket. -/
theorem yield_fst_eq_nil_or (K : SyntacticEnvironment Atom) :
    (yield K).1 = [] ∨ ∃ t, (yield K).1 = .lparen :: t := by
  induction K with
  | nil => exact .inl rfl
  | cons s K ih =>
    rcases ih with h | ⟨t, h⟩
    · refine .inr ?_
      cases s <;> simp [h, Step.yield]
    · exact .inr ⟨t ++ s.yield.1, by simp [h]⟩


/-- The string before the gap of an environment splits at its outermost step: the outermost steps of
two environments with the same initial string have the same initial string. -/
theorem Step.yield_fst_append_inj {s s' : Step Atom} {K K' : SyntacticEnvironment Atom}
    (h : s.yield.1 ++ K.yield.1 = s'.yield.1 ++ K'.yield.1) : s.yield.1 = s'.yield.1 := by
  have hK := SyntacticEnvironment.yield_fst_eq_nil_or K
  have hK' := SyntacticEnvironment.yield_fst_eq_nil_or K'
  have nK := SyntacticEnvironment.yield_fst_ne K
  have nK' := SyntacticEnvironment.yield_fst_ne K'
  cases s <;> cases s' <;> (try cases ‹Connective›) <;> (try cases ‹Connective›) <;>
    simp only [Step.yield, Token.lead, Token.sep, List.cons_append, List.nil_append,
      List.append_assoc, List.cons.injEq, reduceCtorEq, true_and, false_and, and_false] at h ⊢
  all_goals first
    | exact absurd h (nK _ _)
    | exact absurd h.symm (nK' _ _)
    | exact absurd h (Formula.yield_append_ne_not _ _ _)
    | exact absurd h.symm (Formula.yield_append_ne_not _ _ _)
    | exact absurd h (Formula.yield_append_ne_conn _ _ _ _)
    | exact absurd h.symm (Formula.yield_append_ne_conn _ _ _ _)
    | (obtain ⟨rfl, h'⟩ := Formula.yield_append_inj h; simp_all)
    | (rcases hK with h' | ⟨u, h'⟩ <;> rcases hK' with h'' | ⟨u', h''⟩ <;> simp_all)


/-- Two environments have the same initial string when the tokens before their gaps agree. -/
def SameInitialString (K K' : SyntacticEnvironment Atom) : Prop := K.yield.1 = K'.yield.1

theorem SameInitialString.symm {K K' : SyntacticEnvironment Atom} (h : K.SameInitialString K') :
    K'.SameInitialString K := Eq.symm h

theorem yield_fst_eq_nil_iff {K : SyntacticEnvironment Atom} : K.yield.1 = [] ↔ K = [] := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ rfl⟩
  cases K with
  | nil => rfl
  | cons s K => cases s <;> simp [Step.yield] at h

/-- Unique readability of the string before a gap: it splits step by step. -/
theorem sameInitialString_iff_forall₂ {K K' : SyntacticEnvironment Atom} :
    K.SameInitialString K' ↔ List.Forall₂ Step.SameInitialString K K' := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · induction K using List.reverseRecOn generalizing K' with
    | nil => obtain rfl := yield_fst_eq_nil_iff.1 h.symm; exact .nil
    | append_singleton K s ih =>
      rcases List.eq_nil_or_concat K' with rfl | ⟨K₀, s', rfl⟩
      · exact absurd (yield_fst_eq_nil_iff.1 h) (by simp)
      · simp only [SameInitialString, List.concat_eq_append, yield_append, yield_cons, yield_nil,
          List.nil_append, List.append_nil] at h
        have hs := Step.yield_fst_append_inj h
        rw [hs, List.append_cancel_left_eq] at h
        rw [List.concat_eq_append]
        exact List.rel_append (ih h) (.cons hs .nil)
  · induction h with
    | nil => rfl
    | cons hs _ ih => simp only [SameInitialString, yield_cons] at ih ⊢; rw [ih, hs]

/-- A good final of `K ++ M` is a good final of `K` inside one of `M`. -/
theorem sameInitialString_append_iff {K M L : SyntacticEnvironment Atom} :
    (K ++ M).SameInitialString L ↔
      ∃ K' M', L = K' ++ M' ∧ K.SameInitialString K' ∧ M.SameInitialString M' := by
  simp only [sameInitialString_iff_forall₂]
  refine ⟨fun h ↦ ⟨L.take K.length, L.drop K.length, (List.take_append_drop _ _).symm, ?_, ?_⟩,
    fun ⟨K', M', he, hK, hM⟩ ↦ he ▸ List.rel_append hK hM⟩
  · simpa using List.forall₂_take K.length h
  · simpa using List.forall₂_drop K.length h

theorem SameInitialString.cons {s s' : Step Atom} {K K' : SyntacticEnvironment Atom}
    (hs : s.SameInitialString s') (hK : K.SameInitialString K') :
    SameInitialString (s :: K) (s' :: K') :=
  congrArg₂ (· ++ ·) hK hs

theorem sameInitialString_nil_iff {K : SyntacticEnvironment Atom} :
    SameInitialString [] K ↔ K = [] := by
  rw [SameInitialString, yield_nil, eq_comm, yield_fst_eq_nil_iff]

/-- A good final of `K ++ [s]` is a good final of `K` inside a good final of the outermost step. -/
theorem sameInitialString_append_singleton {K L : SyntacticEnvironment Atom} {s : Step Atom} :
    (K ++ [s]).SameInitialString L ↔
      ∃ K' s', L = K' ++ [s'] ∧ K.SameInitialString K' ∧ s.SameInitialString s' := by
  rw [sameInitialString_append_iff]
  constructor
  · rintro ⟨K', M', rfl, hK, hM⟩
    obtain ⟨s', rfl⟩ : ∃ s', M' = [s'] := by
      have := (sameInitialString_iff_forall₂.1 hM).length_eq
      match M', this with
      | [s'], _ => exact ⟨s', rfl⟩
    exact ⟨K', s', rfl, hK, by simpa [SameInitialString, Step.SameInitialString] using hM⟩
  · rintro ⟨K', s', rfl, hK, hs⟩
    exact ⟨K', [s'], rfl, hK, by simpa [SameInitialString, Step.SameInitialString] using hs⟩

/-- The string after the gap of a step determines the step among those with its initial string, even
followed by more tokens. -/
theorem Step.eq_of_yield_snd_append {s s' : Step Atom} {u u' : List (Token Atom)}
    (hs : s.SameInitialString s') (h : s.yield.2 ++ u = s'.yield.2 ++ u') : s = s' ∧ u = u' := by
  cases s <;> cases s' <;> (try cases ‹Connective›) <;> (try cases ‹Connective›) <;>
    simp only [SameInitialString, Step.yield, Token.lead, Token.sep, List.cons_append,
      List.nil_append, List.append_assoc, List.cons.injEq, reduceCtorEq, true_and, false_and,
      and_false, Step.right.injEq, Step.left.injEq, true_and, and_true] at hs h ⊢
  all_goals first
    | exact h
    | exact absurd hs (Formula.yield_append_ne_not _ _ _)
    | exact absurd hs.symm (Formula.yield_append_ne_not _ _ _)
    | exact absurd hs (Formula.yield_append_ne_conn _ _ _ _)
    | exact absurd hs.symm (Formula.yield_append_ne_conn _ _ _ _)
    | (obtain ⟨rfl, h'⟩ := Formula.yield_append_inj h; simp_all)
    | (obtain ⟨rfl, h'⟩ := Formula.yield_append_inj hs; simp_all)
    | simp_all

/-- The string after a gap determines the environment among those with its initial string, even
followed by more tokens. -/
theorem eq_of_yield_snd_append {K K' : SyntacticEnvironment Atom} {t t' : List (Token Atom)}
    (hK : K.SameInitialString K') (h : K.yield.2 ++ t = K'.yield.2 ++ t') : K = K' ∧ t = t' := by
  induction sameInitialString_iff_forall₂.1 hK generalizing t t' with
  | nil => simpa using h
  | cons hs _ ih =>
    simp only [yield_cons, List.append_assoc] at h
    obtain ⟨rfl, h'⟩ := Step.eq_of_yield_snd_append hs h
    obtain ⟨rfl, rfl⟩ := ih (sameInitialString_iff_forall₂.2 ‹_›) h'
    exact ⟨rfl, rfl⟩

/-- Among environments with one initial string, no string after the gap is a proper prefix of
another. -/
theorem eq_of_yield_snd_prefix {K K' : SyntacticEnvironment Atom} (hK : K.SameInitialString K')
    (h : K.yield.2 <+: K'.yield.2) : K = K' :=
  let ⟨t, ht⟩ := h
  (eq_of_yield_snd_append (t' := []) hK (by simpa using ht)).1

/-! ### Parsing points -/

/-- `AgreeUpTo n K K'` holds when `K'` keeps the string before the gap of `K` and continues its
first `n` tokens after the gap, so that it is `K` with a good final at the `n`-th parsing point of
[kalomoiros-2023]'s Definition 3.4.4. -/
def AgreeUpTo (n : ℕ) (K K' : SyntacticEnvironment Atom) : Prop :=
  K.SameInitialString K' ∧ K.yield.2.take n <+: K'.yield.2

/-- The first parsing point, right after the trigger, admits every good final. -/
@[simp] theorem agreeUpTo_zero_iff {K K' : SyntacticEnvironment Atom} :
    AgreeUpTo 0 K K' ↔ K.SameInitialString K' := by
  simp [AgreeUpTo]

theorem AgreeUpTo.refl (n : ℕ) (K : SyntacticEnvironment Atom) : AgreeUpTo n K K :=
  ⟨rfl, List.take_prefix _ _⟩

theorem AgreeUpTo.mono {m n : ℕ} {K K' : SyntacticEnvironment Atom} (h : AgreeUpTo m K K')
    (hnm : n ≤ m) : AgreeUpTo n K K' := by
  refine ⟨h.1, ?_⟩
  rw [show K.yield.2.take n = (K.yield.2.take m).take n by rw [List.take_take, min_eq_left hnm]]
  exact (List.take_prefix _ _).trans h.2

/-- From the last token after the gap on, only the environment itself agrees. -/
theorem agreeUpTo_iff_eq {n : ℕ} {K K' : SyntacticEnvironment Atom} (hn : K.yield.2.length ≤ n) :
    AgreeUpTo n K K' ↔ K' = K := by
  refine ⟨fun ⟨hK, h⟩ ↦ ?_, fun h ↦ h ▸ .refl n K⟩
  rw [List.take_of_length_le hn] at h
  exact (eq_of_yield_snd_prefix hK h).symm

private theorem take_append_prefix_iff {α : Type*} {n : ℕ} {a a' b b' : List α}
    (h : a <+: a' → a = a') (h' : a' <+: a → a' = a) :
    a.take n ++ b.take (n - a.length) <+: a' ++ b' ↔ a.take n <+: a' ∧ b.take (n - a.length) <+: b' := by
  by_cases hn : n ≤ a.length
  · rw [Nat.sub_eq_zero_of_le hn, List.take_zero, List.append_nil]
    refine ⟨fun hp ↦ ⟨?_, List.nil_prefix⟩, fun ⟨hp, _⟩ ↦ hp.trans (List.prefix_append _ _)⟩
    by_cases ha : n ≤ a'.length
    · exact List.prefix_of_prefix_length_le hp (List.prefix_append _ _) (by simp; omega)
    · have ha' := h' ((List.prefix_of_prefix_length_le (List.prefix_append _ _) hp
        (by simp; omega)).trans (List.take_prefix _ _))
      exact absurd (ha' ▸ hn) ha
  · rw [List.take_of_length_le (by omega)]
    refine ⟨fun hp ↦ ?_, fun ⟨h₁, h₂⟩ ↦ ?_⟩
    · obtain rfl : a = a' := by
        rcases le_total a.length a'.length with hl | hl
        · exact h (List.prefix_of_prefix_length_le ((List.prefix_append a _).trans hp)
            (List.prefix_append _ _) hl)
        · exact (h' (List.prefix_of_prefix_length_le (List.prefix_append _ _)
            ((List.prefix_append a _).trans hp) hl)).symm
      exact ⟨List.prefix_rfl, (List.prefix_append_right_inj _).1 hp⟩
    · obtain rfl := h h₁
      exact (List.prefix_append_right_inj _).2 h₂

/-- A good final of `K ++ M` at a parsing point is a good final of `K` there inside a good final of
`M` at the corresponding parsing point. -/
theorem agreeUpTo_append_iff {n : ℕ} {K M L : SyntacticEnvironment Atom} :
    AgreeUpTo n (K ++ M) L ↔ ∃ K' M', L = K' ++ M' ∧ AgreeUpTo n K K' ∧
      AgreeUpTo (n - K.yield.2.length) M M' := by
  have key {K K' : SyntacticEnvironment Atom} (hK : K.SameInitialString K')
      (h : K.yield.2 <+: K'.yield.2) : K.yield.2 = K'.yield.2 := by
    rw [eq_of_yield_snd_prefix hK h]
  simp only [AgreeUpTo, sameInitialString_append_iff]
  constructor
  · rintro ⟨⟨K', M', rfl, hK, hM⟩, h⟩
    rw [yield_append, yield_append, List.take_append] at h
    obtain ⟨h₁, h₂⟩ := (take_append_prefix_iff (key hK) (key hK.symm)).1 h
    exact ⟨K', M', rfl, ⟨hK, h₁⟩, hM, h₂⟩
  · rintro ⟨K', M', rfl, ⟨hK, h₁⟩, hM, h₂⟩
    refine ⟨⟨K', M', rfl, hK, hM⟩, ?_⟩
    rw [yield_append, yield_append, List.take_append]
    exact (take_append_prefix_iff (key hK) (key hK.symm)).2 ⟨h₁, h₂⟩

@[simp] theorem agreeUpTo_nil_iff {n : ℕ} {K : SyntacticEnvironment Atom} :
    AgreeUpTo n [] K ↔ K = [] := by
  simp [AgreeUpTo, sameInitialString_nil_iff]

/-- A good final of `s :: K` at a parsing point is a good final of the step there inside a good
final of `K` at the corresponding parsing point. -/
theorem agreeUpTo_cons_iff {n : ℕ} {s : Step Atom} {K L : SyntacticEnvironment Atom} :
    AgreeUpTo n (s :: K) L ↔ ∃ s' K', L = s' :: K' ∧ AgreeUpTo n [s] [s'] ∧
      AgreeUpTo (n - s.yield.2.length) K K' := by
  rw [show s :: K = [s] ++ K from rfl, agreeUpTo_append_iff]
  constructor
  · rintro ⟨M, K', rfl, hs, hK⟩
    obtain ⟨s', rfl⟩ : ∃ s', M = [s'] := by
      have := (sameInitialString_iff_forall₂.1 hs.1).length_eq
      match M, this with
      | [s'], _ => exact ⟨s', rfl⟩
    exact ⟨s', K', rfl, hs, by simpa using hK⟩
  · rintro ⟨s', K', rfl, hs, hK⟩
    exact ⟨[s'], K', rfl, hs, by simpa using hK⟩

/-! ### The continuations at a parsing point -/

variable (I : Atom → Set W)

/-- The continuations at parsing point `n` after the gap of `K`: the truth functions of the good
finals that keep the first `n` items after the gap, and at the last parsing point the sentence's
own. -/
def continuations (K : SyntacticEnvironment Atom) : ℕ∞ → Set (Set W → Set W)
  | ⊤ => {K.truth I}
  | (n : ℕ) => (·.truth I) '' {K' | AgreeUpTo n K K'}

@[simp] theorem continuations_top (K : SyntacticEnvironment Atom) :
    K.continuations I ⊤ = {K.truth I} := rfl

theorem continuations_natCast (n : ℕ) (K : SyntacticEnvironment Atom) :
    K.continuations I n = (·.truth I) '' {K' | AgreeUpTo n K K'} := rfl

/-- The first parsing point consults every good final. -/
theorem continuations_zero (K : SyntacticEnvironment Atom) :
    K.continuations I 0 = (·.truth I) '' {K' | K.SameInitialString K'} := by
  rw [show (0 : ℕ∞) = ((0 : ℕ) : ℕ∞) from rfl, continuations_natCast]
  simp only [agreeUpTo_zero_iff]

theorem truth_mem_continuations (n : ℕ∞) (K : SyntacticEnvironment Atom) :
    K.truth I ∈ K.continuations I n := by
  induction n using ENat.recTopCoe with
  | top => rfl
  | coe n => exact ⟨K, AgreeUpTo.refl n K, rfl⟩

/-- A later parsing point consults fewer continuations. -/
theorem antitone_continuations (K : SyntacticEnvironment Atom) : Antitone (K.continuations I) := by
  intro m n hmn
  induction n using ENat.recTopCoe with
  | top => exact Set.singleton_subset_iff.2 (truth_mem_continuations I m K)
  | coe n =>
    induction m using ENat.recTopCoe with
    | top => exact absurd hmn (WithTop.not_top_le_coe n)
    | coe m =>
      rintro _ ⟨K', hK', rfl⟩
      exact ⟨K', hK'.mono (by exact_mod_cast hmn), rfl⟩

/-- From the last item after the gap on, a parsing point consults only the sentence itself. -/
theorem continuations_eq_top_of_le {n : ℕ} {K : SyntacticEnvironment Atom}
    (hn : K.yield.2.length ≤ n) :
    K.continuations I n = K.continuations I ⊤ := by
  rw [continuations_natCast, continuations_top]
  simp only [agreeUpTo_iff_eq hn, Set.ofPred_eq_eq_singleton, Set.image_singleton]

end SyntacticEnvironment

namespace Formula

open SyntacticEnvironment

/-- The triggers of a formula, each with its environment and its presupposition and assertion, so
that `K.fill (trigger p p') = F` for every `(K, p, p')` listed. -/
def triggers : Formula Atom → List (SyntacticEnvironment Atom × Atom × Atom)
  | atom _ => []
  | trigger p p' => [([], p, p')]
  | not F => (triggers F).map fun o ↦ (o.1 ++ [.not], o.2)
  | bin c F G => (triggers F).map (fun o ↦ (o.1 ++ [.left c G], o.2)) ++
      (triggers G).map fun o ↦ (o.1 ++ [.right c F], o.2)

/-- Local accommodation leaves no trigger. -/
@[simp] theorem triggers_accommodate (F : Formula Atom) : F.accommodate.triggers = [] := by
  induction F with
  | atom => rfl
  | trigger => rfl
  | not F ih => simp [accommodate, triggers, ih]
  | bin c F G ihF ihG => simp [accommodate, triggers, ihF, ihG]

theorem fill_of_mem_triggers {F : Formula Atom} {o : SyntacticEnvironment Atom × Atom × Atom}
    (h : o ∈ F.triggers) : o.1.fill (trigger o.2.1 o.2.2) = F := by
  induction F generalizing o with
  | atom => simp [triggers] at h
  | trigger p p' => simp only [triggers, List.mem_singleton] at h; subst h; rfl
  | not F ih =>
    obtain ⟨o', ho', rfl⟩ := List.mem_map.1 h
    rw [fill_append, ih ho']; rfl
  | bin c F G ihF ihG =>
    rcases List.mem_append.1 h with h | h <;> obtain ⟨o', ho', rfl⟩ := List.mem_map.1 h
    · rw [fill_append, ihF ho']; rfl
    · rw [fill_append, ihG ho']; rfl

end Formula

/-- The material after the gap of an environment contains no trigger. -/
def SyntacticEnvironment.TriggerFreeFinal (K : SyntacticEnvironment Atom) : Prop :=
  ∀ c G, SyntacticEnvironment.Step.left c G ∈ K → G.triggers = []

theorem SyntacticEnvironment.triggerFreeFinal_append {K K' : SyntacticEnvironment Atom} :
    (K ++ K').TriggerFreeFinal ↔ K.TriggerFreeFinal ∧ K'.TriggerFreeFinal := by
  simp only [TriggerFreeFinal, List.mem_append, or_imp, forall_and]

theorem SyntacticEnvironment.triggerFreeFinal_singleton {s : Step Atom} :
    TriggerFreeFinal [s] ↔ ∀ c G, s = .left c G → G.triggers = [] := by
  simp only [TriggerFreeFinal, List.mem_singleton, eq_comm]

/-! ### Karttunen's local contexts from the good finals -/

namespace SyntacticEnvironment

variable (I : Atom → Set W)

theorem isTruthFunctional_truth (K : SyntacticEnvironment Atom) :
    IsTruthFunctional (K.truth I) := by
  induction K with
  | nil => exact fun _ _ _ h ↦ h
  | cons s K ih =>
    intro w d d' h
    refine ih w _ _ ?_
    cases s <;> simp [Step.truth, h]

theorem isTruthFunctional_of_mem_continuations {n : ℕ∞} {K : SyntacticEnvironment Atom}
    {f : Set W → Set W} (hf : f ∈ K.continuations I n) : IsTruthFunctional f := by
  induction n using ENat.recTopCoe with
  | top => exact hf ▸ isTruthFunctional_truth I K
  | coe n =>
    obtain ⟨K', -, rfl⟩ := hf
    exact isTruthFunctional_truth I K'

/-- The formula's truth value depends on the gap of `s :: K` iff it depends on the gap of `s` and
on the gap of `K`. -/
theorem dependsAt_truth_cons {s : Step Atom} {K : SyntacticEnvironment Atom} {w : W} :
    DependsAt (truth I (s :: K)) w ↔ DependsAt (s.truth I) w ∧ DependsAt (K.truth I) w := by
  have hK := isTruthFunctional_truth I K
  change ¬ (w ∈ K.truth I (s.truth I Set.univ) ↔ w ∈ K.truth I (s.truth I ∅)) ↔ _
  unfold DependsAt
  by_cases ha : w ∈ s.truth I Set.univ <;> by_cases hb : w ∈ s.truth I ∅
  · rw [hK.mem_iff_of_mem ha, hK.mem_iff_of_mem hb]; tauto
  · rw [hK.mem_iff_of_mem ha, hK.mem_iff_of_notMem hb]; tauto
  · rw [hK.mem_iff_of_notMem ha, hK.mem_iff_of_mem hb]; tauto
  · rw [hK.mem_iff_of_notMem ha, hK.mem_iff_of_notMem hb]; tauto

/-- The truth value depends on the second argument of a binary connective exactly in its local
context. -/
theorem dependsAt_right_iff (c : Connective) (F : Formula Atom) (w : W) :
    DependsAt ((Step.right c F).truth I) w ↔ w ∈ (Step.right c F).localContext I Set.univ := by
  cases c <;> simp [DependsAt, Step.truth, Step.localContext, Connective.eval,
    Connective.localContext]

/-- Some second argument makes the truth value depend on the first argument of a binary
connective. -/
theorem exists_dependsAt_left [Nonempty Atom] (c : Connective) (w : W) :
    ∃ G, DependsAt ((Step.left c G).truth I) w := by
  let a := Classical.arbitrary Atom
  let taut : Formula Atom := .bin .cond (.atom a) (.atom a)
  cases c
  · exact ⟨taut, by simp [taut, DependsAt, Step.truth, Connective.eval, Formula.truth]⟩
  · exact ⟨.not taut, by simp [taut, DependsAt, Step.truth, Connective.eval, Formula.truth]⟩
  · exact ⟨.not taut, by simp [taut, DependsAt, Step.truth, Connective.eval, Formula.truth]⟩

private theorem mem_localContext_of_dependsAt {K K' : SyntacticEnvironment Atom}
    (h : SameInitialString K K') {w : W} (hw : DependsAt (K'.truth I) w) :
    w ∈ K.localContext I Set.univ := by
  rw [sameInitialString_iff_forall₂] at h
  induction h with
  | nil => trivial
  | @cons s _ _ _ hs _ ih =>
    obtain ⟨hs', hK⟩ := (dependsAt_truth_cons I).1 hw
    rw [localContext_cons, Step.localContext_eq_inter]
    refine ⟨ih hK, ?_⟩
    cases s with
    | right c F =>
      obtain rfl := Step.sameInitialString_right_iff.1 hs
      exact (dependsAt_right_iff I c F w).1 hs'
    | _ => trivial

/-- Some good final makes the truth value at `w` depend on the gap of `K` iff `w` is in
[karttunen-1974-presupposition]'s local context of the gap. -/
theorem exists_dependsAt_iff [Nonempty Atom] (K : SyntacticEnvironment Atom) (w : W) :
    (∃ K', SameInitialString K K' ∧ DependsAt (K'.truth I) w) ↔
      w ∈ K.localContext I Set.univ := by
  refine ⟨fun ⟨_, hK', hw⟩ ↦ mem_localContext_of_dependsAt I hK' hw, fun hw ↦ ?_⟩
  induction K with
  | nil => exact ⟨[], rfl, by simp [DependsAt, truth]⟩
  | cons s K ih =>
    rw [localContext_cons, Step.localContext_eq_inter] at hw
    obtain ⟨K', hK', hdep⟩ := ih hw.1
    cases s with
    | not =>
      exact ⟨.not :: K', SameInitialString.cons rfl hK',
        (dependsAt_truth_cons I).2 ⟨by simp [DependsAt, Step.truth], hdep⟩⟩
    | right c F =>
      exact ⟨.right c F :: K', SameInitialString.cons rfl hK',
        (dependsAt_truth_cons I).2 ⟨(dependsAt_right_iff I c F w).2 hw.2, hdep⟩⟩
    | left c G =>
      obtain ⟨G', hG'⟩ := exists_dependsAt_left I c w
      exact ⟨.left c G' :: K', SameInitialString.cons rfl hK',
        (dependsAt_truth_cons I).2 ⟨hG', hdep⟩⟩

end SyntacticEnvironment

/-- The filtering evaluation is defined at `w` iff every trigger's presupposition holds there
whenever `w` is in the trigger's [karttunen-1974-presupposition] local context. -/
theorem Formula.middleKleene_ne_zero_iff (I : Atom → Set W) (F : Formula Atom) (w : W) :
    F.middleKleene I w ≠ 0 ↔
      ∀ o ∈ F.triggers, w ∈ o.1.localContext I Set.univ → w ∈ I o.2.1 := by
  open SyntacticEnvironment in
  induction F with
  | atom p => simp [middleKleene, eval, triggers]
  | trigger p p' => simp [middleKleene, eval, triggers]
  | not F ih =>
    simp only [middleKleene, eval, Pi.neg_apply, ne_eq, SignType.neg_eq_zero_iff, triggers,
      List.forall_mem_map, localContext_append, localContext_cons, localContext_nil,
      Step.localContext]
    exact ih
  | bin c F G ihF ihG =>
    simp only [triggers, List.forall_mem_append, List.forall_mem_map, localContext_append,
      localContext_cons, localContext_nil, Step.localContext]
    rw [← ihF]
    have hG : (∀ o ∈ G.triggers, w ∈ o.1.localContext I (c.localContext Set.univ (F.truth I)) →
        w ∈ I o.2.1) ↔ (w ∈ c.localContext Set.univ (F.truth I) → G.middleKleene I w ≠ 0) := by
      rw [ihG]
      refine ⟨fun h hc o ho hl ↦ h o ho ?_, fun h o ho hl ↦ ?_⟩
      · rw [localContext_eq_inter]; exact ⟨hc, hl⟩
      · rw [localContext_eq_inter] at hl; exact h hl.1 o ho hl.2
    rw [hG, middleKleene_bin_ne_zero I]

/-! ### Occurrences -/

/-- The occurrence of the trigger `trigger p p'` at the gap of `K`, with the continuations of its
parsing points. -/
def SyntacticEnvironment.occurrence (I : Atom → Set W) (K : SyntacticEnvironment Atom)
    (p p' : Atom) : Occurrence W (Set W) where
  presupposition := I p
  assertion := I p'
  continuations := K.continuations I
  truth := K.truth I
  antitone_continuations := SyntacticEnvironment.antitone_continuations I K
  continuations_top := SyntacticEnvironment.continuations_top I K

/-- The occurrences of the triggers of a formula. -/
def Formula.occurrences (I : Atom → Set W) (F : Formula Atom) : List (Occurrence W (Set W)) :=
  F.triggers.map fun t ↦ t.1.occurrence I t.2.1 t.2.2

theorem Formula.forall_mem_occurrences {I : Atom → Set W} {F : Formula Atom}
    {P : Occurrence W (Set W) → Prop} :
    (∀ o ∈ Formula.occurrences I F, P o) ↔ ∀ t ∈ F.triggers, P (t.1.occurrence I t.2.1 t.2.2) :=
  List.forall_mem_map

end Presupposition
