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

/-- Two steps have the same initial string when a good final may turn one into the other, which it
does by replacing the second argument of a first argument, and the connective unless it is *if*,
which precedes its antecedent. -/
inductive Step.SameInitialString : Step Atom → Step Atom → Prop
  | not : Step.SameInitialString .not .not
  | right (c : Connective) (F : Formula Atom) : Step.SameInitialString (.right c F) (.right c F)
  | left {c c' : Connective} (hc : c = .cond ↔ c' = .cond) (G G' : Formula Atom) :
      Step.SameInitialString (.left c G) (.left c' G')

@[refl] theorem Step.SameInitialString.refl : ∀ s : Step Atom, s.SameInitialString s
  | .not => .not
  | .right c F => .right c F
  | .left _ G => .left Iff.rfl G G

/-- `SameInitialString K K'` holds when `K'` keeps the material of `K` before the gap and replaces
what follows it, so that it is `K` with another good final. -/
def SameInitialString (K K' : SyntacticEnvironment Atom) : Prop :=
  List.Forall₂ Step.SameInitialString K K'

@[refl] theorem SameInitialString.refl (K : SyntacticEnvironment Atom) : SameInitialString K K :=
  List.forall₂_same.2 fun s _ ↦ .refl s

/-- A good final of `K ++ [s]` is a good final of `K` inside a good final of the outermost step. -/
theorem sameInitialString_append_singleton {K L : SyntacticEnvironment Atom} {s : Step Atom} :
    SameInitialString (K ++ [s]) L ↔
      ∃ K' s', L = K' ++ [s'] ∧ SameInitialString K K' ∧ s.SameInitialString s' := by
  induction K generalizing L with
  | nil =>
    simp only [List.nil_append, SameInitialString, List.forall₂_cons_left_iff,
      List.forall₂_nil_left_iff]
    constructor
    · rintro ⟨s', _, hs, rfl, rfl⟩; exact ⟨[], s', rfl, rfl, hs⟩
    · rintro ⟨K', s', rfl, rfl, hs⟩; exact ⟨s', [], hs, rfl, rfl⟩
  | cons t K ih =>
    simp only [List.cons_append, SameInitialString, List.forall₂_cons_left_iff] at ih ⊢
    constructor
    · rintro ⟨t', L', ht, hL, rfl⟩
      obtain ⟨K', s', rfl, hK, hs⟩ := ih.1 hL
      exact ⟨t' :: K', s', rfl, ⟨t', K', ht, hK, rfl⟩, hs⟩
    · rintro ⟨K', s', rfl, ⟨t', K'', ht, hK, rfl⟩, hs⟩
      exact ⟨t', K'' ++ [s'], ht, ih.2 ⟨K'', s', rfl, hK, hs⟩, rfl⟩

/-! ### Parsing points -/

/-- The number of items of the string that follow the first argument of a connective is two for a
conjunction or a disjunction, the connective and the second argument, and one for *if*, the
consequent, since *if* precedes its antecedent and its separator is forced. -/
def _root_.Presupposition.Connective.rightItems : Connective → ℕ
  | .cond => 1
  | _ => 2

/-- The number of items of the string after the gap of a step; only closing brackets, which are
forced, follow the argument of a negation and the second argument of a connective. -/
def Step.rightItems : Step Atom → ℕ
  | .left c _ => c.rightItems
  | _ => 0

/-- The number of items of the string after the gap. -/
def rightItems (K : SyntacticEnvironment Atom) : ℕ := (K.map Step.rightItems).sum

@[simp] theorem rightItems_nil : rightItems ([] : SyntacticEnvironment Atom) = 0 := rfl

@[simp] theorem rightItems_cons (s : Step Atom) (K : SyntacticEnvironment Atom) :
    rightItems (s :: K) = s.rightItems + rightItems K := by
  simp [rightItems]

theorem rightItems_append (K K' : SyntacticEnvironment Atom) :
    rightItems (K ++ K') = rightItems K + rightItems K' := by
  simp [rightItems]

/-- `s'` keeps the material of `s` before the gap and its first `n` items after it. -/
def Step.AgreeUpTo (n : ℕ) : Step Atom → Step Atom → Prop
  | .not, s' => s' = .not
  | .right c F, s' => s' = .right c F
  | .left c G, s' =>
    if n = 0 then ∃ c' G', s' = .left c' G' ∧ (c = .cond ↔ c' = .cond)
    else if n < c.rightItems then ∃ G', s' = .left c G' else s' = .left c G

/-- `AgreeUpTo n K K'` holds when `K'` keeps the material of `K` before the gap and the first `n`
items after it, so that it is `K` with a good final of the string up to the `n`-th item, the parsing
points of [kalomoiros-2023]. -/
def AgreeUpTo : ℕ → SyntacticEnvironment Atom → SyntacticEnvironment Atom → Prop
  | _, [], K' => K' = []
  | n, s :: K, K' =>
    ∃ s' K'', K' = s' :: K'' ∧ s.AgreeUpTo n s' ∧ AgreeUpTo (n - s.rightItems) K K''

theorem Step.agreeUpTo_zero_iff {s s' : Step Atom} : s.AgreeUpTo 0 s' ↔ s.SameInitialString s' := by
  cases s with
  | not => exact ⟨fun h ↦ h ▸ .not, fun h ↦ by cases h; rfl⟩
  | right c F => exact ⟨fun h ↦ h ▸ .right c F, fun h ↦ by cases h; rfl⟩
  | left c G =>
    simp only [AgreeUpTo, ite_true]
    exact ⟨fun ⟨c', G', he, hc⟩ ↦ he ▸ .left hc G G', fun h ↦ by cases h with
      | left hc _ G' => exact ⟨_, G', rfl, hc⟩⟩

/-- The first parsing point, right after the trigger, admits every good final. -/
theorem agreeUpTo_zero_iff {K K' : SyntacticEnvironment Atom} :
    AgreeUpTo 0 K K' ↔ SameInitialString K K' := by
  induction K generalizing K' with
  | nil => exact ⟨fun h ↦ h ▸ .nil, fun h ↦ by cases h; rfl⟩
  | cons s K ih =>
    simp only [AgreeUpTo, Nat.zero_sub, SameInitialString, List.forall₂_cons_left_iff, ih,
      Step.agreeUpTo_zero_iff]
    exact ⟨fun ⟨s', K'', he, hs, hK⟩ ↦ ⟨s', K'', hs, hK, he⟩,
      fun ⟨s', K'', hs, hK, he⟩ ↦ ⟨s', K'', he, hs, hK⟩⟩

theorem Step.AgreeUpTo.refl (n : ℕ) (s : Step Atom) : s.AgreeUpTo n s := by
  cases s with
  | not => rfl
  | right c F => rfl
  | left c G =>
    simp only [AgreeUpTo]
    split_ifs
    · exact ⟨c, G, rfl, Iff.rfl⟩
    · exact ⟨G, rfl⟩

theorem AgreeUpTo.refl (n : ℕ) (K : SyntacticEnvironment Atom) : AgreeUpTo n K K := by
  induction K generalizing n with
  | nil => rfl
  | cons s K ih => exact ⟨s, K, rfl, .refl n s, ih _⟩

theorem Step.AgreeUpTo.mono {m n : ℕ} {s s' : Step Atom} (h : s.AgreeUpTo m s') (hnm : n ≤ m) :
    s.AgreeUpTo n s' := by
  cases s with
  | not => exact h
  | right c F => exact h
  | left c G =>
    simp only [AgreeUpTo] at h ⊢
    by_cases hn0 : n = 0
    · simp only [hn0, ite_true]
      by_cases hm0 : m = 0
      · simpa [hm0] using h
      · by_cases hm : m < c.rightItems
        · simp only [hm0, hm, ite_false, ite_true] at h
          obtain ⟨G', rfl⟩ := h
          exact ⟨c, G', rfl, Iff.rfl⟩
        · simp only [hm0, hm, ite_false] at h
          exact ⟨c, G, h, Iff.rfl⟩
    · have hm0 : ¬ m = 0 := by omega
      by_cases hn : n < c.rightItems
      · by_cases hm : m < c.rightItems
        · simpa [hn0, hn, hm0, hm] using h
        · simp only [hm0, hm, ite_false] at h
          simp only [hn0, hn, ite_false, ite_true]
          exact ⟨G, h⟩
      · have hm : ¬ m < c.rightItems := by omega
        simpa [hn0, hn, hm0, hm] using h

theorem AgreeUpTo.mono {m n : ℕ} {K K' : SyntacticEnvironment Atom} (h : AgreeUpTo m K K')
    (hnm : n ≤ m) : AgreeUpTo n K K' := by
  induction K generalizing m n K' with
  | nil => exact h
  | cons s K ih =>
    obtain ⟨s', K'', rfl, hs, hK⟩ := h
    exact ⟨s', K'', rfl, hs.mono hnm, ih hK (Nat.sub_le_sub_right hnm _)⟩

theorem Step.agreeUpTo_iff_eq {n : ℕ} {s s' : Step Atom} (hn : s.rightItems ≤ n) :
    s.AgreeUpTo n s' ↔ s' = s := by
  cases s with
  | not => exact Iff.rfl
  | right c F => exact Iff.rfl
  | left c G =>
    have h1 : 1 ≤ c.rightItems := by cases c <;> decide
    have hn0 : ¬ n = 0 := by simp only [rightItems] at hn; omega
    have hn' : ¬ n < c.rightItems := by simp only [rightItems] at hn; omega
    simp only [AgreeUpTo, hn0, hn', ite_false]

/-- From the last parsing point on, only the environment itself agrees. -/
theorem agreeUpTo_iff_eq {n : ℕ} {K K' : SyntacticEnvironment Atom} (hn : rightItems K ≤ n) :
    AgreeUpTo n K K' ↔ K' = K := by
  induction K generalizing n K' with
  | nil => exact Iff.rfl
  | cons s K ih =>
    rw [rightItems_cons] at hn
    simp only [AgreeUpTo, Step.agreeUpTo_iff_eq (show s.rightItems ≤ n by omega),
      ih (show rightItems K ≤ n - s.rightItems by omega)]
    exact ⟨fun ⟨_, _, he, rfl, rfl⟩ ↦ he, fun h ↦ ⟨s, K, h, rfl, rfl⟩⟩

/-- A good final of `K ++ [s]` up to a parsing point is a good final of `K` inside one of `s`. -/
theorem agreeUpTo_append_singleton {n : ℕ} {K L : SyntacticEnvironment Atom} {s : Step Atom} :
    AgreeUpTo n (K ++ [s]) L ↔
      ∃ K' s', L = K' ++ [s'] ∧ AgreeUpTo n K K' ∧ s.AgreeUpTo (n - rightItems K) s' := by
  induction K generalizing n L with
  | nil =>
    simp only [List.nil_append, AgreeUpTo, rightItems_nil, Nat.sub_zero]
    exact ⟨fun ⟨s', K'', he, hs, hK⟩ ↦ ⟨[], s', by rw [he, hK]; rfl, rfl, hs⟩,
      fun ⟨K', s', he, hK, hs⟩ ↦ ⟨s', [], by rw [he, hK]; rfl, hs, rfl⟩⟩
  | cons t K ih =>
    simp only [List.cons_append, AgreeUpTo, rightItems_cons, ih]
    constructor
    · rintro ⟨t', _, rfl, ht, K', s', rfl, hK, hs⟩
      exact ⟨t' :: K', s', rfl, ⟨t', K', rfl, ht, hK⟩, by rwa [Nat.sub_add_eq]⟩
    · rintro ⟨_, s', rfl, ⟨t', K', rfl, ht, hK⟩, hs⟩
      exact ⟨t', K' ++ [s'], rfl, ht, K', s', rfl, hK, by rwa [← Nat.sub_add_eq]⟩

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
theorem continuations_eq_top_of_le {n : ℕ} {K : SyntacticEnvironment Atom} (hn : rightItems K ≤ n) :
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
  induction h with
  | nil => trivial
  | cons hs _ ih =>
    obtain ⟨hs', hK⟩ := (dependsAt_truth_cons I).1 hw
    rw [localContext_cons, Step.localContext_eq_inter]
    refine ⟨ih hK, ?_⟩
    cases hs with
    | not => trivial
    | right c F => exact (dependsAt_right_iff I c F w).1 hs'
    | left => trivial

/-- Some good final makes the truth value at `w` depend on the gap of `K` iff `w` is in
[karttunen-1974-presupposition]'s local context of the gap. -/
theorem exists_dependsAt_iff [Nonempty Atom] (K : SyntacticEnvironment Atom) (w : W) :
    (∃ K', SameInitialString K K' ∧ DependsAt (K'.truth I) w) ↔
      w ∈ K.localContext I Set.univ := by
  refine ⟨fun ⟨_, hK', hw⟩ ↦ mem_localContext_of_dependsAt I hK' hw, fun hw ↦ ?_⟩
  induction K with
  | nil => exact ⟨[], .nil, by simp [DependsAt, truth]⟩
  | cons s K ih =>
    rw [localContext_cons, Step.localContext_eq_inter] at hw
    obtain ⟨K', hK', hdep⟩ := ih hw.1
    cases s with
    | not =>
      exact ⟨.not :: K', .cons .not hK',
        (dependsAt_truth_cons I).2 ⟨by simp [DependsAt, Step.truth], hdep⟩⟩
    | right c F =>
      exact ⟨.right c F :: K', .cons (.right c F) hK',
        (dependsAt_truth_cons I).2 ⟨(dependsAt_right_iff I c F w).2 hw.2, hdep⟩⟩
    | left c G =>
      obtain ⟨G', hG'⟩ := exists_dependsAt_left I c w
      exact ⟨.left c G' :: K', .cons (.left Iff.rfl G G') hK',
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
