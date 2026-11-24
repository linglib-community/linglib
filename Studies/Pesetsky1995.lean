module

public import Mathlib.Logic.Relation
public import Linglib.Data.Examples.Pesetsky1995
public import Linglib.Syntax.Tree.Shell
public import Linglib.Languages.English.Adpositions

/-!
# Pesetsky (1995): Zero Syntax

In the Cascade of [pesetsky-1995] the dependents of a predicate form a right-branching stack of
prepositional phrases, each preposition with a phrase in its specifier and the phrase of the
next preposition as its complement, so that the heads from the predicate downward are linearly
ordered by c-command. A head moves only into the head that governs it, the next one up. We
record at each head position the word that stands there, and define one step of head movement:
the word at a position, when its host is an affix, adjoins to the word at the position above
and leaves its own position empty, and the result keeps the host of the word above. A sequence
of heads converges when some sequence of steps leaves no affix outside the word of the
predicate. We prove that this holds exactly when no affix stands below a head that is not one.

The causative reading of an object-experiencer verb, and of a double object verb with a Causer
for its subject, comes from a zero preposition CAUS, an affix, which is not selected by the
predicate and so stands below the prepositions that introduce its selected arguments. *At*,
*about*, *to* and *for* are not affixes, while the zero preposition G of the double object
construction is one. A Causer therefore excludes a Target or Subject Matter, *The article in
the Times angered Bill at the government*, and the prepositional dative, *The war years gave
his first big success to Mailer*, and allows the double object construction. The zero morpheme
SUG of *His manner was angry* behaves in the same way. The judgments the book reports for
these cases are the ones convergence predicts.

The Causer is the complement of CAUS, the lowest position of the Cascade, which every specifier
c-commands, and from there it moves to the specifier of the verb phrase, from which it
c-commands them. The first is the configuration in which the Experiencer binds into the Causer
in *Pictures of each other annoyed the kids*.

## Implementation notes

* A step of head movement is a relation on lists of words, one per head position, and not an
  operation on trees: the tree substrate has no adjunction of a head to a head whose category it
  shares, as CAUS shares that of *at*. A word is written host first, so a step that moves a word
  into an empty position moves it through a trace.
* That an affix must reach the predicate is stated in the book of CAUS, of G and of SUG, and is
  required here of every affixal head. The three zero morphemes are one `Morph`, a suffix with
  no segmental material: they differ in meaning, which a morph does not record, and the account
  reads only that each is an affix.
* The prepositional dative has the Theme in the specifier of *to* and the Goal below it, as in
  the Cascade the book gives for *give books to these people*; the diagram of the
  prepositional dative with CAUS is labelled with the Goal above *to*. No theorem here
  depends on which phrase a specifier holds.
* *Hand* and *bring* take a Causer and show no contrast between the two dative frames. The book
  takes such verbs to have a Causer subject without CAUS, and their rows are compared with the
  sequence of heads without it.
* *About* is not among the prepositions of `English.Adpositions`.

## TODO

* The checking account, on which CAUS is on the verb from the start and the preposition CAUS
  raises to it, and with it the two positions of the Causer and the condition on movement
  between positions of one θ-role.
* Strong and weak features: CAUS that suppresses no θ-role, as in *John broke the cookie into
  little pieces*, need not move, and which verbs take which CAUS is not derived.
* The unselected prepositions that may stand above or below CAUS, *Interviewing Nixon gave
  nobody a book at any time*, are covered by the characterization of convergence and have no
  rows.

## References

* [pesetsky-1995]
* [larson-1988]
-/

@[expose] public section

namespace Pesetsky1995

open PhraseStructure Tree Shell Morphology Relation

/-! ### Head movement -/

section HeadMovement

variable {α : Type*} {p : α → Prop} {s t : List (List α)} {l l₁ l₂ : List α} {v : α}

/-- (488), (489): a step of head movement. The word `w :: z` at a head position, whose host `w`
is an affix, adjoins to the word `y` at the position above it and leaves its position empty; the
result keeps the host of `y`. -/
inductive Adjoins (p : α → Prop) : List (List α) → List (List α) → Prop
  | intro (a : List (List α)) (y : List α) (w : α) (z : List α) (b : List (List α)) (hw : p w) :
      Adjoins p (a ++ y :: (w :: z) :: b) (a ++ (y ++ w :: z) :: [] :: b)

theorem Adjoins.flatten_eq (h : Adjoins p s t) : t.flatten = s.flatten := by
  obtain ⟨a, y, w, z, b, -⟩ := h
  simp

theorem Adjoins.length_eq (h : Adjoins p s t) : t.length = s.length := by
  obtain ⟨a, y, w, z, b, -⟩ := h
  simp

theorem Adjoins.append_left (a : List (List α)) (h : Adjoins p s t) :
    Adjoins p (a ++ s) (a ++ t) := by
  obtain ⟨a', y, w, z, b, hw⟩ := h
  simpa only [List.append_assoc] using Adjoins.intro (a ++ a') y w z b hw

-- Whatever follows the host of a word is an affix.
theorem Adjoins.forall_tail (h : Adjoins p s t) (hs : ∀ u ∈ s, ∀ w ∈ u.tail, p w) :
    ∀ u ∈ t, ∀ w ∈ u.tail, p w := by
  obtain ⟨a, y, w, z, b, hw⟩ := h
  intro u hu x hx
  simp only [List.mem_append, List.mem_cons] at hu
  rcases hu with hu | rfl | rfl | hu
  · exact hs u (by simp [hu]) x hx
  · rcases y with _ | ⟨y₀, y⟩
    · exact hs (w :: z) (by simp) x (by simpa using hx)
    · simp only [List.cons_append, List.tail_cons, List.mem_append, List.mem_cons] at hx
      rcases hx with hx | rfl | hx
      · exact hs (y₀ :: y) (by simp) x (by simpa using hx)
      · exact hw
      · exact hs (w :: z) (by simp) x (by simpa using hx)
  · simp at hx
  · exact hs u (by simp [hu]) x hx

theorem forall_tail_of_reflTransGen (h : ReflTransGen (Adjoins p) s t)
    (hs : ∀ u ∈ s, ∀ w ∈ u.tail, p w) : ∀ u ∈ t, ∀ w ∈ u.tail, p w := by
  induction h with
  | refl => exact hs
  | tail _ h ih => exact h.forall_tail ih

theorem flatten_eq_of_reflTransGen (h : ReflTransGen (Adjoins p) s t) : t.flatten = s.flatten := by
  induction h with
  | refl => rfl
  | tail _ h ih => exact h.flatten_eq.trans ih

-- Affixes below a word adjoin to it one after another, the lowest first.
theorem reflTransGen_adjoins_of_forall (u : List α) (hl : ∀ w ∈ l, p w) (b : List (List α)) :
    ReflTransGen (Adjoins p) (u :: l.map ([·]) ++ b)
      ((u ++ l) :: List.replicate l.length [] ++ b) := by
  induction l generalizing u with
  | nil => simp [ReflTransGen.refl]
  | cons w l ih =>
    have h₁ := (ih [w] fun x hx ↦ hl x (by simp [hx])).lift ([u] ++ ·) fun _ _ ↦
      Adjoins.append_left [u]
    have h₂ := Adjoins.intro [] u w l (List.replicate l.length [] ++ b) (hl w (by simp))
    simpa [List.replicate_succ] using h₁.tail h₂

/-- (510): a sequence of heads, the predicate first, converges when some sequence of steps of
head movement leaves no affix outside the word of the predicate. -/
def Converges (p : α → Prop) (l : List α) : Prop :=
  ∃ u s, ReflTransGen (Adjoins p) (l.map ([·])) (u :: s) ∧ ∀ x ∈ s, ∀ w ∈ x, ¬ p w

theorem converges_cons_iff_exists :
    Converges p (v :: l) ↔ ∃ l₁ l₂, l = l₁ ++ l₂ ∧ (∀ w ∈ l₁, p w) ∧ ∀ w ∈ l₂, ¬ p w := by
  constructor
  · rintro ⟨u, s, h, hs⟩
    have hf : u ++ s.flatten = v :: l := by
      simpa [← List.flatMap_def] using flatten_eq_of_reflTransGen h
    have hu := forall_tail_of_reflTransGen h
      (fun u hu w hw ↦ by obtain ⟨x, -, rfl⟩ := List.mem_map.1 hu; simp at hw) u (by simp)
    have hs' : ∀ w ∈ s.flatten, ¬ p w := fun w hw ↦ by
      obtain ⟨x, hx, hwx⟩ := List.mem_flatten.1 hw
      exact hs x hx w hwx
    rcases u with _ | ⟨x, u⟩
    · exact ⟨[], l, rfl, by simp, fun w hw ↦ hs' w (by simp_all)⟩
    · obtain ⟨rfl, rfl⟩ : x = v ∧ u ++ s.flatten = l := by simpa using hf
      exact ⟨u, s.flatten, rfl, hu, hs'⟩
  · rintro ⟨l₁, l₂, rfl, h₁, h₂⟩
    refine ⟨v :: l₁, _, by simpa using reflTransGen_adjoins_of_forall [v] h₁ (l₂.map ([·])), ?_⟩
    intro x hx w hw
    simp only [List.mem_append, List.mem_replicate, List.mem_map] at hx
    rcases hx with ⟨-, rfl⟩ | ⟨y, hy, rfl⟩
    · simp at hw
    · exact h₂ w (by simp_all)

/-- A sequence of heads converges exactly when no affix stands below a head that is not an
affix. -/
theorem converges_cons_iff : Converges p (v :: l) ↔ l.Pairwise fun a b ↦ p b → p a := by
  rw [converges_cons_iff_exists]
  constructor
  · rintro ⟨l₁, l₂, rfl, h₁, h₂⟩
    exact List.pairwise_append.2 ⟨List.pairwise_of_forall_mem_list fun a ha _ _ _ ↦ h₁ a ha,
      List.pairwise_of_forall_mem_list fun _ _ b hb hpb ↦ (h₂ b hb hpb).elim,
      fun a ha _ _ _ ↦ h₁ a ha⟩
  · intro h
    induction l with
    | nil => exact ⟨[], [], rfl, by simp, by simp⟩
    | cons a l ih =>
      obtain ⟨ha, hl⟩ := List.pairwise_cons.1 h
      by_cases hpa : p a
      · obtain ⟨l₁, l₂, rfl, h₁, h₂⟩ := ih hl
        exact ⟨a :: l₁, l₂, rfl, by simpa [hpa] using h₁, h₂⟩
      · exact ⟨[], a :: l, rfl, by simp, by
          simpa [hpa] using fun b hb hpb ↦ hpa (ha b hb hpb)⟩

instance [DecidablePred p] (v : α) (l : List α) : Decidable (Converges p (v :: l)) :=
  decidable_of_iff _ converges_cons_iff.symm

/-- An affix below a head that is not an affix cannot reach the predicate. -/
theorem not_converges_of_not_of {q c : α} (hq : ¬ p q) (hc : p c) (l₃ : List α) :
    ¬ Converges p (v :: (l₁ ++ q :: (l₂ ++ c :: l₃))) := by
  rw [converges_cons_iff, List.pairwise_append]
  rintro ⟨-, h, -⟩
  exact hq ((List.pairwise_cons.1 h).1 c (by simp) hc)

end HeadMovement

/-! ### Affixes -/

/-- A morph is an affix when it is bound to a host as one. -/
abbrev IsAffix (m : Morph) : Prop := m.kind.attachment? = some .affix

/-- CAUS, the zero causative preposition, an affix. -/
def caus : Morph := .suff ""

/-- G, the zero preposition of the double object construction, an affix. -/
def g : Morph := .suff ""

/-- SUG, the zero morpheme of an adjective predicated of what suggests an emotion, an affix. -/
def sug : Morph := .suff ""

/-! ### The Target/Subject Matter restriction and the two dative frames -/

open Examples

/-- The prepositions that introduce the selected arguments of each frame. -/
def _root_.Pesetsky1995.Examples.Frame.heads : Frame → List Morph
  | .bare => []
  | .doubleObject => [g]
  | .toPhrase => English.Adpositions.to_.morphs
  | .forPhrase => English.Adpositions.for_.morphs
  | .atPhrase => English.Adpositions.at_.morphs
  | .aboutPhrase => [.free "about"]

/-- The zero morpheme that comes with the role of the subject: CAUS with a Causer and SUG with a
Suggestor. -/
def _root_.Pesetsky1995.Examples.Subject.zero : Subject → List Morph
  | .causer => [caus]
  | .suggestor => [sug]
  | .agent | .experiencer => []

/-- The heads of the Cascade of the predicate `v`: the prepositions of its selected arguments,
and below them the zero morpheme, which is not selected. -/
def heads (v : Morph) (s : Subject) (f : Frame) : List Morph := v :: (f.heads ++ s.zero)

/-- A preposition that is not an affix, as *at* and *about* are not, strands CAUS below it. -/
theorem tsm_restriction (v : Morph) {q : Morph} (hq : ¬ IsAffix q) :
    ¬ Converges IsAffix [v, q, caus] :=
  not_converges_of_not_of (l₁ := []) (l₂ := []) hq rfl []

-- (514): without a Target or Subject Matter nothing intervenes.
theorem converges_caus (v : Morph) : Converges IsAffix [v, caus] :=
  converges_cons_iff.2 (by decide)

-- (511), (512): CAUS reaches the verb through G and not through *to*.
theorem oehrle (v : Morph) :
    Converges IsAffix (heads v .causer .doubleObject) ∧
      ¬ Converges IsAffix (heads v .causer .toPhrase) := by
  simp only [heads, converges_cons_iff]
  decide

-- (517): an unselected preposition may stand below CAUS and not above it.
theorem converges_unselected (v : Morph) {q : Morph} (hq : ¬ IsAffix q) :
    Converges IsAffix [v, g, caus, q] ∧ ¬ Converges IsAffix [v, g, q, caus] :=
  ⟨converges_cons_iff.2 (by simp [g, caus, IsAffix, Morph.suff]),
    not_converges_of_not_of (l₁ := [g]) (l₂ := []) hq rfl []⟩

/-- An example is acceptable exactly when the heads of its Cascade converge. -/
theorem acceptable_iff_converges (v : Morph) :
    ∀ x : Example, x ∉ [.ex_503c, .ex_503d] → ∀ s ∈ x.subject, ∀ f ∈ x.frame,
      (x.datum.judgment = .acceptable ↔ Converges IsAffix (heads v s f)) := by
  simp only [heads, converges_cons_iff]
  decide

-- (503): *hand* shows no contrast, as a verb whose Causer comes without CAUS.
theorem acceptable_hand (v : Morph) :
    ∀ x ∈ [Example.ex_503c, .ex_503d], ∀ f ∈ x.frame,
      (x.datum.judgment = .acceptable ↔ Converges IsAffix (heads v .agent f)) := by
  simp only [heads, converges_cons_iff]
  decide

/-! ### Cascades -/

section Cascade

variable (v : Morph) (s : Subject) (f : Frame) (subj : Tree Cat Morph) (arg : ℕ → Tree Cat Morph)

/-- (455): the shells of the Cascade of the predicate `v`, with `subj` in its specifier and
`arg i` in the specifier of the `i`th preposition. -/
def cascade : List (Shell Morph) :=
  { cat := .V, spec := subj, head := terminal .V v } ::
    (f.heads ++ s.zero).mapIdx fun i p ↦ { cat := .P, spec := arg i, head := terminal .P p }

theorem length_cascade : (cascade v s f subj arg).length = (heads v s f).length := by
  simp [cascade, heads]

-- The words at the head positions of a Cascade are its heads.
theorem flatMap_yield_cascade :
    (cascade v s f subj arg).flatMap (fun L ↦ L.head.yield) = heads v s f := by
  cases s <;> cases f <;> rfl

local notation "C" => cascade v s f subj arg

theorem getElem?_headPos_cascade (causer : Tree Cat Morph) {k : ℕ} (hk : k < (heads v s f).length) :
    (stack C causer)[headPos C k]? =
      some (terminal (if k = 0 then .V else .P) (heads v s f)[k]) := by
  have hk' : k < (C).length := by rwa [length_cascade]
  rw [getElem?_headPos _ hk']
  rcases k with _ | k <;> simp [cascade, heads]

/-- In the Cascade of a predicate with CAUS every specifier c-commands the complement of CAUS,
and none is c-commanded by it; a phrase in the specifier of the predicate c-commands the
others. -/
theorem cCommands_argPos_cascade (causer : Tree Cat Morph) {i j : ℕ} (hij : i < j)
    (hj : j ≤ (heads v s f).length) :
    (stack C causer).CCommands (argPos C i) (argPos C j) ∧
      ¬ (stack C causer).CCommands (argPos C j) (argPos C i) := by
  rw [← length_cascade v s f subj arg] at hj
  exact ⟨(cCommands_argPos_iff _ _ (by omega) hj).2 hij,
    fun h ↦ hij.asymm ((cCommands_argPos_iff _ _ hj (by omega)).1 h)⟩

-- (513): the verb c-commands *at*, and *at* CAUS.
theorem cCommands_headPos_cascade (causer : Tree Cat Morph) {i j : ℕ} (hij : i < j)
    (hj : j < (heads v s f).length) :
    (stack C causer).CCommands (headPos C i) (headPos C j) := by
  rw [← length_cascade v s f subj arg] at hj
  exact (cCommands_headPos_iff _ _ (by omega) hj).2 hij

end Cascade

end Pesetsky1995
