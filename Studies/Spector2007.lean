module

public import Linglib.Semantics.Questions.Partition.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Insert
public import Mathlib.Order.Minimal

/-!
# Spector (2007): Scalar Implicatures: Exhaustivity and Gricean Reasoning

This file formalizes the Gricean derivation of exhaustivity of [spector-2007]. The
neo-Gricean rules infer from an utterance that the speaker does not believe any stronger
scalar alternative and then, assuming the speaker maximally informed, that the alternative is
false; on multiple disjunctions the second step yields unwanted negations, which the
alternative-expanding repair of [sauerland-2004] avoids only by an ad hoc scale. The paper
replaces the two rules by one reasoning over the question under discussion, a partition
([groenendijk-stokhof-1984]): the speaker's information state, relativized to the question,
entails the answer and no stronger member of the alternative set, and the hearer assumes the
state maximally informed among such states. `IsOptimal`, `optimalStates` and `maximalStates`
state this over any partition question, and `Implicates` what every maximal state entails.

For answers to a question about which atoms hold, states and answers are sets of valuations,
the finest question applies, and the alternative set of a positive answer, one that favors no
negative literal, is the set of positive answers. `isOptimal_iff` derives the paper's
reduction of optimality to "the answer is the strongest positive proposition the state
entails", `Pos i = P`, and `maximalStates_eq` its theorem: the unique maximal state is
the minimal valuations of `P` (`Minimal`), so a positive answer implicates its
exhaustification in the sense of Groenendijk and Stokhof. `no_unwanted_negation` checks the
reasoning against the disjunction case: no optimal state for *A or B* decides *A*.

## Implementation notes

Information states are consistent, so the contradiction is not a state; without this the
degenerate case of a single atom would admit the empty state as optimal. Positivity follows
the paper's main text, favoring a positive literal and no negative one, which entails the
appendix's clause that the proposition is neither the tautology nor the contradiction. The
appendix's syntactic theorems, that a proposition favors a literal exactly when every
formula expressing it mentions the literal and that positive propositions are those
expressible without negation, are not formalized, nor are the alternative sets the paper
proposes for negative and quasi-positive answers. The paper's third fact, that removing a
minimal valuation from a positive proposition leaves it positive, is bypassed: the proof of
the theorem here goes through the reduction directly.

## References

* [spector-2007]
* [groenendijk-stokhof-1984]
* [sauerland-2004]
-/

@[expose] public section

namespace Spector2007

/-! ### The Gricean reasoning over a partition question -/

section Gricean

variable {W : Type*} (Q : Setoid W)

/-- An information state relativized to the question is the union of the cells it meets. -/
def relativize (i : Set W) : Set W := {w | ∃ w' ∈ i, Q w' w}

theorem subset_relativize (i : Set W) : i ⊆ relativize Q i := fun w hw ↦ ⟨w, hw, Q.refl' w⟩

@[simp] theorem relativize_bot (i : Set W) : relativize ⊥ i = i := by
  ext w; simp [relativize]

/-- An answer is strongly relevant when it excludes a cell and does not cut across cells. -/
def StronglyRelevant (α : Set W) : Prop :=
  (∃ w, Q.cell w ∩ α = ∅) ∧ ∀ w, w ∈ α ↔ Q.cell w ⊆ α

/-- The answer `α` is optimal in state `i` with respect to the alternative set `S` when the
relativized state entails `α` and no member of `S` it entails is stronger. -/
def IsOptimal (S : Set (Set W)) (α i : Set W) : Prop :=
  relativize Q i ⊆ α ∧ ∀ α' ∈ S, relativize Q i ⊆ α' → ¬ α' ⊂ α

/-- The consistent states in which `α` is optimal. -/
def optimalStates (S : Set (Set W)) (α : Set W) : Set (Set W) :=
  {i | i.Nonempty ∧ IsOptimal Q S α i}

/-- The maximally informed optimal states are those no other optimal state is stronger than. -/
def maximalStates (S : Set (Set W)) (α : Set W) : Set (Set W) :=
  {i | i ∈ optimalStates Q S α ∧ ∀ i' ∈ optimalStates Q S α, ¬ relativize Q i' ⊂ relativize Q i}

/-- An answer implicates what every maximally informed optimal state entails. -/
def Implicates (S : Set (Set W)) (α β : Set W) : Prop := ∀ i ∈ maximalStates Q S α, i ⊆ β

theorem maximalStates_subset (S : Set (Set W)) (α : Set W) :
    maximalStates Q S α ⊆ optimalStates Q S α :=
  fun _ h ↦ h.1

end Gricean

/-! ### Positive propositions -/

/-- A valuation, the set of atoms it makes true. -/
abbrev Valuation (Atom : Type*) := Finset Atom

/-- A proposition, the set of valuations making it true. -/
abbrev Proposition (Atom : Type*) := Set (Valuation Atom)

/-- A literal is an atom or its negation. -/
inductive Literal (Atom : Type*) where
  | pos (a : Atom)
  | neg (a : Atom)
  deriving DecidableEq, Repr

variable {Atom : Type*}

namespace Literal

/-- The atom of a literal. -/
def atom : Literal Atom → Atom
  | pos a => a
  | neg a => a

/-- The literal holds in a valuation. -/
def Holds : Literal Atom → Valuation Atom → Prop
  | pos a, V => a ∈ V
  | neg a, V => a ∉ V

end Literal

/-- The positive extension of `P` collects all supersets of its valuations. -/
def Pos (P : Proposition Atom) : Proposition Atom := {V | ∃ V' ∈ P, V' ⊆ V}

theorem subset_Pos (P : Proposition Atom) : P ⊆ Pos P := fun V hV ↦ ⟨V, hV, Finset.Subset.refl V⟩

theorem Pos_mono {P P' : Proposition Atom} (h : P ⊆ P') : Pos P ⊆ Pos P' :=
  fun _ ⟨V', hV', hle⟩ ↦ ⟨V', h hV', hle⟩

theorem Pos_setOf_minimal (P : Proposition Atom) : Pos {V | Minimal (· ∈ P) V} = Pos P := by
  refine Set.Subset.antisymm (Pos_mono fun _ h ↦ h.prop) fun V ⟨V', hV', hle⟩ ↦ ?_
  obtain ⟨t, hts, ht⟩ := exists_minimal_le_of_wellFoundedLT (· ∈ P) V' hV'
  exact ⟨t, ht, hts.trans hle⟩

theorem setOf_minimal_subset_of_Pos_eq {P i : Proposition Atom} (h : Pos i = P) :
    {V | Minimal (· ∈ P) V} ⊆ i := by
  intro V hV
  by_contra hVi
  obtain ⟨V', hV'i, hle⟩ : V ∈ Pos i := h ▸ hV.prop
  exact hV.not_prop_of_lt (Finset.ssubset_iff_subset_ne.2 ⟨hle, fun heq ↦ hVi (heq ▸ hV'i)⟩)
    (h ▸ subset_Pos i hV'i)

variable [DecidableEq Atom]

/-- The valuation identical to `V` except on the atom of `L`. -/
def flip (V : Valuation Atom) (L : Literal Atom) : Valuation Atom :=
  if h : L.atom ∈ V then V.erase L.atom else V.cons L.atom h

/-- `P` favors `L` when some valuation makes both true and flipping `L` makes `P` false. -/
def Favors (P : Proposition Atom) (L : Literal Atom) : Prop :=
  ∃ V ∈ P, L.Holds V ∧ flip V L ∉ P

/-- A positive proposition favors a positive literal and no negative one. -/
def IsPositive (P : Proposition Atom) : Prop :=
  (∃ a, Favors P (.pos a)) ∧ ∀ a, ¬ Favors P (.neg a)

/-- The positive propositions, the alternative set of a positive answer. -/
def positives : Set (Proposition Atom) := {P | IsPositive P}

theorem IsPositive.cons_mem {P : Proposition Atom} (hP : IsPositive P) {V : Valuation Atom}
    (hV : V ∈ P) {a : Atom} (ha : a ∉ V) : V.cons a ha ∈ P := by
  by_contra h
  refine hP.2 a ⟨V, hV, ha, ?_⟩
  simpa [flip, Literal.atom, ha] using h

theorem IsPositive.mem_of_subset {P : Proposition Atom} (hP : IsPositive P)
    {V' V : Valuation Atom} (hV' : V' ∈ P) (hle : V' ⊆ V) : V ∈ P := by
  generalize hn : V.card - V'.card = n
  induction n using Nat.strong_induction_on generalizing V' with
  | _ n ih =>
    rcases eq_or_ssubset_of_subset hle with rfl | hss
    · exact hV'
    · obtain ⟨a, haV, haV'⟩ := Finset.exists_of_ssubset hss
      have hsub : V'.cons a haV' ⊆ V := fun x hx ↦
        (Finset.mem_cons.1 hx).elim (fun h ↦ h ▸ haV) (fun h ↦ hle h)
      have hcard : V'.card < V.card := Finset.card_lt_card hss
      exact ih _ (by rw [Finset.card_cons]; omega) (hP.cons_mem hV' haV') hsub rfl

theorem IsPositive.nonempty {P : Proposition Atom} (hP : IsPositive P) : P.Nonempty :=
  let ⟨_, V, hV, _⟩ := hP.1
  ⟨V, hV⟩

theorem IsPositive.ne_univ {P : Proposition Atom} (hP : IsPositive P) : P ≠ Set.univ := by
  rintro rfl
  obtain ⟨_, _, -, -, h⟩ := hP.1
  exact h (Set.mem_univ _)

theorem isPositive_of_upward {P : Proposition Atom} (hne : P.Nonempty) (hnu : P ≠ Set.univ)
    (hup : ∀ V ∈ P, ∀ V', V ⊆ V' → V' ∈ P) : IsPositive P := by
  refine ⟨?_, fun a ⟨V, hV, haV, hflip⟩ ↦ ?_⟩
  · obtain ⟨V₀, hV₀⟩ := hne
    obtain ⟨V, -, hV⟩ := exists_minimal_le_of_wellFoundedLT (· ∈ P) V₀ hV₀
    have hVP := hV.prop
    have hVne : V.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      rintro rfl
      exact hnu (Set.eq_univ_of_forall fun V' ↦ hup ∅ hVP V' (Finset.empty_subset _))
    obtain ⟨a, ha⟩ := hVne
    refine ⟨a, V, hVP, ha, fun hmem ↦ hV.not_prop_of_lt (Finset.erase_ssubset ha) ?_⟩
    simpa [flip, Literal.atom, ha] using hmem
  · have haV' : a ∉ V := haV
    refine hflip ?_
    simpa [flip, Literal.atom, haV'] using
      hup V hV (V.cons a haV') fun x hx ↦ Finset.mem_cons.2 (Or.inr hx)

theorem Pos_of_isPositive {P : Proposition Atom} (hP : IsPositive P) : Pos P = P :=
  Set.Subset.antisymm (fun _ ⟨_, hV', hle⟩ ↦ hP.mem_of_subset hV' hle) (subset_Pos P)

theorem Pos_isPositive {i : Proposition Atom} (hi : i.Nonempty) (hnu : Pos i ≠ Set.univ) :
    IsPositive (Pos i) :=
  isPositive_of_upward (hi.mono (subset_Pos i)) hnu
    fun _ ⟨V', hV', hle⟩ _ hle' ↦ ⟨V', hV', hle.trans hle'⟩

/-! ### The reduction and the theorem -/

theorem isOptimal_iff {P i : Proposition Atom} (hP : IsPositive P) (hi : i.Nonempty) :
    IsOptimal ⊥ positives P i ↔ Pos i = P := by
  simp only [IsOptimal, relativize_bot, positives, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hiP, hopt⟩
    have hsub : Pos i ⊆ P := fun _ ⟨V', hV', hle⟩ ↦ hP.mem_of_subset (hiP hV') hle
    by_contra hne
    have hnu : Pos i ≠ Set.univ := fun h ↦ hP.ne_univ (Set.eq_univ_of_univ_subset (h ▸ hsub))
    exact hopt (Pos i) (Pos_isPositive hi hnu) (subset_Pos i)
      (Set.ssubset_iff_subset_ne.2 ⟨hsub, hne⟩)
  · rintro rfl
    exact ⟨subset_Pos i, fun α' hα' hiα' hss ↦
      hss.2 ((Pos_mono hiα').trans (Pos_of_isPositive hα').subset)⟩

theorem optimalStates_eq {P : Proposition Atom} (hP : IsPositive P) :
    optimalStates ⊥ positives P = {i | i.Nonempty ∧ Pos i = P} :=
  Set.ext fun _ ↦ and_congr_right (isOptimal_iff hP)

theorem maximalStates_eq {P : Proposition Atom} (hP : IsPositive P) :
    maximalStates ⊥ positives P = {{V | Minimal (· ∈ P) V}} := by
  have hI := optimalStates_eq hP
  have hExh : {V | Minimal (· ∈ P) V} ∈ optimalStates ⊥ positives P := by
    rw [hI]
    exact ⟨exists_minimal_of_wellFoundedLT _ hP.nonempty,
      by rw [Pos_setOf_minimal, Pos_of_isPositive hP]⟩
  have hent : ∀ i ∈ optimalStates ⊥ positives P, {V | Minimal (· ∈ P) V} ⊆ i := fun i hi ↦ by
    rw [hI] at hi
    exact setOf_minimal_subset_of_Pos_eq hi.2
  ext i
  simp only [maximalStates, Set.mem_ofPred_eq, Set.mem_singleton_iff, relativize_bot]
  constructor
  · rintro ⟨hi, hmax⟩
    by_contra hne
    exact hmax _ hExh (Set.ssubset_iff_subset_ne.2 ⟨hent i hi, fun h ↦ hne h.symm⟩)
  · rintro rfl
    exact ⟨hExh, fun i' hi' hss ↦ hss.2 (hent i' hi')⟩

theorem implicates_setOf_minimal {P : Proposition Atom} (hP : IsPositive P) :
    Implicates ⊥ positives P {V | Minimal (· ∈ P) V} := by
  intro i hi
  rw [maximalStates_eq hP, Set.mem_singleton_iff] at hi
  exact hi.subset

/-! ### Disjunction -/

/-- The proposition that `a` holds. -/
def atomProp (a : Atom) : Proposition Atom := {V | a ∈ V}

/-- *A or B*. -/
def orProp (a b : Atom) : Proposition Atom := {V | a ∈ V ∨ b ∈ V}

/-- *Only A or only B*. -/
def exclOr (a b : Atom) : Proposition Atom := {V | V = {a} ∨ V = {b}}

theorem orProp_isPositive (a b : Atom) : IsPositive (orProp a b) := by
  refine isPositive_of_upward ⟨{a}, Or.inl (Finset.mem_singleton_self a)⟩ ?_ ?_
  · intro h
    have : (∅ : Valuation Atom) ∈ orProp a b := by rw [h]; exact Set.mem_univ _
    rcases this with h' | h' <;> exact Finset.notMem_empty _ h'
  · rintro _ hV _ hle
    rcases hV with h | h
    exacts [Or.inl (hle h), Or.inr (hle h)]

theorem setOf_minimal_orProp (a b : Atom) : {V | Minimal (· ∈ orProp a b) V} = exclOr a b := by
  ext V
  simp only [orProp, exclOr, Set.mem_ofPred_eq, minimal_iff_forall_lt]
  constructor
  · rintro ⟨hV, hmin⟩
    have single : ∀ c ∈ V, (∀ x ∈ V, x = c) → V = {c} := fun c hc h ↦
      Finset.eq_singleton_iff_unique_mem.2 ⟨hc, h⟩
    rcases hV with ha | hb
    · refine Or.inl (single a ha fun x hx ↦ ?_)
      by_contra hne
      exact hmin (Finset.erase_ssubset hx) (Or.inl (Finset.mem_erase.2 ⟨fun h ↦ hne h.symm, ha⟩))
    · refine Or.inr (single b hb fun x hx ↦ ?_)
      by_contra hne
      exact hmin (Finset.erase_ssubset hx) (Or.inr (Finset.mem_erase.2 ⟨fun h ↦ hne h.symm, hb⟩))
  · rintro (rfl | rfl)
    · refine ⟨Or.inl (Finset.mem_singleton_self a), fun V' hss hV' ↦ ?_⟩
      rw [Finset.eq_empty_of_ssubset_singleton hss] at hV'
      exact hV'.elim (Finset.notMem_empty a) (Finset.notMem_empty b)
    · refine ⟨Or.inr (Finset.mem_singleton_self b), fun V' hss hV' ↦ ?_⟩
      rw [Finset.eq_empty_of_ssubset_singleton hss] at hV'
      exact hV'.elim (Finset.notMem_empty a) (Finset.notMem_empty b)

theorem orProp_implicates_exclOr (a b : Atom) :
    Implicates ⊥ positives (orProp a b) (exclOr a b) :=
  setOf_minimal_orProp a b ▸ implicates_setOf_minimal (orProp_isPositive a b)

theorem no_unwanted_negation {a b : Atom} (hab : a ≠ b) {i : Proposition Atom}
    (hi : i ∈ optimalStates ⊥ positives (orProp a b)) :
    ¬ i ⊆ atomProp a ∧ ¬ i ⊆ (atomProp a)ᶜ := by
  rw [optimalStates_eq (orProp_isPositive a b)] at hi
  obtain ⟨-, hPos⟩ := hi
  have hb : ({b} : Valuation Atom) ∈ orProp a b := Or.inr (Finset.mem_singleton_self b)
  have ha : ({a} : Valuation Atom) ∈ orProp a b := Or.inl (Finset.mem_singleton_self a)
  constructor
  · intro h
    have hsub : Pos i ⊆ atomProp a := fun _ ⟨_, hV', hle⟩ ↦ hle (h hV')
    rw [hPos] at hsub
    exact hab (Finset.mem_singleton.1 (hsub hb))
  · intro h
    have hsub : Pos i ⊆ atomProp b := by
      rintro _ ⟨V', hV', hle⟩
      have hV'or : V' ∈ orProp a b := hPos ▸ subset_Pos i hV'
      rcases hV'or with ha' | hb'
      · exact absurd ha' (h hV')
      · exact hle hb'
    rw [hPos] at hsub
    exact hab (Finset.mem_singleton.1 (hsub ha)).symm

end Spector2007
