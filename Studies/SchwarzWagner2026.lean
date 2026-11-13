module

public import Linglib.Data.Examples.Readers
public import Linglib.Data.Examples.SchwarzWagner2026
public import Linglib.Pragmatics.NeoGricean.Basic
public import Linglib.Semantics.Composition.Constituency
public import Linglib.Semantics.Composition.Rules
public import Linglib.Core.Data.RoseTree.Licensed
public import Linglib.Semantics.Presupposition.Strengthening
public import Linglib.Semantics.Quantification.Basic
public import Studies.Fox2007
public import Studies.Katzir2007
public import Studies.TrinhHaida2015

/-!
# Schwarz and Wagner (2026): Resolving Symmetry without Constraining Alternatives

Katzir and Fox let an implicature negate only alternatives no more complex than the assertion.
Schwarz and Wagner let it negate anything and constrain the output: a strengthening is [blocked
when it entails a simplex meaning stronger than the assertion](##blocked_iff), so the assertion
must be [a strongest simplex meaning it entails](##minimalFor_iff_not_blocked). The two constraints
are [the conjuncts of Sauerland's secondary implicature](##isSecondaryImplicature_iff_not_blocked),
and blocking is [Katzir's own principle](##blocked_iff_katzir_blocked) read at the strengthened
meaning. The examples are corners of a square of opposition, differing in which corners are lexical:
[blocking misjudges only (76b)](##blocked_misjudges_iff), [the filter with a stalemate four
rows](##filter_misjudges_iff). Blocking also [rules out free choice](##blocked_freeChoice), which
the paper does not discuss.

## Implementation notes

* The paper's `Excl` is free, so it [carries no information](##exh_compl_singleton): every
  satisfiable strengthening is one, and what the constraint reads is the output `s` and the set `F`
  of simplex meanings. Trees enter only through `F` (`simplex`). The paper's (5) negates all of
  `Excl`, `exh` only what the assertion does not entail; they differ only on contradictions.
* `Blocked` is a `lowerClosure` rather than `NeoGricean.primaryImplicatures`, its complement,
  because the paper declines to choose between Gricean and grammatical strengthening.
* One grammar covers the examples. Its clauses compose by Functional Application in the reader of
  worlds, to the hub's determiners at a restrictor and a predicate's extension in each world, the
  square `sqAt`. *Permitted*, *required* and *optional* are those determiners over the deontic
  alternatives, parallel to *some*, *all* and *not all* on the paper's own account of (52). A
  `Case` is a prejacent with its lexicon, and each lexicon lists only the words the paper's
  discussion of that example uses.
* `optional` is the O corner, [not strictly symmetric with *required*](##not_isSymmetric_O), as the
  paper argues from (54) and [(55)](##compl_O_eq_A). On the `I \ A` of [swanson-2010], [both
  readings of (52) are blocked](##blocked_of_sdiff_mem) and [both continuations in (54) are
  contradictory](##sdiff_inf_eq_bot), where at the O corner [only (54b) is](##O_inf_eq_bot_iff).
  Katzir's (21), the target of [swanson-2010], survives (52) on this entry, though the paper groups
  it with CF: it reads only strictly stronger alternatives, and [`A` is the only such
  corner](##lt_I_iff). Only [the filter with a stalemate](##filter_misjudges_iff) stays refuted.
* Complexity is the paper's plain notion, with lexical items as the source: blocking needs none of
  Katzir's contextual sources, and this one bounds size (`atMostAsComplex.numNodes_le`).
* What is not simplex comes from a table of what each category can denote
  (`meanings_mem_of_licensed`), not from listing the trees.

## TODO

The contextual cases (23), (58), (59), the disjunction (29), the embedding (79), the question
effects (61)–(65) and the triples of footnote 17 are not rows; recoverability is not modelled.
[bar-lev-bassi-trinh-2025] derive blocking's effects from fatal competition and partition by
exhaustification against the 2024 manuscript's equivalence version, and that comparison needs a
theory of questions here.

## References

* [schwarz-wagner-2026]
* [katzir-2007]
* [fox-katzir-2011]
* [sauerland-2004]
* [fox-2007]
* [trinh-haida-2015]
* [breheny-et-al-2018]
* [swanson-2010]
* [bar-lev-bassi-trinh-2025]
-/

@[expose] public section

namespace SchwarzWagner2026

open Set Exhaustification Alternatives NeoGricean Aristotelian PhraseStructure Tree

/-! ### The blocking constraint -/

section Order

variable {α : Type*} [Preorder α] {F : Set α} {s p : α}

/-- The blocking constraint (19), (67): the strengthening `s` of `p` is blocked by the simplex
meanings `F` when it lies below one strictly stronger than `p`. -/
def Blocked (F : Set α) (s p : α) : Prop := s ∈ lowerClosure (F ∩ Iio p)

theorem blocked_iff : Blocked F s p ↔ ∃ q ∈ F, s ≤ q ∧ q < p := by
  simp only [Blocked, mem_lowerClosure, mem_inter_iff, mem_Iio]
  exact exists_congr fun q ↦ ⟨fun ⟨⟨h₁, h₂⟩, h₃⟩ ↦ ⟨h₁, h₃, h₂⟩, fun ⟨h₁, h₃, h₂⟩ ↦ ⟨⟨h₁, h₂⟩, h₃⟩⟩

-- Section 1.3
end Order

/-! ### Blocking and its precursors -/

section Sets

variable {W : Type*} {F : Set (Set W)} {p s a b : Set W}

/-- A strengthening is unblocked when the assertion is a strongest simplex meaning it entails: the
"maximize basic meaning" of Section 1.3 is Maximize Presupposition read at the strengthened
meaning. -/
theorem minimalFor_iff_not_blocked {S : Type*} {alts : S → Set S} {content : S → Set W} {φ : S} :
    MinimalFor (· ∈ insert φ (alts φ) ∩ content ⁻¹' Ici s) content φ ↔
      s ⊆ content φ ∧ ¬ Blocked (content '' alts φ) s (content φ) := by
  rw [Presupposition.minimalFor_preimage_Ici_iff, blocked_iff]
  simp only [mem_image, not_exists, not_and, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  exact and_congr_right fun _ ↦ forall₂_congr fun _ _ ↦
    ⟨fun h hs hss ↦ h hss hs, fun h hss hs ↦ h hs hss⟩

theorem exh_compl_singleton (hs : s.Nonempty) (h : s ⊆ p) : exh {sᶜ} p = s := by
  have hnot : ¬ p ⊆ sᶜ := fun hp ↦ let ⟨w, hw⟩ := hs; hp (h hw) hw
  rw [exh_singleton_of_not_subset hnot, sdiff_compl, inter_eq_right.2 h]

theorem not_blocked_iff_mem_primaryImplicatures :
    ¬ Blocked F s p ↔ s ∈ primaryImplicatures F p := by
  rw [blocked_iff, mem_primaryImplicatures]
  push Not
  exact forall₂_congr fun q _ ↦ ⟨fun h hq hs ↦ h hs hq, fun h hs hq ↦ h hq hs⟩

/-- The complexity filter (66) and blocking (67) are the conjuncts of Sauerland's secondary
implicature (43), for an alternative stronger than the assertion: the proposal keeps the second and
drops the first. -/
theorem isSecondaryImplicature_iff_not_blocked :
    IsSecondaryImplicature F p a ↔ a ∈ F ∧ a ⊂ p ∧ ¬ Blocked F (p \ a) p := by
  rw [not_blocked_iff_mem_primaryImplicatures, isSecondaryImplicature_iff, mem_primaryImplicatures]

-- Section 4, (68)
theorem blocked_sdiff_iff : Blocked F (p \ a) p ↔ ∃ q ∈ F, q ⊂ p ∧ p ⊆ a ∪ q := by
  simp only [blocked_iff, sdiff_subset_iff]
  exact exists_congr fun q ↦ and_congr_right fun _ ↦ and_comm

theorem IsSymmetric.blocked_sdiff_iff (h : IsSymmetric p a b) :
    Blocked F (p \ a) p ↔ (F ∩ Ico b p).Nonempty := by
  rw [Blocked, h.sdiff_eq, mem_lowerClosure]
  exact ⟨fun ⟨q, ⟨hq, hp⟩, hb⟩ ↦ ⟨q, hq, hb, hp⟩, fun ⟨q, hq, hb, hp⟩ ↦ ⟨q, ⟨hq, hp⟩, hb⟩⟩

-- Section 4.1: with both partners simplex, strict symmetry blocks both strengthenings.
theorem IsSymmetric.blocked_sdiff (h : IsSymmetric p a b) (hb : b ∈ F) (ha : a.Nonempty) :
    Blocked F (p \ a) p :=
  (IsSymmetric.blocked_sdiff_iff h).2 ⟨b, hb, le_rfl, h.symm.ssubset_left ha⟩

-- Section 4.1
theorem exists_isSymmetric_blocked : ∃ (F : Set (Set (Fin 4))) (p a b : Set (Fin 4)),
    IsSymmetric p a b ∧ a ∈ F ∧ b ∉ F ∧ Blocked F (p \ a) p ∧ Blocked F (p \ b) p := by
  refine ⟨{{0, 3}, {1, 2, 3}, univ}, univ, {0, 3}, {1, 2}, ⟨?_, ?_⟩, by simp, ?_, ?_, ?_⟩
  · ext i; fin_cases i <;> simp
  · rw [Set.disjoint_left]; intro i; fin_cases i <;> simp
  · intro h
    simp only [mem_insert_iff, mem_singleton_iff] at h
    rcases h with h | h | h
    · have := (Set.ext_iff.1 h 0).2; simp at this
    · have := (Set.ext_iff.1 h 3).2; simp at this
    · have := (Set.ext_iff.1 h 0).2; simp at this
  · refine blocked_iff.2 ⟨{1, 2, 3}, by simp, ?_, subset_univ _, fun h ↦ ?_⟩
    · intro i; fin_cases i <;> simp
    · have := h (mem_univ (0 : Fin 4)); simp at this
  · refine blocked_iff.2 ⟨{0, 3}, by simp, ?_, subset_univ _, fun h ↦ ?_⟩
    · intro i; fin_cases i <;> simp
    · have := h (mem_univ (1 : Fin 4)); simp at this

-- (14)
theorem exhIE_eq_self_of_mem {A G : Set (Set W)} {S : Set W} (hA : TrinhHaida2015.IsDomain G S A)
    (hfin : A.Finite) (h : exhIE A S ∈ G) : exhIE A S = S := by
  have hIE : {a | IsInnocentlyExcludable A S a}.Finite := hfin.subset fun _ ha ↦ ha.1
  have hsup : ⋃₀ {a | IsInnocentlyExcludable A S a} ∈ BooleanSubalgebra.closure A := by
    refine hIE.induction_on_subset _ (by rw [sUnion_empty]; exact BooleanSubalgebra.bot_mem)
      fun {a X} ha _ _ ih ↦ ?_
    rw [sUnion_insert]
    exact BooleanSubalgebra.sup_mem (BooleanSubalgebra.subset_closure ha.1) ih
  have heq : exhIE A S = S \ ⋃₀ {a | IsInnocentlyExcludable A S a} := by
    ext w
    simp only [mem_exhIE_iff, mem_sdiff, mem_sUnion, mem_ofPred_eq, not_exists, not_and]
  have hcl : exhIE A S ∈ BooleanSubalgebra.closure A :=
    heq ▸ BooleanSubalgebra.sdiff_mem (BooleanSubalgebra.subset_closure hA.self_mem) hsup
  refine (exhIE_subset A S).eq_of_not_ssubset fun hlt ↦ ?_
  exact exhIE_notMem_lowerClosure hfin (mem_lowerClosure.2 ⟨_, ⟨hA.closed _ h hcl, hlt⟩, le_rfl⟩)

end Sets

section Katzir

open Katzir2007 in
/-- Blocking is Katzir's conversational principle (21) with weak assertability read at the
strengthened meaning. -/
theorem blocked_iff_katzir_blocked {M : Type*} {m : Tree Cat Katzir2007.Word → Set M}
    {t : Tree Cat Katzir2007.Word} {s : Set M} :
    Blocked (m '' structuralAlternatives lexicon t) s (m t) ↔
      Katzir2007.Blocked (fun t' ↦ s ⊆ m t') m t := by
  simp only [SchwarzWagner2026.blocked_iff, Katzir2007.Blocked, assertableAlts, mem_image]
  constructor
  · rintro ⟨_, ⟨t', ht', rfl⟩, hs, hlt⟩
    exact ⟨t', ⟨ht', hs⟩, hlt⟩
  · rintro ⟨t', ⟨ht', hs⟩, hlt⟩
    exact ⟨_, ⟨t', ht', rfl⟩, hs, hlt⟩

end Katzir

/-! ### Free choice -/

section FreeChoice

variable {W α : Type*} [Lattice α] {O : α → Set W} {x y : α}

open Fox2007

/-- Blocking rules out free choice, however derived, since it reads only the output: *You may have
x* is simpler than *You may have x or y*, strictly stronger, and entailed by the free-choice
reading. One round of innocent exclusion is never blocked (`exhIE_notMem_lowerClosure`); the second
round of [fox-2007]'s recursion is. -/
theorem blocked_freeChoice {F : Set (Set W)} (hF : O x ∈ F) (hO : Monotone O)
    (hab : O (x ⊔ y) ⊆ O x ∪ O y) (hx : (O x \ O y).Nonempty) (hy : (O y \ O x).Nonempty)
    (hfc : ((O x ∩ O y) \ O (x ⊓ y)).Nonempty) :
    Blocked F (exhIter (sauerlandAlt O x y) 2 (O (x ⊔ y))) (O (x ⊔ y)) := by
  rw [free_choice hO hab hx hy hfc]
  obtain ⟨w, hwy, hwx⟩ := hy
  exact blocked_iff.2 ⟨O x, hF, fun v hv ↦ hv.1.1, hO le_sup_left,
    fun h ↦ hwx (h (hO le_sup_right hwy))⟩

-- (14), (16)
theorem freeChoice_notMem (hO : Monotone O) (hx : (O x \ O y).Nonempty)
    (hy : (O y \ O x).Nonempty) (hfc : ((O x ∩ O y) \ O (x ⊓ y)).Nonempty) :
    (O x ∩ O y) \ O (x ⊓ y) ∉ sauerlandAlt O x y := by
  obtain ⟨u, hux, huy⟩ := hx
  obtain ⟨v, hvy, hvx⟩ := hy
  obtain ⟨z, hz⟩ := hfc
  simp only [sauerlandAlt, mem_insert_iff, mem_singleton_iff]
  rintro (h | h | h | h)
  · have : u ∈ (O x ∩ O y) \ O (x ⊓ y) := by rw [h]; exact hO le_sup_left hux
    exact huy this.1.2
  · have : u ∈ (O x ∩ O y) \ O (x ⊓ y) := by rw [h]; exact hux
    exact huy this.1.2
  · have : v ∈ (O x ∩ O y) \ O (x ⊓ y) := by rw [h]; exact hvy
    exact hvx this.1.1
  · exact hz.2 (h ▸ hz)

end FreeChoice

/-! ### Blocking on a square of opposition -/

section Square

variable {α : Type*} [BooleanAlgebra α] {sq : Square α} {F : Set α} {s : α}

theorem lt_I_iff (h : SquareRelations sq) (hne : ∀ t, sq.triangle t ≠ ⊥) {q : α}
    (hq : q ∈ ({sq.A, sq.E, sq.I, sq.O} : Set α)) : q < sq.I ↔ q = sq.A := by
  have hE : ¬ sq.E ≤ sq.I := fun hle ↦ hne .none (h.contradEI.disjoint.eq_bot_of_le hle)
  have hIA : ¬ sq.I ≤ sq.A := fun hle ↦ hne .someNotAll <| le_bot_iff.1 <|
    (inf_le_inf_right _ hle).trans h.contradAO.disjoint.le_bot
  simp only [mem_insert_iff, mem_singleton_iff] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact ⟨fun _ ↦ rfl, fun _ ↦ h.subalternAI.lt_of_not_ge hIA⟩
  · exact ⟨fun hlt ↦ absurd hlt.le hE, fun heq ↦ absurd (heq.le.trans h.subalternAI) hE⟩
  · exact ⟨fun hlt ↦ absurd hlt (lt_irrefl _), fun heq ↦ absurd heq.le hIA⟩
  · exact ⟨fun hlt ↦ absurd (h.subalternEO.trans hlt.le) hE,
      fun heq ↦ (hE ((h.subalternEO.trans heq.le).trans h.subalternAI)).elim⟩

theorem blocked_I_iff (h : SquareRelations sq) (hne : ∀ t, sq.triangle t ≠ ⊥)
    (hF : F ⊆ {sq.A, sq.E, sq.I, sq.O}) : Blocked F s sq.I ↔ sq.A ∈ F ∧ s ≤ sq.A := by
  rw [blocked_iff]
  constructor
  · rintro ⟨q, hq, hsq, hlt⟩
    obtain rfl := (lt_I_iff h hne (hF hq)).1 hlt
    exact ⟨hq, hsq⟩
  · rintro ⟨hA, hs⟩
    exact ⟨sq.A, hA, hs, (lt_I_iff h hne (by simp)).2 rfl⟩

theorem blocked_I_sdiff_O_iff (h : SquareRelations sq) (hne : ∀ t, sq.triangle t ≠ ⊥)
    (hF : F ⊆ {sq.A, sq.E, sq.I, sq.O}) : Blocked F (sq.I \ sq.O) sq.I ↔ sq.A ∈ F := by
  rw [blocked_I_iff h hne hF, h.I_sdiff_O]
  simp

theorem not_blocked_I_sdiff_A (h : SquareRelations sq) (hne : ∀ t, sq.triangle t ≠ ⊥)
    (hF : F ⊆ {sq.A, sq.E, sq.I, sq.O}) : ¬ Blocked F (sq.I \ sq.A) sq.I := by
  rw [blocked_I_iff h hne hF, h.I_sdiff_A]
  rintro ⟨-, hle⟩
  exact hne .someNotAll <| le_bot_iff.1 <|
    (le_inf hle inf_le_right).trans h.contradAO.disjoint.le_bot

theorem exhIE_I_eq_self {W : Type*} {sq : Square (Set W)} (h : SquareRelations sq)
    (hne : ∀ t, sq.triangle t ≠ ⊥) : exhIE {sq.I, sq.A, sq.O} sq.I = sq.I := by
  have hcov : sq.I ⊆ sq.A ∪ sq.O := fun w _ ↦
    show w ∈ sq.A ⊔ sq.O from h.contradAO.sup_eq_top ▸ mem_univ w
  refine exhIE_eq_self_of_subset_union hcov ?_ ?_
  · have heq : sq.I \ sq.A = sq.I ⊓ sq.O := h.I_sdiff_A
    exact heq ▸ nonempty_iff_ne_empty.2 (show sq.I ⊓ sq.O ≠ ∅ from hne .someNotAll)
  · have heq : sq.I \ sq.O = sq.A := h.I_sdiff_O
    exact heq ▸ nonempty_iff_ne_empty.2 (show sq.A ≠ ∅ from hne .all)

-- Section 2.5: if *optional* is `I \ A`, blocking rules out both readings of (52).
theorem blocked_of_sdiff_mem {W : Type*} {sq : Square (Set W)} {F : Set (Set W)}
    (h : SquareRelations sq) (hne : ∀ t, sq.triangle t ≠ ⊥) (hA : sq.A ∈ F)
    (hO : sq.I \ sq.A ∈ F) : Blocked F (sq.I \ sq.A) sq.I ∧ Blocked F sq.A sq.I := by
  have hs : IsSymmetric sq.I sq.A (sq.I \ sq.A) := isSymmetric_sdiff h.subalternAI
  refine ⟨IsSymmetric.blocked_sdiff hs hO (nonempty_iff_ne_empty.2 (hne .all)), ?_⟩
  have hO' : (sq.I \ sq.A).Nonempty :=
    h.I_sdiff_A ▸ nonempty_iff_ne_empty.2 (show sq.I ⊓ sq.O ≠ ∅ from hne .someNotAll)
  simpa only [hs.symm.sdiff_eq] using IsSymmetric.blocked_sdiff hs.symm hA hO'

-- Section 4.1: at the O corner the partners of (52) are no longer strictly symmetric.
theorem not_isSymmetric_O {W : Type*} {sq : Square (Set W)} (h : SquareRelations sq)
    (hne : ∀ t, sq.triangle t ≠ ⊥) : ¬ IsSymmetric sq.I sq.A sq.O := fun hs ↦
  hne .none (h.contradEI.disjoint.eq_bot_of_le (h.subalternEO.trans hs.subset_right))

-- (54): at the O corner only (54b) is contradictory.
theorem O_inf_eq_bot_iff (h : SquareRelations sq) (hne : ∀ t, sq.triangle t ≠ ⊥) :
    (sq.O ⊓ sq.E = ⊥ ↔ Examples.ex_54a.judgment = .unacceptable) ∧
      (sq.O ⊓ sq.A = ⊥ ↔ Examples.ex_54b.judgment = .unacceptable) :=
  ⟨iff_of_false (fun hE ↦ hne .none ((inf_eq_right.2 h.subalternEO).symm.trans hE)) (by decide),
    iff_of_true h.contradAO.disjoint.symm.eq_bot rfl⟩

-- (54): at `I \ A` both are, where the paper finds a contrast.
theorem sdiff_inf_eq_bot (h : SquareRelations sq) :
    (sq.I \ sq.A) ⊓ sq.E = ⊥ ∧ (sq.I \ sq.A) ⊓ sq.A = ⊥ :=
  ⟨(h.contradEI.disjoint.symm.mono_left sdiff_le).eq_bot, disjoint_sdiff_self_left.eq_bot⟩

-- (55): negating the O corner gives *required*, the preferred reading; negating `I \ A` does not.
theorem compl_O_eq_A (h : SquareRelations sq) (hne : ∀ t, sq.triangle t ≠ ⊥) :
    sq.Oᶜ = sq.A ∧ ¬ (sq.I \ sq.A)ᶜ ≤ sq.A :=
  ⟨h.contradAO.symm.compl_eq, fun hle ↦ hne .none <| h.contraryAE.symm.eq_bot_of_le <|
    (le_compl_iff_disjoint_right.2 (h.contradEI.disjoint.mono_right sdiff_le)).trans hle⟩

end Square

/-! ### The examples -/

/-- The lexical items of the examples: a determiner per corner of the square (*some*, *all* or
*permitted*, *required*, *optional*), a noun, a predicate and its antonym, negation. -/
inductive Word
  | some_ | all_ | nall | noun | pred | antonym | not_
  deriving DecidableEq, Repr

/-- The category of a word. -/
def catOf : Word → Cat
  | .some_ | .all_ | .nall => .Det
  | .noun => .N
  | .pred | .antonym => .V
  | .not_ => .Neg

/-- A clause is a noun phrase and a verb phrase; a noun phrase, labelled by its noun, is a
determiner and a noun; a verb phrase is an optional negation and a verb phrase. -/
def pat : Cat → List Cat
  | .S => [.N, .V]
  | .N => [.Det, .N]
  | .V => [.Neg, .V]
  | _ => []

/-- The local trees of the grammar over the words `Ws`, with daughters possibly deleted. -/
def Licit (Ws : Finset Word) : Label Cat Word → List (Label Cat Word) → Prop
  | .terminal c w, ks => w ∈ Ws ∧ c = catOf w ∧ ks = []
  | .phrase c _, ks => (ks.map Label.cat).Sublist (pat c)
  | _, _ => False

instance (Ws : Finset Word) : ∀ l ks, Decidable (Licit Ws l ks)
  | .terminal _ _, _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _))
  | .phrase _ _, _ => inferInstanceAs (Decidable (List.Sublist _ _))
  | .trace _ _, _ => isFalse id
  | .bind _ _, _ => isFalse id

/-- A sentence with a determiner, the noun, and a predicate phrase. -/
abbrev sentence (d : Word) (v : Tree Cat Word) : Tree Cat Word :=
  .node .S [.node .N [.terminal .Det d, .terminal .N .noun], v]

/-- The words the base lexicon always has: the assertion's own. -/
def base : Finset (Tree Cat Word) := {.terminal .Det .some_, .terminal .N .noun, .terminal .V .pred}

/-- The examples, by what the language lexicalizes beyond the assertion. -/
inductive Case
  /-- (1) *Some players responded*: the A corner. -/
  | bare
  /-- (33) *Some players have not responded*: the A corner, the assertion holding a negation. -/
  | negated
  /-- (42) *Some players were inside*: the A corner and an antonym, (46). -/
  | antonym
  /-- (52) *Going to confession is permitted*: the A and O corners, *required* and *optional*. -/
  | lexicalized
  /-- (76) *John-wa ki-te yoi*: no other corner; necessity is complex, (77). -/
  | minimal
  deriving DecidableEq, Repr

/-- The lexicon of each example. -/
def lex : Case → Finset (Tree Cat Word)
  | .bare | .negated => insert (.terminal .Det .all_) base
  | .antonym => insert (.terminal .Det .all_) (insert (.terminal .V .antonym) base)
  | .lexicalized => insert (.terminal .Det .all_) (insert (.terminal .Det .nall) base)
  | .minimal => base

/-- The assertion of each example. -/
def prejacent : Case → Tree Cat Word
  | .negated => sentence .some_ (.node .V [.terminal .Neg .not_, .terminal .V .pred])
  | _ => sentence .some_ (.terminal .V .pred)

section Interpretation

open Quantifier Interpreter

variable {E W : Type} (A : Set E) (X : W → Set E)

/-- *Not every*, the O corner of the determiners' square. -/
abbrev nallDet : Det E := (Det.every : Det E)ᶜ

/-- The domain of the one basic type, the individuals. -/
abbrev Dom (E : Type) : Unit → Type := fun _ ↦ E

/-- The type of predicates. -/
abbrev et : Ty Unit := .base () ⇒ .t

/-- The type of quantifiers. -/
abbrev ett : Ty Unit := et ⇒ .t

/-- The type of determiners. -/
abbrev det : Ty Unit := et ⇒ ett

/-- A typed meaning relative to a world. -/
abbrev Denotation (E W : Type) : Type := Σ a : Ty Unit, W → a.Dom (Dom E)

/-- Word meanings relative to a world: a predicate's extension varies with the world, and the
determiners are the hub's. -/
def denotes : Word → Option (Denotation E W)
  | .some_ => some ⟨det, fun _ ↦ Det.some⟩
  | .all_ => some ⟨det, fun _ ↦ Det.every⟩
  | .nall => some ⟨det, fun _ ↦ nallDet⟩
  | .noun => some ⟨et, fun _ ↦ A⟩
  | .pred => some ⟨et, X⟩
  | .antonym => some ⟨et, fun w ↦ ((X w)ᶜ : Set E)⟩
  | .not_ => some ⟨et ⇒ et, fun _ (P : Set E) ↦ (Pᶜ : Set E)⟩

/-- The meanings of a tree, by Functional Application at each world. -/
def meanings (t : Tree Cat Word) : List (Denotation E W) :=
  t.values (typeDriven application) ((inferInstance : application.Structure (Ty.Dom (Dom E))).pi W)
    (W := fun a ↦ W → a.Dom (Dom E)) id fun
    | .inl w => (denotes A X w).toList
    | .inr _ => []

/-- The paper's simplex meanings: those of the sentences no more complex than the assertion, in its
plain sense of deleting constituents and replacing them by lexical items. -/
def simplex (c : Case) : Set (Set W) :=
  {q | ∃ ψ, atMostAsComplex ↑(lex c) ψ (prejacent c) ∧ (⟨.t, q⟩ : Denotation E W) ∈ meanings A X ψ}

/-- The determiners' square at the restrictor, at the predicate's extension in each world. -/
def sqAt : Square (Set W) where
  A := {w | Det.every A (X w)}
  E := {w | Det.no A (X w)}
  I := {w | Det.some A (X w)}
  O := {w | nallDet A (X w)}

variable {A X}

theorem sqAt_relations (hA : A.Nonempty) : SquareRelations (sqAt A X) :=
  (Det.square_relations hA).map (F := BoundedLatticeHom (Quantifier E) (Set W))
    (CompleteLatticeHom.setPreimage X).toBoundedLatticeHom

-- Two members of the restrictor make the square nondegenerate over the possible extensions.
example {a b : E} (ha : a ∈ A) (hb : b ∈ A) (hab : a ≠ b) (t : Triangle) :
    (sqAt A id).triangle t ≠ ⊥ := by
  have key {s : Set (Set E)} {x : Set E} (hx : x ∈ s) : s ≠ ⊥ := fun h ↦ (h ▸ hx : x ∈ (⊥ : Set _))
  cases t
  · exact key (x := ∅) fun _ _ h ↦ h
  · exact key (x := {a}) ⟨⟨a, ha, rfl⟩, fun h ↦ hab (h hb).symm⟩
  · exact key (x := univ) fun _ _ ↦ mem_univ _

/-- The square of the assertion: the assertion is its `I` corner. -/
def squareOf (sq : Square (Set W)) : Case → Square (Set W)
  | .negated => sq.inner
  | _ => sq

/-- What each category can denote, for determiners `Ds`, predicates `Fs`, and negation if `N`. -/
def Table (A : Set E) (N : Prop) (Fs : Set (W → E → Prop)) (Ds : Set (Det E)) :
    Cat → Set (Denotation E W)
  | .S => {d | d.1 ≠ .t ∨ ∃ D ∈ Ds, ∃ f ∈ Fs, d = ⟨.t, fun w ↦ D A (f w)⟩}
  | .N => {d | (∃ D ∈ Ds, d = ⟨det, fun _ ↦ D⟩) ∨ (∃ D ∈ Ds, d = ⟨ett, fun _ ↦ D A⟩) ∨
      d = ⟨et, fun _ ↦ A⟩}
  | .Det => {d | ∃ D ∈ Ds, d = ⟨det, fun _ ↦ D⟩}
  | .V => {d | (∃ f ∈ Fs, d = ⟨et, f⟩) ∨
      (N ∧ d = ⟨et ⇒ et, fun _ (P : Set E) ↦ (Pᶜ : Set E)⟩)}
  | .Neg => {d | N ∧ d = ⟨et ⇒ et, fun _ (P : Set E) ↦ (Pᶜ : Set E)⟩}
  | _ => ∅

variable {N : Prop} {Fs : Set (W → E → Prop)} {Ds : Set (Det E)} {Ws : Finset Word}
  {c : Case} {q : Set W}

theorem table_unary {c a : Cat} (ha : a ∈ pat c) : Table A N Fs Ds a ⊆ Table A N Fs Ds c := by
  intro d hd
  unfold pat at ha
  split at ha <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  · rcases ha with rfl | rfl
    · rcases hd with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | rfl <;> exact Or.inl fun h ↦ by cases h
    · rcases hd with ⟨_, _, rfl⟩ | ⟨_, rfl⟩ <;> exact Or.inl fun h ↦ by cases h
  · rcases ha with rfl | rfl
    · exact Or.inl hd
    · exact hd
  · rcases ha with rfl | rfl
    · exact Or.inr hd
    · exact hd

theorem table_binary (hneg : N → ∀ f ∈ Fs, (fun w ↦ (f w : Set E)ᶜ) ∈ Fs) {c a b : Cat}
    (hab : [a, b].Sublist (pat c)) : ∀ x ∈ Table A N Fs Ds a, ∀ y ∈ Table A N Fs Ds b,
      ∀ (u : Ty Unit) (m : Application x.1 y.1 u),
        (⟨u, fun w ↦ m.eval (Dom E) (x.2 w) (y.2 w)⟩ : Denotation E W) ∈ Table A N Fs Ds c := by
  intro x hx y hy u m
  have pair {x y : Cat} (h : [a, b].Sublist [x, y]) : a = x ∧ b = y := by
    simpa using h.eq_of_length_le (by simp)
  unfold pat at hab
  split at hab
  · obtain ⟨rfl, rfl⟩ := pair hab
    rcases hx with ⟨D, hD, rfl⟩ | ⟨D, hD, rfl⟩ | rfl <;> rcases hy with ⟨f, hf, rfl⟩ | ⟨_, rfl⟩ <;>
      cases m <;> first
        | exact Or.inr ⟨D, hD, f, hf, rfl⟩
        | exact Or.inl fun h ↦ by cases h
  · obtain ⟨rfl, rfl⟩ := pair hab
    obtain ⟨D, hD, rfl⟩ := hx
    rcases hy with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | rfl <;> cases m
    exact Or.inr (Or.inl ⟨D, hD, rfl⟩)
  · obtain ⟨rfl, rfl⟩ := pair hab
    obtain ⟨hN, rfl⟩ := hx
    rcases hy with ⟨f, hf, rfl⟩ | ⟨_, rfl⟩ <;> cases m
    exact Or.inl ⟨_, hneg hN f hf, rfl⟩
  · simp at hab

-- every meaning of a licensed tree lies in a table of what each category can denote, if the
-- table is closed under the local trees the relation admits
theorem meanings_mem_of_licensed {R : Tree.Label Cat Word → List (Tree.Label Cat Word) → Prop}
    {U : Cat → Set (Denotation E W)}
    (hT : ∀ c w d, R (.terminal c w) [] → denotes A X w = some d → d ∈ U c)
    (h1 : ∀ c k a, R (.phrase c k) [a] → U a.cat ⊆ U c)
    (h2 : ∀ c k a b, R (.phrase c k) [a, b] → ∀ x ∈ U a.cat, ∀ y ∈ U b.cat,
      ∀ (u : Ty Unit) (m : Application x.1 y.1 u),
        (⟨u, fun w ↦ m.eval (Dom E) (x.2 w) (y.2 w)⟩ : Denotation E W) ∈ U c)
    (hne : ∀ n c ks, ¬ R (.trace n c) ks ∧ ¬ R (.bind n c) ks) (t : Tree Cat Word) :
    t.Licensed R → ∀ d ∈ meanings A X t, d ∈ U t.cat := by
  refine RoseTree.rec' (motive := fun t ↦ t.Licensed R → ∀ d ∈ meanings A X t,
    d ∈ U (Tree.cat t)) (fun l cs ih ht d hd ↦ ?_) t
  obtain ⟨hr, hc⟩ := RoseTree.licensed_node_iff.1 ht
  cases l with
  | terminal c w =>
    rcases cs with _ | ⟨c', r⟩
    · simp only [meanings, Tree.values, Tree.derivs, Tree.skeleton, Interpreter.derivs,
        List.map_map, List.mem_map, Option.mem_toList] at hd
      obtain ⟨⟨a, x⟩, hx, rfl⟩ := hd
      exact hT c w _ hr hx
    · simp [meanings, Tree.values, Tree.derivs, Tree.skeleton] at hd
  | phrase c k =>
    rcases cs with _ | ⟨t₁, _ | ⟨t₂, _ | ⟨t₃, r⟩⟩⟩
    · simp [meanings, Tree.values, Tree.derivs, Tree.skeleton] at hd
    · exact h1 c k _ hr (ih t₁ (by simp) (hc t₁ (by simp)) d
        (by simpa [meanings, Tree.values_phrase_unary] using hd))
    · simp only [meanings, Tree.values_phrase_binary, List.mem_flatMap, List.mem_map] at hd
      obtain ⟨x, hx, y, hy, ⟨u, m⟩, -, rfl⟩ := hd
      exact h2 c k _ _ hr x (ih t₁ (by simp) (hc t₁ (by simp)) x hx) y
        (ih t₂ (by simp) (hc t₂ (by simp)) y hy) u m
    · simp [meanings, Tree.values, Tree.derivs, Tree.skeleton] at hd
  | trace n c => exact absurd hr (hne n c _).1
  | bind n c => exact absurd hr (hne n c _).2

theorem licensed_of_alt {source : Set (Tree Cat Word)} {φ ψ : Tree Cat Word}
    (hs : ∀ s ∈ source, s.Licensed (Licit Ws)) (hφ : φ.Licensed (Licit Ws))
    (h : atMostAsComplex source ψ φ) : ψ.Licensed (Licit Ws) := by
  refine licensed_of_atMostAsComplex hs (fun l ks i hl hr ↦ ?_) (fun l ks i k hi hl hc hr ↦ ?_)
    (fun _ _ _ _ _ h ↦ h) hφ h
  · cases l with
    | phrase c k => exact ((List.eraseIdx_sublist ks i).map _).trans hr
    | _ => exact hl.elim
  · cases l with
    | phrase c k =>
      have hi' : Label.cat ks[i] = (ks.map Label.cat)[i]'(by simpa using hi) := by simp
      simpa only [Licit, List.map_set, hc, hi', List.set_getElem_self] using hr
    | _ => exact hl.elim

theorem simplex_subset (hs : ∀ s ∈ (↑(lex c) : Set (Tree Cat Word)), s.Licensed (Licit Ws))
    (hφ : (prejacent c).Licensed (Licit Ws))
    (hneg : N → ∀ f ∈ Fs, (fun w ↦ (f w : Set E)ᶜ) ∈ Fs)
    (hsome : .some_ ∈ Ws → Det.some ∈ Ds) (hall : .all_ ∈ Ws → Det.every ∈ Ds)
    (hnall : .nall ∈ Ws → nallDet ∈ Ds) (hpred : .pred ∈ Ws → X ∈ Fs)
    (hant : .antonym ∈ Ws → (fun w ↦ (X w)ᶜ) ∈ Fs) (hnot : .not_ ∈ Ws → N)
    (hq : q ∈ simplex A X c) : ∃ D ∈ Ds, ∃ f ∈ Fs, q = fun w ↦ D A (f w) := by
  obtain ⟨ψ, hψ, h⟩ := hq
  have hcat : Tree.cat ψ = .S := hψ.cat_eq.trans (by cases c <;> rfl)
  have hT (c : Cat) (w d) (hw : Licit Ws (.terminal c w) List.nil) (hd : denotes A X w = some d) :
      d ∈ Table A N Fs Ds c := by
    obtain ⟨hw, rfl, -⟩ := hw
    cases w <;> cases hd
    · exact ⟨_, hsome hw, rfl⟩
    · exact ⟨_, hall hw, rfl⟩
    · exact ⟨_, hnall hw, rfl⟩
    · exact Or.inr (Or.inr rfl)
    · exact Or.inl ⟨_, hpred hw, rfl⟩
    · exact Or.inl ⟨_, hant hw, rfl⟩
    · exact ⟨hnot hw, rfl⟩
  have hm := meanings_mem_of_licensed (R := Licit Ws) (U := Table A N Fs Ds) hT
    (fun _ _ _ hr ↦ table_unary (hr.subset (by simp)))
    (fun _ _ _ _ hr ↦ table_binary hneg hr)
    (fun _ _ _ ↦ ⟨id, id⟩) ψ (licensed_of_alt hs hφ hψ) _ h
  rw [hcat] at hm
  rcases hm with h0 | ⟨D, hD, f, hf, he⟩
  · exact absurd rfl h0
  · exact ⟨D, hD, f, hf, eq_of_heq (Sigma.mk.inj_iff.1 he).2⟩

theorem nall_compl_iff {B : Set E} : nallDet A Bᶜ ↔ Det.some A B :=
  (not_congr Det.no_iff_not_some).trans not_not

theorem some_compl_iff {B : Set E} : Det.some A Bᶜ ↔ nallDet A B := by
  simpa using (nall_compl_iff (A := A) (B := Bᶜ)).symm

theorem simplex_subset_corners (c : Case) :
    simplex A X c ⊆ {(sqAt A X).A, (sqAt A X).E, (sqAt A X).I, (sqAt A X).O} := by
  intro q hq
  obtain ⟨D, hD, f, hf, rfl⟩ := simplex_subset (N := True) (Fs := {X, fun w ↦ (X w)ᶜ})
    (Ds := {Det.some, Det.every, nallDet})
    (Ws := {.some_, .all_, .nall, .noun, .pred, .antonym, .not_})
    (by cases c <;> decide) (by cases c <;> decide)
    (fun _ f hf ↦ by
      rcases hf with rfl | rfl
      · exact Or.inr rfl
      · exact Or.inl (funext fun w ↦ compl_compl (X w)))
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) hq
  simp only [mem_insert_iff, mem_singleton_iff] at hD hf ⊢
  rcases hf with rfl | rfl <;> rcases hD with rfl | rfl | rfl
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inl rfl
  · exact Or.inr (Or.inr (Or.inr rfl))
  · exact Or.inr (Or.inr (Or.inr (Set.ext fun w ↦ some_compl_iff)))
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl (Set.ext fun w ↦ nall_compl_iff)))

theorem simplex_bare_subset : simplex A X .bare ⊆ {(sqAt A X).I, (sqAt A X).A} := by
  intro q hq
  obtain ⟨D, hD, f, rfl, rfl⟩ := simplex_subset (c := .bare) (N := False) (Fs := {X})
    (Ds := {Det.some, Det.every}) (Ws := {.some_, .all_, .noun, .pred})
    (by decide) (by decide) (fun h ↦ h.elim)
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) hq
  rcases hD with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem simplex_minimal_subset : simplex A X .minimal ⊆ {(sqAt A X).I} := by
  intro q hq
  obtain ⟨D, rfl, f, rfl, rfl⟩ := simplex_subset (c := .minimal) (N := False) (Fs := {X})
    (Ds := {Det.some}) (Ws := {.some_, .noun, .pred})
    (by decide) (by decide) (fun h ↦ h.elim)
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) hq
  rfl

theorem sentence_mem {d d' : Word} {v : Tree Cat Word} (hφ : prejacent c = sentence d v)
    (h : Tree.terminal .Det d' ∈ lex c) :
    atMostAsComplex ↑(lex c) (sentence d' v) (prejacent c) := by
  rw [hφ]
  exact .single (.inChild ⟨0, by simp⟩ (.inChild ⟨0, by simp⟩ (.subst rfl h)))

theorem A_mem_simplex (hc : c ≠ .minimal) : (squareOf (sqAt A X) c).A ∈ simplex A X c := by
  cases c <;> first
    | exact absurd rfl hc
    | exact ⟨_, sentence_mem (d' := .all_) rfl (by decide), List.mem_cons_self⟩

theorem O_mem_simplex (hc : c = .negated ∨ c = .antonym ∨ c = .lexicalized) :
    (squareOf (sqAt A X) c).O ∈ simplex A X c := by
  rcases hc with rfl | rfl | rfl
  · refine ⟨sentence .some_ (.terminal .V .pred), .single ?_, List.mem_cons_self⟩
    exact .inChild ⟨1, by simp⟩ (ψ_child := Tree.terminal Cat.V Word.pred)
      (.contract (by simp) rfl trivial)
  · have hO : (squareOf (sqAt A X) .antonym).O = fun w ↦ Det.some A (X w)ᶜ :=
      Set.ext fun _ ↦ some_compl_iff.symm
    rw [hO]
    exact ⟨sentence .some_ (.terminal .V .antonym),
      .single (.inChild ⟨1, by simp⟩ (.subst rfl (by decide))), List.mem_cons_self⟩
  · exact ⟨_, sentence_mem (d' := .nall) rfl (by decide), List.mem_cons_self⟩

theorem simplex_subset_squareOf (c : Case) : simplex A X c ⊆ {(squareOf (sqAt A X) c).A,
    (squareOf (sqAt A X) c).E, (squareOf (sqAt A X) c).I, (squareOf (sqAt A X) c).O} := by
  cases c <;> first
    | exact simplex_subset_corners _
    | refine (simplex_subset_corners _).trans fun q hq ↦ ?_
      simp only [mem_insert_iff, mem_singleton_iff, squareOf, Square.inner] at hq ⊢
      tauto

theorem squareOf_relations (h : SquareRelations (sqAt A X)) (c : Case) :
    SquareRelations (squareOf (sqAt A X) c) := by
  cases c <;> first | exact h | exact h.inner

theorem squareOf_triangle_ne (hne : ∀ t, (sqAt A X).triangle t ≠ ⊥) (c : Case) (t : Triangle) :
    (squareOf (sqAt A X) c).triangle t ≠ ⊥ := by
  cases c <;> first
    | exact hne t
    | cases t
      · exact hne .all
      · exact fun h0 ↦ hne .someNotAll ((inf_comm _ _).trans h0)
      · exact hne .none

theorem O_ne_I (h : SquareRelations (sqAt A X)) (hne : ∀ t, (sqAt A X).triangle t ≠ ⊥) :
    (sqAt A X).O ≠ (sqAt A X).I := fun heq ↦
  hne .all (h.contraryAE.eq_bot_of_le (by
    rw [← h.contradEI.symm.compl_eq, ← heq, ← h.contradAO.compl_eq, compl_compl]))

theorem O_ne_A (h : SquareRelations (sqAt A X)) (hne : ∀ t, (sqAt A X).triangle t ≠ ⊥) :
    (sqAt A X).O ≠ (sqAt A X).A := fun heq ↦
  hne .all (h.contradAO.disjoint.eq_bot_of_le heq.ge)

theorem A_notMem_simplex_minimal (h : SquareRelations (sqAt A X))
    (hne : ∀ t, (sqAt A X).triangle t ≠ ⊥) : (sqAt A X).A ∉ simplex A X .minimal := fun hA ↦
  absurd (mem_singleton_iff.1 (simplex_minimal_subset hA)) ((lt_I_iff h hne (by simp)).2 rfl).ne

theorem O_notMem_simplex (h : SquareRelations (sqAt A X)) (hne : ∀ t, (sqAt A X).triangle t ≠ ⊥)
    (hc : c = .bare ∨ c = .minimal) : (sqAt A X).O ∉ simplex A X c := fun hO ↦ by
  rcases hc with rfl | rfl
  · rcases simplex_bare_subset hO with hq | hq
    · exact O_ne_I h hne hq
    · exact O_ne_A h hne hq
  · exact O_ne_I h hne (simplex_minimal_subset hO)

/-- Which alternative an exclusion negates: the scalar alternative `A` or the symmetric one `O`, the
pair of the paper's (10) and (68). -/
inductive Excluded
  | scalar | symmetric
  deriving DecidableEq, Repr

/-- The other alternative of the pair. -/
def Excluded.other : Excluded → Excluded
  | .scalar => .symmetric
  | .symmetric => .scalar

/-- The negated alternative at each example. -/
def excl (sq : Square (Set W)) (c : Case) : Excluded → Set W
  | .scalar => (squareOf sq c).A
  | .symmetric => (squareOf sq c).O

-- Excluding the scalar alternative is never blocked, and excluding the symmetric one always is,
-- except where the language lacks a simplex scalar alternative to block it.
theorem not_blocked_iff (h : SquareRelations (sqAt A X)) (hne : ∀ t, (sqAt A X).triangle t ≠ ⊥)
    (c : Case) (e : Excluded) :
    ¬ Blocked (simplex A X c) ((squareOf (sqAt A X) c).I \ excl (sqAt A X) c e)
      (squareOf (sqAt A X) c).I ↔ e = .scalar ∨ c = .minimal := by
  have hr := squareOf_relations h c
  have hn := squareOf_triangle_ne hne c
  cases e
  · simpa [excl] using not_blocked_I_sdiff_A hr hn (simplex_subset_squareOf c)
  · simp only [excl, reduceCtorEq, false_or]
    rw [blocked_I_sdiff_O_iff hr hn (simplex_subset_squareOf c)]
    cases c <;> first
      | simpa using A_mem_simplex (by decide)
      | simpa [squareOf] using A_notMem_simplex_minimal h hne

-- What the complexity filter permits: the scalar alternative where the language has one, and the
-- symmetric one where it is simplex too.
theorem excl_mem_simplex_iff (h : SquareRelations (sqAt A X))
    (hne : ∀ t, (sqAt A X).triangle t ≠ ⊥) (c : Case) (e : Excluded) :
    excl (sqAt A X) c e ∈ simplex A X c ↔
      (e = .scalar ∧ c ≠ .minimal) ∨ (e = .symmetric ∧ c ≠ .bare ∧ c ≠ .minimal) := by
  cases e <;> cases c <;> simp only [excl, reduceCtorEq, ne_eq, not_true_eq_false,
    not_false_eq_true, and_self, and_false, false_and, or_false, false_or, iff_true, iff_false] <;>
    first
      | exact A_mem_simplex (by decide)
      | exact O_mem_simplex (by decide)
      | exact A_notMem_simplex_minimal h hne
      | exact O_notMem_simplex h hne (by decide)

-- The filter with the stalemate assumption (26) permits an exclusion only if its alternative is
-- simplex and the other is not, which is only the scalar alternative of (1).
theorem filter_iff (h : SquareRelations (sqAt A X)) (hne : ∀ t, (sqAt A X).triangle t ≠ ⊥)
    (c : Case) (e : Excluded) :
    (excl (sqAt A X) c e ∈ simplex A X c ∧ excl (sqAt A X) c e.other ∉ simplex A X c) ↔
      e = .scalar ∧ c = .bare := by
  rw [excl_mem_simplex_iff h hne, excl_mem_simplex_iff h hne]
  cases e <;> cases c <;> simp [Excluded.other]

end Interpretation

/-! ### The judgments -/

/-- A row: the example, the excluded alternative, and whether the reading is available. -/
structure Row where
  case : Case
  excluded : Excluded
  available : Bool
  deriving DecidableEq

def Row.ofDatum (ex : Datum) : Option Row := do
  let c ← ex.parse? "case" [("bare", Case.bare), ("negated", .negated), ("antonym", .antonym),
    ("lexicalized", .lexicalized), ("minimal", .minimal)]
  let e ← ex.parse? "excluded" [("scalar", Excluded.scalar), ("symmetric", .symmetric)]
  let a ← ex.parse? "available" [("yes", true), ("no", false)]
  pure ⟨c, e, a⟩

/-- The rows of the paper's examples. -/
def rows : List Row := Examples.all.filterMap Row.ofDatum

theorem rows_available_iff :
    rows.length = 10 ∧ ∀ r ∈ rows, r.available = true ↔ r.excluded = .scalar := by
  decide

section Comparison

variable {E W : Type} {A : Set E} {X : W → Set E}

/-- Blocking misjudges only (76b), as the paper says. -/
theorem blocked_misjudges_iff (h : SquareRelations (sqAt A X))
    (hne : ∀ t, (sqAt A X).triangle t ≠ ⊥) :
    ∀ r ∈ rows, (¬ (¬ Blocked (simplex A X r.case)
      ((squareOf (sqAt A X) r.case).I \ excl (sqAt A X) r.case r.excluded)
        (squareOf (sqAt A X) r.case).I ↔ r.available = true)) ↔
      r.case = .minimal ∧ r.excluded = .symmetric := by
  intro r hr
  rw [not_blocked_iff h hne]
  revert r
  decide

-- The filter with the stalemate misjudges the available reading of every example but (1).
theorem filter_misjudges_iff (h : SquareRelations (sqAt A X))
    (hne : ∀ t, (sqAt A X).triangle t ≠ ⊥) :
    ∀ r ∈ rows, (¬ ((excl (sqAt A X) r.case r.excluded ∈ simplex A X r.case ∧
      excl (sqAt A X) r.case r.excluded.other ∉ simplex A X r.case) ↔ r.available = true)) ↔
        r.excluded = .scalar ∧ r.case ≠ .bare := by
  intro r hr
  rw [filter_iff h hne]
  revert r
  decide

end Comparison

end SchwarzWagner2026
