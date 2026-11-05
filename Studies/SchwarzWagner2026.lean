module

public import Linglib.Data.Examples.SchwarzWagner2026
public import Linglib.Pragmatics.NeoGricean.Basic
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
* One grammar covers the examples. `Word` has one lexical item per corner and a predicate with an
  optional antonym: *some*, *all* and *permitted*, *required*, *optional* are parallel on the
  paper's own account of (52). A `Case` is a prejacent with its lexicon, and each lexicon lists only
  the words the paper's discussion of that example uses. `optional` is the O corner, not `I ⊓ O`,
  as the paper argues from (54).
* Meanings are read at an arbitrary nondegenerate square, so the results hold at `Det.square` and
  `modalSquare` alike.

## Errata

Section 4.1 says that under strict symmetry the complexity filter and blocking "are necessarily
aligned", reasoning from the equalities (70) that blocking prohibits a strengthening only if the
other alternative is simplex. That holds of the first version (14), not of the revised (67) the
section quotes, which [also reads every simplex meaning strictly
between](##IsSymmetric.blocked_sdiff_iff), and [the alignment fails](##exists_isSymmetric_blocked).
Section 4.3's extension to entailment symmetry, whose proof the paper omits, inherits this. The
paper offers no example with such a meaning.

## TODO

The contextual cases (23), (58), (59), the disjunction (29), the embedding (79) and the question
effects (61)–(65) are not rows; recoverability is not modelled. [bar-lev-bassi-trinh-2025] derive
blocking's effects from fatal competition and partition by exhaustification against the 2024
manuscript's equivalence version, and that comparison needs a theory of questions here.

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
  simp only [mem_image, not_exists, not_and, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  exact and_congr_right fun _ ↦ forall₂_congr fun _ _ ↦ ⟨fun h hs hss ↦ h hss hs, fun h hss hs ↦ h hs hss⟩

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
x* is simpler than *You may have x or y*, strictly stronger, and entailed by the free-choice reading.
One round of innocent exclusion is never blocked (`exhIE_notMem_lowerClosure`); the second round of
[fox-2007]'s recursion is. -/
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
  have hE : ¬ sq.E ≤ sq.I := fun hle ↦ hne .E (h.contradEI.disjoint.eq_bot_of_le hle)
  have hIA : ¬ sq.I ≤ sq.A := fun hle ↦ hne .IO <| le_bot_iff.1 <|
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

theorem I_sdiff_O (h : SquareRelations sq) : sq.I \ sq.O = sq.A := by
  rw [_root_.sdiff_eq, ← h.contradAO.eq_compl, inf_eq_right.2 h.subalternAI]

theorem I_sdiff_A (h : SquareRelations sq) : sq.I \ sq.A = sq.I ⊓ sq.O := by
  rw [_root_.sdiff_eq, h.contradAO.compl_eq]

theorem blocked_I_sdiff_O_iff (h : SquareRelations sq) (hne : ∀ t, sq.triangle t ≠ ⊥)
    (hF : F ⊆ {sq.A, sq.E, sq.I, sq.O}) : Blocked F (sq.I \ sq.O) sq.I ↔ sq.A ∈ F := by
  rw [blocked_I_iff h hne hF, I_sdiff_O h]
  simp

theorem not_blocked_I_sdiff_A (h : SquareRelations sq) (hne : ∀ t, sq.triangle t ≠ ⊥)
    (hF : F ⊆ {sq.A, sq.E, sq.I, sq.O}) : ¬ Blocked F (sq.I \ sq.A) sq.I := by
  rw [blocked_I_iff h hne hF, I_sdiff_A h]
  rintro ⟨-, hle⟩
  exact hne .IO <| le_bot_iff.1 <| (le_inf hle inf_le_right).trans h.contradAO.disjoint.le_bot

theorem exhIE_I_eq_self {W : Type*} {sq : Square (Set W)} (h : SquareRelations sq)
    (hne : ∀ t, sq.triangle t ≠ ⊥) : exhIE {sq.I, sq.A, sq.O} sq.I = sq.I := by
  have hcov : sq.I ⊆ sq.A ∪ sq.O := fun w _ ↦
    show w ∈ sq.A ⊔ sq.O from h.contradAO.sup_eq_top ▸ mem_univ w
  refine exhIE_eq_self_of_subset_union hcov ?_ ?_
  · have heq : sq.I \ sq.A = sq.I ⊓ sq.O := I_sdiff_A h
    exact heq ▸ nonempty_iff_ne_empty.2 (show sq.I ⊓ sq.O ≠ ∅ from hne .IO)
  · have heq : sq.I \ sq.O = sq.A := I_sdiff_O h
    exact heq ▸ nonempty_iff_ne_empty.2 (show sq.A ≠ ∅ from hne .A)

end Square

/-! ### The examples -/

/-- The lexical items of the examples: one per corner of the square, *some*, *all* or *permitted*,
*required*, *optional*; a noun; a predicate and its antonym; negation. -/
inductive Word
  | some_ | all_ | nall | noun | pred | antonym | not_
  deriving DecidableEq, Repr

/-- A sentence with a determiner, the noun, and a predicate phrase. -/
abbrev sentence (d : Word) (v : Tree Cat Word) : Tree Cat Word :=
  .node .S [.terminal .Det d, .terminal .N .noun, v]

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

variable {α : Type*} (sq : Square α)

/-- A predicate phrase denotes the square of its scope: an antonym or a negation takes the inner
negation. -/
def scope : Tree Cat Word → Option (Square α)
  | .terminal .V .pred => some sq
  | .terminal .V .antonym => some sq.inner
  | .node .V [.terminal .Neg .not_, t] => (scope t).map Square.inner
  | _ => none

/-- A determiner denotes a corner. -/
def corner (r : Square α) : Word → Option α
  | .some_ => some r.I
  | .all_ => some r.A
  | .nall => some r.O
  | _ => none

/-- The basic meaning of a sentence, where there is one. -/
def meaning : Tree Cat Word → Option α
  | .node .S [.terminal .Det d, .terminal .N .noun, v] => (scope sq v).bind (corner · d)
  | _ => none

/-- The paper's simplex meanings: those of the sentences no more complex than the assertion. -/
def simplex (c : Case) : Set α :=
  {q | ∃ ψ ∈ structuralAlternatives (lex c) (prejacent c), meaning sq ψ = some q}

/-- The square of the assertion: the assertion is its `I` corner. -/
def squareOf : Case → Square α
  | .negated => sq.inner
  | _ => sq

end Interpretation

section Results

variable {α : Type*} {sq : Square α} {c : Case} {ψ : Tree Cat Word} {q : α}

theorem scope_eq {t : Tree Cat Word} {r : Square α} (h : scope sq t = some r) :
    r = sq ∨ r = sq.inner := by
  fun_induction scope sq t generalizing r with
  | case1 => simp_all
  | case2 => simp_all
  | case3 _ ih =>
    obtain ⟨r', hr', rfl⟩ := Option.map_eq_some_iff.1 h
    rcases ih hr' with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl rfl
  | case4 => simp_all

theorem meaning_mem (h : meaning sq ψ = some q) : q ∈ ({sq.A, sq.E, sq.I, sq.O} : Set α) := by
  unfold meaning at h
  split at h
  · obtain ⟨r, hr, hq⟩ := Option.bind_eq_some_iff.1 h
    rcases scope_eq hr with rfl | rfl <;> revert hq <;> unfold corner <;> split <;>
      simp +contextual [Square.inner]
  · simp at h

theorem simplex_subset (c : Case) : simplex sq c ⊆ {sq.A, sq.E, sq.I, sq.O} :=
  fun _ ⟨_, _, h⟩ ↦ meaning_mem h

/-- Whether a tree is a terminal bearing one of the words `B`. -/
def HasWord (B : Finset Word) (t : Tree Cat Word) : Prop :=
  (t.value.terminal?.any fun x ↦ decide (x.2 ∈ B)) = true

instance (B : Finset Word) : DecidablePred (HasWord B) :=
  fun _ ↦ inferInstanceAs (Decidable (_ = true))

theorem not_hasWord {B : Finset Word}
    (hsrc : ∀ t ∈ substitutionSource (lex c) (prejacent c), ∀ s ∈ t.subtrees, ¬ HasWord B s)
    (hφ : ∀ s ∈ (prejacent c).subtrees, ¬ HasWord B s)
    (hψ : ψ ∈ structuralAlternatives (lex c) (prejacent c)) : ∀ s ∈ ψ.subtrees, ¬ HasWord B s :=
  subtree_preservation _ (HasWord B) hsrc
    (fun _ _ _ _ h ↦ h) (fun _ _ _ _ _ h ↦ h) (fun _ _ _ _ h ↦ h) hφ hψ

@[simp] theorem hasWord_terminal {B : Finset Word} {c : Cat} {w : Word} :
    HasWord B (Tree.terminal c w) ↔ w ∈ B := by
  simp [HasWord, Label.terminal?, RoseTree.value]

theorem scope_eq_of_free {v : Tree Cat Word} {r : Square α} {B : Finset Word}
    (hB : Word.antonym ∈ B ∧ Word.not_ ∈ B) (hfree : ∀ s ∈ v.subtrees, ¬ HasWord B s)
    (h : scope sq v = some r) : r = sq := by
  fun_cases scope sq v with
  | case1 => simpa [scope] using h.symm
  | case2 =>
    exact absurd (hasWord_terminal.2 hB.1)
      (hfree (Tree.terminal .V .antonym) (by simp [RoseTree.subtrees_node]))
  | case3 t =>
    exact absurd (hasWord_terminal.2 hB.2)
      (hfree (Tree.terminal .Neg .not_) (by simp [RoseTree.subtrees_node]))
  | case4 => simp_all [scope]

theorem meaning_of_free {B : Finset Word} (hB : Word.antonym ∈ B ∧ Word.not_ ∈ B)
    (hfree : ∀ s ∈ ψ.subtrees, ¬ HasWord B s) (h : meaning sq ψ = some q) :
    ∃ d, d ∉ B ∧ corner sq d = some q := by
  fun_cases meaning sq ψ with
  | case1 d v =>
    obtain ⟨r, hr, hq⟩ := Option.bind_eq_some_iff.1 (by simpa [meaning] using h)
    have hsub : ∀ s ∈ RoseTree.subtrees v, ¬ HasWord B s := fun s hs ↦ hfree s <| by
      rw [RoseTree.subtrees_node]
      exact List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨v, by simp, hs⟩)
    obtain rfl := scope_eq_of_free hB hsub hr
    refine ⟨d, fun hd ↦ hfree (Tree.terminal .Det d) ?_ (hasWord_terminal.2 hd), hq⟩
    rw [RoseTree.subtrees_node]
    exact List.mem_cons_of_mem _
      (List.mem_flatMap.2 ⟨Tree.terminal .Det d, by simp, by simp [RoseTree.subtrees_node]⟩)
  | case2 => simp_all [meaning]

theorem simplex_bare_subset : simplex sq .bare ⊆ {sq.I, sq.A} := by
  rintro q ⟨ψ, hψ, h⟩
  obtain ⟨d, hd, hq⟩ := meaning_of_free (B := {.antonym, .not_, .nall}) (by decide)
    (not_hasWord (forall_mem_substitutionSource.2 ⟨by decide, by decide⟩) (by decide) hψ) h
  cases d <;> simp_all [corner]

theorem simplex_minimal_subset : simplex sq .minimal ⊆ {sq.I} := by
  rintro q ⟨ψ, hψ, h⟩
  obtain ⟨d, hd, hq⟩ := meaning_of_free (B := {.antonym, .not_, .nall, .all_}) (by decide)
    (not_hasWord (forall_mem_substitutionSource.2 ⟨by decide, by decide⟩) (by decide) hψ) h
  cases d <;> simp_all [corner]

theorem sentence_mem {d d' : Word} {v : Tree Cat Word} (hφ : prejacent c = sentence d v)
    (h : Tree.terminal .Det d' ∈ lex c) :
    sentence d' v ∈ structuralAlternatives (lex c) (prejacent c) := by
  rw [hφ]
  exact .single (.inChild ⟨0, by simp⟩ (.subst rfl (mem_union_left _ h)))

theorem A_mem_simplex (hc : c ≠ .minimal) : (squareOf sq c).A ∈ simplex sq c := by
  cases c <;> first
    | exact absurd rfl hc
    | exact ⟨_, sentence_mem (d' := .all_) rfl (by decide), rfl⟩

theorem O_mem_simplex (hc : c = .negated ∨ c = .antonym ∨ c = .lexicalized) :
    (squareOf sq c).O ∈ simplex sq c := by
  rcases hc with rfl | rfl | rfl
  · refine ⟨sentence .some_ (.terminal .V .pred), .single ?_, rfl⟩
    exact .inChild ⟨2, by simp⟩ (ψ_child := Tree.terminal Cat.V Word.pred)
      (.contract (by simp) rfl trivial)
  · exact ⟨sentence .some_ (.terminal .V .antonym), .single
      (.inChild ⟨2, by simp⟩ (.subst rfl (mem_union_left _ (by decide)))), rfl⟩
  · exact ⟨_, sentence_mem (d' := .nall) rfl (by decide), rfl⟩

theorem simplex_subset_squareOf (c : Case) : simplex sq c ⊆
    {(squareOf sq c).A, (squareOf sq c).E, (squareOf sq c).I, (squareOf sq c).O} := by
  cases c <;> first
    | exact simplex_subset _
    | refine (simplex_subset _).trans fun q hq ↦ ?_
      simp only [mem_insert_iff, mem_singleton_iff, squareOf, Square.inner] at hq ⊢
      tauto

variable [BooleanAlgebra α]

theorem squareOf_relations (h : SquareRelations sq) (c : Case) :
    SquareRelations (squareOf sq c) := by
  cases c <;> first | exact h | exact h.inner

theorem squareOf_triangle_ne (hne : ∀ t, sq.triangle t ≠ ⊥) (c : Case) (t : Triangle) :
    (squareOf sq c).triangle t ≠ ⊥ := by
  cases c <;> first
    | exact hne t
    | cases t
      · exact hne .A
      · exact fun h0 ↦ hne .IO ((inf_comm sq.I sq.O).trans h0)
      · exact hne .E

theorem A_notMem_simplex_minimal (h : SquareRelations sq) (hne : ∀ t, sq.triangle t ≠ ⊥) :
    sq.A ∉ simplex sq .minimal := fun hA ↦
  absurd (mem_singleton_iff.1 (simplex_minimal_subset hA))
    ((lt_I_iff h hne (by simp)).2 rfl).ne

theorem O_ne_I (h : SquareRelations sq) (hne : ∀ t, sq.triangle t ≠ ⊥) : sq.O ≠ sq.I := fun heq ↦
  hne .A (h.contraryAE.eq_bot_of_le (by
    rw [← h.contradEI.symm.compl_eq, ← heq, ← h.contradAO.compl_eq, compl_compl]))

theorem O_ne_A (h : SquareRelations sq) (hne : ∀ t, sq.triangle t ≠ ⊥) : sq.O ≠ sq.A := fun heq ↦
  hne .A (h.contradAO.disjoint.eq_bot_of_le heq.ge)

theorem O_notMem_simplex (h : SquareRelations sq) (hne : ∀ t, sq.triangle t ≠ ⊥)
    (hc : c = .bare ∨ c = .minimal) : sq.O ∉ simplex sq c := fun hO ↦ by
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

/-- The negated alternative at each example. -/
def excl (sq : Square α) (c : Case) : Excluded → α
  | .scalar => (squareOf sq c).A
  | .symmetric => (squareOf sq c).O

theorem not_blocked_iff (h : SquareRelations sq) (hne : ∀ t, sq.triangle t ≠ ⊥) (c : Case)
    (e : Excluded) :
    ¬ Blocked (simplex sq c) ((squareOf sq c).I \ excl sq c e) (squareOf sq c).I ↔
      e = .scalar ∨ c = .minimal := by
  have hr := squareOf_relations h c
  have hn := squareOf_triangle_ne hne c
  cases e
  · simpa [excl] using not_blocked_I_sdiff_A hr hn (simplex_subset_squareOf c)
  · simp only [excl, reduceCtorEq, false_or]
    rw [blocked_I_sdiff_O_iff hr hn (simplex_subset_squareOf c)]
    cases c <;> first
      | simpa using A_mem_simplex (by decide)
      | simpa [squareOf] using A_notMem_simplex_minimal h hne

theorem excl_mem_simplex_iff (h : SquareRelations sq) (hne : ∀ t, sq.triangle t ≠ ⊥) (c : Case)
    (e : Excluded) : excl sq c e ∈ simplex sq c ↔
      (e = .scalar ∧ c ≠ .minimal) ∨ (e = .symmetric ∧ c ≠ .bare ∧ c ≠ .minimal) := by
  cases e <;> cases c <;> simp only [excl, reduceCtorEq, ne_eq, not_true_eq_false,
    not_false_eq_true, and_self, and_false, false_and, or_false, false_or, iff_true, iff_false] <;>
    first
      | exact A_mem_simplex (by decide)
      | exact O_mem_simplex (by decide)
      | exact A_notMem_simplex_minimal h hne
      | exact O_notMem_simplex h hne (by decide)

/-- The other alternative of the pair. -/
def Excluded.other : Excluded → Excluded
  | .scalar => .symmetric
  | .symmetric => .scalar

-- (26), (1)
theorem filter_iff (h : SquareRelations sq) (hne : ∀ t, sq.triangle t ≠ ⊥) (c : Case)
    (e : Excluded) : (excl sq c e ∈ simplex sq c ∧ excl sq c e.other ∉ simplex sq c) ↔
      e = .scalar ∧ c = .bare := by
  rw [excl_mem_simplex_iff h hne, excl_mem_simplex_iff h hne]
  cases e <;> cases c <;> simp [Excluded.other]

end Results

/-! ### The square at the determiners -/

section Determiners

open Quantifier.Det

variable {E : Type*} {A : Set E} {a b : E}

-- Negating the scope is the inner negation of the determiners' square.
example (B : Set E) : (Quantifier.Det.square A).inner.A B ↔ every A Bᶜ := by
  simp [Square.inner, Quantifier.Det.square, no, every]

example (B : Set E) : (Quantifier.Det.square A).inner.I B ↔ Quantifier.Det.some A Bᶜ := by
  simp [Square.inner, Quantifier.Det.square, Quantifier.Det.some, every, Set.not_subset,
    Set.Nonempty]

-- Two players make the square nondegenerate, so the examples hold of *some* and *all*.
example (ha : a ∈ A) (hb : b ∈ A) (hab : a ≠ b) (t : Triangle) :
    (Quantifier.Det.square A).triangle t ≠ ⊥ := by
  have key : ∀ (q : Quantifier E) (B : Set E), q B → q ≠ ⊥ := fun q B hq h ↦ by
    subst h
    exact hq
  cases t
  · exact key _ ∅ (fun _ _ h ↦ h)
  · exact key _ {a} ⟨⟨a, ha, rfl⟩, fun h ↦ hab (h hb).symm⟩
  · exact key _ univ fun _ _ ↦ mem_univ _

end Determiners

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

variable {α : Type*} [BooleanAlgebra α] {sq : Square α}

/-- Blocking misjudges only (76b), as the paper says. -/
theorem blocked_misjudges_iff (h : SquareRelations sq) (hne : ∀ t, sq.triangle t ≠ ⊥) :
    ∀ r ∈ rows, (¬ (¬ Blocked (simplex sq r.case)
      ((squareOf sq r.case).I \ excl sq r.case r.excluded) (squareOf sq r.case).I ↔
        r.available = true)) ↔ r.case = .minimal ∧ r.excluded = .symmetric := by
  intro r hr
  rw [not_blocked_iff h hne]
  revert r
  decide

-- (1)
theorem filter_misjudges_iff (h : SquareRelations sq) (hne : ∀ t, sq.triangle t ≠ ⊥) :
    ∀ r ∈ rows, (¬ ((excl sq r.case r.excluded ∈ simplex sq r.case ∧
      excl sq r.case r.excluded.other ∉ simplex sq r.case) ↔ r.available = true)) ↔
        r.excluded = .scalar ∧ r.case ≠ .bare := by
  intro r hr
  rw [filter_iff h hne]
  revert r
  decide

end Comparison

end SchwarzWagner2026
