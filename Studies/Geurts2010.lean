module

public import Studies.GeurtsPouscoulous2009
public import Linglib.Pragmatics.NeoGricean.Basic
public import Linglib.Semantics.Exhaustification.Basic
public import Linglib.Data.Examples.Geurts2010
public import Mathlib.Order.Atoms
public import Mathlib.Order.Bounds.Defs
public import Mathlib.Order.UpperLower.Basic

/-!
# Geurts (2010): Quantity Implicatures

A quantity implicature is an inference about a speaker's beliefs, drawn from the speaker's not
having said something stronger. With alternatives closed under conjunction and disjunction, which
the book declines, and Competence assumed wherever consistent, the Standard Recipe [gives exactly
the exclusive reading of a long
disjunction](##Ioi_sdiff_sUnion_isSecondaryImplicature_eq_setOf_isAtom); under *may* it [leaves no
consistent state](##Sentence.standardRecipe_may_or_eq_empty). Partitioning the speaker's states
instead gives [free choice](##Sentence.mem_survivors_may_or_iff) and [form-sensitive scalar
inferences](##Sentence.mem_survivors_scalar_iff). Comparing readings for strength [picks out the
upward-entailing scopes](##readings_ssubset_iff), where the experiment finds no upper bound.

## Implementation notes

* A state is the worlds compatible with the speaker's beliefs. `may` quantifies over it, which
  builds in footnote 5 of p. 111.
* `IsSecondaryImplicature` serves as the necessary condition on Competence of p. 41, per
  alternative; strengthening wherever it holds is an assumption made here, the book's Recipe being
  a heuristic.
* `Sentence.survivors` applies heuristic (i) categorically, with one alternative per cell and `size`
  for economy, so (26b) comes out by length rather than the monolexicality p. 124 credits. Heuristic
  (ii), which p. 117 invokes, is not formalized.
* Upper sets model the closure of the disjuncts under conjunction and disjunction, up to the empty
  set and the whole space.
* (61b, c) are read through the quantifiers of (62).

## TODO

* §8.3 presupposition implicatures, §6.6 open alternatives, Spector's route (pp. 169–170,
  [spector-2006]), and the free choice of (20), p. 120, without a modal.
* The consistency check against the innocent exclusion of [fox-2007] at (34) and (35).
* The experiments of Chapters 4 and 5, for `Data/Statistics`.

## References

* [geurts-2010]
* [geurts-pouscoulous-2009]
* [fox-2007]
* [russell-2006]
* [sauerland-2004]
* [soames-1982]
* [spector-2006]
* [vanrooij-schulz-2004]
-/

@[expose] public section

namespace Geurts2010

open Set NeoGricean Question

variable {W : Type*} {s φ ψ : Set W}

/-! ### The Standard Recipe -/

-- p. 110, footnote 4; p. 167
theorem inter_nonempty_of_subset_union (hq : s ⊆ φ ∪ ψ) (hψ : ¬ s ⊆ ψ) : (s ∩ φ).Nonempty :=
  let ⟨_, hw, hwψ⟩ := not_subset.1 hψ
  ⟨_, hw, (hq hw).resolve_right hwψ⟩

-- p. 41: given Quality, the weak implicatures make Competence fail for a disjunct, when the rest
-- of the disjunction is itself an alternative
theorem notMem_polar_of_subset_union (hq : s ⊆ φ ∪ ψ) (hφ : ¬ s ⊆ φ) (hψ : ¬ s ⊆ ψ) :
    s ∉ polar φ := fun h ↦
  (mem_polar.1 h).elim hφ fun hc ↦
    let ⟨_, hw, hwφ⟩ := inter_nonempty_of_subset_union hq hψ
    hc hw hwφ

/-! ### Long disjunctions

The worlds of (29), p. 61, are ordered by what they make true. A world with `⊥` below it is one in
which no disjunct holds, so the long disjunction (31) is `Ioi ⊥`; the conjunction of the disjuncts
below `x` is `Ici x`, and a world in which just one disjunct holds is an atom. -/

section LongDisjunction

variable {α : Type*} [PartialOrder α] [OrderBot α] {a b c x : α} {t : Set α}

private theorem notMem_Ici_of_isAtom (hb : IsAtom b) (hx : x ≠ ⊥) (h : x ≠ b) : b ∉ Ici x :=
  fun hle ↦ h ((hb.le_iff_eq hx).1 hle)

private theorem Ici_ssubset_Ioi_bot (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b) :
    Ici a ⊂ Ioi (⊥ : α) :=
  ⟨fun _ hy ↦ ha.bot_lt.trans_le hy, fun h ↦ notMem_Ici_of_isAtom hb ha.1 hab (h hb.bot_lt)⟩

private theorem compl_Iic_ssubset_Ioi_bot (hx : IsAtom x) : (Iic x)ᶜ ⊂ Ioi (⊥ : α) :=
  ⟨fun _ hy ↦ bot_lt_iff_ne_bot.2 fun he ↦ hy (he ▸ bot_le), fun h ↦ h hx.bot_lt le_rfl⟩

-- pp. 63–64: with the alternatives (34) and (35), closed under conjunction only, `K¬A` passes the
-- consistency check once there are three disjuncts, because (35) leaves out the rest of the
-- disjunction
theorem isSecondaryImplicature_Ici (ha : IsAtom a) (hb : IsAtom b) (hc : IsAtom c) (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) :
    IsSecondaryImplicature (Ici '' {x | x ≠ ⊥}) (Ioi ⊥) (Ici a) := by
  refine isSecondaryImplicature_iff.2 ⟨⟨a, ha.1, rfl⟩, Ici_ssubset_Ioi_bot ha hb hab, ?_⟩
  rintro _ ⟨x, hx, rfl⟩ - hsub
  have hxb : x = b := (hb.le_iff_eq hx).1 (hsub ⟨hb.bot_lt, notMem_Ici_of_isAtom hb ha.1 hab⟩)
  have hxc : x = c := (hc.le_iff_eq hx).1 (hsub ⟨hc.bot_lt, notMem_Ici_of_isAtom hc ha.1 hac⟩)
  exact hbc (hxb.symm.trans hxc)

-- pp. 62–63: the binary parse (32) eliminates one column too many, and (33) symmetrically
theorem union_sdiff_parse (A B C : Set W) :
    ((A ∪ B) ∪ C) \ (((A ∪ B) ∩ C) ∪ ((A ∩ B) ∪ C) ∪ (A ∩ B ∩ C)) =
      ((A ∪ B) \ (A ∩ B)) \ C := by
  ext w
  simp only [mem_sdiff, mem_union, mem_inter_iff]
  tauto

-- contra p. 64: over the closure the text rejects, the weak implicatures give ignorance about every
-- disjunct
theorem notMem_polar_Ici_of_mem_primaryImplicatures (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b)
    {s : Set α} (hq : s ⊆ Ioi ⊥) (hp : s ∈ primaryImplicatures {χ | IsUpperSet χ} (Ioi ⊥)) :
    s ∉ polar (Ici a) := by
  have hweak := mem_primaryImplicatures.1 hp
  refine fun h ↦ (Question.mem_polar.1 h).elim
    (hweak _ (isUpperSet_Ici a) (Ici_ssubset_Ioi_bot ha hb hab)) fun hna ↦ ?_
  exact hweak _ (isLowerSet_Iic a).compl (compl_Iic_ssubset_Ioi_bot ha) fun y hy hya ↦
    hna hy ((ha.le_iff_eq (mem_Ioi.1 (hq hy)).ne').1 hya).ge

variable [IsAtomic α]

private theorem exists_isAtom_le {y : α} (hy : y ∈ Ioi ⊥) : ∃ b, IsAtom b ∧ b ≤ y :=
  (eq_bot_or_exists_atom_le y).resolve_left (mem_Ioi.1 hy).ne'

-- contra p. 64: over alternatives closed under conjunction and disjunction, an alternative passes
-- the consistency check just when it holds in no world in which only one disjunct does
theorem isSecondaryImplicature_upperSets_iff :
    IsSecondaryImplicature {χ | IsUpperSet χ} (Ioi ⊥) t ↔
      IsUpperSet t ∧ t ⊂ Ioi ⊥ ∧ ∀ x, IsAtom x → x ∉ t := by
  rw [isSecondaryImplicature_iff]
  refine and_congr_right fun _ ↦ and_congr_right fun _ ↦
    ⟨fun h x hx hxt ↦ ?_, fun h χ hχ hχφ hsub ↦ ?_⟩
  · exact h _ (isLowerSet_Iic x).compl (compl_Iic_ssubset_Ioi_bot hx)
      fun y hy hle ↦ hy.2 ((hx.le_iff_eq (mem_Ioi.1 hy.1).ne').1 hle ▸ hxt)
  · exact hχφ.2 fun y hy ↦
      let ⟨b, hb, hby⟩ := exists_isAtom_le hy
      hχ hby (hsub ⟨hb.bot_lt, h b hb⟩)

/-- Closing the alternatives of a long disjunction under conjunction and under disjunction, and
strengthening wherever Competence is consistent, yields exactly the exclusive reading. -/
theorem Ioi_sdiff_sUnion_isSecondaryImplicature_eq_setOf_isAtom :
    Ioi ⊥ \ ⋃₀ {t | IsSecondaryImplicature {χ | IsUpperSet χ} (Ioi ⊥) t} = {x : α | IsAtom x} := by
  ext x
  simp only [mem_sdiff, mem_Ioi, mem_sUnion, mem_ofPred_eq, isSecondaryImplicature_upperSets_iff]
  refine ⟨fun ⟨hx, hn⟩ ↦ ?_, fun hx ↦ ⟨hx.bot_lt, fun ⟨t, ⟨_, _, h⟩, hxt⟩ ↦ h x hx hxt⟩⟩
  by_contra hna
  obtain ⟨b, hb, hbx⟩ := exists_isAtom_le hx
  refine hn ⟨Ici x, ⟨isUpperSet_Ici x, ⟨fun _ hy ↦ hx.trans_le hy, fun h ↦ ?_⟩, fun y hy hxy ↦ ?_⟩,
    le_rfl⟩
  · exact hna (le_antisymm hbx (h hb.bot_lt) ▸ hb)
  · exact hna ((hy.le_iff_eq hx.ne').1 hxy ▸ hy)

end LongDisjunction

/-! ### Intentions first

Alternatives are sentences (pp. 29, 112), so complexity can be read off them. A speaker's state is
the set of worlds compatible with what the speaker believes, and `may` quantifies over it. -/

/-- The sentences of the examples of Chapter 6, over atomic clauses `P`. -/
inductive Sentence (P : Type*) where
  | atom : P → Sentence P
  | neg : Sentence P → Sentence P
  | or : Sentence P → Sentence P → Sentence P
  | and : Sentence P → Sentence P → Sentence P
  | may : Sentence P → Sentence P

namespace Sentence

variable {P : Type*} {V : P → Set W} {x y a b c u : Sentence P} {p q : P}

/-- The number of nodes of a sentence, a first approximation to its complexity. -/
def size : Sentence P → ℕ
  | atom _ => 1
  | neg x => x.size + 1
  | or x y | and x y => x.size + y.size + 1
  | may x => x.size + 1

/-- The worlds at which a sentence is true, given the valuation of its atomic clauses and the
state `s` that `may` quantifies over. -/
def eval (V : P → Set W) (s : Set W) : Sentence P → Set W
  | atom p => V p
  | neg x => (eval V s x)ᶜ
  | or x y => eval V s x ∪ eval V s y
  | and x y => eval V s x ∩ eval V s y
  | may x => {_w | (s ∩ eval V s x).Nonempty}

/-- $\mathrm{Bel}_S$: a speaker in state `s` believes the sentence. -/
def Believes (V : P → Set W) (s : Set W) (x : Sentence P) : Prop := s ⊆ x.eval V s

/-- $\mathrm{Poss}_S$: a speaker in state `s` considers what the sentence says possible. -/
def Poss (V : P → Set W) (s : Set W) (x : Sentence P) : Prop := (s ∩ x.eval V s).Nonempty

theorem poss_of_believes (hs : s.Nonempty) (h : x.Believes V s) : x.Poss V s :=
  let ⟨w, hw⟩ := hs
  ⟨w, hw, h hw⟩

theorem believes_may (hs : s.Nonempty) : (may x).Believes V s ↔ x.Poss V s :=
  ⟨fun h ↦ let ⟨_, hw⟩ := hs; h hw, fun h _ _ ↦ h⟩

theorem poss_neg : (neg x).Poss V s ↔ ¬ x.Believes V s := by
  simp [Poss, Believes, eval, inter_compl_nonempty_iff]

theorem not_poss_neg : ¬ (neg x).Poss V s ↔ x.Believes V s := by rw [poss_neg, not_not]

theorem poss_or : (or x y).Poss V s ↔ x.Poss V s ∨ y.Poss V s := by
  simp only [Poss, eval, inter_union_distrib_left, union_nonempty]

/-- The Standard Recipe's weak implicatures with Quality: the consistent states that believe the
sentence uttered and none of the alternatives `alts`. -/
def standardRecipe (V : P → Set W) (x : Sentence P) (alts : Set (Sentence P)) : Set (Set W) :=
  {s | s.Nonempty ∧ x.Believes V s ∧ ∀ a ∈ alts, ¬ a.Believes V s}

-- (11), steps i–iv of p. 110: for a plain disjunction the Standard Recipe delivers ignorance
theorem poss_of_mem_standardRecipe_or
    (hs : s ∈ standardRecipe V (or (atom p) (atom q)) {atom p, atom q}) :
    (atom p).Poss V s ∧ (atom q).Poss V s :=
  ⟨inter_nonempty_of_subset_union hs.2.1 (hs.2.2 (atom q) (by simp)),
    inter_nonempty_of_subset_union (fun _ hw ↦ (hs.2.1 hw).symm) (hs.2.2 (atom p) (by simp))⟩

/-- Under *may*, the same reasoning leaves the speaker no consistent state at all: the Standard
Recipe's weak implicatures contradict what was said. -/
theorem standardRecipe_may_or_eq_empty (p q : P) :
    standardRecipe V (may (or (atom p) (atom q))) {may (atom p), may (atom q)} = ∅ := by
  refine eq_empty_of_forall_notMem fun s ⟨hs, hq, ha⟩ ↦ ?_
  rcases poss_or.1 ((believes_may hs).1 hq) with h | h
  · exact ha _ (by simp) ((believes_may hs).2 h)
  · exact ha _ (by simp) ((believes_may hs).2 h)

/-- The partition of pp. 113–117 by what the speaker considers possible among `x` and `y`, with the
sentence that expresses each cell: `c` for $i_1$, where both are, `a` for $i_2$, where only `x` is,
and `b` for $i_3$, where only `y` is. -/
abbrev cells (V : P → Set W) (x y a b c : Sentence P) : List (Set (Set W) × Sentence P) :=
  [({s | x.Poss V s ∧ y.Poss V s}, c), ({s | x.Poss V s ∧ ¬ y.Poss V s}, a),
    ({s | ¬ x.Poss V s ∧ y.Poss V s}, b)]

variable {κ : Type*} [Preorder κ] {cost : Sentence P → κ}

/-- The alternative heuristic (i): the consistent states that believe the sentence uttered and
could not have expressed their cell by a sentence at most as complex, lower `cost` meaning more
available. -/
def survivors (V : P → Set W) (cost : Sentence P → κ) (u : Sentence P)
    (alts : List (Set (Set W) × Sentence P)) : Set (Set W) :=
  {s | s.Nonempty ∧ u.Believes V s ∧ ∀ c ∈ alts, s ∈ c.1 → ¬ cost c.2 ≤ cost u}

-- `i₂` and `i₃` go by the heuristic, and `i₄` by Quality
theorem mem_survivors_cells_iff (ha : cost a ≤ cost u) (hb : cost b ≤ cost u)
    (hc : ¬ cost c ≤ cost u) (hq : ∀ s, s.Nonempty → u.Believes V s → x.Poss V s ∨ y.Poss V s) :
    s ∈ survivors V cost u (cells V x y a b c) ↔
      s.Nonempty ∧ u.Believes V s ∧ x.Poss V s ∧ y.Poss V s := by
  simp only [survivors, mem_ofPred_eq, List.forall_mem_cons, List.not_mem_nil, false_implies,
    implies_true, and_true]
  refine and_congr_right fun hs ↦ and_congr_right fun hu ↦ ⟨fun ⟨_, h2, h3⟩ ↦ ?_,
    fun ⟨hx, hy⟩ ↦ ⟨fun _ ↦ hc, fun h ↦ absurd hy h.2, fun h ↦ absurd hx h.1⟩⟩
  rcases hq s hs hu with hx | hy
  · exact ⟨hx, by_contra fun hy ↦ h2 ⟨hx, hy⟩ ha⟩
  · exact ⟨by_contra fun hx ↦ h3 ⟨hx, hy⟩ hb, hy⟩

/-- (15), p. 115: *George is British or Canadian*, with the alternatives (16). -/
abbrev altsOr (V : P → Set W) (p q : P) : List (Set (Set W) × Sentence P) :=
  cells V (atom p) (atom q) (atom p) (atom q)
    (and (may (atom p)) (and (may (atom q)) (or (atom p) (atom q))))

/-- (17), p. 117: *George may be British or Canadian*, with the alternatives (18). For the
performative (19), p. 118, a state is what the speaker permits. -/
abbrev altsMayOr (V : P → Set W) (p q : P) : List (Set (Set W) × Sentence P) :=
  cells V (atom p) (atom q) (may (atom p)) (may (atom q)) (and (may (atom p)) (may (atom q)))

/-- (13), p. 112: *many of the nurses were drunk*, with the alternatives (14), p. 113: `x` in the
cell of believing `x`, `u` and not `x` in that of believing its negation, and `u` and maybe `x` in
that of no opinion. The three-way partition of p. 113 is the partition by what is possible, among
`x` and its negation, since only the inconsistent state considers neither possible. The last two
alternatives have the same size, as p. 122 says of (22). -/
abbrev altsScalar (V : P → Set W) (u x : Sentence P) : List (Set (Set W) × Sentence P) :=
  cells V x (neg x) x (and u (neg x)) (and u (may x))

-- p. 115: the speaker of (15) considers both disjuncts possible
theorem mem_survivors_or_iff :
    s ∈ survivors V size (or (atom p) (atom q)) (altsOr V p q) ↔
      s.Nonempty ∧ s ⊆ V p ∪ V q ∧ (atom p).Poss V s ∧ (atom q).Poss V s :=
  mem_survivors_cells_iff (by simp [size]) (by simp [size]) (by simp [size])
    fun _ hs hu ↦ poss_or.1 (poss_of_believes hs hu)

/-- Free choice: of the speakers of *George may be British or Canadian*, those that survive the
alternative heuristic are just the consistent ones that believe *may* of each disjunct, the very
alternatives the Standard Recipe has them not believe. -/
theorem mem_survivors_may_or_iff :
    s ∈ survivors V size (may (or (atom p) (atom q))) (altsMayOr V p q) ↔
      s.Nonempty ∧ (may (atom p)).Believes V s ∧ (may (atom q)).Believes V s := by
  rw [mem_survivors_cells_iff (by simp [size]) (by simp [size]) (by simp [size])
    fun _ hs hu ↦ poss_or.1 ((believes_may hs).1 hu)]
  refine and_congr_right fun hs ↦ ?_
  simp only [believes_may hs]
  exact ⟨fun ⟨_, h⟩ ↦ h, fun h ↦ ⟨poss_or.2 (.inl h.1), h⟩⟩

/-- The alternative heuristic is sensitive to form: a speaker's saying `u` rules out that the
speaker believes `x` just when `x` is no more complex than `u`. -/
theorem mem_survivors_scalar_iff :
    s ∈ survivors V size u (altsScalar V u x) ↔
      s.Nonempty ∧ u.Believes V s ∧ (x.size ≤ u.size → ¬ x.Believes V s) := by
  simp only [survivors, mem_ofPred_eq, List.forall_mem_cons, List.not_mem_nil, false_implies,
    implies_true, and_true, not_poss_neg]
  refine and_congr_right fun hs ↦ and_congr_right fun _ ↦
    ⟨fun ⟨_, h, _⟩ hle hb ↦ h ⟨poss_of_believes hs hb, hb⟩ hle, fun h ↦ ⟨fun _ ↦ ?_,
      fun hb hle ↦ h hle hb.2, fun _ ↦ ?_⟩⟩ <;> simp only [size] <;> omega

-- (23), p. 122: once previous use makes (22a) as available as what was said, the state of believing
-- *not all* goes too and no opinion is left
theorem mem_survivors_of_available (ha : cost x ≤ cost u) (hb : cost (and u (neg x)) ≤ cost u)
    (hc : ¬ cost (and u (may x)) ≤ cost u) :
    s ∈ survivors V cost u (altsScalar V u x) ↔
      s.Nonempty ∧ u.Believes V s ∧ x.Poss V s ∧ (neg x).Poss V s :=
  mem_survivors_cells_iff ha hb hc fun s hs _ ↦
    let ⟨w, hw⟩ := hs
    (em (w ∈ x.eval V s)).imp (⟨w, hw, ·⟩) (⟨w, hw, ·⟩)

end Sentence

open Sentence

/-! ### Conventionalism -/

section Conventionalism

open Quantifier Quantifier.Det GeurtsPouscoulous2009 Exhaustification

private theorem someNotAllC_subset (R : Situation) : someNotAllC R ⊆ someC R := fun _ h ↦ h.1

/-- Enhanced lexicalism prefers the upper-bounded reading of (62): in its weak version (33) provided
this strengthens the sentence, just under the upward-entailing quantifiers, and in its strong
version (32) unless it weakens the sentence, which adds the non-monotone *exactly two*. -/
theorem readings_ssubset_iff (q : Quant) :
    (localReading q ⊂ classicalReading q ↔ PredictsLocalSIWeak (q.sem : Det (Fin 3))) ∧
      (¬ classicalReading q ⊂ localReading q ↔ PredictsLocalSI (q.sem : Det (Fin 3))) := by
  have up {r : Quant} {t : Trial} (hw : PredictsLocalSIWeak (r.sem : Det (Fin 3)))
      (hs : PredictsLocalSI (r.sem : Det (Fin 3))) (hc : Classical r t) (hl : ¬ Local r t) :
      (localReading r ⊂ classicalReading r ↔ PredictsLocalSIWeak (r.sem : Det (Fin 3))) ∧
        (¬ classicalReading r ⊂ localReading r ↔ PredictsLocalSI (r.sem : Det (Fin 3))) :=
    ⟨iff_of_true ⟨fun R hR ↦ hw univ (someNotAllC_subset R) hR, fun h ↦ hl (h hc)⟩ hw,
      iff_of_true (fun h ↦ hl (h.1 hc)) hs⟩
  have down {r : Quant} {t : Trial} (hw : ¬ PredictsLocalSIWeak (r.sem : Det (Fin 3)))
      (hs : ¬ PredictsLocalSI (r.sem : Det (Fin 3))) (hc : ¬ Classical r t) (hl : Local r t) :
      (localReading r ⊂ classicalReading r ↔ PredictsLocalSIWeak (r.sem : Det (Fin 3))) ∧
        (¬ classicalReading r ⊂ localReading r ↔ PredictsLocalSI (r.sem : Det (Fin 3))) :=
    ⟨iff_of_false (fun h ↦ hc (h.1 hl)) hw, iff_of_false (not_not.2
      ⟨fun R hR ↦ not_not.1 hs univ (someNotAllC_subset R) hR, fun h' ↦ hc (h' hl)⟩) hs⟩
  cases q with
  | all => exact up all_predictsLocalSIWeak all_predictsLocalSI classical_all not_local_all
  | moreThanOne =>
    exact up moreThanOne_predictsLocalSIWeak moreThanOne_predictsLocalSI classical_moreThanOne
      not_local_moreThanOne
  | exactlyTwo =>
    exact ⟨iff_of_false (fun h ↦ not_classical_exactlyTwo_b (h.1 local_exactlyTwo_b))
        exactlyTwo_not_predictsLocalSIWeak,
      iff_of_true (fun h ↦ not_local_exactlyTwo_a (h.1 classical_exactlyTwo_a))
        exactlyTwo_predictsLocalSI⟩
  | notAll =>
    exact down notAll_not_predictsLocalSIWeak notAll_not_predictsLocalSI not_classical_notAll
      local_notAll
  | notMoreThanOne =>
    exact down notMoreThanOne_not_predictsLocalSIWeak notMoreThanOne_not_predictsLocalSI
      not_classical_notMoreThanOne local_notMoreThanOne

variable {some all : Set W}

-- (47), (57), pp. 150, 156–157, with O of (39) as `exh`: the Power Principle prefers the
-- narrow-scope parse (57b) of (56b), which yields the inference the text says does not go through.
-- That it is the stronger needs a serial relation, which the text leaves tacit
theorem isLeast_readings_core (R : SetRel W W) [ModalLogic.IsSerial R] (ha : all ⊂ some) :
    IsLeast {R.core some, exh {R.core some, R.core all} (R.core some),
        R.core (exh {some, all} some)} (R.core (exh {some, all} some)) := by
  have hcore : R.core (some \ all) ⊆ R.core some := fun _ hw _ hv ↦ (hw hv).1
  rw [exh_insert_of_subset (p := some) subset_rfl, exh_singleton_of_not_subset ha.2]
  refine ⟨by simp, ?_⟩
  rintro _ (rfl | rfl | rfl)
  · exact hcore
  · refine fun w hw ↦ ⟨hcore hw, ?_⟩
    rintro q (rfl | rfl) hwq
    · exact subset_rfl
    · obtain ⟨v, hv⟩ := ModalLogic.IsSerial.serial (R := R) w
      exact absurd (hwq hv) (hw hv).2
  · exact subset_rfl

end Conventionalism

/-! ### Embedded implicatures -/

section Embedded

variable {M A F : Set W}

-- §8.1, (6)–(8), pp. 166–167: the implicature *not all the figs* passes the consistency check
theorem isSecondaryImplicature_mango (hA : A ⊆ F) (hM : (M \ F).Nonempty)
    (hF : (F \ (M ∪ A)).Nonempty) : IsSecondaryImplicature {M, F, A, M ∪ A} (M ∪ F) A := by
  obtain ⟨f, hf, hfn⟩ := hF
  obtain ⟨m, hm, hmn⟩ := hM
  simp only [mem_union, not_or] at hfn
  have hfd : f ∈ (M ∪ F) \ A := ⟨.inr hf, hfn.2⟩
  have hmd : m ∈ (M ∪ F) \ A := ⟨.inl hm, fun h ↦ hmn (hA h)⟩
  refine isSecondaryImplicature_iff.2
    ⟨by simp, ⟨fun _ hw ↦ .inr (hA hw), fun h ↦ hfn.2 (h hfd.1)⟩, ?_⟩
  rintro χ (rfl | rfl | rfl | rfl) - h
  · exact hfn.1 (h hfd)
  · exact hmn (h hmd)
  · exact hfn.2 (h hfd)
  · exact (h hfd).elim hfn.1 hfn.2

-- §8.1: Competence fails for (7a), (7b) and (7d), so no strong implicature that Cleo had no mango
theorem isSecondaryImplicature_mango_iff (hA : A ⊆ F) (hM : (M \ F).Nonempty)
    (hF : (F \ (M ∪ A)).Nonempty) {χ : Set W} (hχ : χ ∈ ({M, F, A, M ∪ A} : Set (Set W))) :
    IsSecondaryImplicature {M, F, A, M ∪ A} (M ∪ F) χ ↔ χ = A := by
  have hFφ : F ⊂ M ∪ F := ⟨subset_union_right, fun h ↦
    let ⟨_, hw, hwF⟩ := hM; hwF (h (.inl hw))⟩
  have hMφ : M ⊂ M ∪ F := ⟨subset_union_left, fun h ↦
    let ⟨_, hw, hn⟩ := hF; hn (.inl (h (.inr hw)))⟩
  refine ⟨fun h ↦ ?_, fun h ↦ by subst h; exact isSecondaryImplicature_mango hA hM hF⟩
  have hb := (isSecondaryImplicature_iff.1 h).2.2
  rcases hχ with rfl | rfl | rfl | rfl
  · exact absurd (fun w hw ↦ hw.1.resolve_left hw.2) (hb _ (by simp) hFφ)
  · exact absurd (fun w hw ↦ hw.1.resolve_right hw.2) (hb _ (by simp) hMφ)
  · rfl
  · exact absurd (fun w hw ↦ hw.1.resolve_left fun hwM ↦ hw.2 (.inl hwM)) (hb _ (by simp) hFφ)

open GeurtsPouscoulous2009 in
-- §8.2, (10)–(12), pp. 168–169, after [vanrooij-schulz-2004] and [russell-2006]: the reading of (9)
-- that looks local, from the strong implicature at the speaker and Competence of the subject. The
-- step for *hope*, (15)–(17), pp. 170–171, has the same form and differs in the plausibility of
-- (16)
theorem subset_core_exh {R : SetRel W W} {some all : Set W} (hall : all ⊂ some)
    (hq : s ⊆ R.core some) (h10 : s ⊆ (R.core all)ᶜ) (h11 : s ⊆ R.core all ∪ R.core allᶜ) :
    s ⊆ R.core (Exhaustification.exh {some, all} some) :=
  fun _ hw ↦ local_of_global_of_opinionated R hall (hq hw) (h10 hw) (h11 hw)

section Indefinites

variable {D : Type*} {sailor some all : W → Set D} {t : SetRel W D}

-- (32)–(35), pp. 179–180: the state of (32) is a relation between worlds and values of the
-- discourse referent, which the hearer's question is about, and the Standard Recipe runs as usual:
-- (34) with Competence about the referent gives the model (35)
theorem subset_inter_compl_ofSuccessors
    (h32 : t ⊆ SetRel.ofSuccessors sailor ∩ SetRel.ofSuccessors some)
    (h34 : ¬ t ⊆ SetRel.ofSuccessors all) (hc : t ∈ polar (SetRel.ofSuccessors all)) :
    t ⊆ SetRel.ofSuccessors sailor ∩ SetRel.ofSuccessors some ∩ (SetRel.ofSuccessors all)ᶜ :=
  subset_inter h32 ((Question.mem_polar.1 hc).resolve_left h34)

end Indefinites

end Embedded

/-! ### The judgments -/

section Rows

open GeurtsPouscoulous2009

/-- The Horn set of Table 2, in order of increasing strength. -/
def quantifierTable : List (String × Fin 4) := [("some", 0), ("many", 1), ("most", 2), ("all", 3)]

/-- A row of Table 2: the polarity of the frame, the quantifier filling it and the predicted
alternatives. -/
structure Table2Row where
  polarity : Polarity
  quantifier : Fin 4
  alternatives : List (Fin 4)
  deriving DecidableEq

/-- Reads a row of Table 2. -/
def Table2Row.ofDatum (ex : Datum) : Option Table2Row := do
  let polarity ← ex.parse? "negated" [("false", Polarity.positive), ("true", .negative)]
  let quantifier ← ex.parse? "quantifier" quantifierTable
  pure ⟨polarity, quantifier, (ex.features "alternative").filterMap (List.lookup · quantifierTable)⟩

example : Datum.ReadCount Table2Row.ofDatum Examples.all 8 := by decide

-- Table 2: the alternatives printed are those of the definition (24) by Horn sets, on which a
-- sentence is an alternative iff it is stronger, for any strictly stronger meanings of the four
-- quantifiers. The reversal under negation is among sentences; the meanings keep their order, and
-- the ordering a Horn scale (4), p. 51, would impose plays no part (pp. 57–59)
theorem rows_table2 {a : Fin 4 → Set W} (ha : StrictAnti a) :
    ∀ r ∈ Examples.all.filterMap Table2Row.ofDatum, ∀ k,
      k ∈ r.alternatives ↔ r.polarity • a k ⊂ r.polarity • a r.quantifier := by
  have key : ∀ r ∈ Examples.all.filterMap Table2Row.ofDatum, ∀ k, k ∈ r.alternatives ↔
      if r.polarity = .positive then r.quantifier < k else k < r.quantifier := by decide
  intro r hr k
  rw [key r hr k]
  rcases r.polarity with _ | _
  · simpa using ha.lt_iff_gt.symm
  · simpa using (compl_lt_compl_iff_lt.trans ha.lt_iff_gt).symm

/-- The three contrasts on which Gricean reasoning derives one inference and not its neighbour. -/
inductive Item where
  | sameLength | longer | figs | mango | referent | everySailor
  deriving DecidableEq

/-- The statement that the theory derives the inference, over any model of the sentence. -/
def Item.Derived : Item → Prop
  | .sameLength => ∀ {W : Type} (V : Bool → Set W) (s : Set W),
      s ∈ survivors V size (atom true) (altsScalar V (atom true) (atom false)) →
        ¬ (atom false).Believes V s
  | .longer => ∀ {W : Type} (V : Bool → Set W) (s : Set W),
      s ∈ survivors V size (atom true) (altsScalar V (atom true) (and (atom false) (atom true))) →
        ¬ (and (atom false) (atom true)).Believes V s
  | .figs => ∀ {W : Type} (M F A : Set W), A ⊆ F → (M \ F).Nonempty → (F \ (M ∪ A)).Nonempty →
      IsSecondaryImplicature {M, F, A, M ∪ A} (M ∪ F) A
  | .mango => ∀ {W : Type} (M F A : Set W), A ⊆ F → (M \ F).Nonempty → (F \ (M ∪ A)).Nonempty →
      IsSecondaryImplicature {M, F, A, M ∪ A} (M ∪ F) M
  | .referent => ∀ {W D : Type} (sailor some all : W → Set D) (t : SetRel W D),
      t ⊆ SetRel.ofSuccessors sailor ∩ SetRel.ofSuccessors some → ¬ t ⊆ SetRel.ofSuccessors all →
        t ∈ polar (SetRel.ofSuccessors all) → t ⊆ (SetRel.ofSuccessors all)ᶜ
  | .everySailor => ∀ {W D : Type} (sailor all : W → Set D) (t : SetRel W D),
      t ⊆ SetRel.ofSuccessors sailor → t ⊆ (SetRel.ofSuccessors all)ᶜ →
        t ⊆ Prod.fst ⁻¹' (SetRel.ofSuccessors (sailor ⊓ all)).dom ᶜ

theorem Item.derived_iff : ∀ i : Item, i.Derived ↔ i ∉ [Item.longer, .mango, .everySailor]
  | .sameLength => iff_of_true (fun _ _ h ↦ (mem_survivors_scalar_iff.1 h).2.2 le_rfl) (by decide)
  -- (26b), p. 124: *big toe* is longer than *toe*, so that nothing rules out believing it
  | .longer => iff_of_false (fun h ↦ @h Unit (fun _ ↦ univ) univ
      (mem_survivors_scalar_iff.2 ⟨univ_nonempty, fun _ _ ↦ mem_univ _, by simp [size]⟩)
      fun _ _ ↦ ⟨mem_univ _, mem_univ _⟩) (by decide)
  | .figs => iff_of_true (fun _ _ _ ↦ isSecondaryImplicature_mango) (by decide)
  -- (3), p. 165: Competence is not consistent for the first disjunct
  | .mango => iff_of_false (fun h ↦ by
      have hA : ({2} : Set (Fin 3)) ⊆ {1, 2} := by simp
      have hM : (({0} : Set (Fin 3)) \ {1, 2}).Nonempty := ⟨0, by simp⟩
      have hF : (({1, 2} : Set (Fin 3)) \ ({0} ∪ {2})).Nonempty := ⟨1, by simp⟩
      have := (isSecondaryImplicature_mango_iff hA hM hF (by simp)).1
        (@h (Fin 3) {0} {1, 2} {2} hA hM hF)
      exact absurd (mem_singleton_iff.1 (this ▸ mem_singleton (0 : Fin 3))) (by decide)) (by decide)
  | .referent => iff_of_true (fun _ _ _ _ h32 h34 hc ↦
      (subset_inter_compl_ofSuccessors h32 h34 hc).trans inter_subset_right) (by decide)
  -- pp. 139, 180: (35) does not entail that (14) is false: the story need not be about every sailor
  | .everySailor => iff_of_false (fun h ↦ by
      have := @h Unit Bool (fun _ ↦ univ) (fun _ ↦ {true}) {((), false)}
        (fun _ _ ↦ mem_univ _) (by rintro _ rfl hb; simp [SetRel.ofSuccessors] at hb)
      exact this rfl ⟨true, mem_univ _, rfl⟩) (by decide)

/-- Reads the item of a row and whether the text says the inference is conveyed. -/
def inference? (ex : Datum) : Option (Item × Bool) := do
  let item ← ex.parse? "item" [("sameLength", Item.sameLength), ("longer", .longer),
    ("figs", .figs), ("mango", .mango), ("referent", .referent), ("everySailor", .everySailor)]
  let conveys ← ex.bool? "conveys"
  pure (item, conveys)

example : Datum.ReadCount inference? Examples.all 7 := by decide

-- (13), (26), (6), (3), (31), (29): the theory derives what the text says is conveyed, and not its
-- neighbour
theorem rows_conveys : ∀ r ∈ Examples.all.filterMap inference?, (r.2 = true ↔ r.1.Derived) := by
  simp only [Item.derived_iff]
  decide

/-- Reads the quantifier of a row of (61) and whether the inference is conveyed. -/
def quantifierRow? (ex : Datum) : Option (Quant × Bool) := do
  let q ← ex.parse? "quantifier" [("all", Quant.all), ("moreThanOne", .moreThanOne),
    ("exactlyTwo", .exactlyTwo)]
  let conveys ← ex.bool? "conveys"
  pure (q, conveys)

example : Datum.ReadCount quantifierRow? Examples.all 3 := by decide

-- (61), p. 158: (32) prefers the upper-bounded reading of each sentence, and the text says that
-- none of these inferences goes through
theorem rows_61 : ∀ r ∈ Examples.all.filterMap quantifierRow?,
    ¬ classicalReading r.1 ⊂ localReading r.1 ∧ r.2 = false := by
  have h (q : Quant) := (readings_ssubset_iff q).2
  simp only [h, Quant.predictsLocalSI_iff]
  decide

/-- Reads whether the inference of a row of (56) is conveyed. -/
def attitudeRow? (ex : Datum) : Option Bool :=
  (ex.feature? "attitude").bind fun _ ↦ ex.bool? "conveys"

example : Datum.ReadCount attitudeRow? Examples.all 3 := by decide

-- (56), pp. 156–157: the Power Principle prefers the parse (57b) that yields each inference, and
-- the text calls that prediction plain false
theorem rows_56 (R : SetRel W W) [ModalLogic.IsSerial R] {some all : Set W} (ha : all ⊂ some) :
    ∀ r ∈ Examples.all.filterMap attitudeRow?,
      IsLeast {R.core some, Exhaustification.exh {R.core some, R.core all} (R.core some),
        R.core (Exhaustification.exh {some, all} some)}
          (R.core (Exhaustification.exh {some, all} some)) ∧ r = false := by
  have key : ∀ r ∈ Examples.all.filterMap attitudeRow?, r = false := by decide
  exact fun r hr ↦ ⟨isLeast_readings_core R ha, key r hr⟩

end Rows

end Geurts2010
