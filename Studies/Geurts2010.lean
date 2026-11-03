module

public import Studies.GeurtsPouscoulous2009
public import Linglib.Pragmatics.NeoGricean.Basic
public import Linglib.Semantics.Exhaustification.Basic
public import Linglib.Data.Examples.Geurts2010
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Order.Atoms
public import Mathlib.Order.Minimal
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
upward-entailing scopes](##boundedReading_ssubset_iff), where the experiment finds no upper bound.

## Implementation notes

* A state is the worlds compatible with the speaker's beliefs. `may` quantifies over it, which
  builds in footnote 5 of p. 111.
* `IsSecondaryImplicature` serves as the necessary condition on Competence of p. 41, per
  alternative; strengthening wherever it holds is an assumption made here, the book's Recipe being
  a heuristic.
* `Sentence.survivors` applies heuristic (i) categorically, with one alternative per cell and `size`
  for economy, so (26b) comes out by length rather than the monolexicality p. 124 credits.
* Upper sets are the closure of the disjuncts under conjunction and disjunction ([each is a union of
  conjunctions](##eq_iUnion_iInter_of_isUpperSet)).
* The alternatives of (20), p. 120, are reconstructed; (61b, c) are read through the quantifiers of
  (62).

## Errata

* pp. 63–64: with three disjuncts (35) gives only non-belief in `x`, since [believing it false stays
  consistent](##isSecondaryImplicature_Ici).
* p. 64: closure under disjunction does not repeat the trouble of (32): [only alternatives false
  wherever just one disjunct holds pass](##isSecondaryImplicature_upperSets_iff), and it [gives
  ignorance](##notMem_polar_Ici_of_mem_primaryImplicatures).
* p. 115: "American" for British.
* p. 143: (25) should end [*or we love it*](##compl_sdiff_like).
* p. 149: (42b) is [*some but not many*](##exh_compl_many), not "many but not all".
* p. 168: (9a) for (9).
* pp. 169–170: (11) and (16) put the disjunction outside the belief, [harmlessly given (10) or
  (15)](##subset_or_subset_iff).
* p. 188: (46) omits *not*.
* p. 189: [O reaches RICH₂ given RICH₁](##exh_rich), so "out of reach" overstates.

## TODO

* §8.3 presupposition implicatures, §6.6 open alternatives, and Spector's route (pp. 169–170,
  [spector-2006]).
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

/-- Soames's Competence⁺ (12), p. 37: the speaker's beliefs agree with the facts at `w`. -/
def CompetentPlus (w : W) (s ψ : Set W) : Prop := (w ∈ ψ → s ⊆ ψ) ∧ (w ∉ ψ → s ⊆ ψᶜ)

-- p. 38
theorem CompetentPlus.mem_polar {w : W} (h : CompetentPlus w s ψ) : s ∈ polar ψ :=
  Question.mem_polar.2 ((em (w ∈ ψ)).imp h.1 h.2)

-- p. 38, Travis, who has an opinion on everything regardless of the facts
theorem not_competentPlus_of_subset {w : W} (hs : s.Nonempty) (hw : w ∉ ψ) (h : s ⊆ ψ) :
    ¬ CompetentPlus w s ψ := fun hc ↦
  let ⟨_, hv⟩ := hs
  hc.2 hw hv (h hv)

-- the diagram of p. 39: non-belief is disbelief or no opinion, no opinion being non-competence
theorem compl_Iic_eq_union (ψ : Set W) :
    (Iic ψ)ᶜ = (Iic ψᶜ \ {∅}) ∪ (polar ψ : Set (Set W))ᶜ := by
  rw [← compl_Iic_inter_polar]
  ext s
  simp only [mem_union, mem_inter_iff, mem_compl_iff, mem_Iic, SetLike.mem_coe, mem_polar]
  tauto

-- p. 40: (16) and (17) exclude each other, so (16) cannot come from strengthening (17)
theorem disjoint_Iic_compl_polar (ψ : Set W) :
    Disjoint (Iic ψᶜ) (polar ψ : Set (Set W))ᶜ :=
  disjoint_left.2 fun _ h hc ↦ hc (mem_polar.2 (.inr h))

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

-- p. 120: what is possible and on which the speaker has an opinion, the speaker believes
theorem subset_of_inter_nonempty_of_mem_polar (hp : (s ∩ ψ).Nonempty) (hc : s ∈ polar ψ) :
    s ⊆ ψ :=
  (mem_polar.1 hc).resolve_right fun h ↦ let ⟨_, hw, hwψ⟩ := hp; h hw hwψ

-- p. 54: the Horn scale (4) makes (10) an alternative to (9), but (9) entails (10), so that the
-- weak implicature contradicts Quality
theorem Iic_inter_compl_Iic_eq_empty {ι : Type*} [Preorder ι] {E : Set W → Set W} {a : ι → Set W}
    {i j : ι} (hE : Antitone E) (ha : Antitone a) (h : i ≤ j) :
    Iic (E (a i)) ∩ (Iic (E (a j)))ᶜ = ∅ :=
  eq_empty_of_forall_notMem fun _ hs ↦ hs.2 (subset_trans hs.1 (hE (ha h)))

/-! ### Long disjunctions

The worlds of (29) are ordered by what they make true. A world with `⊥` below it is one in which no
disjunct holds, so the long disjunction (31) is `Ioi ⊥`; the conjunction of the disjuncts below `x`
is `Ici x`, and a world in which just one disjunct holds is an atom. -/

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
    IsSecondaryImplicature (Ioi ⊥) (Ici '' {x | x ≠ ⊥}) (Ici a) := by
  refine isSecondaryImplicature_iff.2 ⟨⟨a, ha.1, rfl⟩, Ici_ssubset_Ioi_bot ha hb hab, ?_⟩
  rintro _ ⟨x, hx, rfl⟩ - hsub
  have hxb : x = b := (hb.le_iff_eq hx).1 (hsub ⟨hb.bot_lt, notMem_Ici_of_isAtom hb ha.1 hab⟩)
  have hxc : x = c := (hc.le_iff_eq hx).1 (hsub ⟨hc.bot_lt, notMem_Ici_of_isAtom hc ha.1 hac⟩)
  exact hbc (hxb.symm.trans hxc)

-- (32), p. 62: over the alternatives of the parse (A ∨ B) ∨ C, the strong implicature of (32b)
-- goes through, which rules out the world in which only C holds
theorem isSecondaryImplicature_parse (ha : IsAtom a) (hb : IsAtom b) (hc : IsAtom c) (hab : a ≠ b)
    (hac : a ≠ c) :
    IsSecondaryImplicature (Ioi ⊥)
      {(Ici a ∪ Ici b) ∩ Ici c, (Ici a ∩ Ici b) ∪ Ici c, Ici a ∩ Ici b ∩ Ici c}
      ((Ici a ∩ Ici b) ∪ Ici c) := by
  have hb' : a ∉ Ici b := notMem_Ici_of_isAtom ha hb.1 hab.symm
  have hc' : a ∉ Ici c := notMem_Ici_of_isAtom ha hc.1 hac.symm
  have hψ : a ∉ (Ici a ∩ Ici b) ∪ Ici c := by rintro (h | h); exacts [hb' h.2, hc' h]
  refine isSecondaryImplicature_iff.2 ⟨by simp, ⟨?_, fun h ↦ hψ (h ha.bot_lt)⟩, ?_⟩
  · rintro y (h | h)
    exacts [ha.bot_lt.trans_le h.1, hc.bot_lt.trans_le h]
  · have hsdiff : a ∈ Ioi ⊥ \ ((Ici a ∩ Ici b) ∪ Ici c) := ⟨ha.bot_lt, hψ⟩
    rintro χ (rfl | rfl | rfl) - h
    exacts [hc' (h hsdiff).2, hψ (h hsdiff), hc' (h hsdiff).2]

-- pp. 62–63: the two binary parses each eliminate one column too many
theorem union_sdiff_parse_left (A B C : Set W) :
    ((A ∪ B) ∪ C) \ (((A ∪ B) ∩ C) ∪ ((A ∩ B) ∪ C) ∪ (A ∩ B ∩ C)) =
      ((A ∪ B) \ (A ∩ B)) \ C := by
  ext w
  simp only [mem_sdiff, mem_union, mem_inter_iff]
  tauto

theorem union_sdiff_parse_right (A B C : Set W) :
    (A ∪ (B ∪ C)) \ ((A ∪ (B ∩ C)) ∪ (A ∩ (B ∪ C)) ∪ (A ∩ (B ∩ C))) =
      ((B ∪ C) \ (B ∩ C)) \ A := by
  ext w
  simp only [mem_sdiff, mem_union, mem_inter_iff]
  tauto

-- contra p. 64: over the closure the text rejects, the weak implicatures give ignorance about every
-- disjunct
theorem notMem_polar_Ici_of_mem_primaryImplicatures (ha : IsAtom a) (hb : IsAtom b) (hab : a ≠ b)
    {s : Set α} (hq : s ⊆ Ioi ⊥) (hp : s ∈ primaryImplicatures (Ioi ⊥) {χ | IsUpperSet χ}) :
    s ∉ polar (Ici a) := by
  have hweak := mem_primaryImplicatures.1 hp
  refine fun h ↦ (Question.mem_polar.1 h).elim
    (hweak _ (isUpperSet_Ici a) (Ici_ssubset_Ioi_bot ha hb hab)) fun hna ↦ ?_
  exact hweak _ (isLowerSet_Iic a).compl (compl_Iic_ssubset_Ioi_bot ha) fun y hy hya ↦
    hna hy ((ha.le_iff_eq (mem_Ioi.1 (hq hy)).ne').1 hya).ge

-- an upper set of the worlds of (29) is a union of conjunctions of disjuncts, so that the upper
-- sets are the closure p. 64 considers
theorem eq_iUnion_iInter_of_isUpperSet {κ : Type*} {u : Set (Set κ)} (hu : IsUpperSet u) :
    u = ⋃ x ∈ u, ⋂ i ∈ x, Ici ({i} : Set κ) := by
  ext w
  simp only [mem_iUnion, mem_iInter, mem_Ici, singleton_subset_iff, exists_prop]
  exact ⟨fun hw ↦ ⟨w, hw, fun _ h ↦ h⟩, fun ⟨x, hx, h⟩ ↦ hu (fun i hi ↦ h i hi) hx⟩

-- p. 61: the only alternative (30) of the substitution method leaves worlds with two disjuncts
example : ({0, 1} : Set (Fin 3)) ∈ Ioi ⊥ \ Ici ⊤ ∧ ¬ IsAtom ({0, 1} : Set (Fin 3)) := by
  refine ⟨⟨bot_lt_iff_ne_bot.2 (insert_nonempty _ _).ne_empty, fun h ↦ ?_⟩, fun h ↦ ?_⟩
  · simpa using h (mem_univ (2 : Fin 3))
  · obtain ⟨i, hi⟩ := Set.isAtom_iff.1 h
    have h0 : (0 : Fin 3) ∈ ({i} : Set (Fin 3)) := hi ▸ (by simp)
    have h1 : (1 : Fin 3) ∈ ({i} : Set (Fin 3)) := hi ▸ (by simp)
    exact absurd (subsingleton_singleton h0 h1) (by decide)

variable [IsAtomic α]

private theorem exists_isAtom_le {y : α} (hy : y ∈ Ioi ⊥) : ∃ b, IsAtom b ∧ b ≤ y :=
  (eq_bot_or_exists_atom_le y).resolve_left (mem_Ioi.1 hy).ne'

-- an upper set with every atom in it holds wherever a disjunct does
private theorem Ioi_bot_subset_of_forall_isAtom_mem {χ : Set α} (hχ : IsUpperSet χ)
    (h : ∀ x, IsAtom x → x ∈ χ) : Ioi ⊥ ⊆ χ := fun _ hy ↦
  let ⟨_, hb, hby⟩ := exists_isAtom_le hy
  hχ hby (h _ hb)

-- contra p. 64: over alternatives closed under conjunction and disjunction, an alternative passes
-- the consistency check just when it holds in no world in which only one disjunct does
theorem isSecondaryImplicature_upperSets_iff :
    IsSecondaryImplicature (Ioi ⊥) {χ | IsUpperSet χ} t ↔
      IsUpperSet t ∧ t ⊂ Ioi ⊥ ∧ ∀ x, IsAtom x → x ∉ t := by
  rw [isSecondaryImplicature_iff]
  refine and_congr_right fun _ ↦ and_congr_right fun _ ↦
    ⟨fun h x hx hxt ↦ ?_, fun h χ hχ hχφ hsub ↦ ?_⟩
  · exact h _ (isLowerSet_Iic x).compl (compl_Iic_ssubset_Ioi_bot hx)
      fun y hy hle ↦ hy.2 ((hx.le_iff_eq (mem_Ioi.1 hy.1).ne').1 hle ▸ hxt)
  · exact hχφ.2 (Ioi_bot_subset_of_forall_isAtom_mem hχ fun b hb ↦ hsub ⟨hb.bot_lt, h b hb⟩)

/-- Closing the alternatives of a long disjunction under conjunction and under disjunction, and
strengthening wherever Competence is consistent, yields exactly the exclusive reading. -/
theorem Ioi_sdiff_sUnion_isSecondaryImplicature_eq_setOf_isAtom :
    Ioi ⊥ \ ⋃₀ {t | IsSecondaryImplicature (Ioi ⊥) {χ | IsUpperSet χ} t} = {x : α | IsAtom x} := by
  ext x
  simp only [mem_sdiff, mem_Ioi, mem_sUnion, mem_ofPred_eq, isSecondaryImplicature_upperSets_iff]
  refine ⟨fun ⟨hx, hn⟩ ↦ ?_, fun hx ↦ ⟨hx.bot_lt, fun ⟨t, ⟨_, _, h⟩, hxt⟩ ↦ h x hx hxt⟩⟩
  by_contra hna
  obtain ⟨b, hb, hbx⟩ := exists_isAtom_le hx
  refine hn ⟨Ici x, ⟨isUpperSet_Ici x, ⟨fun _ hy ↦ hx.trans_le hy, fun h ↦ ?_⟩, fun y hy hxy ↦ ?_⟩,
    le_rfl⟩
  · exact hna (le_antisymm hbx (h hb.bot_lt) ▸ hb)
  · exact hna ((hy.le_iff_eq hx.ne').1 hxy ▸ hy)

-- the exclusive state itself meets the weak implicatures of that closure, so the reading is not
-- vacuous
theorem setOf_isAtom_mem_primaryImplicatures :
    {x : α | IsAtom x} ∈ primaryImplicatures (Ioi ⊥) {χ | IsUpperSet χ} :=
  mem_primaryImplicatures.2 fun _ hχ hχφ hsub ↦
    hχφ.2 (Ioi_bot_subset_of_forall_isAtom_mem hχ fun _ hb ↦ hsub hb)

-- p. 41: that the speaker cannot believe all the disjuncts false holds at any length
theorem eq_empty_of_forall_subset_compl_Ici {s : Set α} (hq : s ⊆ Ioi ⊥)
    (h : ∀ a, IsAtom a → s ⊆ (Ici a)ᶜ) : s = ∅ :=
  eq_empty_of_forall_notMem fun _ hy ↦
    let ⟨_, hb, hby⟩ := exists_isAtom_le (hq hy)
    h _ hb hy hby

example : Ioi ⊥ \ ⋃₀ {t | IsSecondaryImplicature (Ioi ⊥) {χ | IsUpperSet χ} t} =
    {w : Set (Fin 3) | ∃ i, w = {i}} := by
  rw [Ioi_sdiff_sUnion_isSecondaryImplicature_eq_setOf_isAtom]
  exact Set.ext fun _ ↦ Set.isAtom_iff

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

/-- The sentence `x` entails the sentence `y`. -/
def Entails (V : P → Set W) (x y : Sentence P) : Prop := ∀ s, x.Believes V s → y.Believes V s

theorem believes_may (hs : s.Nonempty) : (may x).Believes V s ↔ x.Poss V s :=
  ⟨fun h ↦ let ⟨_, hw⟩ := hs; h hw, fun h _ _ ↦ h⟩

theorem believes_and : (and x y).Believes V s ↔ x.Believes V s ∧ y.Believes V s :=
  subset_inter_iff

theorem believes_neg : (neg x).Believes V s ↔ ¬ x.Poss V s :=
  ⟨fun h ⟨_, hw, hwx⟩ ↦ h hw hwx, fun h w hw hwx ↦ h ⟨w, hw, hwx⟩⟩

theorem poss_neg : (neg x).Poss V s ↔ ¬ x.Believes V s := by
  simp [Poss, Believes, eval, inter_compl_nonempty_iff]

theorem not_poss_neg : ¬ (neg x).Poss V s ↔ x.Believes V s := by rw [poss_neg, not_not]

theorem poss_or : (or x y).Poss V s ↔ x.Poss V s ∨ y.Poss V s := by
  simp only [Poss, eval, inter_union_distrib_left, union_nonempty]

/-- The Standard Recipe's weak implicatures with Quality: the consistent states that believe the
sentence uttered and none of the alternatives `alts`. -/
def standardRecipe (V : P → Set W) (x : Sentence P) (alts : Set (Sentence P)) : Set (Set W) :=
  {s | s.Nonempty ∧ x.Believes V s ∧ ∀ a ∈ alts, ¬ a.Believes V s}

-- on a plain disjunction this is the recipe of `NeoGricean.primaryImplicatures`
theorem mem_standardRecipe_or_iff (hp : V p ⊂ V p ∪ V q) (hq : V q ⊂ V p ∪ V q) :
    s ∈ standardRecipe V (or (atom p) (atom q)) {atom p, atom q} ↔
      s.Nonempty ∧ s ∈ Iic (V p ∪ V q) ∩ primaryImplicatures (V p ∪ V q) {V p, V q} := by
  simp only [standardRecipe, mem_ofPred_eq, mem_inter_iff, mem_primaryImplicatures]
  refine and_congr_right fun _ ↦ and_congr_right fun _ ↦ ?_
  simp only [mem_insert_iff, mem_singleton_iff, forall_eq_or_imp, forall_eq]
  exact ⟨fun ⟨h1, h2⟩ ↦ ⟨fun _ ↦ h1, fun _ ↦ h2⟩, fun ⟨h1, h2⟩ ↦ ⟨h1 hp, h2 hq⟩⟩

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

open Classical in
/-- The sentence a speaker in state `s` could have used to express what the speaker considers
possible, among `x` and `y`: `c` in cell $i_1$, where both are, `a` in $i_2$, where only `x` is, and
`b` in $i_3$, where only `y` is. Cell $i_4$, where neither is, falls with $i_3$; the examples
discard it by Quality or consistency. -/
noncomputable def say (V : P → Set W) (x y a b c : Sentence P) (s : Set W) : Sentence P :=
  if x.Poss V s then (if y.Poss V s then c else a) else b

theorem say_of_poss (hx : x.Poss V s) (hy : y.Poss V s) : say V x y a b c s = c := by
  simp [say, hx, hy]

theorem say_rec {C : Sentence P → Prop} (hc : x.Poss V s → y.Poss V s → C c)
    (ha : x.Poss V s → ¬ y.Poss V s → C a) (hb : ¬ x.Poss V s → C b) :
    C (say V x y a b c s) := by
  unfold say
  split_ifs with h h'
  exacts [hc h h', ha h h', hb h]

/-- The alternatives of pp. 115–116: what a consistent speaker of `u` would say is something the
speaker believes and which entails `u`. -/
def AreAlternatives (V : P → Set W) (u : Sentence P) (say : Set W → Sentence P) : Prop :=
  ∀ s, s.Nonempty → u.Believes V s → (say s).Believes V s ∧ (say s).Entails V u

variable {κ : Type*} [Preorder κ] {cost : Sentence P → κ}

/-- The alternative heuristic (i): the consistent states that believe the sentence uttered and
could not have expressed which cell they are in by a sentence at most as complex. The partition is
the fibres of `say`, and `cost` ranks sentences, lower meaning more available. -/
def survivors (V : P → Set W) (cost : Sentence P → κ) (u : Sentence P)
    (say : Set W → Sentence P) : Set (Set W) :=
  {s | s.Nonempty ∧ u.Believes V s ∧ ¬ cost (say s) ≤ cost u}

theorem mem_survivors_say_iff (ha : cost a ≤ cost u) (hb : cost b ≤ cost u)
    (hc : ¬ cost c ≤ cost u) :
    s ∈ survivors V cost u (say V x y a b c) ↔
      s.Nonempty ∧ u.Believes V s ∧ x.Poss V s ∧ y.Poss V s := by
  simp only [survivors, mem_ofPred_eq, say]
  split_ifs <;> simp_all

-- the alternative heuristic (ii), p. 116: where the alternative of cell `i₁` is the hardest to
-- express, the most likely states are those of `i₁`
theorem maximalFor_say_iff {Q : Set W → Prop} (ha : cost a < cost c) (hb : cost b < cost c)
    {s₀ : Set W} (h₀ : Q s₀) (hx₀ : x.Poss V s₀) (hy₀ : y.Poss V s₀) :
    MaximalFor Q (fun s ↦ cost (say V x y a b c s)) s ↔ Q s ∧ x.Poss V s ∧ y.Poss V s := by
  have hle : ∀ t, cost (say V x y a b c t) ≤ cost c := fun _ ↦
    say_rec (C := fun r ↦ cost r ≤ cost c) (fun _ _ ↦ le_rfl) (fun _ _ ↦ ha.le) fun _ ↦ hb.le
  refine ⟨fun h ↦ ⟨h.1, ?_⟩, fun ⟨hs, hx, hy⟩ ↦ ⟨hs, fun t _ _ ↦ ?_⟩⟩
  · have hge : cost c ≤ cost (say V x y a b c s) := by
      simpa only [say_of_poss hx₀ hy₀] using
        h.2 h₀ (by simpa only [say_of_poss hx₀ hy₀] using hle s)
    by_contra hn
    have hlt : cost (say V x y a b c s) < cost c :=
      say_rec (C := fun r ↦ cost r < cost c) (fun h1 h2 ↦ absurd ⟨h1, h2⟩ hn) (fun _ _ ↦ ha)
        fun _ ↦ hb
    exact hlt.not_ge hge
  · simpa only [say_of_poss hx hy] using hle t

/-- The partition of (15) and (20): `c` says that `x` and `y` are possible, on top of `u`. -/
noncomputable abbrev sayEither (V : P → Set W) (x y a b u : Sentence P) : Set W → Sentence P :=
  say V x y a b (and (may x) (and (may y) u))

theorem mem_survivors_sayEither_iff (ha : a.size ≤ u.size) (hb : b.size ≤ u.size) :
    s ∈ survivors V size u (sayEither V x y a b u) ↔
      s.Nonempty ∧ u.Believes V s ∧ x.Poss V s ∧ y.Poss V s :=
  mem_survivors_say_iff ha hb (by simp only [size]; omega)

private theorem believes_entails_top (hs : s.Nonempty) (hu : u.Believes V s) (hx : x.Poss V s)
    (hy : y.Poss V s) :
    (and (may x) (and (may y) u)).Believes V s ∧ (and (may x) (and (may y) u)).Entails V u :=
  ⟨believes_and.2 ⟨(believes_may hs).2 hx, believes_and.2 ⟨(believes_may hs).2 hy, hu⟩⟩,
    fun _ h ↦ (believes_and.1 (believes_and.1 h).2).2⟩

/-- (15), p. 115: *George is British or Canadian*, with the alternatives (16). -/
noncomputable abbrev sayOr (V : P → Set W) (p q : P) : Set W → Sentence P :=
  sayEither V (atom p) (atom q) (atom p) (atom q) (or (atom p) (atom q))

/-- (17), p. 117: *George may be British or Canadian*, with the alternatives (18). For the
performative (19), p. 118, a state is what the speaker permits. -/
noncomputable abbrev sayMayOr (V : P → Set W) (p q : P) : Set W → Sentence P :=
  say V (atom p) (atom q) (may (atom p)) (may (atom q)) (and (may (atom p)) (may (atom q)))

-- p. 115: the speaker of (15) considers both disjuncts possible
theorem mem_survivors_or_iff :
    s ∈ survivors V size (or (atom p) (atom q)) (sayOr V p q) ↔
      s.Nonempty ∧ s ⊆ V p ∪ V q ∧ (atom p).Poss V s ∧ (atom q).Poss V s :=
  mem_survivors_sayEither_iff (by simp [size]) (by simp [size])

-- p. 115: (16) are alternatives in the sense of the method
example : AreAlternatives V (or (atom p) (atom q)) (sayOr V p q) :=
  fun s hs h ↦ say_rec (C := fun r ↦ r.Believes V s ∧ r.Entails V (or (atom p) (atom q)))
    (believes_entails_top hs h)
    (fun _ hq ↦ ⟨fun w hw ↦ (h hw).resolve_right fun hwq ↦ hq ⟨w, hw, hwq⟩,
      fun _ h' _ hw ↦ .inl (h' hw)⟩)
    fun hp ↦ ⟨fun w hw ↦ (h hw).resolve_left fun hwp ↦ hp ⟨w, hw, hwp⟩,
      fun _ h' _ hw ↦ .inr (h' hw)⟩

/-- Free choice: of the speakers of *George may be British or Canadian*, those that survive the
alternative heuristic are just the consistent ones that consider each disjunct possible. -/
theorem mem_survivors_may_or_iff :
    s ∈ survivors V size (may (or (atom p) (atom q))) (sayMayOr V p q) ↔
      s.Nonempty ∧ (atom p).Poss V s ∧ (atom q).Poss V s := by
  rw [mem_survivors_say_iff (by simp [size]) (by simp [size]) (by simp [size])]
  refine ⟨fun ⟨hs, _, h⟩ ↦ ⟨hs, h⟩, fun ⟨hs, hp, hq⟩ ↦ ⟨hs, ?_, hp, hq⟩⟩
  exact (believes_may hs).2 (poss_or.2 (.inl hp))

-- p. 117: (18) are alternatives in the sense of the method
example : AreAlternatives V (may (or (atom p) (atom q))) (sayMayOr V p q) := fun s hs h ↦ by
  have key {r : P} (hr : V r ⊆ V p ∪ V q) : (may (atom r)).Entails V (may (or (atom p) (atom q))) :=
    fun _ h' _ hw ↦ (h' hw).mono (inter_subset_inter_right _ hr)
  refine say_rec (C := fun r ↦ r.Believes V s ∧ r.Entails V (may (or (atom p) (atom q))))
    (fun hp hq ↦ ⟨believes_and.2 ⟨(believes_may hs).2 hp, (believes_may hs).2 hq⟩,
      fun t h' ↦ key subset_union_left t (believes_and.1 h').1⟩)
    (fun hp _ ↦ ⟨(believes_may hs).2 hp, key subset_union_left⟩) fun hp ↦ ?_
  rcases poss_or.1 ((believes_may hs).1 h) with h' | h'
  · exact absurd h' hp
  · exact ⟨(believes_may hs).2 h', key subset_union_right⟩

-- p. 118: the survivors believe the very alternative the Standard Recipe has them not believe
theorem believes_of_mem_survivors_may_or
    (h : s ∈ survivors V size (may (or (atom p) (atom q))) (sayMayOr V p q)) :
    (may (atom p)).Believes V s ∧ (may (atom q)).Believes V s :=
  have ⟨hs, hp, hq⟩ := mem_survivors_may_or_iff.1 h
  ⟨(believes_may hs).2 hp, (believes_may hs).2 hq⟩

-- p. 117 applies the heuristic (ii) to (17), and p. 119 reasons by (i) for (19): both single out
-- `i₁`
theorem maximalFor_sayMayOr_iff (hp : (V p).Nonempty) (hq : (V q).Nonempty) :
    MaximalFor (fun s : Set W ↦ s.Nonempty ∧ (may (or (atom p) (atom q))).Believes V s)
      (fun s ↦ (sayMayOr V p q s).size) s ↔
      (s.Nonempty ∧ (may (or (atom p) (atom q))).Believes V s) ∧
        (atom p).Poss V s ∧ (atom q).Poss V s := by
  obtain ⟨w, hw⟩ := hp
  obtain ⟨v, hv⟩ := hq
  exact maximalFor_say_iff (by simp [size]) (by simp [size]) (s₀ := V p ∪ V q)
    ⟨⟨w, .inl hw⟩, fun _ _ ↦ ⟨w, .inl hw, .inl hw⟩⟩ ⟨w, .inl hw, hw⟩ ⟨v, .inr hv, hv⟩

-- pp. 119–120: free choice reports, where `V` gives the restaurant's permissions: with Competence
-- for each proposition at issue the weak inferences become beliefs
theorem subset_of_mem_survivors_or
    (h : s ∈ survivors V size (or (atom p) (atom q)) (sayOr V p q)) (hp : s ∈ polar (V p))
    (hq : s ∈ polar (V q)) : s ⊆ V p ∧ s ⊆ V q :=
  have ⟨_, _, hpp, hpq⟩ := mem_survivors_or_iff.1 h
  ⟨subset_of_inter_nonempty_of_mem_polar hpp hp, subset_of_inter_nonempty_of_mem_polar hpq hq⟩

/-- (13), p. 112: *many of the nurses were drunk*, with the alternatives (14), p. 113: `x` in the
cell of believing `x`, `u` and not `x` in that of believing its negation, and `u` and maybe `x` in
that of no opinion. The three-way partition of p. 113 is the partition by what is possible, among
`x` and its negation, since only the inconsistent state considers neither possible. The last two
alternatives have the same size, as p. 122 says of (22). -/
noncomputable abbrev sayScalar (V : P → Set W) (u x : Sentence P) : Set W → Sentence P :=
  say V x (neg x) x (and u (neg x)) (and u (may x))

/-- The alternative heuristic is sensitive to form: a speaker's saying `u` rules out that the
speaker believes `x` just when `x` is no more complex than `u`. -/
theorem mem_survivors_scalar_iff :
    s ∈ survivors V size u (sayScalar V u x) ↔
      s.Nonempty ∧ u.Believes V s ∧ (x.size ≤ u.size → ¬ x.Believes V s) := by
  simp only [survivors, mem_ofPred_eq, say]
  refine and_congr_right fun hs ↦ and_congr_right fun _ ↦ ?_
  rw [← not_poss_neg]
  by_cases hp : x.Poss V s <;> by_cases hn : (neg x).Poss V s
  · simp [hp, hn, size]
  · simp [hp, hn]
  · simp [hp, hn, size]
  · rw [not_poss_neg] at hn
    exact absurd (let ⟨w, hw⟩ := hs; ⟨w, hw, hn hw⟩) hp

-- p. 113: (14) are alternatives in the sense of the method
example (hx : x.Entails V u) : AreAlternatives V u (sayScalar V u x) :=
  fun s hs h ↦ say_rec (C := fun r ↦ r.Believes V s ∧ r.Entails V u)
    (fun hp _ ↦ ⟨believes_and.2 ⟨h, (believes_may hs).2 hp⟩, fun _ h' ↦ (believes_and.1 h').1⟩)
    (fun _ hn ↦ ⟨not_poss_neg.1 hn, hx⟩)
    fun hp ↦ ⟨believes_and.2 ⟨h, believes_neg.2 hp⟩, fun _ h' ↦ (believes_and.1 h').1⟩

-- p. 114: Competence eliminates the cell of no opinion, which leaves the strong implicature
theorem subset_compl_of_mem_survivors_scalar
    (h : s ∈ survivors V size (atom p) (sayScalar V (atom p) (atom q))) (hc : s ∈ polar (V q)) :
    s ⊆ (V q)ᶜ :=
  (Question.mem_polar.1 hc).resolve_left ((mem_survivors_scalar_iff.1 h).2.2 le_rfl)

-- (23), p. 122: with *many though not all* in the discourse (of the interns, in the text), previous
-- use lowers that alternative, the state of believing *not all* goes too, and no opinion is left
theorem mem_survivors_indicator_iff (hx : x.size ≤ u.size) :
    s ∈ survivors V (({and u (neg x)}ᶜ : Set (Sentence P)).indicator size) u (sayScalar V u x) ↔
      s.Nonempty ∧ u.Believes V s ∧ x.Poss V s ∧ (neg x).Poss V s := by
  have hu : u ∈ ({and u (neg x)}ᶜ : Set (Sentence P)) := fun h ↦ by
    have := congrArg size (mem_singleton_iff.1 h)
    simp only [size] at this
    omega
  have hc : and u (may x) ∈ ({and u (neg x)}ᶜ : Set (Sentence P)) := fun h ↦ by
    simpa using mem_singleton_iff.1 h
  refine mem_survivors_say_iff ?_ ?_ ?_
  · rw [indicator_of_mem hu]
    by_cases h : x ∈ ({and u (neg x)}ᶜ : Set (Sentence P))
    · rwa [indicator_of_mem h]
    · simp [indicator_of_notMem h]
  · simp [indicator_of_notMem]
  · rw [indicator_of_mem hu, indicator_of_mem hc]
    simp only [size]
    omega

end Sentence

open Sentence

section Pizza

variable {D : Type*}

/-- The clauses of (20), *many people had pizza or pasta*, and of its alternatives. -/
inductive PizzaClause where
  | manyEither | manyPizza | manyPasta | somePizza | somePasta

/-- The worlds at which a clause of (20) holds, where `pizza w` and `pasta w` are those who had
pizza and pasta at `w`. -/
def PizzaClause.val (many : Set D → Prop) (pizza pasta : W → Set D) : PizzaClause → Set W
  | manyEither => {w | many (pizza w ∪ pasta w)}
  | manyPizza => {w | many (pizza w)}
  | manyPasta => {w | many (pasta w)}
  | somePizza => {w | (pizza w).Nonempty}
  | somePasta => {w | (pasta w).Nonempty}

variable {many : Set D → Prop} {pizza pasta : W → Set D}

local notation "V₂₀" => PizzaClause.val many pizza pasta

/-- Alternatives to (20), reconstructed after (18) for the partition of p. 120 by *some people had
pizza* and *some people had pasta*. -/
noncomputable abbrev sayMany (many : Set D → Prop) (pizza pasta : W → Set D) :
    Set W → Sentence PizzaClause :=
  sayEither (PizzaClause.val many pizza pasta) (atom .somePizza) (atom .somePasta) (atom .manyPizza)
    (atom .manyPasta) (atom .manyEither)

-- (20), p. 120: free choice with no modal
theorem mem_survivors_many_iff :
    s ∈ survivors V₂₀ size (atom .manyEither) (sayMany many pizza pasta) ↔
      s.Nonempty ∧ (atom .manyEither).Believes V₂₀ s ∧ (atom .somePizza).Poss V₂₀ s ∧
        (atom .somePasta).Poss V₂₀ s :=
  mem_survivors_sayEither_iff le_rfl le_rfl

example (hm : Monotone many) :
    AreAlternatives V₂₀ (atom .manyEither) (sayMany many pizza pasta) := fun s hs h ↦
  say_rec (C := fun r ↦ r.Believes V₂₀ s ∧ r.Entails V₂₀ (atom .manyEither))
    (believes_entails_top hs h)
    (fun _ hn ↦ ⟨fun w hw ↦ by
      have he : pasta w = ∅ := not_nonempty_iff_eq_empty.1 fun hw' ↦ hn ⟨w, hw, hw'⟩
      simpa [eval, PizzaClause.val, he] using h hw, fun _ h' _ hw ↦ hm subset_union_left (h' hw)⟩)
    fun hn ↦ ⟨fun w hw ↦ by
      have he : pizza w = ∅ := not_nonempty_iff_eq_empty.1 fun hw' ↦ hn ⟨w, hw, hw'⟩
      simpa [eval, PizzaClause.val, he] using h hw, fun _ h' _ hw ↦ hm subset_union_right (h' hw)⟩

end Pizza

-- (31), p. 61, with p. 115, extending the text: a speaker who rules out a disjunct could have used
-- the shorter disjunction, so the survivors of the heuristic consider every disjunct possible
theorem inter_nonempty_of_forall_not_subset {ι : Type*} {A : ι → Set W} {J : Finset ι} {i : ι}
    (hq : s ⊆ ⋃ j ∈ J, A j) (h : ∀ J' ⊂ J, ¬ s ⊆ ⋃ j ∈ J', A j) (hi : i ∈ J) :
    (s ∩ A i).Nonempty := by
  classical
  by_contra hne
  refine h _ (Finset.erase_ssubset hi) fun w hw ↦ ?_
  obtain ⟨j, hj, hwj⟩ := mem_iUnion₂.1 (hq hw)
  exact mem_iUnion₂.2 ⟨j, Finset.mem_erase.2 ⟨fun he ↦ hne ⟨w, hw, he ▸ hwj⟩, hj⟩, hwj⟩

/-! ### Conventionalism -/

section Conventionalism

open Quantifier Quantifier.Det GeurtsPouscoulous2009 Exhaustification

private theorem someNotAllC_subset (R : Situation) : someNotAllC R ⊆ someC R := fun _ h ↦ h.1

/-- Enhanced lexicalism in its weak version (33) prefers the upper-bounded reading of (62) provided
this strengthens the sentence, which holds just under the upward-entailing quantifiers. -/
theorem boundedReading_ssubset_iff (q : Quant) :
    localReading q ⊂ classicalReading q ↔ PredictsLocalSIWeak (q.sem : Det (Fin 3)) := by
  have pos {r : Quant} {t : Trial} (hr : PredictsLocalSIWeak (r.sem : Det (Fin 3)))
      (hc : Classical r t) (hl : ¬ Local r t) :
      (localReading r ⊂ classicalReading r) ↔ PredictsLocalSIWeak (r.sem : Det (Fin 3)) :=
    iff_of_true ⟨fun R hR ↦ hr univ (someNotAllC_subset R) hR, fun h ↦ hl (h hc)⟩ hr
  have neg {r : Quant} {t : Trial} (hr : ¬ PredictsLocalSIWeak (r.sem : Det (Fin 3)))
      (hc : ¬ Classical r t) (hl : Local r t) :
      (localReading r ⊂ classicalReading r) ↔ PredictsLocalSIWeak (r.sem : Det (Fin 3)) :=
    iff_of_false (fun h ↦ hc (h.1 hl)) hr
  cases q with
  | all => exact pos all_predictsLocalSIWeak classical_all not_local_all
  | moreThanOne =>
    exact pos moreThanOne_predictsLocalSIWeak classical_moreThanOne not_local_moreThanOne
  | exactlyTwo =>
    exact neg exactlyTwo_not_predictsLocalSIWeak not_classical_exactlyTwo_b local_exactlyTwo_b
  | notAll => exact neg notAll_not_predictsLocalSIWeak not_classical_notAll local_notAll
  | notMoreThanOne =>
    exact neg notMoreThanOne_not_predictsLocalSIWeak not_classical_notMoreThanOne
      local_notMoreThanOne

-- (32), pp. 146–147: the strong version prefers it unless this weakens the sentence, which also
-- covers the non-monotone *exactly two*
theorem not_classicalReading_ssubset_iff (q : Quant) :
    ¬ classicalReading q ⊂ localReading q ↔ PredictsLocalSI (q.sem : Det (Fin 3)) := by
  have anti {r : Quant} (hr : ¬ PredictsLocalSI (r.sem : Det (Fin 3))) {t : Trial}
      (hc : ¬ Classical r t) (hl : Local r t) :
      (¬ classicalReading r ⊂ localReading r) ↔ PredictsLocalSI (r.sem : Det (Fin 3)) :=
    iff_of_false (not_not.2 ⟨fun R hR ↦ not_not.1 hr univ (someNotAllC_subset R) hR,
      fun h' ↦ hc (h' hl)⟩) hr
  cases q with
  | all =>
    exact iff_of_true ((boundedReading_ssubset_iff .all).2 all_predictsLocalSIWeak).not_gt
      all_predictsLocalSI
  | moreThanOne =>
    exact iff_of_true
      ((boundedReading_ssubset_iff .moreThanOne).2 moreThanOne_predictsLocalSIWeak).not_gt
      moreThanOne_predictsLocalSI
  | exactlyTwo =>
    exact iff_of_true (fun h ↦ not_local_exactlyTwo_a (h.1 classical_exactlyTwo_a))
      exactlyTwo_predictsLocalSI
  | notAll => exact anti notAll_not_predictsLocalSI not_classical_notAll local_notAll
  | notMoreThanOne =>
    exact anti notMoreThanOne_not_predictsLocalSI not_classical_notMoreThanOne
      local_notMoreThanOne

-- p. 159: of the squares of Figure 1, one is connected to all the circles
theorem existsUnique_figure2 : ∃! s : Fin 3, ∀ c, figure2 s c :=
  ⟨0, fun _ ↦ .inl rfl, by decide⟩

variable {some many all : Set W}

-- (39)–(40): `exh` is the operator O of (39); O (44b), the parse under negation (42c)
theorem exh_many (hs : many ⊆ some) (ha : all ⊂ many) :
    exh {some, many, all} many = many \ all :=
  exh_eq_sdiff_of_forall (by simp) ha.2 (by
    rintro r (rfl | rfl | rfl)
    exacts [.inl hs, .inl subset_rfl, .inr subset_rfl])

-- (43): O (43b), the parse (42b)
theorem exh_compl_many (hs : many ⊂ some) (ha : all ⊆ many) :
    exh {someᶜ, manyᶜ, allᶜ} manyᶜ = manyᶜ ∩ some := by
  rw [exh_eq_sdiff_of_forall (q := someᶜ) (by simp) (fun h ↦ hs.2 (compl_subset_compl.1 h)) (by
    rintro r (rfl | rfl | rfl)
    exacts [.inr subset_rfl, .inl subset_rfl, .inl (compl_subset_compl.2 ha)]), sdiff_compl]

-- (47), p. 150: the Power Principle prefers (42b) to the readings (42a) and (42c)
theorem isLeast_readings_negation (hs : many ⊂ some) (ha : all ⊂ many) :
    IsLeast {manyᶜ, exh {someᶜ, manyᶜ, allᶜ} manyᶜ, (exh {some, many, all} many)ᶜ}
      (exh {someᶜ, manyᶜ, allᶜ} manyᶜ) := by
  rw [exh_compl_many hs ha.1, exh_many hs.1 ha]
  refine ⟨by simp, ?_⟩
  rintro _ (rfl | rfl | rfl)
  · exact inter_subset_left
  · exact subset_rfl
  · exact fun w hw hn ↦ hw.1 hn.1

-- (57), pp. 156–157: the Power Principle prefers the narrow-scope parse (57b) of (56b), which
-- yields the inference the text says does not go through. That it is the stronger needs a serial
-- relation, which the text leaves tacit
theorem isLeast_readings_core (R : SetRel W W) [ModalLogic.IsSerial R] (ha : all ⊂ some) :
    IsLeast {R.core some, exh {R.core some, R.core all} (R.core some),
        R.core (exh {some, all} some)} (R.core (exh {some, all} some)) := by
  have hcore : R.core (some \ all) ⊆ R.core some := fun _ hw _ hv ↦ (hw hv).1
  rw [exh_pair ha.2]
  refine ⟨by simp, ?_⟩
  rintro _ (rfl | rfl | rfl)
  · exact hcore
  · refine fun w hw ↦ ⟨hcore hw, ?_⟩
    rintro q (rfl | rfl) hwq
    · exact subset_rfl
    · obtain ⟨v, hv⟩ := ModalLogic.IsSerial.serial (R := R) w
      exact absurd (hwq hv) (hw hv).2
  · exact subset_rfl

-- (25), p. 143: the negated upper-bounded *like* is *don't like or love*, not the printed *don't
-- like or don't love*, which excludes the continuation *we LOVE it*
theorem compl_sdiff_like {like love : Set W} (h : love ⊆ like) :
    (like \ love)ᶜ = likeᶜ ∪ love ∧ Disjoint (likeᶜ ∪ loveᶜ) love := by
  refine ⟨by ext w; simp only [mem_compl_iff, mem_sdiff, mem_union]; tauto, ?_⟩
  exact disjoint_left.2 fun _ hw hl ↦ hw.elim (· (h hl)) (· hl)

-- (48)–(49), p. 189: O can shift a lower bound too, given the alternative RICH₁
theorem exh_rich {rich rich₂ : Set W} (h : rich₂ ⊆ rich) (hne : rich₂.Nonempty) :
    exh {rich \ rich₂} rich = rich₂ := by
  obtain ⟨v, hv⟩ := hne
  rw [exh_eq_sdiff_of_forall (mem_singleton _) (fun hs ↦ (hs (h hv)).2 hv)
    (by rintro r rfl; exact .inr subset_rfl), sdiff_sdiff_eq_self h]

end Conventionalism

/-! ### Embedded implicatures -/

section Embedded

variable {M A F : Set W}

-- §8.1, (6)–(8): the implicature *not all the figs* passes the consistency check
theorem isSecondaryImplicature_mango (hA : A ⊆ F) (hM : (M \ F).Nonempty)
    (hF : (F \ (M ∪ A)).Nonempty) : IsSecondaryImplicature (M ∪ F) {M, F, A, M ∪ A} A := by
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
    IsSecondaryImplicature (M ∪ F) {M, F, A, M ∪ A} χ ↔ χ = A := by
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
-- that looks local, from the strong implicature at the speaker and Competence of the subject
theorem subset_core_exh {R : SetRel W W} {some all : Set W} (hall : all ⊂ some)
    (hq : s ⊆ R.core some) (h10 : s ⊆ (R.core all)ᶜ) (h11 : s ⊆ R.core all ∪ R.core allᶜ) :
    s ⊆ R.core (Exhaustification.exh {some, all} some) :=
  fun _ hw ↦ local_of_global_of_opinionated R hall (hq hw) (h10 hw) (h11 hw)

-- (10)–(12) and, for *hope*, (15)–(17), pp. 170–171, share this form, for any attitude: what
-- separates them is the plausibility of the second premise. (11) and (16), as printed, have the
-- disjunction outside the speaker's belief; given the first premise that says the same, and without
-- it it is strictly stronger
theorem subset_or_subset_iff {X Y : Set W} (h10 : s ⊆ Xᶜ) : (s ⊆ X ∨ s ⊆ Y) ↔ s ⊆ X ∪ Y :=
  ⟨fun h ↦ h.elim (·.trans subset_union_left) (·.trans subset_union_right),
    fun h ↦ .inr fun _ hw ↦ (h hw).resolve_left (h10 hw)⟩

example : ∃ (s X Y : Set (Fin 2)), s ⊆ X ∪ Y ∧ ¬ (s ⊆ X ∨ s ⊆ Y) :=
  ⟨univ, {0}, {0}ᶜ, (union_compl_self _).ge, by
    rintro (h | h)
    · exact absurd (h (mem_univ 1)) (by simp)
    · exact h (mem_univ 0) rfl⟩

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

-- p. 139: that (14) is false, given (32), entails (35), so that the alternative-based inference is
-- the stronger
theorem subset_compl_ofSuccessors (h32 : t ⊆ SetRel.ofSuccessors sailor)
    (h14 : t ⊆ Prod.fst ⁻¹' (SetRel.ofSuccessors (sailor ⊓ all)).dom ᶜ) :
    t ⊆ (SetRel.ofSuccessors all)ᶜ :=
  fun p hp hall ↦ h14 hp ⟨p.2, h32 hp, hall⟩

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
-- the ordering a Horn scale (4) would impose plays no part (pp. 57–59)
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

/-- The inferences of the rows that a Gricean derivation bears on, which the text says are conveyed
or not. -/
inductive Item where
  | disjunct | freeChoice | sameLength | afterUse | longer | figs | mango | referent | everySailor
  deriving DecidableEq

/-- The statement that the theory derives the inference, over any model of the sentence. -/
def Item.Derived : Item → Prop
  | .disjunct => ∀ {W : Type} (V : Bool → Set W) (s : Set W),
      s ∈ survivors V size (or (atom true) (atom false)) (sayOr V true false) →
        (atom true).Poss V s ∧ (atom false).Poss V s
  | .freeChoice => ∀ {W : Type} (V : Bool → Set W) (s : Set W),
      s ∈ survivors V size (may (or (atom true) (atom false))) (sayMayOr V true false) →
        (atom true).Poss V s ∧ (atom false).Poss V s
  | .sameLength => ∀ {W : Type} (V : Bool → Set W) (s : Set W),
      s ∈ survivors V size (atom true) (sayScalar V (atom true) (atom false)) →
        ¬ (atom false).Believes V s
  | .afterUse => ∀ {W : Type} (V : Bool → Set W) (s : Set W),
      s ∈ survivors V (({and (atom true) (neg (atom false))}ᶜ : Set (Sentence Bool)).indicator size)
        (atom true) (sayScalar V (atom true) (atom false)) →
        ¬ (atom false).Believes V s ∧ (atom false).Poss V s
  | .longer => ∀ {W : Type} (V : Bool → Set W) (s : Set W),
      s ∈ survivors V size (atom true) (sayScalar V (atom true) (and (atom false) (atom true))) →
        ¬ (and (atom false) (atom true)).Believes V s
  | .figs => ∀ {W : Type} (M F A : Set W), A ⊆ F → (M \ F).Nonempty → (F \ (M ∪ A)).Nonempty →
      IsSecondaryImplicature (M ∪ F) {M, F, A, M ∪ A} A
  | .mango => ∀ {W : Type} (M F A : Set W), A ⊆ F → (M \ F).Nonempty → (F \ (M ∪ A)).Nonempty →
      IsSecondaryImplicature (M ∪ F) {M, F, A, M ∪ A} M
  | .referent => ∀ {W D : Type} (sailor some all : W → Set D) (t : SetRel W D),
      t ⊆ SetRel.ofSuccessors sailor ∩ SetRel.ofSuccessors some → ¬ t ⊆ SetRel.ofSuccessors all →
        t ∈ polar (SetRel.ofSuccessors all) → t ⊆ (SetRel.ofSuccessors all)ᶜ
  | .everySailor => ∀ {W D : Type} (sailor all : W → Set D) (t : SetRel W D),
      t ⊆ SetRel.ofSuccessors sailor → t ⊆ (SetRel.ofSuccessors all)ᶜ →
        t ⊆ Prod.fst ⁻¹' (SetRel.ofSuccessors (sailor ⊓ all)).dom ᶜ

-- (26b), p. 124: *big toe* is longer than *toe*, so that nothing rules out believing it
theorem Item.not_derived_longer : ¬ Item.longer.Derived := fun h ↦
  @h Unit (fun _ ↦ univ) univ
    (mem_survivors_scalar_iff.2 ⟨univ_nonempty, fun _ _ ↦ mem_univ _, by simp [size]⟩)
    fun _ _ ↦ ⟨mem_univ _, mem_univ _⟩

-- (3), p. 165: Competence is not consistent for the first disjunct
theorem Item.not_derived_mango : ¬ Item.mango.Derived := fun h ↦ by
  have hA : ({2} : Set (Fin 3)) ⊆ {1, 2} := by simp
  have hM : (({0} : Set (Fin 3)) \ {1, 2}).Nonempty := ⟨0, by simp⟩
  have hF : (({1, 2} : Set (Fin 3)) \ ({0} ∪ {2})).Nonempty := ⟨1, by simp⟩
  have := (isSecondaryImplicature_mango_iff hA hM hF (by simp)).1
    (@h (Fin 3) {0} {1, 2} {2} hA hM hF)
  exact absurd (mem_singleton_iff.1 (this ▸ mem_singleton (0 : Fin 3))) (by decide)

-- pp. 139, 180: (35) does not entail that (14) is false, so that the story need not be about every
-- sailor
theorem Item.not_derived_everySailor : ¬ Item.everySailor.Derived := fun h ↦ by
  have := @h Unit Bool (fun _ ↦ univ) (fun _ ↦ {true}) {((), false)}
    (fun _ _ ↦ mem_univ _) (by rintro _ rfl hb; simp [SetRel.ofSuccessors] at hb)
  exact this rfl ⟨true, mem_univ _, rfl⟩

theorem Item.derived_iff : ∀ i : Item, i.Derived ↔ i ∉ [Item.longer, .mango, .everySailor]
  | .disjunct => iff_of_true (fun _ _ h ↦ (mem_survivors_or_iff.1 h).2.2) (by decide)
  | .freeChoice => iff_of_true (fun _ _ h ↦ (mem_survivors_may_or_iff.1 h).2) (by decide)
  | .sameLength => iff_of_true (fun _ _ h ↦ (mem_survivors_scalar_iff.1 h).2.2 le_rfl) (by decide)
  | .afterUse => iff_of_true (fun _ _ h ↦ by
      obtain ⟨_, _, hp, hn⟩ :=
        (mem_survivors_indicator_iff (x := atom false) (u := atom true) le_rfl).1 h
      exact ⟨poss_neg.1 hn, hp⟩) (by decide)
  | .longer => iff_of_false Item.not_derived_longer (by decide)
  | .figs => iff_of_true (fun _ _ _ ↦ isSecondaryImplicature_mango) (by decide)
  | .mango => iff_of_false Item.not_derived_mango (by decide)
  | .referent => iff_of_true (fun _ _ _ _ h32 h34 hc ↦
      (subset_inter_compl_ofSuccessors h32 h34 hc).trans inter_subset_right) (by decide)
  | .everySailor => iff_of_false Item.not_derived_everySailor (by decide)

/-- Reads the item of a row and whether the text says the inference is conveyed. -/
def inference? (ex : Datum) : Option (Item × Bool) := do
  let item ← ex.parse? "item" [("disjunct", Item.disjunct), ("freeChoice", .freeChoice),
    ("sameLength", .sameLength), ("afterUse", .afterUse), ("longer", .longer), ("figs", .figs),
    ("mango", .mango), ("referent", .referent), ("everySailor", .everySailor)]
  let conveys ← ex.bool? "conveys"
  pure (item, conveys)

example : Datum.ReadCount inference? Examples.all 11 := by decide

-- the rows on which a derivation bears: the theory derives what the text says is conveyed
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
  simp only [not_classicalReading_ssubset_iff, Quant.predictsLocalSI_iff]
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
