module

public import Mathlib.Data.Fintype.Prod
public import Linglib.Semantics.Exhaustification.InnocentExclusion
public import Linglib.Semantics.Quantification.Basic
public import Linglib.Data.Examples.Magri2009

/-!
# Magri (2009): A Theory of Individual-Level Predicates Based on Blind Mandatory Scalar Implicatures

[magri-2009] explains the oddness of *#Some Italians come from a warm country* and of
*#Sometimes, John is tall* by one mechanism, the blind mandatory scalar implicature. The
strengthened meaning is [fox-2007]'s innocent exclusion computed with logical entailment, blind to
common knowledge (the Blindness Hypothesis (32)), and a sentence whose strengthened meaning
contradicts common knowledge is odd (the Mismatch Hypothesis (33), `Odd`). Blindness is
essential: with entailment given common knowledge these sentences would not be strengthened at
all (`exhIE_image_inter`). The implicature is mandatory because relevance, constrained by (43),
cannot set aside an alternative that is contextually equivalent to the utterance
(`disjoint_exhR`), while an ordinary implicature depends on the context (`exists_isRelevance`).
Both hypotheses carry over to presuppositions, (65) and (66) (`odd_univ_iff`).

Individual-level predicates differ from stage-level ones only in common knowledge: they are
permanent, (70) (`Permanent`), hence homogeneous over any part of a lifespan (`Homogeneous`,
(71)). The oddness of *sometimes* with *tall*, (72b), is then that of *some* with *come from a
warm country*, (73) (`odd_some`, `sometimes_odd`). An existential in the scope of a universal,
against its alternatives with definite descriptions (49), (94), is odd when common knowledge fixes
a single witness for it (`odd_narrowSome`). This covers the fronted indefinite of (46a) and (54a)
(`winner_odd`, `running_odd`) and the existential reading of a bare plural subject of an
individual-level predicate, (84b), whose narrowest scope puts it below GEN (`existential_odd`).
A universal over individuals rescues the existential, since distinct individuals may have distinct
witnesses, (54b) and (102b) (`table_not_odd`, `universal_not_odd`). The same computation predicts
the German word order facts of [diesing-1992], (8) and (125) (`word_order_rows`). Overt *always*
competes with GEN, which presupposes homogeneity, so *#John is always tall* is odd, (134a)
(`always_odd`), but *Firemen are always tall* is not, (139b) (`always_bare_not_odd`).

## Implementation notes

* Propositions are sets of worlds. A world of §3.3 and §4 is the extension of the one predicate
  at issue over individuals and an index (times, or objects and times), with lifespans, nouns and
  restrictors held fixed, so every extension is a logically possible world. The worlds the paper
  exhibits, (98), the table of (54) and the world of §4.3, are constructed.
* GEN contributes its universal assertion (137) to truth conditions; its homogeneity
  presupposition is used only in §4.6, as in the paper. The restrictor `C̃` of (90) is arbitrary,
  as in the paper, and the definite alternatives (93b) restrict GEN to the part of each lifespan
  in `C`.
* The world (98) is sampled at three times of `C̃`, one in each fireman's stretch of tallness in
  the paper's picture.

## TODO

* The alternatives of the episodic existential reading (92b), sketched in footnote 20, are not
  formalized.
* The facts of §4.4 (non-kind bare plurals, association with *only*, statives, locatives) are
  discussion only, and the contrast (133) with definite subjects is left open by the paper.

## References

* [magri-2009]
* [fox-2007]
* [carlson-1977]
* [diesing-1992]
-/

@[expose] public section

namespace Magri2009

open Exhaustification Quantifier Set

/-! ### Blind strengthening and oddness (§3.2) -/

section Oddness

variable {W : Type*} {Wck φ ψ : Set W}

/-- The Mismatch Hypothesis (33): the sentence `φ`, with alternatives `ALT`, is odd when its
strengthened meaning contradicts common knowledge `Wck`. By the Blindness Hypothesis (32) the
strengthened meaning is innocent exclusion (30) with logical entailment, computed over all worlds
rather than over `Wck`. -/
def Odd (Wck : Set W) (ALT : Set (Set W)) (φ : Set W) : Prop :=
  Disjoint (exhIE ALT φ) Wck

private theorem disjoint_diff_iff {s t u : Set W} : Disjoint (s \ t) u ↔ s ∩ u ⊆ t := by
  simp only [disjoint_left, subset_def, mem_sdiff, mem_inter_iff, and_imp, not_imp_not]

/-- (34), (82): against one alternative that `φ` can hold without, `φ` is odd exactly when common
knowledge makes it entail the alternative. -/
theorem odd_pair_iff (h : (φ \ ψ).Nonempty) : Odd Wck {φ, ψ} φ ↔ φ ∩ Wck ⊆ ψ := by
  rw [Odd, exhIE_pair_sdiff φ h, disjoint_diff_iff]

/-- (53), (97), (109): against the alternatives `ψP i`, blind strengthening denies them all when
`φ` can hold with all of them false. -/
theorem exhIE_insert_range {ι : Type*} {ψP : ι → Set W} (h : (φ \ ⋃ i, ψP i).Nonempty) :
    exhIE (insert φ (range ψP)) φ = φ \ ⋃ i, ψP i := by
  have hexh : exh (insert φ (range ψP)) φ = φ \ ⋃ i, ψP i := by
    obtain ⟨v, hvφ, hv⟩ := h
    ext x
    simp only [mem_exh, forall_mem_insert, forall_mem_range, mem_sdiff, mem_iUnion, not_exists]
    exact and_congr_right fun _ ↦ ⟨fun h i hx ↦ hv (mem_iUnion.2 ⟨i, h.2 i hx hvφ⟩),
      fun h ↦ ⟨fun _ ↦ subset_rfl, fun i hx ↦ (h i hx).elim⟩⟩
  rw [exhIE_eq_exh_of_nonempty _ _ (hexh ▸ h), hexh]

theorem odd_insert_range_iff {ι : Type*} {ψP : ι → Set W} (h : (φ \ ⋃ i, ψP i).Nonempty) :
    Odd Wck (insert φ (range ψP)) φ ↔ φ ∩ Wck ⊆ ⋃ i, ψP i := by
  rw [Odd, exhIE_insert_range h, disjoint_diff_iff]

/-- (34): the Blindness Hypothesis is essential. Strengthening with entailment given common
knowledge (31b), that is innocent exclusion over the propositions restricted to `Wck`, leaves `φ`
unstrengthened when its alternatives are equivalent to it given common knowledge. -/
theorem exhIE_image_inter {ALT : Set (Set W)} (hφ : φ ∈ ALT)
    (h : ∀ a ∈ ALT, a ∩ Wck = φ ∩ Wck) : exhIE ((· ∩ Wck) '' ALT) (φ ∩ Wck) = φ ∩ Wck := by
  rw [eq_singleton_iff_unique_mem.2 ⟨mem_image_of_mem _ hφ, forall_mem_image.2 h⟩,
    exhIE_singleton_self]

/-! ### Mandatoriness (§3.2.5) -/

/-- The postulates (43) on a relevance property `R` in a context where `φ` is uttered: the
utterance is relevant (43a), and propositions equivalent given common knowledge are alike in
relevance (43b). -/
structure IsRelevance (Wck φ : Set W) (R : Set W → Prop) : Prop where
  uttered : R φ
  congr {p q : Set W} : p ∩ Wck = q ∩ Wck → (R p ↔ R q)

/-- (42): the prejacent with every relevant innocently excludable alternative denied, the
counterpart over sets of `Excluder.restrict` applied to `innocent`. -/
def exhR (R : Set W → Prop) (ALT : Set (Set W)) (φ : Set W) : Set W :=
  {x | x ∈ φ ∧ ∀ a, IsInnocentlyExcludable ALT φ a → R a → x ∉ a}

variable {R : Set W → Prop} {ALT : Set (Set W)}

/-- (45): an alternative equivalent to the utterance given common knowledge is relevant. -/
theorem IsRelevance.relevant (hR : IsRelevance Wck φ R) (h : ψ ∩ Wck = φ ∩ Wck) : R ψ :=
  (hR.congr h).2 hR.uttered

/-- (45): a mismatching implicature is mandatory. When an excludable alternative is equivalent to
the utterance given common knowledge, the strengthened meaning (42) contradicts common knowledge
whatever relevance property the context supplies. -/
theorem disjoint_exhR (hR : IsRelevance Wck φ R) (hψ : IsInnocentlyExcludable ALT φ ψ)
    (h : ψ ∩ Wck = φ ∩ Wck) : Disjoint (exhR R ALT φ) Wck := by
  refine disjoint_left.2 fun x hx hck ↦ hx.2 ψ hψ (hR.relevant h) ?_
  have : x ∈ ψ ∩ Wck := h ▸ ⟨hx.1, hck⟩
  exact this.1

/-- (40), (44): an implicature that does not mismatch is not mandatory. Relevance of exactly the
propositions equivalent to the utterance given common knowledge satisfies (43) and sets aside
every other alternative. -/
theorem exists_isRelevance (h : ψ ∩ Wck ≠ φ ∩ Wck) : ∃ R, IsRelevance Wck φ R ∧ ¬ R ψ :=
  ⟨fun p ↦ p ∩ Wck = φ ∩ Wck, ⟨rfl, fun hpq ↦ by rw [hpq]⟩, h⟩

/-! ### Homogeneity (§3.4, §4.1) -/

variable {α : Type*} {A B : W → α → Prop}

/-- Homogeneity of the scope `B` with respect to the restrictor `A`: all `A`s are `B`s or none
are. It is the presupposition YES ∪ NO of the distributivity operator (67) and of GEN (137), and
(71b) takes common knowledge to entail it. -/
def Homogeneous (A B : α → Prop) : Prop := GQ.every A B ∨ GQ.no A B

/-- (38), (73), (72b): a sentence with *some* is odd when common knowledge makes its scope
homogeneous with respect to its restrictor, (71): its Horn-mate with *all* is logically but not
contextually stronger. -/
theorem odd_some (hck : ∀ x ∈ Wck, Homogeneous (A x) (B x))
    (h : ∃ x, GQ.some (A x) (B x) ∧ ¬ GQ.every (A x) (B x)) :
    Odd Wck {{x | GQ.some (A x) (B x)}, {x | GQ.every (A x) (B x)}} {x | GQ.some (A x) (B x)} :=
  (odd_pair_iff h).2 fun x ⟨hs, hx⟩ ↦
    (hck x hx).resolve_right fun hno ↦ (GQ.no_contradicts_some _ _).1 hno hs

/-- (61), (62), (63), (142): a sentence without presupposition, (68a), is odd by the Mismatch
Hypothesis for presuppositions (66) when its Horn-mate presupposes `p`, (68b), which common
knowledge entails but logic does not: the blind strengthened presupposition (64) is `pᶜ`. -/
theorem odd_univ_iff {p : Set W} (h : pᶜ.Nonempty) : Odd Wck {univ, p} univ ↔ Wck ⊆ p := by
  rw [odd_pair_iff (by rwa [← compl_eq_univ_sdiff]), univ_inter]

end Oddness

/-! ### An existential in the scope of a universal (§3.3) -/

section NarrowExistential

variable {E I : Type*} {Wck : Set (E → I → Prop)} {N : E → Prop} {D : I → Prop}
  {R : E → I → Prop}

/-- An existential over `N` in the scope of a universal over the index restrictor `D`: (48b),
(56), (91b), (105). -/
def narrowSome (N : E → Prop) (D : I → Prop) : Set (E → I → Prop) :=
  {f | GQ.every D fun i ↦ GQ.some N fun x ↦ f x i}

/-- The alternative with *the N such and such*, a Horn-mate of the existential by (49) and (94),
denoting `d`, with the index restricted by `R d`: (50b), (57), (93b), (106b). -/
def definite (R : E → I → Prop) (d : E) : Set (E → I → Prop) :=
  {f | GQ.every (R d) (f d)}

/-- The scalar alternatives (25) of `narrowSome N D`: itself and the definite alternative for
each `N`. -/
def alts (N : E → Prop) (D : I → Prop) (R : E → I → Prop) : Set (Set (E → I → Prop)) :=
  insert (narrowSome N D) (range fun d : {d // N d} ↦ definite R d)

/-- (52), (96), (108): the definite alternatives together amount to the reading with the
existential taking widest scope, (51), (95), (107). -/
theorem iUnion_definite :
    ⋃ d : {d // N d}, definite R d = {f | GQ.some N fun d ↦ GQ.every (R d) (f d)} := by
  ext f
  simp [definite, GQ.some]

/-- (46a), (54a), (99): an existential in the scope of a universal is odd when, at every world
compatible with common knowledge, an `N` true at some index of `D` is true throughout its own
restrictor, and when logically it can hold with every definite alternative false, as at (98).
Blind strengthening denies the widest-scope reading, which common knowledge makes it entail. -/
theorem odd_narrowSome (hD : ∃ i, D i)
    (hck : ∀ f ∈ Wck, ∀ x, N x → ∀ i, D i → f x i → ∀ j, R x j → f x j)
    (h : (narrowSome N D \ ⋃ d : {d // N d}, definite R d).Nonempty) :
    Odd Wck (alts N D R) (narrowSome N D) := by
  refine (odd_insert_range_iff h).2 fun f ⟨hf, hfck⟩ ↦ ?_
  obtain ⟨i, hi⟩ := hD
  obtain ⟨x, hx, hxi⟩ := hf i hi
  exact mem_iUnion.2 ⟨⟨x, hx⟩, hck f hfck x hx i hi hxi⟩

/-- (46a): *#On every day, a fireman won* is odd when it is common knowledge that the same person
was the winner on every day of `D`. -/
theorem winner_odd (hD : ∃ i, D i) (hck : ∀ f ∈ Wck, ∃ g, ∀ x i, D i → (f x i ↔ x = g))
    (h : (narrowSome N D \ ⋃ d : {d // N d}, definite (fun _ ↦ D) d).Nonempty) :
    Odd Wck (alts N D fun _ ↦ D) (narrowSome N D) :=
  odd_narrowSome hD (fun f hf x _ i hi hxi j hj ↦
    let ⟨_, hg⟩ := hck f hf
    (hg x j hj).2 ((hg x i hi).1 hxi)) h

end NarrowExistential

/-! #### The context of (54) -/

section Table

/-- The competitions of (54). -/
inductive Competition where
  | swimming
  | running
  | jumping
  deriving DecidableEq, Fintype

/-- The winners in the table of (54). -/
inductive Winner where
  | x
  | y
  | z
  deriving DecidableEq, Fintype

/-- The competition each person of (54) won on every day. -/
def Winner.competition : Winner → Competition
  | .x => .swimming
  | .y => .running
  | .z => .jumping

/-- The table of (54): each of `x`, `y`, `z` won one competition on all five days. -/
def table (g : Winner) (p : Competition × Fin 5) : Prop := p.1 = g.competition

/-- The common knowledge of (54): the same person won each competition on all five days. -/
def sameWinner : Set (Winner → Competition × Fin 5 → Prop) :=
  {f | ∀ c, ∃ g, ∀ w t, f w (c, t) ↔ w = g}

/-- (54a): *#Every day, a fireman won the running competition* is odd in the context of (54). -/
theorem running_odd :
    Odd sameWinner (alts (fun _ ↦ True) (fun p ↦ p.1 = .running) fun _ p ↦ p.1 = .running)
      (narrowSome (fun _ ↦ True) fun p ↦ p.1 = .running) := by
  refine winner_odd ⟨(.running, 0), rfl⟩ (fun f hf ↦ ?_)
    ⟨fun g p ↦ g = if p.2 = 0 then .x else .y, ?_⟩
  · obtain ⟨g, hg⟩ := hf .running
    refine ⟨g, fun w ⟨c, t⟩ hc ↦ ?_⟩
    obtain rfl : c = .running := hc
    exact hg w t
  · simp only [narrowSome, definite, GQ.every, GQ.some, mem_sdiff, mem_ofPred_eq, mem_iUnion,
      not_exists]
    decide

/-- (54b): *Every day, for every competition, a fireman won* is fine in the context of (54): the
table is compatible with common knowledge, verifies the sentence (56), and falsifies each
definite alternative (57). -/
theorem table_not_odd :
    ¬ Odd sameWinner (alts (fun _ ↦ True) (fun _ ↦ True) fun _ _ ↦ True)
      (narrowSome (fun _ ↦ True) fun _ ↦ True) := by
  have h : table ∈ narrowSome (fun _ : Winner ↦ True) (fun _ : Competition × Fin 5 ↦ True) \
      ⋃ d : {_d : Winner // True}, definite (fun _ _ ↦ True) d := by
    simp only [table, narrowSome, definite, GQ.every, GQ.some, mem_sdiff, mem_ofPred_eq,
      mem_iUnion, not_exists]
    decide
  rw [alts, odd_insert_range_iff ⟨_, h⟩]
  refine fun hsub ↦ h.2 (hsub ⟨h.1, ?_⟩)
  simp only [sameWinner, table, mem_ofPred_eq]
  decide

end Table

/-! ### Individual-level predicates (§4) -/

section IndividualLevel

variable {E T : Type*} (live : E → T → Prop)

/-- (70): an extension of the predicate compatible with common knowledge about an
individual-level predicate. True of an individual at some time, it is true of it throughout its
lifespan `live d`. -/
def Permanent (f : E → T → Prop) : Prop :=
  ∀ d, (∃ t, f d t) → ∀ t, live d t → f d t

variable {live} {Wck : Set (E → T → Prop)} {f : E → T → Prop} {j : E} {C D : T → Prop}
  {t₁ t₂ : T}

/-- (71): a permanent predicate is homogeneous over any restrictor within a lifespan. -/
theorem Permanent.homogeneous (hf : Permanent live f) {d : E} {A : T → Prop}
    (hA : ∀ t, A t → live d t) : Homogeneous A (f d) := by
  by_cases h : ∃ t, f d t
  · exact .inl fun t ht ↦ hf d h t (hA t ht)
  · exact .inr fun t _ ht ↦ h ⟨t, ht⟩

/-! #### Existential Q-adverbs (§4.1) -/

/-- (79b): *Sometimes, John is tall*, the adverb restricted by `C` and, by (76) and (77), by
John's lifespan. -/
def sometimes (live : E → T → Prop) (j : E) (C : T → Prop) : Set (E → T → Prop) :=
  {f | GQ.some (fun t ↦ live j t ∧ C t) (f j)}

/-- (80b): its Horn-mate (81) with *always*. -/
def always (live : E → T → Prop) (j : E) (C : T → Prop) : Set (E → T → Prop) :=
  {f | GQ.every (fun t ↦ live j t ∧ C t) (f j)}

private theorem mem_sometimes_sdiff_always (h₁ : live j t₁ ∧ C t₁) (h₂ : live j t₂ ∧ C t₂)
    (hne : t₁ ≠ t₂) : (fun _ t ↦ t = t₁) ∈ sometimes live j C \ always live j C :=
  ⟨⟨t₁, h₁, rfl⟩, fun h ↦ hne (h t₂ h₂).symm⟩

/-- (72b), (82): *#Sometimes, John is tall* is odd for every restrictor `C` of the adverb that
meets John's lifespan at two times: its Horn-mate with *always* is logically stronger but
equivalent given (70). -/
theorem sometimes_odd (hck : ∀ f ∈ Wck, Permanent live f) (h₁ : live j t₁ ∧ C t₁)
    (h₂ : live j t₂ ∧ C t₂) (hne : t₁ ≠ t₂) :
    Odd Wck {sometimes live j C, always live j C} (sometimes live j C) :=
  odd_some (A := fun (_ : E → T → Prop) t ↦ live j t ∧ C t) (B := fun f ↦ f j)
    (fun f hf ↦ (hck f hf).homogeneous fun _ h ↦ h.1)
    ⟨fun _ t ↦ t = t₁, mem_sometimes_sdiff_always h₁ h₂ hne⟩

/-- (72a): *Sometimes, John is available* is fine, since common knowledge does not make a
stage-level predicate permanent. -/
example (h₁ : live j t₁ ∧ C t₁) (h₂ : live j t₂ ∧ C t₂) (hne : t₁ ≠ t₂) :
    ¬ Odd univ {sometimes live j C, always live j C} (sometimes live j C) := by
  have hw := mem_sometimes_sdiff_always h₁ h₂ hne
  rw [odd_pair_iff ⟨_, hw⟩]
  exact fun h ↦ hw.2 (h ⟨hw.1, trivial⟩)

/-! #### Bare plural subjects (§4.2) -/

/-- (84b), (99): the existential reading (91b) of the bare plural subject of *Firemen are tall* is
odd. The existential has narrowest scope (88), below GEN over the restrictor `D` (the `C̃` of
(90)); blind strengthening denies that some fireman is tall throughout the part of his lifespan in
`C`, (97), and given (70) a fireman tall at a time of `D` is tall throughout his lifespan. -/
theorem existential_odd {N : E → Prop} (hck : ∀ f ∈ Wck, Permanent live f) (hD : ∃ t, D t)
    (h : (narrowSome N D \ ⋃ d : {d // N d}, definite (fun d t ↦ C t ∧ live d t) d).Nonempty) :
    Odd Wck (alts N D fun d t ↦ C t ∧ live d t) (narrowSome N D) :=
  odd_narrowSome hD (fun f hf x _ i _ hxi _ hj ↦ hck f hf x ⟨i, hxi⟩ _ hj.2) h

end IndividualLevel

/-! #### The world (98) -/

section World98

/-- The three firemen of (98). -/
inductive Fireman where
  | d₁
  | d₂
  | d₃
  deriving DecidableEq, Fintype

/-- The time of `C̃` at which each fireman of (98) is tall. -/
def Fireman.tallAt : Fireman → Fin 3
  | .d₁ => 2
  | .d₂ => 1
  | .d₃ => 0

/-- The lifespans of (98) at the three times of `C̃`: `d₁` is born after the first, `d₃` dies
before the last. -/
def lifespan : Fireman → Fin 3 → Prop
  | .d₁, t => t ≠ 0
  | .d₂, _ => True
  | .d₃, t => t ≠ 2

instance : DecidableRel lifespan := fun d t ↦
  match d with
  | .d₁ => inferInstanceAs (Decidable (t ≠ 0))
  | .d₂ => inferInstanceAs (Decidable True)
  | .d₃ => inferInstanceAs (Decidable (t ≠ 2))

/-- The world (98): at each time of `C̃` some fireman is tall, and none is tall throughout the
part of his lifespan in `C̃`. -/
def world98 (d : Fireman) (t : Fin 3) : Prop := t = d.tallAt

/-- The existential reading (91b) and its definite alternatives (93b) in the model of (98), with
`C` and `C̃` all three times. -/
abbrev alts98 : Set (Set (Fireman → Fin 3 → Prop)) :=
  alts (fun _ ↦ True) (fun _ ↦ True) fun d t ↦ True ∧ lifespan d t

/-- The world (98) verifies the existential reading and falsifies every definite alternative. -/
theorem world98_mem : world98 ∈ narrowSome (fun _ ↦ True) (fun _ ↦ True) \
    ⋃ d : {_d : Fireman // True}, definite (fun d t ↦ True ∧ lifespan d t) d := by
  simp only [world98, narrowSome, definite, GQ.every, GQ.some, mem_sdiff, mem_ofPred_eq,
    mem_iUnion, not_exists]
  decide

/-- The existential reading of a bare plural subject is odd against the common knowledge `Wck`
about its predicate, in the model of (98). -/
def ExistentialOdd (Wck : Set (Fireman → Fin 3 → Prop)) : Prop :=
  Odd Wck alts98 (narrowSome (fun _ ↦ True) fun _ ↦ True)

/-- (84b): the existential reading of *Firemen are tall* is odd, since common knowledge makes an
individual-level predicate permanent (70). -/
theorem existentialOdd_permanent : ExistentialOdd {f | Permanent lifespan f} :=
  existential_odd (fun _ h ↦ h) ⟨0, trivial⟩ ⟨_, world98_mem⟩

/-- (84a): the existential reading of *Firemen are available* is fine, since common knowledge
does not constrain a stage-level predicate and the world (98) is compatible with it. -/
theorem not_existentialOdd_univ : ¬ ExistentialOdd univ := by
  rw [ExistentialOdd, alts98, alts, odd_insert_range_iff ⟨_, world98_mem⟩]
  exact fun h ↦ world98_mem.2 (h ⟨world98_mem.1, trivial⟩)

end World98

/-! #### Embedding under a universal (§4.3) -/

section Universal

/-- The two Jewish women of the world of §4.3. -/
inductive Woman where
  | a₁
  | a₂
  deriving DecidableEq, Fintype

/-- The two Jewish men of the world of §4.3. -/
inductive Man where
  | b₁
  | b₂
  deriving DecidableEq, Fintype

/-- The one man each woman of §4.3 is related to. -/
def Woman.relative : Woman → Man
  | .a₁ => .b₁
  | .a₂ => .b₂

/-- The world of §4.3: `a₁` is related only to `b₁` and `a₂` only to `b₂`, at all times. -/
def distributed {T : Type*} (a : Woman) (p : Man × T) : Prop := p.1 = a.relative

/-- (102b), (109): the existential reading (105) of the bare plural subject of *Jewish women are
related to every Jewish man*, with the universal object scoping over GEN, is fine. Given
restrictors that meet the lifespans, the world where `a₁` is related only to `b₁` and `a₂` only
to `b₂` is compatible with (70) for *related*, verifies (105), and falsifies each definite
alternative (106b). With the definite object of (102a) instead, the reading falls under
`existential_odd`. -/
theorem universal_not_odd {T : Type*} {live : Woman → T → Prop} {C D : Man → T → Prop}
    (h₁ : ∃ t, C .b₂ t ∧ live .a₁ t) (h₂ : ∃ t, C .b₁ t ∧ live .a₂ t) :
    ¬ Odd {f | ∀ b, Permanent live fun a t ↦ f a (b, t)}
      (alts (fun _ ↦ True) (fun p ↦ D p.1 p.2) fun a p ↦ C p.1 p.2 ∧ live a p.2)
      (narrowSome (fun _ ↦ True) fun p ↦ D p.1 p.2) := by
  have h : distributed ∈ narrowSome (fun _ ↦ True) (fun p : Man × T ↦ D p.1 p.2) \
      ⋃ a : {_a : Woman // True}, definite (fun a p ↦ C p.1 p.2 ∧ live a p.2) a := by
    refine ⟨fun ⟨b, _⟩ _ ↦ ?_, ?_⟩
    · cases b
      exacts [⟨.a₁, trivial, rfl⟩, ⟨.a₂, trivial, rfl⟩]
    · simp only [mem_iUnion, not_exists]
      rintro ⟨_ | _, _⟩ ha
      · obtain ⟨t, ht⟩ := h₁
        exact absurd (ha (.b₂, t) ht) nofun
      · obtain ⟨t, ht⟩ := h₂
        exact absurd (ha (.b₁, t) ht) nofun
  rw [alts, odd_insert_range_iff ⟨_, h⟩]
  exact fun hsub ↦ h.2 (hsub ⟨h.1, fun _ _ ⟨_, ht⟩ _ _ ↦ ht⟩)

end Universal

/-! #### German word order (§4.5) -/

section GermanWordOrder


/-- Common knowledge about the predicate of a row, by (70) from the level ([carlson-1977]) its
`predicate_level` feature records: an individual-level predicate is permanent, a stage-level one
unconstrained. -/
def commonKnowledgeOf (row : Datum) : Option (Set (Fireman → Fin 3 → Prop)) :=
  match row.feature? "predicate_level" with
  | some "individual" => some {f | Permanent lifespan f}
  | some "stage" => some univ
  | _ => none

private theorem exists_existentialOdd_iff (row : Datum) :
    (∃ Wck ∈ commonKnowledgeOf row, ExistentialOdd Wck) ↔
      row.feature? "predicate_level" = some "individual" := by
  unfold commonKnowledgeOf
  split <;> simp_all [existentialOdd_permanent, not_existentialOdd_univ]

/-- A row of (8) is predicted odd when its bare plural subject sits to the right of *ja doch*,
where it has only the existential reading (§4.5.1), and that reading is odd for its predicate,
(128), (129). -/
def PredictedOdd (row : Datum) : Prop :=
  row.feature? "position" = some "right" ∧ ∃ Wck ∈ commonKnowledgeOf row, ExistentialOdd Wck

/-- (8), (125): a row is acceptable exactly when it is not predicted odd; only (8c), with the
individual-level *intelligent* and its subject to the right of *ja doch*, is odd. -/
theorem word_order_rows :
    ∀ row ∈ Examples.all, (row.judgment = .acceptable ↔ ¬ PredictedOdd row) := by
  simp only [PredictedOdd, exists_existentialOdd_iff]
  decide

end GermanWordOrder

/-! #### Overt universal Q-adverbs (§4.6) -/

section Always

variable {E T : Type*} {live : E → T → Prop} {Wck : Set (E → T → Prop)} {j : E} {t₁ t₂ : T}

/-- (137): the homogeneity presupposition of GEN with restrictor `A`, the scope being the
predicate's extension read through `B`: (138b) for *John is tall*, (141b) for *Firemen are
tall*. -/
def genPresup {α : Type*} (A : α → Prop) (B : (E → T → Prop) → α → Prop) :
    Set (E → T → Prop) :=
  {f | Homogeneous A (B f)}

/-- (134a), (138): *#John is always tall* is odd by the Mismatch Hypothesis for presuppositions.
It presupposes nothing, (138a), while its Horn-mate *John is tall*, with GEN, presupposes that
John is tall at all or at none of the times he is alive, (138b), which (70) entails. -/
theorem always_odd (hck : ∀ f ∈ Wck, Permanent live f) (h₁ : live j t₁) (h₂ : live j t₂)
    (hne : t₁ ≠ t₂) : Odd Wck {univ, genPresup (live j) fun f ↦ f j} univ :=
  (odd_univ_iff ⟨fun _ t ↦ t = t₁,
    fun h ↦ h.elim (fun h ↦ hne (h t₂ h₂).symm) fun h ↦ h t₁ h₁ rfl⟩).2
    fun f hf ↦ (hck f hf).homogeneous fun _ h ↦ h

/-- (139b), (141): *Firemen are always tall* is fine. The homogeneity presupposition of GEN is now
over firemen and their times, and (70) is compatible with some firemen being tall and others
not. -/
theorem always_bare_not_odd {N : E → Prop} {d₁ d₂ : E} (h₁ : N d₁ ∧ live d₁ t₁)
    (h₂ : N d₂ ∧ live d₂ t₂) (hne : d₁ ≠ d₂) :
    ¬ Odd {f | Permanent live f}
      {univ, genPresup (fun p : E × T ↦ N p.1 ∧ live p.1 p.2) fun f p ↦ f p.1 p.2} univ := by
  have hf : (fun d _ ↦ d = d₁) ∉ genPresup (fun p : E × T ↦ N p.1 ∧ live p.1 p.2)
      fun f p ↦ f p.1 p.2 :=
    fun h ↦ h.elim (fun h ↦ hne (h (d₂, t₂) h₂).symm) fun h ↦ h (d₁, t₁) h₁ rfl
  rw [odd_univ_iff ⟨_, hf⟩]
  exact fun h ↦ hf (h (show Permanent live fun d _ ↦ d = d₁ from fun _ ⟨_, hd⟩ _ _ ↦ hd))

end Always

end Magri2009
