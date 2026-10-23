module

public import Mathlib.Data.Set.Lattice.Bounded

/-!
# Chierchia 2004: parallel recursive strengthening

[chierchia-2004] ("Scalar Implicatures, Polarity Phenomena, and the
Syntax/Pragmatics Interface", §3) computes two meanings for every expression in
tandem: a plain value `‖α‖` and a strengthened value `‖α‖^S` that folds scalar
implicatures in as soon as their triggers appear. Direct implicatures enter at
scope sites by a variant of [krifka-1995a]'s rule (75); the Strength Condition
(§3.1) requires `‖α‖^S` to entail `‖α‖` at every step; and Strong Application
(84) dispatches on entailment behaviour: non-DE functions pass strengthened
values through, DE functions strip the argument's implicatures and add indirect
implicatures at the matrix level. Implicature suspension in exactly the
*any*-licensing environments — the Generalization on SIs (53) — is `Antitone`
reversal of the Strength Condition, and intervention (§4.3) follows from NPIs
competing with strong rather than plain meanings (127).

## Main definitions

* `Meaning`, `Meaning.lexical`, `Meaning.StrengthCondition` — the plain and strengthened value
  and the entailment they must keep
* `Meaning.strengthen`, `strongApplyDE` — implicature addition at a scope site, and Strong
  Application's DE branch

## Main results

* `strengthen_strong_eq_of_isGreatest`, `strongApplyDE_strong_eq_of_isGreatest` — negating all
  strictly stronger alternatives coincides with the paper's `σ` where `σ` is defined
* `some_not_all_implicature`, `doubt_and_indirect_implicature` — direct and indirect implicatures
* `and_blocks_any`, `or_licenses_any` — intervention: *any* under *and* competes with a strong
  meaning, under *or* it does not

## Implementation notes

Numbered items follow the circulated manuscript (the "Bicocca, May 2001"
version); the published chapter may renumber. The paper's scalar assertion `σ`
is a definite description — *the* weakest alternative asymmetrically entailing
the target, ⊥ if none — well-defined only when the stronger alternatives have a
greatest element, as on the paper's linearly ordered scales. `Meaning.strengthen`
and `strongApplyDE` instead negate *all* strictly stronger alternatives, a total
operation that coincides with negating `σ` exactly where `σ` is defined
(`strengthen_strong_eq_of_isGreatest`, `strongApplyDE_strong_eq_of_isGreatest`;
the `σ = ⊥` case is the empty intersection). The
appendix's `‖α‖^S` is a *set* of admissible strong meanings (implicature
addition at a scope site is optional); `Meaning.strong` tracks the maximal
admissible strengthening, the path the paper's own computations follow.

## References

* [chierchia-2004]
* [krifka-1995a]
-/

@[expose] public section

namespace Chierchia2004


variable {World : Type*}

/-! ### Strengthened meanings -/

/-- The semantic values the parallel recursion assigns to a propositional
node: the plain value `‖α‖`, the strengthened value `‖α‖^S`, and the active
scalar alternatives. -/
structure Meaning (World : Type*) where
  /-- The plain semantic value `‖α‖`. -/
  plain : Set World
  /-- The strengthened semantic value `‖α‖^S`. -/
  strong : Set World
  /-- The active scalar alternatives. -/
  alternatives : Set (Set World)

/-- (73a): a lexical item's strong meaning is its plain meaning. -/
def Meaning.lexical (φ : Set World) (ALT : Set (Set World)) :
    Meaning World :=
  ⟨φ, φ, ALT⟩

/-- The Strength Condition (§3.1): the strong value entails the plain value,
`sm.strong ⊆ sm.plain`. -/
def Meaning.StrengthCondition (sm : Meaning World) : Prop :=
  sm.strong ⊆ sm.plain

theorem Meaning.lexical_strengthCondition (φ : Set World) (ALT : Set (Set World)) :
    (Meaning.lexical φ ALT).StrengthCondition :=
  λ _ h => h

/-! ### Krifka's rule -/

/-- Krifka's rule (75) [krifka-1995a]: at a scope site, conjoin the strong
value with the negations of the strictly stronger alternatives. -/
def Meaning.strengthen (sm : Meaning World) : Meaning World where
  plain := sm.plain
  strong := sm.strong ∩ ⋂ a ∈ {a ∈ sm.alternatives | a ⊂ sm.plain}, aᶜ
  alternatives := sm.alternatives

variable {sm : Meaning World} {w : World}

@[simp]
theorem Meaning.mem_strengthen_strong :
    w ∈ sm.strengthen.strong ↔
      w ∈ sm.strong ∧ ∀ a ∈ sm.alternatives, a ⊂ sm.plain → w ∉ a := by
  simp [Meaning.strengthen]

/-- Strengthening preserves the Strength Condition. -/
theorem Meaning.StrengthCondition.strengthen (h : sm.StrengthCondition) :
    sm.strengthen.StrengthCondition :=
  λ _ hw => h hw.1

/-- Strengthening is proper whenever some activated alternative is strictly
stronger and consistent. -/
theorem Meaning.strengthen_strong_ssubset (hsc : sm.StrengthCondition)
    (h : ∃ a ∈ sm.alternatives, a ⊂ sm.plain ∧ a.Nonempty) :
    sm.strengthen.strong ⊂ sm.plain := by
  obtain ⟨a, haALT, haφ, w, hwa⟩ := h
  exact (Set.ssubset_iff_of_subset (λ _ hw => hsc hw.1)).mpr
    ⟨w, haφ.1 hwa, λ hmem => (mem_strengthen_strong.1 hmem).2 a haALT haφ hwa⟩

/-- Agreement with the paper's scalar assertion `σ`: whenever the strictly
stronger alternatives have a weakest member `a₀` — the case in which (2)'s
definite description is defined, as on linearly ordered scales — negating all
of them is negating `a₀` alone. -/
theorem Meaning.strengthen_strong_eq_of_isGreatest {a₀ : Set World}
    (h : IsGreatest {a ∈ sm.alternatives | a ⊂ sm.plain} a₀) :
    sm.strengthen.strong = sm.strong ∩ a₀ᶜ := by
  ext w
  simp only [mem_strengthen_strong, Set.mem_inter_iff, Set.mem_compl_iff]
  exact ⟨λ ⟨hw, hall⟩ => ⟨hw, hall a₀ h.1.1 h.1.2⟩,
    λ ⟨hw, h₀⟩ => ⟨hw, λ a haA haφ hwa => h₀ (h.2 ⟨haA, haφ⟩ hwa)⟩⟩

/-- A node none of whose alternatives is strictly stronger strengthens
vacuously — the strongest member of a scale triggers no implicature ((130)). -/
theorem Meaning.strengthen_strong_eq_of_not_ssubset
    (h : ∀ a ∈ sm.alternatives, ¬a ⊂ sm.plain) :
    sm.strengthen.strong = sm.strong :=
  Set.ext λ _ => ⟨λ hw => hw.1,
    λ hw => mem_strengthen_strong.2 ⟨hw, λ a ha hss => absurd hss (h a ha)⟩⟩

/-- Strengthening over a pair scale whose second member is strictly stronger:
the classic "φ but not ψ" implicature. -/
theorem Meaning.strengthen_strong_lexical_pair {φ ψ : Set World} (h : ψ ⊂ φ) :
    (Meaning.lexical φ {φ, ψ}).strengthen.strong = φ \ ψ := by
  rw [Set.sdiff_eq]
  exact Meaning.strengthen_strong_eq_of_isGreatest
    ⟨⟨Or.inr rfl, h⟩, by rintro a ⟨rfl | rfl, ha⟩; exacts [absurd ha (lt_irrefl _), le_rfl]⟩

/-! ### Scale axioms -/

/-- An admissible context choice of scale for an uttered scalar term — the
scale axioms (99). -/
structure IsScaleSelection (lexicalScale chosen : Set (Set World)) (utt : Set World) :
    Prop where
  /-- (99a): the chosen scale is a subset of the lexical scale. -/
  chosen_subset : chosen ⊆ lexicalScale
  /-- (99b): the chosen scale has at least two members. -/
  nontrivial : chosen.Nontrivial
  /-- The uttered term belongs to its chosen scale (presupposed by (99)). -/
  utt_mem : utt ∈ chosen
  /-- (99c): the uttered term is not the strongest chosen member whenever the
  lexical scale offers a stronger one — the "if possible" proviso. -/
  not_strongest : (∃ a ∈ lexicalScale, a ⊂ utt) → ∃ a ∈ chosen, a ⊂ utt

/-- Under the scale axioms, a stronger lexical alternative guarantees proper
strengthening — the point of the (99c) proviso. -/
theorem IsScaleSelection.strengthen_ssubset {lex chosen : Set (Set World)} {utt : Set World}
    (h : IsScaleSelection lex chosen utt) (hstr : ∃ a ∈ lex, a ⊂ utt)
    (hne : ∀ a ∈ chosen, a ⊂ utt → a.Nonempty) :
    (Meaning.lexical utt chosen).strengthen.strong ⊂ utt :=
  let ⟨a, ha, hau⟩ := h.not_strongest hstr
  Meaning.strengthen_strong_ssubset (Meaning.lexical_strengthCondition utt chosen)
    ⟨a, ha, hau, hne a ha hau⟩

/-! ### Downward entailingness suspends implicatures -/

/-- Generalization on SIs (53): a DE function maps the strengthened argument to
a *weaker* matrix value, so keeping a direct implicature under DE embedding
would violate the Strength Condition — implicatures are suspended in exactly
the *any*-licensing environments. -/
theorem si_npi_generalization {f : Set World → Set World} (hDE : Antitone f)
    (hsc : sm.StrengthCondition) :
    f sm.plain ⊆ f sm.strong :=
  hDE hsc

/-- Instantiation of (53) at strengthened arguments. -/
theorem de_blocks_direct_si {f : Set World → Set World} (hDE : Antitone f)
    (hsc : sm.StrengthCondition) :
    f sm.plain ⊆ f sm.strengthen.strong :=
  si_npi_generalization hDE hsc.strengthen

/-! ### Strong Application -/

/-- Apply a function and its strengthening to a node's two tracks, projecting
alternatives pointwise ((82b)) — the non-DE clause of Strong Application (84). -/
def Meaning.map (f fS : Set World → Set World) (g : Meaning World) : Meaning World :=
  ⟨f g.plain, fS g.strong, f '' g.alternatives⟩

/-- The Strength-Condition fallback (§3.1): remove the argument's implicatures
by resetting its strong track to the plain value. -/
def Meaning.weaken (g : Meaning World) : Meaning World :=
  ⟨g.plain, g.plain, g.alternatives⟩

/-- Strong Application (84), DE clause: strip the argument's implicatures,
apply, and re-strengthen at the matrix level. -/
def strongApplyDE (f fS : Set World → Set World) (g : Meaning World) : Meaning World :=
  (g.weaken.map f fS).strengthen

variable {f fS : Set World → Set World} {g : Meaning World}

@[simp]
theorem mem_strongApplyDE_strong :
    w ∈ (strongApplyDE f fS g).strong ↔
      w ∈ fS g.plain ∧ ∀ a ∈ g.alternatives, f a ⊂ f g.plain → w ∉ f a := by
  simp [strongApplyDE, Meaning.map, Meaning.weaken]

/-- (84) at a lexical argument: apply plainly and re-run Krifka's rule over the
image scale. -/
theorem strongApplyDE_lexical (f : Set World → Set World) (φ : Set World)
    (ALT : Set (Set World)) :
    strongApplyDE f f (.lexical φ ALT) = (Meaning.lexical (f φ) (f '' ALT)).strengthen :=
  rfl

/-- Agreement with (84)'s matrix-level `σ`: inherited from the (75) lemma, the
DE clause being strengthening at the mapped node. -/
theorem strongApplyDE_strong_eq_of_isGreatest {ψ₀ : Set World}
    (h : IsGreatest {ψ ∈ f '' g.alternatives | ψ ⊂ f g.plain} ψ₀) :
    (strongApplyDE f fS g).strong = fS g.plain ∩ ψ₀ᶜ :=
  Meaning.strengthen_strong_eq_of_isGreatest (sm := g.weaken.map f fS) h

/-- The non-DE clause of (84) preserves the Strength Condition when `f` is UE
and its strengthening entails it. -/
theorem Meaning.map_strengthCondition (hf : Monotone f) (hfS : fS ≤ f)
    (hg : g.StrengthCondition) :
    (g.map f fS).StrengthCondition :=
  λ _ hw => hf hg (hfS _ hw)

/-- The DE clause of (84) satisfies the Strength Condition by construction: it
falls back to the plain argument before re-strengthening. -/
theorem strongApplyDE_strengthCondition (hfS : fS ≤ f) :
    (strongApplyDE f fS g).StrengthCondition :=
  Meaning.StrengthCondition.strengthen (hfS g.plain)

/-! ### The direct implicature of "some" -/

/-- Worlds for "John saw some students": saw none, some-but-not-all, or all. -/
def sawSome : Set (Fin 3) := {w | w ≠ 0}

/-- "John saw every student" — true only in the saw-all world. -/
def sawEvery : Set (Fin 3) := {w | w = 2}

theorem sawEvery_ssubset : sawEvery ⊂ sawSome :=
  (Set.ssubset_iff_of_subset (λ w hw => by simp_all [sawEvery, sawSome])).mpr
    ⟨1, by simp [sawSome], by simp [sawEvery]⟩

/-- (74)–(76): strengthening the lexical node of "John saw some students"
computes the direct implicature — some but not every. -/
theorem some_not_all_implicature :
    (Meaning.lexical sawSome {sawSome, sawEvery}).strengthen.strong =
      sawSome \ sawEvery :=
  Meaning.strengthen_strong_lexical_pair sawEvery_ssubset

/-! ### The doubt example -/

/-- "John drinks", over worlds valuating ⟨drinks, drives⟩. -/
def drinks : Set (Bool × Bool) := {w | w.1}

/-- "John drives". -/
def drives : Set (Bool × Bool) := {w | w.2}

theorem drinks_ne_drives : drinks ≠ drives :=
  λ h => by simpa [drinks, drives] using Set.ext_iff.1 h (true, false)

/-- The (81)–(83) computation: embedding "John drinks and drives" under DE
*doubt* (modelled as complement) yields the indirect implicature (83b) — doubt
the conjunction yet believe the disjunction. -/
theorem doubt_and_indirect_implicature :
    (strongApplyDE compl compl
        (.lexical (drinks ∩ drives) {drinks ∩ drives, drinks ∪ drives})).strong =
      (drinks ∩ drives)ᶜ ∩ (drinks ∪ drives) := by
  have h : (drinks ∪ drives)ᶜ ⊂ (drinks ∩ drives)ᶜ :=
    compl_lt_compl_iff_lt.2 (inf_lt_sup.2 drinks_ne_drives)
  rw [strongApplyDE_lexical, Set.image_pair,
    Meaning.strengthen_strong_lexical_pair h, Set.sdiff_compl]

/-! ### Intervention -/

/-- Worlds valuate ⟨John ate the cake, drank coffee c₁, drank coffee c₂⟩;
`{c₁}` is the default coffee domain and `{c₁, c₂}` its widening. -/
def ateCake : Set (Bool × Bool × Bool) := {w | w.1}

/-- "John drank some coffee" on the default domain `{c₁}`. -/
def drankC1 : Set (Bool × Bool × Bool) := {w | w.2.1}

/-- "John drank coffee c₂" — the widened part of the domain. -/
def drankC2 : Set (Bool × Bool × Bool) := {w | w.2.2}

/-- (128b): universal closure over domain choices of "I doubt that John ate the
cake and drank any coffee", spelled out over the nonempty subdomains of
`{c₁, c₂}`. -/
def anyAndClosure : Set (Bool × Bool × Bool) :=
  (ateCake ∩ drankC1)ᶜ ∩ (ateCake ∩ drankC2)ᶜ ∩ (ateCake ∩ (drankC1 ∪ drankC2))ᶜ

/-- The *some*-competitor of (128): "I doubt that John ate the cake and drank
some coffee" ((129a)), strengthened by the DE clause of (84). -/
def someAndCompetitor : Meaning (Bool × Bool × Bool) :=
  strongApplyDE compl compl
    (.lexical (ateCake ∩ drankC1) {ateCake ∩ drankC1, ateCake ∪ drankC1})

theorem ateCake_ne_drankC1 : ateCake ≠ drankC1 :=
  λ h => by simpa [ateCake, drankC1] using Set.ext_iff.1 h (true, false, false)

/-- (129b): the competitor's strong meaning — doubt the conjunction yet believe
John did one of the two. -/
theorem someAndCompetitor_strong :
    someAndCompetitor.strong = (ateCake ∩ drankC1)ᶜ ∩ (ateCake ∪ drankC1) := by
  have h : (ateCake ∪ drankC1)ᶜ ⊂ (ateCake ∩ drankC1)ᶜ :=
    compl_lt_compl_iff_lt.2 (inf_lt_sup.2 ateCake_ne_drankC1)
  simp only [someAndCompetitor]
  rw [strongApplyDE_lexical, Set.image_pair,
    Meaning.strengthen_strong_lexical_pair h, Set.sdiff_compl]

/-- (127)/(128): *any* is blocked under *doubt … and*. The universal closure
fails to entail the competitor's *strong* meaning — the indirect implicature of
the intervening *and* is what breaks the entailment. -/
theorem and_blocks_any : ¬anyAndClosure ⊆ someAndCompetitor.strong := by
  intro h
  have hw : (false, false, false) ∈ anyAndClosure := by
    simp [anyAndClosure, ateCake, drankC1, drankC2]
  have := (someAndCompetitor_strong ▸ h hw).2
  simp [ateCake, drankC1] at this

/-- The closure does entail the competitor's *plain* meaning: competition with
plain meanings ((122)-style) would wrongly license *any* under *and*. -/
theorem and_any_entails_plain : anyAndClosure ⊆ (ateCake ∩ drankC1)ᶜ :=
  λ _ hw => hw.1.1

/-- (130): universal closure of "I doubt that John ate the cake or drank any
coffee" over the nonempty subdomains of `{c₁, c₂}`. -/
def anyOrClosure : Set (Bool × Bool × Bool) :=
  (ateCake ∪ drankC1)ᶜ ∩ (ateCake ∪ drankC2)ᶜ ∩ (ateCake ∪ (drankC1 ∪ drankC2))ᶜ

/-- The *some*-competitor of (130): under *doubt*, *or* is the strongest member
of its scale, so no indirect implicature arises. -/
def someOrCompetitor : Meaning (Bool × Bool × Bool) :=
  strongApplyDE compl compl
    (.lexical (ateCake ∪ drankC1) {ateCake ∩ drankC1, ateCake ∪ drankC1})

/-- (130): the or-competitor's strong meaning is its plain meaning — the
strongest member of a scale triggers no implicature. -/
theorem someOrCompetitor_strong :
    someOrCompetitor.strong = (ateCake ∪ drankC1)ᶜ := by
  simp only [someOrCompetitor]
  rw [strongApplyDE_lexical, Set.image_pair]
  refine Meaning.strengthen_strong_eq_of_not_ssubset (λ a ha => ?_)
  rcases ha with rfl | rfl
  · exact λ hlt => lt_irrefl _ ((compl_lt_compl_iff_lt.1 hlt).trans_le inf_le_sup)
  · exact lt_irrefl _

/-- (130): *any* is licensed under *doubt … or* — the closure entails the
competitor's strong meaning, which never gained an indirect implicature. -/
theorem or_licenses_any : anyOrClosure ⊆ someOrCompetitor.strong := by
  rw [someOrCompetitor_strong]
  exact λ _ hw => hw.1.1

end Chierchia2004
