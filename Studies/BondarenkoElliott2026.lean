module

public import Linglib.Logic.Truthmaker.Basic
public import Linglib.Semantics.Mereology

/-!
# Bondarenko and Elliott (2026): Monotonicity via mereology in the semantics of attitude reports

[sharvit-2024]'s puzzle: a weak NPI is licensed in the relative clause of *Katya doesn't
believe the rumor that Anton has ever spread* but not in the complement clause of *Katya
doesn't believe the rumor that Anton has ever snowboarded*. Weak NPIs need an environment
that is Strawson downward- and not Strawson upward-entailing. Under the content-based
approach to clausal embedding, subset semantics for the *that*-clause makes the singular
definite both, by uniqueness collapse, while equality semantics (`CONT x = ⟦S⟧`) makes it
neither, by functionality. [bondarenko-elliott-2026] keep equality semantics and add
mereological structure to attitudinal eventualities and their contents, with informational
parthood `p' ≤ p` iff `p ⊆ p'`: the content function reflects proper parthood (`MSI`), the
theme function preserves it (`MSO`), a believing has the content of its theme (`TECM`), and
parts of believings are believings of the same holder (`BelievingDIV`).

`MSI` alone closes belief under entailment (`believes_of_ssubset`, `not_believes_of_ssubset`).
For *Katya believes the rumor that p*, the chain `TECM ∘ MSI ∘ BelievingDIV ∘ MSO` closes
the positive sentence under weakening of the rumor's content
(`believesTheRumorThat_of_ssubset`), so its negation is Strawson downward-entailing in the
restrictor (`not_believesTheRumorThat_of_ssubset`), while a model in which the agent
believes the weaker rumor but not the stronger shows that the negation is not Strawson
upward-entailing (`negated_not_sue`) — the profile the licensing condition demands. Closure
under conjunction needs two further principles, that the content of a sum is the
intersection of the contents and that one holder's believings are closed under sum
(`believes_inter`); without them belief need not close (`not_believes_inter`). Finally, the
paper's refinement of informational parthood to Fine's conjunctive parthood on alternative
sets is `Truthmaker.IsConjunctivePart`, with alternatives ordered informationally in
`(Set W)ᵒᵈ`. Between single alternatives it is entailment
(`isConjunctivePart_singleton_iff_subset`), and its witness that disjunction introduction
fails — *Jessica married an American linguist* does not make *Jessica married a linguist or
a philosopher* a conjunctive part — is `not_isConjunctivePart_disjunction`.

## References

* [bondarenko-elliott-2026]
* [cheng-1973]
* [sharvit-2024]
-/

@[expose] public section

namespace BondarenkoElliott2026

open Mereology

variable {V E W : Type*}

/-! ### Constraints on the lexical maps

The content, theme and holder maps are partial, so they return `Option`; a content is a
set of worlds, and `p ⊂ p'` says `p'` is informationally a proper part of `p`. -/

section Constraints

variable [Preorder V] [Preorder E]

/-- The content map maps to sub-parts of the input when every proper informational part of a
content is the content of a proper part of its bearer. -/
def MSI (CONT : V → Option (Set W)) : Prop :=
  ∀ ⦃x p p'⦄, CONT x = some p → p ⊂ p' → ∃ x', x' < x ∧ CONT x' = some p'

/-- The theme map maps to sub-parts of the output when every proper part of an eventuality has
a theme that is a proper part of the eventuality's theme. -/
def MSO (THEME : V → Option E) : Prop :=
  ∀ ⦃e e' te⦄, e' < e → THEME e = some te → ∃ x', x' < te ∧ THEME e' = some x'

/-- A predicate `P` of eventualities satisfies theme-event content matching when every
`P`-eventuality has the content of its theme. -/
def TECM (P : V → Prop) (CONT_v : V → Option (Set W)) (CONT_e : E → Option (Set W))
    (THEME : V → Option E) : Prop :=
  ∀ ⦃e te⦄, P e → THEME e = some te → CONT_v e = CONT_e te

/-- Parts of a believing are believings of the same holder — divisive reference
([cheng-1973]) for attitudinal eventualities. -/
structure BelievingDIV (believe : V → Prop) (HOLDER : V → Option E) : Prop where
  div : DIV believe
  holder : ∀ ⦃e e' M⦄, HOLDER e = some M → e' ≤ e → HOLDER e' = some M

/-- Location at a world is inherited by parts, as worlds are maximal eventualities. -/
def LocatedDIV (located : V → W → Prop) : Prop :=
  ∀ ⦃e e' : V⦄ ⦃w : W⦄, e' ≤ e → located e w → located e' w

end Constraints

/-! ### Belief and closure under entailment -/

/-- Equality semantics for *M believes p*: a believing of `M` with content `p`. -/
def Believes (believe : V → Prop) (HOLDER : V → Option E) (CONT : V → Option (Set W)) (M : E)
    (p : Set W) : Prop :=
  ∃ e, believe e ∧ HOLDER e = some M ∧ CONT e = some p

section Closure

variable [Preorder V] {believe : V → Prop} {HOLDER : V → Option E} {CONT : V → Option (Set W)}
  {M : E} {p p' : Set W}

theorem believes_of_ssubset (hMSI : MSI CONT) (hDIV : BelievingDIV believe HOLDER) (hlt : p ⊂ p')
    (h : Believes believe HOLDER CONT M p) : Believes believe HOLDER CONT M p' :=
  let ⟨_, hbel, hhol, hcont⟩ := h
  let ⟨e', hlt', hcont'⟩ := hMSI hcont hlt
  ⟨e', hDIV.div hlt'.le hbel, hDIV.holder hhol hlt'.le, hcont'⟩

theorem not_believes_of_ssubset (hMSI : MSI CONT) (hDIV : BelievingDIV believe HOLDER)
    (hlt : p ⊂ p') (h : ¬ Believes believe HOLDER CONT M p') :
    ¬ Believes believe HOLDER CONT M p :=
  fun hb ↦ h (believes_of_ssubset hMSI hDIV hlt hb)

end Closure

/-! ### The Sharvit configuration: *believes the rumor that p* -/

section Sharvit

variable [Preorder V] [Preorder E]

/-- Equality semantics for *M believes the rumor that p* at world `w`: a believing of `M`
located at `w` whose theme is a rumor with content `p`. -/
def BelievesTheRumorThat (believe : V → Prop) (HOLDER : V → Option E)
    (located : V → W → Prop) (THEME : V → Option E) (rumor : E → Prop)
    (CONT_e : E → Option (Set W)) (M : E) (p : Set W) (w : W) : Prop :=
  ∃ e r, located e w ∧ believe e ∧ HOLDER e = some M ∧ THEME e = some r ∧ rumor r ∧
    CONT_e r = some p

variable {believe : V → Prop} {HOLDER : V → Option E} {CONT_v : V → Option (Set W)}
  {CONT_e : E → Option (Set W)} {THEME : V → Option E} {rumor : E → Prop}
  {located : V → W → Prop} {M : E} {p p' : Set W} {w : W}

/-- The positive sentence is closed under weakening of the rumor's content. The believing's
content is its theme's (`TECM`), which has a part with the weaker content (`MSI`) that is a
located believing of the same holder (`BelievingDIV`) themed to a part of the rumor (`MSO`),
which is a rumor with that content (`TECM` again). -/
theorem believesTheRumorThat_of_ssubset (hMSI : MSI CONT_v) (hMSO : MSO THEME)
    (hTECM : TECM believe CONT_v CONT_e THEME) (hDIV : BelievingDIV believe HOLDER)
    (hRumor : DIV rumor) (hLoc : LocatedDIV located) (hlt : p ⊂ p')
    (h : BelievesTheRumorThat believe HOLDER located THEME rumor CONT_e M p w) :
    BelievesTheRumorThat believe HOLDER located THEME rumor CONT_e M p' w := by
  obtain ⟨e, r, hloc, hbel, hhol, hthm, hrum, hcont⟩ := h
  obtain ⟨e', hlt', hcont'⟩ := hMSI ((hTECM hbel hthm).trans hcont) hlt
  obtain ⟨r', hr', hthm'⟩ := hMSO hlt' hthm
  have hbel' := hDIV.div hlt'.le hbel
  exact ⟨e', r', hLoc hlt'.le hloc, hbel', hDIV.holder hhol hlt'.le, hthm', hRumor hr'.le hrum,
    (hTECM hbel' hthm').symm.trans hcont'⟩

theorem not_believesTheRumorThat_of_ssubset (hMSI : MSI CONT_v) (hMSO : MSO THEME)
    (hTECM : TECM believe CONT_v CONT_e THEME) (hDIV : BelievingDIV believe HOLDER)
    (hRumor : DIV rumor) (hLoc : LocatedDIV located) (hlt : p ⊂ p')
    (h : ¬ BelievesTheRumorThat believe HOLDER located THEME rumor CONT_e M p' w) :
    ¬ BelievesTheRumorThat believe HOLDER located THEME rumor CONT_e M p w :=
  fun hb ↦ h (believesTheRumorThat_of_ssubset hMSI hMSO hTECM hDIV hRumor hLoc hlt hb)

end Sharvit

/-- The three-element domain of the not-SUE model, the holder and the two rumors. -/
private inductive NotSUE where
  | katya
  | strong
  | weak
  deriving DecidableEq

private instance : Preorder NotSUE where
  le := Eq
  le_refl _ := rfl
  le_trans _ _ _ := Eq.trans

/-- The negated sentence is not Strawson upward-entailing. Some model satisfying all of the
constraints has Katya believe the weaker rumor (content `Set.univ`) but not the
stronger one (content `{true}`). Functionality of the content map, not the mereological
constraints, is what blocks the inference. -/
theorem negated_not_sue :
    ∃ (V E W : Type) (_ : Preorder V) (_ : Preorder E) (believe : V → Prop)
      (HOLDER : V → Option E) (CONT_v : V → Option (Set W)) (CONT_e : E → Option (Set W))
      (THEME : V → Option E)
      (rumor : E → Prop) (located : V → W → Prop) (M : E) (p p' : Set W) (w : W),
      MSI CONT_v ∧ MSO THEME ∧ TECM believe CONT_v CONT_e THEME ∧
        BelievingDIV believe HOLDER ∧ DIV rumor ∧ LocatedDIV located ∧ p ⊂ p' ∧
        BelievesTheRumorThat believe HOLDER located THEME rumor CONT_e M p' w ∧
        ¬ BelievesTheRumorThat believe HOLDER located THEME rumor CONT_e M p w := by
  refine ⟨Unit, NotSUE, Bool, inferInstance, inferInstance, fun _ ↦ True, fun _ ↦ some .katya,
    fun _ ↦ some Set.univ, fun | .katya => none | .strong => some {true} | .weak => some Set.univ,
    fun _ ↦ some .weak, fun s ↦ s = .strong ∨ s = .weak, fun _ _ ↦ True, .katya, {true},
    Set.univ, true, ?_, ?_, ?_, ⟨fun _ _ _ _ ↦ trivial, fun _ _ _ h _ ↦ h⟩, ?_,
    fun _ _ _ _ _ ↦ trivial,
    ⟨Set.subset_univ _, fun h ↦ Bool.false_ne_true (h (Set.mem_univ false))⟩,
    ⟨(), .weak, trivial, trivial, rfl, rfl, Or.inr rfl, rfl⟩, ?_⟩
  · rintro _ p₀ q hcont hlt
    obtain rfl : Set.univ = p₀ := Option.some.inj hcont
    exact absurd (Set.subset_univ q) hlt.2
  · intro e e' _ hlt _
    cases e; cases e'
    exact (lt_irrefl _ hlt).elim
  · rintro _ te _ hthm
    rw [← Option.some.inj hthm]
  · rintro r r' (rfl : r' = r) hrum
    exact hrum
  · rintro ⟨_, r, _, _, _, hthm, _, hcont⟩
    rw [← Option.some.inj hthm] at hcont
    exact Bool.false_ne_true
      (show false ∈ ({true} : Set Bool) from Option.some.inj hcont ▸ Set.mem_univ false)

/-! ### Closure under conjunction -/

section Conjunction

variable [SemilatticeSup V] {believe : V → Prop} {HOLDER : V → Option E}
  {CONT : V → Option (Set W)}

/-- The content of a sum of contentful entities is the intersection of their contents. -/
def CONTSum (CONT : V → Option (Set W)) : Prop :=
  ∀ ⦃x y px py⦄, CONT x = some px → CONT y = some py → CONT (x ⊔ y) = some (px ∩ py)

/-- One holder's believings are closed under sum. -/
def SumClosed (believe : V → Prop) (HOLDER : V → Option E) : Prop :=
  ∀ ⦃e e' M⦄, believe e → believe e' → HOLDER e = some M → HOLDER e' = some M →
    believe (e ⊔ e') ∧ HOLDER (e ⊔ e') = some M

theorem believes_inter (hCONT : CONTSum CONT) (hSum : SumClosed believe HOLDER) {M : E}
    {p q : Set W} (hp : Believes believe HOLDER CONT M p) (hq : Believes believe HOLDER CONT M q) :
    Believes believe HOLDER CONT M (p ∩ q) :=
  let ⟨e, hbe, hhe, hce⟩ := hp
  let ⟨e', hbe', hhe', hce'⟩ := hq
  let ⟨hb, hh⟩ := hSum hbe hbe' hhe hhe'
  ⟨e ⊔ e', hb, hh, hCONT hce hce'⟩

end Conjunction

theorem not_believes_inter :
    ∃ (V E W : Type) (_ : Preorder V) (believe : V → Prop) (HOLDER : V → Option E)
      (CONT : V → Option (Set W)) (M : E) (p q : Set W),
      Believes believe HOLDER CONT M p ∧ Believes believe HOLDER CONT M q ∧
        ¬ Believes believe HOLDER CONT M (p ∩ q) := by
  refine ⟨Bool, Unit, Bool, inferInstance, fun _ ↦ True, fun _ ↦ some (),
    fun e ↦ some (if e then {true} else {false}), (), {true}, {false},
    ⟨true, trivial, rfl, rfl⟩, ⟨false, trivial, rfl, rfl⟩, ?_⟩
  rintro ⟨e, _, _, hcont⟩
  cases e <;> simp only [Option.some.injEq, Bool.false_eq_true, ↓reduceIte] at hcont
  · exact absurd (hcont ▸ rfl : (false : Bool) ∈ ({true} : Set Bool) ∩ {false}).1 (by decide)
  · exact absurd (hcont ▸ rfl : (true : Bool) ∈ ({true} : Set Bool) ∩ {false}).2 (by decide)

/-! ### Conjunctive parthood

Alternatives are ordered informationally, so `toDual p ≤ toDual p'` in `(Set W)ᵒᵈ` when
`p' ⊆ p`. -/

open Truthmaker OrderDual

theorem isConjunctivePart_singleton_iff_subset (p q : Set W) :
    IsConjunctivePart ({toDual q} : Set (Set W)ᵒᵈ) {toDual p} ↔ p ⊆ q :=
  isConjunctivePart_singleton_singleton

theorem not_isConjunctivePart_disjunction (p₁ p₂ p₃ : Set W) (h : ¬ p₃ ⊆ p₂) :
    ¬ IsConjunctivePart ({toDual p₁, toDual p₂} : Set (Set W)ᵒᵈ) {toDual p₃} := fun hc ↦
  h ((isConjunctivePart_singleton_right_iff (Set.insert_nonempty _ _)).1 hc _
    (Set.mem_insert_of_mem _ rfl))

end BondarenkoElliott2026
