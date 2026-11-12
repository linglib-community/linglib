module

public import Studies.Gajewski2007
public import Linglib.Semantics.Exhaustification.Basic
public import Linglib.Data.Examples.Romoli2013b

/-!
# Romoli (2013): A scalar implicature-based approach to neg-raising

Romoli derives neg-raising as a scalar implicature. A neg-raising predicate such as *think* is a
plain universal over its modal base, and its lexical alternative is the excluded middle, where a
predicate without neg-raising such as *be certain* has its existential dual. Exhaustifying a
negated neg-raising predicate against the negated excluded middle [gives the predicate over the
negated complement](##Romoli2013b.exhNot_eq_posExt_negation), the truth set that Gajewski's
presupposition gives, while the same sentences are plainly false, not undefined, where
the subject has no opinion. Since the excluded middle is entailed wherever the predicate is not
under a downward entailing operator, it [does not project](##Romoli2013b.exh_of_monotone) from
questions, conditionals or modals as a presupposition would, and in the restrictor of a universal
exhaustification yields [an inference of its
own](##Romoli2013b.isGreatest_everyWho). With the enriched meanings as the direct implicatures that
the licensing of strict NPIs reads, the library's licensing theory [admits the strict NPI of each
example where Romoli accepts it](##Romoli2013b.judgments_predicted), the restrictors of
quantifiers aside.

## Implementation notes

* Romoli's exhaustification denies every alternative that the prejacent does not entail. Which
  alternatives those are is fixed by the theory, not by the model: the families of alternatives
  are indexed in order of logical strength, and the exhaustified prejacent holds where its index
  is the greatest true one, `IsGreatest`. In an upward entailing
  environment the excluded middle is the weaker alternative, which
  `Exhaustification.exh` shows in any model.
* Romoli adopts the proposal of Gajewski and of Chierchia that a strict NPI needs an environment
  that stays downward entailing once implicatures and presuppositions are added. The library's
  `PolarityItem.Licenser.scalar` pairs an operator with its meaning enriched by its direct
  implicature, and `Licenser.Carries` reads anti-additivity off the enriched meaning, so the two
  negated predicates are scalar licensers that share an operator and differ in the enrichment.

## TODO

* Suspension by relevance to the question under discussion, the negated universal, and the truth
  predicates *it is true that*, whose presupposition is to disrupt licensing in two of the
  examples, are not formalized.
* Stacked predicates are exhaustified here without the condition that exhaustification leave the
  presupposition of its prejacent untouched, which is what blocks the lowered reading of *want*
  over *believe*. It needs *want* with von Fintel's presupposition and exhaustification of
  presupposing prejacents.
* The restrictors of *every* and *no* are to fail to license because of their existential
  presupposition. The library's restrictor contexts carry none, and the example with *in weeks*
  awaits a lexical entry.

## References

* [romoli-2013b]
* [gajewski-2007]
* [gajewski-2011]
* [chierchia-2013]
* [von-fintel-1999]
-/

@[expose] public section

namespace Romoli2013b

open Exhaustification NegRaising PolarityItem NaturalLogic SetRel

variable {W : Type*} {R : SetRel W W} {p q : Set W} {w : W}

private theorem dom_inter_core_compl_union (R : SetRel W W) (p q : Set W) :
    R.dom ∩ R.core (p ∪ q)ᶜ = (R.dom ∩ R.core pᶜ) ∩ (R.dom ∩ R.core qᶜ) := by
  rw [Set.compl_union, core_inter, Set.inter_inter_distrib_left]

private theorem mem_dom_inter_core_compl_iff :
    w ∈ R.dom ∩ R.core pᶜ ↔ w ∉ R.core p ∧ w ∈ excludedMiddle R p :=
  (Set.ext_iff.1 (compl_core_inter_excludedMiddle R p) w).symm

/-! ### The basic case and negation (§5.1) -/

/-- Where a neg-raising predicate stands in an upward entailing environment `f`, the excluded
middle alternative is entailed and exhaustification adds nothing: unembedded (88), and under a
possibility modal (96). -/
theorem exh_of_monotone {V : Type*} {f : Set W → Set V} (hf : Monotone f) (R : SetRel W W)
    (p : Set W) :
    exh {f (R.core p), f (excludedMiddle R p)} (f (R.core p)) = f (R.core p) :=
  exh_eq_self <| by
    rintro _ (rfl | rfl)
    exacts [subset_rfl, hf (core_subset_excludedMiddle R p)]

-- On a chain of two alternatives the weaker is the greatest true one where it holds and the
-- stronger does not.
private theorem isGreatest_zero_fin_two {A : Fin 2 → Prop} :
    IsGreatest {i | A i} 0 ↔ A 0 ∧ ¬ A 1 :=
  ⟨fun h ↦ ⟨h.1, fun h1 ↦ absurd (h.2 h1) (by decide)⟩,
    fun h ↦ ⟨h.1, fun i hi ↦ match i, hi with
      | 0, _ => le_rfl
      | 1, h1 => absurd h1 h.2⟩⟩

-- An index is the greatest true one where it is true and every index not below it is false.
private theorem isGreatest_iff_forall_not {ι : Type*} [Preorder ι] {s : Set ι} {i : ι} :
    IsGreatest s i ↔ i ∈ s ∧ ∀ j, ¬ j ≤ i → j ∉ s :=
  and_congr_right fun _ ↦ ⟨fun h _ hj hs ↦ hj (h hs), fun h _ hs ↦ not_not.1 fun hj ↦ h _ hj hs⟩

/-- A negated neg-raising predicate exhaustified against its stronger alternative, the negated
excluded middle: the `exh[not P]` of (116). -/
def exhNot (R : SetRel W W) (p : Set W) : Set W :=
  {w | IsGreatest {i | w ∈ ![(R.core p)ᶜ, (excludedMiddle R p)ᶜ] i} 0}

theorem mem_exhNot_iff : w ∈ exhNot R p ↔ w ∉ R.core p ∧ w ∈ excludedMiddle R p := by
  rw [exhNot, Set.mem_ofPred_eq, isGreatest_zero_fin_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Set.mem_compl_iff, not_not]

-- (91)
theorem exhNot_eq (R : SetRel W W) (p : Set W) : exhNot R p = R.dom ∩ R.core pᶜ :=
  Set.ext fun _ ↦ mem_exhNot_iff.trans mem_dom_inter_core_compl_iff.symm

/-- Exhaustification denies the negated excluded middle, and the negated predicate becomes the
predicate over the negated complement (91): the scalar account and the presuppositional account of
[gajewski-2007] make a negated neg-raising predicate true at the same worlds. -/
theorem exhNot_eq_posExt_negation (R H : SetRel W W) (p : Set W) :
    exhNot R p = Trivalent.posExt (negation R H p) :=
  (exhNot_eq R p).trans (posExt_negation R H p).symm

open Classical in
-- Where the subject has no opinion the presuppositional predicate is undefined, and on the scalar
-- account the predicate and its exhaustified negation are both false (fn. 13).
theorem box_eq_undefined_of_notMem_excludedMiddle (H : SetRel W W)
    (hw : w ∉ excludedMiddle R p) :
    box R H (fun u ↦ Trivalent.ofProp (u ∈ p)) w = .undefined ∧ w ∉ R.core p ∧ w ∉ exhNot R p := by
  refine ⟨?_, fun hp ↦ hw (.inl hp), fun hn ↦ hw (mem_exhNot_iff.1 hn).2⟩
  by_contra hd
  exact hw (by simpa [Trivalent.posExt] using (box_ne_undefined_iff.1 hd).2)

-- (116)
theorem isAntiAdditive_exhNot (R : SetRel W W) : IsAntiAdditive (exhNot R) := fun p q ↦ by
  simp only [exhNot_eq, Set.sup_eq_union, Set.inf_eq_inter, dom_inter_core_compl_union]

-- (124)
theorem isGreatest_compl_core_preimage :
    IsGreatest {i | w ∈ ![(R.core p)ᶜ, (R.preimage p)ᶜ] i} 0 ↔
      w ∉ R.core p ∧ w ∈ R.preimage p := by
  rw [isGreatest_zero_fin_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Set.mem_compl_iff, not_not]

/-! ### Non-upward-entailing environments (§5.2.2) -/

variable {E : Type*} {B : E → SetRel W W} {Q : E → Set W}

/-- *Every x who P, Q*. -/
def everyWho (P Q : E → Set W) : Set W := {w | ∀ x, w ∈ P x → w ∈ Q x}

/-- In the restrictor of a universal, exhaustification adds that someone who believes the
complement false is outside the scope ((100)–(102)), an inference that the presuppositional
account does not make. -/
theorem isGreatest_everyWho :
    IsGreatest {i | w ∈ ![everyWho (fun x ↦ (B x).core p) Q,
        everyWho (fun x ↦ excludedMiddle (B x) p) Q] i} 0 ↔
      w ∈ everyWho (fun x ↦ (B x).core p) Q ∧ ∃ x, w ∈ (B x).core pᶜ ∧ w ∉ Q x := by
  rw [isGreatest_zero_fin_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  refine and_congr_right fun hw ↦ ⟨fun hn ↦ ?_, fun ⟨x, hx, hQ⟩ hall ↦ hQ (hall x (.inr hx))⟩
  by_contra hc
  exact hn fun x hx ↦ by_contra fun hQ ↦ hc ⟨x, hx.resolve_left fun hp ↦ hQ (hw x hp), hQ⟩

/-! ### Negative quantifiers (§7.2) -/

/-- *No one P*. -/
def noOne (P : E → Set W) : Set W := {w | ∀ x, w ∉ P x}

/-- *Not everyone P*, the alternative of *no one P* (162). -/
def notEvery (P : E → Set W) : Set W := {w | ∃ x, w ∉ P x}

/-- The alternatives of *no one thinks p* (165b), indexed by the quantifier and by the predicate,
each with the stronger alternative second. -/
def noOneAlternatives (B : E → SetRel W W) (p : Set W) (i : Fin 2 × Fin 2) : Set W :=
  ![notEvery, noOne] i.1 fun x ↦ ![(B x).core p, excludedMiddle (B x) p] i.2

-- (164), (165)
theorem isGreatest_noOne [Nonempty E] :
    IsGreatest {i | w ∈ noOneAlternatives B p i} (1, 0) ↔
      w ∈ ⋂ x, (B x).dom ∩ (B x).core pᶜ := by
  rw [isGreatest_iff_forall_not]
  simp only [Set.mem_ofPred_eq, noOneAlternatives, Prod.forall, Fin.forall_fin_two, Prod.mk_le_mk,
    Matrix.cons_val_zero, Matrix.cons_val_one, Set.mem_iInter, mem_dom_inter_core_compl_iff]
  refine ⟨fun ⟨hw, ⟨_, h01⟩, _, _⟩ x ↦ ⟨hw x, ?_⟩, fun hw ↦ ⟨fun x ↦ (hw x).1,
    ⟨fun h ↦ by simp at h, fun _ ⟨x, hx⟩ ↦ hx (hw x).2⟩,
    fun h ↦ by simp at h,
    fun _ hn ↦ hn (Classical.arbitrary E) (hw _).2⟩⟩
  by_contra hx
  exact h01 (by simp) ⟨x, hx⟩

-- (164), (165) [gajewski-2007]
theorem isGreatest_noOne_iff_mem_posExt_noOneNR [Nonempty E] :
    IsGreatest {i | w ∈ noOneAlternatives B p i} (1, 0) ↔
      w ∈ Trivalent.posExt (Gajewski2007.noOneNR Set.univ B p) := by
  rw [isGreatest_noOne, Gajewski2007.posExt_noOneNR]
  simp [Gajewski2007.every]

/-! ### Stacked predicates (§7.3.1) -/

/-- The alternatives of a negated neg-raising predicate over another (172c), indexed by the
alternatives of the higher and of the lower predicate. -/
def stackAlternatives (R₁ R₂ : SetRel W W) (p : Set W) (i : Fin 2 × Fin 2) : Set W :=
  (![R₁.core, excludedMiddle R₁] i.1 (![R₂.core p, excludedMiddle R₂ p] i.2))ᶜ

/-- Exhaustified against its three alternatives, a negated neg-raising predicate over another has
the negation below both, whichever predicate is on top ((172)–(175)). The scalar account alone
therefore predicts no asymmetry between *believe* over *want* and *want* over *believe*. -/
theorem isGreatest_stack (R₁ R₂ : SetRel W W) (p : Set W) :
    IsGreatest {i | w ∈ stackAlternatives R₁ R₂ p i} (0, 0) ↔
      w ∈ R₁.dom ∩ R₁.core (R₂.dom ∩ R₂.core pᶜ) := by
  have key : w ∈ R₁.dom ∩ R₁.core (R₂.dom ∩ R₂.core pᶜ) ↔
      w ∉ R₁.core (R₂.core p) ∧ w ∈ R₁.core (excludedMiddle R₂ p) ∧
        w ∈ excludedMiddle R₁ (R₂.core p) := by
    rw [← compl_core_inter_excludedMiddle R₂ p, core_inter, ← Set.inter_assoc,
      ← compl_core_inter_excludedMiddle R₁ (R₂.core p)]
    exact ⟨fun ⟨⟨h₁, h₂⟩, h₃⟩ ↦ ⟨h₁, h₃, h₂⟩, fun ⟨h₁, h₃, h₂⟩ ↦ ⟨⟨h₁, h₂⟩, h₃⟩⟩
  rw [key]
  rw [isGreatest_iff_forall_not]
  simp only [Set.mem_ofPred_eq, stackAlternatives, Prod.forall, Fin.forall_fin_two, Prod.mk_le_mk,
    Matrix.cons_val_zero, Matrix.cons_val_one, Set.mem_compl_iff, not_not]
  exact ⟨fun ⟨hw, ⟨_, h01⟩, h10, _⟩ ↦ ⟨hw, h01 (by simp), h10 (by simp)⟩,
    fun ⟨hw, h₂, h₃⟩ ↦ ⟨hw, ⟨fun h ↦ by simp at h, fun _ ↦ h₂⟩,
      fun _ ↦ h₃, fun _ ↦ .inl h₂⟩⟩

/-! ### Strict NPIs (§6)

Each environment is a licenser whose enriched meaning is the exhaustified one. Negated *think* and
negated *be certain* share the operator of a negated universal and differ in the enrichment, by
`exhNot_eq` and `isGreatest_compl_core_preimage`. -/

/-- The environments in which the paper places a strict NPI. -/
inductive Environment
  /-- A context that the library names: sentential negation, (118) and (128), and the restrictor
  of a universal, (117a) and (119). -/
  | named (c : LicensingContext)
  /-- A negated neg-raising predicate, as in *doesn't think* and *doesn't believe*. -/
  | notThink
  /-- A negated universal without neg-raising, *isn't certain* (112b). -/
  | notCertain
  /-- A negative quantifier over a neg-raising predicate, (160). -/
  | noOneThinks
  deriving DecidableEq, Repr

open LicensingContext in
/-- The licenser of an environment, with its exhaustified meaning as the enrichment. -/
noncomputable def Environment.licenser : Environment → Licenser
  | .named c => c.licenser
  | .notThink => .scalar
      ⟨⟨Accessibility, fun p ↦ Set p.W, fun _ ↦ Prop, fun p P ↦ p.w ∉ p.R.core P⟩,
        fun p P ↦ p.w ∈ p.R.dom ∩ p.R.core Pᶜ⟩
  | .notCertain => .scalar
      ⟨⟨Accessibility, fun p ↦ Set p.W, fun _ ↦ Prop, fun p P ↦ p.w ∉ p.R.core P⟩,
        fun p P ↦ p.w ∉ p.R.core P ∧ p.w ∈ p.R.preimage P⟩
  | .noOneThinks => .scalar
      ⟨⟨Gajewski2007.People, fun p ↦ Set p.W, fun p ↦ Set p.W,
          fun p P ↦ {w | ∀ x ∈ p.O, w ∉ (p.B x).core P}⟩,
        fun p P ↦ Trivalent.posExt (Gajewski2007.noOneNR p.O p.B P)⟩

theorem carries_notThink : Environment.notThink.licenser.Carries .antiAdditive :=
  ⟨⟨fun _ _ _ hab hb ha ↦ hb (core_mono hab ha),
      fun h ↦ h ⟨Unit, .univ, ()⟩ (Set.empty_subset Set.univ)
        (fun hc ↦ hc (Set.mem_univ ((), ()))) fun _ _ ↦ trivial⟩,
    fun p ↦ ProjectivitySignature.holdsFor_antiAdd_iff.2
      ⟨fun P Q ↦ propext (Set.ext_iff.1 (dom_inter_core_compl_union p.R P Q) p.w),
        eq_false fun ⟨⟨_, hu⟩, h⟩ ↦ h hu trivial⟩⟩

theorem not_carries_notCertain : ¬ Environment.notCertain.licenser.Carries .antiAdditive :=
  fun h ↦ ((ProjectivitySignature.holdsFor_antiAdd_iff.1 (h.2 ⟨Bool, .univ, true⟩)).1.antitone
    (Set.empty_subset {true})
    ⟨fun hc ↦ absurd (hc (Set.mem_univ (true, false))) (by simp), true, rfl, trivial⟩).2.elim
      fun _ hb ↦ hb.1

theorem carries_noOneThinks : Environment.noOneThinks.licenser.Carries .antiAdditive :=
  ⟨⟨fun _ _ _ hab _ hb x hx ha ↦ hb x hx (core_mono hab ha), fun h ↦
      h ⟨Unit, Unit, .univ, fun _ ↦ .univ, ⟨(), trivial⟩⟩ (Set.empty_subset Set.univ)
        (show () ∈ {w | ∀ x ∈ Set.univ, w ∉ SetRel.core (.univ : SetRel Unit Unit) ∅} from
          fun _ _ hc ↦ hc (Set.mem_univ ((), ())))
        () trivial fun _ _ ↦ trivial⟩,
    fun p ↦ ProjectivitySignature.holdsFor_antiAdd_iff.2
      ⟨Gajewski2007.isAntiAdditive_posExt_noOneNR p.O p.B, by
        obtain ⟨x, hx⟩ := p.nonempty
        refine Set.eq_empty_of_forall_notMem fun w hw ↦ ?_
        have hw' : w ∈ Trivalent.posExt (Gajewski2007.noOneNR p.O p.B Set.univ) := hw
        rw [Gajewski2007.posExt_noOneNR] at hw'
        simpa using Set.mem_iInter₂.1 hw' x hx⟩⟩

instance (e : Environment) : Decidable (e.licenser.Carries .antiAdditive) :=
  match e with
  | .named c => inferInstanceAs (Decidable (c.licenser.Carries .antiAdditive))
  | .notThink => isTrue carries_notThink
  | .notCertain => isFalse not_carries_notCertain
  | .noOneThinks => isTrue carries_noOneThinks

/-! ### The paper's judgments -/

open Examples

/-- A link from an example to the lexical entry of its strict NPI and to the environment in which
the item stands. -/
structure Link where
  /-- The polarity item. -/
  item : PolarityItem
  /-- The environment of the item. -/
  environment : Environment

open English.PolarityItems in
/-- The links of the examples. The examples with a truth predicate, (129) and (131), and the one
with *in weeks*, (117b), are not linked. -/
def links : List (Datum × Link) :=
  [(ex_112a, ⟨until_, .notThink⟩), (ex_112b, ⟨until_, .notCertain⟩),
    (ex_115, ⟨until_, .notThink⟩), (ex_117a, ⟨until_, .named .universalRestrictor⟩),
    (ex_118, ⟨until_, .named .negation⟩), (ex_119, ⟨until_, .named .universalRestrictor⟩),
    (ex_128, ⟨until_, .named .negation⟩), (ex_130, ⟨until_, .notThink⟩),
    (ex_160, ⟨until_, .noOneThinks⟩)]

-- The words of each link's item occur in its example, so a link to the wrong item fails.
theorem links_attested :
    ∀ p ∈ links, ∀ w ∈ Datum.wordsOf p.2.item.form, w ∈ Datum.wordsOf p.1.primaryText := by
  decide +kernel

private theorem links_strict :
    ∀ p ∈ links, p.2.item.licensor = some .antiAdditive ∧ p.2.item.antiLicensor = none ∧
      ¬ p.2.item.IsFCI := by
  decide +kernel

private theorem admits_iff (l : Datum × Link) (hl : l ∈ links) :
    l.2.environment.licenser.Admits l.2.item ↔
      l.2.environment.licenser.Carries .antiAdditive :=
  have ⟨hs, ha, hf⟩ := links_strict l hl
  Licenser.admits_iff_carries hs (by decide) ha hf

private theorem links_carries :
    ∀ p ∈ links, (p.2.environment ≠ .named .universalRestrictor →
        (p.1.judgment = .acceptable ↔ p.2.environment.licenser.Carries .antiAdditive)) ∧
      (p.2.environment = .named .universalRestrictor →
        p.1.judgment = .ungrammatical ∧ p.2.environment.licenser.Carries .antiAdditive) := by
  decide +kernel

/-- The licensing theory admits the strict NPI of each example in its environment exactly when the
paper judges the example acceptable, the restrictor of a universal aside: negated *think* is
anti-additive once enriched, and negated *be certain* is no longer downward entailing
((112), (123)–(127)). -/
theorem judgments_predicted :
    ∀ p ∈ links, p.2.environment ≠ .named .universalRestrictor →
      (p.1.judgment = .acceptable ↔ p.2.environment.licenser.Admits p.2.item) :=
  fun p hp hr ↦ ((links_carries p hp).1 hr).trans (admits_iff p hp).symm

-- (117a), (119)
theorem restrictor_not_licensed :
    ∀ p ∈ links, p.2.environment = .named .universalRestrictor →
      p.1.judgment = .ungrammatical ∧ p.2.environment.licenser.Admits p.2.item :=
  fun p hp hr ↦ ⟨((links_carries p hp).2 hr).1, (admits_iff p hp).2 ((links_carries p hp).2 hr).2⟩

end Romoli2013b
