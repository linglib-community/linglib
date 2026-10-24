module

public import Mathlib.Data.Set.Functor
public import Mathlib.Data.Set.Lattice.Bounded
public import Linglib.Logic.Modal.Defs
public import Linglib.Fragments.Japanese.Determiners
public import Linglib.Fragments.German.PolarityItems
public import Studies.Haspelmath1997
public import Linglib.Data.Examples.KratzerShimoyama2002

/-!
# Kratzer and Shimoyama (2002): Indeterminate Pronouns: The View from Japanese

This file formalizes the paper's Hamblin semantics for indeterminate pronouns and its
application to German *irgendein*. Every expression denotes a set of alternatives; an
indeterminate pronoun denotes a set of individuals, composition is pointwise functional
application, and the alternatives expand until an operator, existential, universal, negative,
or interrogative, closes them. Since closure returns a single proposition, alternatives are
caught by the nearest operator, which is the paper's locality constraint on association.
Determiner quantification is the special case in which the alternatives are individuals.
*Irgendein* widens a domain-restricted indefinite to the whole extension of its noun, and
modals are sensitive to the propositional alternatives in their scope; their truth conditions
are weak, and the distribution requirement behind the free-choice effect, that every
alternative be realised at some accessible world, is not entailed by them but derived as a
conversational implicature from the reasons a speaker could have for widening, present
under *kann* and *muss* and cancelled under negated possibility. The paper closes with the
selectivity of Indo-European indeterminates, *irgendein* associating only with existential
closure, and the Beck effects, in which an intervening operator blocks the in situ wh-phrase.

The paper's sentences with *irgendein* are acceptable exactly in the environments the fragment
entry `German.PolarityItems.irgendein` lists (`rows_irgendein`). Under a negative operator
selectivity decides: *niemand* and *auf keinen Fall* close their scope with [∃] and admit the
item, while the inflectional negation *nicht* carries [Neg] and does not
(`rows_irgendein_selective`). Strength does not decide it, since the licensing table licenses the
item under the downward-entailing *nicht* (`negation_licenses_irgendein`). Haspelmath's map
agrees: the environments the entry lists realize functions of his *irgend-* series, and
inflectional negation realizes direct negation, which the series lacks (`irgendein_haspelmath`).

## Implementation notes

Hamblin functional application is mathlib's `Set.seq`, and singleton denotations are
`{f}`; the four sentential operators return singleton sets, as in the paper, so that closure
is idle on an already closed set. The existential and universal operators are what the
coordinators *ka* and *mo* denote on the set of alternatives (`opExists_eq_denote_ka`,
`opForall_eq_denote_mo`), and on individual alternatives they give the readings of the
indeterminate quantifiers in `Fragments/Japanese/Determiners.lean` (`denote_image_eq_reading`),
an identification of *ka* and *mo* with the coordinators that the fragment makes and the paper
does not. The modal semantics is stated for an accessibility relation
on any type of worlds, and the free-choice computations are the paper's three tables with
the derived implicature as a hypothesis. The Beck-effect paradigm and its scrambled
counterpart are example rows, keyed by the intervener's interpretable feature, and so is the
paradigm of *irgendein*, keyed by its licensing environment. Locators
follow the 2002 manuscript, whose numbering the published chapter keeps.

## References

* [kratzer-shimoyama-2002]
* [hamblin-1973b] — alternative semantics for questions
* [haspelmath-1997] — the Latvian and Japanese series
* [kadmon-landman-1993] — widening for a reason
* [beck-1996] — intervention effects
-/

@[expose] public section

namespace KratzerShimoyama2002

open ModalLogic
open SetRel

/-! ### Hamblin composition (§2, §3) -/

section Composition

variable {W E : Type*}

theorem seq_singleton (f : E → W → Prop) (A : Set E) : Set.seq {f} A = f '' A := by
  ext p; simp [Set.mem_seq_iff]

/-- `opExists A` is existential closure, the single proposition true where some alternative is. -/
def opExists (A : Set (W → Prop)) : Set (W → Prop) := {fun w ↦ ∃ p ∈ A, p w}

/-- `opForall A` is universal closure, the single proposition true where every alternative is. -/
def opForall (A : Set (W → Prop)) : Set (W → Prop) := {fun w ↦ ∀ p ∈ A, p w}

/-- `opNeg A` is negative closure, the single proposition true where no alternative is. -/
def opNeg (A : Set (W → Prop)) : Set (W → Prop) := {fun w ↦ ∀ p ∈ A, ¬ p w}

/-- The question operator returns the alternatives themselves. -/
def opQ (A : Set (W → Prop)) : Set (W → Prop) := A

theorem opNeg_eq (A : Set (W → Prop)) : opNeg A = {fun w ↦ ¬ ∃ p ∈ A, p w} := by
  simp [opNeg, not_exists]

theorem opExists_singleton (p : W → Prop) : opExists {p} = {p} := by simp [opExists]

theorem opForall_singleton (p : W → Prop) : opForall {p} = {p} := by simp [opForall]

/-- Alternatives are caught by the nearest operator (4), so a higher operator applied after closure
changes nothing. -/
theorem opForall_opExists (A : Set (W → Prop)) : opForall (opExists A) = opExists A :=
  opForall_singleton _

theorem opExists_opForall (A : Set (W → Prop)) : opExists (opForall A) = opForall A :=
  opExists_singleton _

/-- Existential closure over the propositions a predicate yields from a set of individuals is
ordinary existential quantification (§2). -/
theorem opExists_image (P : E → W → Prop) (A : Set E) :
    opExists (P '' A) = {fun w ↦ ∃ x ∈ A, P x w} := by
  simp [opExists]

theorem opForall_image (P : E → W → Prop) (A : Set E) :
    opForall (P '' A) = {fun w ↦ ∀ x ∈ A, P x w} := by
  simp [opForall]

theorem opExists_eq_denote_ka (A : Set (W → Prop)) :
    opExists A = {Japanese.Coordination.ka.denote A} := by
  rw [opExists, Coordinator.denote_of_disjunctive rfl]; congr 1; ext w; simp [sSup_apply]

theorem opForall_eq_denote_mo (A : Set (W → Prop)) :
    opForall A = {Japanese.Coordination.mo.denote A} := by
  rw [opForall, Coordinator.denote_of_conjunctive rfl]; congr 1; ext w; simp [sInf_apply]

theorem opNeg_eq_denote {c : Coordinator} (hc : c.role = .negative) (A : Set (W → Prop)) :
    opNeg A = {c.denote A} := by
  rw [opNeg, Coordinator.denote_of_negative hc]; congr 1; ext w; simp [sSup_apply]

/-- An indeterminate's particle applied to a predicate's propositions over a set of individuals
gives the indeterminate quantifier's reading (§2). -/
theorem denote_image_eq_reading [Fintype E] (q : IndeterminateQuantifier)
    (P : E → W → Prop) (A : Set E) :
    q.particle.denote (P '' A) = fun w ↦ q.reading E (· ∈ A) (P · w) := by
  funext w
  rw [Coordinator.denote_apply, Set.image_image]
  rfl

end Composition

/-! ### *Dare(-ga) nemutta* (§2) -/

section Derivation

variable {W E : Type*} (human slept : E → W → Prop)

/-- `dare human w` is *dare* 'who', the humans at the evaluation world. -/
def dare (w : W) : Set E := {x | human x w}

/-- `nemutta slept` is *nemutta* 'slept', a single alternative. -/
def nemutta : Set (E → W → Prop) := {slept}

theorem dare_nemutta (w : W) :
    Set.seq (nemutta slept) (dare human w) = {p | ∃ x, human x w ∧ p = slept x} := by
  rw [nemutta, seq_singleton]
  ext p; simp [dare, eq_comm]

theorem dare_ka (w : W) :
    opExists (Set.seq (nemutta slept) (dare human w)) = {fun w' ↦ ∃ x, human x w ∧ slept x w'} := by
  rw [nemutta, seq_singleton, opExists_image]; rfl

theorem dare_mo (w : W) :
    opForall (Set.seq (nemutta slept) (dare human w)) = {fun w' ↦ ∀ x, human x w → slept x w'} := by
  rw [nemutta, seq_singleton, opForall_image]; rfl

end Derivation

/-! ### Widening and modals (§7) -/

section Modals

variable {W E : Type*}

/-- `ein man D` is *ein Mann* with the contextual domain `D`, a subset of the men. -/
def ein (man : E → Prop) (D : Set E) : Set E := {x | man x ∧ x ∈ D}

/-- *irgend-* widens over every value of the domain variable. -/
def irgend (den : Set E → Set E) : Set E := ⋃ D, den D

theorem irgend_ein (man : E → Prop) : irgend (ein man) = {x | man x} := by
  ext x
  simp only [irgend, ein, Set.mem_iUnion, Set.mem_ofPred_eq]
  exact ⟨fun ⟨_, h, _⟩ ↦ h, fun h ↦ ⟨Set.univ, h, Set.mem_univ x⟩⟩

theorem subset_irgend (den : Set E → Set E) (D : Set E) : den D ⊆ irgend den :=
  Set.subset_iUnion den D

/-- `kann R A` is *kann* over the propositional alternatives `A`, the possibility that some
alternative holds. -/
def kann (R : SetRel W W) (A : Set (W → Prop)) : Set (W → Prop) :=
  {◇[R] fun w ↦ ∃ p ∈ A, p w}

/-- `muss R A` is *muss* over the propositional alternatives `A`, the necessity that some
alternative holds. -/
def muss (R : SetRel W W) (A : Set (W → Prop)) : Set (W → Prop) :=
  {□[R] fun w ↦ ∃ p ∈ A, p w}

/-- `distribution R A w` is the distribution requirement, that every alternative is possible. -/
def distribution (R : SetRel W W) (A : Set (W → Prop)) (w : W) : Prop :=
  ∀ p ∈ A, ◇[R] p w

theorem kann_singleton (R : SetRel W W) (p : W → Prop) : kann R {p} = {◇[R] p} := by
  simp [kann]

theorem muss_singleton (R : SetRel W W) (p : W → Prop) : muss R {p} = {□[R] p} := by
  simp [muss]

/-- *muss* does not entail the distribution requirement (§6). -/
theorem not_distribution_of_muss :
    ∃ (R : SetRel Bool Bool) (A : Set (Bool → Prop)) (w : Bool),
      (∀ q ∈ muss R A, q w) ∧ ¬ distribution R A w :=
  ⟨.id, {fun w ↦ w = true, fun w ↦ w = false}, true,
    fun q hq ↦ by
      rw [muss, Set.mem_singleton_iff] at hq
      subst hq
      exact fun w' hw' ↦ ⟨_, Set.mem_insert _ _, (SetRel.mem_id.1 hw').symm⟩,
    fun h ↦ by
      obtain ⟨w', hw', hp⟩ := h _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))
      rw [SetRel.mem_id] at hw'
      subst hw'
      exact Bool.noConfusion hp⟩

end Modals

/-! ### The free-choice implicature (§8)

Widening is for a reason: strengthening, avoiding a false claim, or avoiding a false
exhaustivity inference. For (16), had the speaker chosen the narrower set with one
alternative, the exhaustivity inference would have excluded the other; the only reason to
widen is that this inference is false, so each alternative's possibility implies the other's.
The same reasoning yields the implicature of (17); under the negated possibility of (18)
every such reason is already entailed by what was said, and the implicature is cancelled. -/

section FreeChoice

variable {W : Type*} (R : SetRel W W) (A B : W → Prop) (w : W)

theorem kann_pair : (∀ q ∈ kann R {A, B}, q w) ↔ ◇[R] (fun w ↦ A w ∨ B w) w := by
  simp [kann, Diamond, exists_or, and_or_left]

theorem muss_pair : (∀ q ∈ muss R {A, B}, q w) ↔ □[R] (fun w ↦ A w ∨ B w) w := by
  simp [muss, Box]

/-- In (16) the truth-conditional content with the implicature yields free choice. -/
theorem total_kann (hT : ◇[R] (fun w ↦ A w ∨ B w) w) (hI : ◇[R] A w ↔ ◇[R] B w) :
    ◇[R] A w ∧ ◇[R] B w := by
  obtain ⟨w', hw', h⟩ := hT
  rcases h with h | h
  · exact ⟨⟨w', hw', h⟩, hI.mp ⟨w', hw', h⟩⟩
  · exact ⟨hI.mpr ⟨w', hw', h⟩, ⟨w', hw', h⟩⟩

/-- In (17) the total meaning implies both possibilities once some world is accessible. -/
theorem total_muss (hT : □[R] (fun w ↦ A w ∨ B w) w) (hI : □[R] A w ↔ □[R] B w)
    (hser : ∃ w', w ~[R] w') : ◇[R] A w ∧ ◇[R] B w := by
  obtain ⟨w₀, hw₀⟩ := hser
  by_cases hA : □[R] A w
  · exact ⟨⟨w₀, hw₀, hA w₀ hw₀⟩, ⟨w₀, hw₀, hI.mp hA w₀ hw₀⟩⟩
  · have hB : ¬ □[R] B w := fun h ↦ hA (hI.mpr h)
    simp only [Box, not_forall] at hA hB
    obtain ⟨wa, hwa, ha⟩ := hA
    obtain ⟨wb, hwb, hb⟩ := hB
    exact ⟨⟨wb, hwb, (hT wb hwb).resolve_right hb⟩, ⟨wa, hwa, (hT wa hwa).resolve_left ha⟩⟩

/-- In (18), under negated possibility, every reason for widening is already entailed, so no
strengthening is available. -/
theorem total_neg_kann (hT : ¬ ◇[R] (fun w ↦ A w ∨ B w) w) : ¬ ◇[R] A w ∧ ¬ ◇[R] B w :=
  ⟨fun ⟨w', hw', h⟩ ↦ hT ⟨w', hw', Or.inl h⟩, fun ⟨w', hw', h⟩ ↦ hT ⟨w', hw', Or.inr h⟩⟩

end FreeChoice

/-! ### Selectivity and intervention (§9) -/

open scoped Denotes in
/-- Japanese indeterminates do not change shape (§9). *Dare-ka* and *dare-mo* share their
indeterminate and differ in their readings, which their particles' coordinations supply. -/
theorem japanese_same_base.{u} :
    Japanese.Determiners.dare_ka.indeterminate = Japanese.Determiners.dare_mo.indeterminate ∧
      (⟦Japanese.Determiners.dare_ka⟧ : Set Quantifier.GQ.Family.{u}) ≠
        ⟦Japanese.Determiners.dare_mo⟧ := by
  refine ⟨rfl, ?_⟩
  rw [Japanese.Determiners.denote_dare_ka, Japanese.Determiners.denote_dare_mo]
  exact fun h ↦ Quantifier.GQ.Family.some_ne_every (Set.singleton_eq_singleton_iff.1 h)

/-- The Latvian series serve pairwise disjoint functions on [haspelmath-1997]'s map, so they are
selective (§1, §9). -/
theorem latvian_selective :
    Haspelmath1997.latvian.Pairwise (Disjoint ·.functions ·.functions) := by
  decide

theorem japanese_series_disjoint :
    Haspelmath1997.japanese.Pairwise (Disjoint ·.functions ·.functions) := by
  decide

/-- In (23) and (24), a multiple question with an in-situ wh-phrase is ungrammatical iff an operator
with an interpretable feature intervenes. -/
theorem rows_beck :
    ∀ r ∈ Examples.all, (r.feature? "order").isSome →
      (r.judgment = .ungrammatical ↔
        r.feature? "order" = some "intervener-first" ∧ r.feature? "feature" ≠ some "none") := by
  decide +kernel

/-! ### The distribution of *irgendein* (§6, §9) -/

open PolarityItem

/-- `contextOf? r` is the licensing environment a row of the *irgendein* paradigm names. -/
def contextOf? (r : Datum) : Option LicensingContext :=
  r.parse? "context"
    [("question", .question), ("doubtVerb", .doubtVerb), ("modalPossibility", .modalPossibility),
      ("modalNecessity", .modalNecessity), ("nobody", .nobody), ("negation", .negation)]

/-- A sentence with *irgendein* is acceptable exactly in the environments the fragment entry
lists, (12), (13), (16)–(18), (21) and (22). -/
theorem rows_irgendein :
    ∀ r ∈ Examples.all, ∀ c ∈ contextOf? r,
      (r.judgment = .acceptable ↔ c ∈ German.PolarityItems.irgendein.licensingContexts) := by
  decide

/-- Under a negative operator, *irgendein* is acceptable exactly when that operator closes its scope
with [∃] ((12), (18), (21)). -/
theorem rows_irgendein_selective :
    ∀ r ∈ Examples.all, (contextOf? r).isSome → ∀ f ∈ r.feature? "feature",
      (r.judgment = .acceptable ↔ f = "exists") := by
  decide

/-- The licensing theory licenses *irgendein* under inflectional negation, yet (21) is
ungrammatical, so selectivity rather than strength excludes it. -/
theorem negation_licenses_irgendein :
    LicensingContext.negation.licenser.Licenses German.PolarityItems.irgendein ∧
      Examples.ex21.judgment = .ungrammatical :=
  ⟨by simp [German.PolarityItems.irgendein, PolarityItem.IsNPI], rfl⟩

theorem irgendein_haspelmath :
    ∀ s ∈ Haspelmath1997.german, s.toSeries = German.Indefinites.irgendSeries →
      (∀ c ∈ German.PolarityItems.irgendein.licensingContexts, ∀ f ∈ c.haspelmath,
        f ∈ s.functions) ∧
        ∀ f ∈ LicensingContext.negation.haspelmath, f ∉ s.functions := by
  decide

end KratzerShimoyama2002
