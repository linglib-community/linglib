module

public import Mathlib.Logic.Equiv.Basic
public import Linglib.Logic.Trivalent.UniversalInference
public import Linglib.Semantics.Presupposition.QuantifiedLocalContext
public import Linglib.Semantics.Reference.ChoiceFunction

/-!
# Chatain (2025): Reducing pronoun accessibility to presupposition satisfaction

A discourse pronoun denotes the pick of a choice function from a witness set and is undefined
where the set is empty (`pro`), and an indexed indefinite asserts that its witness set is
nonempty (`antecedent`), so a pronoun is accessible where an existence presupposition is
satisfied. Under Middle Kleene connectives and universally projecting determiners the
presupposition is filtered after the antecedent, in a bathroom disjunction and in a donkey
sentence, and projects when the pronoun comes first. Quantifying over the choice function gives
the universal and existential readings, and restricting the witness set to the local context of
its indefinite gives the subordination constraint.

## Implementation notes

A point of evaluation `S` is a world, or a world with an assignment once binders are present, and
a binder is the family `b : α → S` of points at which its variable takes each value. The
constraint on indexing fixes the witness set of an indefinite's index, so the definitions take a
witness set and a choice function rather than an index (`forall_isExpressive_iff`). The paper's
examples are the rows of `Data.Examples.Chatain2025`.

## TODO

* The constraint on choice-function variation, which bars a choice function from varying with a
  binder that its witness set is constant in, and the expressivity constraint weakened to match
  are not formalized: `IsExpressive` and the two readings quantify over unrestricted families.

## References

* [chatain-2025]
* [schlenker-2009]
-/

@[expose] public section

namespace Chatain2025

open Trivalent Quantifier Presupposition Bilattice

variable {ι α S E : Type*}

/-! ### Pronouns and their antecedents -/

/-- The discourse pronoun on the witness set `G` and the choice function `f`: at each point of
evaluation the pick of `f` from `G`, undefined where `G` is empty. -/
def pro (G : S → Set E) (f : S → ChoiceFunction E) (s : S) : Part E :=
  ⟨(G s).Nonempty, fun _ ↦ f s (G s)⟩

/-- The clause that predicates `VP` of the pronoun, undefined where the pronoun is. -/
noncomputable def clause (G : S → Set E) (f : S → ChoiceFunction E) (VP : S → E → Prop) (s : S) :
    Trivalent :=
  ofPart ((pro G f s).map (VP s))

open Classical in
/-- The indefinite sentence with witness set `G`. The constraint on indexing gives an indefinite
an index whose witness set is the intersection of its restrictor and its scope, so the sentence
asserts that the witness set is nonempty. -/
noncomputable def antecedent (G : S → Set E) (s : S) : Trivalent :=
  ofProp (G s).Nonempty

variable {G : S → Set E} {f : S → ChoiceFunction E} {VP : S → E → Prop} {s : S}

@[simp]
theorem clause_eq_undefined_iff : clause G f VP s = .undefined ↔ ¬ (G s).Nonempty :=
  ofPart_eq_undefined_iff

@[simp]
theorem clause_eq_true_iff :
    clause G f VP s = .true ↔ (G s).Nonempty ∧ VP s (f s (G s)) := by
  simp only [clause, ofPart_eq_true_iff, Part.mem_map_iff, pro, Part.mem_mk_iff]
  exact ⟨fun ⟨_, ⟨_, ⟨h, rfl⟩, rfl⟩, ha⟩ ↦ ⟨h, ha⟩, fun ⟨h, ha⟩ ↦ ⟨_, ⟨_, ⟨h, rfl⟩, rfl⟩, ha⟩⟩

@[simp]
theorem clause_eq_false_iff :
    clause G f VP s = .false ↔ (G s).Nonempty ∧ ¬ VP s (f s (G s)) := by
  simp only [clause, ofPart_eq_false_iff, Part.mem_map_iff, pro, Part.mem_mk_iff]
  exact ⟨fun ⟨_, ⟨_, ⟨h, rfl⟩, rfl⟩, ha⟩ ↦ ⟨h, ha⟩, fun ⟨h, ha⟩ ↦ ⟨_, ⟨_, ⟨h, rfl⟩, rfl⟩, ha⟩⟩

@[simp]
theorem antecedent_eq_true_iff : antecedent G s = .true ↔ (G s).Nonempty := by
  simp [antecedent]

@[simp]
theorem antecedent_eq_false_iff : antecedent G s = .false ↔ ¬ (G s).Nonempty := by
  simp [antecedent]

@[simp]
theorem antecedent_ne_undefined : antecedent G s ≠ .undefined := by
  simp [antecedent]

/-! ### Filtering by the connectives

The pronoun's presupposition is filtered after its antecedent (*there is a phone-book and it is in
the cabinet*) and by a `but` that filters in both directions; it projects when the pronoun comes
first, where the antecedent is then redundant; and after a negated antecedent the conjunction is
defined only where it is false. -/

theorem meetMiddle_antecedent_clause_ne_undefined :
    meetMiddle (antecedent G s) (clause G f VP s) ≠ .undefined := by
  simp

theorem meetMiddle_antecedent_clause_eq_true_iff :
    meetMiddle (antecedent G s) (clause G f VP s) = .true ↔
      (G s).Nonempty ∧ VP s (f s (G s)) := by
  simp

theorem meetMiddle_compl_antecedent_clause_eq_undefined_iff :
    meetMiddle (antecedent G s)ᶜ (clause G f VP s) = .undefined ↔ ¬ (G s).Nonempty := by
  simp

theorem meetMiddle_compl_antecedent_clause_ne_true :
    meetMiddle (antecedent G s)ᶜ (clause G f VP s) ≠ .true := by
  simp only [ne_eq, meetMiddle_eq_true_iff, compl_eq_true_iff, antecedent_eq_false_iff,
    clause_eq_true_iff]
  tauto

/-- *Either there isn't a phone-book or it is in the cabinet*: the negation of the first disjunct
filters the pronoun's presupposition. -/
theorem joinMiddle_compl_antecedent_clause_ne_undefined :
    joinMiddle (antecedent G s)ᶜ (clause G f VP s) ≠ .undefined := by
  simp

theorem joinMiddle_compl_antecedent_clause_eq_true_iff :
    joinMiddle (antecedent G s)ᶜ (clause G f VP s) = .true ↔
      ¬ (G s).Nonempty ∨ VP s (f s (G s)) := by
  simp only [joinMiddle_eq_true_iff, compl_eq_true_iff, compl_eq_false_iff,
    antecedent_eq_false_iff, antecedent_eq_true_iff, clause_eq_true_iff]
  tauto

theorem meetMiddle_clause_antecedent_eq_undefined_iff :
    meetMiddle (clause G f VP s) (antecedent G s) = .undefined ↔ ¬ (G s).Nonempty := by
  simp

theorem antecedent_eq_true_of_meetMiddle_clause_ne_undefined
    (h : meetMiddle (clause G f VP s) (antecedent G s) ≠ .undefined) :
    antecedent G s = .true := by
  simpa using h

theorem clause_inf_antecedent_ne_undefined : clause G f VP s ⊓ antecedent G s ≠ .undefined := by
  simp

/-! ### Pronouns under quantifiers

Determiners are read by universal projection (`Quantifier.Det.universalProjection`): undefined
unless the scope is defined wherever the restrictor is true. -/

variable {Q : Det α} {p q : α → Trivalent} {b : α → S}

theorem universalProjection_clause_eq_undefined_iff :
    Det.universalProjection Q p (fun y ↦ clause G f VP (b y)) = .undefined ↔
      ¬ ∀ y, p y = .true → (G (b y)).Nonempty := by
  simp

/-- *Every tourist who bought a ticket has already used it*: the indefinite in the restrictor
filters the presupposition of the pronoun in the scope, whatever the determiner. -/
theorem universalProjection_antecedent_clause_ne_undefined :
    Det.universalProjection Q (fun y ↦ p y ⊓ antecedent G (b y)) (fun y ↦ clause G f VP (b y)) ≠
      .undefined := by
  classical
  simp

theorem universalProjection_every_antecedent_clause_eq_true_iff :
    Det.universalProjection Det.every (fun y ↦ p y ⊓ antecedent G (b y))
        (fun y ↦ clause G f VP (b y)) = .true ↔
      ∀ y, p y = .true → (G (b y)).Nonempty → VP (b y) (f (b y) (G (b y))) := by
  classical
  simp only [Det.universalProjection_eq_true_iff, inf_eq_true_iff, antecedent_eq_true_iff,
    ne_eq, clause_eq_undefined_iff, not_not, and_imp, Det.every, Set.subset_def, mem_posExt,
    clause_eq_true_iff]
  exact ⟨fun h y hy hG ↦ (h.2 y hy hG).2, fun h ↦ ⟨fun _ _ hG ↦ hG, fun y hy hG ↦ ⟨hG, h y hy hG⟩⟩⟩

/-- The universal rule is below deployment: for a determiner that lives on its restrictor,
universal projection has the deployed value wherever it is defined, so a presupposition
satisfied under the universal rule is satisfied under deployment. -/
theorem universalProjection_kLE_deployQuantifier (hQ : (Q (posExt p)).LivesOn (posExt p)) :
    Q.universalProjection p q ≤ₖ deployQuantifier (Q (posExt p)) q :=
  Quantifier.universalProjection_kLE_deployQuantifier hQ

theorem deployQuantifier_clause_ne_undefined {Q : Quantifier α}
    (hQ : Q.LivesOn {y | (G (b y)).Nonempty}) :
    deployQuantifier Q (fun y ↦ clause G f VP (b y)) ≠ .undefined := by
  classical
  rw [deployQuantifier_of_livesOn hQ fun y hy ↦ by simpa using hy]
  exact ofProp_ne_undefined

/-! ### Existential and universal readings

Quantifying universally over the choice function gives the universal reading of a conjunction and
of a donkey sentence, and quantifying existentially the existential one. -/

theorem forall_meetMiddle_eq_true_iff [Nonempty E] :
    (∀ f : S → ChoiceFunction E, meetMiddle (antecedent G s) (clause G f VP s) = .true) ↔
      (G s).Nonempty ∧ ∀ x ∈ G s, VP s x := by
  simp only [meetMiddle_antecedent_clause_eq_true_iff]
  refine ⟨fun h ↦ ⟨(h fun _ ↦ .epsilon).1, fun x hx ↦ ?_⟩, fun h f ↦
    ⟨h.1, h.2 _ ((f s).apply_mem h.1)⟩⟩
  obtain ⟨g, hg⟩ := ChoiceFunction.exists_apply_eq (A := G s) hx
  exact hg ▸ (h fun _ ↦ g).2

theorem exists_meetMiddle_eq_true_iff :
    (∃ f : S → ChoiceFunction E, meetMiddle (antecedent G s) (clause G f VP s) = .true) ↔
      ∃ x ∈ G s, VP s x := by
  simp only [meetMiddle_antecedent_clause_eq_true_iff]
  refine ⟨fun ⟨f, h⟩ ↦ ⟨_, (f s).apply_mem h.1, h.2⟩, fun ⟨x, hx, hVP⟩ ↦ ?_⟩
  obtain ⟨g, hg⟩ := ChoiceFunction.exists_apply_eq (A := G s) hx
  exact ⟨fun _ ↦ g, ⟨x, hx⟩, hg ▸ hVP⟩

theorem forall_donkey_eq_true_iff [Nonempty E] :
    (∀ f : S → ChoiceFunction E, Det.universalProjection Det.every
        (fun y ↦ p y ⊓ antecedent G (b y)) (fun y ↦ clause G f VP (b y)) = .true) ↔
      ∀ y, p y = .true → ∀ x ∈ G (b y), VP (b y) x := by
  simp only [universalProjection_every_antecedent_clause_eq_true_iff]
  refine ⟨fun h y hy x hx ↦ ?_, fun h f y hy hG ↦ h y hy _ ((f (b y)).apply_mem hG)⟩
  obtain ⟨g, hg⟩ := ChoiceFunction.exists_apply_eq (A := G (b y)) hx
  exact hg ▸ h (fun _ ↦ g) y hy ⟨x, hx⟩

/-- Existential quantification over the choice function gives the existential reading of a
donkey sentence. The choice function varies with the point of evaluation, so each value of the
bound variable gets its own pick. -/
theorem exists_donkey_eq_true_iff [Nonempty E] :
    (∃ f : S → ChoiceFunction E, Det.universalProjection Det.every
        (fun y ↦ p y ⊓ antecedent G (b y)) (fun y ↦ clause G f VP (b y)) = .true) ↔
      ∀ y, p y = .true → (G (b y)).Nonempty → ∃ x ∈ G (b y), VP (b y) x := by
  simp only [universalProjection_every_antecedent_clause_eq_true_iff]
  refine ⟨fun ⟨f, h⟩ y hy hG ↦ ⟨_, (f (b y)).apply_mem hG, h y hy hG⟩, fun h ↦ ?_⟩
  obtain ⟨F, hF⟩ := Classical.skolem.1 fun s ↦
    show ∃ g : ChoiceFunction E, (∃ x ∈ G s, VP s x) → VP s (g (G s)) from
      (em (∃ x ∈ G s, VP s x)).elim
        (fun hs ↦ ((ChoiceFunction.exists_apply_iff_of_nonempty (hs.imp fun _ h ↦ h.1)
          (VP s)).2 hs).imp fun _ h _ ↦ h)
        fun hs ↦ ⟨.epsilon, fun h ↦ (hs h).elim⟩
  exact ⟨F, fun y hy hG ↦ hF (b y) (h y hy hG)⟩

/-! ### Indices -/

/-- The expressivity constraint: every witness set and choice function is named by an index. -/
def IsExpressive (G : ι → S → Set E) (f : ι → S → ChoiceFunction E) : Prop :=
  Function.Surjective fun i ↦ (G i, f i)

/-- The pairs of a witness set and a choice function index themselves expressively. -/
example : IsExpressive (ι := (S → Set E) × (S → ChoiceFunction E)) Prod.fst Prod.snd :=
  fun x ↦ ⟨x, rfl⟩

theorem forall_isExpressive_iff
    (h : ∃ (G : ι → S → Set E) (f : ι → S → ChoiceFunction E), IsExpressive G f) (i : ι)
    (W : S → Set E) (φ : (S → ChoiceFunction E) → Prop) :
    (∀ (G : ι → S → Set E) (f : ι → S → ChoiceFunction E),
      IsExpressive G f → G i = W → φ (f i)) ↔ ∀ γ, φ γ := by
  classical
  refine ⟨fun hφ γ ↦ ?_, fun hφ _ f _ _ ↦ hφ (f i)⟩
  obtain ⟨G, f, hGf⟩ := h
  obtain ⟨j, hj⟩ := hGf (W, γ)
  obtain ⟨hG, hf⟩ : G j = W ∧ f j = γ := Prod.mk.inj hj
  have hi : Equiv.swap i j i = j := Equiv.swap_apply_left i j
  simpa [hi, hf] using
    hφ (G ∘ Equiv.swap i j) (f ∘ Equiv.swap i j) (hGf.comp (Equiv.swap i j).surjective)
      (by simp [hi, hG])

/-! ### The subordination constraint

With the witness set restricted to the local context of its indefinite, a pronoun under a second
quantifier presupposes that the second restrictor lies within the first (*every tourist bought a
ticket. # Most locals have already used it*). -/

/-- The witness set of an indefinite in the local context `R`: empty at the points outside
it. -/
def restrict (R : Set S) (G : S → Set E) (s : S) : Set E :=
  {x | s ∈ R ∧ x ∈ G s}

@[simp]
theorem restrict_nonempty_iff {R : Set S} : (restrict R G s).Nonempty ↔ s ∈ R ∧ (G s).Nonempty := by
  simp [restrict, Set.Nonempty]

theorem universalProjection_clause_restrict_eq_undefined_iff {R : Set S} :
    Det.universalProjection Q p (fun y ↦ clause (restrict R G) f VP (b y)) = .undefined ↔
      ¬ ∀ y, p y = .true → b y ∈ R ∧ (G (b y)).Nonempty := by
  simp

/-- *Every tourist bought a ticket. # Most locals have already used it*: when the witness set is
restricted to the local context that the first quantifier gives its scope, the pronoun under a
second quantifier is defined only where the second restrictor lies within the first. -/
theorem subordination_constraint {W : Type*} [Finite E]
    {q : NumberTree} {A : W → Set E} {C : Set W} {R : Set (W × E)}
    (hR : IsLocalContext C {scopeTruth q A} R) {G : W × E → Set E}
    {f : W × E → ChoiceFunction E} {VP : W × E → E → Prop} {Q : Det E} {p : E → Trivalent} {w : W}
    (h : Det.universalProjection Q p (fun y ↦ clause (restrict R G) f VP (w, y)) ≠ .undefined)
    {y : E} (hy : p y = .true) : y ∈ A w := by
  rw [ne_eq, universalProjection_clause_restrict_eq_undefined_iff, not_not] at h
  have hw := (h y hy).1
  rw [hR.unique (isLocalContext_scopeTruth q A C)] at hw
  exact hw.2.1

end Chatain2025
