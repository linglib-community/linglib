module

public import Mathlib.Logic.Equiv.Basic
public import Linglib.Logic.Trivalent.Deployment
public import Linglib.Semantics.Presupposition.QuantifiedLocalContext
public import Linglib.Semantics.Reference.ChoiceFunction

/-!
# Chatain (2025): Reducing pronoun accessibility to presupposition satisfaction

A discourse pronoun denotes the pick of a choice function from a witness set and is undefined
where the set is empty (`pro`), and an indexed indefinite asserts that its witness set is
nonempty (`antecedent`), so a pronoun is accessible where an existence presupposition is
satisfied. Under Middle Kleene connectives and determiners with a filtering restrictor the
presupposition is filtered after the antecedent, in a bathroom disjunction and in a donkey
sentence, and projects when the pronoun comes first. Quantifying over the choice function gives
the universal and existential readings, and restricting the witness set to the local context of
its indefinite gives the subordination constraint.

## Implementation notes

A point of evaluation `S` is a world, or a world with an assignment once binders are present, and
a binder is the family `b : α → S` of points at which its variable takes each value. The
constraint on indexing fixes the witness set of an indefinite's index, so the definitions take a
witness set and a choice function rather than an index (`forall_expressive_iff`). The paper's
examples are the rows of `Data.Examples.Chatain2025`.

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
  ⟨(G s).Nonempty, fun _ ↦ f s (· ∈ G s)⟩

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
    clause G f VP s = .true ↔ (G s).Nonempty ∧ VP s (f s (· ∈ G s)) := by
  simp only [clause, ofPart_eq_true_iff, Part.mem_map_iff, pro, Part.mem_mk_iff]
  exact ⟨fun ⟨_, ⟨_, ⟨h, rfl⟩, rfl⟩, ha⟩ ↦ ⟨h, ha⟩, fun ⟨h, ha⟩ ↦ ⟨_, ⟨_, ⟨h, rfl⟩, rfl⟩, ha⟩⟩

@[simp]
theorem clause_eq_false_iff :
    clause G f VP s = .false ↔ (G s).Nonempty ∧ ¬ VP s (f s (· ∈ G s)) := by
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

/-! ### Filtering by the connectives -/

/-- *There is a phone-book and it is in the cabinet*: the first conjunct filters the pronoun's
presupposition. -/
theorem meetMiddle_antecedent_clause_ne_undefined :
    meetMiddle (antecedent G s) (clause G f VP s) ≠ .undefined := by
  simp

theorem meetMiddle_antecedent_clause_eq_true_iff :
    meetMiddle (antecedent G s) (clause G f VP s) = .true ↔
      (G s).Nonempty ∧ VP s (f s (· ∈ G s)) := by
  simp

/-- *There isn't a phone-book and it is in the cabinet* is defined only where there is a
phone-book. -/
theorem meetMiddle_compl_antecedent_clause_eq_undefined_iff :
    meetMiddle (antecedent G s)ᶜ (clause G f VP s) = .undefined ↔ ¬ (G s).Nonempty := by
  simp

/-- *There isn't a phone-book and it is in the cabinet* is true nowhere. -/
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
      ¬ (G s).Nonempty ∨ VP s (f s (· ∈ G s)) := by
  simp only [joinMiddle_eq_true_iff, compl_eq_true_iff, compl_eq_false_iff,
    antecedent_eq_false_iff, antecedent_eq_true_iff, clause_eq_true_iff]
  tauto

/-- *It is in the cabinet and there is a phone-book*: the presupposition of a first conjunct
projects. -/
theorem meetMiddle_clause_antecedent_eq_undefined_iff :
    meetMiddle (clause G f VP s) (antecedent G s) = .undefined ↔ ¬ (G s).Nonempty := by
  simp

/-- Where *it is in the cabinet and there is a phone-book* is defined its second conjunct is
true, so in a context that satisfies the presupposition the second conjunct is redundant. -/
theorem antecedent_eq_true_of_meetMiddle_clause_ne_undefined
    (h : meetMiddle (clause G f VP s) (antecedent G s) ≠ .undefined) :
    antecedent G s = .true := by
  simpa using h

/-- *It's not available at the library now but there is a phone-book*: a conjunction that
filters in both directions lets the antecedent follow the pronoun. -/
theorem clause_inf_antecedent_ne_undefined : clause G f VP s ⊓ antecedent G s ≠ .undefined := by
  simp

/-! ### Pronouns under quantifiers -/

open Classical in
/-- A determiner whose restrictor filters the presuppositions of its scope: undefined unless the
scope is defined wherever the restrictor is true, and otherwise the value of the two-valued
determiner on the positive extensions. -/
noncomputable def filtering (Q : Det α) (p q : α → Trivalent) : Trivalent :=
  transplication (ofProp (∀ x, p x = .true → q x ≠ .undefined)) (ofProp (Q (posExt p) (posExt q)))

variable {Q : Det α} {p q : α → Trivalent} {b : α → S}

@[simp]
theorem filtering_eq_undefined_iff :
    filtering Q p q = .undefined ↔ ¬ ∀ x, p x = .true → q x ≠ .undefined := by
  simp [filtering]

@[simp]
theorem filtering_eq_true_iff :
    filtering Q p q = .true ↔
      (∀ x, p x = .true → q x ≠ .undefined) ∧ Q (posExt p) (posExt q) := by
  simp [filtering]

/-- *Every tourist bought a ticket. Most have already used it*: under a quantifier binding the
witness set, the pronoun presupposes that the witness set of every individual in the restrictor
is nonempty. -/
theorem filtering_clause_eq_undefined_iff :
    filtering Q p (fun y ↦ clause G f VP (b y)) = .undefined ↔
      ¬ ∀ y, p y = .true → (G (b y)).Nonempty := by
  simp

/-- *Every tourist who bought a ticket has already used it*: the indefinite in the restrictor
filters the presupposition of the pronoun in the scope, whatever the determiner. -/
theorem filtering_antecedent_clause_ne_undefined :
    filtering Q (fun y ↦ p y ⊓ antecedent G (b y)) (fun y ↦ clause G f VP (b y)) ≠
      .undefined := by
  classical
  simp

/-- A donkey sentence with *every* is true when every individual in the restrictor with a
nonempty witness set stands in the relation to the pick from it. -/
theorem filtering_every_antecedent_clause_eq_true_iff :
    filtering Det.every (fun y ↦ p y ⊓ antecedent G (b y))
        (fun y ↦ clause G f VP (b y)) = .true ↔
      ∀ y, p y = .true → (G (b y)).Nonempty → VP (b y) (f (b y) (· ∈ G (b y))) := by
  classical
  simp only [filtering_eq_true_iff, inf_eq_true_iff, antecedent_eq_true_iff,
    ne_eq, clause_eq_undefined_iff, not_not, and_imp, Det.every, Set.subset_def, mem_posExt,
    clause_eq_true_iff]
  exact ⟨fun h y hy hG ↦ (h.2 y hy hG).2, fun h ↦ ⟨fun _ _ hG ↦ hG, fun y hy hG ↦ ⟨hG, h y hy hG⟩⟩⟩

/-- The universal rule is below deployment: for a determiner that lives on its restrictor,
where `filtering` is defined it has the deployed value, so a presupposition satisfied under the
universal rule is satisfied under deployment. -/
theorem filtering_kLE_deployQuantifier (hQ : (Q (posExt p)).LivesOn (posExt p)) :
    filtering Q p q ≤ₖ deployQuantifier (Q (posExt p)) q := by
  classical
  rw [kLE_iff]
  by_cases hd : ∀ x, p x = .true → q x ≠ .undefined
  · refine .inr ?_
    rw [deployQuantifier_of_livesOn hQ fun u hu ↦ hd u hu, filtering, ofProp_eq_true_iff.2 hd,
      transplication_true_left]
  · exact .inl (filtering_eq_undefined_iff.2 hd)

/-- Under deployment a quantifier that lives on the individuals with a nonempty witness set
filters the pronoun's presupposition, with no projection rule assumed. -/
theorem deployQuantifier_clause_ne_undefined {Q : Quantifier α}
    (hQ : Q.LivesOn {y | (G (b y)).Nonempty}) :
    deployQuantifier Q (fun y ↦ clause G f VP (b y)) ≠ .undefined := by
  classical
  rw [deployQuantifier_of_livesOn hQ fun y hy ↦ by simpa using hy]
  exact ofProp_ne_undefined

/-! ### Existential and universal readings -/

/-- Universal quantification over the choice function gives the universal reading of a
conjunction. -/
theorem forall_meetMiddle_eq_true_iff [Nonempty E] :
    (∀ f : S → ChoiceFunction E, meetMiddle (antecedent G s) (clause G f VP s) = .true) ↔
      (G s).Nonempty ∧ ∀ x ∈ G s, VP s x := by
  simp only [meetMiddle_antecedent_clause_eq_true_iff]
  refine ⟨fun h ↦ ⟨(h fun _ ↦ .epsilon).1, fun x hx ↦ ?_⟩, fun h f ↦
    ⟨h.1, h.2 _ ((f s).apply_of_exists h.1)⟩⟩
  obtain ⟨g, hg⟩ := ChoiceFunction.exists_apply_eq (N := (· ∈ G s)) hx
  exact hg ▸ (h fun _ ↦ g).2

/-- Existential quantification over the choice function gives the existential reading of a
conjunction. -/
theorem exists_meetMiddle_eq_true_iff :
    (∃ f : S → ChoiceFunction E, meetMiddle (antecedent G s) (clause G f VP s) = .true) ↔
      ∃ x ∈ G s, VP s x := by
  simp only [meetMiddle_antecedent_clause_eq_true_iff]
  refine ⟨fun ⟨f, h⟩ ↦ ⟨_, (f s).apply_of_exists h.1, h.2⟩, fun ⟨x, hx, hVP⟩ ↦ ?_⟩
  obtain ⟨g, hg⟩ := ChoiceFunction.exists_apply_eq (N := (· ∈ G s)) hx
  exact ⟨fun _ ↦ g, ⟨x, hx⟩, hg ▸ hVP⟩

/-- Universal quantification over the choice function gives the universal reading of a donkey
sentence. -/
theorem forall_donkey_eq_true_iff [Nonempty E] :
    (∀ f : S → ChoiceFunction E, filtering Det.every (fun y ↦ p y ⊓ antecedent G (b y))
        (fun y ↦ clause G f VP (b y)) = .true) ↔
      ∀ y, p y = .true → ∀ x ∈ G (b y), VP (b y) x := by
  simp only [filtering_every_antecedent_clause_eq_true_iff]
  refine ⟨fun h y hy x hx ↦ ?_, fun h f y hy hG ↦ h y hy _ ((f (b y)).apply_of_exists hG)⟩
  obtain ⟨g, hg⟩ := ChoiceFunction.exists_apply_eq (N := (· ∈ G (b y))) hx
  exact hg ▸ h (fun _ ↦ g) y hy ⟨x, hx⟩

/-- Existential quantification over the choice function gives the existential reading of a
donkey sentence. The choice function varies with the point of evaluation, so each value of the
bound variable gets its own pick. -/
theorem exists_donkey_eq_true_iff [Nonempty E] :
    (∃ f : S → ChoiceFunction E, filtering Det.every (fun y ↦ p y ⊓ antecedent G (b y))
        (fun y ↦ clause G f VP (b y)) = .true) ↔
      ∀ y, p y = .true → (G (b y)).Nonempty → ∃ x ∈ G (b y), VP (b y) x := by
  classical
  simp only [filtering_every_antecedent_clause_eq_true_iff]
  refine ⟨fun ⟨f, h⟩ y hy hG ↦ ⟨_, (f (b y)).apply_of_exists hG, h y hy hG⟩, fun h ↦ ?_⟩
  have key (s : S) (hs : ∃ x ∈ G s, VP s x) :
      ∃ g : ChoiceFunction E, VP s (g (· ∈ G s)) :=
    let ⟨x, hx, hVP⟩ := hs
    let ⟨g, hg⟩ := ChoiceFunction.exists_apply_eq (N := (· ∈ G s)) hx
    ⟨g, hg ▸ hVP⟩
  refine ⟨fun s ↦ if hs : ∃ x ∈ G s, VP s x then (key s hs).choose else .epsilon,
    fun y hy hG ↦ ?_⟩
  have hs := h y hy hG
  simpa only [dite_eq_left hs] using (key (b y) hs).choose_spec

/-! ### Indices -/

/-- The expressivity constraint: every witness set and choice function is named by an index. -/
def Expressive (G : ι → S → Set E) (f : ι → S → ChoiceFunction E) : Prop :=
  Function.Surjective fun i ↦ (G i, f i)

/-- The pairs of a witness set and a choice function index themselves expressively. -/
example : Expressive (ι := (S → Set E) × (S → ChoiceFunction E)) Prod.fst Prod.snd :=
  fun x ↦ ⟨x, rfl⟩

/-- A claim holds on every expressive family that gives the index `i` the witness set `W` iff it
holds of every choice function: the constraint on indexing fixes the witness set of an
indefinite's index and leaves its choice function free. -/
theorem forall_expressive_iff
    (h : ∃ (G : ι → S → Set E) (f : ι → S → ChoiceFunction E), Expressive G f) (i : ι)
    (W : S → Set E) (φ : (S → ChoiceFunction E) → Prop) :
    (∀ (G : ι → S → Set E) (f : ι → S → ChoiceFunction E),
      Expressive G f → G i = W → φ (f i)) ↔ ∀ γ, φ γ := by
  classical
  refine ⟨fun hφ γ ↦ ?_, fun hφ _ f _ _ ↦ hφ (f i)⟩
  obtain ⟨G, f, hGf⟩ := h
  obtain ⟨j, hj⟩ := hGf (W, γ)
  obtain ⟨hG, hf⟩ : G j = W ∧ f j = γ := Prod.mk.inj hj
  have hi : Equiv.swap i j i = j := Equiv.swap_apply_left i j
  simpa [hi, hf] using
    hφ (G ∘ Equiv.swap i j) (f ∘ Equiv.swap i j) (hGf.comp (Equiv.swap i j).surjective)
      (by simp [hi, hG])

/-! ### The subordination constraint -/

/-- The witness set of an indefinite in the local context `R`: empty at the points outside
it. -/
def restrict (R : Set S) (G : S → Set E) (s : S) : Set E :=
  {x | s ∈ R ∧ x ∈ G s}

@[simp]
theorem restrict_nonempty_iff {R : Set S} : (restrict R G s).Nonempty ↔ s ∈ R ∧ (G s).Nonempty := by
  simp [restrict, Set.Nonempty]

/-- *Every tourist bought a ticket. # Most locals have already used it*: with the witness set
restricted to the local context of its indefinite, the pronoun under a second quantifier
presupposes that the second restrictor lies within the first. -/
theorem filtering_clause_restrict_eq_undefined_iff {R : Set S} :
    filtering Q p (fun y ↦ clause (restrict R G) f VP (b y)) = .undefined ↔
      ¬ ∀ y, p y = .true → b y ∈ R ∧ (G (b y)).Nonempty := by
  simp

/-- *Every tourist bought a ticket. # Most locals have already used it*: when the witness set is
restricted to the local context that the first quantifier gives its scope, the pronoun under a
second quantifier is defined only where the second restrictor lies within the first. -/
theorem restrictor_of_filtering_clause_restrict_ne_undefined {W : Type*} [Finite E]
    {q : NumberTree} {A : W → E → Prop} {C : Set W} {R : Set (W × E)}
    (hR : IsLocalContext C {scopeTruth q A} R) {G : W × E → Set E}
    {f : W × E → ChoiceFunction E} {VP : W × E → E → Prop} {Q : Det E} {p : E → Trivalent} {w : W}
    (h : filtering Q p (fun y ↦ clause (restrict R G) f VP (w, y)) ≠ .undefined) {y : E}
    (hy : p y = .true) : A w y := by
  rw [ne_eq, filtering_clause_restrict_eq_undefined_iff, not_not] at h
  have hw := (h y hy).1
  rw [hR.unique (isLocalContext_scopeTruth q A C)] at hw
  exact hw.2.1

end Chatain2025
