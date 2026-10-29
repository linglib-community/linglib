module

public import Linglib.Core.Logic.Function.FactorsThrough
public import Linglib.Syntax.Gender.Basic

/-!
# Gender assignment systems

This file defines an assignment system, the rules by which a language assigns its nouns to
genders, and its semantic core.

An assignment system is an ordered list of rules, each reading either a noun's meaning, a
semantic rule, or its form, a formal rule, morphological or phonological; the first rule that
applies decides, and a residue gender catches what no rule covers. The order is part of the
system. Where a semantic and a formal rule both apply they can conflict, and many systems give
the semantic rules precedence (`AssignmentSystem.SemanticFirst`), while others let a formal rule
win, as the German diminutives make *Männchen* 'little man' neuter. Where only one kind of rule
applies the order is idle. The semantic core is the set of nouns the semantic rules cover, and
in a system whose semantic rules come first it determines gender by meaning. Typological work
finds no system that is formal alone, that is, no attested system with an empty semantic core.

## Main definitions

* `Gender.AssignmentRule`: a semantic or a formal rule.
* `Gender.AssignmentSystem`: an ordered list of rules and a residue gender.
* `Gender.AssignmentSystem.assign`: the gender the first applicable rule gives.
* `Gender.AssignmentSystem.semantic`, `Gender.AssignmentSystem.formal`: the semantic and the
  formal rules in order, each as one partial function.
* `Gender.AssignmentSystem.SemanticFirst`: every semantic rule precedes every formal rule.
* `Gender.AssignmentSystem.IsStrictSemantic`: a system whose formal rules never apply.
* `Gender.AssignmentSystem.semanticCore`: the nouns the semantic rules cover.
* `Gender.IsNatural`: a noun's gender is the one a semantic rule assigns its meaning.

## Main results

* `Gender.AssignmentSystem.assign_of_semantic`: where the semantic rules come first, they decide
  the nouns they cover.
* `Gender.AssignmentSystem.assign_of_formal`: a formal rule decides in the semantic residue,
  whatever the order.
* `Gender.AssignmentSystem.factorsThrough_semanticCore`: where the semantic rules come first,
  gender is a function of meaning on the semantic core.
* `Gender.AssignmentSystem.factorsThrough_of_isStrictSemantic`: in a strict semantic system,
  gender is a function of meaning everywhere.
* `Gender.AssignmentSystem.isNatural_iff_mem_semanticCore`: where the semantic rules come first,
  a noun's gender is natural exactly on the semantic core.

## Implementation notes

The system is typed by the meaning `σ` its semantic rules read and the form `φ` its formal
rules read; a language's fragment supplies the maps from nouns to both. A rule is a partial
function to a gender, and a rule set is applied in its listed order.

## References

* [corbett-1991] — chapters 2 and 3: semantic and formal assignment, and the semantic core
* [dahl-2000] — the animacy refinement of the semantic core
* [kramer-2015] — the semantic core generalization restated
-/

@[expose] public section

namespace Gender

section Natural

variable {N σ G : Type*}

/-- A noun's gender is natural when the semantic rule assigns it to the noun's meaning. -/
def IsNatural (rule : σ → Option G) (sem : N → σ) (gender : N → G) (n : N) : Prop :=
  rule (sem n) = some (gender n)

instance [DecidableEq G] (rule : σ → Option G) (sem : N → σ) (gender : N → G) :
    DecidablePred (IsNatural rule sem gender) :=
  fun _ ↦ inferInstanceAs (Decidable (_ = _))

end Natural

/-- A gender assignment rule reads a noun's meaning, a semantic rule, or its form, a formal rule,
morphological or phonological, and assigns a gender where it applies. -/
inductive AssignmentRule (σ φ G : Type*) where
  | semantic (rule : σ → Option G)
  | formal (rule : φ → Option G)

namespace AssignmentRule

variable {σ φ G : Type*}

/-- The gender a rule gives a semantic rule's reading of the meaning, `none` for a formal rule. -/
def readMeaning : AssignmentRule σ φ G → σ → Option G
  | semantic r, s => r s
  | formal _, _ => none

/-- The gender a rule gives a formal rule's reading of the form, `none` for a semantic rule. -/
def readForm : AssignmentRule σ φ G → φ → Option G
  | semantic _, _ => none
  | formal r, f => r f

/-- The gender a rule gives a noun of meaning `s` and form `f`. -/
def apply (r : AssignmentRule σ φ G) (s : σ) (f : φ) : Option G :=
  (r.readMeaning s).or (r.readForm f)

theorem apply_of_readMeaning_eq_none {r : AssignmentRule σ φ G} {s : σ} (f : φ)
    (h : r.readMeaning s = none) : r.apply s f = r.readForm f := by
  simp [apply, h]

theorem apply_of_readForm_eq_none {r : AssignmentRule σ φ G} (s : σ) {f : φ}
    (h : r.readForm f = none) : r.apply s f = r.readMeaning s := by
  cases r <;> simp_all [apply, readMeaning, readForm]

end AssignmentRule

/-- An assignment system consists of rules, applied in order, and the residue gender. -/
structure AssignmentSystem (σ φ G : Type*) where
  /-- The rules, the first applicable one deciding. -/
  rules : List (AssignmentRule σ φ G)
  /-- The gender of nouns no rule covers. -/
  residue : G

namespace AssignmentSystem

private theorem findSome?_congr {α β : Type*} {f g : α → Option β} {l : List α}
    (h : ∀ x ∈ l, f x = g x) : l.findSome? f = l.findSome? g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.findSome?_cons, h a List.mem_cons_self,
      ih fun x hx ↦ h x (List.mem_cons_of_mem a hx)]

variable {N σ φ G : Type*} (A : AssignmentSystem σ φ G) (sem : N → σ) (form : N → φ)

/-- The gender of a noun is the one the first applicable rule gives, or the residue gender. -/
def assign (n : N) : G := (A.rules.findSome? (·.apply (sem n) (form n))).getD A.residue

/-- The semantic rules in order, as one partial function of the meaning. -/
def semantic (s : σ) : Option G := A.rules.findSome? (·.readMeaning s)

/-- The formal rules in order, as one partial function of the form. -/
def formal (f : φ) : Option G := A.rules.findSome? (·.readForm f)

/-- The semantic rules take precedence when every semantic rule precedes every formal rule. -/
def SemanticFirst : Prop :=
  ∃ (sems : List (σ → Option G)) (forms : List (φ → Option G)),
    A.rules = sems.map .semantic ++ forms.map .formal

variable {A sem form}

/-- Where the semantic rules come first, the gender is the semantic rules' if they apply, then
the formal rules', then the residue. -/
theorem assign_eq_of_semanticFirst (h : A.SemanticFirst) (n : N) :
    A.assign sem form n = ((A.semantic (sem n)).or (A.formal (form n))).getD A.residue := by
  obtain ⟨sems, forms, hr⟩ := h
  have h₁ : sems.findSome? (fun _ ↦ (none : Option G)) = none :=
    List.findSome?_eq_none_iff.2 fun _ _ ↦ rfl
  have h₂ : forms.findSome? (fun _ ↦ (none : Option G)) = none :=
    List.findSome?_eq_none_iff.2 fun _ _ ↦ rfl
  simp [assign, semantic, formal, hr, List.findSome?_map, Function.comp_def, h₁, h₂,
    AssignmentRule.apply, AssignmentRule.readMeaning, AssignmentRule.readForm]

/-- Semantic rules that come first decide the nouns they cover. -/
theorem assign_of_semantic (h : A.SemanticFirst) {n : N} {g : G}
    (hs : A.semantic (sem n) = some g) : A.assign sem form n = g := by
  simp [assign_eq_of_semanticFirst h, hs]

theorem assign_of_semantic_eq_none {n : N} (h : A.semantic (sem n) = none) :
    A.assign sem form n = (A.formal (form n)).getD A.residue := by
  have h' := List.findSome?_eq_none_iff.1 h
  rw [assign, formal]
  congr 1
  exact findSome?_congr fun r hr ↦ AssignmentRule.apply_of_readMeaning_eq_none _ (h' r hr)

/-- A formal rule decides in the semantic residue, whatever the order of the rules. -/
theorem assign_of_formal {n : N} {g : G} (h₁ : A.semantic (sem n) = none)
    (h₂ : A.formal (form n) = some g) : A.assign sem form n = g := by
  simp [assign_of_semantic_eq_none h₁, h₂]

theorem assign_of_residue {n : N} (h₁ : A.semantic (sem n) = none)
    (h₂ : A.formal (form n) = none) : A.assign sem form n = A.residue := by
  simp [assign_of_semantic_eq_none h₁, h₂]

variable (A) in
/-- A strict semantic system has no formal rule that applies. -/
def IsStrictSemantic : Prop := ∀ x, A.formal x = none

/-- In a strict semantic system the gender is a function of the meaning. -/
theorem factorsThrough_of_isStrictSemantic (h : A.IsStrictSemantic) :
    Function.FactorsThrough (A.assign sem form) sem := fun a b hab ↦ by
  have key (n : N) : A.assign sem form n = (A.semantic (sem n)).getD A.residue := by
    have h' := List.findSome?_eq_none_iff.1 (h (form n))
    rw [assign, semantic]
    congr 1
    exact findSome?_congr fun r hr ↦ AssignmentRule.apply_of_readForm_eq_none _ (h' r hr)
  rw [key, key, hab]

variable (A sem) in
/-- The semantic core is the set of nouns the semantic rules cover. -/
def semanticCore : Set N := {n | (A.semantic (sem n)).isSome}

/-- Where the semantic rules come first, gender is a function of meaning on the semantic
core. -/
theorem factorsThrough_semanticCore (h : A.SemanticFirst) :
    ((A.semanticCore sem).domRestrict (A.assign sem form)).FactorsThrough
      ((A.semanticCore sem).domRestrict sem) :=
  fun a b hab ↦ by
    obtain ⟨g, hg⟩ := Option.isSome_iff_exists.1 b.2
    have hab' : sem a = sem b := hab
    simp only [Set.domRestrict_apply, assign_eq_of_semanticFirst h, hab', hg, Option.some_or,
      Option.getD_some]

/-- Where the semantic rules come first, a noun's gender is natural exactly when the noun lies
in the semantic core. -/
theorem isNatural_iff_mem_semanticCore (h : A.SemanticFirst) (n : N) :
    IsNatural A.semantic sem (A.assign sem form) n ↔ n ∈ A.semanticCore sem := by
  cases hs : A.semantic (sem n) <;>
    simp [IsNatural, semanticCore, assign_eq_of_semanticFirst h, hs]

end AssignmentSystem

end Gender
