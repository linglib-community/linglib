module

public import Linglib.Semantics.Conditionals.Restrictor
public import Linglib.Data.Examples.VonFintelIatridou2005
public import Mathlib.Tactic.DeriveFintype

/-!
# von Fintel & Iatridou (2005): What to Do If You Want to Go to Harlem

This file formalizes [von-fintel-iatridou-2005]'s analysis of anankastic conditionals, the
Harlem sentence *if you want to go to Harlem, you have to take the A train* (1). Three analyses
in [kratzer-1991]'s framework fail. The obvious one, the *if*-clause restricting the modal base
of a teleological *have to* ordered by the actual goals (11), founders on the Hoboken problem:
when you actually want to go to Hoboken the best *want-Harlem* worlds take the PATH train, so the
sentence is predicted false. [saebo-2001]'s analysis adds the hypothetical goal to the ordering
source instead (14), and founders on conflicting goals: with Hoboken and Harlem inconsistent,
the best worlds achieve either, so the sentence is again false (13). The nested analysis, a
covert closeness modal restricted by the *if*-clause over the teleological one (15), (16),
fails where the closest *want-Harlem* worlds keep the Hoboken goal (§5). The paper's proposal
follows [sloman-1970]: a teleological modal takes a designated goal, which every world
quantified over achieves, while the remaining goals are ancillary considerations that rank
those worlds; *have to* quantifies over all goal-achieving accessible worlds and *ought to*
over the best of them (24), so *have to* entails *ought to* and not conversely (`haveTo`,
`oughtTo`). The designated goal overrides the actual goals, which dissolves the Hoboken and
mayor problems (25), (26) and predicts the *have to* and *ought to* verdicts of Huitink's van
Nistelrooy scenario (27). Necessary conditions come out trivially true under *have to* (34),
and [nissenbaum-2005]'s *to go to Harlem, you ought to kiss Pedro Martinez* (36) comes out true,
against which the paper conjectures that the prejacent must be an essential part of a way of
achieving the goal (42), `IsEssentialPart`.

## Implementation notes

The obvious analysis is `Conditional.Restrictor.conditionalNecessity`, and the designated-goal
modals are Kratzer necessity over the base restricted to the goal, with the ancillary ordering
source for *ought to* and the empty one for *have to*. The scenarios are finite world types
with the relevant propositions as predicates and the refutations decided. The condition (42)
quantifies over arbitrary propositions, and so holds of any prejacent as soon as some accessible
world lacks both the prejacent and the goal (`isEssentialPart_of_exists`); the paper leaves the
status of the condition open. The paper's examples are the rows of
`Data.Examples.VonFintelIatridou2005`.

## References

* [von-fintel-iatridou-2005]
* [kratzer-1991]
* [saebo-2001]
* [sloman-1970]
* [nissenbaum-2005]
-/

@[expose] public section

namespace VonFintelIatridou2005

open Modality Conditional.Restrictor

variable {W : Type*} {f g : Background W} {p q : W → Prop} {w : W}

/-! ### The obvious analysis and the Hoboken problem (§3) -/

/-- In the Hoboken scenario you take the A train or the PATH train, and hypothetically want to go
to Harlem or not; the A train reaches Harlem, the PATH train Hoboken. -/
inductive Hoboken
  /-- Wants Harlem, takes the A train. -/
  | wantA
  /-- Wants Harlem, takes the PATH train. -/
  | wantPath
  /-- Does not want Harlem, takes the A train. -/
  | otherA
  /-- Does not want Harlem, takes the PATH train. -/
  | otherPath
  deriving DecidableEq, Fintype

namespace Hoboken

abbrev wantHarlem : Hoboken → Prop := fun w ↦ w = wantA ∨ w = wantPath
abbrev takeA : Hoboken → Prop := fun w ↦ w = wantA ∨ w = otherA
abbrev goHoboken : Hoboken → Prop := fun w ↦ w = wantPath ∨ w = otherPath
abbrev goHarlem : Hoboken → Prop := takeA

/-- The actual goal in every world is to go to Hoboken. -/
abbrev goals : Background Hoboken := fun _ ↦ {goHoboken}

/-- On the obvious analysis (11) the Harlem sentence is false, since the best *want-Harlem* world
takes the PATH train. -/
theorem not_obvious : ¬ conditionalNecessity ⊥ goals wantHarlem takeA wantA := by
  simp only [conditionalNecessity, necessity_iff, bestWorlds, Preorder.mem_minimals_iff,
    Background.mem_accessibleWorlds, Background.restrict, Preorder.ofCriteria_le_iff,
    Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq, Pi.bot_apply,
    Set.bot_eq_empty, Set.mem_empty_iff_false, false_imp_iff, implies_true, and_true]
  decide

end Hoboken

/-! ### Sæbø's analysis and conflicting goals (§4) -/

/-- The conflicting-goals scenario (13): this afternoon you take the A train to Harlem or the
PATH train to Hoboken, not both. -/
inductive Conflict
  | aTrain
  | pathTrain
  deriving DecidableEq, Fintype

namespace Conflict

abbrev takeA : Conflict → Prop := (· = aTrain)
abbrev goHarlem : Conflict → Prop := takeA
abbrev goHoboken : Conflict → Prop := (· = pathTrain)

/-- Sæbø's ordering source (14) is the actual goal of going to Hoboken with the hypothetical
goal of going to Harlem added. -/
abbrev saebo : Background Conflict := fun _ ↦ {goHoboken, goHarlem}

theorem not_saebo : ¬ necessity ⊥ saebo takeA aTrain := by
  simp only [necessity_iff, bestWorlds, Preorder.mem_minimals_iff, Background.mem_accessibleWorlds,
    Preorder.ofCriteria_le_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
    forall_eq_or_imp, forall_eq,
    Pi.bot_apply,
    Set.bot_eq_empty, Set.mem_empty_iff_false, false_imp_iff,
    implies_true]
  decide

end Conflict

/-! ### Nested modality (§5) -/

/-- In the scenario of §5 the closest world in which you want to go to Harlem is one in which
you still want to go to Hoboken as well. -/
inductive Nested
  /-- The actual world: wants Hoboken, takes the PATH train. -/
  | actual
  /-- Wants both, takes the PATH train. -/
  | bothPath
  /-- Wants both, takes the A train. -/
  | bothA
  deriving DecidableEq, Fintype

namespace Nested

abbrev wantHarlem : Nested → Prop := fun w ↦ w = bothPath ∨ w = bothA
abbrev takeA : Nested → Prop := (· = bothA)
abbrev goHoboken : Nested → Prop := fun w ↦ w = actual ∨ w = bothPath
abbrev goHarlem : Nested → Prop := takeA

/-- The goals of each world are Hoboken in the actual world and both in the others. -/
def goals : Background Nested
  | actual => {goHoboken}
  | _ => {goHoboken, goHarlem}

/-- The closeness ordering of the higher modal is agreement with the actual world on wanting
Hoboken. -/
abbrev closeness : Background Nested := fun _ ↦ {goHoboken}

/-- On the nested analysis (16) the Harlem sentence is false, since the PATH train remains among the
best worlds. -/
theorem not_nested :
    ¬ conditionalNecessity ⊥ closeness wantHarlem
      (fun w' ↦ necessity ⊥ goals takeA w') actual := by
  simp only [conditionalNecessity, necessity_iff, bestWorlds, Preorder.mem_minimals_iff,
    Background.mem_accessibleWorlds, Background.restrict, Preorder.ofCriteria_le_iff,
    Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq, Pi.bot_apply,
    Set.bot_eq_empty, Set.mem_empty_iff_false, false_imp_iff, implies_true, and_true]
  intro h
  have := h bothPath (by decide) bothPath
  simp only [goals, Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq] at this
  exact absurd (this (by decide)) (by decide)

end Nested

/-! ### Designated goals (§6) -/

/-- *To p, have to q* (24b) holds when every accessible world achieving the designated goal `p`
is a `q`-world. -/
def haveTo (f : Background W) (p q : W → Prop) (w : W) : Prop :=
  conditionalNecessity f ⊥ p q w

/-- *To p, ought to q* (24a) holds when every accessible world achieving the designated goal `p`
that is best by the ancillary considerations `g` is a `q`-world. -/
def oughtTo (f g : Background W) (p q : W → Prop) (w : W) : Prop :=
  conditionalNecessity f g p q w

theorem haveTo_iff : haveTo f p q w ↔ ∀ v ∈ f.accessibleWorlds w, p v → q v :=
  (restrictor_eq_strict f p q w).trans Conditional.mem_strictImp_forall

theorem oughtTo_of_haveTo (h : haveTo f p q w) : oughtTo f g p q w := by
  rw [oughtTo, conditionalNecessity, necessity_iff]
  intro v hv
  have hv' := Background.mem_accessibleWorlds.1 (Preorder.minimals_subset _ _ hv)
  exact haveTo_iff.1 h v (Background.mem_accessibleWorlds.2 fun r hr ↦
    hv' r (Set.mem_insert_of_mem _ hr)) (hv' p (Set.mem_insert _ _))

/-- A necessary condition of the goal is trivially something you have to do (34). -/
theorem haveTo_of_imp (h : ∀ v, p v → q v) : haveTo f p q w :=
  haveTo_iff.2 fun v _ hp ↦ h v hp

/-- In Sloman's London example (23), *you ought to take the train, but you don't have to* is true,
the train being the best means but not the only one. -/
theorem exists_oughtTo_not_haveTo :
    oughtTo (⊥ : Background Bool) (fun _ ↦ {(· = true)}) (fun _ ↦ True) (· = true) true ∧
      ¬ haveTo (⊥ : Background Bool) (fun _ ↦ True) (· = true) true := by
  simp only [oughtTo, conditionalNecessity, haveTo_iff, necessity_iff, bestWorlds,
    Preorder.mem_minimals_iff, Background.mem_accessibleWorlds, Background.restrict,
    Preorder.ofCriteria_le_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
    forall_eq_or_imp, forall_eq,
    Pi.bot_apply,
    Set.bot_eq_empty, Set.mem_empty_iff_false, false_imp_iff, implies_true,
    and_true]
  decide

/-- With going to Harlem the designated goal (25), you have to take the A train whatever your actual
goals. -/
theorem Hoboken.haveTo_takeA : haveTo ⊥ Hoboken.goHarlem Hoboken.takeA Hoboken.wantA :=
  haveTo_of_imp fun _ h ↦ h

/-- In Huitink's van Nistelrooy scenario (27) both the A and the C train reach Harlem, and Ruud
rides the A train. -/
inductive Ruud
  | aTrain
  | cTrain
  deriving DecidableEq, Fintype

namespace Ruud

abbrev takeA : Ruud → Prop := (· = aTrain)
abbrev meetRuud : Ruud → Prop := takeA

theorem not_haveTo_and_oughtTo :
    ¬ haveTo ⊥ (fun _ ↦ True) takeA aTrain ∧
      oughtTo ⊥ (fun _ ↦ {meetRuud}) (fun _ ↦ True) takeA aTrain := by
  simp only [oughtTo, conditionalNecessity, haveTo_iff, necessity_iff, bestWorlds,
    Preorder.mem_minimals_iff, Background.mem_accessibleWorlds, Background.restrict,
    Preorder.ofCriteria_le_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
    forall_eq_or_imp, forall_eq,
    Pi.bot_apply,
    Set.bot_eq_empty, Set.mem_empty_iff_false, false_imp_iff, implies_true,
    and_true]
  decide

end Ruud

/-! ### Kissing Pedro Martinez (§7.2) -/

/-- In Nissenbaum's scenario (36) the A and the C train reach Harlem, Pedro Martinez rides the C
train, and you want to kiss him. -/
inductive Pedro
  | aTrain
  | cTrainKiss
  | home
  deriving DecidableEq, Fintype

namespace Pedro

abbrev goHarlem : Pedro → Prop := fun w ↦ w = aTrain ∨ w = cTrainKiss
abbrev kissPedro : Pedro → Prop := (· = cTrainKiss)

theorem oughtTo_kissPedro : oughtTo ⊥ (fun _ ↦ {kissPedro}) goHarlem kissPedro aTrain := by
  simp only [oughtTo, conditionalNecessity, necessity_iff, bestWorlds, Preorder.mem_minimals_iff,
    Background.mem_accessibleWorlds, Background.restrict, Preorder.ofCriteria_le_iff,
    Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq, Pi.bot_apply,
    Set.bot_eq_empty, Set.mem_empty_iff_false, false_imp_iff, implies_true, and_true]
  decide

end Pedro

/-- By (42), `q` is an essential part of a way of achieving `p` when some premises together with
`q` entail `p` over the modal base while without `q` they do not. -/
def IsEssentialPart (f : Background W) (p q : W → Prop) (w : W) : Prop :=
  ∃ P : Set (W → Prop), sInf (insert q (f w ∪ P)) ≤ p ∧ ¬ sInf (f w ∪ P) ≤ p

/-- Over arbitrary premises any prejacent is an essential part (42) once some accessible world lacks
both the prejacent and the goal. -/
theorem isEssentialPart_of_exists (h : ∃ v ∈ f.accessibleWorlds w, ¬ q v ∧ ¬ p v) :
    IsEssentialPart f p q w := by
  obtain ⟨v, hv, hq, hp⟩ := h
  refine ⟨{fun u ↦ p u ∨ ¬ q u}, fun u hu ↦ ?_, fun hall ↦ hp (hall v ?_)⟩
  · simp only [sInf_insert, sInf_union, sInf_singleton, Pi.inf_apply, inf_Prop_eq] at hu
    exact hu.2.2.resolve_right (not_not.2 hu.1)
  · simp only [sInf_union, sInf_singleton, Pi.inf_apply, inf_Prop_eq]
    exact ⟨hv, Or.inr hq⟩

/-- In Nissenbaum's scenario, staying home neither kisses Pedro nor reaches Harlem, so kissing
Pedro counts as essential by (42). -/
theorem Pedro.isEssentialPart_kissPedro :
    IsEssentialPart ⊥ Pedro.goHarlem Pedro.kissPedro Pedro.aTrain :=
  isEssentialPart_of_exists ⟨Pedro.home, by simp, by decide⟩

end VonFintelIatridou2005
