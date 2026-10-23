module

public import Linglib.Pragmatics.Bidirectional
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Order.Prod.Lex.Basic
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Semantics.Reference.Definiteness

/-!
# Blutner (2000): Some aspects of optimality in natural language interpretation

Blutner evaluates form-meaning pairs from the speaker's and the hearer's side at once
(`Pragmatics/Bidirectional.lean`). His schematic tableaux pit an unmarked against a marked form
and a stereotypical against a marked situation, under a constraint F against marked forms and a
constraint C against marked situations. The results below hold for every harmony strictly
monotone in the two markedness orders, so for either ranking of F and C, which the paper leaves
open. Strong bidirection blocks the marked form in every interpretation and yields Horn's division
of pragmatic labour only when the generator stipulates it; weak bidirection derives it.

For presupposition projection, AvoidA counts accommodated markers and BeStrong prefers stronger
outcomes. Ranked in that order they select global accommodation when no binder is available,
binding when the antecedent supplies one, and, where global accommodation is unavailable, the
stronger local reading over the higher intermediate site that van der Sandt's and Geurts's
preference would choose. The Q-principle blocks accommodation when a non-triggering alternative
expresses the same outcome.

## Main statements

* `strong_total_blocking`: strong bidirection blocks the marked form in every interpretation on
  any generator in which both forms can express the stereotypical situation.
* `marked_marked_mem_strongOptimalSet_iff`: strong bidirection pairs the marked form with the
  marked situation only if the generator excludes both mixed pairs.
* `weak_division_of_labour`: weak bidirection pairs the unmarked form with the stereotypical
  situation and the marked form with the marked one.
* `strength_local_height_intermediate`: without global accommodation, BeStrong selects the local
  reading where the higher-site preference selects the intermediate one.

## Implementation notes

* The markedness orders on forms and situations are pulled back from the violations of F and C.
* BeStrong compares outcomes by entailment, as sets of worlds, so the harmony of a resolution is
  its AvoidA count followed lexicographically by its outcome.
* The quantified sentences of the paper's (19) and (20) are read through the conditional schema
  for one individual; global accommodation is left out of their generator because it would
  leave the bound marker free.

## TODO

* The generalization (23), that a trigger does not accommodate iff it has a simple
  non-triggering alternative, as a theorem over generators in which AvoidA ranks first.

## References

* [blutner-2000]
* [horn-1984]
* [van-der-sandt-1992]
* [geurts-1995]
* [asher-lascarides-1998]
-/

@[expose] public section

namespace Blutner2000

open BidirectionalOT Set

/-! ### Total blocking and the division of pragmatic labour

The schematic tableaux (7), (9), (10) and (12): an unmarked and a marked form, such as *kill* and
*cause to die*, and a stereotypical and a marked situation. -/

/-- The unmarked and the marked form. -/
inductive Form where
  | unmarked
  | marked
  deriving DecidableEq, Fintype, Repr

/-- The stereotypical and the marked situation. -/
inductive Situation where
  | stereotypical
  | marked
  deriving DecidableEq, Fintype, Repr

/-- The violations of F, the constraint against marked forms. -/
def Form.markedness : Form → ℕ
  | .unmarked => 0
  | .marked => 1

/-- The violations of C, the constraint against marked situations. -/
def Situation.markedness : Situation → ℕ
  | .stereotypical => 0
  | .marked => 1

instance : LinearOrder Form := LinearOrder.lift' Form.markedness (by decide)

instance : LinearOrder Situation := LinearOrder.lift' Situation.markedness (by decide)

theorem strictMono_profile_markedness :
    StrictMono (profile [(·.1.markedness), (·.2.markedness)] : Form × Situation → List ℕ) ∧
      StrictMono (profile [(·.2.markedness), (·.1.markedness)] : Form × Situation → List ℕ) := by
  refine ⟨strictMono_profile ?_ fun p q h ↦ ?_, strictMono_profile ?_ fun p q h ↦ ?_⟩ <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      exists_eq_or_imp, exists_eq_left]
  · exact ⟨fun _ _ h ↦ h.1, fun _ _ h ↦ h.2⟩
  · exact (Prod.lt_iff.1 h).imp And.left And.right
  · exact ⟨fun _ _ h ↦ h.2, fun _ _ h ↦ h.1⟩
  · exact (Prod.lt_iff.1 h).symm.imp And.right And.left

/-- The iconic pairing matches the unmarked form with the stereotypical situation and the marked
form with the marked one, an isomorphism of the two markedness orders. -/
def iconicity : Form ≃o Situation where
  toFun | .unmarked => .stereotypical | .marked => .marked
  invFun | .stereotypical => .unmarked | .marked => .marked
  left_inv a := by cases a <;> rfl
  right_inv b := by cases b <;> rfl
  map_rel_iff' {a b} := by cases a <;> cases b <;> decide

variable {α : Type*} [Preorder α] {f : Form × Situation → α} {G : Set (Form × Situation)}

/-- On any generator letting both forms express the stereotypical situation, strong bidirection
keeps only the unmarked stereotypical pair, as for (7) and (9). -/
theorem strong_total_blocking (hf : StrictMono f) (hu : (.unmarked, .stereotypical) ∈ G)
    (hm : (.marked, .stereotypical) ∈ G) :
    strongOptimalSet G f = {(.unmarked, .stereotypical)} := by
  ext ⟨a, b⟩
  rw [strongOptimalSet, mem_unblockedSet, blocks_iff_of_strictMono hf, mem_singleton_iff]
  refine ⟨fun ⟨_, hb⟩ ↦ ?_, ?_⟩
  · cases a <;> cases b
    · rfl
    · exact (hb ⟨_, hu, .inl rfl, Prod.mk_lt_mk_iff_right.2 (by decide)⟩).elim
    · exact (hb ⟨_, hu, .inr rfl, Prod.mk_lt_mk_iff_left.2 (by decide)⟩).elim
    · exact (hb ⟨_, hm, .inl rfl, Prod.mk_lt_mk_iff_right.2 (by decide)⟩).elim
  · rintro ⟨⟩
    refine ⟨hu, fun ⟨⟨c, d⟩, _, _, hlt⟩ ↦ ?_⟩
    rcases Prod.lt_iff.1 hlt with ⟨h, -⟩ | ⟨-, h⟩
    · exact Nat.not_lt_zero _ h
    · exact Nat.not_lt_zero _ h

/-- Strong bidirection pairs the marked form with the marked situation iff the generator excludes
both mixed pairs, as stipulated in (10). -/
theorem marked_marked_mem_strongOptimalSet_iff (hf : StrictMono f) :
    (.marked, .marked) ∈ strongOptimalSet G f ↔
      (.marked, .marked) ∈ G ∧ (.marked, .stereotypical) ∉ G ∧ (.unmarked, .marked) ∉ G := by
  rw [strongOptimalSet, mem_unblockedSet, blocks_iff_of_strictMono hf]
  refine ⟨fun ⟨hG, hb⟩ ↦ ⟨hG, fun h ↦ hb ⟨_, h, .inl rfl, Prod.mk_lt_mk_iff_right.2 (by decide)⟩,
    fun h ↦ hb ⟨_, h, .inr rfl, Prod.mk_lt_mk_iff_left.2 (by decide)⟩⟩, fun ⟨hG, hs, hu⟩ ↦
      ⟨hG, fun ⟨⟨c, d⟩, hq, hshare, hlt⟩ ↦ ?_⟩⟩
  cases c <;> cases d
  · rcases hshare with h | h <;> cases h
  · exact hu hq
  · exact hs hq
  · exact lt_irrefl _ hlt

/-- Weak bidirection derives the division of pragmatic labour (12), pairing unmarked with
stereotypical and marked with marked. -/
theorem weak_division_of_labour (hf : StrictMono f) :
    superoptimalSet univ f = {(.unmarked, .stereotypical), (.marked, .marked)} := by
  rw [superoptimalSet_eq_graphOn _ iconicity hf finite_univ.isWF (subset_univ _)]
  ext ⟨a, b⟩
  simp only [mem_graphOn, mem_univ, true_and, mem_insert_iff, mem_singleton_iff, Prod.mk.injEq]
  revert a b
  decide

theorem strongOptimalSet_ssubset_superoptimalSet (hf : StrictMono f) :
    strongOptimalSet univ f ⊂ superoptimalSet univ f := by
  rw [strong_total_blocking hf (mem_univ _) (mem_univ _), weak_division_of_labour hf, pair_comm]
  exact ssubset_insert (by simp)

/-! ### Presupposition projection

A conditional "if p then q" whose consequent presupposes r, with the presupposition resolved
locally, at the antecedent or globally (15), (16). The form is fixed, so each competition is an
I-principle competition among the resolutions. -/

/-- The sites at which the presupposition can be resolved. -/
inductive ProjectionSite where
  | «local»
  | intermediate
  | global
  deriving DecidableEq, Fintype, Repr

/-- The antecedent `p`, the consequent `q` and the presupposition `r`. -/
inductive Atom where
  | p
  | q
  | r
  deriving DecidableEq, Fintype

/-- A world fixes the truth of the three atoms. -/
abbrev World := Atom → Bool

/-- The proposition expressed with the presupposition resolved at the site. -/
def ProjectionSite.projection : ProjectionSite → World → Prop
  | .global => fun w ↦ w .r ∧ (w .p → w .q)
  | .intermediate => fun w ↦ w .r ∧ w .p → w .q
  | .local => fun w ↦ w .p → w .q ∧ w .r

instance (s : ProjectionSite) (w : World) : Decidable (s.projection w) := by
  cases s <;> dsimp only [ProjectionSite.projection] <;> infer_instance

/-- The outcome of resolving at the site, the worlds of the context where its projection holds. -/
def ProjectionSite.outcome (worlds : Finset World) (s : ProjectionSite) : Finset World :=
  worlds.filter s.projection

/-- The harmony of AvoidA ≫ BeStrong compares the number of accommodated markers, then the
outcome, a stronger outcome being more harmonic. -/
def harmony (avoidA : ProjectionSite → ℕ) (worlds : Finset World) (p : Unit × ProjectionSite) :
    ℕ ×ₗ Finset World :=
  toLex (avoidA p.2, p.2.outcome worlds)

local instance : DecidableLT (ℕ ×ₗ Finset World) := Prod.Lex.decidable _ _

/-! #### "If Peter has a dog, then his cat is gray" (15), (17)

No binder is available, so every site accommodates Peter's cat and BeStrong decides. -/

/-- In (17) the global outcome is the strongest and the intermediate one the weakest. -/
theorem dog_outcome_ssubset :
    ProjectionSite.global.outcome .univ ⊂ ProjectionSite.local.outcome .univ ∧
      ProjectionSite.local.outcome .univ ⊂ ProjectionSite.intermediate.outcome .univ := by
  decide

theorem dog_global_accommodation :
    superoptimal .univ (harmony (fun _ ↦ 1) .univ) = {((), .global)} := by
  decide

/-! #### "If Peter has a cat, then his cat is gray" (16), (18)

The antecedent is the presupposition, so the intermediate site binds Peter's cat. -/

/-- The worlds of the cat conditional, where the antecedent is the presupposition. -/
def catWorlds : Finset World := Finset.univ.filter fun w ↦ w .p = w .r

/-- Only the intermediate site binds the presupposition. -/
def catAvoidA : ProjectionSite → ℕ
  | .intermediate => 0
  | _ => 1

/-- In (18) the global outcome is stronger than the intermediate one, and the local and
intermediate outcomes coincide, as the paper's footnote notes. -/
theorem cat_outcome :
    ProjectionSite.global.outcome catWorlds ⊂ ProjectionSite.intermediate.outcome catWorlds ∧
      ProjectionSite.local.outcome catWorlds = ProjectionSite.intermediate.outcome catWorlds := by
  decide

theorem cat_intermediate_binding :
    superoptimal .univ (harmony catAvoidA catWorlds) = {((), .intermediate)} := by
  decide

/-! #### "Every team member will come to the match in her car" (19), (20)

Global accommodation would leave the bound marker free, so only the local and intermediate
sites compete, and both accommodate. Strength selects the local reading, "every team member owns
a car and will come in it", where a preference for the higher site selects the intermediate
reading, "every team member who owns a car will come in it". -/

/-- The resolutions of a presupposition with a bound marker. -/
def boundSites : Finset (Unit × ProjectionSite) := {((), .local), ((), .intermediate)}

/-- The depth of a site below the main context, which the higher-site preference minimizes. -/
def ProjectionSite.depth : ProjectionSite → ℕ
  | .global => 0
  | .intermediate => 1
  | .local => 2

theorem strength_local_height_intermediate :
    superoptimal boundSites (harmony (fun _ ↦ 1) .univ) = {((), .local)} ∧
      superoptimal boundSites (profile [fun _ ↦ 1, (·.2.depth)]) = {((), .intermediate)} := by
  decide

/-! ### Accommodation blocked by the Q-principle (22)

"He had an accident. A car hit him." against "He had an accident. ??The car hit him.": from a
context neutral about cars both continuations have the same outcome, but only the definite
accommodates. -/

/-- AvoidA penalizes the presuppositional definite, which accommodates the car, and not its
non-triggering indefinite alternative, which introduces it. -/
def accidentAvoidA : Definiteness × Unit → ℕ
  | (.definite, _) => 1
  | (.indefinite, _) => 0

theorem accommodation_blocked :
    superoptimal (Finset.univ : Finset (Definiteness × Unit)) accidentAvoidA =
      {(.indefinite, ())} := by
  decide

theorem accommodation_blocked_is_Q :
    QBlocks accidentAvoidA ↑(Finset.univ : Finset (Definiteness × Unit)) (.definite, ()) := by
  decide

end Blutner2000
