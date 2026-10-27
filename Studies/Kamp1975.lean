module

public import Linglib.Semantics.Modification.Classification
public import Linglib.Logic.Trivalent.Basic
public import Mathlib.Data.Set.Basic
public import Mathlib.Algebra.Order.Ring.Rat
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Linglib.Logic.Modal.Extensional

/-!
# Kamp (1975): Two theories about adjectives

Kamp's first theory treats an adjective as a function from properties to properties,
constrained by meaning postulates that make it predicative, privative or affirmative, with
*alleged* satisfying none; extensionality is a separate dimension. His second theory, for vague
adjectives, gives them partial extensions and, after van Fraassen, derives the comparative from
quantification over the admissible completions: one object is at least as A as another when
every completion that puts the second in the extension puts the first in. A rival definition,
which compares the measures of the completion sets, makes any two objects comparable, which Kamp
rejects for adjectives with several criteria such as *clever*; for one-dimensional adjectives the
two agree. Before this, Kamp argues that no many-valued logic handles borderline cases.

## Implementation notes

* The measure of (13) is specialized to atomic `ℚ` weights over a finite set of completions;
  only the ordering matters, so the weights need not sum to one.
* The Smith and Jones witness is symmetric, one criterion each; the paper's scenario is
  asymmetric, and the witness shows the incomparability and the forced verdict, not the
  paper's specific outcome.

## Errata

* Definition (7) asks for a single function $F'$ on extensions with $F(P)(w) = F'(P(w))$ at
  every world, while the gloss after it and the claim that every predicative adjective is
  extensional need $F'$ to vary with the world. A predicative adjective whose property differs
  between worlds, such as `grayAdj`, satisfies (4) and the gloss but not (7) as printed. The
  study reads (7) by its gloss, `ModalLogic.IsExtensional`.

## References

* [kamp-1975]
* [van-fraassen-1969]
* [lewis-1970]
* [klein-1980]
* [partee-2010]
-/

@[expose] public section

namespace Kamp1975

open Modifier Modifier

/-! ### Bridge to single-world predicates

The classification (`Modifier.IsIntersective`, `.IsSubsective`, …) is
one order-theoretic definition instantiated at two carriers: the
intensional `W → E → Prop = W → E → Prop` and the single-world
`E → Prop`. The bridge theorems below show that fixing a world sends
the first instance to the second. -/

section Bridge

variable {W E : Type*}

/-- At a fixed world an intersective modifier of intensional properties is an intersective
modifier of predicates, `N ↦ adj (fun _ ↦ N) w`. -/
theorem intersective_at_world {adj : Modifier (W → E → Prop)}
    (h : IsIntersective adj) (w : W) :
    IsIntersective (fun N : E → Prop ↦ adj (fun _ ↦ N) w) := by
  obtain ⟨Q, hQ⟩ := h
  exact ⟨Q w, fun N ↦ congrFun (hQ fun _ ↦ N) w⟩

/-- At a fixed world a subsective modifier of intensional properties is a subsective modifier
of predicates. -/
theorem subsective_at_world {adj : Modifier (W → E → Prop)}
    (h : IsSubsective adj) (w : W) :
    IsSubsective (fun N : E → Prop ↦ adj (fun _ ↦ N) w) :=
  fun N ↦ h (fun _ ↦ N) w

end Bridge

/-! ### The many-valued dilemma -/

/-- No truth-functional conjunction is both idempotent at the borderline value and false on
borderline contradictions (pp. 130–131). -/
theorem kleene_dilemma :
    ¬∃ (meet : SignType → SignType → SignType), meet 0 0 = 0 ∧ meet 0 (-0) = -1 := by
  rintro ⟨meet, hidem, hcontra⟩
  rw [SignType.neg_zero, hidem] at hcontra
  cases hcontra

/-- Strong Kleene conjunction, `⊓` on `SignType`, takes the idempotent horn of the dilemma, so
borderline contradictions are not false. -/
example : (0 : SignType) ⊓ 0 = 0 ∧ (0 : SignType) ⊓ 0ᶜ ≠ ⊥ :=
  ⟨inf_idem _, SignType.inf_compl_zero_ne_bot⟩

/-! ### The completion comparative

Definition (12) (paper § 4): u₁ is at least as A as u₂ iff every
admissible completion that puts u₂ in the extension also puts u₁ in it.
[klein-1980] § 5.3 states the strict comparative existentially over
comparison classes; the bridge is
`Klein1980.kleinPreorder_eq_kampPreorder`. -/

/-- Kamp's completion comparative, definition (12) of § 4, is the preorder in which `u₁ ≤ u₂`
when every completion in `S` that puts `u₂` in the extension also puts `u₁` in, so that `≤`
reads *at least as A as*. Kamp credits (12) to [lewis-1970], who attributes it to Kaplan. -/
@[reducible] def kampPreorder {E C : Type*} (ext : C → E → Prop) (S : Set C) :
    Preorder E where
  le u₁ u₂ := ∀ c ∈ S, ext c u₂ → ext c u₁
  le_refl _ := fun _ _ h ↦ h
  le_trans _ _ _ hab hbc := fun c hc h ↦ hab c hc (hbc c hc h)

theorem kampPreorder_antitone {E C : Type*} (ext : C → E → Prop) (u₁ u₂ : E) :
    Antitone (fun S ↦ (kampPreorder ext S).le u₁ u₂) :=
  fun _ _ hle hall c hc ↦ hall c (hle hc)

/-! ### Completion and measured comparatives

Kamp's second candidate, definition (13) (paper § 4), compares the
*measures* of the completion sets rather than the sets themselves. His
§ 5 argues against (13) for multi-criteria adjectives: it makes any two
entities comparable, while (12) leaves Smith and Jones incomparable in
cleverness — for Kamp the right verdict. For one-dimensional adjectives
(*heavy*, *tall*, *hot*) the two provably coincide. -/

section MeasuredComparative

variable {E C : Type*} (ext : C → E → Prop) [∀ c e, Decidable (ext c e)]
  (S : Finset C) (p : C → ℚ)

/-- The measured comparative, definition (13) of § 4, holds of `u₁` and `u₂` when the
completions putting `u₂` in the extension weigh at most as much as those putting `u₁` in. -/
def kampMeasureLe (u₁ u₂ : E) : Prop :=
  ∑ c ∈ S with ext c u₂, p c ≤ ∑ c ∈ S with ext c u₁, p c

/-- The measured comparative makes any two objects comparable, Kamp's objection to it in § 5,
which the completion comparative escapes (`clever_incomparable`). -/
theorem kampMeasureLe_total (u₁ u₂ : E) :
    kampMeasureLe ext S p u₁ u₂ ∨ kampMeasureLe ext S p u₂ u₁ :=
  le_total _ _

theorem kampMeasureLe_of_kampPreorder_le (hp : ∀ c ∈ S, 0 ≤ p c) {u₁ u₂ : E}
    (h : (kampPreorder ext (S : Set C)).le u₁ u₂) :
    kampMeasureLe ext S p u₁ u₂ := by
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_
    fun c hc _ ↦ hp c (Finset.mem_filter.mp hc).1
  intro c hc
  rw [Finset.mem_filter] at hc ⊢
  exact ⟨hc.1, h c hc.1 hc.2⟩

/-! #### Smith and Jones

Two criteria for *clever* — problem-solving and quick-wittedness — as
two completions; Smith passes one, Jones the other. Under (12) the two
are incomparable, which Kamp argues is correct; (13) must issue a
verdict (`kampMeasureLe_total`). Kamp's own scenario is asymmetric
(Smith *much* better at problems, only slightly worse in wit, so (13)
wrongly makes Smith cleverer); this symmetric toy witnesses the
incomparability and the forced verdict, not that specific outcome. -/

/-- The two criteria of cleverness, problem solving and quick wit. -/
inductive Crit | problemSolving | quickWit deriving DecidableEq

/-- Smith and Jones. -/
inductive P2 | smith | jones deriving DecidableEq

/-- Smith is clever by the first criterion and Jones by the second. -/
def cleverExt : Crit → P2 → Prop
  | .problemSolving, .smith => True
  | .quickWit,       .jones => True
  | _,               _      => False

/-- By the completion comparative Smith and Jones are incomparable in cleverness, which Kamp
takes to capture the comparative correctly for adjectives with several criteria. -/
theorem clever_incomparable :
    ¬ (kampPreorder cleverExt Set.univ).le .smith .jones ∧
    ¬ (kampPreorder cleverExt Set.univ).le .jones .smith :=
  ⟨fun h ↦ h .quickWit trivial trivial,
   fun h ↦ h .problemSolving trivial trivial⟩

/-! #### One-dimensionality -/

/-- An adjective is one-dimensional, as *heavy*, *tall* and *hot* are in § 5, when the
completion sets of any two entities are comparable by inclusion. The condition is Kamp's (18),
stated in § 6. -/
def OneDimensional : Prop :=
  ∀ u₁ u₂ : E, (∀ c ∈ S, ext c u₁ → ext c u₂) ∨ (∀ c ∈ S, ext c u₂ → ext c u₁)

/-- For a one-dimensional adjective and strictly positive weights, the two comparatives agree (§ 5).
-/
theorem kampPreorder_le_iff_kampMeasureLe (hp : ∀ c ∈ S, 0 < p c)
    (h18 : OneDimensional ext S) (u₁ u₂ : E) :
    (kampPreorder ext (S : Set C)).le u₁ u₂ ↔ kampMeasureLe ext S p u₁ u₂ := by
  refine ⟨kampMeasureLe_of_kampPreorder_le ext S p fun c hc ↦ (hp c hc).le,
          fun h13 ↦ ?_⟩
  rcases h18 u₂ u₁ with h | h
  · exact fun c hc ↦ h c hc
  · intro c hcS hc₂
    by_contra hc₁
    have hlt : ∑ c ∈ S with ext c u₁, p c < ∑ c ∈ S with ext c u₂, p c := by
      refine Finset.sum_lt_sum_of_subset ?_ (i := c) ?_ ?_ (hp c hcS) ?_
      · intro d hd
        rw [Finset.mem_filter] at hd ⊢
        exact ⟨hd.1, h d hd.1 hd.2⟩
      · exact Finset.mem_filter.mpr ⟨hcS, hc₂⟩
      · simp [hc₁]
      · exact fun d hd _ ↦ (hp d (Finset.mem_filter.mp hd).1).le
    exact absurd h13 (not_le.mpr hlt)

end MeasuredComparative

/-! ### A member of each class

Each class in the hierarchy is non-empty: explicit denotations that
provably satisfy each definition from `Classification.lean`, modeling
the classic examples from the literature — "gray" (intersective), "fake"
(privative), "skillful" (subsective but not extensional), "alleged"
(non-subsective/modal).

[partee-2010] argues that the privative class should be eliminated
in favor of subsective + noun coercion. The witness `fakeAdj` below
models the traditional analysis; see `Partee2010.lean` for the
coercion reanalysis. -/

section Witnesses

/-- Two worlds suffice to distinguish extensional from non-extensional. -/
inductive W2 | w₁ | w₂

/-- Three entities suffice for all witness constructions. -/
inductive E3 | a | b | c

/-- *gray* is predicative, Kamp's definition (4) (p. 124), since it conjoins a property with the
noun, so *gray cat* entails both *gray* and *cat*. Only `a` is gray, and only at `w₁`. -/
def grayAdj : Modifier (W2 → E3 → Prop) := fun N w x ↦ (w = .w₁ ∧ x = .a) ∧ N w x

theorem gray_intersective : IsIntersective grayAdj :=
  ⟨fun w x ↦ w = .w₁ ∧ x = .a, fun _ ↦ rfl⟩

/-- *gray* is therefore also extensional and subsective. -/
example : ModalLogic.IsExtensional grayAdj :=
  Modifier.IsIntersective.isExtensional gray_intersective
example : IsSubsective grayAdj := gray_intersective.isSubsective

/-- No single function on extensions gives *gray*, so the predicative *gray* is not extensional by
(7) as printed (p. 125). -/
theorem not_exists_forall_grayAdj_eq :
    ¬ ∃ F' : (E3 → Prop) → E3 → Prop, ∀ N w, grayAdj N w = F' (N w) := by
  rintro ⟨F', hF'⟩
  have h := (congrFun (hF' (fun _ _ ↦ True) .w₁) .a).trans
    (congrFun (hF' (fun _ _ ↦ True) .w₂) .a).symm
  simp [grayAdj] at h

/-- *fake* is privative, Kamp's definition (5) (p. 125), so *fake gun* entails *not a gun*. Kamp
doubts that any English adjective is privative "in all of its possible uses". -/
def fakeAdj : Modifier (W2 → E3 → Prop) := fun N w x ↦
  (match x with | .b => True | _ => False) ∧ ¬ N w x

theorem fake_privative : IsPrivative fakeAdj :=
  Modifier.isPrivative_iff_forall.mpr fun _ _ _ h ↦ h.2

/-- *skillful* is affirmative, Kamp's definition (6) (p. 125), but not extensional (7). A
skillful surgeon is a surgeon, yet skill depends on the noun's intension and not just its current
extension, as in the case of cobblers and darts players that Kamp credits to Lewis. -/
def skillfulAdj : Modifier (W2 → E3 → Prop) := fun N w x ↦
  N w x ∧ match x with
    | .a => N .w₁ .a  -- a's skill assessment depends on N's intension
    | _  => False

theorem skillful_subsective : IsSubsective skillfulAdj :=
  fun _ _ _ h ↦ h.1

theorem skillful_not_extensional : ¬ ModalLogic.IsExtensional skillfulAdj := by
  intro hext
  let N₁ : W2 → E3 → Prop := fun _ _ ↦ True
  let N₂ : W2 → E3 → Prop := fun w x ↦ match w, x with
    | .w₁, .a => False
    | _, _    => True
  have hagree : N₁ .w₂ = N₂ .w₂ := by
    funext x; cases x <;> simp [N₁, N₂]
  have h := hext .w₂ hagree
  have hLHS : skillfulAdj N₁ .w₂ .a := ⟨trivial, trivial⟩
  exact (congrFun h .a ▸ hLHS).2

/-- *alleged* satisfies no meaning postulate, Kamp's opening example (1) (p. 123) being that
*every alleged thief is a thief* is no logical truth. -/
def allegedAdj : Modifier (W2 → E3 → Prop) := fun _N _ x ↦
  match x with | .a => True | _ => False

theorem alleged_extensional : ModalLogic.IsExtensional allegedAdj :=
  fun _ _ _ _ ↦ rfl

/-- *alleged N* does not entail *N*. -/
theorem alleged_not_subsective : ¬ IsSubsective allegedAdj := by
  intro h
  exact h (fun _ _ ↦ False) .w₁ .a trivial

theorem alleged_not_privative : ¬ IsPrivative allegedAdj := by
  intro h
  exact Modifier.isPrivative_iff_forall.mp h (fun _ _ ↦ True) .w₁ .a trivial trivial

end Witnesses

end Kamp1975
