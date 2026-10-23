module

public import Linglib.Syntax.Mereological.AngularLocality

/-!
# Derivations in mereological syntax

A derivation builds syntactic objects by licensed subjunctions. Subjoining `x` to `y` is licensed
when nothing subjoins to itself (Irreflexivity), the new part lands in the next free dimension of
`y` (Dimensionality), a part moves only as Angular Locality allows, and an object that is not yet
a part joins only an object that is not a part either (Mereological Extension), so that external
subjunction always targets a root.

Licensed subjunction only adds parthood edges, and it keeps structures well formed. Moving a part
creates no new parts of anything: Angular Locality only lets a part subjoin to an object that
already contains it, and always as a 2-part. Two consequences hold along whole derivations. A
domain stays a domain, so an object leaves a 2-part only from that 2-part's edge, which is
successive cyclicity. And once the 2-part slot of a 2-part `b` is filled by `c`, nothing inside
`b` other than `c` and the parts of `c` ever leaves `b`: a filled 2-part is a strong island.

## Main definitions

* `Parthood.Subjoins P x y Q`: subjoining `x` to `y` is licensed in `P` and yields `Q`.
* `Parthood.Derives`: derivation by licensed subjunctions, and `Parthood.Reaches P x y`: some
  derivation from `P` makes `x` a part of `y`.

## Main statements

* `Parthood.Subjoins.imm_two_of_isPart`: a part always subjoins as a 2-part.
* `Parthood.Derives.acyclic`: derivations preserve Irreflexivity.
* `Parthood.IsDomain.eq_or_nPart_two_of_derives`: an object escapes a 2-part only from its edge.
* `Parthood.IsDomain.not_reaches`: a filled 2-part is an island in every derivation.

## References

* [adger-2025]
-/

@[expose] public section

namespace MereologicalSyntax.Parthood

open Relation

variable {α : Type*} [DecidableEq α] {P Q R : Parthood α} {x y : α}

/-- Subjoining `x` to `y` is licensed in `P` and yields `Q`. -/
structure Subjoins (P : Parthood α) (x y : α) (Q : Parthood α) : Prop where
  /-- Nothing subjoins to itself (Irreflexivity). -/
  ne : x ≠ y
  /-- The new part lands in the next free dimension of `y` (Dimensionality). -/
  subjoin_eq : P.subjoin x y = some Q
  /-- A part moves only as Angular Locality allows. -/
  canSubjoin : P.IsPart x → P.CanSubjoin x y
  /-- An object that is not yet a part joins only an object that is not a part either
  (Mereological Extension). -/
  extension : ¬ P.IsPart x → ¬ P.IsPart y

instance [Fintype α] : Decidable (P.Subjoins x y Q) :=
  decidable_of_iff (x ≠ y ∧ P.subjoin x y = some Q ∧ (P.IsPart x → P.CanSubjoin x y) ∧
      (¬ P.IsPart x → ¬ P.IsPart y))
    ⟨fun ⟨h₁, h₂, h₃, h₄⟩ ↦ ⟨h₁, h₂, h₃, h₄⟩, fun ⟨h₁, h₂, h₃, h₄⟩ ↦ ⟨h₁, h₂, h₃, h₄⟩⟩

/-- `Q` arises from `P` by one licensed subjunction. -/
def Step (P Q : Parthood α) : Prop := ∃ x y, P.Subjoins x y Q

/-- `Q` arises from `P` by licensed subjunctions. -/
def Derives : Parthood α → Parthood α → Prop := ReflTransGen Step

theorem Subjoins.derives (h : P.Subjoins x y Q) : P.Derives Q := .single ⟨x, y, h⟩

@[refl]
theorem Derives.refl (P : Parthood α) : P.Derives P := ReflTransGen.refl

theorem Derives.trans (h₁ : P.Derives Q) (h₂ : Q.Derives R) : P.Derives R :=
  ReflTransGen.trans h₁ h₂

/-! ### What one licensed subjunction changes -/

namespace Subjoins

theorem le (h : P.Subjoins x y Q) : P ≤ Q := le_of_subjoin h.subjoin_eq

theorem imm_iff (h : P.Subjoins x y Q) :
    ∃ n, P.nextDim y = some n ∧ ∀ m a b, Q.Imm m a b ↔ P.Imm m a b ∨ (m = n ∧ a = x ∧ b = y) :=
  imm_subjoin_iff h.subjoin_eq

theorem imm_two_of_isPart (h : P.Subjoins x y Q) (hx : P.IsPart x) : Q.Imm .two x y := by
  obtain ⟨n, hn, hQ⟩ := h.imm_iff
  obtain rfl := nextDim_eq_two (isSome_onePart_of_canSubjoin (h.canSubjoin hx)) hn
  exact (hQ _ _ _).2 (.inr ⟨rfl, rfl, rfl⟩)

private theorem edge_iff (h : P.Subjoins x y Q) (a b : α) :
    (∃ m, Q.Imm m a b) ↔ (∃ m, P.Imm m a b) ∨ (a = x ∧ b = y) := by
  obtain ⟨n, -, hQ⟩ := h.imm_iff
  simp only [hQ]
  exact ⟨fun ⟨m, hm⟩ ↦ hm.imp (⟨m, ·⟩) (·.2), fun h ↦ h.elim (fun ⟨m, hm⟩ ↦ ⟨m, .inl hm⟩)
    fun hab ↦ ⟨n, .inr ⟨rfl, hab⟩⟩⟩

theorem descendant_iff_of_isPart (h : P.Subjoins x y Q) (hx : P.IsPart x) {u v : α} :
    Q.Descendant u v ↔ P.Descendant u v := by
  refine ⟨fun huv ↦ TransGen.closed (fun a b hab ↦ ?_) _ _ huv, (·.mono h.le)⟩
  rcases (h.edge_iff a b).1 hab with hab | ⟨rfl, rfl⟩
  · exact .single hab
  · exact descendant_of_canSubjoin (h.canSubjoin hx)

theorem descendant_iff_of_not_isPart (h : P.Subjoins x y Q) (hx : ¬ P.IsPart x) {u v : α} :
    Q.Descendant u v ↔ P.Descendant u v ∨ ((u = x ∨ P.Descendant u x) ∧ v = y) := by
  have hy : ∀ m b, ¬ P.Imm m y b := fun m b hyb ↦ h.extension hx ⟨m, b, hyb⟩
  constructor
  · intro huv
    induction huv with
    | single hab =>
      rcases (h.edge_iff _ _).1 hab with hab | ⟨rfl, rfl⟩
      · exact .inl (.single hab)
      · exact .inr ⟨.inl rfl, rfl⟩
    | tail _ hbc ih =>
      rcases (h.edge_iff _ _).1 hbc with hbc | ⟨rfl, rfl⟩
      · rcases ih with ih | ⟨-, rfl⟩
        · exact .inl (ih.tail hbc)
        · exact absurd hbc.choose_spec (hy _ _)
      · rcases ih with ih | ⟨-, rfl⟩
        · exact .inr ⟨.inr ih, rfl⟩
        · exact absurd rfl h.ne
  · rintro (huv | ⟨hux, rfl⟩)
    · exact huv.mono h.le
    · have hxy := TransGen.single (r := fun a b ↦ ∃ m, Q.Imm m a b)
        ((h.edge_iff _ _).2 (.inr ⟨rfl, rfl⟩))
      rcases hux with rfl | hux
      · exact hxy
      · exact (hux.mono h.le).trans hxy

theorem descendant_of_isPart (h : P.Subjoins x y Q) {u v : α} (hv : P.IsPart v)
    (huv : Q.Descendant u v) : P.Descendant u v := by
  by_cases hx : P.IsPart x
  · exact (h.descendant_iff_of_isPart hx).1 huv
  · rcases (h.descendant_iff_of_not_isPart hx).1 huv with huv | ⟨-, rfl⟩
    · exact huv
    · exact absurd hv (h.extension hx)

theorem acyclic (h : P.Subjoins x y Q) (hP : P.Acyclic) : Q.Acyclic := by
  intro u hu
  by_cases hx : P.IsPart x
  · exact hP u ((h.descendant_iff_of_isPart hx).1 hu)
  · rcases (h.descendant_iff_of_not_isPart hx).1 hu with hu | ⟨hux, rfl⟩
    · exact hP _ hu
    · rcases hux with rfl | hux
      · exact h.ne rfl
      · exact h.extension hx hux.isPart

end Subjoins

/-! ### Along derivations -/

namespace Derives

theorem le (h : P.Derives Q) : P ≤ Q := by
  induction h with
  | refl => exact le_rfl
  | tail _ hRQ ih =>
    obtain ⟨_, _, hRQ⟩ := hRQ
    exact ih.trans hRQ.le

theorem descendant_of_isPart (h : P.Derives Q) {u v : α} (hv : P.IsPart v)
    (huv : Q.Descendant u v) : P.Descendant u v := by
  induction h with
  | refl => exact huv
  | tail hPR hRQ ih =>
    obtain ⟨_, _, hRQ⟩ := hRQ
    exact ih (hRQ.descendant_of_isPart (hv.mono (Derives.le hPR)) huv)

theorem acyclic (h : P.Derives Q) (hP : P.Acyclic) : Q.Acyclic := by
  induction h with
  | refl => exact hP
  | tail _ hRQ ih =>
    obtain ⟨_, _, hRQ⟩ := hRQ
    exact hRQ.acyclic ih

theorem dimensional (h : P.Derives Q) (hP : P.Dimensional) : Q.Dimensional := by
  induction h with
  | refl => exact hP
  | tail _ hRQ ih =>
    obtain ⟨_, _, hRQ⟩ := hRQ
    exact ih.subjoin hRQ.subjoin_eq

theorem eq_or_descendant_of_nPart_two {b c γ : α} (h : P.Derives Q) (hc : P.Imm .two c b)
    (hγ : Q.NPart .two γ b) : γ = c ∨ P.Descendant γ c :=
  (hγ.eq_or_nPart_of_imm (h.le hc)).imp_right fun hγc ↦
    h.descendant_of_isPart ⟨.two, b, hc⟩ (descendant_of_nPart hγc)

theorem not_canSubjoin_of_not_descendant {γ β : α} (h : P.Derives Q) (hβ : P.IsPart β)
    (hγβ : ¬ P.Descendant γ β) : ¬ Q.CanSubjoin γ β := fun hc ↦
  hγβ (h.descendant_of_isPart hβ (descendant_of_canSubjoin hc))

theorem not_imm_of_not_descendant {γ β : α} {n : Dim} (h : P.Derives Q) (hβ : P.IsPart β)
    (hγβ : ¬ P.Descendant γ β) : ¬ Q.Imm n γ β := fun hn ↦
  hγβ (h.descendant_of_isPart hβ (.single ⟨n, hn⟩))

end Derives

/-- Some derivation from `P` makes `x` a part of `y`. -/
def Reaches (P : Parthood α) (x y : α) : Prop := ∃ Q, P.Derives Q ∧ ∃ n, Q.Imm n x y

theorem Subjoins.reaches (h : P.Subjoins x y Q) : P.Reaches x y :=
  let ⟨n, _, hQ⟩ := h.imm_iff
  ⟨Q, h.derives, n, (hQ _ _ _).2 (.inr ⟨rfl, rfl, rfl⟩)⟩

theorem Reaches.of_derives {a b : α} (h : P.Derives Q) (hQ : Q.Reaches a b) : P.Reaches a b :=
  let ⟨R, hR, hab⟩ := hQ
  ⟨R, h.trans hR, hab⟩

/-! ### Domains along derivations -/

namespace IsDomain

variable {S : Set α} {b c γ β : α}

theorem subjoins (hD : P.IsDomain S b) (h : P.Subjoins x y Q) : Q.IsDomain S b where
  isPart z hz := (hD.isPart z hz).mono h.le
  exit z hz n w hzw hw := by
    obtain ⟨d, hd, hQ⟩ := h.imm_iff
    rcases (hQ _ _ _).1 hzw with hzw | ⟨rfl, rfl, rfl⟩
    · exact (hD.exit z hz n w hzw hw).imp_right (·.imp_right (·.mono h.le))
    · have hx := h.canSubjoin (hD.isPart _ hz)
      exact ⟨nextDim_eq_two (isSome_onePart_of_canSubjoin hx) hd,
        (hD.eq_or_nPart_two_of_canSubjoin hz hw hx).imp_right (·.mono h.le)⟩

theorem derives (hD : P.IsDomain S b) (h : P.Derives Q) : Q.IsDomain S b := by
  induction h with
  | refl => exact hD
  | tail _ hRQ ih =>
    obtain ⟨_, _, hRQ⟩ := hRQ
    exact ih.subjoins hRQ

theorem eq_or_nPart_two_of_derives (hD : P.IsDomain S b) (h : P.Derives Q) {n : Dim}
    (hγ : γ ∈ S) (hβ : β ∉ S) (hγβ : Q.Imm n γ β) : γ = b ∨ Q.NPart .two γ b :=
  ((hD.derives h).exit γ hγ n β hγβ hβ).2

theorem not_reaches (hD : P.IsDomain S b) (hc : P.Imm .two c b) (hγ : γ ∈ S) (hγb : γ ≠ b)
    (hγc : γ ≠ c) (hdc : ¬ P.Descendant γ c) (hβ : β ∉ S) : ¬ P.Reaches γ β :=
  fun ⟨_, h, _, hγβ⟩ ↦ (hD.eq_or_nPart_two_of_derives h hγ hβ hγβ).elim hγb fun hb ↦
    (h.eq_or_descendant_of_nPart_two hc hb).elim hγc hdc

end IsDomain

end MereologicalSyntax.Parthood
