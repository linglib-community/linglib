module

public import Linglib.Logic.Trivalent.Four
public import Linglib.Logic.Trivalent.Basic
public import Linglib.Logic.Consequence

/-!
# Fitting (2021): The strict/tolerant idea and bilattices

This file formalizes Fitting's generalization of the strict/tolerant logic `ST` of Cobreros,
Égré, Ripley and van Rooij from three values to any logical bilattice: an interlaced bilattice
with negation and conflation together with a prime bifilter of designated values, after Arieli
and Avron. Over its exact values `−a = a` and anticonsistent values `−a ≤ₖ a` live
two logics (Definition 8.7.1): `ST⟨B, F⟩` reads premises strictly and conclusions tolerantly
over anticonsistent valuations, `C⟨B, F⟩` reads both strictly over exact valuations. They
validate the same sequents (Proposition 8.7.2, `stValid_iff_cValid`), yet cut is locally valid
only in the second (Proposition 8.7.3, `cut_not_local_stValid`).

The examples come from products `L ⊙ L` of De Morgan algebras: the exact values of `L ⊙ L` are
`L` (Proposition 8.8.3, `exactIso`), `D × L` is a prime bifilter for every prime filter `D`
(Lemma 8.9.2, `PrimeFilter.prod`), and `C⟨L ⊙ L, D × L⟩` is the logic `⟨L, D⟩` itself
(Proposition 8.9.3, `cValid_prod_iff`). Hence every logical De Morgan algebra has a
strict/tolerant counterpart with the same consequence relation (Proposition 8.10.1,
`stValid_prod_iff`): classical logic from `Bool`, `K3` and `LP` from `SignType`, and `FDE`
from `FOUR` (Examples 8.10.2–8.10.5).

## Implementation notes

* Formulas have conjunction, disjunction and negation only (Definition 8.6.1); prime bifilters and
  prime filters carry the nonemptiness and properness that §8.2 requires of designated sets.
* Sequent satisfaction is `Consequence.Satisfies`, with strict and tolerant designation as the
  premise and conclusion standards, so local cut in `C⟨B, F⟩` is `Consequence.Satisfies.cut`.
  `STValid` and `CValid` are `Consequence.MixedConsequence` over the anticonsistent and exact
  valuations and `LValid` over all valuations into `L`, so Propositions 8.7.2 and 8.9.3 are pairs
  of model correspondences (`Consequence.MixedConsequence.comap`).
* Lemma 8.8.2, the general interlaced-bilattice route to Proposition 8.8.3, is not formalized;
  the proposition is proved in coordinates for the product.
* Locators use the chapter's numbering, `8.n` for the preprint's `§n`.

## References

* [fitting-2021]
* [cobreros-etal-2012]
* [arieli-avron-1996]
* [arieli-avron-1998]
* [belnap-1977]
* [priest-1979]
-/

@[expose] public section

open Bilattice Product

namespace Fitting2021

variable {B α : Type*}

/-! ### Formulas and valuations (§8.6) -/

/-- Formulas over propositional letters built by conjunction, disjunction and negation, with no
implication ([fitting-2021] Def 8.6.1). -/
inductive Fml (α : Type*) where
  | atom (p : α)
  | and (φ ψ : Fml α)
  | or (φ ψ : Fml α)
  | not (φ : Fml α)

section Eval

variable [Lattice B] [InvolutiveCompl B] [Lattice (Know B)]

/-- The extension of a valuation to formulas ([fitting-2021] Def 8.6.2). -/
def Fml.eval (v : α → B) : Fml α → B
  | atom p => v p
  | and φ ψ => φ.eval v ⊓ ψ.eval v
  | or φ ψ => φ.eval v ⊔ ψ.eval v
  | not φ => (φ.eval v)ᶜ

section Conflation

variable [Conflation B] [NegConfComm B]

theorem eval_isExact {v : α → B} (hv : ∀ p, IsExact (v p)) :
    ∀ φ : Fml α, IsExact (φ.eval v)
  | .atom p => hv p
  | .and φ ψ => (eval_isExact hv φ).inf (eval_isExact hv ψ)
  | .or φ ψ => (eval_isExact hv φ).sup (eval_isExact hv ψ)
  | .not φ => (eval_isExact hv φ).compl

variable [Negation B] [IsInterlaced B]

theorem eval_isAnticonsistent {v : α → B} (hv : ∀ p, IsAnticonsistent (v p)) :
    ∀ φ : Fml α, IsAnticonsistent (φ.eval v)
  | .atom p => hv p
  | .and φ ψ => (eval_isAnticonsistent hv φ).inf (eval_isAnticonsistent hv ψ)
  | .or φ ψ => (eval_isAnticonsistent hv φ).sup (eval_isAnticonsistent hv ψ)
  | .not φ => (eval_isAnticonsistent hv φ).compl

end Conflation

variable [Negation B] [IsInterlaced B]

theorem eval_kLE_eval {v w : α → B} (h : ∀ p, v p ≤ₖ w p) :
    ∀ φ : Fml α, φ.eval v ≤ₖ φ.eval w
  | .atom p => h p
  | .and φ ψ => by
    calc φ.eval v ⊓ ψ.eval v
        ≤ₖ φ.eval w ⊓ ψ.eval v := IsInterlaced.inf_kmono (eval_kLE_eval h φ) _
      _ = ψ.eval v ⊓ φ.eval w := inf_comm ..
      _ ≤ₖ ψ.eval w ⊓ φ.eval w := IsInterlaced.inf_kmono (eval_kLE_eval h ψ) _
      _ = φ.eval w ⊓ ψ.eval w := inf_comm ..
  | .or φ ψ => by
    calc φ.eval v ⊔ ψ.eval v
        ≤ₖ φ.eval w ⊔ ψ.eval v := IsInterlaced.sup_kmono (eval_kLE_eval h φ) _
      _ = ψ.eval v ⊔ φ.eval w := sup_comm ..
      _ ≤ₖ ψ.eval w ⊔ φ.eval w := IsInterlaced.sup_kmono (eval_kLE_eval h ψ) _
      _ = φ.eval w ⊔ ψ.eval w := sup_comm ..
  | .not φ => compl_kLE_compl (eval_kLE_eval h φ)

end Eval

/-! ### Prime bifilters ([fitting-2021] Def 8.6.5, after [arieli-avron-1998]) -/

section Bifilter

variable [Lattice B] [Lattice (Know B)]

/-- A prime bifilter is a proper nonempty subset that is a prime filter for both the truth and the
knowledge lattice operations ([fitting-2021] Def 8.6.5). It generalizes the designated values
`{t, ⊤}` of `FOUR` ([arieli-avron-1996], [arieli-avron-1998]). -/
structure PrimeBifilter (B : Type*) [Lattice B] [Lattice (Know B)] where
  /-- The designated values. -/
  carrier : Set B
  nonempty : carrier.Nonempty
  ne_univ : carrier ≠ Set.univ
  inf_mem_iff {a b : B} : a ⊓ b ∈ carrier ↔ a ∈ carrier ∧ b ∈ carrier
  kInf_mem_iff {a b : B} : (a ⊓ₖ b) ∈ carrier ↔ a ∈ carrier ∧ b ∈ carrier
  sup_mem_iff {a b : B} : a ⊔ b ∈ carrier ↔ a ∈ carrier ∨ b ∈ carrier
  kSup_mem_iff {a b : B} : (a ⊔ₖ b) ∈ carrier ↔ a ∈ carrier ∨ b ∈ carrier

instance : Membership B (PrimeBifilter B) := ⟨fun F a ↦ a ∈ F.carrier⟩

theorem PrimeBifilter.mem_of_kLE (F : PrimeBifilter B) {a b : B} (ha : a ∈ F) (h : a ≤ₖ b) :
    b ∈ F := by
  have hab : a ⊔ₖ b = b :=
    toKnow.injective (by simpa only [toKnow_kSup] using sup_eq_right.mpr h)
  exact hab ▸ F.kSup_mem_iff.mpr (Or.inl ha)

theorem PrimeBifilter.mem_of_le (F : PrimeBifilter B) {a b : B} (ha : a ∈ F) (h : a ≤ b) :
    b ∈ F :=
  sup_eq_right.mpr h ▸ F.sup_mem_iff.mpr (Or.inl ha)

end Bifilter

/-! ### The strict/tolerant and classical logics of a logical bilattice (§8.7) -/

section Logics

variable [Lattice B] [InvolutiveCompl B] [Lattice (Know B)] [Conflation B]

/-- A value is strictly designated when it is designated and exact ([fitting-2021] Def 8.7.1). -/
def StrictlyDesignated (F : PrimeBifilter B) (a : B) : Prop := a ∈ F ∧ IsExact a

/-- A value is tolerantly designated when it is designated and anticonsistent
([fitting-2021] Def 8.7.1). -/
def TolerantlyDesignated (F : PrimeBifilter B) (a : B) : Prop := a ∈ F ∧ IsAnticonsistent a

/-- A valuation satisfies a sequent strict-to-tolerantly when some conclusion is tolerantly
designated whenever every premise is strictly designated. -/
def STSatisfies (F : PrimeBifilter B) (v : α → B) (Γ Δ : List (Fml α)) : Prop :=
  Consequence.Satisfies (fun v φ ↦ StrictlyDesignated F (φ.eval v))
    (fun v φ ↦ TolerantlyDesignated F (φ.eval v)) v Γ Δ

/-- A valuation satisfies a sequent strictly on both sides. -/
def CSatisfies (F : PrimeBifilter B) (v : α → B) (Γ Δ : List (Fml α)) : Prop :=
  Consequence.Satisfies (fun v φ ↦ StrictlyDesignated F (φ.eval v))
    (fun v φ ↦ StrictlyDesignated F (φ.eval v)) v Γ Δ

/-- `ST⟨B, F⟩` validity is the mixed consequence of strict premises and tolerant conclusions over
the valuations into the anticonsistent values ([fitting-2021] Def 8.7.1). -/
def STValid (F : PrimeBifilter B) (Γ Δ : List (Fml α)) : Prop :=
  Consequence.MixedConsequence
    (fun (v : {v : α → B // ∀ p, IsAnticonsistent (v p)}) φ ↦ StrictlyDesignated F (φ.eval v))
    (fun v φ ↦ TolerantlyDesignated F (φ.eval v)) Γ Δ

/-- `C⟨B, F⟩` validity is the consequence of strict premises and strict conclusions over the
valuations into the exact values ([fitting-2021] Def 8.7.1). -/
def CValid (F : PrimeBifilter B) (Γ Δ : List (Fml α)) : Prop :=
  Consequence.MixedConsequence
    (fun (v : {v : α → B // ∀ p, IsExact (v p)}) φ ↦ StrictlyDesignated F (φ.eval v))
    (fun v φ ↦ StrictlyDesignated F (φ.eval v)) Γ Δ

instance {F : PrimeBifilter B} [DecidablePred (· ∈ F)] [DecidablePred (IsExact (B := B))]
    (a : B) : Decidable (StrictlyDesignated F a) :=
  inferInstanceAs (Decidable (_ ∧ _))

instance {F : PrimeBifilter B} [DecidablePred (· ∈ F)]
    [DecidablePred (IsAnticonsistent (B := B))] (a : B) : Decidable (TolerantlyDesignated F a) :=
  inferInstanceAs (Decidable (_ ∧ _))

section Interlaced

variable [Negation B] [IsInterlaced B] [NegConfComm B]

theorem stValid_iff_cValid (F : PrimeBifilter B) (Γ Δ : List (Fml α)) :
    STValid F Γ Δ ↔ CValid F Γ Δ := by
  refine ⟨fun h ↦ h.comap (fun v ↦ ⟨v, fun p ↦ (v.2 p).isAnticonsistent⟩) (fun _ _ _ ↦ id)
    fun v ψ _ hψ ↦ ⟨hψ.1, eval_isExact v.2 ψ⟩, fun h ↦ ?_⟩
  choose e he hle using fun (v : {v : α → B // ∀ p, IsAnticonsistent (v p)}) p ↦
    (v.2 p).exists_exact_kLE
  refine h.comap (fun v ↦ ⟨e v, he v⟩) (fun v φ _ hφ ↦ ?_) fun v ψ _ hψ ↦
    ⟨F.mem_of_kLE hψ.1 (eval_kLE_eval (hle v) ψ), eval_isAnticonsistent v.2 ψ⟩
  rwa [(eval_isExact (he v) φ).eq_of_kLE hφ.2 (eval_kLE_eval (hle v) φ)]

end Interlaced

theorem cut_cSatisfies (F : PrimeBifilter B) {Γ Δ : List (Fml α)} {A : Fml α} {v : α → B}
    (h₁ : CSatisfies F v (A :: Γ) Δ) (h₂ : CSatisfies F v Γ (A :: Δ)) : CSatisfies F v Γ Δ :=
  Consequence.Satisfies.cut id h₁ h₂

variable [BoundedOrder (Know B)]

theorem cut_not_local_stValid (F : PrimeBifilter B) (p : α) (hbt : (⊥ : Know B) ≠ ⊤) :
    ¬ ∀ v : α → B, (∀ q, IsAnticonsistent (v q)) →
      STSatisfies F v [.atom p] [] → STSatisfies F v [] [.atom p] →
      STSatisfies F v ([] : List (Fml α)) [] := by
  intro h
  set kT : B := ofKnow (⊤ : Know B) with hkT
  have hle_top : ∀ x : B, x ≤ₖ kT := fun x ↦ by
    rw [hkT, kLE_def, toKnow_ofKnow]; exact le_top
  have hanti : IsAnticonsistent kT := hle_top _
  have hnexact : ¬ IsExact kT := by
    intro hex
    have h1 := conf_kLE_conf (hle_top (conf (ofKnow (⊥ : Know B))))
    rw [conf_conf, show conf kT = kT from hex] at h1
    rw [hkT, kLE_def, toKnow_ofKnow, toKnow_ofKnow] at h1
    exact hbt (le_antisymm h1 bot_le).symm
  have hmem : kT ∈ F := by
    obtain ⟨a, ha⟩ := F.nonempty
    exact F.mem_of_kLE ha (hle_top a)
  have hfinal := h (fun _ ↦ kT) (fun _ ↦ hanti)
    (fun hΓ ↦ absurd (hΓ _ (List.Mem.head _)).2 hnexact)
    (fun _ ↦ ⟨.atom p, List.Mem.head _, hmem, hanti⟩)
  obtain ⟨ψ, hψ, -⟩ := hfinal (fun φ hφ ↦ nomatch hφ)
  exact nomatch hψ

end Logics

/-! ### Products of De Morgan algebras (§§8.8–8.9) -/

section DeMorgan

variable {L : Type*} [Lattice L]

section ExactIso

variable [BoundedOrder L] [InvolutiveCompl L]

/-- The exact members of `L ⊙ L` are the pairs `⟨a, aᶜ⟩`, and under the truth order they are `L`
([fitting-2021] Prop 8.8.3). -/
def exactIso : {x : L ⊙ L // IsExact x} ≃o L where
  toFun x := x.1.pro
  invFun a := ⟨mk a aᶜ, (Product.isExact_iff _).2 rfl⟩
  left_inv x := Subtype.ext (Product.ext rfl ((Product.isExact_iff _).1 x.2).symm)
  right_inv _ := rfl
  map_rel_iff' {x y} := by
    show x.1.pro ≤ y.1.pro ↔ x ≤ y
    rw [← Subtype.coe_le_coe, le_def, (Product.isExact_iff _).1 x.2,
      (Product.isExact_iff _).1 y.2, InvolutiveCompl.compl_le_compl_iff_le, and_self]

end ExactIso

/-- A prime filter of `L` holds the designated values of a logical De Morgan algebra `⟨L, D⟩`,
nonempty and proper as §8.2 requires ([fitting-2021] Def 8.9.1). -/
structure PrimeFilter (L : Type*) [Lattice L] where
  /-- The designated values. -/
  carrier : Set L
  nonempty : carrier.Nonempty
  ne_univ : carrier ≠ Set.univ
  inf_mem_iff {a b : L} : a ⊓ b ∈ carrier ↔ a ∈ carrier ∧ b ∈ carrier
  sup_mem_iff {a b : L} : a ⊔ b ∈ carrier ↔ a ∈ carrier ∨ b ∈ carrier

instance : Membership L (PrimeFilter L) := ⟨fun D a ↦ a ∈ D.carrier⟩

section Prod

variable [BoundedOrder L]

/-- `D × L` is a prime bifilter of `L ⊙ L` ([fitting-2021] Lemma 8.9.2). -/
def PrimeFilter.prod (D : PrimeFilter L) : PrimeBifilter (L ⊙ L) where
  carrier := {x | x.pro ∈ D}
  nonempty := let ⟨a, ha⟩ := D.nonempty; ⟨Product.mk a ⊥, ha⟩
  ne_univ h := D.ne_univ (Set.eq_univ_of_forall fun a ↦
    (show Product.mk a ⊥ ∈ {x : L ⊙ L | x.pro ∈ D} from h ▸ Set.mem_univ _))
  inf_mem_iff := D.inf_mem_iff
  kInf_mem_iff := D.inf_mem_iff
  sup_mem_iff := D.sup_mem_iff
  kSup_mem_iff := D.sup_mem_iff

theorem PrimeFilter.mem_prod_iff (D : PrimeFilter L) (x : L ⊙ L) : x ∈ D.prod ↔ x.pro ∈ D :=
  Iff.rfl

instance (D : PrimeFilter L) [DecidablePred (· ∈ D)] : DecidablePred (· ∈ D.prod) :=
  fun x ↦ inferInstanceAs (Decidable (x.pro ∈ D))

variable [InvolutiveCompl L]

theorem strictlyDesignated_prod_iff (D : PrimeFilter L) (x : L ⊙ L) :
    StrictlyDesignated D.prod x ↔ x.pro ∈ D ∧ x.con = x.proᶜ :=
  and_congr Iff.rfl (Product.isExact_iff x)

theorem tolerantlyDesignated_prod_iff (D : PrimeFilter L) (x : L ⊙ L) :
    TolerantlyDesignated D.prod x ↔ x.pro ∈ D ∧ x.proᶜ ≤ x.con :=
  and_congr Iff.rfl (Product.isAnticonsistent_iff x)

end Prod

variable [InvolutiveCompl L]

/-- The logic `⟨L, D⟩` evaluates formulas in `L` by meet, join and the De Morgan complement. -/
def Fml.evalL (v : α → L) : Fml α → L
  | atom p => v p
  | and φ ψ => φ.evalL v ⊓ ψ.evalL v
  | or φ ψ => φ.evalL v ⊔ ψ.evalL v
  | not φ => (φ.evalL v)ᶜ

/-- A sequent is valid in the logic `⟨L, D⟩` when designated premises entail a designated
conclusion (§8.2). -/
def LValid (D : PrimeFilter L) (Γ Δ : List (Fml α)) : Prop :=
  Consequence.MixedConsequence (fun v φ ↦ φ.evalL v ∈ D) (fun v φ ↦ φ.evalL v ∈ D) Γ Δ

/-- The exact valuation of `L ⊙ L` a valuation in `L` determines, `p ↦ ⟨v p, (v p)ᶜ⟩`. -/
def exactVal (v : α → L) (p : α) : L ⊙ L := mk (v p) (v p)ᶜ

theorem exactVal_isExact (v : α → L) (p : α) : IsExact (exactVal v p) :=
  (Product.isExact_iff _).2 rfl

theorem eq_exactVal_of_isExact {v : α → L ⊙ L} (hv : ∀ p, IsExact (v p)) :
    v = exactVal fun p ↦ (v p).pro :=
  funext fun p ↦ Product.ext rfl ((Product.isExact_iff _).1 (hv p))

theorem eval_exactVal (v : α → L) : ∀ φ : Fml α, φ.eval (exactVal v) = mk (φ.evalL v) (φ.evalL v)ᶜ
  | .atom _ => rfl
  | .and φ ψ => by
    rw [Fml.eval, Fml.evalL, eval_exactVal v φ, eval_exactVal v ψ, mk_inf_mk,
      InvolutiveCompl.compl_inf]
  | .or φ ψ => by
    rw [Fml.eval, Fml.evalL, eval_exactVal v φ, eval_exactVal v ψ, mk_sup_mk,
      InvolutiveCompl.compl_sup]
  | .not φ => by
    rw [Fml.eval, Fml.evalL, eval_exactVal v φ, mk_compl, InvolutiveCompl.compl_compl]

variable [BoundedOrder L]

theorem cValid_prod_iff (D : PrimeFilter L) (Γ Δ : List (Fml α)) :
    CValid D.prod Γ Δ ↔ LValid D Γ Δ := by
  have hval (v : α → L) (φ : Fml α) : φ.eval (exactVal v) ∈ D.prod ↔ φ.evalL v ∈ D := by
    rw [PrimeFilter.mem_prod_iff, eval_exactVal, pro_mk]
  refine ⟨fun h ↦ h.comap (fun v ↦ ⟨exactVal v, exactVal_isExact v⟩)
      (fun v φ _ hφ ↦ ⟨(hval v φ).2 hφ, eval_isExact (exactVal_isExact v) φ⟩)
      fun v ψ _ hψ ↦ (hval v ψ).1 hψ.1,
    fun h ↦ h.comap (fun v p ↦ (v.1 p).pro) (fun v φ _ hφ ↦ ?_) fun v ψ _ hψ ↦ ?_⟩
  · rw [eq_exactVal_of_isExact v.2] at hφ
    exact (hval _ φ).1 hφ.1
  · rw [eq_exactVal_of_isExact v.2]
    exact ⟨(hval _ ψ).2 hψ, eval_isExact (exactVal_isExact _) ψ⟩

/-! ### Generating strict/tolerant examples (§8.10) -/

theorem stValid_prod_iff (D : PrimeFilter L) (Γ Δ : List (Fml α)) :
    STValid D.prod Γ Δ ↔ LValid D Γ Δ :=
  (stValid_iff_cValid _ _ _).trans (cValid_prod_iff D Γ Δ)

theorem cut_not_local_prod [Nontrivial L] (D : PrimeFilter L) (p : α) :
    ¬ ∀ v : α → L ⊙ L, (∀ q, IsAnticonsistent (v q)) →
      STSatisfies D.prod v [.atom p] [] → STSatisfies D.prod v [] [.atom p] →
      STSatisfies D.prod v ([] : List (Fml α)) [] :=
  cut_not_local_stValid D.prod p fun h ↦
    bot_ne_top (congrArg (fun k : Know (L ⊙ L) ↦ (ofKnow k).pro) h)

end DeMorgan

/-! ### Examples 8.10.2–8.10.5: classical logic, `K3`, `LP` and `FDE` -/

section Examples

/-- Classical logic is the logical De Morgan algebra `Bool` with `{true}` designated. -/
def classicalFilter : PrimeFilter Bool where
  carrier := {b | b = true}
  nonempty := ⟨true, rfl⟩
  ne_univ h := absurd (h ▸ Set.mem_univ false) (by decide)
  inf_mem_iff {a b} := by revert a b; decide
  sup_mem_iff {a b} := by revert a b; decide

instance : DecidablePred (· ∈ classicalFilter) := fun b ↦ inferInstanceAs (Decidable (b = true))

/-- The designated values `{t, ⊤}` of `FOUR` ([fitting-2021] Example 8.7.4) are `{true} × Bool`
([fitting-2021] Example 8.10.2). -/
abbrev fourBifilter : PrimeBifilter FOUR := classicalFilter.prod

theorem mem_fourBifilter_iff : ∀ x : FOUR, x ∈ fourBifilter ↔ x = FOUR.T ∨ x = FOUR.I := by
  decide

/-- `FOUR`'s exact values are the classical `{F, T}` ([fitting-2021] Example 8.7.4). -/
theorem four_isExact_iff : ∀ x : FOUR, IsExact x ↔ x = FOUR.F ∨ x = FOUR.T := by decide

/-- `FOUR`'s anticonsistent values are `{F, T, I}`, the value space of `LP`
([fitting-2021] Example 8.7.4). -/
theorem four_isAnticonsistent_iff :
    ∀ x : FOUR, IsAnticonsistent x ↔ x = FOUR.F ∨ x = FOUR.T ∨ x = FOUR.I := by
  decide

/-- `ST` and classical logic validate the same sequents, the original collapse of
[cobreros-etal-2012] (via [fitting-2021] Example 8.7.4). -/
theorem four_stValid_iff_cValid {α : Type*} (Γ Δ : List (Fml α)) :
    STValid fourBifilter Γ Δ ↔ CValid fourBifilter Γ Δ :=
  stValid_iff_cValid fourBifilter Γ Δ

theorem four_cut_not_local {α : Type*} (p : α) :
    ¬ ∀ v : α → FOUR, (∀ q, IsAnticonsistent (v q)) →
      STSatisfies fourBifilter v [.atom p] [] → STSatisfies fourBifilter v [] [.atom p] →
      STSatisfies fourBifilter v ([] : List (Fml α)) [] :=
  cut_not_local_prod classicalFilter p

/-- `K3`, Kleene's strong three-valued logic, is `SignType` with `{1}` designated
([fitting-2021] Example 8.10.3). -/
def k3Filter : PrimeFilter SignType where
  carrier := {a | a = 1}
  nonempty := ⟨1, rfl⟩
  ne_univ h := absurd (h ▸ Set.mem_univ (-1)) (by decide)
  inf_mem_iff {a b} := by revert a b; decide
  sup_mem_iff {a b} := by revert a b; decide

instance : DecidablePred (· ∈ k3Filter) := fun a ↦ inferInstanceAs (Decidable (a = 1))

/-- `LP`, the logic of paradox of [priest-1979], is `SignType` with `{0, 1}` (Fitting's `{½, 1}`)
designated ([fitting-2021] Example 8.10.4). -/
def lpFilter : PrimeFilter SignType where
  carrier := {a | a ≠ -1}
  nonempty := ⟨1, by decide⟩
  ne_univ h := absurd (h ▸ Set.mem_univ (-1)) (by decide)
  inf_mem_iff {a b} := by revert a b; decide
  sup_mem_iff {a b} := by revert a b; decide

instance : DecidablePred (· ∈ lpFilter) := fun a ↦ inferInstanceAs (Decidable (a ≠ -1))

/-- The bilattice `NINE = SignType ⊙ SignType` of Figure 4 ([fitting-2021] Example 8.10.3). -/
abbrev NINE := SignType ⊙ SignType

/-- `NINE`'s exact values are `{f, d⊤, t}` ([fitting-2021] §8.5). -/
theorem nine_isExact_iff : ∀ x : NINE,
    IsExact x ↔ x = mk (-1) 1 ∨ x = mk 0 0 ∨ x = mk 1 (-1) := by
  decide

/-- `NINE`'s consistent values are the exact ones with `{df, ⊥, dt}` ([fitting-2021] §8.5). -/
theorem nine_isConsistent_iff : ∀ x : NINE, IsConsistent x ↔ IsExact x ∨
    x = mk (-1) 0 ∨ x = mk (-1) (-1) ∨ x = mk 0 (-1) := by
  decide

/-- `NINE`'s anticonsistent values are the exact ones with `{of, ⊤, ot}`
([fitting-2021] §8.5). -/
theorem nine_isAnticonsistent_iff : ∀ x : NINE, IsAnticonsistent x ↔ IsExact x ∨
    x = mk 0 1 ∨ x = mk 1 1 ∨ x = mk 1 0 := by
  decide

/-- The two prime bifilters of `NINE` come from `K3` and `LP` ([fitting-2021] Examples 8.7.5 and
8.10.4). -/
theorem nine_bifilters : (∀ x : NINE, x ∈ k3Filter.prod ↔
      x = mk 1 (-1) ∨ x = mk 1 0 ∨ x = mk 1 1) ∧
    ∀ x : NINE, x ∈ lpFilter.prod ↔ x = mk 0 (-1) ∨ x = mk 1 (-1) ∨
      x = mk 0 0 ∨ x = mk 1 0 ∨ x = mk 0 1 ∨ x = mk 1 1 := by
  decide

/-- With `K3` the strictly designated values reduce to `{t}`, so `C⟨NINE, {1} × K3⟩` is `K3`
([fitting-2021] Example 8.7.5). -/
theorem k3_strict_iff : ∀ x : NINE, StrictlyDesignated k3Filter.prod x ↔ x = mk 1 (-1) := by
  decide

/-- With `LP` the strictly designated values are `{d⊤, t}` and the tolerantly designated ones
`{t, d⊤, ot, of, ⊤}` ([fitting-2021] Example 8.10.4). -/
theorem lp_designated : (∀ x : NINE, StrictlyDesignated lpFilter.prod x ↔
      x = mk 0 0 ∨ x = mk 1 (-1)) ∧
    ∀ x : NINE, TolerantlyDesignated lpFilter.prod x ↔ x = mk 1 (-1) ∨
      x = mk 0 0 ∨ x = mk 1 0 ∨ x = mk 0 1 ∨ x = mk 1 1 := by
  decide

/-- `P, ¬P ⇒ Q` fails in strict/tolerant `LP` as in `LP`, with countermodel `v(P) = d⊤` and
`v(Q) = f` ([fitting-2021] Example 8.10.4). -/
theorem lp_explosion_fails :
    ¬ STValid lpFilter.prod [.atom true, .not (.atom true)] [.atom false] := fun h ↦
  absurd (h ⟨fun b ↦ if b then mk 0 0 else mk (-1) 1, by decide⟩ (by decide))
    (by decide)

/-- `FDE` is the logical De Morgan algebra `FOUR` under the truth order with `{t, ⊤}` designated
([fitting-2021] Example 8.10.5). -/
def fdeFilter : PrimeFilter FOUR where
  carrier := {x | x = FOUR.T ∨ x = FOUR.I}
  nonempty := ⟨FOUR.T, Or.inl rfl⟩
  ne_univ h := absurd (h ▸ Set.mem_univ FOUR.U) (by decide)
  inf_mem_iff {a b} := by revert a b; decide
  sup_mem_iff {a b} := by revert a b; decide

instance : DecidablePred (· ∈ fdeFilter) :=
  fun x ↦ inferInstanceAs (Decidable (x = FOUR.T ∨ x = FOUR.I))

/-- The bilattice `SIXTEEN = FOUR ⊙ FOUR` of Figure 6 ([fitting-2021] Example 8.10.5). -/
abbrev SIXTEEN := FOUR ⊙ FOUR

/-- `FDE`'s strict/tolerant counterpart validates exactly the sequents of `FDE`
([fitting-2021] Example 8.10.5). -/
theorem fde_stValid_iff {α : Type*} (Γ Δ : List (Fml α)) :
    STValid fdeFilter.prod Γ Δ ↔ LValid fdeFilter Γ Δ :=
  stValid_prod_iff fdeFilter Γ Δ

/-- Not every value is exact, consistent or anticonsistent, since `⟨⊥, ⊤⟩` and `⟨⊤, ⊥⟩` of
`SIXTEEN` are neither consistent nor anticonsistent ([fitting-2021] §8.5, Example 8.10.5). -/
theorem sixteen_neither :
    ¬ IsConsistent (mk FOUR.U FOUR.I : SIXTEEN) ∧
      ¬ IsAnticonsistent (mk FOUR.U FOUR.I : SIXTEEN) ∧
      ¬ IsConsistent (mk FOUR.I FOUR.U : SIXTEEN) ∧
      ¬ IsAnticonsistent (mk FOUR.I FOUR.U : SIXTEEN) := by
  simp only [Product.isConsistent_iff, Product.isAnticonsistent_iff]
  decide

end Examples

end Fitting2021
