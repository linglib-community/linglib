module

public import Linglib.Logic.Bilattice.Representation
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

The examples come from products `L ⊙ L` of De Morgan algebras. The exact values of an interlaced
bilattice with conflation are the first factor of its representation as a product (Lemma 8.8.2,
`exactIsoIci`), so those of `L ⊙ L` are `L` (Proposition 8.8.3, `exactIso`). `D × L` is a prime
bifilter for every prime filter `D` (Lemma 8.9.2, `PrimeFilter.prod`), and `C⟨L ⊙ L, D × L⟩` is
the logic `⟨L, D⟩` itself (Proposition 8.9.3, `cValid_prod_iff`). Hence every logical De Morgan
algebra has a strict/tolerant counterpart with the same consequence relation (Proposition 8.10.1,
`stValid_prod_iff`): classical logic from `Bool`, `K3` and `LP` from `Trivalent`, and `FDE` from
`FOUR` (Examples 8.10.2–8.10.5).

## Implementation notes

* Formulas have conjunction, disjunction and negation only (Definition 8.6.1); prime bifilters and
  prime filters carry the nonemptiness and properness that §8.2 requires of designated sets.
* Sequent satisfaction is `Consequence.Satisfies`, with strict and tolerant designation as the
  premise and conclusion standards, so local cut in `C⟨B, F⟩` is `Consequence.Satisfies.cut`.
  `STValid` and `CValid` are `Consequence.MixedConsequence` over the anticonsistent and exact
  valuations and `LValid` over all valuations into `L`, so Propositions 8.7.2 and 8.9.3 are pairs
  of model correspondences (`Consequence.MixedConsequence.comap`).
* Lemma 8.8.2 assumes a negation that its proof never uses, so `exactIsoIci` drops it. Its six
  items are the inverse laws and the monotonicity of one order isomorphism.

## References

* [fitting-2021]
* [avron-1996]
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

variable [InvolutiveCompl (Know B)] [Conflation B] [NegConfComm B]

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
  | .and φ ψ => inf_kLE_inf (eval_kLE_eval h φ) (eval_kLE_eval h ψ)
  | .or φ ψ => sup_kLE_sup (eval_kLE_eval h φ) (eval_kLE_eval h ψ)
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

variable [Lattice B] [InvolutiveCompl B] [Lattice (Know B)] [InvolutiveCompl (Know B)]

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

variable [Conflation B] [Negation B] [IsInterlaced B] [NegConfComm B]

theorem stValid_iff_cValid (F : PrimeBifilter B) (Γ Δ : List (Fml α)) :
    STValid F Γ Δ ↔ CValid F Γ Δ := by
  refine ⟨fun h ↦ h.comap (fun v ↦ ⟨v, fun p ↦ (v.2 p).isAnticonsistent⟩) (fun _ _ _ ↦ id)
    fun v ψ _ hψ ↦ ⟨hψ.1, eval_isExact v.2 ψ⟩, fun h ↦ ?_⟩
  have hle (v : {v : α → B // ∀ p, IsAnticonsistent (v p)}) p := (v.2 p).inf_conf_kLE
  refine h.comap (fun v ↦ ⟨fun p ↦ v.1 p ⊓ conf (v.1 p), fun p ↦ isExact_inf_conf _⟩)
    (fun v φ _ hφ ↦ ?_) fun v ψ _ hψ ↦
    ⟨F.mem_of_kLE hψ.1 (eval_kLE_eval (hle v) ψ), eval_isAnticonsistent v.2 ψ⟩
  rwa [(eval_isExact (fun _ ↦ isExact_inf_conf _) φ).eq_of_kLE hφ.2 (eval_kLE_eval (hle v) φ)]

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
  have hle_top : ∀ x : B, x ≤ₖ kT := fun _ ↦ le_top (α := Know B)
  have hanti : IsAnticonsistent kT := hle_top _
  have hnexact : ¬ IsExact kT := hkT ▸ not_isExact_ofKnow_top hbt
  have hmem : kT ∈ F := by
    obtain ⟨a, ha⟩ := F.nonempty
    exact F.mem_of_kLE ha (hle_top a)
  have hfinal := h (fun _ ↦ kT) (fun _ ↦ hanti)
    (fun hΓ ↦ absurd (hΓ _ (List.Mem.head _)).2 hnexact)
    (fun _ ↦ ⟨.atom p, List.Mem.head _, hmem, hanti⟩)
  obtain ⟨ψ, hψ, -⟩ := hfinal (fun φ hφ ↦ nomatch hφ)
  exact nomatch hψ

end Logics

/-! ### The exact values and the representation (§8.8) -/

section Exact

variable [Lattice B] [BoundedOrder B] [Lattice (Know B)] [BoundedOrder (Know B)] [IsInterlaced B]
  [InvolutiveCompl (Know B)] [Conflation B]

/-- In an interlaced bilattice with conflation, `x ↦ x ∨ ⊥` maps the exact values isomorphically
onto `L_B`, the first factor of the representation, with inverse `y ↦ y ∧ −y`
([fitting-2021] Lemma 8.8.2 and the proof of Prop 8.8.3). -/
def exactIsoIci : {x : B // IsExact x} ≃o Set.Ici (ofKnow ⊥ : B) :=
  Equiv.toOrderIso
    { toFun x := ⟨x.1 ⊔ ofKnow ⊥, le_sup_right⟩
      invFun y := ⟨y.1 ⊓ conf y.1, isExact_inf_conf y.1⟩
      left_inv x := Subtype.ext <| by
        dsimp only
        rw [conf_sup, x.2.eq, conf_ofKnow_bot, sup_ofKnow_bot_inf_sup_ofKnow_top]
      right_inv y := Subtype.ext <| by
        have h : conf y.1 ⊔ ofKnow ⊥ = ⊤ := top_le_iff.1 <|
          (ofKnow_top_sup_ofKnow_bot (B := B)).symm.trans_le <| sup_le_sup_right
            ((conf_ofKnow_bot (B := B)).symm.trans_le (conf_le_conf y.2)) _
        dsimp only
        rw [inf_sup_ofKnow_bot, sup_eq_left.2 y.2, h, inf_top_eq] }
    (fun _ _ h ↦ sup_le_sup_right h _)
    fun _ _ h ↦ inf_le_inf h (conf_le_conf h)

end Exact

/-! ### Products of De Morgan algebras (§§8.8–8.9) -/

section DeMorgan

variable {L : Type*} [Lattice L]

section ExactIso

variable [BoundedOrder L] [InvolutiveCompl L]

/-- Under the truth order the exact members of `L ⊙ L` are `L` ([fitting-2021] Prop 8.8.3): they
are its `L_B` by Lemma 8.8.2, and the `L_B` of a product is its first factor. -/
def exactIso : {x : L ⊙ L // IsExact x} ≃o L := exactIsoIci.trans Product.iciIso

@[simp] theorem exactIso_apply (x : {x : L ⊙ L // IsExact x}) : exactIso x = x.1.pro :=
  sup_bot_eq _

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
noncomputable abbrev fourBifilter : PrimeBifilter FOUR := classicalFilter.prod

theorem mem_fourBifilter_iff : ∀ x : FOUR, x ∈ fourBifilter ↔ x = FOUR.T ∨ x = FOUR.I := by
  decide

-- Example 8.7.4 [fitting-2021]
theorem four_isExact_iff : ∀ x : FOUR, IsExact x ↔ x = FOUR.F ∨ x = FOUR.T := by decide

-- Example 8.7.4 [fitting-2021]
theorem four_isAnticonsistent_iff :
    ∀ x : FOUR, IsAnticonsistent x ↔ x = FOUR.F ∨ x = FOUR.T ∨ x = FOUR.I := by
  decide

-- Example 8.7.4 [cobreros-etal-2012] [fitting-2021]
theorem four_stValid_iff_cValid {α : Type*} (Γ Δ : List (Fml α)) :
    STValid fourBifilter Γ Δ ↔ CValid fourBifilter Γ Δ :=
  stValid_iff_cValid fourBifilter Γ Δ

theorem four_cut_not_local {α : Type*} (p : α) :
    ¬ ∀ v : α → FOUR, (∀ q, IsAnticonsistent (v q)) →
      STSatisfies fourBifilter v [.atom p] [] → STSatisfies fourBifilter v [] [.atom p] →
      STSatisfies fourBifilter v ([] : List (Fml α)) [] :=
  cut_not_local_prod classicalFilter p

/-- `K3`, Kleene's strong three-valued logic, is `Trivalent` with `{true}` designated
([fitting-2021] Example 8.10.3). -/
def k3Filter : PrimeFilter Trivalent where
  carrier := {a | a = .true}
  nonempty := ⟨.true, rfl⟩
  ne_univ h := absurd (h ▸ Set.mem_univ Trivalent.false) (by decide)
  inf_mem_iff {a b} := by revert a b; decide
  sup_mem_iff {a b} := by revert a b; decide

instance : DecidablePred (· ∈ k3Filter) := fun a ↦ inferInstanceAs (Decidable (a = .true))

/-- `LP`, the logic of paradox of [priest-1979], is `Trivalent` with `{undefined, true}`
(Fitting's `{½, 1}`) designated ([fitting-2021] Example 8.10.4). -/
def lpFilter : PrimeFilter Trivalent where
  carrier := {a | a ≠ .false}
  nonempty := ⟨.true, by decide⟩
  ne_univ h := absurd (h ▸ Set.mem_univ Trivalent.false) (by decide)
  inf_mem_iff {a b} := by revert a b; decide
  sup_mem_iff {a b} := by revert a b; decide

instance : DecidablePred (· ∈ lpFilter) := fun a ↦ inferInstanceAs (Decidable (a ≠ .false))

/-- The bilattice `NINE = Trivalent ⊙ Trivalent` of Figure 4 ([fitting-2021] Example 8.10.3). -/
abbrev NINE := Trivalent ⊙ Trivalent

-- §8.5 [fitting-2021]
theorem nine_isExact_iff : ∀ x : NINE,
    IsExact x ↔ x = mk .false .true ∨ x = mk .undefined .undefined ∨ x = mk .true .false := by
  decide

-- §8.5 [fitting-2021]
theorem nine_isConsistent_iff : ∀ x : NINE, IsConsistent x ↔ IsExact x ∨
    x = mk .false .undefined ∨ x = mk .false .false ∨ x = mk .undefined .false := by
  decide

-- §8.5 [fitting-2021]
theorem nine_isAnticonsistent_iff : ∀ x : NINE, IsAnticonsistent x ↔ IsExact x ∨
    x = mk .undefined .true ∨ x = mk .true .true ∨ x = mk .true .undefined := by
  decide

-- Examples 8.7.5 and 8.10.4 [fitting-2021]
theorem nine_bifilters : (∀ x : NINE, x ∈ k3Filter.prod ↔
      x = mk .true .false ∨ x = mk .true .undefined ∨ x = mk .true .true) ∧
    ∀ x : NINE, x ∈ lpFilter.prod ↔ x = mk .undefined .false ∨ x = mk .true .false ∨
      x = mk .undefined .undefined ∨ x = mk .true .undefined ∨ x = mk .undefined .true ∨
      x = mk .true .true := by
  decide

-- Example 8.7.5 [fitting-2021]
theorem k3_strict_iff :
    ∀ x : NINE, StrictlyDesignated k3Filter.prod x ↔ x = mk .true .false := by
  decide

-- Example 8.10.4 [fitting-2021]
theorem lp_designated : (∀ x : NINE, StrictlyDesignated lpFilter.prod x ↔
      x = mk .undefined .undefined ∨ x = mk .true .false) ∧
    ∀ x : NINE, TolerantlyDesignated lpFilter.prod x ↔ x = mk .true .false ∨
      x = mk .undefined .undefined ∨ x = mk .true .undefined ∨ x = mk .undefined .true ∨
      x = mk .true .true := by
  decide

-- Example 8.10.4 [fitting-2021]
theorem lp_explosion_fails :
    ¬ STValid lpFilter.prod [.atom true, .not (.atom true)] [.atom false] := fun h ↦
  absurd (h ⟨fun b ↦ if b then mk .undefined .undefined else mk .false .true, by decide⟩
    (by decide)) (by decide)

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

-- Example 8.10.5 [fitting-2021]
theorem fde_stValid_iff {α : Type*} (Γ Δ : List (Fml α)) :
    STValid fdeFilter.prod Γ Δ ↔ LValid fdeFilter Γ Δ :=
  stValid_prod_iff fdeFilter Γ Δ

-- §8.5, Example 8.10.5 [fitting-2021]
theorem sixteen_neither :
    ¬ IsConsistent (mk FOUR.U FOUR.I : SIXTEEN) ∧
      ¬ IsAnticonsistent (mk FOUR.U FOUR.I : SIXTEEN) ∧
      ¬ IsConsistent (mk FOUR.I FOUR.U : SIXTEEN) ∧
      ¬ IsAnticonsistent (mk FOUR.I FOUR.U : SIXTEEN) := by
  simp only [Product.isConsistent_iff, Product.isAnticonsistent_iff]
  decide

end Examples

end Fitting2021
