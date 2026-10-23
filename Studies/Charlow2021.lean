module

public import Linglib.Semantics.Composition.Writer
public import Linglib.Semantics.Dynamic.RegisterStructure
public import Linglib.Semantics.Mereology
public import Mathlib.Control.Monad.Cont
public import Mathlib.Tactic.DeriveFintype

/-!
# Charlow (2021): Post-suppositions and semantic theory

*Exactly three boys saw exactly five movies* has a cumulative reading: the boys who saw movies are
three, and the movies they saw are five. Charlow shows that the obvious pointwise dynamic meaning
for modified numerals derives only a weaker pseudo-cumulative reading, which is also true when four
boys saw six movies, and compares three repairs: higher-order dynamic quantifiers whose cardinality
tests take scope on their own, made safe by a subtyping discipline; Brasoveanu's post-suppositions,
packaged as a Writer monad; and an update semantics whose maximization surveys whole contexts. The
update semantics derives the cumulative reading from meanings of the pseudo-cumulative form.

## Main definitions

* `Evar`, `card`, `relTest`: dref introduction (17), the cardinality test (19) and a dynamic verb
  (11); maximization (18) is `Update.maxAt`.
* `pseudoCumulative`, `cumulative`: the logical forms (5) and (6).
* `exactly`, `exactlyHO`: the dynamic quantifier (3) and the higher-order one (24), in mathlib's
  continuation monad.
* `HasType`: the typing (44) of logical forms, with `t` a subtype of `T`.
* `PostSupp`, `exactlyPS`, `sentencePS`: post-suppositional meanings (53) and the sentence (55).
* `maxAtU`, `exactlyU`, `sentenceU`: update-theoretic maximization (78), the quantifier (81) and
  the sentence (82).

## Main results

* `cumulative_scenarioA`, `cumulative_scenarioB`, `pseudoCumulative_scenarioB`: on the models of
  Figure 1, (6) holds in Scenario A only, while (5) holds in Scenario B.
* `scope27` through `scope33`: the six scopings of two higher-order quantifiers reduce to (27)–(30)
  and (32)–(33); four agree with (6) on Figure 1 and two are pseudo-cumulative.
* `hasType_cumulative`, `not_hasType_pseudoCumulative`: (45) has type `T` and (46) has none.
* `reify_sentencePS`: the post-suppositional sentence reifies to (6).
* `lower_maxAtU_image`: the two maximizations are alphabetic variants (79).
* `sentenceU_scenarioA`, `sentenceU_scenarioB`: (82) is cumulative on Figure 1, and
  `down_sentenceULowered` recovers (5) once the object's maximization is lifted from its pointwise
  counterpart, so that update-theoretic maximization is not distributive
  (`not_isDistributive_maxAtU`).

## Implementation notes

* Registers model the paper's variables, and entities are finite sets of atoms, as in §2.1.
* A dynamic quantifier of type `(e → t) → t` is `Cont (Update S) R`; a higher-order one is
  `Cont (Update S) (Cont (Update S) R)`, and (26) is the monad's `joinM`.
* The numerals are parameters. The cardinality test counts atoms (`Mereology.atomCount`).
* Contexts of the update semantics are sets of assignments, and truth at an assignment is a
  nonempty update of its singleton (`CCP.down`).
* The distributivity operators (48), (59) and (85), islands (§5.2) and §7 are not formalized, nor
  the subtyping of towers (40)–(41) beyond the typing of logical forms.

## References

* [charlow-2021]
* [brasoveanu-2013]
-/

@[expose] public section

namespace Charlow2021

open DynamicSemantics DynamicSemantics.Update SetRel RegisterStructure
open scoped DynamicSemantics.Update

/-! ### Pointwise dynamic meanings (§2) -/

section Pointwise

variable {R S E : Type*} [RegisterStructure R S E]

/-- `Evar v P` stores in `v` some entity satisfying `P` (17). -/
def Evar (v : R) (P : E → Prop) : Update S := box {v} {i | P (val v i)}

theorem mem_Evar {v : R} {P : E → Prop} {i j : S} :
    i ~[Evar v P] j ↔ ∃ x, P x ∧ j = extend i v x := by
  simp only [Evar, mem_box_singleton, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨x, rfl⟩, hP⟩
    exact ⟨x, by rwa [val_extend_self] at hP, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, rfl⟩, by rwa [val_extend_self]⟩

theorem fixes_Evar {v r : R} (h : r ≠ v) (P : E → Prop) : Fixes r (Evar (S := S) v P) :=
  fixes_box (by simpa using h) _

/-- `relTest u v r` is the dynamic verb that tests `r` of the values of `u` and `v` (11). -/
def relTest (u v : R) (r : E → E → Prop) : Update S := test {i | r (val u i) (val v i)}

variable [PartialOrder E]

theorem mem_maxAt_Evar_comp_test {u : R} {Q : E → Prop} {C : Condition S} {i j : S} :
    i ~[maxAt u (Evar u Q ○ test C)] j ↔
      ∃ y, j = extend i u y ∧ Maximal (fun y ↦ Q y ∧ extend i u y ∈ C) y := by
  simp only [maxAt, maxBy, Set.mem_ofPred_eq, mem_comp_test, mem_Evar]
  constructor
  · rintro ⟨⟨⟨y, hy, rfl⟩, hC⟩, hmax⟩
    refine ⟨y, rfl, maximal_iff_forall_gt.2 ⟨⟨hy, hC⟩, fun y' hlt ⟨hy', hC'⟩ ↦ ?_⟩⟩
    exact hmax _ ⟨⟨y', hy', rfl⟩, hC'⟩ (by simpa [val_extend_self] using hlt)
  · rintro ⟨y, rfl, hm⟩
    refine ⟨⟨⟨y, hm.prop.1, rfl⟩, hm.prop.2⟩, ?_⟩
    rintro k ⟨⟨y', hy', rfl⟩, hC'⟩ hlt
    rw [val_extend_self, val_extend_self] at hlt
    exact (maximal_iff_forall_gt.1 hm).2 hlt ⟨hy', hC'⟩

theorem mem_maxAt_Evar_comp {v : R} {P Q : E → Prop} {D : Update S} (hD : Fixes v D) {i j : S}
    (hQ : ∀ x, P x → ((∃ k, extend i v x ~[D] k) ↔ Q x)) :
    i ~[maxAt v (Evar v P ○ D)] j ↔
      extend i v (val v j) ~[D] j ∧ Maximal (fun x ↦ P x ∧ Q x) (val v j) := by
  have key : ∀ k, i ~[Evar v P ○ D] k ↔ P (val v k) ∧ extend i v (val v k) ~[D] k := by
    intro k
    simp only [SetRel.mem_comp, mem_Evar]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, hk⟩
      rw [hD _ _ hk, val_extend_self]
      exact ⟨hx, hk⟩
    · rintro ⟨hx, hk⟩
      exact ⟨_, ⟨_, hx, rfl⟩, hk⟩
  simp only [maxAt, maxBy, Set.mem_ofPred_eq, key]
  constructor
  · rintro ⟨⟨hP, hj⟩, hmax⟩
    refine ⟨hj, maximal_iff_forall_gt.2 ⟨⟨hP, (hQ _ hP).1 ⟨_, hj⟩⟩, fun x hlt ⟨hx, hQx⟩ ↦ ?_⟩⟩
    obtain ⟨k, hk⟩ := (hQ x hx).2 hQx
    have hkv : val v k = x := (hD _ _ hk).trans (val_extend_self ..)
    exact hmax k ⟨hkv ▸ hx, hkv ▸ hk⟩ (hkv ▸ hlt)
  · rintro ⟨hj, hm⟩
    refine ⟨⟨hm.prop.1, hj⟩, fun k ⟨hP, hk⟩ hlt ↦ ?_⟩
    exact (maximal_iff_forall_gt.1 hm).2 hlt ⟨hP, (hQ _ hP).1 ⟨k, hk⟩⟩

/-- `card v n` tests that the value of `v` has `n` atoms (19). -/
def card (v : R) (n : ℕ) : Update S := test {i | Mereology.atomCount E (val v i) = n}

theorem mem_comp_card {D : Update S} {v : R} {n : ℕ} {i j : S} :
    i ~[D ○ card v n] j ↔ i ~[D] j ∧ Mereology.atomCount E (val v j) = n :=
  mem_comp_test

/-- Cardinality tests commute, so the order of the tests in (6) and (8) is immaterial (fn. 4). -/
theorem card_comp_card_comm (v u : R) (n m : ℕ) :
    (card v n ○ card u m : Update S) = card u m ○ card v n := by
  simp only [card, test_comp_test, Set.inter_comm]

/-- `pseudoCumulative` is the logical form (5), whose object's cardinality test is trapped under
the subject's maximization. -/
def pseudoCumulative (v u : R) (P Q : E → Prop) (r : E → E → Prop) (n m : ℕ) : Update S :=
  maxAt v (Evar v P ○ (maxAt u (Evar u Q ○ relTest u v r) ○ card u m)) ○ card v n

/-- `cumulative` is the logical form (6), with both cardinality tests outside both maximizations.
-/
def cumulative (v u : R) (P Q : E → Prop) (r : E → E → Prop) (n m : ℕ) : Update S :=
  maxAt v (Evar v P ○ maxAt u (Evar u Q ○ relTest u v r)) ○ card u m ○ card v n

end Pointwise

/-! ### Higher-order dynamic quantifiers (§3) -/

section Tower

universe u

variable {R S : Type u} {E : Type*} [RegisterStructure R S E] [PartialOrder E]

/-- `exactly v n P` is the dynamic quantifier (3), which introduces, maximizes and counts in one
scope. -/
def exactly (v : R) (n : ℕ) (P : E → Prop) : Cont (Update S) R :=
  fun k ↦ maxAt v (Evar v P ○ k v) ○ card v n

/-- `exactlyHO v n P` is the higher-order dynamic quantifier (24), whose cardinality test scopes
above its trace. -/
def exactlyHO (v : R) (n : ℕ) (P : E → Prop) : Cont (Update S) (Cont (Update S) R) :=
  fun c ↦ c (fun k ↦ maxAt v (Evar v P ○ k v)) ○ card v n

/-- The map (26) from higher-order to ordinary quantifiers is the continuation monad's `joinM`, and
sends both the Lift (23) of (3) and (24) to (3). -/
theorem joinM_exactlyHO (v : R) (n : ℕ) (P : E → Prop) :
    joinM (exactlyHO (S := S) v n P) = exactly v n P := rfl

theorem joinM_pure_exactly (v : R) (n : ℕ) (P : E → Prop) :
    joinM (pure (exactly (S := S) v n P) : Cont (Update S) (Cont (Update S) R)) = exactly v n P :=
  rfl

variable (v u : R) (P Q : E → Prop) (r : E → E → Prop) (n m : ℕ)

/-- The scoping (27) is the cumulative logical form (6). -/
theorem scope27 :
    exactlyHO v n P (fun V ↦ exactlyHO u m Q fun U ↦ V fun a ↦ U fun b ↦ relTest b a r) =
      (cumulative v u P Q r n m : Update S) := rfl

/-- The scoping (28) reverses the traces, and is (6) with the object's maximization outside. -/
theorem scope28 :
    exactlyHO v n P (fun V ↦ exactlyHO u m Q fun U ↦ U fun b ↦ V fun a ↦ relTest b a r) =
      (cumulative u v Q P (flip r) m n : Update S) := by
  simp only [exactlyHO, cumulative, relTest, flip, SetRel.comp_assoc, card_comp_card_comm v u]

/-- The scoping (29) reverses the quantifiers, which only reorders the tests of (27). -/
theorem scope29 :
    exactlyHO u m Q (fun U ↦ exactlyHO v n P fun V ↦ V fun a ↦ U fun b ↦ relTest b a r) =
      (cumulative v u P Q r n m : Update S) := by
  simp only [exactlyHO, cumulative, SetRel.comp_assoc, card_comp_card_comm u v]

/-- The scoping (30) reverses both. -/
theorem scope30 :
    exactlyHO u m Q (fun U ↦ exactlyHO v n P fun V ↦ U fun b ↦ V fun a ↦ relTest b a r) =
      (cumulative u v Q P (flip r) m n : Update S) := rfl

/-- The scoping (32) puts the object under the subject's trace, giving the pseudo-cumulative (5).
-/
theorem scope32 :
    exactlyHO v n P (fun V ↦ V fun a ↦ exactlyHO u m Q fun U ↦ U fun b ↦ relTest b a r) =
      (pseudoCumulative v u P Q r n m : Update S) := rfl

/-- The scoping (33) puts the subject under the object's trace. -/
theorem scope33 :
    exactlyHO u m Q (fun U ↦ U fun b ↦ exactlyHO v n P fun V ↦ V fun a ↦ relTest b a r) =
      (pseudoCumulative u v Q P (flip r) m n : Update S) := rfl

end Tower

/-! ### Subtyping (§4.2) -/

section Typing

variable {R E : Type*}

/-- `LF R E` is the syntax of logical forms built from the operators typed in (44). -/
inductive LF (R E : Type*)
  | dref (v : R) (P : E → Prop)
  | max (v : R) (K : LF R E)
  | card (v : R) (n : ℕ)
  | rel (u v : R) (r : E → E → Prop)
  | seq (K L : LF R E)

/-- `Ty` has the types of possibly incomplete (`t`) and definitely complete (`T`) sentences (39).
-/
inductive Ty
  | t
  | T

/-- `HasType K A` is the typing (44), under which dref introduction and verbs are `t`, cardinality
tests are `T`, maximization takes and returns `t`, and dynamic conjunction is polymorphic, with `t`
a subtype of `T` (39). -/
inductive HasType : LF R E → Ty → Prop
  | dref (v : R) (P : E → Prop) : HasType (.dref v P) .t
  | rel (u v : R) (r : E → E → Prop) : HasType (.rel u v r) .t
  | card (v : R) (n : ℕ) : HasType (.card v n) .T
  | max (v : R) {K : LF R E} : HasType K .t → HasType (.max v K) .t
  | seq {K L : LF R E} {A : Ty} : HasType K A → HasType L A → HasType (.seq K L) A
  | sub {K : LF R E} : HasType K .t → HasType K .T

theorem HasType.of_max {v : R} {K : LF R E} {A : Ty} (h : HasType (.max v K) A) :
    HasType K .t := by
  generalize hM : LF.max v K = M at h
  induction h with
  | max _ hK => cases hM; exact hK
  | sub _ ih => exact ih hM
  | _ => cases hM

theorem HasType.right_of_seq {K L : LF R E} (h : HasType (.seq K L) .t) : HasType L .t := by
  cases h with
  | seq _ hL => exact hL

theorem not_hasType_card_t (v : R) (n : ℕ) : ¬ HasType (.card v n : LF R E) .t := nofun

variable (v u : R) (P Q : E → Prop) (r : E → E → Prop) (n m : ℕ)

/-- `LF.cumulative` is the logical form (45). -/
def LF.cumulative : LF R E :=
  .seq (.seq (.max v (.seq (.dref v P) (.max u (.seq (.dref u Q) (.rel u v r))))) (.card u m))
    (.card v n)

/-- `LF.pseudoCumulative` is the logical form (46). -/
def LF.pseudoCumulative : LF R E :=
  .seq (.max v (.seq (.dref v P) (.seq (.max u (.seq (.dref u Q) (.rel u v r))) (.card u m))))
    (.card v n)

/-- (45) has type `T`. -/
theorem hasType_cumulative : HasType (LF.cumulative v u P Q r n m) .T :=
  .seq (.seq (.sub (.max v (.seq (.dref v P) (.max u (.seq (.dref u Q) (.rel u v r))))))
    (.card u m)) (.card v n)

/-- (46) has no type, since its object's cardinality test forces the scope of `Mv` to type `T`. -/
theorem not_hasType_pseudoCumulative (A : Ty) :
    ¬ HasType (LF.pseudoCumulative v u P Q r n m) A := by
  have hmax : ∀ B, ¬ HasType (.max v (.seq (.dref v P) (.seq (.max u (.seq (.dref u Q)
      (.rel u v r))) (.card u m))) : LF R E) B :=
    fun B h ↦ not_hasType_card_t u m h.of_max.right_of_seq.right_of_seq
  intro h
  cases h with
  | seq h _ => exact hmax _ h
  | sub h => cases h with
    | seq h _ => exact hmax _ h

/-- `K.denote` is the update that the logical form `K` denotes. -/
def LF.denote {S : Type*} [RegisterStructure R S E] [PartialOrder E] :
    LF R E → Update S
  | .dref v P => Evar v P
  | .max v K => maxAt v K.denote
  | .card v n => Charlow2021.card v n
  | .rel u v r => relTest u v r
  | .seq K L => K.denote ○ L.denote

variable {S : Type*} [RegisterStructure R S E] [PartialOrder E]

theorem denote_cumulative :
    (LF.cumulative v u P Q r n m).denote = (cumulative v u P Q r n m : Update S) := rfl

theorem denote_pseudoCumulative :
    (LF.pseudoCumulative v u P Q r n m).denote = (pseudoCumulative v u P Q r n m : Update S) := rfl

end Typing

/-! ### Post-suppositions (§5, Appendix B) -/

section PostSuppositional

universe u

variable {R S : Type u} {E : Type*} [RegisterStructure R S E] [PartialOrder E]

/-- A post-suppositional meaning (52) is a computation of the Writer monad over the update monoid,
whose log is its post-supposition; `pure` and `bind` are (120) and (121), the unit being the
dynamic tautology `T` of (15). -/
abbrev PostSupp (S : Type u) := Writer (Update S)

/-- `exactlyPS v n P` is the post-suppositional modified numeral (53), whose cardinality test is
post-supposed. -/
def exactlyPS (v : R) (n : ℕ) (P : E → Prop) : PostSupp S (Cont (Update S) R) :=
  Writer.mk (fun k ↦ maxAt v (Evar v P ○ k v)) (card v n)

/-- `sentencePS` is the sentence (55), composed by Combine⁺, which is the Writer monad's `<*>`
(122). -/
def sentencePS (v u : R) (P Q : E → Prop) (r : E → E → Prop) (n m : ℕ) : PostSupp S (Update S) :=
  (fun B M ↦ B fun a ↦ M fun b ↦ relTest b a r) <$> exactlyPS v n P <*> exactlyPS u m Q

/-- Reification (58) conjoins a meaning with its post-supposition. -/
def PostSupp.reify (p : PostSupp S (Update S)) : Update S := p.val ○ p.log

variable (v u : R) (P Q : E → Prop) (r : E → E → Prop) (n m : ℕ)

theorem val_sentencePS :
    (sentencePS v u P Q r n m : PostSupp S _).val =
      maxAt v (Evar v P ○ maxAt u (Evar u Q ○ relTest u v r)) := rfl

theorem log_sentencePS :
    (sentencePS v u P Q r n m : PostSupp S _).log = card v n ○ card u m := rfl

/-- Reifying (55) gives (57), which is the cumulative (6). -/
theorem reify_sentencePS :
    (sentencePS v u P Q r n m : PostSupp S _).reify = cumulative v u P Q r n m := by
  rw [PostSupp.reify, val_sentencePS, log_sentencePS, cumulative, comp_assoc, card_comp_card_comm]

end PostSuppositional

/-! ### Update semantics (§6) -/

section UpdateTheoretic

variable {R S E : Type*} [RegisterStructure R S E] [PartialOrder E]

/-- Update-theoretic maximization (78) keeps the outputs whose value of `v` is maximal in the
whole updated context. -/
def maxAtU (v : R) (K : CCP S) : CCP S := fun s ↦ {j ∈ K s | ∀ h ∈ K s, ¬ val v j < val v h}

/-- Pointwise maximization is update-theoretic maximization on a singleton (79). -/
theorem lower_maxAtU_image (v : R) (D : Update S) : CCP.lower (maxAtU v D.image) = maxAt v D := by
  ext ⟨i, j⟩
  simp [maxAtU, maxAt, maxBy]

/-- `exactlyU v n P` is the update-theoretic modified numeral (81), of the same form as (3). -/
def exactlyU (v : R) (n : ℕ) (P : E → Prop) : Cont (CCP S) R :=
  fun k ↦ CCP.seq (maxAtU v (CCP.seq (Evar v P).image (k v))) (card v n).image

/-- `sentenceU` is the sentence (82), with the quantifiers in surface scope. -/
def sentenceU (v u : R) (P Q : E → Prop) (r : E → E → Prop) (n m : ℕ) : CCP S :=
  exactlyU v n P fun a ↦ exactlyU u m Q fun b ↦ (relTest b a r).image

/-- `sentenceULowered` is (82) with the object's maximization replaced by the lift of its pointwise
counterpart (p. 34). -/
def sentenceULowered (v u : R) (P Q : E → Prop) (r : E → E → Prop) (n m : ℕ) : CCP S :=
  exactlyU v n P fun a ↦ CCP.seq
    (CCP.lower (maxAtU u (CCP.seq (Evar u Q).image (relTest u a r).image))).image (card u m).image

omit [PartialOrder E] in
private theorem image_comp_eq_seq (D₁ D₂ : Update S) :
    (D₁ ○ D₂).image = CCP.seq D₁.image D₂.image :=
  funext fun _ ↦ SetRel.image_comp ..

/-- Lifting the object's maximization from its pointwise counterpart brings back the
pseudo-cumulative reading (p. 34). -/
theorem down_sentenceULowered (v u : R) (P Q : E → Prop) (r : E → E → Prop) (n m : ℕ) :
    CCP.down (sentenceULowered v u P Q r n m : CCP S) = (pseudoCumulative v u P Q r n m).dom := by
  ext i
  simp only [sentenceULowered, exactlyU, ← image_comp_eq_seq, lower_maxAtU_image, CCP.down,
    pseudoCumulative, CCP.seq, Set.mem_ofPred_eq]
  rw [← lower_maxAtU_image v]
  simp [Set.Nonempty]

end UpdateTheoretic

/-! ### The models of Figure 1 -/

section Figure1

/-- `Ent` has the atoms of Figure 1, four boys and six movies. -/
inductive Ent
  | b1 | b2 | b3 | b4 | m1 | m2 | m3 | m4 | m5 | m6
  deriving DecidableEq, Fintype

/-- `Reg` has the two registers, `v` for boys and `u` for movies. -/
inductive Reg
  | u | v
  deriving DecidableEq

/-- A scenario of Figure 1 gives the boys, the movies, and who saw what. -/
structure Scenario where
  boys : Finset Ent
  movies : Finset Ent
  sees : Finset (Ent × Ent)

namespace Scenario

variable (σ : Scenario)

/-- `σ.Boys X` says that `X` is a plurality of boys. -/
def Boys (X : Finset Ent) : Prop := X.Nonempty ∧ X ⊆ σ.boys

/-- `σ.Movies Y` says that `Y` is a plurality of movies. -/
def Movies (Y : Finset Ent) : Prop := Y.Nonempty ∧ Y ⊆ σ.movies

/-- `σ.Saw Y X` is the cumulative closure of seeing, object first, so that every boy in `X` saw a
movie in `Y` and every movie in `Y` was seen by a boy in `X`. -/
def Saw (Y X : Finset Ent) : Prop := Set.LiftRel (fun b m ↦ (b, m) ∈ σ.sees) ↑X ↑Y

/-- `σ.seen X` is the set of movies that some boy in `X` saw. -/
def seen (X : Finset Ent) : Finset Ent := σ.movies.filter fun m ↦ ∃ b ∈ X, (b, m) ∈ σ.sees

/-- Every seeing is of a movie by a boy. -/
def WellFormed : Prop := σ.sees ⊆ σ.boys ×ˢ σ.movies

/-- Every boy saw some movie. -/
def Total : Prop := ∀ b ∈ σ.boys, ∃ m, (b, m) ∈ σ.sees

/-- `σ.swap` exchanges the roles of boys and movies. -/
def swap : Scenario := ⟨σ.movies, σ.boys, σ.sees.image Prod.swap⟩

instance : Decidable σ.WellFormed := inferInstanceAs (Decidable (σ.sees ⊆ σ.boys ×ˢ σ.movies))
instance : Decidable σ.Total := inferInstanceAs (Decidable (∀ b ∈ σ.boys, _))
instance : DecidablePred σ.Boys := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

variable {σ}

theorem mem_swap_sees {x y : Ent} : (x, y) ∈ σ.swap.sees ↔ (y, x) ∈ σ.sees := by
  simp only [swap, Finset.mem_image, Prod.exists, Prod.swap_prod_mk, Prod.mk.injEq]
  exact ⟨fun ⟨_, _, h, rfl, rfl⟩ ↦ h, fun h ↦ ⟨_, _, h, rfl, rfl⟩⟩

theorem swap_saw : σ.swap.Saw = flip σ.Saw := by
  funext Y X
  exact propext <| by simp only [Saw, Set.LiftRel, flip, Finset.mem_coe, mem_swap_sees, and_comm]

theorem subset_seen {X Y : Finset Ent} (hY : Y ⊆ σ.movies) (h : σ.Saw Y X) : Y ⊆ σ.seen X :=
  fun m hm ↦ let ⟨b, hb, hbm⟩ := h.2 m hm; Finset.mem_filter.2 ⟨hY hm, b, hb, hbm⟩

theorem saw_seen (hw : σ.WellFormed) (ht : σ.Total) {X : Finset Ent} (hX : X ⊆ σ.boys) :
    σ.Saw (σ.seen X) X := by
  refine ⟨fun b hb ↦ ?_, fun m hm ↦ (Finset.mem_filter.1 hm).2⟩
  obtain ⟨m, hbm⟩ := ht b (hX hb)
  exact ⟨m, Finset.mem_filter.2 ⟨(Finset.mem_product.1 (hw hbm)).2, b, hb, hbm⟩, hbm⟩

theorem movies_seen (hw : σ.WellFormed) (ht : σ.Total) {X : Finset Ent} (hX : σ.Boys X) :
    σ.Movies (σ.seen X) :=
  let ⟨b, hb⟩ := hX.1
  let ⟨m, hm, _⟩ := (saw_seen hw ht hX.2).1 b hb
  ⟨⟨m, hm⟩, Finset.filter_subset _ _⟩

theorem maximal_saw_iff (hw : σ.WellFormed) (ht : σ.Total) {X Y : Finset Ent} (hX : σ.Boys X) :
    Maximal (fun Y ↦ σ.Movies Y ∧ σ.Saw Y X) Y ↔ Y = σ.seen X := by
  have hg : σ.Movies (σ.seen X) ∧ σ.Saw (σ.seen X) X := ⟨movies_seen hw ht hX, saw_seen hw ht hX.2⟩
  refine ⟨fun h ↦ ?_, by rintro rfl; exact ⟨hg, fun Y hY _ ↦ subset_seen hY.1.2 hY.2⟩⟩
  have := subset_seen h.prop.1.2 h.prop.2
  exact le_antisymm this (h.2 hg this)

theorem maximal_boys_iff (hne : σ.boys.Nonempty) {X : Finset Ent} :
    Maximal σ.Boys X ↔ X = σ.boys :=
  ⟨fun h ↦ le_antisymm h.prop.2 (h.2 ⟨hne, le_rfl⟩ h.prop.2),
    by rintro rfl; exact ⟨⟨hne, le_rfl⟩, fun _ hY _ ↦ hY.2⟩⟩

end Scenario

/-- Scenario A of Figure 1 has three boys who saw five movies. -/
def scenarioA : Scenario where
  boys := {.b1, .b2, .b3}
  movies := {.m1, .m2, .m3, .m4, .m5}
  sees := {(.b1, .m1), (.b2, .m1), (.b2, .m2), (.b2, .m3), (.b3, .m3), (.b3, .m4), (.b3, .m5)}

/-- Scenario B of Figure 1 adds to Scenario A a fourth boy, who saw a sixth movie. -/
def scenarioB : Scenario where
  boys := {.b1, .b2, .b3, .b4}
  movies := {.m1, .m2, .m3, .m4, .m5, .m6}
  sees := scenarioA.sees ∪ {(.b4, .m6)}

open Scenario

/-- An assignment gives each register a plurality. -/
abbrev St := Reg → Finset Ent

variable {σ : Scenario} {a b : Reg}

theorem mem_maxAt_object (hab : a ≠ b) (hw : σ.WellFormed) (ht : σ.Total) {X : Finset Ent}
    (hX : σ.Boys X) {i k : St} :
    Function.update i a X ~[maxAt (S := St) b (Evar b σ.Movies ○ relTest b a σ.Saw)] k ↔
      k = Function.update (Function.update i a X) b (σ.seen X) := by
  rw [relTest, mem_maxAt_Evar_comp_test]
  simp only [extend_eq_update, val_apply, Set.mem_ofPred_eq, Function.update_self,
    Function.update_of_ne hab]
  constructor
  · rintro ⟨y, rfl, hy⟩
    rw [(maximal_saw_iff hw ht hX).1 hy]
  · rintro rfl
    exact ⟨_, rfl, (maximal_saw_iff hw ht hX).2 rfl⟩

theorem fixes_maxAt_object (hab : a ≠ b) :
    Fixes a (maxAt (S := St) b (Evar b σ.Movies ○ relTest b a σ.Saw)) :=
  ((fixes_Evar hab _).comp (fixes_test _ _)).maxBy

theorem update_update_apply (hab : a ≠ b) (i : St) (X Y : Finset Ent) :
    Function.update (Function.update i a X) b Y a = X := by
  rw [Function.update_of_ne hab, Function.update_self]

/-- (6) is true exactly when all the boys are `n` and the movies they saw `m`. -/
theorem mem_dom_cumulative (hab : a ≠ b) (hw : σ.WellFormed) (ht : σ.Total)
    (hne : σ.boys.Nonempty) (n m : ℕ) (i : St) :
    i ∈ (cumulative (S := St) a b σ.Boys σ.Movies σ.Saw n m).dom ↔
      (σ.seen σ.boys).card = m ∧ σ.boys.card = n := by
  have hQ : ∀ x, σ.Boys x → ((∃ k, extend i a x ~[maxAt (S := St) b
      (Evar b σ.Movies ○ relTest b a σ.Saw)] k) ↔ True) := fun x hx ↦ by
    simp only [extend_eq_update, mem_maxAt_object hab hw ht hx, exists_eq]
  simp only [cumulative, SetRel.mem_dom, mem_comp_card, mem_maxAt_Evar_comp (fixes_maxAt_object hab)
    hQ, and_true, maximal_boys_iff hne, extend_eq_update, val_apply, Mereology.atomCount_finset]
  constructor
  · rintro ⟨j, ⟨⟨hj, hja⟩, hm⟩, hn⟩
    rw [hja] at hj hn
    rw [(mem_maxAt_object hab hw ht ⟨hne, le_rfl⟩).1 hj, Function.update_self] at hm
    exact ⟨hm, hn⟩
  · rintro ⟨hm, hn⟩
    have hja := update_update_apply hab i σ.boys (σ.seen σ.boys)
    refine ⟨_, ⟨⟨?_, hja⟩, by rwa [Function.update_self]⟩, by rwa [hja]⟩
    rw [hja]
    exact (mem_maxAt_object hab hw ht ⟨hne, le_rfl⟩).2 rfl

/-- (5) is true exactly when some maximal plurality of boys who saw `m` movies is `n` boys. -/
theorem mem_dom_pseudoCumulative (hab : a ≠ b) (hw : σ.WellFormed) (ht : σ.Total) (n m : ℕ)
    (i : St) :
    i ∈ (pseudoCumulative (S := St) a b σ.Boys σ.Movies σ.Saw n m).dom ↔
      ∃ X, Maximal (fun X ↦ σ.Boys X ∧ (σ.seen X).card = m) X ∧ X.card = n := by
  have hQ : ∀ x, σ.Boys x → ((∃ k, extend i a x ~[maxAt (S := St) b
      (Evar b σ.Movies ○ relTest b a σ.Saw) ○ card b m] k) ↔ (σ.seen x).card = m) := fun x hx ↦ by
    simp only [extend_eq_update, mem_comp_card, mem_maxAt_object hab hw ht hx, exists_eq_left,
      val_apply, Function.update_self, Mereology.atomCount_finset]
  have hD : Fixes a (maxAt (S := St) b (Evar b σ.Movies ○ relTest b a σ.Saw) ○ card b m) :=
    (fixes_maxAt_object hab).comp (fixes_test _ _)
  simp only [pseudoCumulative, SetRel.mem_dom, mem_comp_card, mem_maxAt_Evar_comp hD hQ, val_apply,
    Mereology.atomCount_finset]
  constructor
  · rintro ⟨j, ⟨-, hX⟩, hn⟩
    exact ⟨_, hX, hn⟩
  · rintro ⟨X, hX, hn⟩
    have hja := update_update_apply hab i X (σ.seen X)
    refine ⟨Function.update (Function.update i a X) b (σ.seen X), ⟨?_, by rw [hja]; exact hX⟩,
      by rwa [hja]⟩
    rw [hja]
    exact ⟨(mem_maxAt_object hab hw ht hX.prop.1).2 rfl, by simpa using hX.prop.2⟩


theorem seen_mono {X X' : Finset Ent} (h : X ⊆ X') : σ.seen X ⊆ σ.seen X' :=
  Finset.monotone_filter_right _ fun _ _ ⟨b, hb, hbm⟩ ↦ ⟨b, h hb, hbm⟩

theorem mem_image_Evar {r : Reg} {P : Finset Ent → Prop} {s : Set St} {j : St} :
    j ∈ (Evar (S := St) r P).image s ↔ ∃ i ∈ s, ∃ x, P x ∧ j = Function.update i r x := by
  simp only [mem_image, mem_Evar, extend_eq_update]

theorem mem_object_context {i j : St} :
    j ∈ CCP.seq (Evar (S := St) Reg.u σ.Movies).image (relTest Reg.u Reg.v σ.Saw).image
        ((Evar (S := St) Reg.v σ.Boys).image {i}) ↔
      ∃ X Y, σ.Boys X ∧ σ.Movies Y ∧ σ.Saw Y X ∧
        j = Function.update (Function.update i .v X) .u Y := by
  simp only [CCP.seq, image_test, Set.mem_inter_iff, mem_image_Evar, Set.mem_singleton_iff,
    relTest, Set.mem_ofPred_eq, val_apply]
  constructor
  · rintro ⟨⟨_, ⟨_, rfl, X, hX, rfl⟩, Y, hY, rfl⟩, hsaw⟩
    refine ⟨X, Y, hX, hY, ?_, rfl⟩
    simpa using hsaw
  · rintro ⟨X, Y, hX, hY, hsaw, rfl⟩
    exact ⟨⟨_, ⟨i, rfl, X, hX, rfl⟩, Y, hY, rfl⟩, by simpa using hsaw⟩

theorem mem_maxAtU_object (hw : σ.WellFormed) (ht : σ.Total) (hne : σ.boys.Nonempty) {i j : St} :
    j ∈ maxAtU Reg.u (CCP.seq (Evar (S := St) Reg.u σ.Movies).image
        (relTest Reg.u Reg.v σ.Saw).image) ((Evar (S := St) Reg.v σ.Boys).image {i}) ↔
      ∃ X, σ.Boys X ∧ σ.Saw (σ.seen σ.boys) X ∧
        j = Function.update (Function.update i .v X) .u (σ.seen σ.boys) := by
  have hall : σ.Boys σ.boys := ⟨hne, le_rfl⟩
  have hsub : ∀ {X Y}, σ.Boys X → σ.Movies Y → σ.Saw Y X → Y ⊆ σ.seen σ.boys :=
    fun hX hY h ↦ (subset_seen hY.2 h).trans (seen_mono hX.2)
  simp only [maxAtU, Set.mem_ofPred_eq, mem_object_context, val_apply]
  constructor
  · rintro ⟨⟨X, Y, hX, hY, h, rfl⟩, hmax⟩
    refine ⟨X, hX, ?_, ?_⟩ <;> obtain rfl : Y = σ.seen σ.boys := by
      refine (hsub hX hY h).eq_of_not_ssubset fun hlt ↦ hmax _ ⟨σ.boys, _, hall,
        movies_seen hw ht hall, saw_seen hw ht le_rfl, rfl⟩ ?_
      simpa using hlt
    exacts [h, rfl]
  · rintro ⟨X, hX, h, rfl⟩
    refine ⟨⟨X, _, hX, movies_seen hw ht hall, h, rfl⟩, ?_⟩
    rintro _ ⟨X', Y', hX', hY', h', rfl⟩ hlt
    simp only [Function.update_self] at hlt
    exact hlt.not_subset (hsub hX' hY' h')

/-- (82) is true exactly when all the boys are `n` and the movies they saw `m`, so it has the
cumulative reading (§6.2). -/
theorem mem_down_sentenceU (hw : σ.WellFormed) (ht : σ.Total) (hne : σ.boys.Nonempty) (n m : ℕ)
    (i : St) :
    i ∈ CCP.down (sentenceU (S := St) Reg.v Reg.u σ.Boys σ.Movies σ.Saw n m) ↔
      (σ.seen σ.boys).card = m ∧ σ.boys.card = n := by
  have hall : σ.Boys σ.boys := ⟨hne, le_rfl⟩
  set G := CCP.seq (Evar (S := St) Reg.v σ.Boys).image
    (exactlyU Reg.u m σ.Movies fun b ↦ (relTest b Reg.v σ.Saw).image) with hGdef
  have hctx : ∀ j, j ∈ G {i} ↔ ∃ X, σ.Boys X ∧ σ.Saw (σ.seen σ.boys) X ∧
      (σ.seen σ.boys).card = m ∧ j = Function.update (Function.update i .v X) .u (σ.seen σ.boys) :=
    fun j ↦ by
    simp only [hGdef, exactlyU, CCP.seq, image_test, Set.mem_inter_iff, card, Set.mem_ofPred_eq,
      val_apply, Mereology.atomCount_finset]
    simp only [mem_maxAtU_object hw ht hne]
    constructor
    · rintro ⟨⟨X, hX, h, rfl⟩, hm⟩
      exact ⟨X, hX, h, by simpa using hm, rfl⟩
    · rintro ⟨X, hX, h, hm, rfl⟩
      exact ⟨⟨X, hX, h, rfl⟩, by simpa using hm⟩
  rw [show sentenceU (S := St) Reg.v Reg.u σ.Boys σ.Movies σ.Saw n m =
    CCP.seq (maxAtU Reg.v G) (card Reg.v n).image from rfl]
  simp only [CCP.down, Set.mem_ofPred_eq, CCP.seq, image_test, Set.Nonempty, Set.mem_inter_iff,
    maxAtU, card, val_apply, Mereology.atomCount_finset, hctx]
  constructor
  · rintro ⟨_, ⟨⟨X, hX, h, hm, rfl⟩, hmax⟩, hn⟩
    obtain rfl : X = σ.boys := by
      refine hX.2.eq_of_not_ssubset fun hlt ↦
        hmax _ ⟨σ.boys, hall, saw_seen hw ht le_rfl, hm, rfl⟩ ?_
      simpa [update_update_apply (show Reg.v ≠ Reg.u by decide)] using hlt
    exact ⟨hm, by simpa [update_update_apply (show Reg.v ≠ Reg.u by decide)] using hn⟩
  · rintro ⟨hm, hn⟩
    refine ⟨_, ⟨⟨σ.boys, hall, saw_seen hw ht le_rfl, hm, rfl⟩, ?_⟩, by simpa using hn⟩
    rintro _ ⟨X', hX', -, -, rfl⟩ hlt
    simp only [update_update_apply (show Reg.v ≠ Reg.u by decide)] at hlt
    exact hlt.not_subset hX'.2

theorem scenarioA_wellFormed : scenarioA.WellFormed := by decide
theorem scenarioB_wellFormed : scenarioB.WellFormed := by decide
theorem scenarioA_total : scenarioA.Total := by decide
theorem scenarioB_total : scenarioB.Total := by decide
theorem scenarioA_swap_wellFormed : scenarioA.swap.WellFormed := by decide
theorem scenarioB_swap_wellFormed : scenarioB.swap.WellFormed := by decide
theorem scenarioA_swap_total : scenarioA.swap.Total := by decide
theorem scenarioB_swap_total : scenarioB.swap.Total := by decide

/-- The cumulative (6) is true in Scenario A (§1.3). -/
theorem cumulative_scenarioA (i : St) :
    i ∈ (cumulative (S := St) Reg.v Reg.u scenarioA.Boys scenarioA.Movies scenarioA.Saw 3 5).dom :=
  (mem_dom_cumulative (by decide) scenarioA_wellFormed scenarioA_total (by decide) 3 5 i).2
    (by decide)

/-- The cumulative (6) is false in Scenario B (§1.3). -/
theorem cumulative_scenarioB (i : St) :
    i ∉ (cumulative (S := St) Reg.v Reg.u scenarioB.Boys scenarioB.Movies scenarioB.Saw 3 5).dom :=
  fun h ↦ absurd ((mem_dom_cumulative (by decide) scenarioB_wellFormed scenarioB_total
    (by decide) 3 5 i).1 h) (by decide)

/-- The pseudo-cumulative (5) is true in Scenario A as well (§1.1). -/
theorem pseudoCumulative_scenarioA (i : St) :
    i ∈ (pseudoCumulative (S := St) Reg.v Reg.u scenarioA.Boys scenarioA.Movies scenarioA.Saw
      3 5).dom :=
  (mem_dom_pseudoCumulative (by decide) scenarioA_wellFormed scenarioA_total 3 5 i).2
    ⟨scenarioA.boys, ⟨by decide, fun _ hY _ ↦ hY.1.2⟩, by decide⟩

theorem maximal_b123 :
    Maximal (fun X ↦ scenarioB.Boys X ∧ (scenarioB.seen X).card = 5) {.b1, .b2, .b3} := by
  refine ⟨by decide, fun Y hY hXY ↦ ?_⟩
  by_contra hYX
  obtain ⟨c, hcY, hcX⟩ := Finset.not_subset.1 hYX
  have hb4 : ∀ c ∈ scenarioB.boys, c ∉ ({.b1, .b2, .b3} : Finset Ent) → c = .b4 := by decide
  have hcover : ∀ c ∈ scenarioB.boys, c = .b4 ∨ c ∈ ({.b1, .b2, .b3} : Finset Ent) := by decide
  have hall : Y = scenarioB.boys := Finset.Subset.antisymm hY.1.2 fun d hd ↦
    (hcover d hd).elim (fun h ↦ h ▸ hb4 c (hY.1.2 hcY) hcX ▸ hcY) (fun h ↦ hXY h)
  exact absurd (hall ▸ hY.2) (by decide)

/-- The pseudo-cumulative (5) is true in Scenario B (§2.3). -/
theorem pseudoCumulative_scenarioB (i : St) :
    i ∈ (pseudoCumulative (S := St) Reg.v Reg.u scenarioB.Boys scenarioB.Movies scenarioB.Saw
      3 5).dom :=
  (mem_dom_pseudoCumulative (by decide) scenarioB_wellFormed scenarioB_total 3 5 i).2
    ⟨_, maximal_b123, by decide⟩

/-- The scopings (28) and (30) agree with (6) in Scenario A. -/
theorem cumulative_swap_scenarioA (i : St) :
    i ∈ (cumulative (S := St) Reg.u Reg.v scenarioA.Movies scenarioA.Boys (flip scenarioA.Saw)
      5 3).dom := by
  rw [← swap_saw]
  exact (mem_dom_cumulative (by decide) scenarioA_swap_wellFormed scenarioA_swap_total
    (by decide) 5 3 i).2 (by decide)

/-- The scopings (28) and (30) agree with (6) in Scenario B. -/
theorem cumulative_swap_scenarioB (i : St) :
    i ∉ (cumulative (S := St) Reg.u Reg.v scenarioB.Movies scenarioB.Boys (flip scenarioB.Saw)
      5 3).dom := by
  rw [← swap_saw]
  exact fun h ↦ absurd ((mem_dom_cumulative (by decide) scenarioB_swap_wellFormed
    scenarioB_swap_total (by decide) 5 3 i).1 h) (by decide)

theorem maximal_m12345 : Maximal (fun Y ↦ scenarioB.swap.Boys Y ∧ (scenarioB.swap.seen Y).card = 3)
    {.m1, .m2, .m3, .m4, .m5} := by
  refine ⟨by decide, fun Y hY hXY ↦ ?_⟩
  by_contra hYX
  obtain ⟨c, hcY, hcX⟩ := Finset.not_subset.1 hYX
  have hm6 : ∀ c ∈ scenarioB.movies, c ∉ ({.m1, .m2, .m3, .m4, .m5} : Finset Ent) → c = .m6 := by
    decide
  have hcover : ∀ c ∈ scenarioB.movies,
      c = .m6 ∨ c ∈ ({.m1, .m2, .m3, .m4, .m5} : Finset Ent) := by decide
  have hall : Y = scenarioB.movies := Finset.Subset.antisymm hY.1.2 fun d hd ↦
    (hcover d hd).elim (fun h ↦ h ▸ hm6 c (hY.1.2 hcY) hcX ▸ hcY) (fun h ↦ hXY h)
  exact absurd (hall ▸ hY.2) (by decide)

/-- The scoping (33) is pseudo-cumulative, and true in Scenario B. -/
theorem pseudoCumulative_swap_scenarioB (i : St) :
    i ∈ (pseudoCumulative (S := St) Reg.u Reg.v scenarioB.Movies scenarioB.Boys (flip scenarioB.Saw)
      5 3).dom := by
  rw [← swap_saw]
  exact (mem_dom_pseudoCumulative (by decide) scenarioB_swap_wellFormed scenarioB_swap_total 5 3
    i).2 ⟨_, maximal_m12345, by decide⟩

/-- (82) is true in Scenario A. -/
theorem sentenceU_scenarioA (i : St) : i ∈ CCP.down (sentenceU (S := St) Reg.v Reg.u
    scenarioA.Boys scenarioA.Movies scenarioA.Saw 3 5) :=
  (mem_down_sentenceU scenarioA_wellFormed scenarioA_total (by decide) 3 5 i).2 (by decide)

/-- (82) is false in Scenario B, though it has the form of the pseudo-cumulative (5). -/
theorem sentenceU_scenarioB (i : St) : i ∉ CCP.down (sentenceU (S := St) Reg.v Reg.u
    scenarioB.Boys scenarioB.Movies scenarioB.Saw 3 5) :=
  fun h ↦ absurd ((mem_down_sentenceU scenarioB_wellFormed scenarioB_total (by decide) 3 5 i).1 h)
    (by decide)

/-- Update-theoretic maximization is not distributive, since otherwise it would be the lift of its
pointwise counterpart, and (82) would be true in Scenario B (§6.2). -/
theorem not_isDistributive_maxAtU : ¬ CCP.IsDistributive (maxAtU (S := St) Reg.u
    (CCP.seq (Evar Reg.u scenarioB.Movies).image (relTest Reg.u Reg.v scenarioB.Saw).image)) := by
  intro hd
  have h : sentenceULowered (S := St) Reg.v Reg.u scenarioB.Boys scenarioB.Movies scenarioB.Saw
      3 5 = sentenceU Reg.v Reg.u scenarioB.Boys scenarioB.Movies scenarioB.Saw 3 5 := by
    simp only [sentenceULowered, sentenceU, exactlyU, CCP.image_lower _ hd]
  have h₁ := pseudoCumulative_scenarioB fun _ ↦ ∅
  rw [← down_sentenceULowered, h] at h₁
  exact sentenceU_scenarioB _ h₁

end Figure1

end Charlow2021
