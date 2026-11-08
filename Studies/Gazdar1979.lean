module

public import Linglib.Logic.Epistemic.Basic
public import Linglib.Data.Examples.Gazdar1979
public import Linglib.Core.Data.Fintype.Sets
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Set.Lattice.Bounded

/-!
# Gazdar (1979): Pragmatics: Implicature, Presupposition, and Logical Form

This file formalizes Gazdar's projection of implicatures. Asserting a sentence commits the speaker
to knowing it, in Hintikka's logic of what the speaker knows and leaves possible, and the sentence
potentially implicates that the speaker leaves possible each clause it leaves open and its
negation, and knows false the stronger scalar alternative of each part it entails. The context
adds these in that order, [each only so far as it fits](##Gazdar1979.not_mem_incr), so that *John
did it or Mary did it* [implicates *not both* and *John did it or Mary did it or both of them did
it* does not](##Gazdar1979.rows_reading), though the two are truth-conditionally equivalent.

## Implementation notes

* Sentences are formulas of `EpistemicLogic` with the speaker as their one agent. In the examples a
  world pairs a valuation of two atoms with the valuations the speaker's information leaves open,
  so that knowledge is S5 there, a special case of the S4 Gazdar takes from Hintikka.
* Presuppositions are not modelled: their potential set is empty, and condition (iv) of (V), which
  refers to them, is dropped.
* A scale gives the stronger alternative of a part, `⟨and, or⟩` and `⟨all, some⟩`.

## References

* [gazdar-1979]
* [hintikka-1962]
-/

@[expose] public section

namespace Gazdar1979

open EpistemicLogic EpistemicLogic.Formula Set

attribute [local instance] Set.decidableSubsetOfFintype

/-! ### Contexts and satisfiable incrementation -/

section Context

variable {W : Type*} {X Y Z c : Set (Set W)} {y : Set W}

/-- (IX): a set of propositions is consistent when some world lies in all of them. -/
def Con (X : Set (Set W)) : Prop := (⋂₀ X).Nonempty

/-- (XVI): the satisfiable incrementation of `X` by `Y` adds to `X` the members of `Y` whose
addition keeps every consistent subset of `X ∪ Y` consistent. -/
def incr (X Y : Set (Set W)) : Set (Set W) :=
  X ∪ {y | y ∈ Y ∧ ∀ Z ⊆ X ∪ Y, Con (insert y Z) ↔ Con Z}

@[inherit_doc] local infixl:65 " ∪! " => incr

theorem Con.anti (h : Con X) (hZ : Z ⊆ X) : Con Z := h.mono (sInter_subset_sInter hZ)

theorem con_of_forall_mem {w : W} (h : ∀ x ∈ X, w ∈ x) : Con X := ⟨w, mem_sInter.2 h⟩

theorem incr_eq_union (h : Con (X ∪ Y)) : X ∪! Y = X ∪ Y :=
  subset_antisymm (union_subset_union_right X fun _ hy ↦ hy.1) <| union_subset subset_union_left
    fun _ hy ↦ .inr ⟨hy, fun _ hZ ↦ ⟨fun h' ↦ h'.anti (subset_insert _ _),
      fun _ ↦ h.anti (insert_subset (.inr hy) hZ)⟩⟩

theorem not_mem_incr (hy : y ∉ X) (hZ : Z ⊆ X ∪ Y) (hc : Con Z) (hn : ¬ Con (insert y Z)) :
    y ∉ X ∪! Y := by
  rintro (h | ⟨-, h⟩)
  exacts [hy h, hn ((h Z hZ).2 hc)]

end Context

@[inherit_doc] local infixl:65 " ∪! " => incr

/-! ### Implicatures -/

section Implicatures

variable {V W : Type*} (M : Model V Unit W) {φ : Formula V Unit} {c : Set (Set W)}

/-- The proposition a sentence expresses, the worlds at which it is true. -/
abbrev den (φ : Formula V Unit) : Set W := {w | M.Sat φ w}

/-- The parts of a sentence, its subformulas, the `ψ` of `X⌢ψ⌢Y` in (IV) and (V). -/
def parts : Formula V Unit → List (Formula V Unit)
  | .atom v => [.atom v]
  | .neg p => .neg p :: parts p
  | .and p q => .and p q :: (parts p ++ parts q)
  | .or p q => .or p q :: (parts p ++ parts q)
  | .K a p => .K a p :: parts p
  | .P a p => .P a p :: parts p
  | .B a p => .B a p :: parts p
  | .C a p => .C a p :: parts p

/-- (V): the clausal implicatures of `φ`, that the speaker leaves possible each part `ψ` that `φ`
neither entails nor contradicts, and leaves its negation possible. -/
def clausal (φ : Formula V Unit) : Set (Set W) :=
  {x | ∃ ψ ∈ parts φ, ¬ den M φ ⊆ den M ψ ∧ ¬ den M φ ⊆ den M ∼ψ ∧
    (x = den M (P () ψ) ∨ x = den M (P () ∼ψ))}

/-- (IV): the scalar implicatures of `φ` on a scale `s` giving the stronger alternative of a part,
that the speaker knows false the stronger alternative of each part that `φ` entails. -/
def scalar (s : Formula V Unit → Option (Formula V Unit)) (φ : Formula V Unit) : Set (Set W) :=
  {x | ∃ ψ ∈ parts φ, ∃ χ ∈ s ψ, den M φ ⊆ den M ψ ∧ x = den M (K () ∼χ)}

/-- (XV) and (XVII): the context after asserting `φ` in the context `c`, which adds that the
speaker knows `φ`, then the clausal and then the scalar implicatures that fit. -/
def update (s : Formula V Unit → Option (Formula V Unit)) (c : Set (Set W)) (φ : Formula V Unit) :
    Set (Set W) :=
  (insert (den M (K () φ)) c ∪! clausal M φ) ∪! scalar M s φ

theorem forall_mem_clausal {q : Set W → Prop} : (∀ x ∈ clausal M φ, q x) ↔
    ∀ ψ ∈ parts φ, ¬ den M φ ⊆ den M ψ → ¬ den M φ ⊆ den M ∼ψ →
      q (den M (P () ψ)) ∧ q (den M (P () ∼ψ)) :=
  ⟨fun h ψ hψ h₁ h₂ ↦ ⟨h _ ⟨ψ, hψ, h₁, h₂, .inl rfl⟩, h _ ⟨ψ, hψ, h₁, h₂, .inr rfl⟩⟩,
    fun h _ ⟨ψ, hψ, h₁, h₂, hx⟩ ↦ hx.elim (fun hx ↦ hx ▸ (h ψ hψ h₁ h₂).1)
      fun hx ↦ hx ▸ (h ψ hψ h₁ h₂).2⟩

theorem forall_mem_scalar {s : Formula V Unit → Option (Formula V Unit)} {q : Set W → Prop} :
    (∀ x ∈ scalar M s φ, q x) ↔ ∀ ψ ∈ parts φ, ∀ χ ∈ s ψ, den M φ ⊆ den M ψ → q (den M (K () ∼χ)) :=
  ⟨fun h ψ hψ χ hχ hφ ↦ h _ ⟨ψ, hψ, χ, hχ, hφ, rfl⟩, fun h _ ⟨ψ, hψ, χ, hχ, hφ, hx⟩ ↦
    hx ▸ h ψ hψ χ hχ hφ⟩

theorem update_eq {s : Formula V Unit → Option (Formula V Unit)}
    (h : Con (insert (den M (K () φ)) c ∪ clausal M φ ∪ scalar M s φ)) :
    update M s c φ = insert (den M (K () φ)) c ∪ clausal M φ ∪ scalar M s φ := by
  rw [update, incr_eq_union (h.anti subset_union_left), incr_eq_union h]

theorem den_K_neg_inter_den_P (χ : Formula V Unit) : den M (K () ∼χ) ∩ den M (P () χ) = ∅ :=
  eq_empty_iff_forall_notMem.2 fun _ ⟨hK, v, hv, hχ⟩ ↦ hK v hv hχ

theorem con_clausal {w : W} (hK : w ∈ den M (K () φ)) (hcl : ∀ x ∈ clausal M φ, w ∈ x) :
    Con (insert (den M (K () φ)) ∅ ∪ clausal M φ) :=
  con_of_forall_mem fun x hx ↦ by
    simp only [mem_union, mem_insert_iff, mem_empty_iff_false, or_false] at hx
    rcases hx with rfl | hx
    exacts [hK, hcl x hx]

theorem con_scalar {s : Formula V Unit → Option (Formula V Unit)} {w : W}
    (hK : w ∈ den M (K () φ)) (hcl : ∀ x ∈ clausal M φ, w ∈ x) (hsc : ∀ x ∈ scalar M s φ, w ∈ x) :
    Con (insert (den M (K () φ)) ∅ ∪ clausal M φ ∪ scalar M s φ) :=
  con_of_forall_mem fun x hx ↦ by
    simp only [mem_union, mem_insert_iff, mem_empty_iff_false, or_false] at hx
    rcases hx with (rfl | hx) | hx
    exacts [hK, hcl x hx, hsc x hx]

/-- (XVII) and p. 136: a scalar implicature that the speaker knows not `χ` is cancelled when a
clausal implicature that the speaker leaves `χ` possible is added before it. -/
theorem K_neg_not_mem_update {s : Formula V Unit → Option (Formula V Unit)} {χ : Formula V Unit}
    (hcon : Con (insert (den M (K () φ)) ∅ ∪ clausal M φ)) (hP : den M (P () χ) ∈ clausal M φ)
    (hne : ∀ x ∈ insert (den M (K () φ)) ∅ ∪ clausal M φ, ∃ w ∈ x, w ∉ den M (K () ∼χ)) :
    den M (K () ∼χ) ∉ update M s ∅ φ := by
  rw [update, incr_eq_union hcon]
  refine not_mem_incr (fun h ↦ let ⟨_, hw, hw'⟩ := hne _ h; hw' hw)
    (singleton_subset_iff.2 (.inl (.inr hP))) (hcon.anti (singleton_subset_iff.2 (.inr hP))) ?_
  rw [Con, sInter_pair, den_K_neg_inter_den_P]
  exact not_nonempty_empty

/-- (25) and (26): asserting *φ but I do not know that φ* commits the speaker to knowing it, which
is necessarily false, Hintikka's solution to Moore's problem. -/
theorem den_K_moore (φ : Formula V Unit) : den M (K () (φ ⋏ ∼K () φ)) = ∅ :=
  eq_empty_iff_forall_notMem.2 fun w h ↦
    (h w ((M.epi_refl ()).refl w)).2 fun v hv ↦ (h v hv).1

end Implicatures

/-! ### The examples

A world of the examples is a valuation of two atoms with the set of valuations the speaker's
information leaves open, among the admissible ones; the speaker's alternatives to a world are the
worlds with the same set. -/

/-- The worlds over the admissible valuations `adm` of two atoms. -/
abbrev World (adm : Finset (Bool × Bool)) :=
  {p : (Bool × Bool) × Finset (Bool × Bool) // p.1 ∈ p.2 ∧ p.2 ⊆ adm}

instance (adm : Finset (Bool × Bool)) : Fintype (World adm) := Subtype.fintype _

/-- The model of the speaker's information about two atoms. -/
abbrev info (adm : Finset (Bool × Bool)) : Model (Fin 2) Unit (World adm) where
  epi _ := {x | x.1.1.2 = x.2.1.2}
  dox _ := {x | x.1.1.2 = x.2.1.2}
  val i w := (if i = 0 then w.1.1.1 else w.1.1.2) = true
  epi_refl _ := ⟨fun _ ↦ rfl⟩
  dox_serial _ := ⟨fun w ↦ ⟨w, rfl⟩⟩
  dox_le_epi _ _ h := h

instance (adm : Finset (Bool × Bool)) (φ : Formula (Fin 2) Unit) :
    DecidablePred (· ∈ den (info adm) φ) :=
  fun w ↦ (info adm).decSat φ w

/-- The scale `⟨and, or⟩` (p. 59): the stronger alternative of a disjunction is the conjunction. -/
def andOr : Formula (Fin 2) Unit → Option (Formula (Fin 2) Unit)
  | .or a b => some (a ⋏ b)
  | _ => none

/-- The scale `⟨all, some⟩` (52) on the atoms *some of the students were there* (`0`) and *all of
them were* (`1`). -/
def allSome : Formula (Fin 2) Unit → Option (Formula (Fin 2) Unit)
  | .atom 0 => some (.atom 1)
  | _ => none

/-- *John did it*, or *some of the students were there*. -/
local notation "𝐚" => (Formula.atom 0 : Formula (Fin 2) Unit)
/-- *Mary did it*, or *all of the students were there*. -/
local notation "𝐛" => (Formula.atom 1 : Formula (Fin 2) Unit)

/-- The valuations on which all of the students being there entails some being there. -/
def allToSome : Finset (Bool × Bool) := Finset.univ.filter fun v ↦ v.2 = true → v.1 = true

/-- (18)-(20): *John did it or Mary did it* implicates that the speaker knows *not (John did it
and Mary did it)*, and the truth-conditionally equivalent *John did it or Mary did it or both of
them did it* does not, its clausal implicature that the speaker leaves (20) possible excluding the
scalar one. -/
theorem exclusive :
    den (info .univ) (𝐚 ⋎ 𝐛) = den (info .univ) (𝐚 ⋎ 𝐛 ⋎ (𝐚 ⋏ 𝐛)) ∧
      den (info .univ) (K () ∼(𝐚 ⋏ 𝐛)) ∈ update (info .univ) andOr ∅ (𝐚 ⋎ 𝐛) ∧
      den (info .univ) (K () ∼(𝐚 ⋏ 𝐛)) ∉ update (info .univ) andOr ∅ (𝐚 ⋎ 𝐛 ⋎ (𝐚 ⋏ 𝐛)) := by
  set M := info .univ
  -- the speaker knows that exactly one of them did it
  let w : World .univ := ⟨((true, false), {(true, false), (false, true)}), by decide⟩
  -- the speaker knows that one of them did it and leaves every combination open
  let w' : World .univ := ⟨((true, true), {(true, false), (false, true), (true, true)}), by decide⟩
  refine ⟨by ext v; revert v; decide, ?_, ?_⟩
  · rw [update_eq M (con_scalar M (w := w) (by decide) ((forall_mem_clausal M).2 (by decide))
      ((forall_mem_scalar M).2 (by decide)))]
    exact .inr ⟨𝐚 ⋎ 𝐛, by decide, 𝐚 ⋏ 𝐛, rfl, subset_rfl, rfl⟩
  · refine K_neg_not_mem_update M (con_clausal M (w := w') (by decide)
      ((forall_mem_clausal M).2 (by decide))) ⟨𝐚 ⋏ 𝐛, by decide, by decide, by decide, .inl rfl⟩
      fun x hx ↦ ?_
    simp only [mem_union, mem_insert_iff, mem_empty_iff_false, or_false] at hx
    rcases hx with rfl | hx
    · exact ⟨w', by decide, by decide⟩
    · revert x hx; exact (forall_mem_clausal M).2 (by decide)

-- (XVII), p. 132: the order is not itself explained, but it matters, for added before the
-- clausal implicatures the scalar implicature of (19) would survive
theorem K_neg_mem_of_scalar_first :
    den (info .univ) (K () ∼(𝐚 ⋏ 𝐛)) ∈
      (insert (den (info .univ) (K () (𝐚 ⋎ 𝐛 ⋎ (𝐚 ⋏ 𝐛)))) ∅ ∪! scalar (info .univ) andOr
        (𝐚 ⋎ 𝐛 ⋎ (𝐚 ⋏ 𝐛))) ∪! clausal (info .univ) (𝐚 ⋎ 𝐛 ⋎ (𝐚 ⋏ 𝐛)) := by
  set M := info .univ
  let w : World .univ := ⟨((true, false), {(true, false), (false, true)}), by decide⟩
  have hcon : Con (insert (den M (K () (𝐚 ⋎ 𝐛 ⋎ (𝐚 ⋏ 𝐛)))) ∅ ∪ scalar M andOr (𝐚 ⋎ 𝐛 ⋎ (𝐚 ⋏ 𝐛))) :=
    con_of_forall_mem (w := w) fun x hx ↦ by
      simp only [mem_union, mem_insert_iff, mem_empty_iff_false, or_false] at hx
      rcases hx with rfl | hx
      · decide
      · revert x hx; exact (forall_mem_scalar M).2 (by decide)
  rw [incr_eq_union hcon]
  exact .inl (.inr ⟨𝐚 ⋎ 𝐛, by decide, 𝐚 ⋏ 𝐛, rfl, by decide, rfl⟩)

/-- (21)-(23): *some of the students were there* implicates that the speaker knows *not all of
them were*, and *some, if not all, of the students were there* does not, its clausal implicature
that the speaker leaves (23) possible excluding the scalar one. -/
theorem notAll :
    den (info allToSome) 𝐚 = den (info allToSome) (∼𝐛 ⟹ 𝐚) ∧
      den (info allToSome) (K () ∼𝐛) ∈ update (info allToSome) allSome ∅ 𝐚 ∧
      den (info allToSome) (K () ∼𝐛) ∉ update (info allToSome) allSome ∅ (∼𝐛 ⟹ 𝐚) := by
  set M := info allToSome
  -- the speaker knows that some but not all were there
  let w : World allToSome := ⟨((true, false), {(true, false)}), by decide⟩
  -- the speaker knows that some were there and leaves open whether all were
  let w' : World allToSome := ⟨((true, true), {(true, false), (true, true)}), by decide⟩
  refine ⟨by ext v; revert v; decide, ?_, ?_⟩
  · rw [update_eq M (con_scalar M (w := w) (by decide) ((forall_mem_clausal M).2 (by decide))
      ((forall_mem_scalar M).2 (by decide)))]
    exact .inr ⟨𝐚, by decide, 𝐛, rfl, subset_rfl, rfl⟩
  · refine K_neg_not_mem_update M (con_clausal M (w := w') (by decide)
      ((forall_mem_clausal M).2 (by decide))) ⟨𝐛, by decide, by decide, by decide, .inl rfl⟩
      fun x hx ↦ ?_
    simp only [mem_union, mem_insert_iff, mem_empty_iff_false, or_false] at hx
    rcases hx with rfl | hx
    · exact ⟨w', by decide, by decide⟩
    · revert x hx; exact (forall_mem_clausal M).2 (by decide)

/-- The judged readings of (18), (19), (21) and (22): a sentence has the reading *not both* or
*not all* exactly when its update adds the scalar implicature. -/
theorem rows_reading :
    (Examples.ex_18.readings.lookup "not both" = some .acceptable ↔
        den (info .univ) (K () ∼(𝐚 ⋏ 𝐛)) ∈ update (info .univ) andOr ∅ (𝐚 ⋎ 𝐛)) ∧
      (Examples.ex_19.readings.lookup "not both" = some .acceptable ↔
        den (info .univ) (K () ∼(𝐚 ⋏ 𝐛)) ∈ update (info .univ) andOr ∅ (𝐚 ⋎ 𝐛 ⋎ (𝐚 ⋏ 𝐛))) ∧
      (Examples.ex_21.readings.lookup "not all" = some .acceptable ↔
        den (info allToSome) (K () ∼𝐛) ∈ update (info allToSome) allSome ∅ 𝐚) ∧
      (Examples.ex_22.readings.lookup "not all" = some .acceptable ↔
        den (info allToSome) (K () ∼𝐛) ∈ update (info allToSome) allSome ∅ (∼𝐛 ⟹ 𝐚)) :=
  ⟨iff_of_true (by decide) exclusive.2.1, iff_of_false (by decide) exclusive.2.2,
    iff_of_true (by decide) notAll.2.1, iff_of_false (by decide) notAll.2.2⟩

end Gazdar1979
