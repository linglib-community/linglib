module

public import Linglib.Core.ModelTheory.EhrenfeuchtFraisse
public import Mathlib.Data.Set.Card

/-!
# The Ehrenfeucht–Fraïssé game on monadic structures

`[UPSTREAM]` candidate. A language is monadic when its only symbols are unary relation symbols, so
each element of a structure has a unary type, the set of symbols holding of it. On monadic
structures the Ehrenfeucht–Fraïssé game is decided by counting: duplicator answers a played
element by its partner and a fresh element by a fresh element of the same type, which is possible
while, for each type, the unplayed elements on the two sides are equinumerous or both at least the
number of rounds left. Conversely, spoiler wins when a type is scarcer on one side, so two
structures for a finite monadic signature are `t`-equivalent exactly when, for each unary type,
their elements of that type are equinumerous or both at least `t`, the first-order case of Peters
and Westerståhl's Theorem 13. With the Hintikka characterization of definability, this makes a
class first-order definable iff it is invariant under these counts up to some threshold, which is
van Benthem's characterization of the first-order definable determiners.

## Main definitions

* `FirstOrder.Language.IsMonadic`: the language has only unary relation symbols.
* `FirstOrder.Language.monadic`, `FirstOrder.Language.monadicStructure`: the monadic language on
  an index type and the structure given by a family of predicates.
* `FirstOrder.Language.unaryType`: the unary relation symbols holding of an element.
* `FirstOrder.Language.MonadicMatch`: tuples with the same equality pattern and unary types.

## Main results

* `FirstOrder.Language.MonadicMatch.duplicatorWins`: the counting strategy wins the game.
* `FirstOrder.Language.DuplicatorWins.min_encard_eq`: conversely, any winning position satisfies the
  counting condition.
* `FirstOrder.Language.elementarilyEquivalentUpTo_iff_min_encard_eq`,
  `FirstOrder.Language.elementarilyEquivalentUpTo_monadicStructure_iff`: the `t`-equivalence
  criterion.
* `FirstOrder.Language.foDefinable_iff_exists_min_encard_eq`: a class of structures for a finite
  monadic signature is definable within `K` iff it is invariant under agreement of the unary type
  counts up to some threshold.

## References

* [peters-westerstahl-2006]
* [van-benthem-1984]
-/

@[expose] public section

universe u v w w'

namespace FirstOrder.Language

open BoundedFormula CategoryTheory

variable (L : Language.{u, v}) {M : Type w} {N : Type w'} [L.Structure M] [L.Structure N]

/-- A language is monadic when its only symbols are unary relation symbols. -/
class IsMonadic : Prop where
  isEmpty_functions : ∀ n, IsEmpty (L.Functions n)
  isEmpty_relations : ∀ n, n ≠ 1 → IsEmpty (L.Relations n)

instance (priority := 100) IsMonadic.isRelational [L.IsMonadic] : L.IsRelational :=
  IsMonadic.isEmpty_functions

/-- The relation symbols of the monadic language on `ι`, one unary symbol for each `i : ι`. -/
inductive monadicRel (ι : Type v) : ℕ → Type v
  | pred (i : ι) : monadicRel ι 1

/-- The monadic language with one unary relation symbol for each `i : ι`. -/
protected def monadic (ι : Type v) : Language.{0, v} := ⟨fun _ => Empty, monadicRel ι⟩

instance {ι : Type v} : (Language.monadic ι).IsMonadic where
  isEmpty_functions _ := inferInstanceAs (IsEmpty Empty)
  isEmpty_relations _ hl := ⟨fun r => by cases r; exact hl rfl⟩

instance {ι : Type v} [Finite ι] : Finite (Language.monadic ι).Symbols := by
  have : Finite (Σ l, (Language.monadic ι).Relations l) :=
    Finite.of_surjective (fun i : ι => (⟨1, .pred i⟩ : Σ l, (Language.monadic ι).Relations l))
      fun ⟨_, .pred i⟩ => ⟨i, rfl⟩
  unfold Symbols
  infer_instance

/-- The unary type of `a` is the set of unary relation symbols that hold of it. -/
def unaryType (a : M) : L.Relations 1 → Prop := fun R => Structure.RelMap R ![a]

/-- Two tuples match when they have the same equality pattern and corresponding entries have the
same unary type, so that they form a partial isomorphism between monadic structures. -/
structure MonadicMatch {n : ℕ} (v : Fin n → M) (w : Fin n → N) : Prop where
  eq_iff : ∀ i j, v i = v j ↔ w i = w j
  unaryType_eq : ∀ i, L.unaryType (v i) = L.unaryType (w i)

section monadicStructure

variable {ι : Type v} (M)

/-- The structure on `M` interpreting each symbol `pred i` as the predicate `P i`. -/
@[instance_reducible]
def monadicStructure (P : ι → M → Prop) : (Language.monadic ι).Structure M where
  RelMap | .pred i => fun x => P i (x 0)

variable {M} {P : ι → M → Prop} {Q : ι → N → Prop}

@[simp] theorem relMap_monadicStructure (i : ι) (x : Fin 1 → M) :
    @Structure.RelMap _ M (monadicStructure M P) 1 (.pred i) x ↔ P i (x 0) := Iff.rfl

theorem unaryType_monadicStructure_eq_iff (a : M) (S : (Language.monadic ι).Relations 1 → Prop) :
    @unaryType _ M (monadicStructure M P) a = S ↔ ∀ i, P i a ↔ S (.pred i) :=
  ⟨fun h i => Iff.of_eq (congrFun h (.pred i)),
    fun h => funext fun | .pred i => propext (h i)⟩

/-- A bijection carrying each predicate `P i` to `Q i` is an isomorphism of the monadic
structures. -/
def monadicStructureEquiv (e : M ≃ N) (h : ∀ i x, Q i (e x) ↔ P i x) :
    @Language.Equiv (Language.monadic ι) M N (monadicStructure M P) (monadicStructure N Q) :=
  @Language.Equiv.mk _ M N (monadicStructure M P) (monadicStructure N Q) e
    (fun f => isEmptyElim f) (fun | .pred i => fun x => h i (x 0))

end monadicStructure

variable {L} {n : ℕ} {v : Fin n → M} {w : Fin n → N}

private theorem sdiff_range_snoc (s : Set M) (v : Fin n → M) (a : M) :
    s \ Set.range (Fin.snoc v a) = (s \ Set.range v) \ {a} := by
  rw [Fin.range_snoc, Set.insert_eq, Set.union_comm, ← Set.sdiff_sdiff]

private theorem min_eq_of_succ {j : ℕ} {x y : ℕ∞}
    (h : min ((j + 1 : ℕ) : ℕ∞) x = min ((j + 1 : ℕ) : ℕ∞) y) :
    min (j : ℕ∞) x = min (j : ℕ∞) y := by
  have hj : (j : ℕ∞) ≤ ((j + 1 : ℕ) : ℕ∞) := by exact_mod_cast j.le_succ
  rw [← min_eq_left hj, min_assoc, h, ← min_assoc, min_eq_left hj]

private theorem min_eq_of_succ_add_one {j : ℕ} {x y : ℕ∞}
    (h : min ((j + 1 : ℕ) : ℕ∞) (x + 1) = min ((j + 1 : ℕ) : ℕ∞) (y + 1)) :
    min (j : ℕ∞) x = min (j : ℕ∞) y := by
  push_cast at h
  rw [min_add_add_right, min_add_add_right] at h
  exact (WithTop.add_right_inj WithTop.one_ne_top).1 h

namespace MonadicMatch

theorem symm (h : L.MonadicMatch v w) : L.MonadicMatch w v :=
  ⟨fun i j => (h.eq_iff i j).symm, fun i => (h.unaryType_eq i).symm⟩

theorem snoc (h : L.MonadicMatch v w) {a : M} {b : N} (heq : ∀ i, v i = a ↔ w i = b)
    (hab : L.unaryType a = L.unaryType b) : L.MonadicMatch (Fin.snoc v a) (Fin.snoc w b) := by
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
      simp only [Fin.snoc_last, Fin.snoc_castSucc, h.eq_iff, heq, iff_self]
    exact eq_comm.trans ((heq _).trans eq_comm)
  · induction i using Fin.lastCases <;> simp [hab, h.unaryType_eq]

theorem exists_snoc {j : ℕ} (h : L.MonadicMatch v w)
    (hc : ∀ S, min ((j + 1 : ℕ) : ℕ∞) (L.unaryType ⁻¹' {S} \ Set.range v).encard =
      min ((j + 1 : ℕ) : ℕ∞) (L.unaryType ⁻¹' {S} \ Set.range w).encard) (a : M) :
    ∃ b, L.MonadicMatch (Fin.snoc v a) (Fin.snoc w b) ∧
      ∀ S, min (j : ℕ∞) (L.unaryType ⁻¹' {S} \ Set.range (Fin.snoc v a)).encard =
        min (j : ℕ∞) (L.unaryType ⁻¹' {S} \ Set.range (Fin.snoc w b)).encard := by
  by_cases ha : a ∈ Set.range v
  · obtain ⟨i, rfl⟩ := ha
    refine ⟨w i, h.snoc (fun _ => h.eq_iff _ _) (h.unaryType_eq i), fun S => ?_⟩
    rw [sdiff_range_snoc, sdiff_range_snoc, Set.sdiff_singleton_eq_self fun hx => hx.2 ⟨i, rfl⟩,
      Set.sdiff_singleton_eq_self fun hx => hx.2 ⟨i, rfl⟩]
    exact min_eq_of_succ (hc S)
  · have haf : a ∈ L.unaryType ⁻¹' {L.unaryType a} \ Set.range v := ⟨rfl, ha⟩
    obtain ⟨b, hbf⟩ : (L.unaryType ⁻¹' {L.unaryType a} \ Set.range w).Nonempty := by
      rw [← Set.one_le_encard_iff_nonempty]
      have h1 : (1 : ℕ∞) ≤
          min ((j + 1 : ℕ) : ℕ∞) (L.unaryType ⁻¹' {L.unaryType a} \ Set.range v).encard :=
        le_min (by exact_mod_cast Nat.le_add_left 1 j) (Set.one_le_encard_iff_nonempty.2 ⟨a, haf⟩)
      exact (hc _ ▸ h1).trans (min_le_right _ _)
    have hb : L.unaryType b = L.unaryType a := hbf.1
    refine ⟨b, h.snoc (fun i => iff_of_false (fun e => ha ⟨i, e⟩) fun e => hbf.2 ⟨i, e⟩) hb.symm,
      fun S => ?_⟩
    rw [sdiff_range_snoc, sdiff_range_snoc]
    by_cases hS : S = L.unaryType a
    · subst hS
      have := hc (L.unaryType a)
      rw [← Set.encard_sdiff_singleton_add_one haf,
        ← Set.encard_sdiff_singleton_add_one hbf] at this
      exact min_eq_of_succ_add_one this
    · rw [Set.sdiff_singleton_eq_self fun hx => hS (hx.1 : _ = S).symm,
        Set.sdiff_singleton_eq_self fun hx => hS ((hx.1 : _ = S).symm.trans hb)]
      exact min_eq_of_succ (hc S)

variable [L.IsMonadic]

theorem realize_iff_of_isAtomic (h : L.MonadicMatch v w) {φ : L.BoundedFormula Empty n}
    (hφ : φ.IsAtomic) : φ.Realize default v ↔ φ.Realize default w := by
  have hvar : ∀ t : L.Term (Empty ⊕ Fin n), ∃ i, t = &i := by
    rintro (⟨x | i⟩ | ⟨f, _⟩)
    exacts [x.elim, ⟨i, rfl⟩, isEmptyElim f]
  cases hφ with
  | equal t₁ t₂ =>
    obtain ⟨i, rfl⟩ := hvar t₁
    obtain ⟨j, rfl⟩ := hvar t₂
    exact h.eq_iff i j
  | @rel l R ts =>
    obtain rfl : l = 1 := by_contra fun hl => (IsMonadic.isEmpty_relations l hl).elim R
    obtain ⟨i, hi⟩ := hvar (ts 0)
    have hv : (fun k => (ts k).realize (Sum.elim default v)) = ![v i] := by
      funext k; obtain rfl := Subsingleton.elim k 0; simp [hi]
    have hw : (fun k => (ts k).realize (Sum.elim default w)) = ![w i] := by
      funext k; obtain rfl := Subsingleton.elim k 0; simp [hi]
    simp only [BoundedFormula.Realize, Relations.boundedFormula]
    rw [hv, hw]
    exact Iff.of_eq (congrFun (h.unaryType_eq i) R)

/-- In a monadic language the counting strategy wins `j` rounds from matched tuples when, for
every unary type, the unplayed elements of that type are equinumerous on the two sides or both at
least `j`. -/
theorem duplicatorWins : ∀ {j n : ℕ} {v : Fin n → M} {w : Fin n → N}, L.MonadicMatch v w →
    (∀ S, min (j : ℕ∞) (L.unaryType ⁻¹' {S} \ Set.range v).encard =
      min (j : ℕ∞) (L.unaryType ⁻¹' {S} \ Set.range w).encard) →
    L.DuplicatorWins j v w
  | 0, _, _, _, h, _ => fun _ hφ => h.realize_iff_of_isAtomic hφ
  | _ + 1, _, _, _, h, hc =>
    ⟨fun _ hφ => h.realize_iff_of_isAtomic hφ,
      fun a => let ⟨b, hb, hbc⟩ := h.exists_snoc hc a; ⟨b, duplicatorWins hb hbc⟩,
      fun b => let ⟨a, ha, hac⟩ := h.symm.exists_snoc (fun S => (hc S).symm) b
        ⟨a, duplicatorWins ha.symm fun S => (hac S).symm⟩⟩

end MonadicMatch

/-- Two structures for a monadic language are `t`-equivalent when, for every unary type, their
elements of that type are equinumerous or both at least `t` ([peters-westerstahl-2006]
Theorem 13 with condition (13.7), first-order case). -/
theorem elementarilyEquivalentUpTo_of_min_encard_eq [L.IsMonadic] {t : ℕ}
    (h : ∀ S, min (t : ℕ∞) (L.unaryType ⁻¹' {S} : Set M).encard =
      min (t : ℕ∞) (L.unaryType ⁻¹' {S} : Set N).encard) :
    M ≅[L, t] N :=
  DuplicatorWins.elementarilyEquivalentUpTo <|
    MonadicMatch.duplicatorWins ⟨fun i => i.elim0, fun i => i.elim0⟩ fun S => by
      simpa [Set.range_eq_empty] using h S

namespace DuplicatorWins

theorem monadicMatch {k : ℕ} (h : L.DuplicatorWins k v w) : L.MonadicMatch v w where
  eq_iff i j := h.realize_iff_of_isAtomic (φ := (&i).bdEqual &j) (.equal _ _)
  unaryType_eq i := funext fun R => propext <| by
    simpa [unaryType] using h.realize_iff_of_isAtomic (φ := R.boundedFormula₁ &i) (.rel _ _)

theorem exists_mem_sdiff_range {k : ℕ} (h : L.DuplicatorWins (k + 1) v w) {S : L.Relations 1 → Prop}
    {a : M} (ha : a ∈ L.unaryType ⁻¹' {S} \ Set.range v) :
    ∃ b ∈ L.unaryType ⁻¹' {S} \ Set.range w, L.DuplicatorWins k (Fin.snoc v a) (Fin.snoc w b) := by
  obtain ⟨b, hb⟩ := h.forth a
  have hm := hb.monadicMatch
  refine ⟨b, ⟨?_, fun ⟨i, hi⟩ => ha.2 ⟨i, ?_⟩⟩, hb⟩
  · have := hm.unaryType_eq (Fin.last n)
    simp only [Fin.snoc_last] at this
    exact (this.symm.trans ha.1 : L.unaryType b = S)
  · simpa [hi] using (hm.eq_iff i.castSucc (Fin.last n)).2

/-- At a winning position for `j` rounds, the unplayed elements of each unary type are
equinumerous on the two sides or both at least `j`. -/
theorem min_encard_eq : ∀ {j n : ℕ} {v : Fin n → M} {w : Fin n → N}, L.DuplicatorWins j v w →
    ∀ S, min (j : ℕ∞) (L.unaryType ⁻¹' {S} \ Set.range v).encard =
      min (j : ℕ∞) (L.unaryType ⁻¹' {S} \ Set.range w).encard
  | 0, _, _, _, _, _ => by simp
  | j + 1, _, v, w, h, S => by
    rcases (L.unaryType ⁻¹' {S} \ Set.range v).eq_empty_or_nonempty with hv | ⟨a, ha⟩
    · rcases (L.unaryType ⁻¹' {S} \ Set.range w).eq_empty_or_nonempty with hw | ⟨b, hb⟩
      · simp [hv, hw]
      · obtain ⟨a, ha, -⟩ := h.symm.exists_mem_sdiff_range hb
        exact absurd (hv ▸ ha) (Set.notMem_empty a)
    · obtain ⟨b, hb, hab⟩ := h.exists_mem_sdiff_range ha
      have := min_encard_eq hab S
      rw [sdiff_range_snoc, sdiff_range_snoc] at this
      rw [← Set.encard_sdiff_singleton_add_one ha, ← Set.encard_sdiff_singleton_add_one hb]
      push_cast
      rw [min_add_add_right, min_add_add_right, this]

end DuplicatorWins

/-- Two structures for a finite monadic signature are `t`-equivalent iff, for every unary type,
their elements of that type are equinumerous or both at least `t` ([peters-westerstahl-2006]
Theorem 13 with condition (13.7), first-order case). -/
theorem elementarilyEquivalentUpTo_iff_min_encard_eq [L.IsMonadic] [Finite L.Symbols] {t : ℕ} :
    (M ≅[L, t] N) ↔ ∀ S, min (t : ℕ∞) (L.unaryType ⁻¹' {S} : Set M).encard =
      min (t : ℕ∞) (L.unaryType ⁻¹' {S} : Set N).encard :=
  ⟨fun h S => by
    simpa [Set.range_eq_empty] using
      (elementarilyEquivalentUpTo_iff_duplicatorWins.1 h).min_encard_eq S,
    elementarilyEquivalentUpTo_of_min_encard_eq⟩

/-- A class of structures for a finite monadic signature is first-order definable within `K` iff,
for some threshold `n`, it is invariant within `K` under agreement of the unary type counts up to
`n`; for two unary predicates this is [van-benthem-1984] Theorem 6.1. -/
theorem foDefinable_iff_exists_min_encard_eq [L.IsMonadic] [Finite L.Symbols]
    {K P : Set (Bundled.{w} L.Structure)} :
    L.FODefinable K P ↔ ∃ n : ℕ, ∀ M ∈ K, ∀ N ∈ K,
      (∀ S, min (n : ℕ∞) (L.unaryType ⁻¹' {S} : Set M).encard =
        min (n : ℕ∞) (L.unaryType ⁻¹' {S} : Set N).encard) → M ∈ P → N ∈ P := by
  simp only [foDefinable_iff_exists_elementarilyEquivalentUpTo,
    elementarilyEquivalentUpTo_iff_min_encard_eq]

/-- Two monadic structures `(M, P)` and `(N, Q)` over a finite index type are `t`-equivalent iff
each part of the partition by the predicates, the elements satisfying exactly the predicates
selected by `S`, has the same size in both or at least `t` elements in both
([peters-westerstahl-2006] Theorem 13 with condition (13.7), first-order case). -/
theorem elementarilyEquivalentUpTo_monadicStructure_iff {ι : Type v} [Finite ι]
    {P : ι → M → Prop} {Q : ι → N → Prop} {t : ℕ} :
    @ElementarilyEquivalentUpTo _ t M N (monadicStructure M P) (monadicStructure N Q) ↔
      ∀ S : ι → Prop, min (t : ℕ∞) {x | ∀ i, P i x ↔ S i}.encard =
        min (t : ℕ∞) {y | ∀ i, Q i y ↔ S i}.encard := by
  have hM (S : (Language.monadic ι).Relations 1 → Prop) :
      @unaryType _ M (monadicStructure M P) ⁻¹' {S} = {x | ∀ i, P i x ↔ S (.pred i)} :=
    Set.ext fun x => unaryType_monadicStructure_eq_iff x S
  have hN (S : (Language.monadic ι).Relations 1 → Prop) :
      @unaryType _ N (monadicStructure N Q) ⁻¹' {S} = {y | ∀ i, Q i y ↔ S (.pred i)} :=
    Set.ext fun y => unaryType_monadicStructure_eq_iff y S
  refine (@elementarilyEquivalentUpTo_iff_min_encard_eq _ M N (monadicStructure M P)
    (monadicStructure N Q) _ _ t).trans ⟨fun h S => ?_, fun h S => ?_⟩
  · simpa only [hM, hN] using h fun | .pred i => S i
  · simpa only [hM, hN] using h fun i => S (.pred i)

end FirstOrder.Language
