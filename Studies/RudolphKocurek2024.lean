module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Core.ModelTheory.LanguageMap
public import Linglib.Core.ModelTheory.Semantics
public import Mathlib.Order.Antisymmetrization
public import Mathlib.Order.Defs.Unbundled
public import Linglib.Logic.ComparativeProbability.WorldOrdering
public import Linglib.Semantics.Degree.Delineation

/-!
# Rudolph and Kocurek (2024): Metalinguistic Gradability

Truth is relative to a semantic ordering, a total preorder ranking interpretations by the strength
of a speaker's commitment to them, together with an interpretation and a world. *A more than B*
holds when some interpretation ranked no higher than the index makes A true and B false and
outranks every one that makes B true and A false, and the equative is the failure of both
comparatives. Degree modifiers come from a distance function on interpretations, the conditional
restricts the ordering to the antecedent's interpretations, and under No Reversal the comparative
is Klein's delineation comparative.

The supplement strengthens the comparative so that the equative becomes transitive, and shows that
metalinguistic degrees, the classes of sets of interpretations under the revised equative, form a
bounded linear order on which the revised comparative is the comparative of degree semantics.

## Main results

* `comp_trans`, `accepted_comp_of_accepted`: the comparative is transitive, and a sentence with
  its negated rival entails it for acceptance but not for truth.
* `evalVery_iff`: *very A* is truth at every reasonably close interpretation.
* `evalRevised_equi_trans`: the revised equative is transitive, unlike the basic one.
* `mc_iff_formulaDeg_lt`: the revised comparative compares metalinguistic degrees.

## Implementation notes

* An interpretation is a world-indexed family of first-order structures. The comparative is the
  strict domination lift of Holliday and Icard on the cone below the index, which *much more*
  shares with a coarser dominance relation.
* `SemanticOrdering` bundles a total preorder as data, since a common ground is a set of pairs of
  an ordering and a world.
* The supplement's revised comparative and equative are clauses on predicates over the cone
  (`RevisedComp`, `RevisedEqui`). The revised semantics applies them to truth sets and the degree
  theory to sets of interpretations, the two uses the supplement says mirror each other. Degrees
  are classes of arbitrary sets, which the clauses read only on the cone.
* Finite models rank interpretations by a map into `ℕ` and list each predicate's extension.

## TODO

* The paper states *if A then more A than not* (its Observation M1) for every `A`, but the
  consequent evaluates `A` under the restricted ordering; `mcond_comp_not` proves it for `A` free
  of the comparative.
* The supplement's semantics for nontotal orderings and its quantifiers for metalinguistic
  superlatives are not formalized.

## References

* [R. E. Rudolph and A. W. Kocurek, *Metalinguistic gradability* (2024)][rudolph-kocurek-2024]
* [A. W. Kocurek, *Supplement to "Metalinguistic gradability"* (2024)][kocurek-2024-supplement]
* [W. H. Holliday and T. F. Icard III, *Measure Semantics and Qualitative Semantics for Epistemic
  Modals* (2013)][holliday-icard-2013]
* [E. Klein, *A Semantics for Positive and Comparative Adjectives* (1980)][klein-1980]
* [D. Lewis, *Counterfactuals* (1973)][lewis-1973b]
* [A. Kratzer, *Modals and Conditionals* (2012)][kratzer-2012]
* [J. Y. Halpern, *Reasoning about Uncertainty* (2003)][halpern-2003]
* [S. Yalcin, *Epistemic Modals* (2007)][yalcin-2007]
-/

@[expose] public section

namespace RudolphKocurek2024

open FirstOrder FirstOrder.Language
open ComparativeProbability

/-! ### Semantic orderings -/

/-- A semantic ordering is a total preorder on interpretations, the paper's ranking of
interpretations by strength of interpretive commitment. It is a structure and not a `Preorder`
instance, because a common ground is a set of pairs of an ordering and a world, so orderings
are data. The strict part is kept transparent so that finite models decide. -/
structure SemanticOrdering (I : Type*) where
  /-- The ranking, where `le a b` means that `a` is ranked no higher than `b`. -/
  le : I → I → Prop
  /-- The ranking is reflexive and transitive. -/
  isPreorder : IsPreorder I le
  /-- Any two interpretations are comparable. -/
  total : Std.Total le

attribute [instance] SemanticOrdering.isPreorder SemanticOrdering.total

namespace SemanticOrdering

variable {I : Type*} (ord : SemanticOrdering I)

theorem le_refl (a : I) : ord.le a a := Std.Refl.refl a

theorem le_trans (a b c : I) : ord.le a b → ord.le b c → ord.le a c := IsTrans.trans a b c

theorem le_total (a b : I) : ord.le a b ∨ ord.le b a := Std.Total.total a b

/-- The strict ordering ranks `a` strictly below `b`. -/
def lt (a b : I) : Prop := ord.le a b ∧ ¬ ord.le b a

instance decRelLt [DecidableRel ord.le] : DecidableRel ord.lt := fun _ _ ↦
  inferInstanceAs (Decidable (_ ∧ _))

theorem lt_of_le_of_lt {a b c : I} (h : ord.le a b) (h' : ord.lt b c) : ord.lt a c :=
  ⟨ord.le_trans a b c h h'.1, fun hca ↦ h'.2 (ord.le_trans c a b hca h)⟩

theorem lt_of_lt_of_le {a b c : I} (h : ord.lt a b) (h' : ord.le b c) : ord.lt a c :=
  ⟨ord.le_trans a b c h.1 h', fun hca ↦ h.2 (ord.le_trans b c a h' hca)⟩

theorem lt_irrefl (a : I) : ¬ ord.lt a a := fun h ↦ h.2 (ord.le_refl a)

theorem le_of_not_lt {a b : I} (h : ¬ ord.lt a b) : ord.le b a :=
  Classical.byContradiction fun hba ↦ h ⟨(ord.le_total a b).resolve_right hba, hba⟩

theorem exists_le_max {S : Set I} (hS : S.Finite) (hne : S.Nonempty) :
    ∃ m ∈ S, ∀ s ∈ S, ord.le s m := by
  let : Preorder I := { le := ord.le, le_refl := ord.le_refl, le_trans := ord.le_trans }
  obtain ⟨m, hm, hmax⟩ := hS.exists_maximal hne
  exact ⟨m, hm, fun s hs ↦ (ord.le_total s m).elim id (hmax hs)⟩

/-- Two interpretations are equivalent when each is ranked no higher than the other. -/
abbrev equiv (a b : I) : Prop := AntisymmRel ord.le a b

instance decRelEquiv [DecidableRel ord.le] : DecidableRel ord.equiv := fun _ _ ↦
  inferInstanceAs (Decidable (_ ∧ _))

/-- The semantic ordering that ranks interpretations by a map into a linear order, the convenient
form for a concrete finite model. -/
def ofRank {α : Type*} [LinearOrder α] (r : I → α) : SemanticOrdering I where
  le a b := r a ≤ r b
  isPreorder := { refl := fun a ↦ _root_.le_refl (r a), trans := fun _ _ _ ↦ _root_.le_trans }
  total := ⟨fun a b ↦ _root_.le_total (r a) (r b)⟩

instance {α : Type*} [LinearOrder α] (r : I → α) : DecidableRel (ofRank r).le := fun a b ↦
  inferInstanceAs (Decidable (r a ≤ r b))

/-- An interpretation is top-ranked when none is ranked strictly above it. -/
def IsMaximal (x : I) : Prop := ∀ y, ¬ ord.lt x y

instance [Fintype I] [DecidableRel ord.le] (x : I) : Decidable (ord.IsMaximal x) := by
  unfold IsMaximal; infer_instance

/-- A predicate is accepted when it holds throughout the top-ranked interpretations. -/
def AcceptedAt (A : I → Prop) : Prop := ∀ x, ord.IsMaximal x → A x

instance [Fintype I] [DecidableRel ord.le] (A : I → Prop) [DecidablePred A] :
    Decidable (ord.AcceptedAt A) := by
  unfold AcceptedAt; infer_instance

end SemanticOrdering

/-! ### The comparative language -/

section Language

variable {W : Type*} {ge_w : W → W → Prop}

/-- The ∃∀ clause of Lewis's comparative possibility, localized to the cone below an index and
comparing difference sets, which is the shape of Kratzer's revised lifting. The dominance relation
is a parameter, so that the comparative is the clause at the strict ordering and *much more* is the
clause at "far below". -/
def ConeStrictLift (le below : W → W → Prop) (P Q : W → Prop) (i : W) : Prop :=
  ∃ a, le a i ∧ P a ∧ ¬ Q a ∧ ∀ b, le b i → Q b → ¬ P b → below b a

instance (le below : W → W → Prop) (P Q : W → Prop) (i : W) [Fintype W]
    [DecidableRel le] [DecidableRel below] [DecidablePred P] [DecidablePred Q] :
    Decidable (ConeStrictLift le below P Q i) := by
  unfold ConeStrictLift; infer_instance

/-- The cone difference set at `i` consists of the members of the cone where `P` holds and `Q`
fails. -/
def coneDiff (le : W → W → Prop) (P Q : W → Prop) (i : W) : Set W :=
  {x | le x i ∧ P x ∧ ¬ Q x}

theorem strict_lewisLift_iff_below {below : W → W → Prop}
    (hTotal : ∀ a b, ge_w a b ∨ ge_w b a)
    (hBelow : ∀ a b, below a b ↔ ge_w b a ∧ ¬ ge_w a b) (A B : Set W) :
    Strict (LewisLift ge_w) A B ↔ ∃ a ∈ A, ∀ b ∈ B, below b a := by
  rw [strict_lewisLift_iff hTotal]
  exact exists_congr fun a ↦ and_congr_right fun _ ↦ forall₂_congr fun b _ ↦ (hBelow b a).symm

theorem coneStrictLift_iff_strict_lewisLift {le below : W → W → Prop}
    (hTotal : ∀ a b, ge_w a b ∨ ge_w b a)
    (hBelow : ∀ a b, below a b ↔ ge_w b a ∧ ¬ ge_w a b) (P Q : W → Prop) (i : W) :
    ConeStrictLift le below P Q i ↔
      Strict (LewisLift ge_w) (coneDiff le P Q i) (coneDiff le Q P i) := by
  rw [strict_lewisLift_iff_below hTotal hBelow]
  unfold ConeStrictLift coneDiff
  simp only [Set.mem_ofPred_eq, and_imp, and_assoc]

variable (le : W → W → Prop) (P Q : W → Prop) (i : W)

/-- The revised comparative clause of the supplement. Some member of the cone below `i` makes `P`
true and `Q` false, ranks strictly above every member making `Q` true and `P` false, and ranks
strictly above either every member making both true or every member making both false. -/
def RevisedComp : Prop :=
  ∃ a, le a i ∧ P a ∧ ¬ Q a ∧ (∀ b, le b i → Q b → ¬ P b → Strict le b a) ∧
    ((∀ b, le b i → P b → Q b → Strict le b a) ∨ (∀ b, le b i → ¬ P b → ¬ Q b → Strict le b a))

/-- The revised equative clause of the supplement. Either every member of the cone below `i` making
exactly one of `P` and `Q` true is matched, at least as high, by one making only the other true, or
every such member is matched, at least as high, both by one making both true and by one making
both false. -/
def RevisedEqui : Prop :=
  ((∀ a, le a i → P a → ¬ Q a → ∃ b, le b i ∧ Q b ∧ ¬ P b ∧ le a b) ∧
    (∀ a, le a i → Q a → ¬ P a → ∃ b, le b i ∧ P b ∧ ¬ Q b ∧ le a b)) ∨
  ∀ a, le a i → (P a ↔ ¬ Q a) →
    (∃ b, le b i ∧ P b ∧ Q b ∧ le a b) ∧ ∃ b, le b i ∧ ¬ P b ∧ ¬ Q b ∧ le a b

instance [Fintype W] [DecidableRel le] [DecidablePred P] [DecidablePred Q] :
    Decidable (RevisedComp le P Q i) := by
  unfold RevisedComp; infer_instance

variable {le P Q i}

theorem revisedComp_iff : RevisedComp le P Q i ↔ ∃ a, le a i ∧ P a ∧ ¬ Q a ∧
    ((∀ b, le b i → Q b → Strict le b a) ∨ (∀ b, le b i → ¬ P b → Strict le b a)) := by
  refine exists_congr fun a ↦ and_congr_right fun _ ↦ and_congr_right fun _ ↦
    and_congr_right fun _ ↦ ⟨?_, ?_⟩
  · rintro ⟨hd, hc | hc⟩
    · exact .inl fun b hb hQ ↦ (em (P b)).elim (hc b hb · hQ) (hd b hb hQ)
    · exact .inr fun b hb hP ↦ (em (Q b)).elim (hd b hb · hP) (hc b hb hP)
  · rintro (h | h)
    · exact ⟨fun b hb hQ _ ↦ h b hb hQ, .inl fun b hb _ hQ ↦ h b hb hQ⟩
    · exact ⟨fun b hb _ hP ↦ h b hb hP, .inr fun b hb hP _ ↦ h b hb hP⟩

theorem coneStrictLift_iff_revisedComp :
    ConeStrictLift le (Strict le) P Q i ↔
      RevisedComp le (fun a ↦ P a ∧ ¬ Q a) (fun a ↦ Q a ∧ ¬ P a) i :=
  exists_congr fun _ ↦ and_congr_right fun _ ↦
    ⟨fun ⟨hP, hQ, hd⟩ ↦ ⟨⟨hP, hQ⟩, fun h ↦ hQ h.1, fun b hb h _ ↦ hd b hb h.1 h.2,
        .inl fun _ _ h h' ↦ (h'.2 h.1).elim⟩,
      fun ⟨⟨hP, hQ⟩, _, hd, _⟩ ↦ ⟨hP, hQ, fun b hb hQ hP ↦ hd b hb ⟨hQ, hP⟩ fun h ↦ hP h.1⟩⟩

theorem revisedComp_iff_coneStrictLift :
    RevisedComp le P Q i ↔
      ConeStrictLift le (Strict le) (fun a ↦ P a ∧ ¬ Q a) (fun a ↦ ¬ P a) i ∨
        ConeStrictLift le (Strict le) (fun a ↦ P a ∧ ¬ Q a) Q i := by
  rw [revisedComp_iff]
  refine ⟨fun ⟨a, ha, hP, hQ, h⟩ ↦ h.elim (fun h ↦ .inr ?_) (fun h ↦ .inl ?_),
    fun h ↦ h.elim (fun ⟨a, ha, ⟨hP, hQ⟩, _, h⟩ ↦ ⟨a, ha, hP, hQ, .inr fun b hb hP ↦ ?_⟩)
      (fun ⟨a, ha, ⟨hP, hQ⟩, _, h⟩ ↦ ⟨a, ha, hP, hQ, .inl fun b hb hQ ↦ ?_⟩)⟩
  · exact ⟨a, ha, ⟨hP, hQ⟩, hQ, fun b hb hQ _ ↦ h b hb hQ⟩
  · exact ⟨a, ha, ⟨hP, hQ⟩, not_not.2 hP, fun b hb hP _ ↦ h b hb hP⟩
  · exact h b hb hP fun h ↦ hP h.1
  · exact h b hb hQ fun h ↦ h.2 hQ

theorem RevisedComp.congr {P' Q' : W → Prop} (hP : ∀ a, le a i → (P a ↔ P' a))
    (hQ : ∀ a, le a i → (Q a ↔ Q' a)) : RevisedComp le P Q i ↔ RevisedComp le P' Q' i :=
  exists_congr fun a ↦ and_congr_right fun ha ↦ by simp +contextual only [hP, hQ, ha]

theorem RevisedEqui.congr {P' Q' : W → Prop} (hP : ∀ a, le a i → (P a ↔ P' a))
    (hQ : ∀ a, le a i → (Q a ↔ Q' a)) : RevisedEqui le P Q i ↔ RevisedEqui le P' Q' i := by
  have hE (X X' : W → Prop) (h : ∀ b, le b i → (X b ↔ X' b)) :
      (∃ b, le b i ∧ X b) ↔ ∃ b, le b i ∧ X' b :=
    exists_congr fun b ↦ and_congr_right (h b)
  unfold RevisedEqui
  refine or_congr (and_congr (forall₂_congr fun a ha ↦ ?_) (forall₂_congr fun a ha ↦ ?_))
    (forall₂_congr fun a ha ↦ ?_) <;> rw [hP a ha, hQ a ha]
  · exact imp_congr_right fun _ ↦ imp_congr_right fun _ ↦
      hE _ _ fun b hb ↦ by simp only [hP b hb, hQ b hb]
  · exact imp_congr_right fun _ ↦ imp_congr_right fun _ ↦
      hE _ _ fun b hb ↦ by simp only [hP b hb, hQ b hb]
  · exact imp_congr_right fun _ ↦ and_congr (hE _ _ fun b hb ↦ by simp only [hP b hb, hQ b hb])
      (hE _ _ fun b hb ↦ by simp only [hP b hb, hQ b hb])


theorem not_revisedComp_self : ¬ RevisedComp le P P i := fun ⟨_, _, hP, hnP, _⟩ ↦ hnP hP

theorem RevisedEqui.refl : RevisedEqui le P P i :=
  .inl ⟨fun _ _ hP hnP ↦ (hnP hP).elim, fun _ _ hP hnP ↦ (hnP hP).elim⟩

theorem RevisedEqui.symm (h : RevisedEqui le P Q i) : RevisedEqui le Q P i := by
  refine h.imp And.symm fun h a ha hQP ↦ ?_
  obtain ⟨⟨b, hb, hPb, hQb, hab⟩, c, hc, hPc, hQc, hac⟩ := h a ha (by tauto)
  exact ⟨⟨b, hb, hQb, hPb, hab⟩, c, hc, hQc, hPc, hac⟩

theorem RevisedEqui.not_revisedComp (h : RevisedEqui le P Q i) : ¬ RevisedComp le P Q i := by
  rintro ⟨a, ha, hPa, hQa, hd, he⟩
  rcases h with ⟨h, -⟩ | h
  · obtain ⟨b, hb, hQb, hPb, hab⟩ := h a ha hPa hQa
    exact (hd b hb hQb hPb).2 hab
  · obtain ⟨⟨b, hb, hPb, hQb, hab⟩, c, hc, hPc, hQc, hac⟩ := h a ha (iff_of_true hPa hQa)
    exact he.elim (fun he ↦ (he b hb hPb hQb).2 hab) fun he ↦ (he c hc hPc hQc).2 hac

section SemanticOrdering

variable {ord : SemanticOrdering W} {R : W → Prop}

/-- The revised comparative is transitive, the supplement's Fact 4: whichever witness ranks higher
witnesses the composite. -/
theorem RevisedComp.trans (h₁ : RevisedComp ord.le P Q i) (h₂ : RevisedComp ord.le Q R i) :
    RevisedComp ord.le P R i := by
  obtain ⟨m₁, hm₁, hP₁, hQ₁, hd₁, he₁⟩ := h₁
  obtain ⟨m₂, hm₂, hQ₂, hR₂, hd₂, he₂⟩ := h₂
  rcases ord.le_total m₂ m₁ with hle | hle
  · have hR₁ : ¬ R m₁ := fun hR ↦ ord.lt_irrefl m₁ (ord.lt_of_lt_of_le (hd₂ m₁ hm₁ hR hQ₁) hle)
    refine ⟨m₁, hm₁, hP₁, hR₁, fun b hb hR hP ↦ ?_,
      he₁.imp (fun h b hb hP hR ↦ ?_) fun h b hb hP hR ↦ ?_⟩ <;> by_cases hQ : Q b
    exacts [hd₁ b hb hQ hP, ord.lt_of_lt_of_le (hd₂ b hb hR hQ) hle, h b hb hP hQ,
      ord.lt_of_lt_of_le (hd₂ b hb hR hQ) hle, hd₁ b hb hQ hP, h b hb hP hQ]
  · have hP₂ : P m₂ := of_not_not fun hP ↦
      ord.lt_irrefl m₂ (ord.lt_of_lt_of_le (hd₁ m₂ hm₂ hQ₂ hP) hle)
    refine ⟨m₂, hm₂, hP₂, hR₂, fun b hb hR hP ↦ ?_,
      he₂.imp (fun h b hb hP hR ↦ ?_) fun h b hb hP hR ↦ ?_⟩ <;> by_cases hQ : Q b
    exacts [ord.lt_of_lt_of_le (hd₁ b hb hQ hP) hle, hd₂ b hb hR hQ, h b hb hQ hR,
      hd₂ b hb hR hQ, ord.lt_of_lt_of_le (hd₁ b hb hQ hP) hle, h b hb hQ hR]

/-- The revised comparative respects the revised equative on the right, the supplement's Fact 11. -/
theorem RevisedComp.of_revisedEqui_right (h : RevisedComp ord.le P Q i)
    (hQR : RevisedEqui ord.le Q R i) : RevisedComp ord.le P R i := by
  obtain ⟨m, hm, hP, hQ, hd, he | he⟩ := h
  · have hQlt (b) (hb : ord.le b i) (hQb : Q b) : ord.lt b m :=
      (em (P b)).elim (he b hb · hQb) (hd b hb hQb)
    have hlt (b) (hb : ord.le b i) (hR : R b) : ord.lt b m := by
      refine (em (Q b)).elim (hQlt b hb) fun hQb ↦ ?_
      rcases hQR with ⟨-, h⟩ | h
      · obtain ⟨c, hc, hQc, -, hbc⟩ := h b hb hR hQb
        exact ord.lt_of_le_of_lt hbc (hQlt c hc hQc)
      · obtain ⟨⟨c, hc, hQc, -, hbc⟩, -⟩ := h b hb (iff_of_false hQb (not_not.2 hR))
        exact ord.lt_of_le_of_lt hbc (hQlt c hc hQc)
    exact ⟨m, hm, hP, fun hR ↦ ord.lt_irrefl m (hlt m hm hR), fun b hb hR _ ↦ hlt b hb hR,
      .inl fun b hb _ hR ↦ hlt b hb hR⟩
  · have hlt (b) (hb : ord.le b i) (hPb : ¬ P b) : ord.lt b m :=
      (em (Q b)).elim (hd b hb · hPb) (he b hb hPb)
    suffices ∃ a, ord.le a i ∧ ¬ R a ∧ ord.le m a by
      obtain ⟨a, ha, hR, hma⟩ := this
      exact ⟨a, ha, of_not_not fun hPa ↦ (hlt a ha hPa).2 hma, hR,
        fun b hb _ hPb ↦ ord.lt_of_lt_of_le (hlt b hb hPb) hma,
        .inr fun b hb hPb _ ↦ ord.lt_of_lt_of_le (hlt b hb hPb) hma⟩
    by_cases hR : R m
    · rcases hQR with ⟨-, h⟩ | h
      · obtain ⟨c, hc, -, hRc, hmc⟩ := h m hm hR hQ
        exact ⟨c, hc, hRc, hmc⟩
      · obtain ⟨-, c, hc, -, hRc, hmc⟩ := h m hm (iff_of_false hQ (not_not.2 hR))
        exact ⟨c, hc, hRc, hmc⟩
    · exact ⟨m, hm, hR, ord.le_refl m⟩

theorem RevisedComp.of_revisedEqui_left (h : RevisedComp ord.le P Q i)
    (hPR : RevisedEqui ord.le P R i) : RevisedComp ord.le R Q i := by
  obtain ⟨m, hm, hP, hQ, hd, he | he⟩ := h
  · have hQlt (b) (hb : ord.le b i) (hQb : Q b) : ord.lt b m :=
      (em (P b)).elim (he b hb · hQb) (hd b hb hQb)
    suffices ∃ a, ord.le a i ∧ R a ∧ ord.le m a by
      obtain ⟨a, ha, hR, hma⟩ := this
      have hlt (b) (hb : ord.le b i) (hQb : Q b) : ord.lt b a :=
        ord.lt_of_lt_of_le (hQlt b hb hQb) hma
      exact ⟨a, ha, hR, fun hQa ↦ ord.lt_irrefl a (hlt a ha hQa), fun b hb hQb _ ↦ hlt b hb hQb,
        .inl fun b hb _ hQb ↦ hlt b hb hQb⟩
    by_cases hR : R m
    · exact ⟨m, hm, hR, ord.le_refl m⟩
    · rcases hPR with ⟨h, -⟩ | h
      · obtain ⟨c, hc, hRc, -, hmc⟩ := h m hm hP hR
        exact ⟨c, hc, hRc, hmc⟩
      · obtain ⟨⟨c, hc, -, hRc, hmc⟩, -⟩ := h m hm (iff_of_true hP hR)
        exact ⟨c, hc, hRc, hmc⟩
  · have hnP (b) (hb : ord.le b i) (hPb : ¬ P b) : ord.lt b m :=
      (em (Q b)).elim (hd b hb · hPb) (he b hb hPb)
    have hPlt (b) (hb : ord.le b i) (hPb : P b) (hRb : ¬ R b) : ord.lt b m := by
      rcases hPR with ⟨h, -⟩ | h
      · obtain ⟨c, hc, -, hPc, hbc⟩ := h b hb hPb hRb
        exact ord.lt_of_le_of_lt hbc (hnP c hc hPc)
      · obtain ⟨-, c, hc, hPc, -, hbc⟩ := h b hb (iff_of_true hPb hRb)
        exact ord.lt_of_le_of_lt hbc (hnP c hc hPc)
    have hR : R m := of_not_not fun hR ↦ ord.lt_irrefl m (hPlt m hm hP hR)
    refine ⟨m, hm, hR, hQ, fun b hb _ hRb ↦ ?_, .inr fun b hb hRb _ ↦ ?_⟩ <;>
      exact (em (P b)).elim (hPlt b hb · hRb) (hnP b hb)

private theorem revisedEqui_or_revisedComp_of_max {m : W} (hm : ord.le m i) (hP : P m)
    (hQ : ¬ Q m) (hmax : ∀ a, ord.le a i → (P a ↔ ¬ Q a) → ord.le a m) :
    RevisedEqui ord.le P Q i ∨ RevisedComp ord.le P Q i := by
  by_cases hd : ∀ b, ord.le b i → Q b → ¬ P b → ord.lt b m
  · by_cases hc₁ : ∀ b, ord.le b i → P b → Q b → ord.lt b m
    · exact .inr ⟨m, hm, hP, hQ, hd, .inl hc₁⟩
    by_cases hc₂ : ∀ b, ord.le b i → ¬ P b → ¬ Q b → ord.lt b m
    · exact .inr ⟨m, hm, hP, hQ, hd, .inr hc₂⟩
    push Not at hc₁ hc₂
    obtain ⟨c₁, hc₁, hPc₁, hQc₁, hlt₁⟩ := hc₁
    obtain ⟨c₂, hc₂, hPc₂, hQc₂, hlt₂⟩ := hc₂
    exact .inl (.inr fun a ha hPQ ↦
      ⟨⟨c₁, hc₁, hPc₁, hQc₁, ord.le_trans _ _ _ (hmax a ha hPQ) (ord.le_of_not_lt hlt₁)⟩,
        c₂, hc₂, hPc₂, hQc₂, ord.le_trans _ _ _ (hmax a ha hPQ) (ord.le_of_not_lt hlt₂)⟩)
  · push Not at hd
    obtain ⟨c, hc, hQc, hPc, hlt⟩ := hd
    exact .inl (.inl ⟨fun a ha hPa hQa ↦ ⟨c, hc, hQc, hPc,
        ord.le_trans _ _ _ (hmax a ha (iff_of_true hPa hQa)) (ord.le_of_not_lt hlt)⟩,
      fun a ha hQa hPa ↦ ⟨m, hm, hP, hQ, hmax a ha (iff_of_false hPa (not_not.2 hQa))⟩⟩)

theorem revisedEqui_or_revisedComp_or_revisedComp [Finite W] (ord : SemanticOrdering W)
    (P Q : W → Prop) (i : W) :
    RevisedEqui ord.le P Q i ∨ RevisedComp ord.le P Q i ∨ RevisedComp ord.le Q P i := by
  rcases {a | ord.le a i ∧ (P a ↔ ¬ Q a)}.eq_empty_or_nonempty with hS | hS
  · have h (a) (ha : ord.le a i) (h : P a ↔ ¬ Q a) : False :=
      Set.notMem_empty a (hS.subset ⟨ha, h⟩)
    exact .inl (.inl ⟨fun a ha hP hQ ↦ (h a ha (iff_of_true hP hQ)).elim,
      fun a ha hQ hP ↦ (h a ha (iff_of_false hP (not_not.2 hQ))).elim⟩)
  obtain ⟨m, ⟨hm, hPQ⟩, hmax⟩ := ord.exists_le_max (Set.toFinite _) hS
  by_cases hP : P m
  · exact (revisedEqui_or_revisedComp_of_max hm hP (hPQ.1 hP)
      fun a ha h ↦ hmax a ⟨ha, h⟩).imp_right .inl
  · exact (revisedEqui_or_revisedComp_of_max hm (not_not.1 (mt hPQ.2 hP)) hP
      fun a ha h ↦ hmax a ⟨ha, by tauto⟩).imp RevisedEqui.symm .inr

/-- The revised equative is transitive, the supplement's Fact 6. -/
theorem RevisedEqui.trans [Finite W] (h₁ : RevisedEqui ord.le P Q i)
    (h₂ : RevisedEqui ord.le Q R i) : RevisedEqui ord.le P R i := by
  rcases revisedEqui_or_revisedComp_or_revisedComp ord P R i with h | h | h
  · exact h
  · exact (h₁.not_revisedComp (h.of_revisedEqui_right h₂.symm)).elim
  · exact (h₂.symm.not_revisedComp (h.of_revisedEqui_right h₁)).elim

end SemanticOrdering

variable {L : Language} {I E : Type*}

/-- The extension of a unary relation symbol in a structure carried as a term. -/
def ext₁ (S : L.Structure E) (R : L.Relations 1) : Set E := {e | S.RelMap R ![e]}

@[simp] theorem mem_ext₁ {S : L.Structure E} {R : L.Relations 1} {e : E} :
    e ∈ ext₁ S R ↔ S.RelMap R ![e] :=
  Iff.rfl

instance (S : L.Structure E) (R : L.Relations 1) (e : E) [h : Decidable (S.RelMap R ![e])] :
    Decidable (e ∈ ext₁ S R) :=
  h

/-- Pointwise decidability of atoms across an interpretation family, the hook that makes
`decide` available on finite models. -/
abbrev DecidableAtoms (interp : I → W → L.Structure E) :=
  ∀ (i : I) (w : W) (n : ℕ) (r : L.Relations n) (x : Fin n → E), Decidable ((interp i w).RelMap r x)

/-- A formula is an embedded classical formula with free variables valued by domain elements, a
boolean combination, or a comparative `A ≻ B` (`comp`). -/
inductive ComparativeFormula (L : Language) (E : Type*) where
  | ofFormula : L.Formula E → ComparativeFormula L E
  | not : ComparativeFormula L E → ComparativeFormula L E
  | inf : ComparativeFormula L E → ComparativeFormula L E → ComparativeFormula L E
  | sup : ComparativeFormula L E → ComparativeFormula L E → ComparativeFormula L E
  | comp : ComparativeFormula L E → ComparativeFormula L E → ComparativeFormula L E

namespace ComparativeFormula

/-- Ground unary predication `R(e)`, as an embedded formula. -/
abbrev matom (R : L.Relations 1) (e : E) : ComparativeFormula L E :=
  .ofFormula (R.formula₁ (Term.var e))

/-- The equative `A ≈ B := ¬(A ≻ B) ∧ ¬(B ≻ A)`. -/
def equi (A B : ComparativeFormula L E) : ComparativeFormula L E :=
  .inf (.not (.comp A B)) (.not (.comp B A))

/-- The weak comparative `A ≽ B := (A ≻ B) ∨ (A ≈ B)`. -/
def weak (A B : ComparativeFormula L E) : ComparativeFormula L E := .sup (.comp A B) (A.equi B)

/-- Formulas free of the comparative, whose truth does not consult the ordering. -/
def ComparativeFree : ComparativeFormula L E → Prop
  | .ofFormula _ => True
  | .not A => A.ComparativeFree
  | .inf A B => A.ComparativeFree ∧ B.ComparativeFree
  | .sup A B => A.ComparativeFree ∧ B.ComparativeFree
  | .comp _ _ => False

variable (interp : I → W → L.Structure E)

/-- Truth at an index of an ordered interpretation family, relative to a raw ordering relation,
since restricted orderings need not be total. The comparative holds when some interpretation in the
cone making `A` true and `B` false strictly dominates every one making `B` true and `A` false. -/
def Realize : ComparativeFormula L E → (I → I → Prop) → I → W → Prop
  | .ofFormula ψ, _, i, w => ψ.RealizeAt (interp i) w id
  | .not A, le, i, w => ¬ Realize A le i w
  | .inf A B, le, i, w => Realize A le i w ∧ Realize B le i w
  | .sup A B, le, i, w => Realize A le i w ∨ Realize B le i w
  | .comp A B, le, i, w =>
      ConeStrictLift le (Strict le) (Realize A le · w) (Realize B le · w) i

instance instDec [Fintype I] [Fintype E] [DecidableEq E]
    [hA : DecidableAtoms interp] (le : I → I → Prop) [DecidableRel le] :
    ∀ (φ : ComparativeFormula L E) (i : I) (w : W), Decidable (Realize interp φ le i w)
  | .ofFormula ψ, i, w =>
      @Formula.decidableRealize L E (interp i w) _ _ (fun n r x ↦ hA i w n r x) E ψ id
  | .not A, i, w => @instDecidableNot _ (instDec le A i w)
  | .inf A B, i, w => @instDecidableAnd _ _ (instDec le A i w) (instDec le B i w)
  | .sup A B, i, w => @instDecidableOr _ _ (instDec le A i w) (instDec le B i w)
  | .comp A B, i, w =>
      haveI : DecidablePred (Realize interp A le · w) := fun j ↦ instDec le A j w
      haveI : DecidablePred (Realize interp B le · w) := fun j ↦ instDec le B j w
      inferInstanceAs (Decidable (ConeStrictLift le (Strict le)
        (Realize interp A le · w) (Realize interp B le · w) i))

variable {interp} {A B : ComparativeFormula L E} {le : I → I → Prop}
  {ord : SemanticOrdering I} {i : I} {w : W}

theorem realize_comp_iff :
    Realize interp (.comp A B) ord.le i w ↔
    ∃ i', ord.le i' i ∧ Realize interp A ord.le i' w ∧
      ¬ Realize interp B ord.le i' w ∧
      ∀ i'', ord.le i'' i → Realize interp B ord.le i'' w →
        ¬ Realize interp A ord.le i'' w → ord.lt i'' i' :=
  Iff.rfl

@[simp] theorem realize_matom (R : L.Relations 1) (e : E) :
    Realize interp (.matom R e) le i w ↔ (interp i w).RelMap R ![e] :=
  Formula.realizeAt_rel₁ (interp i) w id R (Term.var e)

theorem ComparativeFree.realize_congr :
    ∀ {φ : ComparativeFormula L E}, φ.ComparativeFree →
      ∀ {le le' : I → I → Prop} {i : I} {w : W},
      Realize interp φ le i w ↔ Realize interp φ le' i w
  | .ofFormula _, _ => Iff.rfl
  | .not A, h => not_congr (ComparativeFree.realize_congr (show A.ComparativeFree from h))
  | .inf _ _, h => and_congr (ComparativeFree.realize_congr h.1) (ComparativeFree.realize_congr h.2)
  | .sup _ _, h => or_congr (ComparativeFree.realize_congr h.1) (ComparativeFree.realize_congr h.2)
  | .comp _ _, h => h.elim

theorem realize_comp_iff_strict_lewisLift :
    Realize interp (.comp A B) ord.le i w ↔
    Strict (LewisLift (flip ord.le))
      (coneDiff ord.le (Realize interp A ord.le · w) (Realize interp B ord.le · w) i)
      (coneDiff ord.le (Realize interp B ord.le · w) (Realize interp A ord.le · w) i) :=
  coneStrictLift_iff_strict_lewisLift (fun a b ↦ ord.le_total b a) (fun _ _ ↦ Iff.rfl) _ _ _

theorem not_realize_comp_self : ¬ Realize interp (.comp A A) le i w :=
  fun ⟨_, _, hA, hnA, _⟩ ↦ hnA hA

theorem realize_equi_self : Realize interp (A.equi A) le i w :=
  ⟨not_realize_comp_self, not_realize_comp_self⟩

theorem realize_equi_comm :
    Realize interp (A.equi B) le i w ↔ Realize interp (B.equi A) le i w :=
  and_comm

end ComparativeFormula

end Language

/-! ### Truth and acceptance -/

section Framework

variable {L : Language} {I W E : Type*} (interp : I → W → L.Structure E)

/-- Truth at an index `⟨≤, i, w⟩`. -/
abbrev Eval (φ : ComparativeFormula L E) (ord : SemanticOrdering I) (i : I) (w : W) : Prop :=
  ComparativeFormula.Realize interp φ ord.le i w

/-- The assertoric content of a sentence is its truth at every top-ranked interpretation. -/
def AssertoricContent [Fintype I] (φ : ComparativeFormula L E) (ord : SemanticOrdering I)
    (w : W) : Prop :=
  ord.AcceptedAt (fun i ↦ Eval interp φ ord i w)

instance [Fintype I] [Fintype E] [DecidableEq E] [DecidableAtoms interp]
    (φ : ComparativeFormula L E) (ord : SemanticOrdering I) [DecidableRel ord.le] (w : W) :
    Decidable (AssertoricContent interp φ ord w) := by
  unfold AssertoricContent; infer_instance

/-! ### Entailment -/

section Entailment

variable {ord : SemanticOrdering I} {i : I} {w : W} {A B C : ComparativeFormula L E}

theorem eval_of_comp (h : Eval interp (.comp A B) ord i w) (hB : Eval interp B ord i w) :
    Eval interp A ord i w :=
  of_not_not fun hA ↦ let ⟨_, hle, _, _, hdom⟩ := h; (hdom i (ord.le_refl i) hB hA).2 hle

theorem comp_asymm (h : Eval interp (.comp A B) ord i w) : ¬ Eval interp (.comp B A) ord i w :=
  fun ⟨j, hj, hB, hA, domB⟩ ↦
    let ⟨i', hi', hA', hB', domA⟩ := h
    (domA j hj hB hA).2 (domB i' hi' hA' hB').1

/-- The comparative is transitive, since whichever of the two witnesses is ranked higher witnesses
the composite, and the two domination clauses cover the rivals of the composite. -/
theorem comp_trans (h₁ : Eval interp (.comp A B) ord i w)
    (h₂ : Eval interp (.comp B C) ord i w) : Eval interp (.comp A C) ord i w := by
  obtain ⟨i₁, hi₁, hA₁, hB₁, dom₁⟩ := h₁
  obtain ⟨i₂, hi₂, hB₂, hC₂, dom₂⟩ := h₂
  rcases ord.le_total i₂ i₁ with hle | hle
  · refine ⟨i₁, hi₁, hA₁, fun hC₁ ↦ (dom₂ i₁ hi₁ hC₁ hB₁).2 hle, fun j hj hC hA ↦ ?_⟩
    by_cases hB : Eval interp B ord j w
    · exact dom₁ j hj hB hA
    · exact ord.lt_of_lt_of_le (dom₂ j hj hC hB) hle
  · refine ⟨i₂, hi₂, of_not_not fun hA₂ ↦ (dom₁ i₂ hi₂ hB₂ hA₂).2 hle, hC₂, fun j hj hC hA ↦ ?_⟩
    by_cases hB : Eval interp B ord j w
    · exact ord.lt_of_lt_of_le (dom₁ j hj hB hA) hle
    · exact dom₂ j hj hC hB

theorem comp_not_not_iff :
    Eval interp (.comp (.not B) (.not A)) ord i w ↔ Eval interp (.comp A B) ord i w :=
  exists_congr fun _ ↦
    ⟨fun ⟨h₁, h₂, h₃, h₄⟩ ↦ ⟨h₁, not_not.1 h₃, h₂, fun j hj hB hA ↦ h₄ j hj hA (not_not.2 hB)⟩,
      fun ⟨h₁, h₂, h₃, h₄⟩ ↦ ⟨h₁, h₃, not_not.2 h₂, fun j hj hA hB ↦ h₄ j hj (not_not.1 hB) hA⟩⟩

theorem comp_sup (h : Eval interp (.comp A (.sup B C)) ord i w) :
    Eval interp (.comp A B) ord i w ∧ Eval interp (.comp A C) ord i w :=
  let ⟨i', hi', hA, hBC, dom⟩ := h
  ⟨⟨i', hi', hA, fun hB ↦ hBC (Or.inl hB), fun j hj hB hA' ↦ dom j hj (Or.inl hB) hA'⟩,
    ⟨i', hi', hA, fun hC ↦ hBC (Or.inr hC), fun j hj hC hA' ↦ dom j hj (Or.inr hC) hA'⟩⟩

theorem inf_comp (h : Eval interp (.comp (.inf A B) C) ord i w) :
    Eval interp (.comp A C) ord i w ∧ Eval interp (.comp B C) ord i w :=
  let ⟨i', hi', ⟨hA, hB⟩, hC, dom⟩ := h
  ⟨⟨i', hi', hA, hC, fun j hj hC' hnA ↦ dom j hj hC' fun h ↦ hnA h.1⟩,
    ⟨i', hi', hB, hC, fun j hj hC' hnB ↦ dom j hj hC' fun h ↦ hnB h.2⟩⟩

theorem equi_not_not (h : Eval interp (A.equi B) ord i w) :
    Eval interp ((ComparativeFormula.not A).equi (.not B)) ord i w :=
  ⟨fun h' ↦ h.2 ((comp_not_not_iff interp).1 h'), fun h' ↦ h.1 ((comp_not_not_iff interp).1 h')⟩

theorem eval_weak_iff : Eval interp (A.weak B) ord i w ↔ ¬ Eval interp (.comp B A) ord i w :=
  ⟨fun h ↦ h.elim (comp_asymm interp) And.right,
    fun h ↦ (em _).elim Or.inl fun h' ↦ Or.inr ⟨h', h⟩⟩

theorem eval_comp_or_equi :
    Eval interp (.sup (.sup (.comp A B) (.comp B A)) (A.equi B)) ord i w :=
  (em _).elim (Or.inl ∘ Or.inl) fun h₁ ↦ (em _).elim (Or.inl ∘ Or.inr) fun h₂ ↦ Or.inr ⟨h₁, h₂⟩

/-- *More `A` than not* holds at an index iff `A` holds at every interpretation tied with it (the
supplement's Fact 1). -/
theorem eval_comp_not_iff :
    Eval interp (.comp A (.not A)) ord i w ↔ ∀ j, ord.equiv j i → Eval interp A ord j w :=
  ⟨fun ⟨a, ha, _, _, hd⟩ j hj ↦ of_not_not fun hA ↦
      (hd j hj.1 hA hA).2 (ord.le_trans a i j ha hj.2),
    fun h ↦ ⟨i, ord.le_refl i, h i (AntisymmRel.refl _ _), not_not.2 (h i (AntisymmRel.refl _ _)),
      fun b hb _ hA ↦ ⟨hb, fun hib ↦ hA (h b ⟨hb, hib⟩)⟩⟩⟩

variable [Fintype I]

theorem accepted_mono (h : ∀ i, Eval interp A ord i w → Eval interp B ord i w)
    (hA : AssertoricContent interp A ord w) : AssertoricContent interp B ord w :=
  fun x hx ↦ h x (hA x hx)

/-- Accepting `A` and `¬B` means accepting `A ≻ B`. Every top-ranked interpretation makes `A` true
and `B` false, so an interpretation making `B` true and `A` false is not top-ranked and lies
strictly below each of them. -/
theorem accepted_comp_of_accepted (hA : AssertoricContent interp A ord w)
    (hB : AssertoricContent interp (.not B) ord w) :
    AssertoricContent interp (.comp A B) ord w :=
  fun x hx ↦ ⟨x, ord.le_refl x, hA x hx, hB x hx, fun j hj _ hAj ↦
    ⟨hj, fun hxj ↦ hAj (hA j fun y hy ↦ hx y (ord.lt_of_le_of_lt hxj hy))⟩⟩

theorem accepted_of_accepted_equi (h : AssertoricContent interp (A.equi B) ord w)
    (hA : AssertoricContent interp A ord w) : AssertoricContent interp B ord w :=
  fun x hx ↦ of_not_not fun hB ↦ (h x hx).1 ⟨x, ord.le_refl x, hA x hx, hB, fun j hj _ hAj ↦
    ⟨hj, fun hxj ↦ hAj (hA j fun y hy ↦ hx y (ord.lt_of_le_of_lt hxj hy))⟩⟩

end Entailment

/-! ### Distance functions and degree modifiers -/

/-- A distance function says which interpretations count as reasonably close to each one. It is the
parameter behind *very*, *sorta* and *mostly*. -/
structure DistanceFunction (I : Type*) (ord : SemanticOrdering I) where
  /-- `close i i'` means i' is reasonably close to i. -/
  close : I → I → Prop
  /-- The function is centered, so `i ∈ d(i)`. -/
  centered : ∀ i, close i i
  /-- The function is top-bounded, so if `i' ∈ d(i)` then `i' ≤ i`. -/
  topBounded : ∀ i i', close i i' → ord.le i' i
  /-- The function is convex, so if `i' ∈ d(i)` and `i' ≤ i'' ≤ i` then `i'' ∈ d(i)`. -/
  convex : ∀ i i' i'', close i i' → ord.le i' i'' → ord.le i'' i → close i i''
  /-- The function is noncontractive, so if `i' ∈ d(i)` and `i' ≤ j ≤ i` then `i' ∈ d(j)`. -/
  noncontractive : ∀ i i' j, close i i' → ord.le i' j → ord.le j i → close j i'

/-- `i ≪ j` holds when `i` is below `j` and not even reasonably close to it. -/
def FarBelow {I : Type*} (ord : SemanticOrdering I) (d : DistanceFunction I ord)
    (i j : I) : Prop :=
  ord.le i j ∧ ¬ d.close j i

instance {I : Type*} (ord : SemanticOrdering I) (d : DistanceFunction I ord)
    [DecidableRel ord.le] [DecidableRel d.close] :
    DecidableRel (FarBelow ord d) := fun _ _ ↦
  inferInstanceAs (Decidable (_ ∧ _))

theorem FarBelow.asymm {I : Type*} {ord : SemanticOrdering I}
    (d : DistanceFunction I ord) {a b : I} (h : FarBelow ord d a b) :
    ¬ FarBelow ord d b a :=
  fun h' ↦ h'.2 (d.noncontractive b b a (d.centered b) h'.1 h.1)

theorem not_farBelow_total {I : Type*} {ord : SemanticOrdering I}
    (d : DistanceFunction I ord) (a b : I) :
    ¬ FarBelow ord d a b ∨ ¬ FarBelow ord d b a :=
  imp_iff_not_or.mp (FarBelow.asymm d)

section Modifiers

variable (φ ψ : ComparativeFormula L E) (ord : SemanticOrdering I)
  (below : I → I → Prop) (d : DistanceFunction I ord) (i : I) (w : W)

/-- The paper's comparative template is `ConeStrictLift` at the truth sets of the formulas. It is
the clause of ≻ with an arbitrary dominance relation in place of < (`eval_comp_iff_compWith`), and ≫
is the instance at ≪. -/
abbrev EvalCompWith : Prop :=
  ConeStrictLift ord.le below
    (fun j ↦ Eval interp φ ord j w) (fun j ↦ Eval interp ψ ord j w) i

theorem eval_comp_iff_compWith :
    Eval interp (.comp φ ψ) ord i w ↔ EvalCompWith interp φ ψ ord ord.lt i w :=
  Iff.rfl

/-- *Much more*, `A ≫ B`, is the template at ≪. -/
abbrev EvalMuchMore : Prop :=
  EvalCompWith interp φ ψ ord (FarBelow ord d) i w

/-- *very A* is `A ≫ ¬A`, under which every reasonably close interpretation makes `A` true. -/
abbrev EvalVery : Prop :=
  EvalMuchMore interp φ (.not φ) ord d i w

/-- *sorta A* is `¬ very ¬A`, under which some reasonably close interpretation makes `A` true. -/
abbrev EvalSorta : Prop :=
  ¬ EvalVery interp (.not φ) ord d i w

/-- *Mostly A* holds when some reasonably high level strictly below the top makes A uniformly true
and every A-false level below the current interpretation sits below it. It is compatible with A and
with ¬A, unlike `very`, entails `sorta A`, and `mostly A ∧ mostly ¬A` is contradictory. -/
def EvalMostly : Prop :=
  ∃ i', ord.lt i' i ∧ d.close i i' ∧
    (∀ j, ord.equiv j i' → Eval interp φ ord j w) ∧
    ∀ i'', ord.lt i'' i → (∀ j, ord.equiv j i'' → ¬ Eval interp φ ord j w) →
      ord.lt i'' i'

instance [Fintype I] [Fintype E] [DecidableEq E] [DecidableAtoms interp]
    [DecidableRel ord.le] [DecidableRel d.close] :
    Decidable (EvalMostly interp φ ord d i w) := by
  unfold EvalMostly
  haveI h1 : DecidableRel ord.lt := inferInstance
  haveI h2 : DecidableRel ord.equiv := inferInstance
  haveI h3 : ∀ j, Decidable (Eval interp φ ord j w) := fun j ↦ inferInstance
  infer_instance

end Modifiers

section ModifierGroundings

variable (φ ψ : ComparativeFormula L E) (ord : SemanticOrdering I)
  (d : DistanceFunction I ord) (i : I) (w : W)

theorem evalMuchMore_iff_strict_lewisLift :
    EvalMuchMore interp φ ψ ord d i w ↔
    Strict
      (LewisLift (fun a b ↦ ¬ FarBelow ord d a b))
      (coneDiff ord.le (Eval interp φ ord · w) (Eval interp ψ ord · w) i)
      (coneDiff ord.le (Eval interp ψ ord · w) (Eval interp φ ord · w) i) :=
  coneStrictLift_iff_strict_lewisLift
    (fun a b ↦ not_farBelow_total d a b)
    (fun _ _ ↦ ⟨fun h ↦ ⟨FarBelow.asymm d h, not_not_intro h⟩,
      fun h ↦ not_not.mp h.2⟩) _ _ i

theorem evalMostly_iff_strict_lewisLift :
    EvalMostly interp φ ord d i w ↔
    Strict
      (LewisLift (fun a b ↦ ord.le b a))
      {x | ord.lt x i ∧ d.close i x ∧ ∀ j, ord.equiv j x → Eval interp φ ord j w}
      {x | ord.lt x i ∧ ∀ j, ord.equiv j x → ¬ Eval interp φ ord j w} := by
  rw [strict_lewisLift_iff_below
    (fun a b ↦ ord.le_total b a) (fun _ _ ↦ Iff.rfl)]
  simp only [Set.mem_ofPred_eq, and_imp, and_assoc]
  rfl

end ModifierGroundings

section ModifierConsequences

variable {ord : SemanticOrdering I} (d : DistanceFunction I ord) {i : I} {w : W}
  {φ : ComparativeFormula L E}

/-- *very A* is truth at every reasonably close interpretation, since a witness strictly above a
close falsifier would, by noncontractivity, have it close too. -/
theorem evalVery_iff :
    EvalVery interp φ ord d i w ↔ ∀ i', d.close i i' → Eval interp φ ord i' w := by
  constructor
  · rintro ⟨a, ha, hφa, -, hdom⟩ i' hi'
    by_contra hφ
    obtain ⟨hia, hclose⟩ := hdom i' (d.topBounded i i' hi') hφ hφ
    exact hclose (d.noncontractive i i' a hi' hia ha)
  · intro h
    exact ⟨i, ord.le_refl i, h i (d.centered i), not_not.2 (h i (d.centered i)),
      fun b hb hφ _ ↦ ⟨hb, fun hc ↦ hφ (h b hc)⟩⟩

theorem eval_of_very (h : EvalVery interp φ ord d i w) : Eval interp φ ord i w :=
  (evalVery_iff interp d).1 h i (d.centered i)

theorem evalSorta_iff :
    EvalSorta interp φ ord d i w ↔ ∃ i', d.close i i' ∧ Eval interp φ ord i' w :=
  ⟨fun h ↦ Classical.byContradiction fun h' ↦
      h ((evalVery_iff interp d).2 fun i' hi' hφ ↦ h' ⟨i', hi', hφ⟩),
    fun ⟨i', hi', hφ⟩ h ↦ (evalVery_iff interp d).1 h i' hi' hφ⟩

theorem sorta_of_eval (h : Eval interp φ ord i w) : EvalSorta interp φ ord d i w :=
  (evalSorta_iff interp d).2 ⟨i, d.centered i, h⟩

theorem sorta_of_mostly (h : EvalMostly interp φ ord d i w) : EvalSorta interp φ ord d i w :=
  let ⟨i', _, hc, hφ, _⟩ := h
  (evalSorta_iff interp d).2 ⟨i', hc, hφ i' (AntisymmRel.refl _ _)⟩

theorem not_mostly_not_of_mostly (h : EvalMostly interp φ ord d i w) :
    ¬ EvalMostly interp (.not φ) ord d i w :=
  fun ⟨i₂, lt₂, _, all₂, dom₂⟩ ↦
    let ⟨i₁, lt₁, _, all₁, dom₁⟩ := h
    (dom₁ i₂ lt₂ all₂).2 (dom₂ i₁ lt₁ fun j hj ↦ not_not.2 (all₁ j hj)).1

end ModifierConsequences

/-! ### No Reversal and the delineation bridge -/

/-- No Reversal says that below any interpretation separating `a` from `b`, every extension
admitting `b` admits `a`. It is the order-restricted analogue of Klein's monotone delineation. -/
def NoReversal (ord : SemanticOrdering I) (R : L.Relations 1) (w : W)
    (a b : E) : Prop :=
  ∀ i i', ord.le i' i →
    a ∈ ext₁ (interp i w) R → b ∉ ext₁ (interp i w) R →
    b ∈ ext₁ (interp i' w) R → a ∈ ext₁ (interp i' w) R

instance [Fintype I] [DecidableAtoms interp]
    (ord : SemanticOrdering I) [DecidableRel ord.le]
    (R : L.Relations 1) (w : W) (a b : E) :
    Decidable (NoReversal interp ord R w a b) := by
  unfold NoReversal; simp only [mem_ext₁]; infer_instance

section Delineation

variable (ord : SemanticOrdering I) (R : L.Relations 1) (w : W)

/-- The delineation induced by a ranked interpretation family takes the extensions of `R` in the
≤-cone as the admissible comparison classes, and `x` is `R` in `C` iff `x ∈ C`. It instantiates
Klein's comparison-class parameter. -/
def interpretationDelineation (i : I) : Degree.Delineation E :=
  ⟨fun C ↦ {x | (∃ i', ord.le i' i ∧ C = ext₁ (interp i' w) R) ∧ x ∈ C}⟩

theorem delineation_comparative_iff (i : I) (a b : E) :
    (interpretationDelineation interp ord R w i).Comparative a b ↔
    ∃ i', ord.le i' i ∧ a ∈ ext₁ (interp i' w) R ∧ b ∉ ext₁ (interp i' w) R := by
  constructor
  · rintro ⟨C, ⟨⟨i', h_le, rfl⟩, h_aC⟩, h_nb⟩
    exact ⟨i', h_le, h_aC, fun hb ↦ h_nb ⟨⟨i', h_le, rfl⟩, hb⟩⟩
  · rintro ⟨i', h_le, h_a, h_b⟩
    exact ⟨ext₁ (interp i' w) R, ⟨⟨i', h_le, rfl⟩, h_a⟩,
      fun h ↦ h_b h.2⟩

theorem eval_mc_iff_delineation_of_noReversal (i : I) (a b : E)
    (hnr : NoReversal interp ord R w b a) :
    Eval interp (.comp (.matom R a) (.matom R b)) ord i w ↔
    (interpretationDelineation interp ord R w i).Comparative
      a b := by
  rw [Eval, ComparativeFormula.realize_comp_iff, delineation_comparative_iff]
  simp only [ComparativeFormula.realize_matom, ← mem_ext₁]
  constructor
  · rintro ⟨i', h_le, h_A, h_B, -⟩
    exact ⟨i', h_le, h_A, h_B⟩
  · rintro ⟨i', h_le, h_a, h_b⟩
    refine ⟨i', h_le, h_a, h_b, fun i'' h'' hB'' hA'' ↦ ?_⟩
    have h_not : ¬ ord.le i' i'' :=
      fun hle' ↦ h_b (hnr i'' i' hle' hB'' hA'' h_a)
    rcases ord.le_total i'' i' with h1 | h2
    · exact ⟨h1, h_not⟩
    · exact absurd h2 h_not

end Delineation
/-! ### The revised semantics -/

section Revised

/-- Truth under the revised semantics of the supplement, whose comparative is `RevisedComp`. The
basic equative fails transitivity, and the revision strengthens the comparative so that the
equative it defines is transitive. -/
def EvalRevised : ComparativeFormula L E → SemanticOrdering I → I → W → Prop
  | .ofFormula ψ, _, i, w => ψ.RealizeAt (interp i) w id
  | .not A, ord, i, w => ¬ EvalRevised A ord i w
  | .inf A B, ord, i, w => EvalRevised A ord i w ∧ EvalRevised B ord i w
  | .sup A B, ord, i, w => EvalRevised A ord i w ∨ EvalRevised B ord i w
  | .comp A B, ord, i, w => RevisedComp ord.le (EvalRevised A ord · w) (EvalRevised B ord · w) i

instance EvalRevised.instDec [Fintype I] [Fintype E] [DecidableEq E]
    [hA : DecidableAtoms interp] (ord : SemanticOrdering I) [DecidableRel ord.le] :
    ∀ (φ : ComparativeFormula L E) (i : I) (w : W),
      Decidable (EvalRevised interp φ ord i w)
  | .ofFormula ψ, i, w =>
      @Formula.decidableRealize L E (interp i w) _ _ (fun n r x ↦ hA i w n r x) E ψ id
  | .not A, i, w => @instDecidableNot _ (EvalRevised.instDec ord A i w)
  | .inf A B, i, w =>
      @instDecidableAnd _ _ (EvalRevised.instDec ord A i w) (EvalRevised.instDec ord B i w)
  | .sup A B, i, w =>
      @instDecidableOr _ _ (EvalRevised.instDec ord A i w) (EvalRevised.instDec ord B i w)
  | .comp A B, i, w =>
      haveI : DecidablePred (EvalRevised interp A ord · w) := (EvalRevised.instDec ord A · w)
      haveI : DecidablePred (EvalRevised interp B ord · w) := (EvalRevised.instDec ord B · w)
      inferInstanceAs (Decidable (RevisedComp ord.le
        (EvalRevised interp A ord · w) (EvalRevised interp B ord · w) i))

variable {A B C : ComparativeFormula L E} {ord : SemanticOrdering I} {i : I} {w : W}

theorem evalRevised_comp_trans (h₁ : EvalRevised interp (.comp A B) ord i w)
    (h₂ : EvalRevised interp (.comp B C) ord i w) : EvalRevised interp (.comp A C) ord i w :=
  RevisedComp.trans h₁ h₂

variable [Finite I]

theorem evalRevised_equi_iff : EvalRevised interp (A.equi B) ord i w ↔
    RevisedEqui ord.le (EvalRevised interp A ord · w) (EvalRevised interp B ord · w) i := by
  refine ⟨fun ⟨h₁, h₂⟩ ↦ ?_, fun h ↦ ⟨h.not_revisedComp, h.symm.not_revisedComp⟩⟩
  rcases revisedEqui_or_revisedComp_or_revisedComp ord
    (EvalRevised interp A ord · w) (EvalRevised interp B ord · w) i with h | h | h
  exacts [h, (h₁ h).elim, (h₂ h).elim]

/-- The revised equative is transitive, unlike the basic one (`equi_not_trans`). -/
theorem evalRevised_equi_trans (h₁ : EvalRevised interp (A.equi B) ord i w)
    (h₂ : EvalRevised interp (B.equi C) ord i w) : EvalRevised interp (A.equi C) ord i w :=
  (evalRevised_equi_iff interp).2
    (((evalRevised_equi_iff interp).1 h₁).trans ((evalRevised_equi_iff interp).1 h₂))

end Revised
/-! ### The metalinguistic conditional -/

section MCond

variable (A B : ComparativeFormula L E)

/-- The restriction of an ordering relation to the `A`-interpretations drops the other
interpretations. The result is reflexive at `A`-interpretations and transitive but not total, which
is why the consequent of a conditional is evaluated through `EvalGen` and not `Eval`. -/
def restrictLE (le : I → I → Prop) (w : W) : I → I → Prop :=
  fun i j ↦ le i j ∧ ComparativeFormula.Realize interp A le i w ∧
    ComparativeFormula.Realize interp A le j w

instance [Fintype I] [Fintype E] [DecidableEq E] [DecidableAtoms interp]
    (le : I → I → Prop) [DecidableRel le] (w : W) :
    DecidableRel (restrictLE interp A le w) := fun _ _ ↦ by
  unfold restrictLE; infer_instance

variable (ord : SemanticOrdering I) (i : I) (w : W)

/-- The metalinguistic conditional evaluates the antecedent with the full ordering and the
consequent with the ordering restricted to `A`. For `A` and `B` that are not metagradable it reduces
to strict implication over interpretations. Conditionals entail weak comparatives, `A → (A ≻ ¬A)` is
valid (`mcond_m1`), and modus tollens fails for acceptance. -/
def EvalMCond : Prop :=
  ∀ i', ord.le i' i → ComparativeFormula.Realize interp A ord.le i' w →
    ComparativeFormula.Realize interp B (restrictLE interp A ord.le w) i' w

instance [Fintype I] [Fintype E] [DecidableEq E] [DecidableAtoms interp]
    [DecidableRel ord.le] :
    Decidable (EvalMCond interp A B ord i w) := by
  unfold EvalMCond; infer_instance

/-- For a consequent free of the comparative, the metalinguistic conditional is Stalnakerian
entailment (`⊆`) of the consequent by the ranked cone of the antecedent. This is strictly weaker
than the paper's reduction, which also assumes the antecedent free of the comparative. The
antecedent may contain ≻ freely, since it is always evaluated at the full ordering and a consequent
free of the comparative never consults the restricted one. -/
theorem evalMCond_iff_entails (hB : B.ComparativeFree) :
    EvalMCond interp A B ord i w ↔
    {x | ord.le x i ∧ ComparativeFormula.Realize interp A ord.le x w} ⊆
      {x | ComparativeFormula.Realize interp B ord.le x w} := by
  constructor
  · rintro h x ⟨hx1, hx2⟩
    exact hB.realize_congr.mp (h x hx1 hx2)
  · intro h x hx hAx
    exact hB.realize_congr.mpr (h ⟨hx, hAx⟩)

theorem weak_of_mcond (hB : B.ComparativeFree) (h : EvalMCond interp A B ord i w) :
    Eval interp (B.weak A) ord i w :=
  (eval_weak_iff interp).2 fun ⟨i', hi', hA, hnB, _⟩ ↦ hnB (hB.realize_congr.1 (h i' hi' hA))

theorem comp_of_mcond_sup (hA : A.ComparativeFree) (hB : B.ComparativeFree)
    (h₁ : EvalMCond interp (.sup A B) A ord i w) (h₂ : ¬ EvalMCond interp (.sup A B) B ord i w) :
    Eval interp (.comp A B) ord i w := by
  rw [evalMCond_iff_entails interp _ _ ord i w hA] at h₁
  rw [evalMCond_iff_entails interp _ _ ord i w hB, Set.not_subset] at h₂
  obtain ⟨x, ⟨hx, hAB⟩, hnB⟩ := h₂
  exact ⟨x, hx, hAB.resolve_right hnB, hnB, fun j hj hB' hnA ↦ absurd (h₁ ⟨hj, Or.inr hB'⟩) hnA⟩

theorem mcond_comp_not (hA : A.ComparativeFree) : EvalMCond interp A (.comp A (.not A)) ord i w :=
  fun i' _ hA' ↦ ⟨i', ⟨ord.le_refl i', hA', hA'⟩, hA.realize_congr.1 hA',
    not_not.2 (hA.realize_congr.1 hA'),
    fun _ ⟨_, hAb, _⟩ hnA _ ↦ absurd (hA.realize_congr.1 hAb) hnA⟩

end MCond

end Framework

/-! ### The common ground -/

section CommonGround

variable {L : Language} {I W E : Type*} [Fintype I] (interp : I → W → L.Structure E)

/-- The proposition that a sentence expresses over the enriched index consists of the pairs of an
ordering and a world at which its assertoric content holds. The common ground is a set of such
pairs, and an assertion removes the pairs outside this proposition. -/
def assertoricProp (φ : ComparativeFormula L E) : Set (SemanticOrdering I × W) :=
  {p | AssertoricContent interp φ p.1 p.2}

end CommonGround

/-! ### Metalinguistic degrees

The supplement's degree theory. Its equivalence `X ∼ Y` and ordering `X ⊐ Y` of sets of
interpretations are the revised equative and comparative of their membership predicates, so the
degree of a formula is the `∼`-class of its denotation and the comparative compares degrees. -/

section DegreeTheory

variable {I : Type*} (ord : SemanticOrdering I) (i : I)

section Degrees

variable [Finite I]

/-- The equivalence `X ∼ Y` of sets of interpretations ranked no higher than `i`, an equivalence
relation by the supplement's Fact 8. -/
def metalinguisticSetoid : Setoid (Set I) where
  r X Y := RevisedEqui ord.le (· ∈ X) (· ∈ Y) i
  iseqv := ⟨fun _ ↦ .refl, .symm, .trans⟩

/-- Metalinguistic degrees at `i` are the `∼`-classes of sets of interpretations. -/
def MetaDegree : Type _ := Quotient (metalinguisticSetoid ord i)

/-- The metalinguistic degree of a set of interpretations. -/
def deg (X : Set I) : MetaDegree ord i := Quotient.mk _ X

theorem deg_eq_deg_iff {X Y : Set I} :
    deg ord i X = deg ord i Y ↔ RevisedEqui ord.le (· ∈ X) (· ∈ Y) i :=
  ⟨fun h ↦ Quotient.exact h, fun h ↦ Quotient.sound h⟩

/-- `deg X ≤ deg Y` iff `X ⊐ Y` fails, well defined since `⊐` respects `∼` on both sides. -/
protected def MetaDegree.le (d₁ d₂ : MetaDegree ord i) : Prop :=
  Quotient.lift₂ (fun X Y ↦ ¬ RevisedComp ord.le (· ∈ X) (· ∈ Y) i)
    (fun _ _ _ _ (hX : RevisedEqui ord.le _ _ i) (hY : RevisedEqui ord.le _ _ i) ↦
      propext (not_congr ⟨fun h ↦ (h.of_revisedEqui_left hX).of_revisedEqui_right hY,
        fun h ↦ (h.of_revisedEqui_left hX.symm).of_revisedEqui_right hY.symm⟩)) d₁ d₂

/-- The degrees form a linear order, the supplement's Fact 12: irreflexivity, transitivity and
trichotomy of `⊐` become the order axioms on the quotient. -/
noncomputable instance : LinearOrder (MetaDegree ord i) where
  le := MetaDegree.le ord i
  le_refl d := Quotient.inductionOn d fun _ ↦ not_revisedComp_self
  le_trans d₁ d₂ d₃ := Quotient.inductionOn₃ d₁ d₂ d₃ fun X Y _ h₁ h₂ hXZ ↦ by
    rcases revisedEqui_or_revisedComp_or_revisedComp ord (· ∈ X) (· ∈ Y) i with h | h | h
    exacts [h₂ (hXZ.of_revisedEqui_left h), h₁ h, h₂ (h.trans hXZ)]
  le_antisymm d₁ d₂ := Quotient.inductionOn₂ d₁ d₂ fun X Y h₁ h₂ ↦ by
    rcases revisedEqui_or_revisedComp_or_revisedComp ord (· ∈ X) (· ∈ Y) i with h | h | h
    exacts [Quotient.sound h, (h₁ h).elim, (h₂ h).elim]
  le_total d₁ d₂ := Quotient.inductionOn₂ d₁ d₂ fun _ _ ↦ (em _).elim
    (fun h ↦ .inr fun h' ↦ not_revisedComp_self (h.trans h')) .inl
  toDecidableLE := Classical.decRel _

/-- The top degree is that of the cone `I_i` and the bottom degree that of `∅`, the supplement's
Fact 13. -/
noncomputable instance : BoundedOrder (MetaDegree ord i) where
  top := deg ord i {j | ord.le j i}
  le_top d := Quotient.inductionOn d fun _ ⟨_, ha, _, hn, _⟩ ↦ hn ha
  bot := deg ord i ∅
  bot_le d := Quotient.inductionOn d fun _ ⟨a, _, h, _⟩ ↦ Set.notMem_empty a h

@[simp] theorem deg_le_deg_iff {X Y : Set I} :
    deg ord i X ≤ deg ord i Y ↔ ¬ RevisedComp ord.le (· ∈ X) (· ∈ Y) i :=
  Iff.rfl

theorem deg_lt_deg_iff {X Y : Set I} :
    deg ord i Y < deg ord i X ↔ RevisedComp ord.le (· ∈ X) (· ∈ Y) i := by
  rw [lt_iff_le_not_ge, deg_le_deg_iff, deg_le_deg_iff, not_not]
  exact ⟨And.right, fun h ↦ ⟨fun h' ↦ not_revisedComp_self (h'.trans h), h⟩⟩

end Degrees

variable {L : Language} {W E : Type*} (interp : I → W → L.Structure E)

/-- The denotation `⟦φ⟧ᵢ` of a formula, the interpretations ranked no higher than `i` at which it
is true under the revised semantics. -/
def denotation (φ : ComparativeFormula L E) (w : W) : Set I :=
  {j | ord.le j i ∧ EvalRevised interp φ ord j w}

/-- The metalinguistic degree of a formula is the degree of its denotation. -/
noncomputable def formulaDeg [Finite I] (φ : ComparativeFormula L E) (w : W) : MetaDegree ord i :=
  deg ord i (denotation ord i interp φ w)

variable {interp ord i} {A B : ComparativeFormula L E} {w : W}

private theorem mem_denotation_iff {φ : ComparativeFormula L E} {j : I} (hj : ord.le j i) :
    EvalRevised interp φ ord j w ↔ j ∈ denotation ord i interp φ w :=
  (and_iff_right hj).symm

/-- The revised comparative compares the denotations, the supplement's Fact 10. -/
theorem evalRevised_comp_iff_denotation : EvalRevised interp (.comp A B) ord i w ↔
    RevisedComp ord.le (· ∈ denotation ord i interp A w) (· ∈ denotation ord i interp B w) i :=
  RevisedComp.congr (fun _ ↦ mem_denotation_iff) fun _ ↦ mem_denotation_iff

variable [Finite I]

/-- The revised equative holds iff the two formulas have the same degree, the supplement's
Fact 9. -/
theorem evalRevised_equi_iff_formulaDeg_eq :
    EvalRevised interp (A.equi B) ord i w ↔
      formulaDeg ord i interp A w = formulaDeg ord i interp B w := by
  rw [evalRevised_equi_iff interp, formulaDeg, formulaDeg, deg_eq_deg_iff]
  exact RevisedEqui.congr (fun _ ↦ mem_denotation_iff) fun _ ↦ mem_denotation_iff

/-- The revised metalinguistic comparative is the point-standard comparative over the measure
function `formulaDeg` (59). -/
theorem mc_iff_formulaDeg_lt : EvalRevised interp (.comp A B) ord i w ↔
    formulaDeg ord i interp B w < formulaDeg ord i interp A w := by
  rw [evalRevised_comp_iff_denotation, formulaDeg, formulaDeg, deg_lt_deg_iff]

end DegreeTheory

/-! ### Finite models -/

/-- One world. -/
inductive W | w0
  deriving DecidableEq, Repr, Fintype

/-- The model has one entity, Ann. -/
inductive Entity | ann
  deriving DecidableEq, Repr, Fintype

/-- Three interpretations. -/
inductive I3 | i0 | i1 | i2
  deriving DecidableEq, Repr, Fintype

/-- The rank of each of the three interpretations. -/
def rank₃ : I3 → ℕ
  | .i0 => 0
  | .i1 => 1
  | .i2 => 2

/-- The linear ordering `i0 < i1 < i2`. -/
def ord₃ : SemanticOrdering I3 := .ofRank rank₃

instance : DecidableRel ord₃.le := inferInstanceAs (DecidableRel (SemanticOrdering.ofRank rank₃).le)

/-- An interpretation family over a monadic language, from the extension of each predicate at each
interpretation. -/
@[instance_reducible] def interpOf {Sym I E : Type*} (ext : I → Sym → Finset E) :
    I → W → (Language.monadic Sym).Structure E :=
  fun i _ ↦ monadic.structure fun P e ↦ e ∈ ext i P

instance {Sym I E : Type*} [DecidableEq E] (ext : I → Sym → Finset E) :
    DecidableAtoms (interpOf ext) :=
  inferInstance

/-- The predicates *linguist* and *philosopher*. -/
inductive Pred | linguist | philosopher
  deriving DecidableEq, Repr, Fintype

/-- *Ann is a linguist*. -/
abbrev La : ComparativeFormula (Language.monadic Pred) Entity := .matom Pred.linguist .ann

/-- *Ann is a philosopher*. -/
abbrev Pa : ComparativeFormula (Language.monadic Pred) Entity := .matom Pred.philosopher .ann

/-- Ann is a philosopher at `i0`, a linguist at `i1`, both at `i2`. -/
@[instance_reducible] def both : I3 → W → (Language.monadic Pred).Structure Entity :=
  interpOf fun i P ↦ match i, P with
    | .i0, .philosopher | .i1, .linguist | .i2, _ => {.ann}
    | _, _ => ∅

/-- Ann is a philosopher at `i0`, a linguist at `i1`, neither at `i2`. -/
@[instance_reducible] def neither : I3 → W → (Language.monadic Pred).Structure Entity :=
  interpOf fun i P ↦ match i, P with
    | .i0, .philosopher | .i1, .linguist => {.ann}
    | _, _ => ∅

/-- *Ann is more a linguist than a philosopher* is consistent with her being both and with her being
neither, Observation 1. -/
theorem comp_consistent_with_both_and_neither :
    (Eval both (.comp La Pa) ord₃ .i2 .w0 ∧ Eval both La ord₃ .i2 .w0 ∧
      Eval both Pa ord₃ .i2 .w0) ∧
    (Eval neither (.comp La Pa) ord₃ .i2 .w0 ∧ ¬ Eval neither La ord₃ .i2 .w0 ∧
      ¬ Eval neither Pa ord₃ .i2 .w0) := by
  decide

/-- Two tied interpretations. -/
inductive I2 | j0 | j1
  deriving DecidableEq, Repr, Fintype

/-- The ordering with `j0` and `j1` tied at the top. -/
def tiedOrd : SemanticOrdering I2 := .ofRank fun _ ↦ (0 : ℕ)

instance : DecidableRel tiedOrd.le :=
  inferInstanceAs (DecidableRel (SemanticOrdering.ofRank fun _ : I2 ↦ (0 : ℕ)).le)

/-- Ann is a linguist at `j0` and a philosopher at `j1`. -/
@[instance_reducible] def tied : I2 → W → (Language.monadic Pred).Structure Entity :=
  interpOf fun i P ↦ match i, P with
    | .j0, .linguist | .j1, .philosopher => {.ann}
    | _, _ => ∅

/-- *Ann is as much a linguist as not* is consistent, a borderline case, Observation 5. -/
theorem equi_not_consistent : Eval tied (La.equi (.not La)) tiedOrd .j0 .w0 := by decide

theorem accepted_sup_not_accepted_comp :
    AssertoricContent tied (.sup La (.not La)) tiedOrd .w0 ∧
      ¬ AssertoricContent tied (.sup (.comp La (.not La)) (.comp (.not La) La)) tiedOrd .w0 := by
  decide

theorem modus_tollens_not_accepted :
    AssertoricContent tied (.not (.comp La (.not La))) tiedOrd .w0 ∧
      ¬ AssertoricContent tied (.not La) tiedOrd .w0 := by
  decide

/-- The distance function on `ord₃` whose thresholds reach one level down. -/
def dist₃ : DistanceFunction I3 ord₃ where
  close i i' := rank₃ i' ≤ rank₃ i ∧ rank₃ i ≤ rank₃ i' + 1
  centered := by decide
  topBounded := by decide
  convex := by decide
  noncontractive := by decide

instance : DecidableRel dist₃.close := fun _ _ ↦ inferInstanceAs (Decidable (_ ∧ _))

theorem sorta_mostly_consistent_with_not :
    ¬ Eval neither La ord₃ .i2 .w0 ∧ EvalSorta neither La ord₃ dist₃ .i2 .w0 ∧
      EvalMostly neither La ord₃ dist₃ .i2 .w0 := by
  decide

theorem not_very_of_eval : Eval both La ord₃ .i1 .w0 ∧ ¬ EvalVery both La ord₃ dist₃ .i1 .w0 := by
  decide

theorem mcond_not_material : ¬ EvalMCond both La Pa ord₃ .i2 .w0 := by decide

/-! ### No Reversal -/

/-- Two entities for a gradable predicate. -/
inductive Entity2 | ann | ben
  deriving DecidableEq, Repr, Fintype

/-- The predicate *tall*. -/
inductive Pred1 | tall
  deriving DecidableEq, Repr, Fintype

/-- *Ann is tall*. -/
abbrev Ta : ComparativeFormula (Language.monadic Pred1) Entity2 := .matom Pred1.tall .ann

/-- *Ben is tall*. -/
abbrev Tb : ComparativeFormula (Language.monadic Pred1) Entity2 := .matom Pred1.tall .ben

/-- The nested extensions of *tall* have nobody at `i0`, Ann at `i1` and both at `i2`. -/
@[instance_reducible] def nested : I3 → W → (Language.monadic Pred1).Structure Entity2 :=
  interpOf fun i _ ↦ match i with
    | .i0 => ∅
    | .i1 => {.ann}
    | .i2 => {.ann, .ben}

theorem noReversal_nested : NoReversal nested ord₃ Pred1.tall .w0 .ben .ann := by decide

theorem ann_taller_nested :
    Eval nested (.comp Ta Tb) ord₃ .i1 .w0 ∧ ∀ i : I3, ¬ Eval nested (.comp Tb Ta) ord₃ i .w0 := by
  decide

/-- The reversing extensions of *tall* have Ann at `i0`, Ben at `i1` and both at `i2`. -/
@[instance_reducible] def reversing : I3 → W → (Language.monadic Pred1).Structure Entity2 :=
  interpOf fun i _ ↦ match i with
    | .i0 => {.ann}
    | .i1 => {.ben}
    | .i2 => {.ann, .ben}

theorem diverge_without_noReversal :
    ¬ NoReversal reversing ord₃ Pred1.tall .w0 .ben .ann ∧
    ¬ Eval reversing (.comp Ta Tb) ord₃ .i2 .w0 ∧
    (interpretationDelineation reversing ord₃ Pred1.tall .w0 .i2).Comparative
      .ann .ben :=
  ⟨by decide, by decide,
    (delineation_comparative_iff reversing ord₃ Pred1.tall .w0 .i2 .ann .ben).mpr
      ⟨.i0, by decide, by decide, by decide⟩⟩

/-! ### Equative transitivity -/

/-- Three predicates. -/
inductive Pred3 | linguist | philosopher | psychologist
  deriving DecidableEq, Repr, Fintype

/-- Four interpretations. -/
inductive I4 | i | j | k | l
  deriving DecidableEq, Repr, Fintype

/-- The ranks of the supplement's Figure 1, with `i`, `j` and `k` tied above `l`. -/
def rank₄ : I4 → ℕ
  | .l => 0
  | _ => 1

/-- The ordering of the supplement's Figure 1. -/
def ord₄ : SemanticOrdering I4 := .ofRank rank₄

instance : DecidableRel ord₄.le := inferInstanceAs (DecidableRel (SemanticOrdering.ofRank rank₄).le)

/-- The model of the supplement's Figure 1. Ann is a linguist and a philosopher at `i`, only a
philosopher at `j`, a linguist and a psychologist at `k`, and a philosopher and a psychologist at
`l`. -/
@[instance_reducible] def counterexample : I4 → W → (Language.monadic Pred3).Structure Entity :=
  interpOf fun x P ↦ match x, P with
    | .i, .linguist | .i, .philosopher | .j, .philosopher | .k, .linguist | .k, .psychologist
    | .l, .philosopher | .l, .psychologist => {.ann}
    | _, _ => ∅

/-- *Ann is a linguist*, *a philosopher*, *a psychologist*. -/
abbrev La₄ : ComparativeFormula (Language.monadic Pred3) Entity := .matom Pred3.linguist .ann
abbrev Pa₄ : ComparativeFormula (Language.monadic Pred3) Entity := .matom Pred3.philosopher .ann
abbrev Ca₄ : ComparativeFormula (Language.monadic Pred3) Entity := .matom Pred3.psychologist .ann

/-- The basic equative is not transitive, as Ann's case at the top of Figure 1 shows. -/
theorem equi_not_trans :
    Eval counterexample (La₄.equi Pa₄) ord₄ .i .w0 ∧
      Eval counterexample (Pa₄.equi Ca₄) ord₄ .i .w0 ∧
      Eval counterexample (.comp La₄ Ca₄) ord₄ .i .w0 := by
  decide

/-- The revised semantics makes Ann as much a linguist as a psychologist at the top of Figure 1. -/
theorem evalRevised_equi_counterexample :
    EvalRevised counterexample (La₄.equi Pa₄) ord₄ .i .w0 ∧
      EvalRevised counterexample (Pa₄.equi Ca₄) ord₄ .i .w0 ∧
      EvalRevised counterexample (La₄.equi Ca₄) ord₄ .i .w0 := by
  decide

end RudolphKocurek2024

