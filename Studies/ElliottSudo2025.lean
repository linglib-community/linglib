module

public import Linglib.Data.Examples.ElliottSudo2025
public import Linglib.Semantics.Dynamic.Bilateral
public import Studies.GroenendijkStokhof1991

/-!
# Elliott and Sudo (2025): Free choice with anaphora

This file formalizes [elliott-sudo-2025]'s account of free choice with anaphora in Bilateral
Update Semantics. A bathroom disjunction, *either there's no bathroom or it's in a funny place*,
embedded under an existential modal yields the inferences that possibly there is no bathroom and
that possibly there is a bathroom in a funny place, an inference that the classical schema
`◇(φ ∨ ψ) ⊨ ◇φ ∧ ◇ψ` ([kamp-1973], [zimmermann-2000]) cannot state, since its second conjunct
would contain a free pronoun. The modified schema `◇(φ ∨ ψ) ⊨ ◇φ ∧ ◇(¬φ ∧ ψ)` together with
Double Negation Elimination and Egli's theorem derives it, and neither exhaustification over
structurally simpler alternatives ([bar-lev-fox-2020], [fox-katzir-2011], [trinh-haida-2015]) nor
classical update semantics ([heim-1982], [veltman-1996], [groenendijk-stokhof-1991]), where
negation blocks anaphora and DNE fails, validates all three. In Bilateral Update Semantics
([krahmer-muskens-1995]) every sentence has a positive and a negative update over Heimian states,
negation swaps them, so DNE is definitional; an existential introduces its referent by random
assignment in the positive dimension only; the connectives compose the dimensions along the
Strong Kleene tables, so the negation of a negated existential in the first disjunct makes the
referent available to the second, and a bathroom disjunction gets existential truth conditions;
epistemic modals are tests on the state after [veltman-1996], with subsistence
([groenendijk-stokhof-veltman-1996]) for the negative update; and modal disjunction adds to the
positive update the precondition that each disjunct be responsible for some possibilities, which
validates free choice ([simons-2005], [aloni-2022]) while leaving dual prohibition intact. The
same precondition on the negative update of conjunction gives negative free choice, and the dual
universal gives distributive inferences, both with anaphora.

## Implementation notes

* The substrate `BilateralDen` supplies the dimensions, the connectives (61) and (64), the
  existential (44)–(45), the unknown update (53) and assertability (54); this file adds the
  modals (73) and (77), the two parts of a disjunction's positive update (92), modal disjunction
  (96) and its conjunctive counterpart (132).
* The derivations (93), (94) and (70) hold at states where the referent is novel, the article's
  initial states; the bivalence of an existential, that its unknown update is empty, needs a
  nonempty domain. Free choice with anaphora (24) is then derived from the preconditions of
  modal disjunction rather than assumed.
* The comparison with DPL ([groenendijk-stokhof-1991]) is the substrate's definitional DNE against
  `GroenendijkStokhof1991.dne_fails_anaphora`.
* The examples are `Data.Examples.ElliottSudo2025`.

## TODO

* The flavour-neutral modals (89), simplification of disjunctive antecedents (127) and wide free
  choice with anaphora (110) are not represented.

## References

* [elliott-sudo-2025]
* [krahmer-muskens-1995]
* [groenendijk-stokhof-1991]
* [groenendijk-stokhof-veltman-1996]
* [veltman-1996]
* [heim-1982]
* [kamp-1973]
* [zimmermann-2000]
* [simons-2005]
* [aloni-2022]
* [bar-lev-fox-2020]
* [fox-katzir-2011]
* [trinh-haida-2015]
-/

@[expose] public section

namespace ElliottSudo2025

open DynamicSemantics BilateralDen ElliottSudo2025.Examples

/-- A BUS denotation: a bilateral denotation over possibilities with natural-number variables. -/
abbrev BUSDen (W E : Type*) := BilateralDen W ℕ E

/-- A Heimian information state (Def. 3.1). -/
abbrev BUSState (W E : Type*) := Set (Possibility W ℕ (Flat E))

variable {W E : Type*} {s : BUSState W E} {x : ℕ}

/-! ### Novel referents and atomic predications (§3.2–3.3) -/

section Atoms

variable (Q : E → W → Prop)

theorem pred1_positive_of_novel (hx : State.Novel s x) : (pred1 Q x).positive s = ∅ :=
  Set.eq_empty_of_forall_notMem fun p ⟨hp, _, he, _⟩ ↦ Flat.coe_ne_bot (he.symm.trans (hx p hp))

theorem pred1_negative_of_novel (hx : State.Novel s x) : (pred1 Q x).negative s = ∅ :=
  Set.eq_empty_of_forall_notMem fun p ⟨hp, _, he, _⟩ ↦ Flat.coe_ne_bot (he.symm.trans (hx p hp))

theorem pred1_unknownUpdate_of_novel (hx : State.Novel s x) :
    (pred1 Q x).unknownUpdate s = s := by
  ext p
  simp [unknownUpdate, pred1_positive_of_novel Q hx, pred1_negative_of_novel Q hx]

theorem pred1_positive_empty : (pred1 Q x (W := W)).positive ∅ = ∅ := Set.sep_empty _
theorem pred1_negative_empty : (pred1 Q x (W := W)).negative ∅ = ∅ := Set.sep_empty _

-- (45)
theorem exists_negative_subset (φ : BUSDen W E) : (exists_ x φ).negative s ⊆ s :=
  Set.sep_subset _ _

theorem novel_exists_negative (hx : State.Novel s x) (φ : BUSDen W E) :
    State.Novel ((exists_ x φ).negative s) x :=
  hx.mono (exists_negative_subset φ)

-- (76)
theorem mem_lowerClosure_exists_positive_iff {p : Possibility W ℕ (Flat E)} (hp : p ∈ s)
    (hx : State.Novel s x) :
    p ∈ lowerClosure ((exists_ x (pred1 Q x)).positive s) ↔ ∃ e, Q e p.world := by
  constructor
  · rintro ⟨q, ⟨-, e, -, hQ⟩, hpq⟩
    exact ⟨e, (Possibility.le_def.mp hpq).1 ▸ hQ⟩
  · rintro ⟨e, hQ⟩
    refine ⟨p.update x ↑e, ⟨⟨p, hp, e, rfl⟩, e, by simp, hQ⟩, ?_⟩
    refine Possibility.le_def.mpr ⟨rfl, λ v => ?_⟩
    by_cases hv : v = x
    · subst hv
      rw [hx p hp]
      exact bot_le
    · simp [Possibility.update, Function.update_of_ne hv]

-- (55)
theorem exists_unknownUpdate_of_novel [Nonempty E] (hx : State.Novel s x) :
    (exists_ x (pred1 Q x)).unknownUpdate s = ∅ := by
  ext p
  simp only [unknownUpdate, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro hp hpos hneg
  by_cases hw : ∃ e, Q e p.world
  · exact hpos ((mem_lowerClosure_exists_positive_iff Q hp hx).mpr hw)
  · push Not at hw
    refine hneg (subset_lowerClosure ⟨hp, ?_, ?_⟩)
    · rintro ⟨q, ⟨-, e, -, hQ⟩, hqw⟩
      exact hw e (hqw ▸ hQ)
    · obtain ⟨e⟩ := ‹Nonempty E›
      exact ⟨p.update x ↑e, ⟨⟨p, hp, e, rfl⟩, e, by simp, hw e⟩, rfl⟩

theorem exists_assertable [Nonempty E] (hx : State.Novel s x) :
    (exists_ x (pred1 Q x)).assertable s :=
  exists_unknownUpdate_of_novel Q hx

end Atoms

/-! ### Epistemic modals (§3.5) -/

/-- `◇φ` passes positively when the positive update is consistent, (73a). -/
def Possible (φ : BUSDen W E) (s : BUSState W E) : Prop := (φ.positive s).Nonempty

/-- `◇φ` passes negatively when `¬φ` is already implicit in the state modulo anaphoric
information: the state subsists in the negative update, (73b). -/
def Settled (φ : BUSDen W E) (s : BUSState W E) : Prop :=
  lowerClosure s ≤ lowerClosure (φ.negative s)

/-- Epistemic possibility (73): both updates are tests, returning the state or the absurd
state. -/
def diamond (φ : BUSDen W E) : BUSDen W E where
  positive s := {_i ∈ s | Possible φ s}
  negative s := {_i ∈ s | Settled φ s}

/-- Epistemic necessity (77), the dual `□φ = ¬◇¬φ`. -/
def box (φ : BUSDen W E) : BUSDen W E := ~(diamond (~φ))

@[inherit_doc diamond] prefix:max "◇ᵇ" => diamond
@[inherit_doc box] prefix:max "□ᵇ" => box

-- (77a)
theorem box_positive (φ : BUSDen W E) : (□ᵇφ).positive s = (◇ᵇ(~φ)).negative s := rfl

-- (75)
theorem diamond_neg_exists_positive (B : E → W → Prop) :
    (◇ᵇ(~(exists_ x (pred1 B x)))).positive s =
      {_i ∈ s | ((exists_ x (pred1 B x)).negative s).Nonempty} :=
  rfl

-- (76)
theorem settled_neg_exists_iff (B : E → W → Prop) (hx : State.Novel s x) :
    Settled (~(exists_ x (pred1 B x))) s ↔ ∀ p ∈ s, ∃ e, B e p.world := by
  show lowerClosure s ≤ lowerClosure ((exists_ x (pred1 B x)).positive s) ↔ _
  rw [lowerClosure_le]
  exact forall₂_congr λ p hp => mem_lowerClosure_exists_positive_iff B hp hx

/-! ### Modal disjunction (§3.6–3.7) -/

/-- The part of a disjunction's positive update the first disjunct is responsible for, (92a): the
verifying row of the Strong Kleene table. -/
def disjPos1 (φ ψ : BUSDen W E) (s : BUSState W E) : BUSState W E :=
  ψ.positive (φ.positive s) ∪ ψ.negative (φ.positive s) ∪ ψ.unknownUpdate (φ.positive s)

/-- The part the second disjunct is responsible for, (92b): the verifying column. The term
`ψ.positive (φ.negative s)` carries cross-disjunct anaphora. -/
def disjPos2 (φ ψ : BUSDen W E) (s : BUSState W E) : BUSState W E :=
  ψ.positive (φ.positive s) ∪ ψ.positive (φ.negative s) ∪ ψ.positive (φ.unknownUpdate s)

-- (92c), (64)
theorem disj_positive_eq (φ ψ : BUSDen W E) :
    (φ ⊕ ψ).positive s = disjPos1 φ ψ s ∪ disjPos2 φ ψ s := by
  ext p
  simp only [disj, disjPos1, disjPos2, Set.mem_union]
  tauto

open scoped Classical in
/-- Modal disjunction, anaphora-sensitive version (96): the positive update requires each disjunct
to be responsible for some possibilities; the negative update is that of plain disjunction. -/
noncomputable def disjModal (φ ψ : BUSDen W E) : BUSDen W E where
  positive s :=
    if (disjPos1 φ ψ s).Nonempty ∧ (disjPos2 φ ψ s).Nonempty then (φ ⊕ ψ).positive s else ∅
  negative := (φ ⊕ ψ).negative

@[inherit_doc] notation:60 φ " ∨ᶠᶜ " ψ => disjModal φ ψ

theorem fc_preconditions (φ ψ : BUSDen W E) (h : Possible (φ ∨ᶠᶜ ψ) s) :
    (disjPos1 φ ψ s).Nonempty ∧ (disjPos2 φ ψ s).Nonempty := by
  unfold Possible disjModal at h
  by_cases hc : (disjPos1 φ ψ s).Nonempty ∧ (disjPos2 φ ψ s).Nonempty
  · exact hc
  · simp only [hc, ↓reduceIte] at h
    exact (Set.not_nonempty_empty h).elim

section Atomic

variable (c t : W → Prop)

theorem disjPos1_atom : disjPos1 (atom c) (atom t) s = (atom c (V := ℕ) (E := E)).positive s := by
  rw [disjPos1, unknownUpdate_atom, Set.union_empty, atom_complementary]

theorem disjPos2_atom : disjPos2 (atom c) (atom t) s = (atom t (V := ℕ) (E := E)).positive s := by
  rw [disjPos2, unknownUpdate_atom]
  ext p
  simp only [atom, Set.mem_union, Set.mem_ofPred_eq, Set.mem_empty_iff_false, false_and, or_false]
  tauto

-- (84)
theorem possible_disjModal_atom_iff :
    Possible (atom c ∨ᶠᶜ atom t) s ↔ Possible (atom c) s ∧ Possible (atom t) s := by
  have key : (disjPos1 (atom c) (atom t) s).Nonempty ∧ (disjPos2 (atom c) (atom t) s).Nonempty ↔
      ((atom c (V := ℕ) (E := E)).positive s).Nonempty ∧
        ((atom t (V := ℕ) (E := E)).positive s).Nonempty := by
    rw [disjPos1_atom, disjPos2_atom]
  simp only [Possible, disjModal]
  constructor
  · intro h
    by_contra hc
    rw [ite_eq_right (key.not.mpr hc)] at h
    exact Set.not_nonempty_empty h
  · rintro ⟨hc, ht⟩
    rw [ite_eq_left (key.mpr ⟨hc, ht⟩), disj_positive_eq, disjPos1_atom]
    exact hc.mono Set.subset_union_left

theorem lowerClosure_le_sep_iff (pred : W → Prop) :
    lowerClosure s ≤ lowerClosure {p ∈ s | pred p.world} ↔ ∀ p ∈ s, pred p.world := by
  rw [lowerClosure_le]
  refine forall₂_congr λ p hp => ⟨?_, λ h => subset_lowerClosure ⟨hp, h⟩⟩
  rintro ⟨q, ⟨-, hq⟩, hpq⟩
  exact (Possibility.le_def.mp hpq).1 ▸ hq

-- (88)
theorem settled_disjModal_atom_iff :
    Settled (atom c ∨ᶠᶜ atom t) s ↔ ∀ p ∈ s, ¬ c p.world ∧ ¬ t p.world := by
  show lowerClosure s ≤ lowerClosure {p ∈ {p ∈ s | ¬ c p.world} | ¬ t p.world} ↔ _
  rw [show {p ∈ {p ∈ s | ¬ c p.world} | ¬ t p.world} = {p ∈ s | ¬ c p.world ∧ ¬ t p.world} from
    Set.ext λ _ => and_assoc, lowerClosure_le_sep_iff (λ w => ¬ c w ∧ ¬ t w)]

-- (80)
theorem dual_prohibition (h : Settled (atom c ∨ᶠᶜ atom t) s) :
    Settled (atom c (V := ℕ) (E := E)) s ∧ Settled (atom t (V := ℕ) (E := E)) s := by
  rw [settled_disjModal_atom_iff] at h
  exact ⟨(lowerClosure_le_sep_iff (λ w => ¬ c w)).mpr λ p hp => (h p hp).1,
    (lowerClosure_le_sep_iff (λ w => ¬ t w)).mpr λ p hp => (h p hp).2⟩

end Atomic

/-! ### The bathroom disjunction and free choice with anaphora (§3.4.2, §3.7) -/

section Bathroom

variable (P Q : E → W → Prop)

-- (93)
theorem disjPos1_bathroom (hx : State.Novel s x) :
    disjPos1 (~(exists_ x (pred1 P x))) (pred1 Q x) s = (exists_ x (pred1 P x)).negative s := by
  have hn := novel_exists_negative hx (pred1 P x)
  simp [disjPos1, neg, pred1_positive_of_novel Q hn, pred1_negative_of_novel Q hn,
    pred1_unknownUpdate_of_novel Q hn]

-- (94)
theorem disjPos2_bathroom [Nonempty E] (hx : State.Novel s x) :
    disjPos2 (~(exists_ x (pred1 P x))) (pred1 Q x) s =
      (pred1 Q x).positive ((exists_ x (pred1 P x)).positive s) := by
  have hn := novel_exists_negative hx (pred1 P x)
  show (pred1 Q x).positive ((exists_ x (pred1 P x)).negative s) ∪
      (pred1 Q x).positive ((exists_ x (pred1 P x)).positive s) ∪
      (pred1 Q x).positive ((~(exists_ x (pred1 P x))).unknownUpdate s) = _
  rw [unknownUpdate_neg, exists_unknownUpdate_of_novel P hx, pred1_positive_empty,
    pred1_positive_of_novel Q hn, Set.empty_union, Set.union_empty]

-- (70)
theorem bathroom_positive [Nonempty E] (hx : State.Novel s x) :
    ((~(exists_ x (pred1 P x))) ⊕ pred1 Q x).positive s =
      (exists_ x (pred1 P x)).negative s ∪
        (pred1 Q x).positive ((exists_ x (pred1 P x)).positive s) := by
  rw [disj_positive_eq, disjPos1_bathroom P Q hx, disjPos2_bathroom P Q hx]

-- (66)
theorem bathroom_negative :
    ((~(exists_ x (pred1 P x))) ⊕ pred1 Q x).negative s =
      (pred1 Q x).negative ((exists_ x (pred1 P x)).positive s) :=
  rfl

-- (24), (99)
theorem fc_with_anaphora [Nonempty E] (hx : State.Novel s x)
    (h : Possible ((~(exists_ x (pred1 P x))) ∨ᶠᶜ pred1 Q x) s) :
    ((exists_ x (pred1 P x)).negative s).Nonempty ∧
      ((pred1 Q x).positive ((exists_ x (pred1 P x)).positive s)).Nonempty := by
  obtain ⟨h₁, h₂⟩ := fc_preconditions _ _ h
  rw [disjPos1_bathroom P Q hx] at h₁
  rw [disjPos2_bathroom P Q hx] at h₂
  exact ⟨h₁, h₂⟩

-- (25), (90c)
theorem classical_conclusion_impossible (hx : State.Novel s x) : ¬ Possible (pred1 Q x) s := by
  rw [Possible, pred1_positive_of_novel Q hx]
  exact Set.not_nonempty_empty

end Bathroom

/-! ### Double negation and Egli's theorem (§2.1, §3.3–3.4) -/

-- (49) [groenendijk-stokhof-1991]
theorem dne_bus_not_dpl [Nontrivial E] :
    (∀ φ : BUSDen W E, ~~φ = φ) ∧
      ∃ (x : ℕ) (φ : Update (Assignment E)),
        Update.test (Update.neg (Update.test (Update.neg (Update.dexists x φ)))) ≠
          Update.dexists x φ :=
  ⟨BilateralDen.neg_neg, GroenendijkStokhof1991.dne_fails_anaphora⟩

-- (59), (62)
theorem negative_egli_fails :
    ∃ (W E : Type) (x : ℕ) (P Q : E → W → Prop) (s : BUSState W E),
      (exists_ x (pred1 P x ⊙ pred1 Q x)).negative s ≠
        (exists_ x (pred1 P x) ⊙ pred1 Q x).negative s := by
  refine ⟨Unit, Unit, 0, λ _ _ => True, λ _ _ => False, {⟨(), λ _ => ⊥⟩}, λ h => ?_⟩
  have hmem : (⟨(), λ _ => ⊥⟩ : Possibility Unit ℕ (Flat Unit)).update 0 ↑() ∈
      (exists_ 0 (pred1 (λ _ _ => True) 0) ⊙ pred1 (λ _ _ => False) 0).negative
        {⟨(), λ _ => ⊥⟩} :=
    Or.inl (Or.inr ⟨⟨⟨_, rfl, (), rfl⟩, (), by simp, trivial⟩, (), by simp, not_false⟩)
  rw [← h] at hmem
  have := congrArg (fun p : Possibility Unit ℕ (Flat Unit) ↦ p.assignment 0)
    (Set.mem_singleton_iff.mp (exists_negative_subset _ hmem))
  simp [Possibility.update] at this

/-! ### Partial familiarity (§3.3, (56)–(57)) -/

section PartialFamiliarity

/-- The worlds of (56)–(57): `a` is `P` at `wa`, `b` at `wb`, nothing at `w0`. -/
inductive PWorld
  | wa
  | wb
  | w0
  deriving DecidableEq

inductive PEntity
  | a
  | b
  deriving DecidableEq

def pHolds : PEntity → PWorld → Prop
  | .a, .wa => True
  | .b, .wb => True
  | _, _ => False

/-- The assignment `[x → e]`: register 0 defined, all else `∗`. -/
def xTo (e : PEntity) : ℕ → Flat PEntity := fun n ↦ if n = 0 then ↑e else ⊥

/-- The initial assignment `[]`. -/
def blank : ℕ → Flat PEntity := fun _ ↦ ⊥

open PWorld in
/-- The state of (56), where `x` is defined at the `P`-worlds only. -/
def s56 : BUSState PWorld PEntity :=
  {⟨wa, xTo .a⟩, ⟨wa, xTo .b⟩, ⟨wb, xTo .a⟩, ⟨wb, xTo .b⟩, ⟨w0, blank⟩}

-- (56a)
theorem mem_positive_s56 :
    (⟨.wa, xTo .a⟩ : Possibility PWorld ℕ (Flat PEntity)) ∈ (pred1 pHolds 0).positive s56 :=
  ⟨by simp [s56], .a, by simp [xTo], trivial⟩

-- (56c)
theorem gap_mem_unknownUpdate_s56 :
    (⟨.w0, blank⟩ : Possibility PWorld ℕ (Flat PEntity)) ∈ (pred1 pHolds 0).unknownUpdate s56 := by
  refine ⟨by simp [s56], ?_, ?_⟩ <;>
  · rintro ⟨q, ⟨hq, e, he, -⟩, hw, -⟩
    rcases (by simpa [s56] using hq : q = _ ∨ q = _ ∨ q = _ ∨ q = _ ∨ q = _)
      with rfl | rfl | rfl | rfl | rfl <;>
      first
        | exact absurd he Flat.bot_ne_coe
        | simp_all

-- (56)
theorem not_assertable_s56 : ¬ (pred1 pHolds 0).assertable s56 := λ h =>
  Set.notMem_empty _ (h ▸ gap_mem_unknownUpdate_s56)

theorem not_familiar_s56 : ¬ State.Familiar s56 0 := λ h =>
  h ⟨.w0, blank⟩ (show ⟨PWorld.w0, blank⟩ ∈ s56 by simp [s56]) rfl

open PWorld in
/-- The state of (57): `x` is undefined at some possibility of each world but defined at another
with the same world. -/
def s57 : BUSState PWorld PEntity := {⟨wa, xTo .a⟩, ⟨wa, blank⟩, ⟨wb, xTo .b⟩, ⟨wb, blank⟩}

-- (57)
theorem assertable_s57_not_familiar :
    (pred1 pHolds 0).assertable s57 ∧ ¬ State.Familiar s57 0 := by
  refine ⟨?_, fun h ↦ h ⟨.wa, blank⟩ (show ⟨PWorld.wa, blank⟩ ∈ s57 by simp [s57]) rfl⟩
  apply Set.eq_empty_of_forall_notMem
  rintro p ⟨hp, hpos, -⟩
  apply hpos
  have ha : (⟨.wa, xTo .a⟩ : Possibility PWorld ℕ (Flat PEntity)) ∈ (pred1 pHolds 0).positive s57 :=
    ⟨by simp [s57], .a, by simp [xTo], trivial⟩
  have hb : (⟨.wb, xTo .b⟩ : Possibility PWorld ℕ (Flat PEntity)) ∈ (pred1 pHolds 0).positive s57 :=
    ⟨by simp [s57], .b, by simp [xTo], trivial⟩
  have hle : ∀ w e, (⟨w, blank⟩ : Possibility PWorld ℕ (Flat PEntity)) ≤ ⟨w, xTo e⟩ :=
    λ w e => Possibility.le_def.mpr ⟨rfl, λ _ => bot_le⟩
  rcases (by simpa [s57] using hp : p = _ ∨ p = _ ∨ p = _ ∨ p = _) with rfl | rfl | rfl | rfl
  · exact subset_lowerClosure ha
  · exact ⟨_, ha, hle _ _⟩
  · exact subset_lowerClosure hb
  · exact ⟨_, hb, hle _ _⟩

end PartialFamiliarity

/-! ### Distributive inferences with anaphora (§5.2) -/

-- (121)
theorem distributive_preconditions (φ ψ : BUSDen W E) (y : ℕ)
    (h : Possible (forall_ y (φ ∨ᶠᶜ ψ)) s) :
    (disjPos1 φ ψ (State.randomAssign s y)).Nonempty ∧
      (disjPos2 φ ψ (State.randomAssign s y)).Nonempty := by
  obtain ⟨p, -, -, q, hq, -⟩ := h
  exact fc_preconditions φ ψ ⟨q, hq⟩

/-! ### Negative free choice (§5.4) -/

/-- The part of a conjunction's negative update the first conjunct is responsible for: the
falsifying row of the Strong Kleene table (61). -/
def conjNeg1 (φ ψ : BUSDen W E) (s : BUSState W E) : BUSState W E :=
  ψ.positive (φ.negative s) ∪ ψ.negative (φ.negative s) ∪ ψ.unknownUpdate (φ.negative s)

/-- The part the second conjunct is responsible for: the falsifying column. -/
def conjNeg2 (φ ψ : BUSDen W E) (s : BUSState W E) : BUSState W E :=
  ψ.negative (φ.negative s) ∪ ψ.negative (φ.positive s) ∪ ψ.negative (φ.unknownUpdate s)

-- (61)
theorem conj_negative_eq (φ ψ : BUSDen W E) :
    (φ ⊙ ψ).negative s = conjNeg1 φ ψ s ∪ conjNeg2 φ ψ s := by
  ext p
  simp only [conj, conjNeg1, conjNeg2, Set.mem_union]
  tauto

open scoped Classical in
/-- Negative modal conjunction (132): the negative update requires each conjunct to be
responsible for some possibilities. -/
noncomputable def conjModal (φ ψ : BUSDen W E) : BUSDen W E where
  positive := (φ ⊙ ψ).positive
  negative s :=
    if (conjNeg1 φ ψ s).Nonempty ∧ (conjNeg2 φ ψ s).Nonempty then (φ ⊙ ψ).negative s else ∅

-- (130)
theorem negative_modal_conjunction (φ ψ : BUSDen W E) (h : Possible (~(conjModal φ ψ)) s) :
    (conjNeg1 φ ψ s).Nonempty ∧ (conjNeg2 φ ψ s).Nonempty := by
  unfold Possible neg conjModal at h
  by_cases hc : (conjNeg1 φ ψ s).Nonempty ∧ (conjNeg2 φ ψ s).Nonempty
  · exact hc
  · simp only [hc, ↓reduceIte] at h
    exact (Set.not_nonempty_empty h).elim

-- (131)
theorem dual_permission (φ ψ : BUSDen W E) (hφ : CCP.IsEliminative φ.positive)
    (hm : Monotone ψ.positive) (he : CCP.IsEliminative ψ.positive) (h : Possible (φ ⊙ ψ) s) :
    Possible φ s ∧ Possible ψ s := by
  obtain ⟨p, hp⟩ := h
  exact ⟨⟨p, he _ hp⟩, ⟨p, hm (hφ s) hp⟩⟩

-- (129)
theorem negative_fc_with_anaphora [Nonempty E] (A B : E → W → Prop) (hx : State.Novel s x)
    (h : Possible (~(conjModal (exists_ x (pred1 A x)) (pred1 B x))) s) :
    ((exists_ x (pred1 A x)).negative s).Nonempty ∧
      ((pred1 B x).negative ((exists_ x (pred1 A x)).positive s)).Nonempty := by
  obtain ⟨h₁, h₂⟩ := negative_modal_conjunction _ _ h
  have hn := novel_exists_negative hx (pred1 A x)
  refine ⟨h₁.mono ?_, ?_⟩
  · rw [conjNeg1, pred1_positive_of_novel B hn, pred1_negative_of_novel B hn,
      pred1_unknownUpdate_of_novel B hn]
    simp
  · rwa [conjNeg2, pred1_negative_of_novel B hn, exists_unknownUpdate_of_novel A hx,
      pred1_negative_empty, Set.empty_union, Set.union_empty] at h₂

end ElliottSudo2025
