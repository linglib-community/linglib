module

public import Linglib.Data.Examples.ElliottSudo2025
public import Studies.Elliott2023
public import Studies.GroenendijkStokhof1991

/-!
# Elliott and Sudo (2025): Free choice with anaphora

This file formalizes Elliott and Sudo's account of free choice with anaphora in Bilateral Update
Semantics. Under an epistemic modal, *either there's no bathroom or it's in a funny place* implies
that possibly there is no bathroom and possibly there is one in a funny place, which the classical
schema cannot state without a free pronoun. Modal disjunction requires each disjunct to be
responsible for some point of the positive update, and so [derives free choice with
anaphora](##ElliottSudo2025.fc_with_anaphora) and [keeps dual
prohibition](##ElliottSudo2025.dual_prohibition); the same requirement on negated conjunction
[derives negative free choice](##ElliottSudo2025.negative_fc_with_anaphora). Double negation is
definitional, and [fails in dynamic predicate logic](##ElliottSudo2025.dne_bus_not_dpl).

## Implementation notes

* The existential is the substrate's, whose negative update keeps the points that subsist in the
  negative update of the scope, as in Elliott's earlier presentation. The article's (45) compares
  worlds instead; [the two agree at initial states](##ElliottSudo2025.existsNegative_eq_of_initial),
  where the article computes its examples.
* The derivations (93) and (94) hold where the referent is novel. The updates (70) and (66) of the
  bathroom disjunction are Elliott's (33) and (35), and the failure (62) of Egli's theorem in the
  negative dimension is Elliott's (41b), all in `Elliott2023`.
* Modal disjunction (96) and its conjunctive counterpart (132) are defined here, with the parts
  (92) of a disjunction's positive update.

## Errata

* Descent (Defs. 3.3, 3.4) requires only a larger domain, though the prose glosses a descendant as
  identical except for more anaphoric information. So read, [`◇P(x)` passes both positively and
  negatively](##ElliottSudo2025.possible_and_domSubsists_negative) at a state where `x` is `P` at
  one point of a world and not at another; the substrate takes extension.
* (45) compares worlds, so at the state `s[ε_y]` of (121), [where one student read a novel and
  another read none, it retains no point](##ElliottSudo2025.existsNegative_misses_reader), against
  the gloss that (121) requires some student to have read no novel, which the subsistence-based
  negative update meets.

## TODO

* The flavour-neutral modals (89), simplification of disjunctive antecedents (127) and wide free
  choice with anaphora (110) are not represented.

## References

* [elliott-sudo-2025]
* [elliott-2023]
* [krahmer-muskens-1995]
* [groenendijk-stokhof-1991]
* [groenendijk-stokhof-veltman-1996]
* [veltman-1996]
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

open DynamicSemantics BilateralDen

/-- A BUS denotation: a bilateral denotation over possibilities with natural-number variables. -/
abbrev BUSDen (W E : Type*) := BilateralDen W ℕ E

/-- A Heimian information state (Def. 3.1). -/
abbrev BUSState (W E : Type*) := Set (Possibility W ℕ (Flat E))

variable {W E : Type*} {s : BUSState W E} {x : ℕ}

/-! ### The negative update of an existential (§3.2) -/

/-- The negative update of `∃x φ` as (45) prints it: the points of `s` whose world the positive
update does not reach and the negative update of the scope after random assignment does. -/
def existsNegative (x : ℕ) (φ : BUSDen W E) (s : BUSState W E) : BUSState W E :=
  {p ∈ s | p.world ∉ Possibility.world '' φ.positive (State.randomAssign s x) ∧
    p.world ∈ Possibility.world '' φ.negative (State.randomAssign s x)}

theorem mem_lowerClosure_iff_of_eq_bot {p : Possibility W ℕ (Flat E)}
    (hp : ∀ v, p.assignment v = ⊥) (t : BUSState W E) :
    p ∈ lowerClosure t ↔ p.world ∈ Possibility.world '' t :=
  ⟨fun ⟨q, hq, hpq⟩ ↦ ⟨q, hq, (Possibility.le_def.mp hpq).1.symm⟩,
    fun ⟨q, hq, hqw⟩ ↦ ⟨q, hq, Possibility.le_def.mpr ⟨hqw.symm, fun v ↦ hp v ▸ bot_le⟩⟩⟩

theorem existsNegative_eq_of_initial (hs : ∀ p ∈ s, ∀ v, p.assignment v = ⊥) (φ : BUSDen W E) :
    existsNegative x φ s = (exists_ x φ).negative s :=
  Set.ext fun p ↦ and_congr_right fun hp ↦
    and_congr (not_congr (mem_lowerClosure_iff_of_eq_bot (hs p hp) _).symm)
      (mem_lowerClosure_iff_of_eq_bot (hs p hp) _).symm

-- (55)
theorem exists_assertable [Nonempty E] (Q : E → W → Prop) (hx : State.Novel s x) :
    (exists_ x (pred1 Q x)).Assertable s :=
  unknownUpdate_exists_pred1 Q hx

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
  exact forall₂_congr fun p hp ↦ mem_lowerClosure_positive_pred1_randomAssign B hp hx

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
  rw [disjPos1, unknownUpdate_atom, Set.union_empty, positive_union_negative_atom]

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
  refine forall₂_congr fun p hp ↦ ⟨?_, fun h ↦ subset_lowerClosure ⟨hp, h⟩⟩
  rintro ⟨q, ⟨-, hq⟩, hpq⟩
  exact (Possibility.le_def.mp hpq).1 ▸ hq

-- (88)
theorem settled_disjModal_atom_iff :
    Settled (atom c ∨ᶠᶜ atom t) s ↔ ∀ p ∈ s, ¬ c p.world ∧ ¬ t p.world := by
  show lowerClosure s ≤ lowerClosure {p ∈ {p ∈ s | ¬ c p.world} | ¬ t p.world} ↔ _
  rw [show {p ∈ {p ∈ s | ¬ c p.world} | ¬ t p.world} = {p ∈ s | ¬ c p.world ∧ ¬ t p.world} from
    Set.ext fun _ ↦ and_assoc, lowerClosure_le_sep_iff (fun w ↦ ¬ c w ∧ ¬ t w)]

/-- Modal disjunction leaves dual prohibition intact: if `◇(c ∨ t)` passes negatively, so do `◇c`
and `◇t`, (80). -/
theorem dual_prohibition (h : Settled (atom c ∨ᶠᶜ atom t) s) :
    Settled (atom c (V := ℕ) (E := E)) s ∧ Settled (atom t (V := ℕ) (E := E)) s := by
  rw [settled_disjModal_atom_iff] at h
  exact ⟨(lowerClosure_le_sep_iff (fun w ↦ ¬ c w)).mpr fun p hp ↦ (h p hp).1,
    (lowerClosure_le_sep_iff (fun w ↦ ¬ t w)).mpr fun p hp ↦ (h p hp).2⟩

end Atomic

/-! ### The bathroom disjunction and free choice with anaphora (§3.4.2, §3.7) -/

section Bathroom

variable (P Q : E → W → Prop)

-- (93), [elliott-2023] (31)
theorem disjPos1_bathroom (hx : State.Novel s x) :
    disjPos1 (~(exists_ x (pred1 P x))) (pred1 Q x) s = (exists_ x (pred1 P x)).negative s :=
  Elliott2023.positive_donkey_first P Q hx

-- (94)
theorem disjPos2_bathroom [Nonempty E] (hx : State.Novel s x) :
    disjPos2 (~(exists_ x (pred1 P x))) (pred1 Q x) s =
      (pred1 Q x).positive ((exists_ x (pred1 P x)).positive s) := by
  have hn := hx.mono (negative_exists_subset x (pred1 P x) s)
  rw [disjPos2, ← Elliott2023.positive_donkey_second P Q hx]
  show (pred1 Q x).positive ((exists_ x (pred1 P x)).negative s) ∪ _ ∪ _ = _
  rw [positive_pred1_of_novel Q hn, Set.empty_union]

/-- Free choice with anaphora: if the bathroom disjunction with modal disjunction is possible,
so are `¬∃x P(x)` and `∃x (P(x) ∧ Q(x))`, (24). -/
theorem fc_with_anaphora [Nonempty E] (hx : State.Novel s x)
    (h : Possible ((~(exists_ x (pred1 P x))) ∨ᶠᶜ pred1 Q x) s) :
    Possible (~(exists_ x (pred1 P x))) s ∧ Possible (exists_ x (pred1 P x ⊙ pred1 Q x)) s := by
  obtain ⟨h₁, h₂⟩ := fc_preconditions _ _ h
  rw [disjPos1_bathroom P Q hx] at h₁
  rw [disjPos2_bathroom P Q hx] at h₂
  exact ⟨h₁, h₂⟩

theorem ex22 [Nonempty E] (hx : State.Novel s x) :
    (Possible ((~(exists_ x (pred1 P x))) ∨ᶠᶜ pred1 Q x) s →
      Possible (~(exists_ x (pred1 P x))) s ∧ Possible (exists_ x (pred1 P x ⊙ pred1 Q x)) s) ↔
      Examples.ex_22.judgment = .acceptable :=
  iff_of_true (fc_with_anaphora P Q hx) rfl

-- (25), (90c)
theorem classical_conclusion_impossible (hx : State.Novel s x) : ¬ Possible (pred1 Q x) s := by
  rw [Possible, positive_pred1_of_novel Q hx]
  exact Set.not_nonempty_empty

end Bathroom

/-! ### Double negation (§2.1, §3.3) -/

-- (49) [groenendijk-stokhof-1991]
theorem dne_bus_not_dpl [Nontrivial E] :
    (∀ φ : BUSDen W E, ~~φ = φ) ∧
      ∃ (x : ℕ) (φ : Update (Assignment E)),
        Update.test (Update.neg (Update.test (Update.neg (Update.dexists x φ)))) ≠
          Update.dexists x φ :=
  ⟨BilateralDen.neg_neg, GroenendijkStokhof1991.dne_fails_anaphora⟩

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
theorem not_assertable_s56 : ¬ (pred1 pHolds 0).Assertable s56 := fun h ↦
  Set.notMem_empty _ (h ▸ gap_mem_unknownUpdate_s56)

theorem not_familiar_s56 : ¬ State.Familiar s56 0 := fun h ↦
  h ⟨.w0, blank⟩ (show ⟨PWorld.w0, blank⟩ ∈ s56 by simp [s56]) rfl

open PWorld in
/-- The state of (57): `x` is undefined at some possibility of each world but defined at another
with the same world. -/
def s57 : BUSState PWorld PEntity := {⟨wa, xTo .a⟩, ⟨wa, blank⟩, ⟨wb, xTo .b⟩, ⟨wb, blank⟩}

-- (57)
theorem assertable_s57_not_familiar :
    (pred1 pHolds 0).Assertable s57 ∧ ¬ State.Familiar s57 0 := by
  refine ⟨?_, fun h ↦ h ⟨.wa, blank⟩ (show ⟨PWorld.wa, blank⟩ ∈ s57 by simp [s57]) rfl⟩
  apply Set.eq_empty_of_forall_notMem
  rintro p ⟨hp, hpos, -⟩
  apply hpos
  have ha : (⟨.wa, xTo .a⟩ : Possibility PWorld ℕ (Flat PEntity)) ∈ (pred1 pHolds 0).positive s57 :=
    ⟨by simp [s57], .a, by simp [xTo], trivial⟩
  have hb : (⟨.wb, xTo .b⟩ : Possibility PWorld ℕ (Flat PEntity)) ∈ (pred1 pHolds 0).positive s57 :=
    ⟨by simp [s57], .b, by simp [xTo], trivial⟩
  have hle : ∀ w e, (⟨w, blank⟩ : Possibility PWorld ℕ (Flat PEntity)) ≤ ⟨w, xTo e⟩ :=
    fun w e ↦ Possibility.le_def.mpr ⟨rfl, fun _ ↦ bot_le⟩
  rcases (by simpa [s57] using hp : p = _ ∨ p = _ ∨ p = _ ∨ p = _) with rfl | rfl | rfl | rfl
  · exact subset_lowerClosure ha
  · exact ⟨_, ha, hle _ _⟩
  · exact subset_lowerClosure hb
  · exact ⟨_, hb, hle _ _⟩

/-- The state where `x` is `a` at one point of `wa` and `b` at another. -/
def sab : BUSState PWorld PEntity := {⟨.wa, xTo .a⟩, ⟨.wa, xTo .b⟩}

/-- State subsistence (Def. 3.4) with descent as Def. 3.3 prints it: every point of `s` has a point
of `s'` at its world whose domain includes its own. -/
def DomSubsists (s s' : BUSState W E) : Prop :=
  ∀ p ∈ s, ∃ q ∈ s', p.world = q.world ∧ p.domain ⊆ q.domain

/-- With descent as printed, `◇P(x)` passes both positively and negatively at `sab`: the state
subsists in the negative update of `P(x)` by Def. 3.4, though not by extension. -/
theorem possible_and_domSubsists_negative :
    Possible (pred1 pHolds 0) sab ∧ DomSubsists sab ((pred1 pHolds 0).negative sab) ∧
      ¬ Settled (pred1 pHolds 0) sab := by
  have hb : (⟨.wa, xTo .b⟩ : Possibility PWorld ℕ (Flat PEntity)) ∈
      (pred1 pHolds 0).negative sab :=
    ⟨by simp [sab], .b, by simp [xTo], id⟩
  refine ⟨⟨⟨.wa, xTo .a⟩, by simp [sab], .a, by simp [xTo], trivial⟩, ?_, fun h ↦ ?_⟩
  · rintro p (rfl | rfl) <;> refine ⟨_, hb, rfl, fun v hv ↦ ?_⟩ <;>
      by_cases h : v = 0 <;> simp_all [xTo, Possibility.mem_domain]
  · obtain ⟨q, ⟨hq, e, he, hP⟩, hpq⟩ := h (subset_lowerClosure
      (show (⟨.wa, xTo .a⟩ : Possibility PWorld ℕ (Flat PEntity)) ∈ sab from Or.inl rfl))
    have h0 := (Possibility.le_def.mp hpq).2 0
    rw [he] at h0
    obtain rfl : PEntity.a = e := by simpa [xTo] using h0
    rcases hq with rfl | rfl
    · exact hP trivial
    · simp [xTo] at he

end PartialFamiliarity

/-! ### Distributive inferences with anaphora (§5.2) -/

-- (121)
theorem distributive_preconditions (φ ψ : BUSDen W E) (y : ℕ)
    (h : Possible (forall_ y (φ ∨ᶠᶜ ψ)) s) :
    (disjPos1 φ ψ (State.randomAssign s y)).Nonempty ∧
      (disjPos2 φ ψ (State.randomAssign s y)).Nonempty := by
  obtain ⟨p, -, -, q, hq, -⟩ := h
  exact fc_preconditions φ ψ ⟨q, hq⟩


/-- The individuals of a scenario for (120): two students and a novel. -/
inductive Reader
  | ann
  | bea
  | novel
  deriving DecidableEq

/-- Ann read the novel, and nobody read anything else. -/
def reads : Reader → Reader → Unit → Prop
  | .ann, .novel, _ => True
  | _, _, _ => False

/-- The initial state of a one-world scenario. -/
def initR : BUSState Unit Reader := {Possibility.bot ()}

/-- Where Ann read the novel and Bea read nothing, (45) retains no point of `s[ε_y]` for the denial
of `∃x R(y, x)`, though (121) requires some student who read no novel; the subsistence-based
negative update retains Bea's point. -/
theorem existsNegative_misses_reader :
    existsNegative 1 (pred2 reads 0 1) (State.randomAssign initR 0) = ∅ ∧
      (Possibility.bot () : Possibility Unit ℕ (Flat Reader)).update 0 ↑Reader.bea ∈
        (exists_ 1 (pred2 reads 0 1)).negative (State.randomAssign initR 0) := by
  let b : Possibility Unit ℕ (Flat Reader) := Possibility.bot ()
  refine ⟨Set.eq_empty_of_forall_notMem fun p ⟨_, hno, _⟩ ↦ hno
    ⟨(b.update 0 ↑Reader.ann).update 1 ↑Reader.novel,
      ⟨⟨_, ⟨b, rfl, .ann, rfl⟩, .novel, rfl⟩, .ann, by simp, .novel, by simp, trivial⟩, rfl⟩,
    ⟨b, rfl, .bea, rfl⟩, ?_, ?_⟩
  · rintro ⟨q, ⟨-, e₁, he₁, e₂, -, hR⟩, hpq⟩
    have h0 := (Possibility.le_def.mp hpq).2 0
    rw [he₁] at h0
    obtain rfl : Reader.bea = e₁ := by simpa [b, Possibility.bot] using h0
    exact hR
  · exact ⟨(b.update 0 ↑Reader.bea).update 1 ↑Reader.ann,
      ⟨⟨_, ⟨b, rfl, .bea, rfl⟩, .ann, rfl⟩, .bea, by simp, .ann, by simp, id⟩,
      Possibility.le_update_of_eq_bot (by simp [Possibility.bot]) _⟩

theorem ex116 :
    (Possibility.bot () : Possibility Unit ℕ (Flat Reader)).update 0 ↑Reader.bea ∈
        (exists_ 1 (pred2 reads 0 1)).negative (State.randomAssign initR 0) ↔
      ("entails: some student didn't read a novel", Judgment.acceptable) ∈
        Examples.ex_116.readings :=
  iff_of_true existsNegative_misses_reader.2 (by simp [Examples.ex_116])

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

/-- Negative modal conjunction gives negative free choice with anaphora: if `¬(∃x A(x) ∧ B(x))` is
possible, so are `¬∃x A(x)` and `∃x (A(x) ∧ ¬B(x))`, (129). -/
theorem negative_fc_with_anaphora [Nonempty E] (A B : E → W → Prop) (hx : State.Novel s x)
    (h : Possible (~(conjModal (exists_ x (pred1 A x)) (pred1 B x))) s) :
    Possible (~(exists_ x (pred1 A x))) s ∧
      Possible (exists_ x (pred1 A x ⊙ ~(pred1 B x))) s := by
  obtain ⟨h₁, h₂⟩ := negative_modal_conjunction _ _ h
  have hn := hx.mono (negative_exists_subset x (pred1 A x) s)
  refine ⟨h₁.mono ?_, ?_⟩
  · rw [conjNeg1, positive_pred1_of_novel B hn, negative_pred1_of_novel B hn,
      unknownUpdate_pred1_of_novel B hn, Set.empty_union, Set.empty_union]
    exact subset_rfl
  · rwa [conjNeg2, negative_pred1_of_novel B hn, unknownUpdate_exists_pred1 A hx,
      show (pred1 B x).negative (∅ : BUSState W E) = ∅ from Set.sep_empty _, Set.empty_union,
      Set.union_empty] at h₂

end ElliottSudo2025
