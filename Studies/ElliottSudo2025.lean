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
prohibition](##ElliottSudo2025.dual_prohibition). The same requirement on the negative update of
conjunction is [modal disjunction under de Morgan's laws](##ElliottSudo2025.neg_conjModal), so it
[derives negative free choice](##ElliottSudo2025.negative_fc_with_anaphora) from free choice.

## Implementation notes

* The existential is the substrate's, whose negative update keeps the points that subsist in the
  negative update of the scope, as in Elliott's earlier presentation. The article's (45) compares
  worlds instead; [the two agree at initial states](##ElliottSudo2025.existsNegative_eq_of_initial),
  where the article computes its examples.
* The parts (92) of a disjunction's positive update are the substrate's `firstPart` and
  `secondPart` at `true`, and those of a conjunction's negative update, which the article leaves
  to the reader, the same at `false`. The derivations (93) and (94) are Elliott's (31) and (32), the
  updates (70) and (66) of the bathroom disjunction his (33) and (35), and the failure (62) of
  Egli's theorem in the negative dimension his (41b), all in `Elliott2023`.

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

open DynamicSemantics BilateralUpdate

variable {W V E : Type*} {s : Set (Possibility W V (Part E))} {x : V}

/-! ### The negative update of an existential (§3.2) -/

section ExistsNegative

variable [DecidableEq V]

/-- The negative update of `∃x φ` as (45) prints it: the points of `s` whose world the positive
update does not reach and the negative update of the scope after random assignment does. -/
def existsNegative (x : V) (φ : BilateralUpdate W V E) (s : Set (Possibility W V (Part E))) :
    Set (Possibility W V (Part E)) :=
  {p ∈ s | p.world ∉ Possibility.world '' φ.positive (State.randomAssign s x) ∧
    p.world ∈ Possibility.world '' φ.negative (State.randomAssign s x)}

omit [DecidableEq V] in
theorem mem_lowerClosure_iff_of_eq_bot {p : Possibility W V (Part E)}
    (hp : ∀ v, p.assignment v = ⊥) (t : Set (Possibility W V (Part E))) :
    p ∈ lowerClosure t ↔ p.world ∈ Possibility.world '' t :=
  ⟨fun ⟨q, hq, hpq⟩ ↦ ⟨q, hq, (Possibility.le_def.mp hpq).1.symm⟩,
    fun ⟨q, hq, hqw⟩ ↦ ⟨q, hq, Possibility.le_def.mpr ⟨hqw.symm, fun v ↦ hp v ▸ bot_le⟩⟩⟩

theorem existsNegative_eq_of_initial (hs : ∀ p ∈ s, ∀ v, p.assignment v = ⊥)
    (φ : BilateralUpdate W V E) : existsNegative x φ s = (exists_ x φ).negative s :=
  Set.ext fun p ↦ and_congr_right fun hp ↦
    and_congr (not_congr (mem_lowerClosure_iff_of_eq_bot (hs p hp) _).symm)
      (mem_lowerClosure_iff_of_eq_bot (hs p hp) _).symm

-- (55)
theorem exists_assertable [Nonempty E] (Q : E → W → Prop) (hx : State.Novel s x) :
    (exists_ x (pred1 Q x)).Assertable s :=
  unknownUpdate_exists_pred1 Q hx

end ExistsNegative

/-! ### Epistemic modals (§3.5) -/

/-- `◇φ` passes positively when the positive update is consistent, (73a). -/
def Possible (φ : BilateralUpdate W V E) (s : Set (Possibility W V (Part E))) : Prop :=
  (φ.positive s).Nonempty

/-- `◇φ` passes negatively when `¬φ` is already implicit in the state modulo anaphoric
information: the state subsists in the negative update, (73b). -/
def Settled (φ : BilateralUpdate W V E) (s : Set (Possibility W V (Part E))) : Prop :=
  lowerClosure s ≤ lowerClosure (φ.negative s)

/-- Epistemic possibility (73): both updates are tests, `◇φ` positively the test of `φ`'s
positive update for consistency. -/
def diamond (φ : BilateralUpdate W V E) : BilateralUpdate W V E where
  positive := CCP.might φ.positive
  negative := CCP.guard (Settled φ)

/-- Epistemic necessity (77), the dual `□φ = ¬◇¬φ`. -/
def box (φ : BilateralUpdate W V E) : BilateralUpdate W V E := ~(diamond (~φ))

@[inherit_doc diamond] prefix:max "◇ᵇ" => diamond
@[inherit_doc box] prefix:max "□ᵇ" => box

-- (77a)
theorem box_positive (φ : BilateralUpdate W V E) :
    (□ᵇφ).positive s = (◇ᵇ(~φ)).negative s := rfl

section Exists

variable [DecidableEq V]

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

end Exists

/-! ### Modal disjunction (§3.6–3.7) -/

open scoped Classical in
/-- Modal disjunction, anaphora-sensitive version (96): the positive update requires each disjunct
to be responsible for some point of the positive update of plain disjunction; the negative update
is that of plain disjunction. -/
noncomputable def disjModal (φ ψ : BilateralUpdate W V E) : BilateralUpdate W V E where
  positive s :=
    if (firstPart .true φ ψ s).Nonempty ∧ (secondPart .true φ ψ s).Nonempty then (φ ⊕ ψ).positive s
    else ∅
  negative := (φ ⊕ ψ).negative

@[inherit_doc] notation:60 φ " ∨ᶠᶜ " ψ => disjModal φ ψ

open scoped Classical in
/-- Negative modal conjunction (132): the negative update requires each conjunct to be responsible
for some point of the negative update of plain conjunction. -/
noncomputable def conjModal (φ ψ : BilateralUpdate W V E) : BilateralUpdate W V E where
  positive := (φ ⊙ ψ).positive
  negative s :=
    if (firstPart .false φ ψ s).Nonempty ∧ (secondPart .false φ ψ s).Nonempty then
      (φ ⊙ ψ).negative s
    else ∅

theorem fc_preconditions (φ ψ : BilateralUpdate W V E) (h : Possible (φ ∨ᶠᶜ ψ) s) :
    (firstPart .true φ ψ s).Nonempty ∧ (secondPart .true φ ψ s).Nonempty := by
  unfold Possible disjModal at h
  by_cases hc : (firstPart .true φ ψ s).Nonempty ∧ (secondPart .true φ ψ s).Nonempty
  · exact hc
  · simp only [hc, ↓reduceIte] at h
    exact (Set.not_nonempty_empty h).elim

-- fn. 32
theorem neg_conjModal (φ ψ : BilateralUpdate W V E) : ~(conjModal φ ψ) = disjModal (~φ) (~ψ) := by
  ext s : 2
  · simp only [positive_neg, conjModal, disjModal, ← neg_conj]
    congr 1
    simp only [firstPart_neg, secondPart_neg, Trivalent.compl_true]
  · simp [conjModal, disjModal, ← neg_conj]

section Atomic

variable (c t : W → Prop)

theorem firstPart_atom :
    firstPart .true (atom c) (atom t) s = (atom c (V := V) (E := E)).positive s := by
  ext p
  simp only [mem_firstPart, update_true]
  refine ⟨fun ⟨b, hp⟩ ↦ ?_, fun hp ↦ ?_⟩
  · cases b <;> simp_all [update, unknownUpdate_atom]
  · by_cases h : t p.world
    exacts [⟨.true, by simp [hp, h]⟩, ⟨.false, by simp [hp, h]⟩]

theorem secondPart_atom :
    secondPart .true (atom c) (atom t) s = (atom t (V := V) (E := E)).positive s := by
  ext p
  simp only [mem_secondPart, update_true, mem_positive_atom]
  refine ⟨fun ⟨a, hp, h⟩ ↦ ⟨?_, h⟩, fun ⟨hp, h⟩ ↦ ?_⟩
  · cases a <;> simp_all [update, unknownUpdate_atom]
  · by_cases hc : c p.world
    exacts [⟨.true, by simp [hp, hc], h⟩, ⟨.false, by simp [hp, hc], h⟩]

-- (84)
theorem possible_disjModal_atom_iff :
    Possible (atom c ∨ᶠᶜ atom t) s ↔ Possible (atom c) s ∧ Possible (atom t) s := by
  have key : (firstPart .true (atom c) (atom t) s).Nonempty ∧
      (secondPart .true (atom c) (atom t) s).Nonempty ↔
        ((atom c (V := V) (E := E)).positive s).Nonempty ∧
          ((atom t (V := V) (E := E)).positive s).Nonempty := by
    rw [firstPart_atom, secondPart_atom]
  simp only [Possible, disjModal]
  constructor
  · intro h
    by_contra hc
    rw [ite_eq_right (key.not.mpr hc)] at h
    exact Set.not_nonempty_empty h
  · rintro ⟨hc, ht⟩
    rw [ite_eq_left (key.mpr ⟨hc, ht⟩), positive_disj_eq_union, firstPart_atom]
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
  have h : (atom c ⊕ atom t).negative s = {p ∈ s | ¬ c p.world ∧ ¬ t p.world} := by
    ext p
    simp only [negative_disj, mem_negative_atom, Set.mem_sep_iff]
    tauto
  simp only [Settled, disjModal, h]
  exact lowerClosure_le_sep_iff (fun w ↦ ¬ c w ∧ ¬ t w)

/-- Modal disjunction leaves dual prohibition intact: if `◇(c ∨ t)` passes negatively, so do `◇c`
and `◇t`, (80). -/
theorem dual_prohibition (h : Settled (atom c ∨ᶠᶜ atom t) s) :
    Settled (atom c (V := V) (E := E)) s ∧ Settled (atom t (V := V) (E := E)) s := by
  rw [settled_disjModal_atom_iff] at h
  simp only [Settled, negative_atom]
  exact ⟨(lowerClosure_le_sep_iff (fun w ↦ ¬ c w)).mpr fun p hp ↦ (h p hp).1,
    (lowerClosure_le_sep_iff (fun w ↦ ¬ t w)).mpr fun p hp ↦ (h p hp).2⟩

end Atomic

/-! ### The bathroom disjunction and free choice with anaphora (§3.4.2, §3.7) -/

section Bathroom

variable [DecidableEq V] (P Q : E → W → Prop)

/-- Free choice with anaphora: if the bathroom disjunction with modal disjunction is possible,
so are `¬∃x P(x)` and `∃x (P(x) ∧ Q(x))`, (24). -/
theorem fc_with_anaphora [Nonempty E] (hx : State.Novel s x)
    (h : Possible ((~(exists_ x (pred1 P x))) ∨ᶠᶜ pred1 Q x) s) :
    Possible (~(exists_ x (pred1 P x))) s ∧ Possible (exists_ x (pred1 P x ⊙ pred1 Q x)) s := by
  obtain ⟨h₁, h₂⟩ := fc_preconditions _ _ h
  rw [Elliott2023.firstPart_donkey P Q hx] at h₁
  rw [Elliott2023.secondPart_donkey P Q hx] at h₂
  exact ⟨h₁, by rwa [Possible, ← egli, positive_conj]⟩

theorem ex22 [Nonempty E] (hx : State.Novel s x) :
    (Possible ((~(exists_ x (pred1 P x))) ∨ᶠᶜ pred1 Q x) s →
      Possible (~(exists_ x (pred1 P x))) s ∧ Possible (exists_ x (pred1 P x ⊙ pred1 Q x)) s) ↔
      Examples.ex_22.judgment = .acceptable :=
  iff_of_true (fc_with_anaphora P Q hx) rfl

omit [DecidableEq V] in
-- (25), (90c)
theorem classical_conclusion_impossible (hx : State.Novel s x) : ¬ Possible (pred1 Q x) s := by
  rw [Possible, positive_pred1_of_novel Q hx]
  exact Set.not_nonempty_empty

end Bathroom

/-! ### Double negation (§2.1, §3.3) -/

-- (49) [groenendijk-stokhof-1991]
theorem dne_bus_not_dpl [Nontrivial E] :
    (∀ φ : BilateralUpdate W V E, ~~φ = φ) ∧
      ∃ (x : ℕ) (φ : Update (ℕ → E)),
        Update.test (Update.neg (Update.test (Update.neg (Update.dexists x φ)))) ≠
          Update.dexists x φ :=
  ⟨BilateralUpdate.neg_neg, GroenendijkStokhof1991.dne_fails_anaphora⟩

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
def xTo (e : PEntity) : ℕ → Part PEntity := fun n ↦ if n = 0 then .some e else ⊥

/-- The initial assignment `[]`. -/
def blank : ℕ → Part PEntity := fun _ ↦ ⊥

open PWorld in
/-- The state of (56), where `x` is defined at the `P`-worlds only. -/
def s56 : Set (Possibility PWorld ℕ (Part PEntity)) :=
  {⟨wa, xTo .a⟩, ⟨wa, xTo .b⟩, ⟨wb, xTo .a⟩, ⟨wb, xTo .b⟩, ⟨w0, blank⟩}

-- (56a)
theorem mem_positive_s56 :
    (⟨.wa, xTo .a⟩ : Possibility PWorld ℕ (Part PEntity)) ∈ (pred1 pHolds 0).positive s56 :=
  mem_positive_pred1.2 ⟨by simp [s56], .a, by simp [xTo], trivial⟩

-- (56c)
theorem gap_mem_unknownUpdate_s56 :
    (⟨.w0, blank⟩ : Possibility PWorld ℕ (Part PEntity)) ∈ (pred1 pHolds 0).unknownUpdate s56 := by
  have key (q : Possibility PWorld ℕ (Part PEntity)) (hq : q ∈ s56) (hw : PWorld.w0 = q.world)
      (e : PEntity) (he : e ∈ q.assignment 0) : False := by
    rcases (by simpa [s56] using hq : q = _ ∨ q = _ ∨ q = _ ∨ q = _ ∨ q = _)
      with rfl | rfl | rfl | rfl | rfl <;>
      first
        | exact Part.notMem_none e he
        | simp_all
  refine ⟨by simp [s56], fun ⟨q, hq, hle⟩ ↦ ?_, fun ⟨q, hq, hle⟩ ↦ ?_⟩
  · obtain ⟨hq, e, he, -⟩ := mem_positive_pred1.1 hq
    exact key q hq (Possibility.le_def.mp hle).1 e he
  · obtain ⟨hq, e, he, -⟩ := mem_negative_pred1.1 hq
    exact key q hq (Possibility.le_def.mp hle).1 e he

-- (56)
theorem not_assertable_s56 : ¬ (pred1 pHolds 0).Assertable s56 := fun h ↦
  Set.notMem_empty _ (h ▸ gap_mem_unknownUpdate_s56)

theorem not_familiar_s56 : ¬ State.Familiar s56 0 := fun h ↦
  h ⟨.w0, blank⟩ (show ⟨PWorld.w0, blank⟩ ∈ s56 by simp [s56])

open PWorld in
/-- The state of (57): `x` is undefined at some possibility of each world but defined at another
with the same world. -/
def s57 : Set (Possibility PWorld ℕ (Part PEntity)) :=
  {⟨wa, xTo .a⟩, ⟨wa, blank⟩, ⟨wb, xTo .b⟩, ⟨wb, blank⟩}

-- (57)
theorem assertable_s57_not_familiar :
    (pred1 pHolds 0).Assertable s57 ∧ ¬ State.Familiar s57 0 := by
  refine ⟨?_, fun h ↦ h ⟨.wa, blank⟩ (show ⟨PWorld.wa, blank⟩ ∈ s57 by simp [s57])⟩
  apply Set.eq_empty_of_forall_notMem
  rintro p ⟨hp, hpos, -⟩
  apply hpos
  have ha : (⟨.wa, xTo .a⟩ : Possibility PWorld ℕ (Part PEntity)) ∈ (pred1 pHolds 0).positive s57 :=
    mem_positive_pred1.2 ⟨by simp [s57], .a, by simp [xTo], trivial⟩
  have hb : (⟨.wb, xTo .b⟩ : Possibility PWorld ℕ (Part PEntity)) ∈ (pred1 pHolds 0).positive s57 :=
    mem_positive_pred1.2 ⟨by simp [s57], .b, by simp [xTo], trivial⟩
  have hle : ∀ w e, (⟨w, blank⟩ : Possibility PWorld ℕ (Part PEntity)) ≤ ⟨w, xTo e⟩ :=
    fun w e ↦ Possibility.le_def.mpr ⟨rfl, fun _ ↦ bot_le⟩
  rcases (by simpa [s57] using hp : p = _ ∨ p = _ ∨ p = _ ∨ p = _) with rfl | rfl | rfl | rfl
  · exact subset_lowerClosure ha
  · exact ⟨_, ha, hle _ _⟩
  · exact subset_lowerClosure hb
  · exact ⟨_, hb, hle _ _⟩

/-- The state where `x` is `a` at one point of `wa` and `b` at another. -/
def sab : Set (Possibility PWorld ℕ (Part PEntity)) := {⟨.wa, xTo .a⟩, ⟨.wa, xTo .b⟩}

/-- State subsistence (Def. 3.4) with descent as Def. 3.3 prints it: every point of `s` has a point
of `s'` at its world whose domain includes its own. -/
def DomSubsists (s s' : Set (Possibility W V (Part E))) : Prop :=
  ∀ p ∈ s, ∃ q ∈ s', p.world = q.world ∧ p.domain ⊆ q.domain

/-- With descent as printed, `◇P(x)` passes both positively and negatively at `sab`: the state
subsists in the negative update of `P(x)` by Def. 3.4, though not by extension. -/
theorem possible_and_domSubsists_negative :
    Possible (pred1 pHolds 0) sab ∧ DomSubsists sab ((pred1 pHolds 0).negative sab) ∧
      ¬ Settled (pred1 pHolds 0) sab := by
  have hb : (⟨.wa, xTo .b⟩ : Possibility PWorld ℕ (Part PEntity)) ∈
      (pred1 pHolds 0).negative sab :=
    mem_negative_pred1.2 ⟨by simp [sab], .b, by simp [xTo], id⟩
  refine ⟨⟨⟨.wa, xTo .a⟩, mem_positive_pred1.2 ⟨by simp [sab], .a, by simp [xTo], trivial⟩⟩, ?_,
    fun h ↦ ?_⟩
  · rintro p (rfl | rfl) <;> refine ⟨_, hb, rfl, fun v hv ↦ ?_⟩ <;>
      by_cases h : v = 0 <;> simp_all [xTo, Possibility.mem_domain, Part.bot_eq_none]
  · obtain ⟨q, hq', hpq⟩ := h (subset_lowerClosure
      (show (⟨.wa, xTo .a⟩ : Possibility PWorld ℕ (Part PEntity)) ∈ sab from Or.inl rfl))
    obtain ⟨hq, e, he, hP⟩ := mem_negative_pred1.1 hq'
    have ha : PEntity.a ∈ q.assignment 0 := (Possibility.le_def.mp hpq).2 0 _ (by simp [xTo])
    obtain rfl : e = PEntity.a := Part.mem_unique he ha
    rcases hq with rfl | rfl
    · exact hP trivial
    · simp [xTo] at he

end PartialFamiliarity

/-! ### Distributive inferences with anaphora (§5.2) -/

-- (121)
theorem distributive_preconditions [DecidableEq V] (φ ψ : BilateralUpdate W V E) (y : V)
    (h : Possible (forall_ y (φ ∨ᶠᶜ ψ)) s) :
    (firstPart .true φ ψ (State.randomAssign s y)).Nonempty ∧
      (secondPart .true φ ψ (State.randomAssign s y)).Nonempty := by
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
def initR : Set (Possibility Unit ℕ (Part Reader)) := {Possibility.bot ()}

/-- Where Ann read the novel and Bea read nothing, (45) retains no point of `s[ε_y]` for the denial
of `∃x R(y, x)`, though (121) requires some student who read no novel; the subsistence-based
negative update retains Bea's point. -/
theorem existsNegative_misses_reader :
    existsNegative 1 (pred2 reads 0 1) (State.randomAssign initR 0) = ∅ ∧
      (Possibility.bot () : Possibility Unit ℕ (Part Reader)).update 0 (.some Reader.bea) ∈
        (exists_ 1 (pred2 reads 0 1)).negative (State.randomAssign initR 0) := by
  let b : Possibility Unit ℕ (Part Reader) := Possibility.bot ()
  refine ⟨Set.eq_empty_of_forall_notMem fun p ⟨_, hno, _⟩ ↦ hno
    ⟨(b.update 0 (.some Reader.ann)).update 1 (.some Reader.novel), mem_positive_pred2.2
      ⟨⟨_, ⟨b, rfl, .ann, rfl⟩, .novel, rfl⟩, .ann, by simp, .novel, by simp, trivial⟩, rfl⟩,
    ⟨b, rfl, .bea, rfl⟩, ?_, ?_⟩
  · rintro ⟨q, hq, hpq⟩
    obtain ⟨-, e₁, he₁, e₂, -, hR⟩ := mem_positive_pred2.1 hq
    have hb : Reader.bea ∈ q.assignment 0 := (Possibility.le_def.mp hpq).2 0 _ (by simp)
    obtain rfl : e₁ = Reader.bea := Part.mem_unique he₁ hb
    exact hR
  · exact ⟨(b.update 0 (.some Reader.bea)).update 1 (.some Reader.ann), mem_negative_pred2.2
      ⟨⟨_, ⟨b, rfl, .bea, rfl⟩, .ann, rfl⟩, .bea, by simp, .ann, by simp, id⟩,
      Possibility.le_update_of_notMem (by simp [Possibility.domain_update_some]) _⟩

theorem ex116 :
    (Possibility.bot () : Possibility Unit ℕ (Part Reader)).update 0 (.some Reader.bea) ∈
        (exists_ 1 (pred2 reads 0 1)).negative (State.randomAssign initR 0) ↔
      ("entails: some student didn't read a novel", Judgment.acceptable) ∈
        Examples.ex_116.readings :=
  iff_of_true existsNegative_misses_reader.2 (by simp [Examples.ex_116])

/-! ### Negative free choice (§5.4) -/

-- (130)
theorem negative_modal_conjunction (φ ψ : BilateralUpdate W V E)
    (h : Possible (~(conjModal φ ψ)) s) :
    (firstPart .false φ ψ s).Nonempty ∧ (secondPart .false φ ψ s).Nonempty := by
  rw [neg_conjModal] at h
  simpa only [firstPart_neg, secondPart_neg, Trivalent.compl_true] using fc_preconditions _ _ h

-- (131)
theorem dual_permission (φ ψ : BilateralUpdate W V E) (hφ : CCP.IsEliminative φ.positive)
    (hm : Monotone ψ.positive) (he : CCP.IsEliminative ψ.positive) (h : Possible (φ ⊙ ψ) s) :
    Possible φ s ∧ Possible ψ s := by
  obtain ⟨p, hp⟩ := h
  rw [positive_conj] at hp
  exact ⟨⟨p, he _ hp⟩, ⟨p, hm (hφ s) hp⟩⟩

/-- Negative modal conjunction gives negative free choice with anaphora: if `¬(∃x A(x) ∧ B(x))` is
possible, so are `¬∃x A(x)` and `∃x (A(x) ∧ ¬B(x))`, (129). -/
theorem negative_fc_with_anaphora [DecidableEq V] [Nonempty E] (A B : E → W → Prop)
    (hx : State.Novel s x) (h : Possible (~(conjModal (exists_ x (pred1 A x)) (pred1 B x))) s) :
    Possible (~(exists_ x (pred1 A x))) s ∧
      Possible (exists_ x (pred1 A x ⊙ ~(pred1 B x))) s := by
  rw [neg_conjModal, neg_pred1] at h
  rw [neg_pred1]
  exact fc_with_anaphora A (fun e w ↦ ¬ B e w) hx h

end ElliottSudo2025
