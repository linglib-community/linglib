module

public import Linglib.Logic.Team.QBSML.FreeChoice
public import Mathlib.Tactic.DeriveFintype

/-!
# Yan (2023): Monotonicity in Intensional Contexts

This file formalizes Chapter 4 of [yan-2023], which defends an upward-monotonic semantics for
desire verbs against three puzzles: Asher's puzzle and the teach-on-Tuesdays example reported
in [heim-1992], and Ross's paradox under *want* from [crnic-2011] after [ross-1944]. *Want*
is the necessity modal over a bouletic accessibility relation and *it is ok* its dual, §4.4.1,
in the quantified bilateral state-based modal logic of [aloni-vanormondt-2023]. Each puzzle
reduces to a free-choice inference: the monotonic step is valid on the NE-free fragment
(`nec_disj_intro`, `nec_exi_within_mono`); the inference that the agent is ok with the
unwanted alternative follows by □-free choice, Fact 13, from the pragmatically enriched
disjunctive conclusion (`ross_fc`, `fc_of_reinterpret`); and at a desire state that supports
the enriched premise the enriched conclusion is unsupported (`ross_blocked`, `asher_blocked`,
`heim_blocked`), so the three puzzles are pragmatic failures, Table 4.3. Where no disjunction
is overt, the reinterpretation function of Definition 32 supplies one: a predicate with a
contextually salient sub-predicate is read as the disjunction of the predicate within the
sub-predicate and outside it (`reinterpret`), which stays NE-free and is bilaterally
equivalent to the original (`reinterpret_neFree`, `eval_reinterpret_iff`) yet parts from it
under enrichment (`asher_concl_enriched`, `asher_blocked`).

## Implementation notes

* The language of Definition 24 has primitive □, derived ◇ and no ∀. The substrate `Formula`
  has primitive ◇ and ∀ with □ derived, so the enrichment of `□φ` is the negation-clause
  enrichment of `¬◇¬φ`, under which Fact 13 holds as `boxFC`; `reinterpret` extends
  Definition 32 to ∀ and, as a totality filler, to NE.
* The side condition of Definition 32, that the denotation of the sub-predicate is a proper
  subset of the predicate's, is checked against the global model (`IsSubPred`): within the
  agent's desire worlds it must fail, since blocking requires every trip there to be free. The
  relation `sub` that triggers reinterpretation is therefore a contextual parameter, and
  `eval_reinterpret_iff` holds for any choice of it.
* The premise of Asher's puzzle is `□∃x(FREE x ∧ TRIP x)`, the paper's `□∃x FREE x`
  unabbreviated after its footnote reading the generalisation as conjunction elimination; the
  conclusion `◇∃x ¬FREE x` of (27d) is `◇∃x(¬FREE x ∧ TRIP x)`.
* Asher's and Heim's puzzles share one two-world model, `desireModel`: every predicate holds
  at the desire world and only the wanted predicate at the other. The ◇-free-choice route
  through the conditional rephrasing (17)–(18) and the deontic applications of §4.5 are not
  formalized.

## References

* [yan-2023]
* [aloni-vanormondt-2023]
* [aloni-2022]
* [heim-1992]
* [crnic-2011]
* [ross-1944]
* [von-fintel-1999]
-/

@[expose] public section

namespace Yan2023

open FirstOrder QBSML

variable {W Domain Const Pred : Type*}

section

variable {Var : Type*}

/-! ### The reinterpretation function, Definition 32 -/

/-- `within P Q x`, `Q` within `P`, is `P x ∧ Q x`, the paper's `P_Q x`. -/
def within (P Q : Pred) (x : Var) : Formula Var Const Pred := .conj (.pred P x) (.pred Q x)

/-- `without P Q x`, `Q` outside `P`, is `¬P x ∧ Q x`, the paper's `¬P_Q x`. -/
def without (P Q : Pred) (x : Var) : Formula Var Const Pred :=
  .conj (.neg (.pred P x)) (.pred Q x)

theorem within_neFree (P Q : Pred) (x : Var) : (within P Q x : Formula Var Const Pred).NEFree :=
  .conj (.pred _ _) (.pred _ _)

theorem without_neFree (P Q : Pred) (x : Var) :
    (without P Q x : Formula Var Const Pred).NEFree :=
  .conj (.neg (.pred _ _)) (.pred _ _)

/-- Reinterpretation by `P` replaces each atom whose predicate `Q` has `P` as a contextually
salient sub-predicate, `sub P Q`, by the disjunction of `Q` within `P` and `Q` outside `P`, and
commutes with every connective. -/
def reinterpret (sub : Pred → Pred → Prop) [DecidableRel sub] (P : Pred) :
    Formula Var Const Pred → Formula Var Const Pred :=
  Formula.mapAtoms
    (λ Q x => if sub P Q then .disj (within P Q x) (without P Q x) else .pred Q x)
    (λ Q c => if sub P Q then
        .disj (.conj (.predc P c) (.predc Q c)) (.conj (.neg (.predc P c)) (.predc Q c))
      else .predc Q c)

section Reinterpret

variable (sub : Pred → Pred → Prop) [DecidableRel sub] (P : Pred)

theorem reinterpret_neFree {φ : Formula Var Const Pred} (h : φ.NEFree) :
    (reinterpret sub P φ).NEFree :=
  h.mapAtoms
    (λ Q x => by
      show Formula.NEFree (if sub P Q then _ else _)
      split
      · exact .disj (within_neFree _ _ _) (without_neFree _ _ _)
      · exact .pred _ _)
    (λ Q c => by
      show Formula.NEFree (if sub P Q then _ else _)
      split
      · exact .disj (.conj (.predc _ _) (.predc _ _)) (.conj (.neg (.predc _ _)) (.predc _ _))
      · exact .predc _ _)

theorem reinterpret_nec_exi {Q : Pred} (h : sub P Q) (x : Var) :
    reinterpret sub P (Formula.nec (.exi x (.pred Q x)) : Formula Var Const Pred) =
      Formula.nec (.exi x (.disj (within P Q x) (without P Q x))) := by
  simp [reinterpret, Formula.mapAtoms, Formula.nec, h]

end Reinterpret

/-! ### Substitution salva veritate, §4.3.2

The classical equivalence of `Q x` and `(P x ∧ Q x) ∨ (¬P x ∧ Q x)` that licenses
reinterpretation holds bilaterally in team semantics for unenriched formulas. -/

section SalvaVeritate

variable [DecidableEq W] [DecidableEq Var] [Fintype Var] [DecidableEq Domain] [Fintype Domain]
variable (M : Model W Domain Const Pred)

private theorem eval_within_disj_without (P Q : Pred) (x : Var) (b : Bool)
    (s : Finset (Index W Var Domain)) :
    eval M b (Formula.disj (within P Q x) (without P Q x)) s ↔ eval M b (Formula.pred Q x) s := by
  classical
  cases b with
  | true =>
    constructor
    · rintro ⟨t₁, ⟨-, hQ₁⟩, t₂, ⟨-, hQ₂⟩, hsplit⟩ i hi
      rw [← hsplit] at hi
      exact (Finset.mem_union.mp hi).elim (hQ₁ i) (hQ₂ i)
    · intro hQ
      refine ⟨s.filter (λ i => ∀ d : Domain, i.assign x = ↑d → M.relInterp₁ (predSymb P) i.world d),
        ⟨?_, ?_⟩,
        s.filter (λ i => ¬ ∀ d : Domain, i.assign x = ↑d → M.relInterp₁ (predSymb P) i.world d),
        ⟨?_, ?_⟩, Finset.filter_union_filter_not_eq _ s⟩
      · intro i hi
        obtain ⟨his, hcond⟩ := Finset.mem_filter.mp hi
        obtain ⟨d, hd, -⟩ := hQ i his
        exact ⟨d, hd, hcond d hd⟩
      · exact λ i hi => hQ i (Finset.mem_of_mem_filter i hi)
      · intro i hi
        obtain ⟨-, hncond⟩ := Finset.mem_filter.mp hi
        push Not at hncond
        exact hncond
      · exact λ i hi => hQ i (Finset.mem_of_mem_filter i hi)
  | false =>
    constructor
    · rintro ⟨⟨t₁, hnP, t₂, hnQ₁, hsplit₁⟩, ⟨u₁, hP, u₂, hnQ₂, hsplit₂⟩⟩ i hi
      rcases Finset.mem_union.mp (hsplit₁ ▸ hi) with hit₁ | hit₂
      · rcases Finset.mem_union.mp (hsplit₂ ▸ hi) with hiu₁ | hiu₂
        · obtain ⟨d, hd, hnp⟩ := hnP i hit₁
          obtain ⟨d', hd', hp⟩ := hP i hiu₁
          rw [hd, Flat.coe_inj] at hd'
          exact absurd (hd' ▸ hp) hnp
        · exact hnQ₂ i hiu₂
      · exact hnQ₁ i hit₂
    · intro h
      exact ⟨⟨∅, support_empty_of_neFree (.neg (.pred P x)) M, s, h, bot_sup_eq s⟩,
        ⟨∅, support_empty_of_neFree (.pred P x) M, s, h, bot_sup_eq s⟩⟩

private theorem eval_predc_disj (P Q : Pred) (c : Const) (b : Bool)
    (s : Finset (Index W Var Domain)) :
    eval M b (Formula.disj (.conj (.predc P c) (.predc Q c))
        (.conj (.neg (.predc P c)) (.predc Q c))) s ↔
      eval M b (Formula.predc Q c) s := by
  classical
  cases b with
  | true =>
    constructor
    · rintro ⟨t₁, ⟨-, hQ₁⟩, t₂, ⟨-, hQ₂⟩, hsplit⟩ i hi
      rw [← hsplit] at hi
      exact (Finset.mem_union.mp hi).elim (hQ₁ i) (hQ₂ i)
    · intro hQ
      refine ⟨s.filter (λ i => M.relInterp₁ (predSymb P) i.world
          (M.constInterp ((Language.monadic Pred).con c) i.world)), ⟨?_, ?_⟩,
        s.filter (λ i => ¬ M.relInterp₁ (predSymb P) i.world
          (M.constInterp ((Language.monadic Pred).con c) i.world)), ⟨?_, ?_⟩,
        Finset.filter_union_filter_not_eq _ s⟩
      · exact λ i hi => (Finset.mem_filter.mp hi).2
      · exact λ i hi => hQ i (Finset.mem_of_mem_filter i hi)
      · exact λ i hi => (Finset.mem_filter.mp hi).2
      · exact λ i hi => hQ i (Finset.mem_of_mem_filter i hi)
  | false =>
    constructor
    · rintro ⟨⟨t₁, hnP, t₂, hnQ₁, hsplit₁⟩, ⟨u₁, hP, u₂, hnQ₂, hsplit₂⟩⟩ i hi
      rcases Finset.mem_union.mp (hsplit₁ ▸ hi) with hit₁ | hit₂
      · rcases Finset.mem_union.mp (hsplit₂ ▸ hi) with hiu₁ | hiu₂
        · exact absurd (hP i hiu₁) (hnP i hit₁)
        · exact hnQ₂ i hiu₂
      · exact hnQ₁ i hit₂
    · intro h
      exact ⟨⟨∅, support_empty_of_neFree (.neg (.predc P c)) M, s, h, bot_sup_eq s⟩,
        ⟨∅, support_empty_of_neFree (.predc P c) M, s, h, bot_sup_eq s⟩⟩

variable (sub : Pred → Pred → Prop) [DecidableRel sub] (P : Pred) (φ : Formula Var Const Pred)
  (s : Finset (Index W Var Domain))

theorem eval_reinterpret_iff (b : Bool) : eval M b (reinterpret sub P φ) s ↔ eval M b φ s :=
  eval_mapAtoms_iff M
    (λ Q x b s => by
      show eval M b (if sub P Q then _ else _) s ↔ _
      split
      · exact eval_within_disj_without M P Q x b s
      · exact Iff.rfl)
    (λ Q c b s => by
      show eval M b (if sub P Q then _ else _) s ↔ _
      split
      · exact eval_predc_disj M P Q c b s
      · exact Iff.rfl)
    φ b s

theorem support_reinterpret_iff : support M (reinterpret sub P φ) s ↔ support M φ s :=
  eval_reinterpret_iff M sub P φ s true

theorem antiSupport_reinterpret_iff :
    antiSupport M (reinterpret sub P φ) s ↔ antiSupport M φ s :=
  eval_reinterpret_iff M sub P φ s false

end SalvaVeritate

/-! ### Monotonicity, free choice and blocking, §4.4.3

The pattern of Figures 4.2 and 4.3 on an arbitrary model: the monotonic step is valid, the
enriched conclusion yields the unwanted possibility by □-free choice, and a desire state whose
accessible worlds contain no instance of the unwanted disjunct supports the enriched premise
but not the enriched conclusion. -/

section Pattern

variable [DecidableEq W] [DecidableEq Var] [Fintype Var] [DecidableEq Domain] [Fintype Domain]
variable (M : Model W Domain Const Pred) {s : Finset (Index W Var Domain)}

/-- Disjunction introduction under *want*, the mode of Ross's paradox in Table 4.1, is valid
for an NE-free added disjunct. -/
theorem nec_disj_intro {α β : Formula Var Const Pred} (hβ : β.NEFree)
    (h : support M α.nec s) : support M (Formula.disj α β).nec s :=
  support_nec_mono M (λ _ => support_disj_inl M hβ) h

/-- Conjunction elimination under *want* and ∃, the mode of Asher's and Heim's puzzles in
Table 4.1, is valid. -/
theorem nec_exi_within_mono {P Q : Pred} {x : Var}
    (h : support M (Formula.nec (.exi x (within P Q x))) s) :
    support M (Formula.nec (.exi x (.pred Q x))) s :=
  support_nec_mono M (λ _ h' => by obtain ⟨hf, hne, hs⟩ := h'; exact ⟨hf, hne, hs.2⟩) h

/-- By free choice from the enriched reinterpreted want, (14) and (27), the agent is ok with
`Q` within `P` and with `Q` outside `P`. -/
theorem fc_of_reinterpret {sub : Pred → Pred → Prop} [DecidableRel sub] {P Q : Pred} {x : Var}
    (hsub : sub P Q)
    (h : support M (Formula.enrich (reinterpret sub P (Formula.nec (.exi x (.pred Q x))))) s) :
    support M (.poss (.exi x (within P Q x))) s ∧
      support M (.poss (.exi x (without P Q x))) s := by
  rw [reinterpret_nec_exi sub P hsub] at h
  exact boxExiFC M (within_neFree _ _ _) (without_neFree _ _ _) h

theorem support_enrich_nec_predc {A : Pred} {c : Const} (hs : s.Nonempty)
    (hacc : ∀ i ∈ s, (M.access i.world).Nonempty)
    (hA : ∀ i ∈ s, ∀ w ∈ M.access i.world,
      M.relInterp₁ (predSymb A) w (M.constInterp ((Language.monadic Pred).con c) w)) :
    support M (Formula.enrich (Formula.nec (.predc A c))) s := by
  rw [support_enrich_nec_iff]
  refine ⟨λ i hi => ⟨λ j hj => hA i hi j.world (State.mem_modalLift.mp hj).1, ?_⟩, hs⟩
  obtain ⟨w, hw⟩ := hacc i hi
  exact ⟨(w, i.assign), State.mem_modalLift.mpr ⟨hw, rfl⟩⟩

theorem not_support_enrich_nec_disj {A B : Pred} {c : Const} (hs : s.Nonempty)
    (hB : ∀ i ∈ s, ∀ w ∈ M.access i.world,
      ¬ M.relInterp₁ (predSymb B) w (M.constInterp ((Language.monadic Pred).con c) w)) :
    ¬ support M (Formula.enrich (Formula.nec (.disj (.predc A c) (.predc B c)))) s := by
  intro h
  obtain ⟨i, hi⟩ := hs
  obtain ⟨X, hX, ⟨w, hw⟩, hsupp⟩ := (boxFC M (.predc _ _) (.predc _ _) h).2 i hi
  exact hB i hi w (hX hw) (hsupp (w, i.assign) (State.mem_modalLift.mpr ⟨hw, rfl⟩))

theorem support_enrich_nec_exi_within {P Q : Pred} {x : Var} (hs : s.Nonempty)
    (hacc : ∀ i ∈ s, (M.access i.world).Nonempty)
    (hPQ : ∀ i ∈ s, ∀ w ∈ M.access i.world,
      ∃ d, M.relInterp₁ (predSymb P) w d ∧ M.relInterp₁ (predSymb Q) w d) :
    support M (Formula.enrich (Formula.nec (.exi x (within P Q x)))) s := by
  classical
  rw [support_enrich_nec_iff]
  refine ⟨λ i hi => ?_, hs⟩
  obtain ⟨w₀, hw₀⟩ := hacc i hi
  have hL : (State.modalLift (M.access i.world) i.assign).Nonempty :=
    ⟨(w₀, i.assign), State.mem_modalLift.mpr ⟨hw₀, rfl⟩⟩
  set hf : Index W Var Domain → Finset Domain :=
    λ j => Finset.univ.filter
      (λ d => M.relInterp₁ (predSymb P) j.world d ∧ M.relInterp₁ (predSymb Q) j.world d)
  have hfne : ∀ j ∈ State.modalLift (M.access i.world) i.assign, (hf j).Nonempty := by
    intro j hj
    obtain ⟨d, hd⟩ := hPQ i hi j.world (State.mem_modalLift.mp hj).1
    exact ⟨d, by simp [hf, hd]⟩
  have hext : (State.extendFunctional (State.modalLift (M.access i.world) i.assign) x
      hf).Nonempty := by
    obtain ⟨j, hj⟩ := hL
    obtain ⟨d, hd⟩ := hfne j hj
    exact ⟨j.update x d, State.mem_extendFunctional.mpr ⟨j, hj, d, hd, rfl⟩⟩
  refine ⟨⟨hf, hfne, ⟨⟨λ j' hj' => ?_, hext⟩, ⟨λ j' hj' => ?_, hext⟩⟩, hext⟩, hL⟩
  · obtain ⟨j, -, d, hd, rfl⟩ := State.mem_extendFunctional.mp hj'
    exact ⟨d, by simp, ((Finset.mem_filter.mp hd).2).1⟩
  · obtain ⟨j, -, d, hd, rfl⟩ := State.mem_extendFunctional.mp hj'
    exact ⟨d, by simp, ((Finset.mem_filter.mp hd).2).2⟩

theorem support_enrich_nec_exi_pred_of_within {P Q : Pred} {x : Var}
    (h : support M (Formula.enrich (Formula.nec (.exi x (within P Q x)))) s) :
    support M (Formula.enrich (Formula.nec (.exi x (.pred Q x)))) s := by
  rw [support_enrich_nec_iff] at h ⊢
  refine ⟨λ i hi => ?_, h.2⟩
  obtain ⟨⟨hf, hfne, ⟨⟨-, hQ⟩, -⟩⟩, hL⟩ := h.1 i hi
  exact ⟨⟨hf, hfne, hQ⟩, hL⟩

theorem not_support_enrich_reinterpret {sub : Pred → Pred → Prop} [DecidableRel sub]
    {P Q : Pred} {x : Var} (hsub : sub P Q) (hs : s.Nonempty)
    (hPQ : ∀ i ∈ s, ∀ w ∈ M.access i.world,
      ∀ d, M.relInterp₁ (predSymb Q) w d → M.relInterp₁ (predSymb P) w d) :
    ¬ support M (Formula.enrich (reinterpret sub P (Formula.nec (.exi x (.pred Q x))))) s := by
  intro h
  obtain ⟨i, hi⟩ := hs
  obtain ⟨X, hX, ⟨w, hw⟩, hf, hfne, hs'⟩ := (fc_of_reinterpret M hsub h).2 i hi
  have hj : ((w, i.assign) : Index W Var Domain) ∈ State.modalLift X i.assign :=
    State.mem_modalLift.mpr ⟨hw, rfl⟩
  obtain ⟨d, hd⟩ := hfne _ hj
  have hjd : Index.update (w, i.assign) x d ∈
      State.extendFunctional (State.modalLift X i.assign) x hf :=
    State.mem_extendFunctional.mpr ⟨_, hj, d, hd, rfl⟩
  obtain ⟨d₁, hd₁, hnP⟩ := hs'.1 _ hjd
  obtain ⟨d₂, hd₂, hQ⟩ := hs'.2 _ hjd
  simp at hd₁ hd₂
  subst hd₁ hd₂
  exact hnP (hPQ i hi w (hX hw) d hQ)

end Pattern

end

inductive Var
  | x
  deriving DecidableEq, Fintype

/-! ### Ross's paradox under desire, (3), (26), Figure 4.2 -/

/-- The predicates of Ross's paradox are sending and burning the letter. -/
inductive RossPred
  | send | burn
  deriving DecidableEq, Repr

/-- `sendL` is `SEND a`, the constant `a` being the letter. -/
def sendL : Formula Var Unit RossPred := .predc .send ()

/-- `burnL` is `BURN a`. -/
def burnL : Formula Var Unit RossPred := .predc .burn ()

/-- John's desire model has one desire world, reflexively accessible, where the letter is sent
and not burnt. -/
def rossModel : Model Unit Unit Unit RossPred :=
  .ofMonadic (λ _ => {()}) (λ _ _ => ()) (λ _ P _ => P = RossPred.send)

/-- John's desire state is the desire world with the empty assignment. -/
def rossState : Finset (Index Unit Var Unit) := {((), ⊥)}

/-- The monotonic step (26a) to (26b) is semantically valid. -/
theorem ross_monotone {s : Finset (Index Unit Var Unit)} (h : support rossModel sendL.nec s) :
    support rossModel (sendL.disj burnL).nec s :=
  nec_disj_intro rossModel (.predc _ _) h

/-- From the enriched disjunctive want, it is ok to send, (26c), and ok to burn, (26d). -/
theorem ross_fc {s : Finset (Index Unit Var Unit)}
    (h : support rossModel (Formula.enrich (sendL.disj burnL).nec) s) :
    support rossModel (.poss sendL) s ∧ support rossModel (.poss burnL) s :=
  boxFC rossModel (.predc _ _) (.predc _ _) h

theorem ross_premise : support rossModel (Formula.enrich sendL.nec) rossState :=
  support_enrich_nec_predc rossModel (Finset.singleton_nonempty _)
    (λ _ _ => Finset.singleton_nonempty _) (λ _ _ _ _ => rfl)

theorem ross_blocked : ¬ support rossModel (Formula.enrich (sendL.disj burnL).nec) rossState :=
  not_support_enrich_nec_disj rossModel (Finset.singleton_nonempty _)
    (λ _ _ _ _ h => RossPred.noConfusion h)

/-! ### A desire model for a salient sub-predicate

Nicholas wants a free trip, (1); I want to teach on Tuesdays, (2). At the desire world every
predicate holds of the one individual; at the other world only the wanted predicate, so the
sub-predicate's denotation is a proper subset globally. -/

/-- `P` is a sub-predicate of `Q` in `M` when its denotation is a proper subset of `Q`'s. -/
def IsSubPred (M : Model W Domain Const Pred) (P Q : Pred) : Prop :=
  (∀ w d, M.relInterp₁ (predSymb P) w d → M.relInterp₁ (predSymb Q) w d) ∧
    ∃ w d, M.relInterp₁ (predSymb Q) w d ∧ ¬ M.relInterp₁ (predSymb P) w d

/-- In the two-world desire model for the wanted predicate `Q`, only the desire world `true` is
accessible; every predicate holds there and only `Q` at `false`. -/
def desireModel (Q : Pred) : Model Bool Unit Unit Pred :=
  .ofMonadic (λ _ => {true}) (λ _ _ => ()) (λ w P _ => P = Q ∨ w = true)

/-- The desire state is the desire world with the empty assignment. -/
def desireState : Finset (Index Bool Var Unit) := {(true, ⊥)}

theorem isSubPred_desireModel {P Q : Pred} (h : P ≠ Q) : IsSubPred (desireModel Q) P Q :=
  ⟨λ _ _ _ => Or.inl rfl, false, (), Or.inl rfl, λ h' => h'.elim h Bool.false_ne_true⟩

theorem desireModel_premise (P Q : Pred) :
    support (desireModel Q) (Formula.enrich (Formula.nec (.exi Var.x (within P Q .x))))
      desireState :=
  support_enrich_nec_exi_within _ (Finset.singleton_nonempty _)
    (λ _ _ => Finset.singleton_nonempty _)
    (λ _ _ _ hw => ⟨(), Or.inr (Finset.mem_singleton.mp hw), Or.inr (Finset.mem_singleton.mp hw)⟩)

theorem desireModel_concl_enriched (P Q : Pred) :
    support (desireModel Q) (Formula.enrich (Formula.nec (.exi Var.x (.pred Q .x))))
      desireState :=
  support_enrich_nec_exi_pred_of_within _ (desireModel_premise P Q)

theorem desireModel_blocked {sub : Pred → Pred → Prop} [DecidableRel sub] {P Q : Pred}
    (hsub : sub P Q) :
    ¬ support (desireModel Q)
      (Formula.enrich (reinterpret sub P (Formula.nec (.exi Var.x (.pred Q .x))))) desireState :=
  not_support_enrich_reinterpret _ hsub (Finset.singleton_nonempty _)
    (λ _ _ _ hw _ _ => Or.inr (Finset.mem_singleton.mp hw))

/-! ### Asher's puzzle, (1), (27), Figure 4.3 -/

/-- The predicates of Asher's puzzle are being free and being a trip on the Concorde. -/
inductive AsherPred
  | free | trip
  deriving DecidableEq, Repr

/-- FREE is the contextually salient sub-predicate of TRIP. -/
def subFree (P Q : AsherPred) : Prop := P = .free ∧ Q = .trip

instance : DecidableRel subFree := λ _ _ => inferInstanceAs (Decidable (_ ∧ _))

/-- Nicholas wants a free trip, `□∃x(FREE x ∧ TRIP x)`, (27a). -/
abbrev asherPremise : Formula Var Unit AsherPred := (Formula.exi .x (within .free .trip .x)).nec

/-- Nicholas wants a trip, `□∃x TRIP x`, (27b). -/
abbrev asherConcl : Formula Var Unit AsherPred := (Formula.exi .x (.pred .trip .x)).nec

/-- The side condition of Definition 32 holds globally. -/
theorem asher_isSubPred : IsSubPred (desireModel AsherPred.trip) .free .trip :=
  isSubPred_desireModel (by decide)

/-- The monotonic step (27a) to (27b) is semantically valid on any model. -/
theorem asher_monotone {W Domain : Type*} [DecidableEq W] [DecidableEq Domain] [Fintype Domain]
    (M : Model W Domain Unit AsherPred) {s : Finset (Index W Var Domain)}
    (h : support M asherPremise s) : support M asherConcl s :=
  nec_exi_within_mono M h

/-- The enriched reinterpreted conclusion licenses being ok with a free trip, (27c), and with
a non-free trip, (27d). -/
theorem asher_fc {W Domain : Type*} [DecidableEq W] [DecidableEq Domain] [Fintype Domain]
    (M : Model W Domain Unit AsherPred) {s : Finset (Index W Var Domain)}
    (h : support M (Formula.enrich (reinterpret subFree .free asherConcl)) s) :
    support M (.poss (.exi .x (within .free .trip .x))) s ∧
      support M (.poss (.exi .x (without .free .trip .x))) s :=
  fc_of_reinterpret M ⟨rfl, rfl⟩ h

theorem asher_premise :
    support (desireModel AsherPred.trip) (Formula.enrich asherPremise) desireState :=
  desireModel_premise _ _

theorem asher_concl_enriched :
    support (desireModel AsherPred.trip) (Formula.enrich asherConcl) desireState :=
  desireModel_concl_enriched .free _

theorem asher_blocked :
    ¬ support (desireModel AsherPred.trip)
      (Formula.enrich (reinterpret subFree .free asherConcl)) desireState :=
  desireModel_blocked ⟨rfl, rfl⟩

/-! ### Heim's example, (2), (15)–(16)

TEACH is reinterpreted by its salient sub-predicate teaching on Tuesday; the paper leaves the
derivation as parallel to Asher's. -/

/-- The predicates of Heim's example are being on Tuesday and being a teaching next
semester. -/
inductive HeimPred
  | tuesday | teach
  deriving DecidableEq, Repr

/-- TUESDAY is the contextually salient sub-predicate of TEACH. -/
def subTuesday (P Q : HeimPred) : Prop := P = .tuesday ∧ Q = .teach

instance : DecidableRel subTuesday := λ _ _ => inferInstanceAs (Decidable (_ ∧ _))

/-- I want to teach next semester, `□∃x TEACH x`, (15b). -/
abbrev heimConcl : Formula Var Unit HeimPred := (Formula.exi .x (.pred .teach .x)).nec

/-- The enriched reinterpreted conclusion licenses being ok with teaching on a non-Tuesday,
(16c). -/
theorem heim_fc {W Domain : Type*} [DecidableEq W] [DecidableEq Domain] [Fintype Domain]
    (M : Model W Domain Unit HeimPred) {s : Finset (Index W Var Domain)}
    (h : support M (Formula.enrich (reinterpret subTuesday .tuesday heimConcl)) s) :
    support M (.poss (.exi .x (within .tuesday .teach .x))) s ∧
      support M (.poss (.exi .x (without .tuesday .teach .x))) s :=
  fc_of_reinterpret M ⟨rfl, rfl⟩ h

theorem heim_premise :
    support (desireModel HeimPred.teach)
      (Formula.enrich (Formula.nec (.exi Var.x (within .tuesday .teach .x)))) desireState :=
  desireModel_premise _ _

/-- The desire state of a speaker who teaches only on Tuesdays supports the enriched premise
(15a) but not the enriched reinterpreted conclusion. -/
theorem heim_blocked :
    ¬ support (desireModel HeimPred.teach)
      (Formula.enrich (reinterpret subTuesday .tuesday heimConcl)) desireState :=
  desireModel_blocked ⟨rfl, rfl⟩

end Yan2023
