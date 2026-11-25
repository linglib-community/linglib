/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Phase.Chain
public import Linglib.Syntax.Minimalist.Copy.AntiLocality
public import Linglib.Syntax.Minimalist.Derivation.Replay

/-!
# Transfer and the Phase Impenetrability Condition

Transfer seals the domain of a phase head, so that an operation at a later stage cannot inspect it:
the Phase Impenetrability Condition is the effect of Transfer on the search space. A stage is the
root of the object built so far, a position of the finished object, and a `Cut` assigns to each
stage the positions `sealed` by then. A phase head's domain is its complement or the whole phase
short of its root, [the larger of the two](##Minimalist.complementDomain_subset_wholePhaseDomain),
transferred on a `Schedule`; a deleted phase head passes its phasehood to the head of its
complement. A schedule is the merger of the head, the completion of its phase, as in
[chomsky-2000], or either of these [put off to the next phase](##Minimalist.Schedule.ofNextPhase),
as in [chomsky-2001], and waiting for the next head to merge
[waits past the phase's own completion](##Minimalist.Schedule.ofNextPhase_atMerger_le_atCompletion).
Sealed sets are [closed under dominance](##Minimalist.isUpperSet_sealed),
[grow as the derivation proceeds](##Minimalist.sealed_anti), and
[shrink with the domain and with a later schedule](##Minimalist.sealed_mono). Islands and the
condition on chain links [are](##Minimalist.escapes_iff) [cuts](##Minimalist.crosses_iff). A
position reaches its `phaseLevel` when the phase of the lowest phase head whose complement contains
it is complete. An object `RespectsCut` when no chain link of a pronounced token leaves the cut,
and a derivation `Respects` a cut when the object it derives does. The chain links of an object
are themselves a cut, `chainLinks`, and an object respects a cut exactly when the two are
[disjoint](##Minimalist.respectsCut_iff_disjoint), so that it respects a join of cuts exactly
when it [respects each](##Minimalist.respectsCut_sup).

## Implementation notes

* A stage is a position of the finished object, so the derivation is taken to be cyclic.
* The phase heads, and the deleted ones, are supplied by the analysis.

## References

* [chomsky-2000]
* [chomsky-2001]
* [chomsky-2015]
-/

@[expose] public section

namespace Minimalist

open RoseTree

/-- A cut assigns to each stage, the root of the object built so far, the positions an operation
at that stage cannot inspect. -/
abbrev Cut := GornAddress → Set GornAddress

/-- A schedule says, given the phase heads, whether the domain of `h` is transferred by stage `s`.
-/
abbrev Schedule := Finset GornAddress → GornAddress → GornAddress → Prop

variable (hd : HeadDaughter) (t : PlanarSyntacticObject)

/-- The head that transfers for a phase head: the phase head itself, or, where it has deleted, the
lexical head of its complement, which inherits its phasehood. -/
def transferHead (deleted : Finset GornAddress) (h : GornAddress) : GornAddress :=
  if h ∈ deleted then lexicalHeadAt hd t (complement h) else h

/-- The complement of a phase head, [chomsky-2000]'s transfer domain. -/
def complementDomain (h : GornAddress) : Set GornAddress := Set.Ici (complement h)

/-- The phase short of its root, transferred whole. -/
def wholePhaseDomain (h : GornAddress) : Set GornAddress := Set.Ioi (projectionAt hd t h)

/-- The domain of `h` is transferred once `h` has merged. -/
def Schedule.atMerger : Schedule := fun _ h s ↦ s ≤ h.parent

/-- The domain of `h` is transferred once its phase is complete, at every stage above it: the
timing of [chomsky-2000]'s Phase Impenetrability Condition. -/
def Schedule.atCompletion : Schedule := fun _ h s ↦ s < projectionAt hd t h

/-- The schedule `σ` put off by a phase: the domain of `h` is transferred once `σ` holds of a phase
head whose complement contains the phase of `h`. Applied to merger it is the timing of
[chomsky-2001]'s condition. -/
def Schedule.ofNextPhase (σ : Schedule) : Schedule :=
  fun Φ h s ↦ ∃ z ∈ Φ, σ Φ z s ∧ complement z ≤ projectionAt hd t h

/-- The positions sealed at stage `s`: the domains of the phase heads transferred by then. -/
def sealed (Φ : Finset GornAddress) (D : GornAddress → Set GornAddress) (σ : Schedule) : Cut :=
  fun s ↦ {q | ∃ h ∈ Φ, σ Φ h s ∧ q ∈ D h}

instance (h : GornAddress) : DecidablePred (· ∈ complementDomain h) :=
  fun q ↦ decidable_of_iff (complement h ≤ q) Iff.rfl

instance (h : GornAddress) : DecidablePred (· ∈ wholePhaseDomain hd t h) :=
  fun q ↦ decidable_of_iff (projectionAt hd t h < q) Iff.rfl

instance (Φ : Finset GornAddress) (h s : GornAddress) : Decidable (Schedule.atMerger Φ h s) :=
  inferInstanceAs (Decidable (_ ≤ _))

instance (Φ : Finset GornAddress) (h s : GornAddress) :
    Decidable (Schedule.atCompletion hd t Φ h s) :=
  inferInstanceAs (Decidable (_ < _))

instance (σ : Schedule) (Φ : Finset GornAddress) (h s : GornAddress)
    [∀ z, Decidable (σ Φ z s)] : Decidable (Schedule.ofNextPhase hd t σ Φ h s) :=
  inferInstanceAs (Decidable (∃ _ ∈ Φ, _))

instance (Φ : Finset GornAddress) (D : GornAddress → Set GornAddress) (σ : Schedule)
    [∀ h, DecidablePred (· ∈ D h)] [∀ h s, Decidable (σ Φ h s)] (s : GornAddress) :
    DecidablePred (· ∈ sealed Φ D σ s) :=
  fun _ ↦ inferInstanceAs (Decidable (∃ _ ∈ Φ, _))

variable {hd t} {Φ : Finset GornAddress} {D : GornAddress → Set GornAddress} {σ : Schedule}
  {h s : GornAddress}

theorem isUpperSet_complementDomain : IsUpperSet (complementDomain h) := IsUpperSet.Ici _

theorem isUpperSet_wholePhaseDomain : IsUpperSet (wholePhaseDomain hd t h) := IsUpperSet.Ioi _

/-- Sealed positions dominate only sealed positions. -/
theorem isUpperSet_sealed (hD : ∀ h, IsUpperSet (D h)) : IsUpperSet (sealed Φ D σ s) :=
  fun _ _ hab ⟨h, hΦ, hσ, hq⟩ ↦ ⟨h, hΦ, hσ, hD h hab hq⟩

/-- A schedule under which a domain stays transferred seals more at every later stage. -/
theorem sealed_anti (hσ : ∀ h, Antitone (σ Φ h)) : Antitone (sealed Φ D σ) :=
  fun _ _ hs _ ⟨h, hΦ, hσh, hq⟩ ↦ ⟨h, hΦ, hσ h hs hσh, hq⟩

namespace Schedule

theorem antitone_atMerger : Antitone (atMerger Φ h) := fun _ _ hs h ↦ hs.trans h

theorem antitone_atCompletion : Antitone (atCompletion hd t Φ h) :=
  fun _ _ hs h ↦ lt_of_le_of_lt hs h

theorem antitone_ofNextPhase (hσ : ∀ z, Antitone (σ Φ z)) : Antitone (ofNextPhase hd t σ Φ h) :=
  fun _ _ hs ⟨z, hz, hz', hc⟩ ↦ ⟨z, hz, hσ z hs hz', hc⟩

theorem ofNextPhase_mono {σ τ : Schedule} (hστ : σ ≤ τ) :
    ofNextPhase hd t σ ≤ ofNextPhase hd t τ :=
  fun Φ _ s ⟨z, hz, hσ, hc⟩ ↦ ⟨z, hz, hστ Φ z s hσ, hc⟩

/-- A phase is complete only after its head has merged. -/
theorem atCompletion_le_atMerger : atCompletion hd t ≤ atMerger := fun _ h s hs ↦ by
  have : s ≤ Order.pred h := Order.le_pred_of_lt (lt_of_lt_of_le hs (projectionAt_le hd t h))
  exact this

/-- The next phase head merges only after the phase is complete. -/
theorem ofNextPhase_atMerger_le_atCompletion : ofNextPhase hd t atMerger ≤ atCompletion hd t :=
  fun _ _ _ ⟨z, _, hs, hc⟩ ↦ hs.trans_lt ((GornAddress.parent_covBy_sister z).lt.trans_le hc)

end Schedule

theorem mem_sealed {q : GornAddress} : q ∈ sealed Φ D σ s ↔ ∃ h ∈ Φ, σ Φ h s ∧ q ∈ D h := Iff.rfl

/-- Smaller domains transferred later seal less. -/
theorem sealed_mono {D' : GornAddress → Set GornAddress} {σ' : Schedule}
    (hD : ∀ h ∈ Φ, D h ⊆ D' h) (hσ : ∀ h ∈ Φ, σ Φ h s → σ' Φ h s) :
    sealed Φ D σ s ⊆ sealed Φ D' σ' s :=
  fun _ ⟨h, hΦ, hs, hq⟩ ↦ ⟨h, hΦ, hσ h hΦ hs, hD h hΦ hq⟩

/-- A phase contains the complement of its head, so transferring it whole seals the head and the
edge besides. -/
theorem complementDomain_subset_wholePhaseDomain (hp : projectionAt hd t h ≤ h.parent) :
    complementDomain h ⊆ wholePhaseDomain hd t h := fun _ hq ↦
  (hp.trans_lt (GornAddress.parent_covBy_sister h).lt).trans_le hq

/-! ### What a phase head transfers on its own -/

/-- The positions in the domain of `h` outside the domain of every phase head inside it: what the
domain of `h` transfers on its own. -/
def transferSlice (Φ : Finset GornAddress) (D : GornAddress → Set GornAddress) (h : GornAddress) :
    Set GornAddress :=
  {q | q ∈ D h ∧ ∀ h' ∈ Φ, h' ∈ D h → q ∉ D h'}

instance [∀ h, DecidablePred (· ∈ D h)] : DecidablePred (· ∈ transferSlice Φ D h) :=
  fun _ ↦ inferInstanceAs (Decidable (_ ∧ ∀ _ ∈ Φ, _))

theorem transferSlice_subset : transferSlice Φ D h ⊆ D h := fun _ hq ↦ hq.1

theorem disjoint_transferSlice {h' : GornAddress} (hh' : h' ∈ Φ) (hin : h' ∈ D h) :
    Disjoint (transferSlice Φ D h) (D h') :=
  Set.disjoint_left.2 fun _ hq hq' ↦ hq.2 h' hh' hin hq'

/-! ### The phase level -/

variable (hd t) in
/-- The phase level of a position: the phase of the lowest phase head whose complement contains it,
or the root where there is none. [chomsky-2015] computes labels there. -/
def phaseLevel (Φ : Finset GornAddress) (q : t.toRoseTree.Positions) : t.toRoseTree.Positions :=
  ⟨⟨q.val.toList.take
      ((Φ.filter (complement · ≤ q.val)).sup (projectionAt hd t · |>.depth))⟩,
    isLowerSet_validPaths _ (GornAddress.le_def.2 (List.take_prefix _ _)) q.2⟩

theorem phaseLevel_le (q : t.toRoseTree.Positions) : phaseLevel hd t Φ q ≤ q :=
  Subtype.coe_le_coe.1 (GornAddress.le_def.2 (List.take_prefix _ _))

theorem projectionAt_le_phaseLevel {q : t.toRoseTree.Positions} (hΦ : h ∈ Φ) (hc : complement h ≤
    q.val)
    (hp : projectionAt hd t h ≤ h.parent) : projectionAt hd t h ≤ (phaseLevel hd t Φ q).val := by
  have hq := hp.trans ((GornAddress.parent_covBy_sister h).le.trans hc)
  exact GornAddress.le_def.2 (List.prefix_take_iff.2 ⟨GornAddress.le_def.1 hq,
    Finset.le_sup (f := (projectionAt hd t · |>.depth)) (Finset.mem_filter.2 ⟨hΦ, hc⟩)⟩)

theorem phaseLevel_eq_bot {q : t.toRoseTree.Positions} (hq : ∀ h ∈ Φ, ¬ complement h ≤ q.val) :
    phaseLevel hd t Φ q = ⊥ := by
  have : Φ.filter (complement · ≤ q.val) = ∅ := Finset.filter_eq_empty_iff.2 hq
  exact Subtype.ext (GornAddress.ext (by simp [phaseLevel, this]))

/-! ### Chain links that leave a cut -/

variable (hd t) in
/-- A link of the chain of `tok` leaves the positions `cut` seals at the stage of its landing site,
the mother of the phrase that lands. -/
def LinkLeaves (tok : LexicalItem.Token) (cut : Cut) : Prop :=
  ∃ x ∈ links hd t tok, x.2 ∈ cut x.1.parent

instance (tok : LexicalItem.Token) (cut : Cut) [∀ s, DecidablePred (· ∈ cut s)] :
    Decidable (LinkLeaves hd t tok cut) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

variable {tok : LexicalItem.Token} {cut cut' : Cut} in
/-- A link that leaves a cut leaves every cut that seals more. -/
theorem LinkLeaves.mono (h : cut ≤ cut') (hl : LinkLeaves hd t tok cut) :
    LinkLeaves hd t tok cut' :=
  let ⟨x, hx, hc⟩ := hl
  ⟨x, hx, h _ hc⟩

theorem mem_links {tok : LexicalItem.Token} {x : GornAddress × GornAddress} :
    x ∈ links hd t tok ↔ ∃ q ∈ chain t tok, ∃ p ∈ chain t tok, IsLink hd t tok p q ∧
      x = (projectionAt hd t p, q) := by
  simp only [links, List.mem_flatMap, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨q, hq, p, ⟨hp, hl⟩, rfl⟩
    exact ⟨q, hq, p, hp, hl, rfl⟩
  · rintro ⟨q, hq, p, hp, hl, rfl⟩
    exact ⟨q, hq, p, ⟨hp, hl⟩, rfl⟩

theorem mem_validPaths_of_mem_chain {tok : LexicalItem.Token} {p : GornAddress}
    (hp : p ∈ chain t tok) : p ∈ t.toRoseTree.validPaths := by
  simp only [chain, List.mem_filterMap, Option.ite_none_right_eq_some, Option.some.injEq] at hp
  obtain ⟨⟨p', b⟩, hpb, -, rfl⟩ := hp
  obtain ⟨s, hs, -⟩ := mem_positions_iff.1 hpb
  exact (getElem?_eq_some_iff.mp hs).1

theorem parent_lt_of_mem_links {tok : LexicalItem.Token} {x : GornAddress × GornAddress}
    (hx : x ∈ links hd t tok) : x.1.parent < x.2 ∧ ¬ x.1 ≤ x.2 := by
  obtain ⟨q, -, p, hp, hl, rfl⟩ := mem_links.1 hx
  have hv : projectionAt hd t p ∈ t.toRoseTree.validPaths :=
    isLowerSet_validPaths _ (projectionAt_le hd t p) (mem_validPaths_of_mem_chain hp)
  have h0 : projectionAt hd t p ≠ ⊥ := fun h ↦ hl.1.2.1 (h ▸ bot_le)
  have hb := PlanarSyntacticObject.parent_mem_branching (t := t)
    (a := ⟨projectionAt hd t p, hv⟩) fun h ↦ h0 (congrArg Subtype.val h)
  exact (cCommands_iff_parent_lt h0 hb).1 hl.1

theorem not_le_fst_iff {tok : LexicalItem.Token} {x : GornAddress × GornAddress} {D : GornAddress}
    (hx : x ∈ links hd t tok) (hD : D ≤ x.2) : ¬ D ≤ x.1 ↔ x.1.parent < D := by
  obtain ⟨hpx, hnx⟩ := parent_lt_of_mem_links hx
  have h0 : x.1 ≠ ⊥ := fun h ↦ hnx (h ▸ bot_le)
  have hcov : x.1.parent ⋖ x.1 := by
    rw [← GornAddress.pred_eq_parent]
    exact Order.pred_covBy_of_not_isMin (by simpa [isMin_iff_eq_bot] using h0)
  constructor
  · intro hDx
    rcases IsForestOrder.le_total_of_le_of_le hD hpx.le with h | h
    · exact absurd (h.trans hcov.le) hDx
    · exact lt_of_le_of_ne h fun he ↦ hDx (he ▸ hcov.le)
  · intro hlt hDx
    exact hnx (((hcov.eq_or_eq hlt.le hDx).resolve_left hlt.ne') ▸ hD)

/-- An island is a cut: a link escapes the domain at `D` exactly when it leaves the positions `D`
dominates, sealed at every stage above `D`. -/
theorem escapes_iff {tok : LexicalItem.Token} {D : GornAddress} :
    Escapes hd t tok D ↔ LinkLeaves hd t tok (sealed {D} Set.Ici fun _ h s ↦ s < h) := by
  unfold Escapes LinkLeaves
  refine exists_congr fun x ↦ and_congr_right fun hx ↦ ?_
  simp only [sealed, Finset.mem_singleton, exists_eq_left, Set.mem_Ici, Set.mem_ofPred_eq]
  exact ⟨fun ⟨hD, hDx⟩ ↦ ⟨(not_le_fst_iff hx hD).1 hDx, hD⟩,
    fun ⟨hlt, hD⟩ ↦ ⟨hD, (not_le_fst_iff hx hD).2 hlt⟩⟩

/-- The condition on chain links is a cut: a link leaves the phase of `h` exactly when it leaves the
complement of `h`, sealed at every stage above the phase. -/
theorem crosses_iff {tok : LexicalItem.Token} {h : GornAddress} (hh : h ∈ t.toRoseTree.validPaths)
    (h0 : h ≠ ⊥) (hproj : projectionAt hd t h ≤ h.parent) :
    Crosses hd t tok h ↔
      LinkLeaves hd t tok (sealed {h} complementDomain (.atCompletion hd t)) := by
  unfold Crosses LinkLeaves
  refine exists_congr fun x ↦ and_congr_right fun hx ↦ ?_
  obtain ⟨q, hq, p, -, -, rfl⟩ := mem_links.1 hx
  simp only [sealed, Finset.mem_singleton, exists_eq_left, Schedule.atCompletion,
    complementDomain, Set.mem_Ici, Set.mem_ofPred_eq]
  rw [cCommands_iff_complement_le hh h0 (mem_validPaths_of_mem_chain hq)]
  have hle : ∀ hc : complement h ≤ q, projectionAt hd t h ≤ q := fun hc ↦
    hproj.trans ((GornAddress.parent_covBy_sister h).le.trans hc)
  exact ⟨fun ⟨hc, hn⟩ ↦ ⟨(not_le_fst_iff hx (hle hc)).1 hn, hc⟩,
    fun ⟨hlt, hc⟩ ↦ ⟨hc, (not_le_fst_iff hx (hle hc)).2 hlt⟩⟩

/-! ### Anti-locality and the PIC -/

/-- A link that moves the complement of a phase head, landing outside it, moves it to a
specifier of the head's phrase or leaves the complement after the phase is complete: with the
PIC, Abels's anti-locality leaves the complement of a phase head no way out. -/
theorem compToSpec_or_mem_sealed {tok : LexicalItem.Token} {x : GornAddress × GornAddress}
    {h : GornAddress} (hh : h ∈ t.toRoseTree.validPaths) (h0 : h ≠ ⊥) (hhead : IsHeadPosition t h)
    (hx : x ∈ links hd t tok) (hr : projectionAt hd t x.2 = complement h)
    (hin : ¬ complement h ≤ x.1.parent) :
    CompToSpec hd t x ∨ x.2 ∈ sealed {h} complementDomain (.atCompletion hd t) x.1.parent := by
  have hcx : complement h ≤ x.2 := hr ▸ projectionAt_le hd t x.2
  have hlt : x.1.parent < complement h :=
    ((IsForestOrder.le_total_of_le_of_le (parent_lt_of_mem_links hx).1.le hcx).resolve_right
      hin).lt_of_ne fun he ↦ hin he.ge
  have hle : x.1.parent ≤ h.parent := by
    simpa [GornAddress.pred_eq_parent] using Order.le_pred_of_lt hlt
  have hcomp : CompToSpec hd t x ↔ projectionAt hd t h ≤ x.1.parent := by
    rw [CompToSpec, hr, complement_complement hh h0]
    exact and_iff_right hhead
  rcases IsForestOrder.le_total_of_le_of_le (projectionAt_le hd t h)
    (hle.trans (GornAddress.parent_le h)) with hph | hph
  · exact .inl (hcomp.2 hph)
  · rcases hph.lt_or_eq with hph | hph
    · refine .inr ⟨h, Finset.mem_singleton_self h, hph, ?_⟩
      exact hcx
    · exact .inl (hcomp.2 hph.ge)

/-! ### Respecting a cut -/

section RespectsCut

variable {hd : HeadDaughter} {t : PlanarSyntacticObject} {cut cut' : Cut}

variable (hd t) in
/-- No chain link of a pronounced token of `t` leaves the cut. With the complements of the phase
heads sealed at completion this is the Phase Impenetrability Condition of [chomsky-2000]. -/
def RespectsCut (cut : Cut) : Prop :=
  ∀ q tok, (q, tok) ∈ tokenList t.toRoseTree → ¬ LinkLeaves hd t tok cut

theorem respectsCut_iff_forall_mem :
    RespectsCut hd t cut ↔ ∀ y ∈ tokenList t.toRoseTree, ¬ LinkLeaves hd t y.2 cut :=
  ⟨fun h y hy ↦ h y.1 y.2 hy, fun h q tok hq ↦ h (q, tok) hq⟩

instance [∀ s, DecidablePred (· ∈ cut s)] : Decidable (RespectsCut hd t cut) :=
  decidable_of_iff _ respectsCut_iff_forall_mem.symm

variable (hd t) in
/-- The chain links of the pronounced tokens of `t` as a cut: at the stage of a link's landing
site, the position of its lower copy. -/
def chainLinks : Cut := fun s ↦
  {q | ∃ y ∈ tokenList t.toRoseTree, ∃ x ∈ links hd t y.2, x.1.parent = s ∧ x.2 = q}

/-- An object respects a cut exactly when the cut is disjoint from its chain links. -/
theorem respectsCut_iff_disjoint : RespectsCut hd t cut ↔ Disjoint cut (chainLinks hd t) := by
  simp only [Pi.disjoint_iff, Set.disjoint_left, RespectsCut, LinkLeaves, chainLinks,
    Set.mem_ofPred_eq]
  constructor
  · rintro h s q hq ⟨y, hy, x, hx, rfl, rfl⟩
    exact h y.1 y.2 hy ⟨x, hx, hq⟩
  · rintro h q tok hq ⟨x, hx, hc⟩
    exact h _ hc ⟨(q, tok), hq, x, hx, rfl, rfl⟩

/-- An object that respects a cut respects any cut that seals less. -/
theorem RespectsCut.anti (h : cut ≤ cut') (hr : RespectsCut hd t cut') : RespectsCut hd t cut :=
  respectsCut_iff_disjoint.2 ((respectsCut_iff_disjoint.1 hr).mono_left h)

variable (hd t) in
@[simp] theorem respectsCut_bot : RespectsCut hd t ⊥ := respectsCut_iff_disjoint.2 disjoint_bot_left

/-- An object respects the join of two cuts exactly when it respects each. -/
theorem respectsCut_sup :
    RespectsCut hd t (cut ⊔ cut') ↔ RespectsCut hd t cut ∧ RespectsCut hd t cut' := by
  simp only [respectsCut_iff_disjoint, disjoint_sup_left]

theorem mem_validPaths_of_mem_tokenList {q : GornAddress} {tok : LexicalItem.Token}
    (h : (q, tok) ∈ tokenList t.toRoseTree) : q ∈ t.toRoseTree.validPaths := by
  obtain ⟨s, hs, -⟩ := mem_positions_iff.1 h
  exact (getElem?_eq_some_iff.mp hs).1

/-- An object that respects the complements of the phase heads `Φ`, sealed at completion, has no
chain link that crosses the phase of a head in `Φ` that projects. -/
theorem RespectsCut.not_crosses {Φ : Finset GornAddress} {h q : GornAddress}
    {tok a : LexicalItem.Token}
    (hr : RespectsCut hd t (sealed Φ complementDomain (.atCompletion hd t)))
    (hq : (q, tok) ∈ tokenList t.toRoseTree) (hΦ : h ∈ Φ) (ha : (h, a) ∈ tokenList t.toRoseTree)
    (h0 : h ≠ ⊥) (hproj : projectionAt hd t h ≤ h.parent) : ¬ Crosses hd t tok h := by
  refine fun hc ↦ hr q tok hq
    (((crosses_iff (mem_validPaths_of_mem_tokenList ha) h0 hproj).1 hc).mono fun s p hp ↦ ?_)
  obtain ⟨k, hk, hσ, hp⟩ := hp
  obtain rfl := Finset.mem_singleton.1 hk
  exact ⟨k, hΦ, hσ, hp⟩

/-- The object a derivation derives respects the cut assigned to it. -/
def Derivation.Respects (d : Derivation) (hd : HeadDaughter) (cut : PlanarSyntacticObject → Cut) :
    Prop :=
  ∃ t ∈ d.externalize?, RespectsCut hd t (cut t)

instance {d : Derivation} {cut : PlanarSyntacticObject → Cut}
    [∀ t s, DecidablePred (· ∈ cut t s)] : Decidable (d.Respects hd cut) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

theorem Derivation.Respects.anti {d : Derivation} {cut cut' : PlanarSyntacticObject → Cut}
    (h : ∀ t, cut t ≤ cut' t) (hr : d.Respects hd cut') : d.Respects hd cut :=
  let ⟨t, ht, hr⟩ := hr
  ⟨t, ht, hr.anti (h t)⟩

/-- A derivation respects the join of two cuts exactly when it respects each. -/
theorem Derivation.respects_sup {d : Derivation} {cut cut' : PlanarSyntacticObject → Cut} :
    d.Respects hd (cut ⊔ cut') ↔ d.Respects hd cut ∧ d.Respects hd cut' := by
  constructor
  · rintro ⟨t, ht, h⟩
    exact ⟨⟨t, ht, (respectsCut_sup.1 h).1⟩, t, ht, (respectsCut_sup.1 h).2⟩
  · rintro ⟨⟨t, ht, h⟩, t', ht', h'⟩
    obtain rfl := Option.mem_unique ht ht'
    exact ⟨t, ht, respectsCut_sup.2 ⟨h, h'⟩⟩

end RespectsCut

end Minimalist
