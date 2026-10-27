module

public import Linglib.Syntax.Minimalist.Probe.Movement
public import Linglib.Syntax.Minimalist.Linearization.Replay
public import Linglib.Data.Examples.HammerlyMathieu2026
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Syntax.Minimalist.Label.RaisingHead

/-!
# Hammerly and Mathieu (2026): long-distance agreement in Border Lakes Ojibwe

A matrix verb in Border Lakes Ojibwe agrees with the embedded argument in Spec,CP, and probes on
Voice, Infl and C with conditions on agreement and on movement decide which argument gets there.
Plain Voice moves a local patient into a second specifier, making the arguments equidistant, and
C's φ ∨ δ probe moves the one bearing δ, by Best Match.

## Main definitions

* `HammerlyMathieu2026.probeStep`: a head's Agree and movement on the syntactic object it heads.
* `HammerlyMathieu2026.target`: the argument C's probe moves to Spec,CP.

## Implementation notes

* The clause is a linearized syntactic object, closeness the maximal projections above a position,
  and movement Internal Merge replayed on it; arguments are nominal leaves. The rows are coded as
  Glottolog's Rainy River Ojibwa, the dialect around Fort Frances, where the speakers consulted are
  from.

## TODO

* Theme signs and impoverishment; agent LDA without Voice's [PART] probe (section 4); fn. 6.

## References

* [hammerly-mathieu-2026]
* [oxford-2019]
* [oxford-2023]
* [lesourd-2019]
* [deal-2024]
-/

@[expose] public section

namespace HammerlyMathieu2026

open Minimalist Probe Core.Order

/-! ### Features, section 3.1 -/

/-- The person, obviation and animacy features of (22), each borne by one category and every more
prominent one: [φ] by every nominal, [ANIM] by the obviative and up, [PROX] by the proximate and
the local persons, [PART] by the first and second persons, and [ADDR] by the second. A category
is its most specific feature. -/
inductive PhiFeature where
  | phi | anim | prox | part | addr
  deriving DecidableEq, Repr, Fintype

instance : LinearOrder PhiFeature := LinearOrder.lift' PhiFeature.ctorIdx (by decide)

/-- A feature a probe seeks, a φ-feature or the δ-feature related to evidentiality. -/
inductive Feature where
  | phi (f : PhiFeature)
  | delta
  deriving DecidableEq, Repr, Fintype

/-- The geometry of (22): a φ-feature dominates the more specific ones, and δ stands alone. -/
def Feature.Le : Feature → Feature → Prop
  | .phi f, .phi g => f ≤ g
  | .delta, .delta => True
  | _, _ => False

instance : DecidableRel Feature.Le := fun a b ↦ by
  cases a <;> cases b <;> unfold Feature.Le <;> infer_instance

instance : PartialOrder Feature where
  le := Feature.Le
  le_refl a := by cases a <;> simp [Feature.Le]
  le_trans := by decide
  le_antisymm := by decide

instance : DecidableLE Feature := inferInstanceAs (DecidableRel Feature.Le)

/-- `Finset.Ici f` is `f` and the features it dominates. -/
instance : LocallyFiniteOrderTop Feature :=
  .ofIci' Feature (fun a ↦ Finset.univ.filter (a ≤ ·)) fun _ _ ↦ by simp

@[simp] theorem Feature.phi_le_phi {f g : PhiFeature} : Feature.phi f ≤ .phi g ↔ f ≤ g :=
  Iff.rfl

/-- The φ-features as features. -/
def Feature.ofPhi : PhiFeature ↪ Feature := ⟨.phi, fun _ _ ↦ Feature.phi.inj⟩

/-- The features of a nominal whose category is `f`, the φ-features `f` contains (22). -/
def phiFeatures (f : PhiFeature) : Finset Feature := (Finset.univ.filter (· ≤ f)).map Feature.ofPhi

@[simp] theorem mem_phiFeatures {f g : PhiFeature} : Feature.phi g ∈ phiFeatures f ↔ g ≤ f := by
  simp [phiFeatures, Feature.ofPhi]

@[simp] theorem delta_not_mem_phiFeatures (f : PhiFeature) : Feature.delta ∉ phiFeatures f := by
  simp [phiFeatures, Feature.ofPhi]

/-- The probe relativized to `f`, [INT:{f}, SAT:{f}], whose interaction copies `f` and the
φ-features it dominates. -/
def relativizedTo (f : PhiFeature) : Spec Feature := .relativized (.phi f)

/-- An argument of the embedded clause. -/
structure Arg where
  /-- The category, the most specific φ-feature. -/
  phi : PhiFeature
  /-- Whether the argument bears δ. -/
  delta : Bool
  deriving DecidableEq, Repr

/-- The features of an argument. -/
def Arg.features (x : Arg) : Finset Feature :=
  if x.delta then insert .delta (phiFeatures x.phi) else phiFeatures x.phi

/-- The roles of the arguments of a transitive clause. -/
inductive Role where
  | ea | ia
  deriving DecidableEq, Repr, Fintype

/-- An embedded transitive clause. -/
structure Clause where
  /-- The agent. -/
  ea : Arg
  /-- The patient. -/
  ia : Arg
  deriving DecidableEq, Repr

/-! ### The probes, section 3.2 -/

/-- The two Voice heads of (23), after [oxford-2023]. -/
inductive Voice where
  | plain | ergative
  deriving DecidableEq, Repr

/-- Voice's agreement probe, plain Voice's [INT:{φ}, SAT:{φ}] (23a); ergative Voice does not
Agree (23b). -/
def Voice.agr : Voice → Spec Feature
  | .plain => relativizedTo .phi
  | .ergative => ⊥

/-- Voice's movement probe, plain Voice's relativized EPP [INT:{PART}, SAT:{PART}] (23a) and
ergative Voice's [INT:{φ}, SAT:{φ}] (23b). -/
def Voice.epp : Voice → Spec Feature
  | .plain => relativizedTo .part
  | .ergative => relativizedTo .phi

/-- The agreement probe of Infl (24), [INT:{φ}, SAT:{PROX}]. -/
def inflAgr : Spec Feature := .ofGeometry (.phi .phi) (.phi .prox)

/-- The movement probe of Infl (24), [INT:{PROX}, SAT:{PROX}]. -/
def inflEpp : Spec Feature := relativizedTo .prox

/-- C's pure φ-probe, of agent and highest-ranked LDA (31b, c). -/
def phiEpp : Spec Feature := relativizedTo .phi

/-- C's pure δ-probe, of free LDA (31a). -/
def deltaEpp : Spec Feature := .relativized .delta

/-- The movement probe of C (25), (32), [INT:{φ ∨ δ}, SAT:{φ ∨ δ}], the join of the φ-probe and the
δ-probe, so that a goal bearing both matches better than a goal bearing one. -/
def cEpp : Spec Feature := phiEpp ⊔ deltaEpp

/-- The deep inverse, an obviative agent acting on a proximate patient. -/
def Clause.IsDeepInverse (x : Clause) : Prop := x.ea.phi = .anim ∧ x.ia.phi = .prox

instance : DecidablePred Clause.IsDeepInverse := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- The Voice of a clause, ergative in the deep inverse, the one configuration considered in which
it converges, and plain otherwise ([oxford-2023]). -/
def Clause.voice (x : Clause) : Voice := if x.IsDeepInverse then .ergative else .plain

/-! ### The clause as a syntactic object, section 3 -/

/-- The verb stem, the root with the verbalizing v, whose specifier is the patient (3). -/
def stem : LexicalItem.Token := ⟨.of .v [.D] "stem", 0⟩

/-- Voice, the theme sign, whose specifier is the agent. -/
def voiceHead : LexicalItem.Token := ⟨.of .Voice [.v, .D] "Voice", 0⟩

/-- Infl, the person prefix and central agreement. -/
def inflHead : LexicalItem.Token := ⟨.of .T [.Voice] "Infl", 0⟩

/-- C, the peripheral suffix. -/
def cHead : LexicalItem.Token := ⟨.of .C [.T] "C", 0⟩

/-- The agent. -/
def agent : LexicalItem.Token := ⟨.of .D [] "agent", 0⟩

/-- The patient. -/
def patient : LexicalItem.Token := ⟨.of .D [] "patient", 0⟩

/-- The features a head copied by Agree, which a higher probe can Agree with ([oxford-2023]). -/
abbrev Copies := LexicalItem.Token → Finset Feature

/-- The features a token exposes to a probe: an argument's features, none for an agent deactivated
by the inherent case ergative Voice assigns, and what a head has copied. -/
def featuresOf (v : Voice) (x : Clause) (c : Copies) (tok : LexicalItem.Token) : Finset Feature :=
  if tok = agent then (if v = .plain then x.ea.features else ∅)
  else if tok = patient then x.ia.features else c tok

/-- The features at a position, those of its token and none for a trace or a phrase. -/
def featuresAt (v : Voice) (x : Clause) (c : Copies) (t : LinearizedSyntacticObject)
    (q : t.val.Positions) : Finset Feature :=
  ((t.termAt q).token?).elim ∅ (featuresOf v x c)

/-- A position bears a nominal; only nominals move (section 3.5.1). -/
def isNominal (t : LinearizedSyntacticObject) (q : t.val.Positions) : Bool :=
  ((t.termAt q).token?).elim false (·.item.cat == .D)

/-- Closeness in the clause: the maximal projections above a position, under which the specifiers
of a head and the head itself are equidistant. -/
abbrev closeness (t : LinearizedSyntacticObject) : t.val.Positions → Finset TreePath :=
  t.above (maximalProjections .raising t)

/-- A stage of the derivation: the object built, what the heads have copied, and the token the
last probe moved. -/
structure Stage where
  /-- The object built. -/
  obj : LinearizedSyntacticObject
  /-- What each head has copied. -/
  copies : Copies
  /-- The token the last probe moved, if any. -/
  moved : Option LexicalItem.Token := none

/-- What the head `h` at the position `hq` of the object copies by Agree under Best Match with
`agr`, added to what the heads have copied. -/
def agreeCopies (v : Voice) (x : Clause) (h : LexicalItem.Token) (agr : Spec Feature) (st : Stage)
    (hq : st.obj.val.Positions) : Copies :=
  let feats := featuresAt v x st.copies st.obj
  Function.update st.copies h
    (agr.copied feats {q | st.obj.val.CCommands hq q} (agr.bestMatch feats (closeness st.obj)))

/-- The nominals a head at the position `hq` c-commands, among which its EPP probe searches. -/
def nominalDomain (t : LinearizedSyntacticObject) (hq : t.val.Positions) : Set t.val.Positions :=
  {q | t.val.CCommands hq q ∧ isNominal t q = true}

instance (t : LinearizedSyntacticObject) (hq : t.val.Positions) :
    DecidablePred (· ∈ nominalDomain t hq) :=
  fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- A probing head at the position `hp` of the object: it Agrees by `agr` under Best Match,
recording what it copies, and attracts the nominal it agrees with by `epp`, which re-merges as its
outer specifier. -/
def probeStep (v : Voice) (x : Clause) (h : LexicalItem.Token) (hp : TreePath)
    (agr epp : Spec Feature) (st : Stage) : Stage :=
  let t := st.obj
  if hhp : hp ∈ t.val.validPaths then
    let c := agreeCopies v x h agr st ⟨hp, hhp⟩
    let feats' := featuresAt v x c t
    match t.attractStep? (epp.toProbe feats') (nominalDomain t ⟨hp, hhp⟩)
        (epp.bestMatch feats' (closeness t)) with
    | some step =>
        ⟨((step.replay? ⟨t, []⟩).map (·.current)).getD t, c, step.mover?.bind (·.token?)⟩
    | none => ⟨t, c, none⟩
  else st

/-- The vP, the patient in Spec,vP. -/
def vP : LinearizedSyntacticObject := {↑patient, ↑stem}

/-- The VoiceP of Voice `v`, the agent its specifier. -/
def voiceP (v : Voice) (x : Clause) : Stage :=
  probeStep v x voiceHead ⟨[1, 0]⟩ v.agr v.epp ⟨{↑agent, {↑voiceHead, vP}}, fun _ ↦ ∅, none⟩

/-- The IP over the VoiceP of Voice `v`. -/
def inflP (v : Voice) (x : Clause) : Stage :=
  let s := voiceP v x
  probeStep v x inflHead ⟨[0]⟩ inflAgr inflEpp ⟨{↑inflHead, s.obj}, s.copies, none⟩

/-- The CP with a movement probe `c` on C, over the VoiceP of Voice `v`. -/
def cP (c : Spec Feature) (v : Voice) (x : Clause) : Stage :=
  let s := inflP v x
  probeStep v x cHead ⟨[0]⟩ ⊥ c ⟨{↑cHead, s.obj}, s.copies, none⟩

/-- The role of an argument token. -/
def roleOf (tok : LexicalItem.Token) : Option Role :=
  if tok = agent then some .ea else if tok = patient then some .ia else none

/-- The argument a probe `c` on C moves to Spec,CP, and so the target of LDA. -/
def target (c : Spec Feature) (x : Clause) : Option Role :=
  (cP c x.voice x).moved.bind roleOf

/-- The clause of an agent and a patient of categories `ea` and `ia`, bearing δ as `δe` and
`δi` say. -/
abbrev clause (ea ia : PhiFeature) (δe δi : Bool) : Clause := ⟨⟨ea, δe⟩, ⟨ia, δi⟩⟩

/-- LDA with a probe `c` on C can target the argument of role `r` in a clause whose agent and
patient have categories `ea` and `ia`, for some placement of δ. -/
def CanTarget (c : Spec Feature) (ea ia : PhiFeature) (r : Role) : Prop :=
  ∃ δe δi : Bool, target c (clause ea ia δe δi) = some r

instance (c : Spec Feature) (ea ia : PhiFeature) (r : Role) : Decidable (CanTarget c ea ia r) :=
  inferInstanceAs (Decidable (∃ _ _, _))

/-! ### The derivations (26) to (30), with no δ -/

/-- An argument without δ. -/
abbrev bare (f : PhiFeature) : Arg := ⟨f, false⟩

/-- (26): Voice Agrees with the obviative patient and leaves it in place, and Infl Agrees with the
proximate agent and moves it. -/
theorem derivation_26 :
    (voiceP .plain ⟨bare .prox, bare .anim⟩).obj = {↑agent, {↑voiceHead, vP}} ∧
      (voiceP .plain ⟨bare .prox, bare .anim⟩).copies voiceHead = phiFeatures .anim ∧
      (inflP .plain ⟨bare .prox, bare .anim⟩).obj =
        {↑agent, {↑inflHead, {.traceOf agent, {↑voiceHead, vP}}}} ∧
      (inflP .plain ⟨bare .prox, bare .anim⟩).copies inflHead = phiFeatures .prox := by
  decide +kernel

-- (27) [oxford-2019]
theorem derivation_27 :
    (voiceP .ergative ⟨bare .anim, bare .prox⟩).obj =
        {↑patient, {↑agent, {↑voiceHead, {.traceOf patient, ↑stem}}}} ∧
      (voiceP .ergative ⟨bare .anim, bare .prox⟩).copies voiceHead = ∅ ∧
      (inflP .ergative ⟨bare .anim, bare .prox⟩).obj = {↑patient, {↑inflHead, {.traceOf patient,
        {↑agent, {↑voiceHead, {.traceOf patient, ↑stem}}}}}} ∧
      (inflP .ergative ⟨bare .anim, bare .prox⟩).copies inflHead = phiFeatures .prox := by
  decide +kernel

-- (28)
theorem derivation_28 :
    (voiceP .plain ⟨bare .part, bare .addr⟩).obj =
        {↑patient, {↑agent, {↑voiceHead, {.traceOf patient, ↑stem}}}} ∧
      (inflP .plain ⟨bare .part, bare .addr⟩).obj =
        {↑inflHead, {↑patient, {↑agent, {↑voiceHead, {.traceOf patient, ↑stem}}}}} ∧
      (inflP .plain ⟨bare .part, bare .addr⟩).moved = none ∧
      (inflP .plain ⟨bare .part, bare .addr⟩).copies inflHead = phiFeatures .addr := by
  decide +kernel

-- (29)
theorem derivation_29 :
    (voiceP .plain ⟨bare .part, bare .prox⟩).obj = {↑agent, {↑voiceHead, vP}} ∧
      (voiceP .plain ⟨bare .part, bare .prox⟩).copies voiceHead = phiFeatures .prox ∧
      (inflP .plain ⟨bare .part, bare .prox⟩).obj =
        {↑agent, {↑inflHead, {.traceOf agent, {↑voiceHead, vP}}}} := by
  decide +kernel

/-- (30): Voice moves the first person patient into a second specifier, and Infl moves neither
argument. -/
theorem derivation_30 :
    (voiceP .plain ⟨bare .prox, bare .part⟩).obj =
        {↑patient, {↑agent, {↑voiceHead, {.traceOf patient, ↑stem}}}} ∧
      (inflP .plain ⟨bare .prox, bare .part⟩).moved = none := by
  decide +kernel

theorem voiceP_moved_iff :
    ∀ (e f : PhiFeature) (δ : Bool), e ≠ .anim →
      ((voiceP .plain ⟨bare e, ⟨f, δ⟩⟩).moved = some patient ↔ .part ≤ f) := by
  decide +kernel

/-! ### The pattern (19) -/

/-- (19a-i): with a proximate agent and an obviative patient, LDA targets the agent, wherever δ
is. -/
theorem target_direct : ∀ δe δi, target cEpp (clause .prox .anim δe δi) = some .ea := by
  decide +kernel

/-- (19a-ii): in the deep inverse LDA targets the proximate patient, wherever δ is. -/
theorem target_inverse : ∀ δe δi, target cEpp (clause .anim .prox δe δi) = some .ia := by
  decide +kernel

/-- (19b): between local persons LDA can target either argument. -/
theorem canTarget_local :
    ∀ r, CanTarget cEpp .part .addr r ∧ CanTarget cEpp .addr .part r := by
  decide +kernel

/-- (19c-i): a local agent acting on a proximate patient is the only possible target. -/
theorem canTarget_localAgent :
    ∀ ea, .part ≤ ea → ∀ r, (CanTarget cEpp ea .prox r ↔ r = .ea) := by
  decide +kernel

/-- (19c-ii): a proximate agent acting on a local patient leaves LDA free. -/
theorem canTarget_localPatient : ∀ ia, .part ≤ ia → ∀ r, CanTarget cEpp .prox ia r := by
  decide +kernel

/-- The arguments of an object in their surface order. -/
def argumentOrder (t : LinearizedSyntacticObject) : List LexicalItem.Token :=
  t.yield.filter (· ∈ [agent, patient])

-- (9), (11)
theorem argumentOrder_nonlocal :
    ∀ δe δi,
      argumentOrder (cP cEpp .plain (clause .prox .anim δe δi)).obj = [agent, patient] ∧
        argumentOrder (cP cEpp .ergative (clause .anim .prox δe δi)).obj = [patient, agent] := by
  decide +kernel

/-- With plain Voice the deep inverse yields the same target and order: Infl skips the obviative
agent, which lacks [PROX], and moves the patient. So LDA does not need ergative Voice; its theme
sign does, since plain Voice copies the patient's features. -/
theorem target_inverse_plain :
    ∀ δe δi, (cP cEpp .plain (clause .anim .prox δe δi)).moved = some patient ∧
      argumentOrder (cP cEpp .plain (clause .anim .prox δe δi)).obj = [patient, agent] ∧
      (voiceP .plain (clause .anim .prox δe δi)).copies voiceHead = phiFeatures .prox := by
  decide +kernel

/-! ### Optional movement, fn. 8 -/

/-- The stages a probing head may leave when, as two reviewers suggest, a tie moves either goal: one
for each nominal the probe agrees with, or the object unchanged if it agrees with none. -/
def probeOptions (v : Voice) (x : Clause) (h : LexicalItem.Token) (hp : TreePath)
    (agr epp : Spec Feature) (st : Stage) : Multiset Stage :=
  let t := st.obj
  if hhp : hp ∈ t.val.validPaths then
    let c := agreeCopies v x h agr st ⟨hp, hhp⟩
    let feats' := featuresAt v x c t
    let movers := Finset.univ.filter fun q ↦ (epp.toProbe feats').AgreesWith
      (nominalDomain t ⟨hp, hhp⟩) (epp.bestMatch feats' (closeness t)) q
    if movers = ∅ then {⟨t, c, none⟩} else movers.val.map fun q ↦
      ⟨(((Step.im (t.termAt q)).replay? ⟨t, []⟩).map (·.current)).getD t, c, (t.termAt q).token?⟩
  else {st}

/-- The targets of LDA under optional movement. -/
def targetsOptional (c : Spec Feature) (x : Clause) : Multiset (Option Role) :=
  let v := x.voice
  ((probeOptions v x voiceHead ⟨[1, 0]⟩ v.agr v.epp
      ⟨{↑agent, {↑voiceHead, vP}}, fun _ ↦ ∅, none⟩).bind fun s ↦
    probeOptions v x inflHead ⟨[0]⟩ inflAgr inflEpp ⟨{↑inflHead, s.obj}, s.copies, none⟩).bind
      fun s ↦ (probeOptions v x cHead ⟨[0]⟩ ⊥ c ⟨{↑cHead, s.obj}, s.copies, none⟩).map
        (·.moved.bind roleOf)

/-- LDA can target role `r` under optional movement. -/
def CanTargetOptional (c : Spec Feature) (ea ia : PhiFeature) (r : Role) : Prop :=
  ∃ δe δi : Bool, some r ∈ targetsOptional c (clause ea ia δe δi)

instance (c : Spec Feature) (ea ia : PhiFeature) (r : Role) :
    Decidable (CanTargetOptional c ea ia r) :=
  inferInstanceAs (Decidable (∃ _ _, _))

/-- Optional movement of tied goals gives the same pattern, as fn. 8 observes. -/
theorem canTargetOptional_iff :
    ∀ ea ia r, (CanTargetOptional cEpp ea ia r ↔ CanTarget cEpp ea ia r) := by
  decide +kernel

/-! ### The judgments, and the typology of section 4 -/

/-- A row's category label. -/
def categoryOf : String → Option PhiFeature
  | "obv" => some .anim
  | "prox" => some .prox
  | "1" => some .part
  | "2" => some .addr
  | _ => none

/-- A row's role label. -/
def roleLabel : String → Option Role
  | "ea" => some .ea
  | "ia" => some .ia
  | _ => none

/-- A probe on C fits the LDA judgments when each row in the base word order is acceptable
exactly if LDA can target its argument. -/
def FitsRows (c : Spec Feature) : Prop :=
  ∀ row ∈ Examples.all, row.feature? "order" = none ∨ row.feature? "order" = some "PROX V OBV" →
    ∀ ea ∈ (row.feature? "ea").bind categoryOf, ∀ ia ∈ (row.feature? "ia").bind categoryOf,
      ∀ r ∈ (row.feature? "lda").bind roleLabel, (row.judgment = .acceptable ↔ CanTarget c ea ia r)

instance : DecidablePred FitsRows := fun _ ↦ by unfold FitsRows; infer_instance

/-- The mixed probe (32) fits every judgment. -/
theorem fitsRows_cEpp : FitsRows cEpp := by decide +kernel

/-- A φ-probe on C does not fit the rows, since a local patient would block LDA, against (12), (13),
(15) and (18). -/
theorem not_fitsRows_phiEpp : ¬ FitsRows phiEpp := by decide +kernel

/-- A δ-probe on C reaches past the proximate in Spec,IP, so LDA could target the obviative
patient that (10) excludes. -/
theorem not_fitsRows_deltaEpp : ¬ FitsRows deltaEpp := by decide +kernel

theorem canTarget_deltaEpp_obviative : CanTarget deltaEpp .prox .anim .ia := by decide +kernel

/-- The category and role of a row's LDA target. -/
def targetOf (row : Datum) : Option (PhiFeature × Role) := do
  let r ← (row.feature? "lda").bind roleLabel
  let f ← (row.feature? (if r = .ea then "ea" else "ia")).bind categoryOf
  pure (f, r)

/-- A proximate patient is an LDA target under an obviative agent (11a) but not under a first-person
agent (16b) (section 4, against [lesourd-2019]). -/
theorem target_eq_ex_11a_ex_16b :
    targetOf Examples.ex_11a = targetOf Examples.ex_16b ∧
      Examples.ex_11a.judgment ≠ Examples.ex_16b.judgment := by
  decide +kernel

theorem not_factorsThrough_category_role :
    ¬ Function.FactorsThrough
      (fun q : PhiFeature × PhiFeature × Role ↦ CanTarget cEpp q.1 q.2.1 q.2.2)
      (fun q ↦ (q.2.2, if q.2.2 = .ea then q.1 else q.2.1)) := by
  intro h
  have := @h (.anim, .prox, .ia) (.part, .prox, .ia) rfl
  exact absurd ((eq_iff_iff.1 this).1 (by decide +kernel)) (by decide +kernel)

end HammerlyMathieu2026
