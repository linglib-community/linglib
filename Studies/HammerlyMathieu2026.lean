module

public import Linglib.Syntax.Minimalist.Probe.Movement
public import Linglib.Data.Examples.HammerlyMathieu2026
public import Mathlib.Tactic.DeriveFintype

/-!
# Hammerly and Mathieu (2026): long-distance agreement in Border Lakes Ojibwe

A matrix verb in Border Lakes Ojibwe agrees with the embedded argument in Spec,CP, and probes on
Voice, Infl and C with conditions on agreement and on movement decide which argument gets there.
Plain Voice moves a local patient into a second specifier, making the arguments equidistant, and
C's φ ∨ δ probe then moves the one bearing δ, by Best Match. So LDA is free when the patient is
local, agent-only under a local agent and a third person patient, and highest-ranked between third
persons.

## Main definitions

* `HammerlyMathieu2026.merge`: a head's Agree and movement over its domain.
* `HammerlyMathieu2026.target`: the argument C's probe moves to Spec,CP.

## Main results

* `target_direct`, `target_inverse`, `canTarget_local`, `canTarget_localAgent`,
  `canTarget_localPatient`: the pattern (19).
* `fitsRows_cEpp`, `not_fitsRows_phiEpp`, `not_fitsRows_deltaEpp`: of the probes on C in (31)
  and (32), only the mixed one fits the judgments.
* `target_inverse_plain`: LDA in the deep inverse does not need ergative Voice.
* `canTargetOptional_iff`: optional movement of tied goals, fn. 8, gives the same pattern.
* `target_eq_ex_11a_ex_16b`: LDA is not fixed by the target's category and role.

## Implementation notes

* An interaction specification [f] is `closure f`, while Best Match counts satisfaction
  conditions as listed. A head bears the union of what it copied; Agree's bundles, one per goal,
  are `interacted` mapped by `intFeatures`.
* The rows are coded as Glottolog's Rainy River Ojibwa, the dialect around Fort Frances, where the
  speakers consulted are from; Glottolog has no Border Lakes languoid.
* Theme signs and Infl's impoverishment are not modelled.

## TODO

* Without Voice's [PART] movement probe the local and mixed configurations should show agent LDA,
  the restricted pattern section 4 discusses.
* A single condition set per probe, which fn. 6 says suffices, should give the same pattern.

## References

* [hammerly-mathieu-2026]
* [oxford-2019]
* [oxford-2023]
* [lesourd-2019]
* [deal-2024]
-/

@[expose] public section

namespace HammerlyMathieu2026

open Minimalist Probe

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
  deriving DecidableEq, Repr

/-- The φ-features as features. -/
def Feature.ofPhi : PhiFeature ↪ Feature := ⟨.phi, fun _ _ ↦ Feature.phi.inj⟩

/-- The features of a nominal whose category is `f`, the φ-features `f` contains (22). -/
def phiFeatures (f : PhiFeature) : Finset Feature := (Finset.univ.filter (· ≤ f)).map Feature.ofPhi

@[simp] theorem mem_phiFeatures {f g : PhiFeature} : Feature.phi g ∈ phiFeatures f ↔ g ≤ f := by
  simp [phiFeatures, Feature.ofPhi]

@[simp] theorem delta_not_mem_phiFeatures (f : PhiFeature) : Feature.delta ∉ phiFeatures f := by
  simp [phiFeatures, Feature.ofPhi]

/-- [f] in an interaction specification, `f` and the φ-features it dominates, the convention of
[deal-2024], so that a probe interacting with [φ] copies every φ-feature of its goal. -/
def closure (f : PhiFeature) : Finset Feature := (Finset.univ.filter (f ≤ ·)).map Feature.ofPhi

@[simp] theorem mem_closure {f g : PhiFeature} : Feature.phi g ∈ closure f ↔ f ≤ g := by
  simp [closure, Feature.ofPhi]

/-- The probe relativized to `f`, [INT:{f}, SAT:{f}]. -/
def relativizedTo (f : PhiFeature) : Spec Feature := ⟨closure f, {.phi f}⟩

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

/-- A goal of the probes: an argument in its role, active unless inherent case has deactivated
it, or a head bearing the features it copied, which a higher probe can Agree with, after
[oxford-2023]. -/
inductive Goal where
  | arg (r : Role) (x : Arg) (active : Bool := true)
  | head (copied : Finset Feature)
  deriving DecidableEq

/-- The features a goal exposes to a probe, none for a deactivated argument. -/
def Goal.features : Goal → Finset Feature
  | .arg _ x active => if active then x.features else ∅
  | .head s => s

/-- The role of a goal that is an argument. -/
def Goal.role? : Goal → Option Role
  | .arg r .. => some r
  | .head _ => none

/-- The arguments of a domain, the goals a movement probe searches, since only nominals move
(section 3.5.1). -/
def nominals (d : List (List Goal)) : List (List Goal) := d.map (·.filter (·.role?.isSome))

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

/-- The agent as Voice's specifier, deactivated by the inherent case ergative Voice assigns. -/
def Voice.agent (v : Voice) (x : Arg) : Goal := .arg .ea x (v == .plain)

/-- The agreement probe of Infl (24), [INT:{φ}, SAT:{PROX}]. -/
def inflAgr : Spec Feature := ⟨closure .phi, {.phi .prox}⟩

/-- The movement probe of Infl (24), [INT:{PROX}, SAT:{PROX}]. -/
def inflEpp : Spec Feature := relativizedTo .prox

/-- C's pure φ-probe, of agent and highest-ranked LDA (31b, c). -/
def phiEpp : Spec Feature := relativizedTo .phi

/-- C's pure δ-probe, of free LDA (31a). -/
def deltaEpp : Spec Feature := ⟨{.delta}, {.delta}⟩

/-- The movement probe of C (25), (32), [INT:{φ ∨ δ}, SAT:{φ ∨ δ}], the join of the φ-probe and the
δ-probe, so that a goal bearing both matches better than a goal bearing one. -/
def cEpp : Spec Feature := phiEpp ⊔ deltaEpp

/-! ### The derivation -/

/-- The domain after a head that Agrees by `agr` over `d`, has specifiers `specs` and attracts
`moved`: a new closest class, the head bearing what it copied, the attracted goal as its outer
specifier and `specs`, all equidistant, over the classes of `d`, which the attracted goal leaves. -/
def extend (agr : Spec Feature) (specs : List Goal) (d : List (List Goal)) (moved : Option Goal) :
    List (List Goal) :=
  (.head (agr.copied Goal.features d) :: moved.toList ++ specs) ::
    d.map fun c ↦ moved.elim c c.erase

/-- A head merging over a domain of equidistance classes, closest first: it Agrees by `agr` and
attracts an argument by `epp`. -/
def merge (agr epp : Spec Feature) (specs : List Goal) (d : List (List Goal)) : List (List Goal) :=
  extend agr specs d (epp.attract Goal.features (nominals d))

/-- An embedded transitive clause. -/
structure Clause where
  /-- The agent. -/
  ea : Arg
  /-- The patient. -/
  ia : Arg
  deriving DecidableEq, Repr

/-- The deep inverse, an obviative agent acting on a proximate patient. -/
def Clause.IsDeepInverse (x : Clause) : Prop := x.ea.phi = .anim ∧ x.ia.phi = .prox

instance : DecidablePred Clause.IsDeepInverse := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- The Voice of a clause, ergative in the deep inverse, the one configuration considered in which
it converges, and plain otherwise ([oxford-2023]). -/
def Clause.voice (x : Clause) : Voice := if x.IsDeepInverse then .ergative else .plain

/-- The vP, the patient in Spec,vP. -/
def vP (x : Clause) : List (List Goal) := [[.arg .ia x.ia]]

/-- The VoiceP of Voice `v`, the agent its specifier. -/
def voiceP (v : Voice) (x : Clause) : List (List Goal) := merge v.agr v.epp [v.agent x.ea] (vP x)

/-- The IP over the VoiceP of Voice `v`. -/
def inflP (v : Voice) (x : Clause) : List (List Goal) := merge inflAgr inflEpp [] (voiceP v x)

/-- The argument a probe `c` on C moves to Spec,CP over the VoiceP of Voice `v`, and so the
target of LDA. -/
def target (c : Spec Feature) (v : Voice) (x : Clause) : Option Role :=
  (c.attract Goal.features (nominals (inflP v x))).bind Goal.role?

/-- The clause of an agent and a patient of categories `ea` and `ia`, bearing δ as `δe` and
`δi` say. -/
abbrev clause (ea ia : PhiFeature) (δe δi : Bool) : Clause := ⟨⟨ea, δe⟩, ⟨ia, δi⟩⟩

/-- LDA with a probe `c` on C can target the argument of role `r` in a clause whose agent and
patient have categories `ea` and `ia`, for some placement of δ. -/
def CanTarget (c : Spec Feature) (ea ia : PhiFeature) (r : Role) : Prop :=
  ∃ δe δi : Bool, target c (clause ea ia δe δi).voice (clause ea ia δe δi) = some r

instance (c : Spec Feature) (ea ia : PhiFeature) (r : Role) : Decidable (CanTarget c ea ia r) :=
  inferInstanceAs (Decidable (∃ _ _, _))

/-! ### The derivations (26) to (30), with no δ -/

/-- An argument without δ. -/
abbrev bare (f : PhiFeature) : Arg := ⟨f, false⟩

/-- (26): Voice Agrees with the obviative patient and leaves it in place. -/
theorem voiceP_26 :
    voiceP .plain ⟨bare .prox, bare .anim⟩ =
      [[.head (phiFeatures .anim), .arg .ea (bare .prox)], [.arg .ia (bare .anim)]] := by
  decide

/-- (26): Infl Agrees with and moves the proximate agent. -/
theorem inflP_26 :
    inflP .plain ⟨bare .prox, bare .anim⟩ =
      [[.head (phiFeatures .prox), .arg .ea (bare .prox)], [.head (phiFeatures .anim)],
        [.arg .ia (bare .anim)]] := by
  decide

/-- (27): ergative Voice copies nothing, so its theme sign is the elsewhere form, the inverse
([oxford-2019]), and moves the proximate patient over its agent. -/
theorem voiceP_27 :
    voiceP .ergative ⟨bare .anim, bare .prox⟩ =
      [[.head ∅, .arg .ia (bare .prox), .arg .ea (bare .anim) false], []] := by
  decide

/-- (27): Infl Agrees with and moves the proximate patient. -/
theorem inflP_27 :
    inflP .ergative ⟨bare .anim, bare .prox⟩ =
      [[.head (phiFeatures .prox), .arg .ia (bare .prox)], [.head ∅, .arg .ea (bare .anim) false],
        []] := by
  decide

/-- (28): Voice Agrees with the second person patient and moves it into a second specifier. -/
theorem voiceP_28 :
    voiceP .plain ⟨bare .part, bare .addr⟩ =
      [[.head (phiFeatures .addr), .arg .ia (bare .addr), .arg .ea (bare .part)], []] := by
  decide

/-- (28): Infl Agrees with Voice and both equidistant arguments, Multiple Agree. -/
theorem inflAgr_interacted_28 :
    inflAgr.interacted Goal.features (voiceP .plain ⟨bare .part, bare .addr⟩) =
      [.head (phiFeatures .addr), .arg .ia (bare .addr), .arg .ea (bare .part)] := by
  decide

/-- (28): Infl moves neither equidistant argument, the Ban on Multiple Move. -/
theorem inflEpp_attract_28 :
    inflEpp.attract Goal.features (nominals (voiceP .plain ⟨bare .part, bare .addr⟩)) = none := by
  decide

/-- (29): Voice leaves the proximate patient in place, and Infl Agrees with Voice, which bears the
patient's features, and with the local agent, the portmanteau of [1SG] and [3SG]. -/
theorem inflAgr_bundles_29 :
    (inflAgr.interacted Goal.features (voiceP .plain ⟨bare .part, bare .prox⟩)).map
        (inflAgr.intFeatures Goal.features) =
      [phiFeatures .prox, phiFeatures .part] := by
  decide

/-- (29): Infl moves the local agent. -/
theorem inflP_29 :
    inflP .plain ⟨bare .part, bare .prox⟩ =
      [[.head (phiFeatures .part), .arg .ea (bare .part)], [.head (phiFeatures .prox)],
        [.arg .ia (bare .prox)]] := by
  decide

/-- (30): Voice moves the first person patient into a second specifier. -/
theorem voiceP_30 :
    voiceP .plain ⟨bare .prox, bare .part⟩ =
      [[.head (phiFeatures .part), .arg .ia (bare .part), .arg .ea (bare .prox)], []] := by
  decide

/-- (30): Infl Agrees with Voice and both equidistant arguments. -/
theorem inflAgr_interacted_30 :
    inflAgr.interacted Goal.features (voiceP .plain ⟨bare .prox, bare .part⟩) =
      [.head (phiFeatures .part), .arg .ia (bare .part), .arg .ea (bare .prox)] := by
  decide

/-- (30): Infl moves neither argument. -/
theorem inflEpp_attract_30 :
    inflEpp.attract Goal.features (nominals (voiceP .plain ⟨bare .prox, bare .part⟩)) = none := by
  decide

/-- Plain Voice moves the patient iff it is a local person, the relativized EPP. -/
theorem voice_epp_attract_iff :
    ∀ (f : PhiFeature) (δ : Bool),
      Voice.plain.epp.attract Goal.features (nominals (vP ⟨bare .phi, ⟨f, δ⟩⟩)) =
          some (.arg .ia ⟨f, δ⟩) ↔ .part ≤ f := by
  decide

/-! ### The pattern (19) -/

/-- (19a-i): with a proximate agent and an obviative patient, LDA targets the agent, wherever δ
is. -/
theorem target_direct : ∀ δe δi, target cEpp .plain (clause .prox .anim δe δi) = some .ea := by
  decide

/-- (19a-ii): in the deep inverse LDA targets the proximate patient, wherever δ is. -/
theorem target_inverse :
    ∀ δe δi, target cEpp .ergative (clause .anim .prox δe δi) = some .ia := by
  decide

/-- (19b): between local persons LDA can target either argument. -/
theorem canTarget_local :
    ∀ r, CanTarget cEpp .part .addr r ∧ CanTarget cEpp .addr .part r := by
  decide

/-- (19c-i): a local agent acting on a proximate patient is the only possible target. -/
theorem canTarget_localAgent :
    ∀ ea, .part ≤ ea → ∀ r, (CanTarget cEpp ea .prox r ↔ r = .ea) := by
  decide

/-- (19c-ii): a proximate agent acting on a local patient leaves LDA free. -/
theorem canTarget_localPatient : ∀ ia, .part ≤ ia → ∀ r, CanTarget cEpp .prox ia r := by
  decide

/-- In the nonlocal configurations the proximate argument is higher than the obviative one, as
the order PROX V OBV of (9) and (11) requires; the verb's position is not modelled. -/
theorem nominals_inflP_nonlocal :
    ∀ δe δi : Bool,
      (nominals (inflP .plain (clause .prox .anim δe δi))).flatten =
          [.arg .ea ⟨.prox, δe⟩, .arg .ia ⟨.anim, δi⟩] ∧
        (nominals (inflP .ergative (clause .anim .prox δe δi))).flatten =
          [.arg .ia ⟨.prox, δi⟩, .arg .ea ⟨.anim, δe⟩ false] := by
  decide

/-- With plain Voice the deep inverse yields the same target and order: Infl skips the obviative
agent, which lacks [PROX], and moves the patient. So LDA does not need ergative Voice; its
theme sign does, since plain Voice would copy the patient's features (`voiceP_27`). -/
theorem target_inverse_plain :
    ∀ δe δi, target cEpp .plain (clause .anim .prox δe δi) = some .ia ∧
      (nominals (inflP .plain (clause .anim .prox δe δi))).flatten =
        [.arg .ia ⟨.prox, δi⟩, .arg .ea ⟨.anim, δe⟩] := by
  decide

/-- Plain Voice in the deep inverse would Agree with the proximate patient. -/
theorem voiceP_plain_inverse :
    voiceP .plain ⟨bare .anim, bare .prox⟩ =
      [[.head (phiFeatures .prox), .arg .ea (bare .anim)], [.arg .ia (bare .prox)]] := by
  decide

/-! ### The judgments, and the typology of section 4 -/

/-- A row's category label. -/
def categoryOf : String → Option PhiFeature
  | "obv" => some .anim
  | "prox" => some .prox
  | "1" => some .part
  | "2" => some .addr
  | _ => none

/-- A row's role label. -/
def roleOf : String → Option Role
  | "ea" => some .ea
  | "ia" => some .ia
  | _ => none

/-- A probe on C fits the LDA judgments when each row in the base word order is acceptable
exactly if LDA can target its argument. -/
def FitsRows (c : Spec Feature) : Prop :=
  ∀ row ∈ Examples.all, row.feature? "order" = none ∨ row.feature? "order" = some "PROX V OBV" →
    ∀ ea ∈ (row.feature? "ea").bind categoryOf, ∀ ia ∈ (row.feature? "ia").bind categoryOf,
      ∀ r ∈ (row.feature? "lda").bind roleOf, (row.judgment = .acceptable ↔ CanTarget c ea ia r)

instance : DecidablePred FitsRows := fun _ ↦ by unfold FitsRows; infer_instance

/-- The mixed probe (32) fits every judgment. -/
theorem fitsRows_cEpp : FitsRows cEpp := by decide

/-- With Voice and Infl as they are, a φ-probe on C cannot choose between the arguments Voice
made equidistant, so a local patient would block LDA, against (12), (13), (15) and (18). -/
theorem not_fitsRows_phiEpp : ¬ FitsRows phiEpp := by decide

/-- A δ-probe on C reaches past the proximate in Spec,IP, so LDA could target the obviative
patient that (10) excludes. -/
theorem not_fitsRows_deltaEpp : ¬ FitsRows deltaEpp := by decide

/-- With δ on the obviative patient, a δ-probe on C moves it past the proximate agent. -/
theorem canTarget_deltaEpp_obviative : CanTarget deltaEpp .prox .anim .ia := by decide

/-- The category and role of a row's LDA target. -/
def targetOf (row : Datum) : Option (PhiFeature × Role) := do
  let r ← (row.feature? "lda").bind roleOf
  let f ← (row.feature? (if r = .ea then "ea" else "ia")).bind categoryOf
  pure (f, r)

/-- A proximate patient is a target of LDA under an obviative agent (11a) but not under a first
person agent (16b), so whether an argument can be targeted depends on its coargument; section 4
argues that a purely local principle selecting the matrix object, as [lesourd-2019] proposes for
Passamaquoddy, cannot express this. -/
theorem target_eq_ex_11a_ex_16b :
    targetOf Examples.ex_11a = targetOf Examples.ex_16b ∧
      Examples.ex_11a.judgment ≠ Examples.ex_16b.judgment := by
  decide

/-- The model derives the asymmetry: LDA with an argument is not a function of its category and
role. -/
theorem not_factorsThrough_category_role :
    ¬ Function.FactorsThrough
      (fun q : PhiFeature × PhiFeature × Role ↦ CanTarget cEpp q.1 q.2.1 q.2.2)
      (fun q ↦ (q.2.2, if q.2.2 = .ea then q.1 else q.2.1)) := by
  intro h
  have := @h (.anim, .prox, .ia) (.part, .prox, .ia) rfl
  exact absurd ((eq_iff_iff.1 this).1 (by decide)) (by decide)

/-! ### Optional movement, fn. 8 -/

/-- The goals a movement probe may attract when, as two reviewers suggest, a tie moves either
goal. -/
def attractOptions (epp : Spec Feature) (d : List (List Goal)) : List (Option Goal) :=
  match epp.interacted Goal.features d with
  | [] => [none]
  | l => l.map some

/-- The domains a head may leave under optional movement. -/
def mergeOptions (agr epp : Spec Feature) (specs : List Goal) (d : List (List Goal)) :
    List (List (List Goal)) :=
  (attractOptions epp (nominals d)).map (extend agr specs d)

/-- The targets of LDA under optional movement. -/
def targetsOptional (c : Spec Feature) (v : Voice) (x : Clause) : List (Option Role) :=
  let voices := mergeOptions v.agr v.epp [v.agent x.ea] (vP x)
  (voices.flatMap (mergeOptions inflAgr inflEpp [])).flatMap fun d ↦
    (attractOptions c (nominals d)).map (·.bind Goal.role?)

/-- LDA can target role `r` under optional movement. -/
def CanTargetOptional (c : Spec Feature) (ea ia : PhiFeature) (r : Role) : Prop :=
  ∃ δe δi : Bool, some r ∈ targetsOptional c (clause ea ia δe δi).voice (clause ea ia δe δi)

instance (c : Spec Feature) (ea ia : PhiFeature) (r : Role) :
    Decidable (CanTargetOptional c ea ia r) :=
  inferInstanceAs (Decidable (∃ _ _, _))

/-- Optional movement of tied goals gives the same pattern, as fn. 8 observes. -/
theorem canTargetOptional_iff :
    ∀ ea ia r, (CanTargetOptional cEpp ea ia r ↔ CanTarget cEpp ea ia r) := by
  decide

end HammerlyMathieu2026
