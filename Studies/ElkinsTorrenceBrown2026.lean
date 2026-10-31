module

public import Linglib.Data.Examples.ElkinsTorrenceBrown2026
public import Linglib.Fragments.Mayan.Mam.Extraction
public import Linglib.Fragments.Mayan.Kiche.Extraction
public import Linglib.Fragments.Mayan.Kaqchikel.Extraction
public import Linglib.Syntax.Minimalist.Clause.Spine
public import Linglib.Syntax.Minimalist.Verbal.Voice
public import Linglib.Syntax.Minimalist.Feature.Valuation
public import Linglib.Morphology.DistributedMorphology.VocabularyInsertion.Basic
public import Linglib.Data.Examples.Readers

/-!
# Elkins, Torrence and Brown (2026): Wh-movement paths and adjunct extraction in Mam

The movement enclitic =(y)a' of San Juan Ostuncalco Mam optionally appears on the predicate,
and on any directional auxiliary, when an instrument, benefactive, dative, locative, reason,
purpose or manner adjunct is extracted, but not with absolutive or ergative arguments, Aissen's
Ergative Extraction Constraint sending the agent through an antipassive, and not with temporals.
The enclitic may occur once per Voice⁰ and Dir⁰ of a clause and, in long-distance extraction,
once per clause along the dependency: in the embedded clause exactly when that clause is at least
VoiceP-sized, so on both predicates over a full CP or an aspectless VoiceP complement, on the
matrix predicate only over a nonfinite VP complement, and on the embedded predicate only in an
embedded question. Elkins, Torrence and Brown analyse the enclitic as the spellout of
Ā-agreement between the extracted adjunct and the [Ā]-bearing heads Voice⁰ and Dir⁰ it passes
through under the Relativized-Minimality successive cyclicity of Rizzi and Abels: Attract Closest
forces the mover through the specifier of each intervening [Ā]-bearer, each Voice⁰ or Dir⁰ copies
the [obl] Case feature the mover receives from its relational noun, and the bundle [Ā, obl] is
realized as =(y)a' or as ∅. Mendes and Ranero's rival Chain Reduction via Substitution for the
K'ichean fronting particle *wi*, which spells out lower copies at the base position and at each
Spec,CP stopover and so derives the Fronting Particle Generalization, predicts a single reflex
within a clause, none in the matrix clause over an aspectless complement, and one inside a
nonfinite complement, all contrary to the Mam data; Keine and Zeijlstra's DP-intervention
leapfrogging predicts at most one reflex per intervening argument, contrary to a clause with
three; and an Agent-Focus-like analysis fails because the enclitic co-occurs with the passive and
appears in every clause of the path while the antipassive is confined to the clause of origin.
The two systems also differ in which adjuncts trigger the reflex: reasons, purposes and manners
do in Mam but are high adjuncts without [appl] in K'ichean, and temporals trigger neither.

## Implementation notes

* Clause sizes are `ClauseSpine`s, the Mam finite, aspectless and nonfinite clauses of (8) and
  §3.3–3.4, with the directional head `Head.dir`, a Mayan-specific category above VoiceP, spliced
  in by `spine`. A dependency is the list of clauses the mover crosses, bottom-up; its `path` is
  the [Ā]-bearers of those clauses and its `sites` the Voice and Dir heads among them, so the
  reflex in a clause is decided by whether the clause projects Voice (`licensed_iff_mem_voice`).
  The rival mechanisms are predicates on the same dependencies, and the rows discriminate them.
* The Agree-and-insertion step is the substrate's `applyAgree` and `subsetPrinciple` over the
  valued features of a Voice head with an unvalued [oblique] probe and the vocabulary item (46a);
  the null exponent (46b) is the independent optionality of each site, `patterns`.
* [obl] on the movers is the article's featural hypothesis (§1.3, §4.2, §5.3): relational nouns
  assign it, the locative and manner wh-words are assumed to acquire it, temporals lack it.
* The examples are `Data.Examples.ElkinsTorrenceBrown2026`; the K'ichean rows are Mendes and
  Ranero's as reported there, and the article's (64), headed K'iche' in the preprint, is Patzún
  Kaqchikel (Mendes and Ranero's (14a), as the article's own (68) records). The variety is SJO
  Mam; Scott's San Juan Atitán Mam is a distinct variety.

## References

* [elkins-torrence-brown-2026]
* [mendes-ranero-2021]
* [rizzi-1990]
* [abels-2003]
* [keine-zeijlstra-2025]
* [van-urk-2018]
* [scott-2023]
* [england-1989]
* [aissen-2017b]
-/

@[expose] public section

namespace ElkinsTorrenceBrown2026

open Minimalist DistributedMorphology ElkinsTorrenceBrown2026.Examples

/-! ### The extended verbal domain (§1.3) -/

/-- A head of the SJO Mam clausal spine is a head of the substrate spine or the directional
auxiliary Dir⁰, the Mayan-specific head whose projection dominates VoiceP (8). -/
inductive Head
  | cat (c : Cat)
  | dir
  deriving DecidableEq, Repr

/-- A clause as its projected heads, bottom-up. -/
abbrev Spine := List Head

/-- A clause of the given size with `n` directionals above Voice (8). Nonfinite clauses, which lack
Voice, lack directionals (§3.4). -/
def spine (s : ClauseSpine) (n : ℕ) : Spine :=
  s.heads.flatMap fun c ↦
    if c = .Voice then .cat .Voice :: List.replicate n .dir else [.cat c]

/-- The Mam finite clause of (8), a CP over the aspect layer, Voice, v and V. -/
def finiteClause : ClauseSpine := ⟨[.V, .v, .Voice, .Asp, .C]⟩

/-- The aspectless clause, a VoiceP-sized reduced clause without the aspect layer or C (§3.3). -/
def aspectlessClause : ClauseSpine := ⟨[.V, .v, .Voice]⟩

/-- The nonfinite clause, a VP-sized complement (§3.4). -/
def nonfiniteClause : ClauseSpine := ⟨[.V]⟩

/-- The reduced K'ichean complement of [mendes-ranero-2021], an AspP without a CP layer (§5.1). -/
def aspP : ClauseSpine := ⟨[.V, .v, .Voice, .Asp]⟩

/-- C⁰, Voice⁰ and Dir⁰ bear [Ā], (41) and (44). -/
def BearsA (h : Head) : Prop := h = .cat .C ∨ h = .cat .Voice ∨ h = .dir

instance : DecidablePred BearsA := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _ ∨ _))

/-- Voice⁰ and Dir⁰ copy the mover's [obl] and host the reflex, (45)–(46), while C⁰ attracts by
[Ā] alone, so there is no C-domain reflex. -/
def HostsReflex (h : Head) : Prop := h = .cat .Voice ∨ h = .dir

instance : DecidablePred HostsReflex := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

theorem HostsReflex.bearsA {h : Head} (hh : HostsReflex h) : BearsA h := Or.inr hh

/-! ### The movement path (§4.1–4.3) -/

/-- A dependency is the list of clauses the extracted adjunct crosses, bottom-up, the clause of
origin first. -/
abbrev Dependency := List Spine

/-- The movement path of (43) is the list of [Ā]-bearing heads of the clauses crossed, bottom-up
and tagged by clause. By Attract Closest (39) the mover stops in the specifier of each. -/
def path (d : Dependency) : List (ℕ × Head) :=
  (List.range d.length).flatMap fun i ↦
    ((d.getD i []).filter fun h ↦ decide (BearsA h)).map (i, ·)

/-- The sites of the reflex are the Agree relations with Voice⁰ or Dir⁰ along the path (§4.2). -/
def sites (d : Dependency) : List (ℕ × Head) :=
  (path d).filter fun p ↦ decide (HostsReflex p.2)

/-- =(y)a' is licensed in clause `i` of the dependency when the path has a site there. -/
def Licensed (d : Dependency) (i : ℕ) : Prop := i ∈ (sites d).map Prod.fst

instance (d : Dependency) (i : ℕ) : Decidable (Licensed d i) :=
  inferInstanceAs (Decidable (_ ∈ _))

theorem mem_path {d : Dependency} {i : ℕ} {h : Head} :
    (i, h) ∈ path d ↔ i < d.length ∧ h ∈ d.getD i [] ∧ BearsA h := by
  simp only [path, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_filter,
    decide_eq_true_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨j, hj, h', ⟨hmem, hb⟩, rfl, rfl⟩
    exact ⟨hj, hmem, hb⟩
  · rintro ⟨hi, hmem, hb⟩
    exact ⟨i, hi, h, ⟨hmem, hb⟩, rfl, rfl⟩

theorem licensed_iff {d : Dependency} {i : ℕ} :
    Licensed d i ↔ ∃ h ∈ d.getD i [], HostsReflex h := by
  simp only [Licensed, sites, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨j, h⟩, ⟨hp, hh⟩, rfl⟩
    exact ⟨h, (mem_path.mp hp).2.1, hh⟩
  · rintro ⟨h, hmem, hh⟩
    refine ⟨(i, h), ⟨mem_path.mpr ⟨?_, hmem, hh.bearsA⟩, hh⟩, rfl⟩
    by_contra hlt
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hlt)] at hmem
    exact List.not_mem_nil hmem

theorem exists_hostsReflex_spine_iff (s : ClauseSpine) (n : ℕ) :
    (∃ h ∈ spine s n, HostsReflex h) ↔ .Voice ∈ s := by
  simp only [spine, List.mem_flatMap, ClauseSpine.mem_def]
  constructor
  · rintro ⟨h, ⟨c, hc, hmem⟩, hh⟩
    split at hmem
    · next hcv => exact hcv ▸ hc
    · next hcv =>
      rw [List.mem_singleton] at hmem
      rcases hh with rfl | rfl
      · exact absurd (Head.cat.inj hmem).symm hcv
      · exact Head.noConfusion hmem
  · intro hv
    exact ⟨.cat .Voice, ⟨.Voice, hv, by simp⟩, Or.inl rfl⟩

/-- =(y)a' is licensed in a clause of the dependency iff that clause projects Voice (Table 3,
§3.3–3.4, §4.3). -/
theorem licensed_iff_mem_voice {d : Dependency} {i : ℕ} {s : ClauseSpine} {n : ℕ}
    (hd : d.getD i [] = spine s n) : Licensed d i ↔ .Voice ∈ s := by
  rw [licensed_iff, hd, exists_hostsReflex_spine_iff]

/-! ### Multiple exponence (§3.1, §5.2) -/

-- (45)
theorem sites_monoclausal (n : ℕ) :
    sites [spine finiteClause n] = (0, .cat .Voice) :: List.replicate n (0, .dir) := by
  simp [sites, path, spine, finiteClause, BearsA, HostsReflex, List.map_replicate]

theorem sites_monoclausal_length (n : ℕ) : (sites [spine finiteClause n]).length = n + 1 := by
  rw [sites_monoclausal]
  simp

/-- In (46b) each site is independently realized as =(y)a' or as ∅, so the surface patterns of a
dependency are the sublists of its sites. -/
def patterns (d : Dependency) : List (List (ℕ × Head)) := (sites d).sublists

-- (22)
theorem patterns_length_22 : (patterns [spine finiteClause 1]).length = 4 := by decide

-- (63), §5.2 [keine-zeijlstra-2025]
theorem sites_exceed_interveners : 1 < (sites [spine finiteClause 2]).length := by
  rw [sites_monoclausal_length]
  decide

/-! ### The rival mechanisms (§3.6, §5.1) -/

/-- Under Chain Reduction via Substitution (55)–(57), the reflex spells out the lower copies of the
mover, the base copy in the clause of origin and the intermediate copy in each Spec,CP crossed,
which linearizes onto the predicate of the next clause up. -/
def CopyLicensed (d : Dependency) (i : ℕ) : Prop :=
  i = 0 ∨ (0 < i ∧ i < d.length ∧ .cat .C ∈ d.getD (i - 1) [])

instance (d : Dependency) (i : ℕ) : Decidable (CopyLicensed d i) :=
  inferInstanceAs (Decidable (_ ∨ _ ∧ _ ∧ _))

-- (54)
theorem fpg (e m : Spine) : CopyLicensed [e, m] 1 ↔ .cat .C ∈ e := by
  simp [CopyLicensed]

-- §3.1, §5.1
theorem copy_single_site (n : ℕ) : (∀ i, CopyLicensed [spine finiteClause n] i → i = 0) ∧
    (sites [spine finiteClause n]).length = n + 1 :=
  ⟨fun i h ↦ h.elim id fun h' ↦ by
    have h1 := h'.1
    have h2 := h'.2.1
    simp only [List.length_singleton] at h2
    omega, sites_monoclausal_length n⟩

-- (31)
theorem copy_fails_aspectless :
    ¬ CopyLicensed [spine aspectlessClause 0, spine finiteClause 0] 1 ∧
      Licensed [spine aspectlessClause 0, spine finiteClause 0] 1 := by
  decide

-- (34)
theorem copy_fails_nonfinite :
    CopyLicensed [spine nonfiniteClause 0, spine finiteClause 0] 0 ∧
      ¬ Licensed [spine nonfiniteClause 0, spine finiteClause 0] 0 := by
  decide

-- (53)
theorem agree_fails_fpg :
    Licensed [spine aspP 0, spine finiteClause 0] 1 ∧
      ¬ CopyLicensed [spine aspP 0, spine finiteClause 0] 1 := by
  decide

-- (24), (38)
theorem origin_only_fails :
    Licensed [spine finiteClause 0, spine finiteClause 0] 1 ∧ (1 : ℕ) ≠ 0 := by
  decide

/-! ### Which movers trigger the reflex (§2, §5.3) -/

/-- The extracted element, if any, is an absolutive or an ergative argument, a dative, the
recipient that a relational noun introduces (§2.2.2), or an adjunct. -/
inductive Mover
  | none
  | absolutive
  | ergative
  | dative
  | adjunct (a : Mayan.Adjunct)
  deriving DecidableEq, Fintype

/-- By the article's featural hypothesis ((9), footnotes 3 and 12, §5.3), a dative and every
adjunct but the temporals bear the [obl] Case feature that Voice⁰ and Dir⁰ copy, while
absolutives and ergatives lack it (§4.2). -/
def Mover.BearsObl : Mover → Prop
  | .dative => True
  | .adjunct a => a ≠ .temporal
  | .none | .absolutive | .ergative => False

instance : DecidablePred Mover.BearsObl
  | .dative => inferInstanceAs (Decidable True)
  | .adjunct a => inferInstanceAs (Decidable (a ≠ _))
  | .none | .absolutive | .ergative => inferInstanceAs (Decidable False)

/-- [mendes-ranero-2021]'s low movers, the dative and the instrument, benefactive and locative
adjuncts, are merged in Spec,ApplP with [appl], which alone triggers *wi* (§5.3). -/
def Mover.IsLow : Mover → Prop
  | .dative => True
  | .adjunct a => a = .instrument ∨ a = .benefactive ∨ a = .locative
  | .none | .absolutive | .ergative => False

instance : DecidablePred Mover.IsLow
  | .dative => inferInstanceAs (Decidable True)
  | .adjunct _ => inferInstanceAs (Decidable (_ ∨ _ ∨ _))
  | .none | .absolutive | .ergative => inferInstanceAs (Decidable False)

-- Table 4
theorem table4 (m : Mover) :
    ¬ (m.BearsObl ↔ m.IsLow) ↔
      m = .adjunct .reason ∨ m = .adjunct .purpose ∨ m = .adjunct .manner := by
  decide +revert

/-- The reflex is realizable in clause `i` when the mover bears [obl] and the path has a site
there. -/
def Realizable (m : Mover) (d : Dependency) (i : ℕ) : Prop := m.BearsObl ∧ Licensed d i

instance (m : Mover) (d : Dependency) (i : ℕ) : Decidable (Realizable m d i) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- An extracted argument is absolutive unless it is the transitive subject, which the
antipassive demotes, or the recipient, a dative; an extracted adjunct is that adjunct. -/
def Mover.ofSite : Mayan.ExtractionSite → Mover
  | .argument .A => .ergative
  | .argument .R => .dative
  | .argument _ => .absolutive
  | .adjunct a => .adjunct a

theorem realizable_iff_mem_realize (s : Mayan.ExtractionSite) :
    Realizable (.ofSite s) [spine finiteClause 0] 0 ↔
      Reflex.morpheme .verbalComplex [Mam.Extraction.movementEnclitic] ∈
        Mam.Extraction.realize s := by
  decide +revert

-- §5.1, §5.3
theorem kiche_mem_realize_iff (c : Mayan.VerbClass) (s : Mayan.ExtractionSite) :
    Reflex.morpheme .verbalComplex [Kiche.Extraction.wi] ∈ Kiche.Extraction.realize c s ↔
      (Mover.ofSite s).IsLow := by
  decide +revert

-- (51), (64)
theorem kaqchikel_realize_eq_kiche (c : Mayan.VerbClass) (agent patient : Person)
    {s : Mayan.ExtractionSite} (hs : s ≠ .argument .A) :
    Kaqchikel.Extraction.realize c agent patient s = Kiche.Extraction.realize c s := by
  rcases s with (_ | _ | _ | _ | _) | (_ | _ | _ | _ | _ | _ | _) <;>
    first | rfl | exact absurd rfl hs

/-! ### Agree and insertion (§4.2) -/

/-- Voice⁰ of the analysis is an [Ā]-bearing head with an unvalued [oblique] probe that Agree with
the mover values, (45a). -/
def voice : Voice.Head :=
  { Voice.agentive with features := .ofList [⟨.oblique, .unvalued⟩] }

/-- The vocabulary item (46a) realizes the valued [obl] on Voice⁰ or Dir⁰. -/
def eqYa : VocabularyItem FeatureVal String :=
  {⟨.oblique, true⟩} ⟷ toString Mam.Extraction.movementEnclitic

theorem agree_spellout :
    (voice.features.applyAgree (.single .oblique true) .oblique).map
      (fun b ↦ subsetPrinciple [eqYa] (b.valued.toFinset : Finset FeatureVal)) =
        ↑(some "=(y)a'") := by
  decide

theorem no_obl_no_agree : voice.features.applyAgree ⊥ .oblique = voice.features :=
  FeatureBundle.applyAgree_bot _ _

/-! ### The rows (§2, §3, §5) -/

/-- The movers as named in the rows. -/
def moverTable : List (String × Mover) :=
  [("none", .none), ("absolutive", .absolutive), ("ergative", .ergative),
    ("instrument", .adjunct .instrument), ("benefactive", .adjunct .benefactive),
    ("dative", .dative), ("locative", .adjunct .locative), ("reason", .adjunct .reason),
    ("purpose", .adjunct .purpose), ("manner", .adjunct .manner), ("temporal", .adjunct .temporal)]

/-- Whether the reflex may appear, as recorded in the rows. -/
def reflexTable : List (String × Bool) := [("licensed", true), ("blocked", false)]

-- §2, §3.5
theorem mamRows_realizable :
    ∀ e ∈ [ex_10b, ex_11b, ex_12b, ex_13a, ex_13b, ex_14b, ex_15b, ex_16b, ex_17b, ex_18b,
        ex_19b, ex_20b, ex_21b, ex_35c, ex_37, ex_65],
      ∀ m, e.parse? "mover" moverTable = some m →
        ∀ b, e.parse? "reflex" reflexTable = some b →
        (b = true ↔ Realizable m [spine finiteClause 0] 0) := by
  decide

-- (51), (64)
theorem kicheanRows_low :
    ∀ e ∈ [ex_51, ex_64], ∀ m, e.parse? "mover" moverTable = some m →
      ∀ b, e.parse? "reflex" reflexTable = some b → (b = true ↔ m.IsLow) := by
  decide

-- (22), (63)
theorem directionalRows_sites :
    ∀ e ∈ [ex_22, ex_63], ∀ n, e.nat? "directionals" = some n →
      ∀ k, e.nat? "hosts" = some k → (sites [spine finiteClause n]).length = k := by
  decide

/-- The clause sizes as named in the rows. -/
def sizeTable : List (String × ClauseSpine) :=
  [("cP", finiteClause), ("voiceP", aspectlessClause), ("bareVP", nonfiniteClause), ("aspP", aspP)]

/-- The dependency of a long-distance row: the embedded clause and, when the wh-expression lands
in the matrix clause, the full-CP matrix clause above it. -/
def dependencyOf (e : Datum) : Option Dependency :=
  (e.parse? "embeddedSize" sizeTable).bind fun s ↦
    e.parse? "landing" [("embedded", [spine s 0]), ("matrix", [spine s 0, spine finiteClause 0])]

-- (24), (26), (31), (34), Table 3
theorem mamLD_licensed :
    ∀ e ∈ [ex_24, ex_26, ex_31, ex_34], ∀ d, dependencyOf e = some d →
      (∀ b, e.parse? "embeddedReflex" reflexTable = some b → (b = true ↔ Licensed d 0)) ∧
        ∀ b, e.parse? "matrixReflex" reflexTable = some b → (b = true ↔ Licensed d 1) := by
  decide

-- (52), (53)
theorem kicheLD_copy :
    ∀ e ∈ [ex_52, ex_53], ∀ d, dependencyOf e = some d →
      (∀ b, e.parse? "embeddedReflex" reflexTable = some b →
          (b = true ↔ CopyLicensed d 0)) ∧
        ∀ b, e.parse? "matrixReflex" reflexTable = some b →
          (b = true ↔ CopyLicensed d 1) := by
  decide

end ElkinsTorrenceBrown2026
