module

public import Linglib.Core.Relation.ReflTransGen
public import Linglib.Pragmatics.SocialMeaning.IndexicalField
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Order.Closure
public import Mathlib.Order.Iterate
public import Mathlib.Tactic.DeriveFintype

/-!
# Eckert (2008): Variation and the indexical field

This file formalizes the indexical field of [eckert-2008]. On [silverstein-2003]'s indexical
order, a first-order index marks membership in a population and every nth-order value is
available for an n + 1st reconstrual, so the paper takes the meaning of a variable to be not a
fixed category but the constellation of ideologically linked meanings that continual
reconstrual creates, any of which a situated use may activate. An ideological field records
what each meaning is available to be construed as (`IdeologicalField`), a reconstrual adds
those construals to a set of meanings, and the indexical field of a first-order index is its
closure under reconstrual, a closure operator whose closed sets are the sets no reconstrual
extends.

The examples are the paper's. [labov-1963]'s Martha's Vineyard (ay) is an indicator become a
marker. The (ING) field of Figure 3, after [campbell-kibler-2007], holds favourable and
unfavourable meanings for both variants, and a hearer expects the variant whose field holds
the impression formed of the speaker. The stances of the /t/ release field of Figure 4 accrete
into qualities, social types anchor the field, and [podesva-2007]'s diva combines the two
extremes of the articulation continuum. Among the Belten High groups of Figure 1, the burnout
girls alone are among the leaders of every variable.

## Implementation notes

Figures 3 and 4 are recorded as printed and the ideological links as the text states them; the
graded strengths of `SocialMeaning.AssociationField` are not in the paper. `Leads` marks a group
among the greatest or second-greatest users of Figure 1 and is derived from the text's two
generalizations, that girls lead the older changes and burnouts the newer. The burned-out
burnout girls, the Beijing variables of Figure 2 from [zhang-2005], Podesva's release-rate
measurements and the (DH) discussion are not represented.

## References

* [eckert-2008]
* [silverstein-2003]
* [labov-1963]
* [campbell-kibler-2007]
* [podesva-2007]
* [eckert-2000]
* [zhang-2005]
-/

@[expose] public section

namespace Eckert2008

open SocialMeaning

/-! ### Indexical order and the indexical field -/

/-- An ideological field records, for each potential meaning, the meanings it is available to
be construed as, the links along which an nth-order value acquires an n + 1st. -/
abbrev IdeologicalField (T : Type*) := T → Finset T

namespace IdeologicalField

variable {T : Type*} [DecidableEq T] (I : IdeologicalField T) {S : Finset T} {t : T}

/-- One reconstrual of `S` adds to its meanings everything they are construed as. -/
def construe (S : Finset T) : Finset T := S ∪ S.biUnion I

@[simp] theorem mem_construe : t ∈ I.construe S ↔ t ∈ S ∨ ∃ s ∈ S, t ∈ I s := by
  simp [construe]

theorem subset_construe (S : Finset T) : S ⊆ I.construe S := Finset.subset_union_left

theorem construe_mono : Monotone I.construe := λ _ _ h =>
  Finset.union_subset_union h (Finset.biUnion_subset_biUnion_of_subset_left _ h)

theorem monotone_construe_iterate (S : Finset T) : Monotone λ n => I.construe^[n] S :=
  I.construe_mono.monotone_iterate_of_le_map (I.subset_construe S)

variable [Fintype T]

/-- The indexical field of a first-order index is its closure under the ideological links,
every meaning the index is continually reconstrued as. -/
def indexicalField : ClosureOperator (Finset T) :=
  .mk₂ (λ S => Finset.univ.filter λ t => ∃ s ∈ S, Relation.ReflTransGen (λ a b => b ∈ I a) s t)
    (λ _ _ h => Finset.mem_filter.2 ⟨Finset.mem_univ _, _, h, .refl⟩)
    (λ _ _ h _ ht => by
      obtain ⟨s, hs, hst⟩ := (Finset.mem_filter.1 ht).2
      obtain ⟨u, hu, hus⟩ := (Finset.mem_filter.1 (h hs)).2
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, u, hu, hus.trans hst⟩)

@[simp] theorem mem_indexicalField :
    t ∈ I.indexicalField S ↔ ∃ s ∈ S, Relation.ReflTransGen (λ a b => b ∈ I a) s t := by
  simp [indexicalField]

theorem iterate_construe_subset_indexicalField (n : ℕ) (S : Finset T) :
    I.construe^[n] S ⊆ I.indexicalField S := by
  induction n with
  | zero => exact I.indexicalField.le_closure S
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    intro t ht
    obtain ht | ⟨s, hs, hts⟩ := I.mem_construe.1 ht
    · exact ih ht
    · obtain ⟨u, hu, hus⟩ := I.mem_indexicalField.1 (ih hs)
      exact I.mem_indexicalField.2 ⟨u, hu, hus.tail hts⟩

theorem mem_indexicalField_iff_exists_iterate :
    t ∈ I.indexicalField S ↔ ∃ n, t ∈ I.construe^[n] S := by
  refine ⟨λ h => ?_, λ ⟨n, h⟩ => I.iterate_construe_subset_indexicalField n S h⟩
  obtain ⟨s, hs, hst⟩ := I.mem_indexicalField.1 h
  clear h
  induction hst with
  | refl => exact ⟨0, hs⟩
  | tail _ hbc ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, by rw [Function.iterate_succ_apply']; exact I.mem_construe.2 (.inr ⟨_, hn, hbc⟩)⟩

theorem isClosed_iff : I.indexicalField.IsClosed S ↔ I.construe S = S := by
  rw [I.indexicalField.isClosed_iff]
  constructor
  · intro h
    refine (I.subset_construe S).antisymm' ?_
    exact (I.iterate_construe_subset_indexicalField 1 S).trans h.subset
  · intro h
    refine (I.indexicalField.le_closure S).antisymm' λ t ht => ?_
    obtain ⟨n, hn⟩ := I.mem_indexicalField_iff_exists_iterate.1 ht
    rwa [Function.iterate_fixed h] at hn

theorem indexicalField_eq_iterate {n : ℕ}
    (h : I.construe (I.construe^[n] S) = I.construe^[n] S) :
    I.indexicalField S = I.construe^[n] S :=
  ((I.indexicalField.monotone (I.monotone_construe_iterate S (Nat.zero_le n))).trans
    (I.isClosed_iff.2 h).closure_eq.le).antisymm (I.iterate_construe_subset_indexicalField n S)

end IdeologicalField

/-! ### Martha's Vineyard (ay) -/

/-- The meanings of centralized (ay) are membership among Vineyarders and the claim about what
a Vineyarder is that the fishermen made with the variant, local authenticity and opposition to
the mainland. -/
inductive VineyardMeaning
  | vineyarder
  | localAuthenticity
  | oppositionToMainland
  deriving DecidableEq, Fintype

/-- The island's ideological field makes available to the index the evaluation of Vineyarders
that the disagreements about the future of the island raised. -/
def vineyardIdeology : IdeologicalField VineyardMeaning
  | .vineyarder => {.localAuthenticity, .oppositionToMainland}
  | _ => ∅

/-- The first-order index of centralized (ay) is membership among Vineyarders. -/
def centralizedAy : Finset VineyardMeaning := {.vineyarder}

theorem vineyard_marker :
    .localAuthenticity ∉ centralizedAy ∧
      .localAuthenticity ∈ vineyardIdeology.construe centralizedAy := by
  decide

theorem indexicalField_centralizedAy :
    vineyardIdeology.indexicalField centralizedAy =
      {.vineyarder, .localAuthenticity, .oppositionToMainland} :=
  vineyardIdeology.indexicalField_eq_iterate (n := 1) (by decide)

/-! ### The (ING) field, Figure 3 -/

/-- The velar and apical variants of (ING). -/
inductive INGVariant
  | velar
  | apical
  deriving DecidableEq, Fintype

theorem INGVariant.eq_velar_or_eq_apical (u : INGVariant) : u = .velar ∨ u = .apical := by
  cases u <;> simp

/-- The potential meanings of Figure 3, the velar variant heard as educated, formal, effortful
and articulate or pretentious, the apical as uneducated, relaxed, easygoing or lazy, and
inarticulate or unpretentious. -/
inductive INGMeaning
  | educated
  | uneducated
  | formal
  | relaxed
  | effortful
  | easygoing
  | lazy
  | articulate
  | pretentious
  | inarticulate
  | unpretentious
  deriving DecidableEq, Fintype

/-- The (ING) field of Figure 3, black for the velar variant and gray for the apical. -/
def ingField : INGVariant → Finset INGMeaning
  | .velar => {.educated, .formal, .effortful, .articulate, .pretentious}
  | .apical => {.uneducated, .relaxed, .easygoing, .lazy, .inarticulate, .unpretentious}

/-- A hearer's evaluation of a meaning is favourable or unfavourable. -/
inductive Evaluation
  | favourable
  | unfavourable
  deriving DecidableEq, Fintype

/-- The text attaches evaluations to the meanings the figure pairs as alternatives, the apical
speaker heard as inarticulate or lazy or else as unpretentious or easygoing and the velar
speaker as articulate or as pretentious; the other meanings carry none. -/
def INGMeaning.evaluation : INGMeaning → Option Evaluation
  | .articulate | .unpretentious | .easygoing => some .favourable
  | .pretentious | .inarticulate | .lazy => some .unfavourable
  | _ => none

/-- A hearer's evaluation activates the region of a variant's field it evaluates that way. -/
def activate (e : Evaluation) (v : INGVariant) : Finset INGMeaning :=
  (ingField v).filter (·.evaluation = some e)

theorem activate_nonempty : ∀ e v, (activate e v).Nonempty := by decide

/-- Presupposed indexicality expects of a speaker the variants whose field holds the impression
the hearer has formed of the speaker from general style and content. -/
def expected (i : INGMeaning) : Finset INGVariant := Finset.univ.filter (i ∈ ingField ·)

theorem expected_educated_uneducated :
    expected .educated = {.velar} ∧ expected .uneducated = {.apical} := by
  decide

/-- The social moves a hearer attributes to the wrong variant. -/
inductive Move
  | pretentious
  | condescending
  | insincere
  deriving DecidableEq, Fintype, Inhabited

/-- The expected variant passes, and the wrong one is heard as pretentious, condescending or
insincere. -/
def interpret (i : INGMeaning) (v : INGVariant) : Finset Move :=
  if v ∈ expected i then ∅ else Finset.univ

theorem interpret_eq_empty_iff (i : INGMeaning) (v : INGVariant) :
    interpret i v = ∅ ↔ v ∈ expected i := by
  unfold interpret; split_ifs with h <;> simp [h, Finset.univ_nonempty.ne_empty]

theorem interpret_velar_of_uneducated : interpret .uneducated .velar = Finset.univ := by
  decide

/-! ### The /t/ release field, Figure 4 -/

/-- The stances of Figure 4, momentary and situated. -/
inductive TStance
  | formal
  | clear
  | emphatic
  | annoyed
  | angry
  | careful
  | exasperated
  | polite
  | effortful
  deriving DecidableEq, Fintype

/-- The permanent qualities of Figure 4, and the quality of habitually taking a stance, the
angry person of stance accretion. -/
inductive TQuality
  | educated
  | articulate
  | elegant
  | prissy
  | habitual (s : TStance)
  deriving DecidableEq, Fintype

/-- A meaning of /t/ release is a stance or a quality. -/
inductive TMeaning
  | stance (s : TStance)
  | quality (q : TQuality)
  deriving DecidableEq, Fintype

/-- Stance accretion is the ideological field on which a stance is available to be construed
as the quality of habitually taking it, the mechanism by which the field is elaborated. -/
def accretion : IdeologicalField TMeaning
  | .stance s => {.quality (.habitual s)}
  | .quality _ => ∅

theorem quality_habitual_mem_construe {S : Finset TMeaning} {s : TStance}
    (h : .stance s ∈ S) : .quality (.habitual s) ∈ accretion.construe S :=
  accretion.mem_construe.2 (.inr ⟨_, h, by simp [accretion]⟩)

/-- The field of /t/ release of Figure 4, nine stances and four qualities. -/
def tRelease : Finset TMeaning :=
  {.stance .formal, .stance .clear, .stance .emphatic, .stance .annoyed, .stance .angry,
    .stance .careful, .stance .exasperated, .stance .polite, .stance .effortful,
    .quality .educated, .quality .articulate, .quality .elegant, .quality .prissy}

/-- Qualities are construed no further, so accretion elaborates the field in one round, and
the indexical field of /t/ release is Figure 4 with the habitual quality of each of its
stances. -/
theorem indexicalField_tRelease :
    accretion.indexicalField tRelease = accretion.construe tRelease :=
  accretion.indexicalField_eq_iterate (n := 1) (by decide)

/-- The social types of Figure 4 are the enregistered voices at the less fluid end of the field
that anchor interpretation, the British of the stereotype /t/ release evokes, the school
teacher of the standard of clear speech, the nerd girl who builds on that standard while
distancing herself from teachers, and the gay diva of [podesva-2007]'s Heath. -/
inductive SocialType
  | british
  | schoolTeacher
  | nerdGirl
  | gayDiva
  deriving DecidableEq

/-- Each type anchors the meanings the text gives it, the British the articulateness of their
stereotype and the elegance it opens up, the teacher clear, careful standard speech, the nerd
girl its clarity and education, the diva the prissiness of the teacher's pet with
exasperation. -/
def SocialType.anchors : SocialType → Finset TMeaning
  | .british => {.quality .articulate, .quality .elegant}
  | .schoolTeacher => {.stance .clear, .stance .careful, .quality .educated}
  | .nerdGirl => {.stance .clear, .quality .educated}
  | .gayDiva => {.quality .prissy, .stance .exasperated}

theorem nerdGirl_anchors_subset :
    SocialType.nerdGirl.anchors ⊆ SocialType.schoolTeacher.anchors := by
  decide

theorem gayDiva_habitual_exasperated :
    .quality (.habitual .exasperated) ∈ accretion.construe SocialType.gayDiva.anchors :=
  quality_habitual_mem_construe (by decide)

/-- The continuum of /t/ articulation runs from hypo- to hyperarticulation, from the deletion
stigmatized in African American English through the flap of American English and the release
of British English to the exaggerated release of the diva's parody. -/
inductive Articulation
  | deletion
  | flap
  | released
  | exaggeratedRelease
  deriving DecidableEq, Fintype

/-- The position of an articulation on the continuum. -/
def Articulation.rank : Articulation → ℕ
  | .deletion => 0
  | .flap => 1
  | .released => 2
  | .exaggeratedRelease => 3

instance : LinearOrder Articulation := .lift' Articulation.rank (by decide)

instance : OrderBot Articulation where
  bot := .deletion
  bot_le := by decide

instance : OrderTop Articulation where
  top := .exaggeratedRelease
  le_top := by decide

/-- The diva style combines deletion with exaggerated bursts. -/
def divaStyle : Finset Articulation := {.deletion, .exaggeratedRelease}

theorem divaStyle_eq : divaStyle = {⊥, ⊤} := rfl

/-! ### Belten High, Figure 1 -/

inductive Gender
  | girl
  | boy
  deriving DecidableEq

/-- The school-oriented jocks and the urban-oriented burnouts. -/
inductive Orientation
  | jock
  | burnout
  deriving DecidableEq

/-- A social category of Figure 1 crosses gender with orientation. -/
structure Group where
  gender : Gender
  orientation : Orientation
  deriving DecidableEq

/-- The seven variables fall into three strata, the older fronting components of the Northern
Cities Shift, stabilized across the suburbs, the newer backing changes more advanced near the
urban centre, and negative concord. -/
inductive Stratum
  | older
  | newer
  | negativeConcord
  deriving DecidableEq, Fintype

/-- A group leads a stratum when it is among the greatest or second-greatest users Figure 1
marks, girls for the older changes and burnouts for the newer urban changes and negative
concord. -/
def Leads (g : Group) : Stratum → Prop
  | .older => g.gender = .girl
  | .newer | .negativeConcord => g.orientation = .burnout

instance (g : Group) : DecidablePred (Leads g)
  | .older => inferInstanceAs (Decidable (g.gender = .girl))
  | .newer | .negativeConcord => inferInstanceAs (Decidable (g.orientation = .burnout))

theorem leads_all_iff (g : Group) : (∀ s, Leads g s) ↔ g = ⟨.girl, .burnout⟩ :=
  ⟨λ h => by cases g; cases h .older; cases h .newer; rfl, by rintro rfl s; cases s <;> rfl⟩

theorem jockBoys_lead_none : ∀ s, ¬ Leads ⟨.boy, .jock⟩ s := by decide

end Eckert2008
