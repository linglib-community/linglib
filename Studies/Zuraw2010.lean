module

public import Linglib.Phonology.OptimalityTheory.Constraint.Defs
public import Linglib.Phonology.OptimalityTheory.PartiallyOrderedConstraints
public import Linglib.Fragments.Tagalog.Phonology

/-!
# Zuraw (2010): A Model of Lexical Variation and the Grammar

This file formalizes Zuraw's factorial typology of Tagalog nasal substitution. When a
nasal-final prefix such as *maŋ-* attaches to an obstruent-initial stem, the nasal and the
obstruent may coalesce into a single nasal at the obstruent's place, as in *maŋ+bigáj* →
*mamigáj* 'to distribute', or the cluster may survive, as in *paŋ+tabój* → *pantabój* 'to goad'.
Six constraints decide the outcome. `DEP-C` and *NC favour substitution, while *ASSOCIATE and the
stringent hierarchy of stem-initial nasals after Prince and de Lacy oppose it.

With the six constraints freely ranked, the share of the rankings that substitute for each
stem-initial stop follows in closed form from uniform sampling of total orders
(`factorial_rates`). Substitution is therefore more likely on voiceless than on voiced stems
(`voicing_monotonicity`) and on fronter than on backer stems (`place_monotonicity`). Newman's
implicational universals, which the paper's Table 5 organizes, hold ranking by ranking, so that
substitution on voiced velar *g* entails substitution on every stop (`g_implies_all`).

## Implementation notes

* The candidate space is the stem-initial stop paired with the substitution decision; the
  constraints the paper holds fixed above the six do not distinguish the two candidates.
* The rates are model quantities of the free-ranking idealization. The paper's dictionary
  counts, corpus rates and acceptability results are not represented; the place effect among
  voiceless stems is not significant in its judgment data.

## References

* [K. Zuraw, *A Model of Lexical Variation and the Grammar with Application to Tagalog Nasal
  Substitution* (2010)][zuraw-2010]
* [K. Zuraw and B. Hayes, *Intersecting Constraint Families: An Argument for Harmonic Grammar*
  (2017)][zuraw-hayes-2017]
* [J. Pater, *Austronesian nasal substitution and other NC effects* (1999)][pater-1999]
* [A. Prince, *Stringency and anti-Paninian hierarchies* (1997)][prince-1997-stringency]
* [P. de Lacy, *The formal expression of markedness* (2002)][delacy-2002]
* [J. Newman, *Nasal replacement in Western Austronesian: an overview* (1984)][newman-1984]
* [R. Blust, *Austronesian nasal substitution: a survey* (2004)][blust-2004]
-/

@[expose] public section

namespace Zuraw2010

open OptimalityTheory Finset ProbabilityTheory

/-! ### Stems and substitution decisions -/

/-- The six stem-initial stops; coalescence maps each to its homorganic nasal. -/
inductive StemC
  | p | t | k
  | b | d | g
  deriving DecidableEq, Repr, Fintype

/-- Nasal substitution either applies, giving the coalesced nasal, or does not, leaving the
faithful cluster. -/
inductive SubSt
  | yes
  | no
  deriving DecidableEq, Repr, Fintype

/-- A candidate is a stem-initial stop paired with a substitution decision. -/
abbrev NSCand := StemC × SubSt

/-- `c.segment` is the stem-initial stop `c` as a segment of `Fragments/Tagalog/Phonology.lean`. -/
def StemC.segment : StemC → Phonology.Segment
  | .p => Tagalog.p | .t => Tagalog.t | .k => Tagalog.k
  | .b => Tagalog.b | .d => Tagalog.d | .g => Tagalog.g

/-- The stem classes that the constraints below list are natural classes, since the stems of *NC
are the voiceless ones, those of *[ŋ the dorsal ones, and those of *[n the ones that are not
labial. -/
theorem mem_iff_segment (c : StemC) :
    (c ∈ [StemC.p, .t, .k] ↔ Phonology.Segment.ofSpecs [(.voice, false)] ≤ c.segment) ∧
      (c ∈ [StemC.k, .g] ↔ Phonology.Segment.ofSpecs [(.dorsal, true)] ≤ c.segment) ∧
      (c ∈ [StemC.t, .d, .k, .g] ↔ Phonology.Segment.ofSpecs [(.labial, false)] ≤ c.segment) := by
  cases c <;> decide

/-- `c.nasal` is the nasal at the place of the stop `c`. -/
def StemC.nasal : StemC → Phonology.Segment
  | .p | .b => Tagalog.m
  | .t | .d => Tagalog.n
  | .k | .g => Tagalog.ŋ

/-- Coalescence gives the nasal of the stop's place, by the fragment's substitution. -/
theorem substitute_segment (c : StemC) : Tagalog.substitute c.segment = [c.nasal] := by
  cases c <;> decide

/-! ### The six constraints -/

/-- `DEP-C` of (6) penalizes inserting a segmental host for the floating nasal, so the faithful
cluster violates it for every stem. It is named after [zuraw-hayes-2017]'s markedness `NasSub`,
which has the same violation profile on this candidate space. -/
def nasSub : Constraint NSCand :=
  Constraint.binary fun c ↦ c.2 = SubSt.no

/-- *NC of (17), after [pater-1999], forbids a nasal followed by a voiceless obstruent, so the
faithful cluster violates it for voiceless stems. -/
def starNC : Constraint NSCand :=
  Constraint.binary fun c ↦ c.1 ∈ [StemC.p, .t, .k] ∧ c.2 = .no

/-- *ASSOCIATE of (7) forbids new association lines across a morpheme boundary, so coalescence
violates it for every stem. -/
def starAssoc : Constraint NSCand :=
  Constraint.binary fun c ↦ c.2 = SubSt.yes

/-- *[ŋ of (19) forbids a stem to begin with ŋ, so coalescence violates it on velar stems. -/
def starInitVelar : Constraint NSCand :=
  Constraint.binary fun c ↦ c.1 ∈ [StemC.k, .g] ∧ c.2 = .yes

/-- *[n of (19) forbids a stem to begin with n or a backer nasal, so coalescence violates it on
coronal and velar stems. -/
def starInitCorVel : Constraint NSCand :=
  Constraint.binary fun c ↦ c.1 ∈ [StemC.t, .d, .k, .g] ∧ c.2 = .yes

/-- *[m of (19) forbids a stem to begin with m or a backer nasal, so coalescence violates it on
every stem. -/
def starInitAll : Constraint NSCand :=
  Constraint.binary fun c ↦ c.2 = SubSt.yes

/-- The six constraints are listed in the order of the paper's footnote on free ranking. -/
def con : ConstraintSet NSCand (Fin 6)
  | 0 => nasSub
  | 1 => starNC
  | 2 => starAssoc
  | 3 => starInitVelar
  | 4 => starInitCorVel
  | 5 => starInitAll

/-- The stringent hierarchy assigns one, two and three violations to coalesced labial, coronal
and velar stems. -/
theorem stringency_violations :
    starInitAll (.p, .yes) + starInitCorVel (.p, .yes) + starInitVelar (.p, .yes) = 1 ∧
    starInitAll (.t, .yes) + starInitCorVel (.t, .yes) + starInitVelar (.t, .yes) = 2 ∧
    starInitAll (.k, .yes) + starInitCorVel (.k, .yes) + starInitVelar (.k, .yes) = 3 := by
  decide

/-- *ASSOCIATE and *[m have the same violation profile on this candidate space. -/
theorem assoc_eq_initAll (c : StemC) (s : SubSt) : starAssoc (c, s) = starInitAll (c, s) := by
  cases c <;> cases s <;> rfl

/-! ### The free-ranking rates -/

/-- The nasal-substitution system makes both decisions available for every stem, under the six
constraints. -/
def nasalSubstitution : ConstraintSystem StemC SubSt (Fin 6) := ⟨fun _ ↦ Finset.univ, con⟩

private theorem nasalSubstitution_gen (c : StemC) :
    nasalSubstitution.gen c = {SubSt.yes, SubSt.no} := by
  unfold nasalSubstitution
  ext o
  cases o <;> simp

/-- `subProb c` is the share of the 720 total orders on which stem `c` substitutes. -/
noncomputable def subProb (c : StemC) : ℝ :=
  (uniformOn (Set.univ : Set (Ranking (Fin 6) 6))).real {σ | PicksAt nasalSubstitution σ c .yes}

/-- The share is the fraction of distinguishing constraints that favour substitution. -/
private theorem subProb_eq_rate (c : StemC) :
    subProb c = ((favoring con c .yes .no).card : ℝ) / (active con c .yes .no).card :=
  uniformOn_real_picksAt_discrete_binary (nasalSubstitution_gen c) fun heq ↦ SubSt.noConfusion heq

theorem subProb_p : subProb .p = 1/2 := by
  rw [subProb_eq_rate, show (favoring con .p .yes .no).card = 2 by
    decide, show (active con .p .yes .no).card = 4 by decide]
  norm_num

theorem subProb_t : subProb .t = 2/5 := by
  rw [subProb_eq_rate, show (favoring con .t .yes .no).card = 2 by
    decide, show (active con .t .yes .no).card = 5 by decide]
  norm_num

theorem subProb_k : subProb .k = 1/3 := by
  rw [subProb_eq_rate, show (favoring con .k .yes .no).card = 2 by
    decide, show (active con .k .yes .no).card = 6 by decide]
  norm_num

theorem subProb_b : subProb .b = 1/3 := by
  rw [subProb_eq_rate, show (favoring con .b .yes .no).card = 1 by
    decide, show (active con .b .yes .no).card = 3 by decide]
  norm_num

theorem subProb_d : subProb .d = 1/4 := by
  rw [subProb_eq_rate, show (favoring con .d .yes .no).card = 1 by
    decide, show (active con .d .yes .no).card = 4 by decide]
  norm_num

theorem subProb_g : subProb .g = 1/5 := by
  rw [subProb_eq_rate, show (favoring con .g .yes .no).card = 1 by
    decide, show (active con .g .yes .no).card = 5 by decide]
  norm_num

/-- The six free-ranking shares of the paper's footnote are a half, two fifths and a third for
the voiceless stops and a third, a quarter and a fifth for the voiced ones. -/
theorem factorial_rates :
    subProb .p = 1/2 ∧ subProb .t = 2/5 ∧ subProb .k = 1/3 ∧
    subProb .b = 1/3 ∧ subProb .d = 1/4 ∧ subProb .g = 1/5 :=
  ⟨subProb_p, subProb_t, subProb_k, subProb_b, subProb_d, subProb_g⟩

/-- Within each voicing class the share falls from labial to coronal to velar. -/
theorem place_monotonicity :
    subProb .p > subProb .t ∧ subProb .t > subProb .k ∧
    subProb .b > subProb .d ∧ subProb .d > subProb .g := by
  rw [subProb_p, subProb_t, subProb_k, subProb_b, subProb_d, subProb_g]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num

/-- At each place the voiceless share is at least the voiced one. -/
theorem voicing_monotonicity :
    subProb .p ≥ subProb .b ∧ subProb .t ≥ subProb .d ∧ subProb .k ≥ subProb .g := by
  rw [subProb_p, subProb_t, subProb_k, subProb_b, subProb_d, subProb_g]
  refine ⟨?_, ?_, ?_⟩ <;> norm_num

/-! ### The implicational universals, ranking by ranking -/

/-- If `c'` has a smaller distinguishing set than `c` and every extra constraint of `c` favours
substitution, then substitution on `c'` entails substitution on `c`. -/
theorem picksAt_extends_smaller_D {σ : Equiv.Perm (Fin 6)} {c c' : StemC}
    (h_D : active con c' .yes .no ⊆ active con c .yes .no)
    (h_Y : favoring con c' .yes .no ⊆ favoring con c .yes .no)
    (h_extra :
      ∀ x ∈ active con c .yes .no, x ∉ active con c' .yes .no → x ∈ favoring con c .yes .no)
    (h_c' : PicksAt nasalSubstitution σ c' .yes) : PicksAt nasalSubstitution σ c .yes := by
  rw [picksAt_binary_iff_exists_favoring_isMinOn (nasalSubstitution_gen c') SubSt.noConfusion]
    at h_c'
  rw [picksAt_binary_iff_exists_favoring_isMinOn (nasalSubstitution_gen c) SubSt.noConfusion]
  obtain ⟨x, hx, hmin⟩ := h_c'
  obtain ⟨z, hz, hzmin⟩ := Equiv.Perm.exists_isMinOn_symm ⟨x, h_D (mem_inter.1 hx).2⟩ σ
  refine ⟨z, mem_inter.2 ⟨?_, hz⟩, hzmin⟩
  by_cases hz' : z ∈ active con c' .yes .no
  · rw [Equiv.Perm.eq_of_isMinOn_symm hz' (mem_inter.1 hx).2 (hzmin.of_subset (coe_subset.2 h_D))
      hmin]
    exact h_Y (mem_inter.1 hx).1
  · exact h_extra z hz hz'

/-- If `c'` has a larger distinguishing set than `c` and its substitution-favouring constraints
all distinguish the candidates for `c`, then substitution on `c'` entails substitution on
`c`. -/
theorem picksAt_extends_larger_D {σ : Equiv.Perm (Fin 6)} {c c' : StemC}
    (h_D : active con c .yes .no ⊆ active con c' .yes .no)
    (h_Y : favoring con c' .yes .no ⊆ favoring con c .yes .no)
    (h_subset : favoring con c' .yes .no ⊆ active con c .yes .no)
    (h_c' : PicksAt nasalSubstitution σ c' .yes) : PicksAt nasalSubstitution σ c .yes := by
  rw [picksAt_binary_iff_exists_favoring_isMinOn (nasalSubstitution_gen c') SubSt.noConfusion]
    at h_c'
  rw [picksAt_binary_iff_exists_favoring_isMinOn (nasalSubstitution_gen c) SubSt.noConfusion]
  obtain ⟨x, hx, hmin⟩ := h_c'
  exact ⟨x, mem_inter.2 ⟨h_Y (mem_inter.1 hx).1, h_subset (mem_inter.1 hx).1⟩,
    hmin.of_subset (coe_subset.2 h_D)⟩

/-- Substitution on voiced *b* entails substitution on voiceless *p*. -/
theorem voicing_b_implies_p (σ : Equiv.Perm (Fin 6)) :
    PicksAt nasalSubstitution σ .b .yes → PicksAt nasalSubstitution σ .p .yes :=
  picksAt_extends_smaller_D (by decide) (by decide) (by decide)

/-- Substitution on voiced *d* entails substitution on voiceless *t*. -/
theorem voicing_d_implies_t (σ : Equiv.Perm (Fin 6)) :
    PicksAt nasalSubstitution σ .d .yes → PicksAt nasalSubstitution σ .t .yes :=
  picksAt_extends_smaller_D (by decide) (by decide) (by decide)

/-- Substitution on voiced *g* entails substitution on voiceless *k*. -/
theorem voicing_g_implies_k (σ : Equiv.Perm (Fin 6)) :
    PicksAt nasalSubstitution σ .g .yes → PicksAt nasalSubstitution σ .k .yes :=
  picksAt_extends_smaller_D (by decide) (by decide) (by decide)

/-- Substitution on velar *k* entails substitution on coronal *t*. -/
theorem place_k_implies_t (σ : Equiv.Perm (Fin 6)) :
    PicksAt nasalSubstitution σ .k .yes → PicksAt nasalSubstitution σ .t .yes :=
  picksAt_extends_larger_D (by decide) (by decide) (by decide)

/-- Substitution on coronal *t* entails substitution on labial *p*. -/
theorem place_t_implies_p (σ : Equiv.Perm (Fin 6)) :
    PicksAt nasalSubstitution σ .t .yes → PicksAt nasalSubstitution σ .p .yes :=
  picksAt_extends_larger_D (by decide) (by decide) (by decide)

/-- Substitution on velar *g* entails substitution on coronal *d*. -/
theorem place_g_implies_d (σ : Equiv.Perm (Fin 6)) :
    PicksAt nasalSubstitution σ .g .yes → PicksAt nasalSubstitution σ .d .yes :=
  picksAt_extends_larger_D (by decide) (by decide) (by decide)

/-- Substitution on coronal *d* entails substitution on labial *b*. -/
theorem place_d_implies_b (σ : Equiv.Perm (Fin 6)) :
    PicksAt nasalSubstitution σ .d .yes → PicksAt nasalSubstitution σ .b .yes :=
  picksAt_extends_larger_D (by decide) (by decide) (by decide)

/-- Substitution on voiced velar *g* entails substitution on every stop, the top of the
implicational hierarchy of Table 5. -/
theorem g_implies_all (σ : Equiv.Perm (Fin 6)) (h : PicksAt nasalSubstitution σ .g .yes) :
    PicksAt nasalSubstitution σ .p .yes ∧ PicksAt nasalSubstitution σ .t .yes ∧
    PicksAt nasalSubstitution σ .k .yes ∧ PicksAt nasalSubstitution σ .b .yes ∧
    PicksAt nasalSubstitution σ .d .yes ∧ PicksAt nasalSubstitution σ .g .yes := by
  have h_d := place_g_implies_d σ h
  have h_b := place_d_implies_b σ h_d
  have h_k := voicing_g_implies_k σ h
  have h_t := place_k_implies_t σ h_k
  have h_p := place_t_implies_p σ h_t
  exact ⟨h_p, h_t, h_k, h_b, h_d, h⟩

/-- Some ranking substitutes on every stop, which is pattern (j) of Table 5, that of Kalinga and
Sarangani Manobo. The identity ranking, with `DEP-C` on top, is one. -/
theorem pattern_j_witness :
    ∃ σ : Equiv.Perm (Fin 6),
      PicksAt nasalSubstitution σ .p .yes ∧ PicksAt nasalSubstitution σ .t .yes ∧
      PicksAt nasalSubstitution σ .k .yes ∧ PicksAt nasalSubstitution σ .b .yes ∧
      PicksAt nasalSubstitution σ .d .yes ∧ PicksAt nasalSubstitution σ .g .yes :=
  ⟨1, by decide, by decide, by decide, by decide, by decide, by decide⟩

end Zuraw2010
