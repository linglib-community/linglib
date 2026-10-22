module

public import Linglib.Phonology.OptimalityTheory.Constraint.ForbiddenPairs
public import Linglib.Phonology.OptimalityTheory.Correspondence.Basic
public import Linglib.Phonology.OptimalityTheory.Tableau

/-!
# Berent et al. (2016): The double identity of linguistic doubling

This file formalizes the account of doubling by Berent, Bat-El, Brentari, Dupuis and
Vaknin-Nusbaum. A doubled form XX has two parses. As a single morpheme it contains two
identical constituents, which the Obligatory Contour Principle (OCP) bans. As a base
followed by its copy it is morphological reduplication, which languages favour. In twelve
experiments speakers disliked doubled novel words and novel ASL signs presented in
isolation, and preferred them once doubling was linked to the meaning of a taught base.
English speakers preferred doubled signs as plurals and not as diminutives, while Hebrew
speakers, whose reduplication marks diminution and never plurality, showed the opposite
pattern.

The authors' formal analysis has two constraints and no ranking. At the phonological
level XX violates the OCP and the control XY does not. At the morphological level the copy
escapes the OCP, which operates within a morpheme, and satisfies DEP, the ban on output
material without an input correspondent, which XY violates by adding material to the base.
Here both violation patterns are computed from the parses, over any type of prosodic
constituent. The winner at each level harmonically bounds its competitors, so the
predictions hold under both rankings.

## Main definitions

* `Parse`: a name as a single morpheme or as a base followed by its copy.
* `ocp`, `dep`: the OCP within each morpheme, and DEP against the taught base.
* `Level`, `tableau`: the level of analysis, and the competition it induces between a
  doubled name and its control.
* `SpokenLanguage`, `SpokenLanguage.Licenses`: the meanings a language marks
  morphologically and by reduplication, and the two transfer conditions on a morphological
  parse of doubling.

## Main results

* `Parse.surface_reduplicated`: the two parses of doubling share a surface form.
* `optimal_phonology`, `optimal_morphology`: the control wins at the phonological level and
  the reduplicative parse at the morphological level, under every ranking.
* `SpokenLanguage.licenses_iff`: a language licenses a meaning when it reduplicates for it,
  or reduplicates for nothing and marks it otherwise.
* `exists_optimal_surface_iff`: doubling is preferred exactly for the licensed meanings.
* `english_licenses_iff`, `hebrew_licenses_iff`, `licenses_not_monotone`: English licenses
  the plural alone and Hebrew the diminutive alone, although Hebrew morphology extends
  English morphology on both dimensions.

## Implementation notes

The control XY is a single morpheme at both levels, and DEP counts the constituents of a
name's stem beyond the taught base. With no base taught a name is its own input, so DEP is
vacuous. The reduplicative parse competes only at the morphological level, where the input
contains the reduplicative morpheme. Negative evidence against reduplication for a meaning
is read as the language reduplicating for other meanings only. The illicit conditions,
where the base and the doubled form name objects of different kinds, are not modelled.

## References

* [berent-bat-el-brentari-dupuis-vaknin-nusbaum-2016]
* [mccarthy-1986]
* [mccarthy-prince-1995]
-/

@[expose] public section

namespace BerentEtAl2016

open OptimalityTheory

variable {α M : Type*} {x y : α}

/-! ### The two parses of doubling -/

/-- A morphological parse of a name over prosodic constituents of type `α`. -/
inductive Parse (α : Type*) where
  /-- A single morpheme. -/
  | simplex (form : List α)
  /-- A base followed by its copy. -/
  | reduplicated (base : List α)
  deriving DecidableEq

namespace Parse

/-- The morphemes of a parse, in order. -/
def morphemes : Parse α → List (List α)
  | simplex form => [form]
  | reduplicated base => [base, base]

/-- The surface form of a parse, which does not record its morphemes. -/
def surface (p : Parse α) : List α := p.morphemes.flatten

/-- A base followed by its copy has the surface form of the simplex double, so doubling is
structurally ambiguous. -/
theorem surface_reduplicated (base : List α) :
    (reduplicated base).surface = (simplex (base ++ base)).surface := by
  simp [surface, morphemes]

/-- The correspondence diagram of a parse against an input treats a simplex name as all
stem, and the copy of a reduplicated name as its reduplicant. -/
def correspondence (input : List α) :
    Parse α → Correspondence ReduplicationRole α
  | simplex form => .reduplication input form []
  | reduplicated base => .reduplication input base base

end Parse

/-! ### The two levels of analysis -/

/-- The level at which a speaker analyses a name. -/
inductive Level where
  /-- A pattern of meaningless elements, the name in isolation. -/
  | phonology
  /-- A form linked to the meaning of a taught base. -/
  | morphology
  deriving DecidableEq

/-- The taught base `x` is the input at the morphological level only. -/
def Level.input (x : α) : Level → Option (List α)
  | .phonology => none
  | .morphology => some [x]

/-- The competitors for a doubled name XX and its control XY are the simplex parses at both
levels, joined by the reduplicative parse at the morphological level. -/
def candidates [DecidableEq α] (x y : α) : Level → Finset (Parse α)
  | .phonology => {.simplex [x, y], .simplex [x, x]}
  | .morphology => {.reduplicated [x], .simplex [x, y], .simplex [x, x]}

/-! ### The constraints -/

/-- DEP counts the constituents of the stem without a correspondent in the taught base.
With no base taught, a name is its own input and DEP is vacuous. -/
def dep (base : Option (List α)) : Constraint (Parse α) := fun p ↦
  base.elim 0 fun b ↦ (p.correspondence b).depViol .input .base

@[simp] theorem dep_none (p : Parse α) : dep none p = 0 := rfl

/-- A simplex name adds to the base whatever it has beyond the base's length. -/
@[simp] theorem dep_some_simplex (b form : List α) :
    dep (some b) (.simplex form) = form.length - b.length :=
  Correspondence.depViol_of_diagonal (.reduplication b form []) .input .base
    (Correspondence.reduplication_edge _ _ _ (by decide))

/-- A reduplicated name adds to the taught base whatever its own base has beyond it, and
its copy adds nothing. -/
@[simp] theorem dep_some_reduplicated (b base : List α) :
    dep (some b) (.reduplicated base) = base.length - b.length :=
  Correspondence.depViol_of_diagonal (.reduplication b base base) .input .base
    (Correspondence.reduplication_edge _ _ _ (by decide))

variable [DecidableEq α]

/-- The OCP counts the adjacent identical constituents within each morpheme. -/
def ocp : Constraint (Parse α) := fun p ↦ (p.morphemes.map Constraint.ocp).sum

@[simp] theorem ocp_simplex_double (x : α) : ocp (.simplex [x, x]) = 1 := by
  simp [ocp, Parse.morphemes]

@[simp] theorem ocp_simplex_pair (h : x ≠ y) : ocp (.simplex [x, y]) = 0 := by
  simp [ocp, Parse.morphemes, h]

/-- The OCP is inapplicable to a base and its copy, which are separate morphemes. -/
@[simp] theorem ocp_reduplicated_singleton (x : α) : ocp (.reduplicated [x]) = 0 := by
  simp [ocp, Parse.morphemes]

/-! ### The competition between a doubled name and its control -/

/-- The OCP and DEP against the input of the level. -/
def con (x : α) (l : Level) : ConstraintSet (Parse α) (Fin 2) := ![ocp, dep (l.input x)]

/-- The competition between XX and XY at a level, under a ranking of the OCP and DEP. -/
def tableau (x y : α) (l : Level) (r : Ranking (Fin 2) 2) : Tableau (Parse α) 2 :=
  .ofRanking (con x l) r (candidates x y l)

/-- At the phonological level the control wins under either ranking, because doubling is
identity within a morpheme, which the OCP bans. -/
theorem optimal_phonology (h : x ≠ y) (r : Ranking (Fin 2) 2) :
    (tableau x y .phonology r).optimal = {.simplex [x, y]} := by
  refine Tableau.ofRanking_optimal_eq_singleton_of_forall_lt (by simp [candidates]) ?_
  simp only [candidates, Finset.mem_insert, Finset.mem_singleton]
  rintro d (rfl | rfl) hd
  · exact absurd rfl hd
  · simp [Pi.lt_def, Pi.le_def, Fin.forall_fin_two, Fin.exists_fin_two, con, Level.input, h]

/-- At the morphological level the reduplicative parse wins under either ranking, because it
escapes the OCP and adds nothing to the base, while the control violates DEP. -/
theorem optimal_morphology (h : x ≠ y) (r : Ranking (Fin 2) 2) :
    (tableau x y .morphology r).optimal = {.reduplicated [x]} := by
  refine Tableau.ofRanking_optimal_eq_singleton_of_forall_lt (by simp [candidates]) ?_
  simp only [candidates, Finset.mem_insert, Finset.mem_singleton]
  rintro d (rfl | rfl | rfl) hd
  · exact absurd rfl hd
  · simp [Pi.lt_def, Pi.le_def, Fin.forall_fin_two, Fin.exists_fin_two, con, Level.input, h]
  · simp [Pi.lt_def, Pi.le_def, Fin.forall_fin_two, Fin.exists_fin_two, con, Level.input]

/-! ### Transfer from the spoken language -/

/-- The morphology of a spoken language as it bears on doubling, over meanings `M`. -/
structure SpokenLanguage (M : Type*) where
  /-- The meanings the language expresses by some morphological means. -/
  marked : Finset M
  /-- The meanings the language expresses by reduplication. -/
  reduplicated : Finset M
  /-- Reduplication is a morphological means. -/
  protected reduplicated_subset : reduplicated ⊆ marked

namespace SpokenLanguage

variable {l : SpokenLanguage M} {f g : M}

/-- A speaker parses doubling with meaning `f` morphologically when the spoken language
gives positive evidence that morphology expresses `f` and no negative evidence that
reduplication cannot, so that if it reduplicates at all, it does so for `f`. -/
def Licenses (l : SpokenLanguage M) (f : M) : Prop :=
  f ∈ l.marked ∧ (l.reduplicated.Nonempty → f ∈ l.reduplicated)

instance [DecidableEq M] : DecidablePred l.Licenses :=
  fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

theorem licenses_iff :
    l.Licenses f ↔ f ∈ l.reduplicated ∨ l.reduplicated = ∅ ∧ f ∈ l.marked := by
  rw [Licenses, Finset.nonempty_iff_ne_empty]
  constructor
  · rintro ⟨hm, hr⟩
    by_cases h : l.reduplicated = ∅
    exacts [.inr ⟨h, hm⟩, .inl (hr h)]
  · rintro (h | ⟨h, hm⟩)
    exacts [⟨l.reduplicated_subset h, fun _ ↦ h⟩, ⟨hm, fun hne ↦ absurd h hne⟩]

/-- Reduplication for a meaning licenses it, which is positive transfer. -/
theorem licenses_of_mem (h : f ∈ l.reduplicated) : l.Licenses f := licenses_iff.2 (.inl h)

/-- Reduplication for another meaning only withdraws the licence, which is negative
transfer. -/
theorem not_licenses_of_mem_of_notMem (hg : g ∈ l.reduplicated) (hf : f ∉ l.reduplicated) :
    ¬ l.Licenses f := fun h ↦ hf (h.2 ⟨g, hg⟩)

/-- A language without reduplication licenses exactly the meanings it marks. -/
theorem licenses_iff_of_eq_empty (h : l.reduplicated = ∅) : l.Licenses f ↔ f ∈ l.marked := by
  simp [licenses_iff, h]

/-- The level at which a speaker analyses a doubled name taught with meaning `f`. -/
def level [DecidableEq M] (l : SpokenLanguage M) (f : M) : Level :=
  if l.Licenses f then .morphology else .phonology

end SpokenLanguage

/-- Doubling is preferred exactly for the meanings the spoken language licenses, in that
the winner surfaces as XX when the meaning is licensed and as XY otherwise. -/
theorem exists_optimal_surface_iff [DecidableEq M] (l : SpokenLanguage M) (f : M) (h : x ≠ y)
    (r : Ranking (Fin 2) 2) :
    (∃ p ∈ (tableau x y (l.level f) r).optimal, p.surface = [x, x]) ↔ l.Licenses f := by
  unfold SpokenLanguage.level
  split_ifs with hf
  · simp [optimal_morphology h, hf, Parse.surface, Parse.morphemes]
  · simp [optimal_phonology h, hf, Parse.surface, Parse.morphemes, h.symm]

/-! ### English and Hebrew -/

/-- The meanings paired with doubled signs in experiments 6 and 10–12. -/
inductive Meaning where
  | plural
  | diminutive
  deriving DecidableEq

/-- English marks plurality, by suffixation (*dog-s*), has no productive diminutive, and
reduplicates for nothing. -/
def english : SpokenLanguage Meaning := ⟨{.plural}, ∅, Finset.empty_subset _⟩

/-- Hebrew marks plurality by suffixation (*shir* 'song', *shirim* 'songs') and diminution
by reduplication (*kelev* 'dog', *klavlav* 'puppy'), which never marks plurality. -/
def hebrew : SpokenLanguage Meaning := ⟨{.plural, .diminutive}, {.diminutive}, by decide⟩

theorem english_licenses_iff {f : Meaning} : english.Licenses f ↔ f = .plural := by
  simp [SpokenLanguage.licenses_iff_of_eq_empty, english]

theorem hebrew_licenses_iff {f : Meaning} : hebrew.Licenses f ↔ f = .diminutive := by
  simp [SpokenLanguage.licenses_iff, hebrew]

/-- Licensing is not monotone in the morphology. Hebrew marks and reduplicates for
everything English does, yet English speakers alone parse a doubled plural
morphologically. -/
theorem licenses_not_monotone :
    english.marked ⊆ hebrew.marked ∧ english.reduplicated ⊆ hebrew.reduplicated ∧
      english.Licenses .plural ∧ ¬ hebrew.Licenses .plural := by
  decide

/-- In the Language × Meaning interaction of experiments 6a and 10a–12a, English speakers
prefer doubled plurals and Hebrew speakers doubled diminutives, under either ranking and
for any constituents. -/
theorem doubling_dissociation (f : Meaning) (h : x ≠ y) (r : Ranking (Fin 2) 2) :
    ((∃ p ∈ (tableau x y (english.level f) r).optimal, p.surface = [x, x]) ↔ f = .plural) ∧
      ((∃ p ∈ (tableau x y (hebrew.level f) r).optimal, p.surface = [x, x]) ↔
        f = .diminutive) := by
  rw [exists_optimal_surface_iff _ _ h, exists_optimal_surface_iff _ _ h,
    english_licenses_iff, hebrew_licenses_iff]
  exact ⟨Iff.rfl, Iff.rfl⟩

end BerentEtAl2016
