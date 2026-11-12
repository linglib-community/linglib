module

public import Mathlib.Order.Interval.Set.Defs
public import Linglib.Semantics.Presupposition.Strengthening
public import Linglib.Semantics.Mereology
public import Linglib.Semantics.Reference.Context.Basic
public import Linglib.Core.Order.UpperLower.Finset
public import Linglib.Semantics.Plurality.NumberFeatures
public import Linglib.Syntax.Person.Features
public import Linglib.Syntax.Gender.Decomposition

/-!
# The domains of φ-features

Following Sauerland, a φ-feature is a presuppositional partial identity function on entities: it
asserts nothing and is defined on a domain, so it denotes that domain, a `Set` of entities. A bundle
denotes the intersection of its features' domains (`Finset.inf`) and the empty bundle everything, so
over well-formed bundles the domains nest by specification (`IsLowerSet.subset_or_subset` with
`Finset.inf_mono`), the Feature-Subset Principle as a consequence of the privative geometry. Person
is read at parthood of the agent and the addressee of the context of utterance, number at atomicity,
and gender at the gender a referent is socially assigned (`Gendered`). For gender Sauerland makes
masculine the unmarked value, the one coordinations of mixed gender take, with feminine presupposing
non-masculinity and neuter genderlessness, so the neuter domain lies inside the feminine one. The
person domains are the participant-set extents of `Person.Bears` pulled back along the participants
of a referent, and a value of the standard tripartition denotes the referents in its domain and in
no stronger one.

## Main definitions

* `Person.dom`, `Number.dom`, `Gender.dom`: the domain of an optional value.
* `Kaplan.Context.participants`: the discourse roles whose holders are part of a referent.

## Main results

* `Person.mem_dom_feature_iff`: a person feature's domain is the pullback of `Person.Bears`.
* `Person.participants_mem_participantSets_first`, `…_second`, `…_third`: the standard
  tripartition values denote the referents in their domain and in no stronger one.
* `Gender.dom_neuter_subset_dom_feminine`: the neuter domain lies inside the feminine one.

## Implementation notes

An absent feature, and a value without a bundle, the impersonal person, the numbers beyond the
dual and the non-sex-based genders, denote the whole domain; the semantically unmarked values,
third person, plural and masculine, are the empty bundles, whose unrestricted domain Wang finds
recruited by honorification. A referent may be gendered neither way, and then it lies in all three
gender domains. The person entries take the agent and the addressee as parts of the referent where
Sauerland has them overlap it; the two coincide for an atomic agent and addressee. The
two-feature decomposition does not see clusivity, so the inclusive is refined to referents
including the addressee. The cells of the standard tripartition are stated one by one, since
Maximize Presupposition (`Presupposition.strengthen`) yields them only when the agent is not
part of the addressee; otherwise the first and second person domains coincide
(`Sauerland2003.strengthen_second_of_degenerate`).

Number is read at the positive values of a bundle alone, so the plural, `[−atomic, −minimal]`,
restricts nothing, where Harbour's region operators read the same bundle as excluding atoms.
[Strengthening recovers those regions](##Number.strengthen_plural) for the singular and the plural
but not for the dual, whose region `Number.dualOf` is built on `[−atomic]`, a value this reading
lacks, so the dual restricts nothing. This is Martí's undergeneration argument against
inclusive-only plurals.

## References

* [sauerland-2003]
* [sauerland-2008b]
* [wang-r-2023]
* [harbour-2014]
* [marti-2020a]
* [schlenker-2012]
-/

@[expose] public section

open Mereology

/-! ### Person -/

namespace Person

variable {W E P T : Type*} [PartialOrder E] (c : Kaplan.Context W E P T) (x : E)

/-- At a context of utterance, [author] is defined of the referents including the agent and
[participant] of those including the agent or the addressee. -/
def Feature.dom : Feature → Set E
  | .author => Set.Ici c.agent
  | .participant => Set.Ici c.agent ∪ Set.Ici c.addressee

/-- At a context of utterance, the first person is defined of the referents including the agent,
the inclusive of those including the agent and the addressee, and the second of those including
the agent or the addressee; the third person and an absent value, the impersonal, restrict
nothing. -/
def dom : Option Person → Set E
  | some .firstInclusive => Set.Ici c.agent ∩ Set.Ici c.addressee
  | p => (p.map toFeatures).elim Set.univ (·.inf (Feature.dom c))

@[simp] theorem dom_none : dom c none = Set.univ := rfl

@[simp] theorem mem_dom_first : x ∈ dom c (some .first) ↔ c.agent ≤ x := by
  simp [dom, Feature.dom, or_and_right]

@[simp] theorem mem_dom_firstInclusive :
    x ∈ dom c (some .firstInclusive) ↔ c.agent ≤ x ∧ c.addressee ≤ x := Iff.rfl

@[simp] theorem mem_dom_firstExclusive :
    x ∈ dom c (some .firstExclusive) ↔ c.agent ≤ x := by
  simp [dom, Feature.dom, or_and_right]

@[simp] theorem mem_dom_second :
    x ∈ dom c (some .second) ↔ c.agent ≤ x ∨ c.addressee ≤ x := by
  simp [dom, Feature.dom]

@[simp] theorem dom_third : dom c (some .third) = Set.univ := by
  simp [dom]

theorem dom_firstInclusive_subset_dom_first :
    dom c (some .firstInclusive) ⊆ dom c (some .first) :=
  fun _ hx ↦ (mem_dom_first c _).2 hx.1

end Person

namespace Kaplan.Context

variable {W E P T : Type*} [PartialOrder E] (c : Context W E P T) (x : E)

open Classical in
/-- The participants of a referent at a context are the discourse roles whose holders, the agent
and the addressee, are part of it. -/
noncomputable def participants : Finset SpeechAct.Role :=
  Finset.univ.filter fun r ↦ (match r with | .speaker => c.agent | .addressee => c.addressee) ≤ x

@[simp] theorem speaker_mem_participants : .speaker ∈ c.participants x ↔ c.agent ≤ x := by
  simp [participants]

@[simp] theorem addressee_mem_participants :
    .addressee ∈ c.participants x ↔ c.addressee ≤ x := by
  simp [participants]

end Kaplan.Context

namespace Person

variable {W E P T : Type*} [PartialOrder E] (c : Kaplan.Context W E P T) (x : E)

/-- A person feature's domain holds the referents whose participants bear the feature. -/
theorem mem_dom_feature_iff (f : Feature) : x ∈ Feature.dom c f ↔ Bears (c.participants x) f := by
  cases f <;> simp [Feature.dom, Bears, Finset.Nonempty, SpeechAct.Role.exists_role]

/-- The first person denotes the referents in its domain. -/
theorem participants_mem_participantSets_first :
    c.participants x ∈ Person.first.participantSets ↔ x ∈ dom c (some .first) := by
  simp only [mem_dom_first, participantSets, Finset.mem_insert, Finset.mem_singleton,
    Finset.ext_iff, SpeechAct.Role.forall_role, Kaplan.Context.speaker_mem_participants,
    Kaplan.Context.addressee_mem_participants]
  simp; tauto

theorem participants_mem_participantSets_second :
    c.participants x ∈ Person.second.participantSets ↔
      x ∈ dom c (some .second) ∧ x ∉ dom c (some .first) := by
  simp only [mem_dom_second, mem_dom_first, participantSets, Finset.mem_singleton,
    Finset.ext_iff, SpeechAct.Role.forall_role, Kaplan.Context.speaker_mem_participants,
    Kaplan.Context.addressee_mem_participants]
  simp; tauto

theorem participants_mem_participantSets_third :
    c.participants x ∈ Person.third.participantSets ↔ x ∉ dom c (some .second) := by
  simp only [mem_dom_second, participantSets, Finset.mem_singleton, Finset.ext_iff,
    SpeechAct.Role.forall_role, Kaplan.Context.speaker_mem_participants,
    Kaplan.Context.addressee_mem_participants]
  simp

end Person

/-! ### Number -/

namespace Number

open Presupposition

variable {E : Type*} [PartialOrder E] (x : E)

/-- `[+atomic]` is defined of the atoms, the `[+atomic]` region of the whole domain, and
`[+minimal]`, whose dual region needs `[−atomic]`, and `[+additive]`, of everything. -/
def Feature.dom : Feature → Set E
  | .atomic => {x | atomsOf ⊤ x}
  | .minimal | .additive => Set.univ

/-- A bundle is defined where its positive values are. -/
def Bundle.dom (b : Bundle) : Set E := (b.filter (·.2)).inf (Feature.dom ·.1)

@[simp] theorem Bundle.dom_empty : Bundle.dom (E := E) ∅ = Set.univ := rfl

/-- A bundle's region lies in its domain: `dom` is the inclusive reading of what `Bundle.exact`
reads exclusively. -/
theorem Bundle.exact_subset_dom (b : Bundle) {x : E} (h : b.exact ⊤ x) : x ∈ Bundle.dom b := by
  refine Set.singleton_subset_iff.1 (Finset.le_inf fun v hv ↦ Set.singleton_subset_iff.2 ?_)
  obtain ⟨hvb, hv2⟩ := Finset.mem_filter.1 hv
  obtain ⟨f, _ | _⟩ := v
  · cases hv2
  · cases f
    · exact ⟨trivial, Bundle.atom_of_exact hvb h⟩
    · trivial
    · trivial

/-- The singular is defined of the atoms; any other value, and an absent one, restricts
nothing. -/
def dom : Option Number → Set E
  | some .singular => {x | Atom x}
  | _ => Set.univ

@[simp] theorem dom_none : dom (E := E) none = Set.univ := rfl

@[simp] theorem mem_dom_singular : x ∈ dom (E := E) (some .singular) ↔ Atom x := Iff.rfl

@[simp] theorem dom_dual : dom (E := E) (some .dual) = Set.univ := rfl

@[simp] theorem dom_plural : dom (E := E) (some .plural) = Set.univ := rfl

/-- Of the features only `[+atomic]` restricts, so a bundle is defined where the singular is if
it carries `[+atomic]` and everywhere otherwise. -/
theorem Bundle.dom_eq (b : Bundle) :
    Bundle.dom (E := E) b = if (.atomic, true) ∈ b then Number.dom (some .singular) else Set.univ := by
  ext x
  simp only [Bundle.dom, Finset.inf_eq_iInf, Set.iInf_eq_iInter, Set.mem_iInter,
    Finset.mem_filter, and_imp, Prod.forall]
  split_ifs with h
  · refine ⟨fun H ↦ ?_, fun hx f v _ hv ↦ ?_⟩
    · simpa [Feature.dom, atomsOf] using H .atomic true h rfl
    · subst hv
      cases f <;> simp_all [Feature.dom, atomsOf]
  · refine iff_of_true (fun f v hf hv ↦ ?_) trivial
    subst hv
    cases f <;> simp_all [Feature.dom]

/-- Only the singular restricts. -/
theorem dom_eq_univ_of_ne_singular {n : Option Number} (h : n ≠ some .singular) :
    dom (E := E) n = Set.univ := by
  rcases n with _ | n
  · rfl
  · cases n <;> first | exact absurd rfl h | rfl

/-- The alternatives of a number value under Maximize Presupposition: a value competes with the
singular and the plural, and an absent value, which carries no number, with nothing. -/
def alts : Option Number → Set (Option Number)
  | none => ∅
  | some _ => {some .singular, some .plural}

variable {y : E}

theorem dom_singular_ssubset_dom_plural (hy : ¬ Atom y) :
    dom (E := E) (some .singular) ⊂ dom (some .plural) := by
  rw [dom_plural]
  exact ⟨Set.subset_univ _, fun h ↦ hy ((mem_dom_singular y).1 (h (Set.mem_univ y)))⟩

/-- The singular's strengthening is the `[+atomic]` region. -/
theorem strengthen_singular :
    strengthen alts dom (some .singular) = {x : E | atomsOf ⊤ x} := by
  rw [strengthen_eq_self]
  · ext x
    simp [atomsOf]
  · rintro ψ hψ hss
    rcases hψ with rfl | rfl
    · exact hss.ne rfl
    · exact hss.not_subset fun x _ ↦ by rw [dom_plural]; trivial

/-- Strengthened against the singular, the plural's unrestricted domain is the `[−atomic]` region:
the inclusive reading of the bundle recovers the exclusive one. -/
theorem strengthen_plural (hy : ¬ Atom y) :
    strengthen alts dom (some .plural) = {x : E | nonAtomsOf ⊤ x} := by
  rw [strengthen_eq_sdiff (ψ := some .singular) (Set.mem_insert _ _)
    (dom_singular_ssubset_dom_plural hy)]
  · ext x
    simp [mem_dom_singular, nonAtomsOf]
  · rintro χ (rfl | rfl) hss
    · exact le_rfl
    · exact absurd rfl hss.ne

end Number

/-! ### Gender -/

/-- A gendered entity domain has disjoint sets of referents gendered masculine and gendered
feminine, as socially constituted. Grammatical gender presupposes it, and a referent may be
gendered neither way. -/
class Gendered (E : Type*) where
  /-- The referents gendered masculine. -/
  masculine : Set E
  /-- The referents gendered feminine. -/
  feminine : Set E
  /-- No referent is gendered both ways. -/
  disjoint : Disjoint masculine feminine

namespace Gender

variable {E : Type*} [Gendered E] (x : E)

/-- Over a gendered entity domain, [feminine] is defined of the referents not gendered masculine
and [neuter] of those not gendered feminine. -/
def Feature.dom : Feature → Set E
  | .feminine => Gendered.masculineᶜ
  | .neuter => Gendered.feminineᶜ

/-- Over a gendered entity domain, the feminine is defined of the referents not gendered
masculine and the neuter of those gendered neither way; the masculine, an absent value and the
common gender restrict nothing. -/
def dom (g : Option UD.Gender) : Set E :=
  (g.bind Features.ofUD).elim Set.univ (·.inf Feature.dom)

@[simp] theorem dom_none : dom (E := E) none = Set.univ := rfl

@[simp] theorem mem_dom_neuter :
    x ∈ dom (some .Neut) ↔ x ∉ Gendered.masculine ∧ x ∉ Gendered.feminine := by
  simp [dom, Features.ofUD, Features.neuter_eq, Feature.dom]

@[simp] theorem mem_dom_feminine : x ∈ dom (some .Fem) ↔ x ∉ Gendered.masculine := by
  simp [dom, Features.ofUD, Features.feminine_eq, Feature.dom]

@[simp] theorem dom_masculine : dom (E := E) (some .Masc) = Set.univ := by
  simp [dom, Features.ofUD, Features.masculine]

/-- The neuter domain lies inside the feminine one, the containment `[+neuter] → [+feminine]` of
the decomposition as a fact about referents. -/
theorem dom_neuter_subset_dom_feminine :
    dom (E := E) (some .Neut) ⊆ dom (some .Fem) :=
  Finset.inf_mono (by decide : Features.feminine ⊆ Features.neuter)

end Gender
