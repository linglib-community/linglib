module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Syntax.Case.Alignment
public import Linglib.Fragments.HindiUrdu.Case
public import Linglib.Semantics.Reference.Animacy
public import Linglib.Semantics.Reference.Nominality
public import Linglib.Data.Examples.Dixon1994

/-!
# Dixon (1994): Ergativity

Dixon analyzes every language in terms of three universal syntactic-semantic relations, S, A
and O (§1.1). A level of grammar is ergative when it treats S like O and unlike A, and accusative
when it treats S like A and unlike O (§8.2). Morphological marking may be split by the verb
(§4.1), by the NP along the Nominal Hierarchy (§4.2), or by tense, aspect or mood (§4.3), and
inter-clausal syntax pivots on S/A or on S/O (Chapter 6).

In an NP-conditioned split, accusative marking of O extends in from the top of the hierarchy and
ergative marking of A from the bottom. The two segments meet, as in Dyirbal and Kuku-Yalanji, or
overlap in a tripartite zone, as in Cashinawa and Yidiny; a gap where neither applies is
unattested, type (g) of the Appendix to Chapter 4. Passive alone feeds an S/A pivot for an NP in
O function and antipassive alone an S/O pivot for one in A function, so a language with a
thoroughgoing S/O pivot must have an antipassive (§6.2.3). English with its S/A pivot passivizes
a clause in which the common NP is O, and Dyirbal with its S/O pivot antipassivizes one in which
it is A (§6.2.2).

## Implementation notes

S, A and O are `ArgumentRole.S`, `.A` and `.P`, following the substrate's Comrie letters, and
a marking of the core relations is any function out of `ArgumentRole`, so that ergativity and
accusativity are the identifications of S the marking makes, `Alignment.IsErgative` and
`Alignment.IsAccusative`. The
Nominal Hierarchy is a linear order with first person at the top; an NP-conditioned split is
a marking conditioned by the position, O accusative and A ergative on two sets of positions,
and its alignment at a position is the substrate's. That the accusative marking is an upper set
and the ergative a lower set is the fit of the split to the hierarchy (`Alignment.Fits`),
proved for each table rather than built into the type. The tables of
§4.2 are given as cutoffs, with the optional accusative of Yidiny's proper names and kin terms
counted as marking; Latin and Waga-Waga, the types with one marking absent or total, are given
directly. Pivots and derivations are the framework of §6.2.1 over core functions, with the
periphery as `none`; the constructions that satisfy a pivot without derivation, such as
Dyirbal's *-ŋurra* and instrumentive, are recorded in the rows only. Not formalized: the
markedness generalizations of §3.4, the bound-versus-free split of §4.2.1, the main-versus-
subordinate split of §4.4, the universal category of subject of Chapter 5, and the mixed
pivots of §6.2.4.

## References

* [dixon-1994]
* [dixon-1972]
* [silverstein-1976]
* [comrie-1978]
-/

@[expose] public section

namespace Dixon1994

open Alignment

variable {κ : Type*}

/-! ### Splits conditioned by the verb, §4.1 -/

/-- A split-S or fluid-S language divides S into two subtypes, Sa, marked like A, and So,
marked like O. -/
inductive SClass
  | sa
  | so
  deriving DecidableEq, Repr

/-- In a fluid-S system (§4.1.2) the S of an instance of use is Sa when its referent controls the
activity and So otherwise. A split-S system (§4.1.1) instead fixes a class for each verb. -/
def fluidS {I : Type*} (control : I → Prop) [DecidablePred control] (i : I) : SClass :=
  if control i then .sa else .so

/-- Under the transitive marking `m`, an S of class `c` is marked like A or like O. -/
def SClass.marking (m : ArgumentRole → κ) : SClass → ArgumentRole → κ
  | c, .S => match c with
    | .sa => m .A
    | .so => m .P
  | _, r => m r

/-- A split system mixes the two simple patterns (§4.1.1), accusative over Sa verbs and ergative
over So verbs, whenever A and O are distinguished. -/
theorem marking_sa_so {m : ArgumentRole → κ} (h : m .A ≠ m .P) :
    IsAccusative (SClass.sa.marking m) ∧ IsErgative (SClass.so.marking m) :=
  ⟨⟨rfl, h⟩, ⟨rfl, h.symm⟩⟩

/-! ### Splits conditioned by the NP: the Nominal Hierarchy, §4.2 -/

/-- The Nominal Hierarchy (Figure 4.5) orders NPs by their likelihood of being in A rather than
in O function, from first person pronouns, second person pronouns, demonstratives and third
person pronouns, and proper names down to common nouns with human, animate and inanimate
reference, the common nouns ordered by the animacy of their referents. -/
inductive Nominal
  | firstPerson
  | secondPerson
  | thirdPerson
  | properName
  | common (a : Animacy)
  deriving DecidableEq, Repr

instance : Fintype Nominal where
  elems := {.firstPerson, .secondPerson, .thirdPerson, .properName, .common .human,
    .common .animate, .common .inanimate}
  complete := by rintro (_ | _ | _ | _ | (_ | _ | _)) <;> decide

/-- Position on the hierarchy, higher to the left. -/
def Nominal.rank : Nominal → ℕ
  | .firstPerson => 6
  | .secondPerson => 5
  | .thirdPerson => 4
  | .properName => 3
  | .common a => a.rank

instance : LinearOrder Nominal := LinearOrder.lift' Nominal.rank (by decide)

/-- The pronoun positions of the Nominal Hierarchy are pronouns, the proper-name position names,
and the rest common nouns. -/
def Nominal.nominality : Nominal → Nominality
  | .firstPerson | .secondPerson | .thirdPerson => .pronoun
  | .properName => .properName
  | .common _ => .commonNoun

theorem Nominal.nominality_monotone : Monotone Nominal.nominality := by
  intro a b; revert a b; decide

variable {H : Type*}

/-- In an NP-conditioned split (§4.2), O is marked accusative at the positions of the hierarchy
where `acc` holds and A ergative where `erg` holds, and S is unmarked. -/
def split (acc erg : H → Prop) [DecidablePred acc] [DecidablePred erg] :
    ArgumentRole → H → Option Case
  | .A, p => if erg p then some .erg else none
  | .P, p => if acc p then some .acc else none
  | _, _ => none

section Split

variable (acc erg : H → Prop) [DecidablePred acc] [DecidablePred erg] (p : H)

@[simp] theorem overt_split_A : overt (split acc erg) .A = {p | erg p} := by
  ext; simp [split]

@[simp] theorem overt_split_P : overt (split acc erg) .P = {p | acc p} := by
  ext; simp [split]

theorem fits_split_iff [Preorder H] :
    Fits (split acc erg) ↔ IsUpperSet {p | acc p} ∧ IsLowerSet {p | erg p} := by
  simp [Fits, and_comm]

theorem isAccusative_split_iff : IsAccusative (split acc erg · p) ↔ acc p ∧ ¬ erg p := by
  by_cases ha : acc p <;> by_cases he : erg p <;> simp [IsAccusative, split, ha, he]

theorem isErgative_split_iff : IsErgative (split acc erg · p) ↔ ¬ acc p ∧ erg p := by
  by_cases ha : acc p <;> by_cases he : erg p <;> simp [IsErgative, split, ha, he]

theorem isTripartite_split_iff : IsTripartite (split acc erg · p) ↔ acc p ∧ erg p := by
  by_cases ha : acc p <;> by_cases he : erg p <;> simp [IsTripartite, split, ha, he]

theorem isNeutral_split_iff : IsNeutral (split acc erg · p) ↔ ¬ acc p ∧ ¬ erg p := by
  by_cases ha : acc p <;> by_cases he : erg p <;> simp [IsNeutral, split, ha, he]

variable {acc erg p} {q : H}

theorem IsAccusative.of_le [Preorder H] (h : Fits (split acc erg))
    (hp : IsAccusative (split acc erg · p)) (hpq : p ≤ q) : IsAccusative (split acc erg · q) := by
  rw [fits_split_iff] at h
  rw [isAccusative_split_iff] at *
  exact ⟨h.1 hpq hp.1, fun hq ↦ hp.2 (h.2 hpq hq)⟩

theorem IsErgative.of_le [Preorder H] (h : Fits (split acc erg))
    (hq : IsErgative (split acc erg · q)) (hpq : p ≤ q) : IsErgative (split acc erg · p) := by
  rw [fits_split_iff] at h
  rw [isErgative_split_iff] at *
  exact ⟨fun hp ↦ hq.1 (h.1 hpq hp), h.2 hpq hq.2⟩

/-- In a split that fits, an overlap of the two markings and a gap between them exclude each
other, so a split is of type (d) of the Appendix to Chapter 4 or of the unattested type (g),
never both. -/
theorem not_isTripartite_and_isNeutral [LinearOrder H] (h : Fits (split acc erg))
    (ht : IsTripartite (split acc erg · p)) (hn : IsNeutral (split acc erg · q)) : False := by
  rw [fits_split_iff] at h
  rw [isTripartite_split_iff] at ht
  rw [isNeutral_split_iff] at hn
  rcases le_total p q with hpq | hqp
  · exact hn.1 (h.1 hpq ht.1)
  · exact hn.2 (h.2 hqp ht.2)

end Split

/-- The split with accusative marking from the top of the hierarchy down to `a` and ergative
marking from the bottom up to `e`. -/
def ofCutoffs [Preorder H] [DecidableLE H] (a e : H) : ArgumentRole → H → Option Case :=
  split (a ≤ ·) (· ≤ e)

theorem fits_ofCutoffs [Preorder H] [DecidableLE H] (a e : H) : Fits (ofCutoffs a e) :=
  (fits_split_iff _ _).2 ⟨isUpperSet_Ici a, isLowerSet_Iic e⟩

/-- Dyirbal (Table 4.1) marks first and second person pronouns accusatively and NPs from third
person pronouns rightwards ergatively, the two meeting without overlap. -/
def dyirbal : ArgumentRole → Nominal → Option Case := ofCutoffs .secondPerson .thirdPerson

/-- Cashinawa (Table 4.2) marks NPs down to third person pronouns accusatively and from third
person pronouns rightwards ergatively, the two overlapping there. -/
def cashinawa : ArgumentRole → Nominal → Option Case := ofCutoffs .thirdPerson .thirdPerson

/-- Yidiny (Table 4.3) marks NPs down to proper names and kin terms accusatively and from human
deictics rightwards ergatively, the two overlapping over the middle of the hierarchy. -/
def yidiny : ArgumentRole → Nominal → Option Case := ofCutoffs .properName .thirdPerson

/-- Latin, of type (a), marks pronouns and masculine and feminine nouns accusatively and has no
ergative, so that neuter nouns have one form for S, A and O. -/
def latin : ArgumentRole → Nominal → Option Case := split (.common .human ≤ ·) (fun _ ↦ False)

/-- Waga-Waga, of type (f) (fn. 14), marks every NP constituent ergatively and NPs down to human
common nouns accusatively, so that the left and middle of the hierarchy are tripartite. -/
def wagaWaga : ArgumentRole → Nominal → Option Case := split (.common .human ≤ ·) (fun _ ↦ True)

/-- Every split of §4.2 fits the Nominal Hierarchy. -/
theorem splits_fit : Fits dyirbal ∧ Fits cashinawa ∧ Fits yidiny ∧ Fits latin ∧ Fits wagaWaga :=
  ⟨fits_ofCutoffs _ _, fits_ofCutoffs _ _, fits_ofCutoffs _ _,
    (fits_split_iff _ _).2 ⟨isUpperSet_Ici _, isLowerSet_empty⟩,
    (fits_split_iff _ _).2 ⟨isUpperSet_Ici _, isLowerSet_univ⟩⟩

/-- The cutoffs induce the alignments of the types. Dyirbal's markings meet at third person
pronouns, type (c); Cashinawa and Yidiny overlap in tripartite zones, type (d); Latin leaves
neuter nouns neutral, type (a); and Waga-Waga is tripartite down to human nouns and ergative
below, type (f). -/
theorem patterns :
    (∀ p, ¬ IsTripartite (dyirbal · p) ∧ ¬ IsNeutral (dyirbal · p)) ∧
      IsAccusative (dyirbal · .secondPerson) ∧ IsErgative (dyirbal · .thirdPerson) ∧
      IsTripartite (cashinawa · .thirdPerson) ∧ IsErgative (cashinawa · .properName) ∧
      IsTripartite (yidiny · .thirdPerson) ∧ IsTripartite (yidiny · .properName) ∧
      IsErgative (yidiny · (.common .human)) ∧ IsNeutral (latin · (.common .animate)) ∧
      IsTripartite (wagaWaga · (.common .human)) ∧
      IsErgative (wagaWaga · (.common .animate)) := by
  decide

/-! ### Splits conditioned by tense, aspect or mood, §4.3 -/

/-- An aspect-conditioned split is aspect-oriented when, as Dixon generalizes, the ergative
marking is found in the perfective and never in the imperfective alone. -/
def AspectOriented (s : Aspect.Perfectivity → AlignmentType) : Prop :=
  s .imperfective = .ergative → s .perfective = .ergative

theorem aspectOriented_hindi : AspectOriented HindiUrdu.alignment := fun h ↦ nomatch h

/-! ### Passive, antipassive and pivots, §6.1 and §6.2 -/

/-- A pivot (§6.2) is the pair of functions an NP common to two linked clauses must bear in each,
S or A in a language with accusative syntax and S or O in one with ergative syntax. -/
inductive Pivot
  | SA
  | SO
  deriving DecidableEq, Repr, Fintype

/-- Whether a core function is a pivot function. -/
def Pivot.Admits : Pivot → ArgumentRole → Prop
  | .SA, .S | .SA, .A => True
  | .SO, .S | .SO, .P => True
  | _, _ => False

instance (π : Pivot) (r : ArgumentRole) : Decidable (π.Admits r) := by
  cases π <;> cases r <;> unfold Pivot.Admits <;> infer_instance

/-- The two derivations of §6.1, each forming an intransitive from a transitive clause. -/
inductive Derivation
  | passive
  | antipassive
  deriving DecidableEq, Repr, Fintype

/-- `d.apply r` is the function the derivation `d` gives the core function `r`. Passive puts O
into S and A into the periphery, antipassive puts A into S and O into the periphery, and the
ditransitive roles are peripheral. -/
def Derivation.apply : Derivation → ArgumentRole → Option ArgumentRole
  | .passive, .P => some .S
  | .antipassive, .A => some .S
  | _, .S => some .S
  | _, _ => none

/-- A derivation feeds a pivot for an NP in function `r` when the derived function is a pivot
function. -/
def Feeds (π : Pivot) (d : Derivation) (r : ArgumentRole) : Prop :=
  ∃ g, d.apply r = some g ∧ π.Admits g

theorem not_admits_iff :
    (∀ r ∈ ArgumentRole.core, ¬ Pivot.SA.Admits r ↔ r = .P) ∧
      ∀ r ∈ ArgumentRole.core, ¬ Pivot.SO.Admits r ↔ r = .A := by
  decide

/-- Passive alone feeds an S/A pivot for an NP in O function, and antipassive alone feeds an
S/O pivot for an NP in A function, §6.2.1 and §6.2.2; each derivation demotes the other
function to the periphery. So a language with a thoroughgoing S/O pivot must have an
antipassive, §6.2.3. -/
theorem feeds_iff :
    (∀ d, Feeds .SA d .P ↔ d = .passive) ∧ (∀ d, Feeds .SO d .A ↔ d = .antipassive) ∧
      ¬ Feeds .SA .passive .A ∧ ¬ Feeds .SO .antipassive .P :=
  ⟨fun d ↦ by cases d <;> simp [Feeds, Derivation.apply, Pivot.Admits],
    fun d ↦ by cases d <;> simp [Feeds, Derivation.apply, Pivot.Admits],
    (fun ⟨_, h, _⟩ ↦ nomatch h), fun ⟨_, h, _⟩ ↦ nomatch h⟩

/-- Interchange A and O, leaving S and the ditransitive roles alone. -/
def swapAO : ArgumentRole → ArgumentRole
  | .A => .P
  | .P => .A
  | r => r

/-- Passive and antipassive are parallel with A and O interchanged, §6.1. -/
theorem apply_swapAO (r : ArgumentRole) :
    Derivation.passive.apply r = Derivation.antipassive.apply (swapAO r) := by
  cases r <;> rfl

end Dixon1994
