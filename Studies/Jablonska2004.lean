module

public import Linglib.Semantics.Aspect.Defs
public import Linglib.Data.Examples.Jablonska2004
public import Linglib.Data.Wordlist.Jablonska2004
public import Studies.Svenonius2004

/-!
# Jabłońska (2004): When the Prefixes Meet the Suffixes

Jabłońska explains the readings of the Polish prefix *po-* by the verbalizer of the stem it
attaches to. A derivation stacks the prefix positions of (41) and the Secondary Imperfective as
layers over a stem, each merging only when its selectional requirement is met, and *po-* measures
along the continuum the verbalizer supplies: the run time of a process, the scale of a gradable
property, or a path.

## Main definitions

* `Verbalizer`: the classes of Table 1 and Table 2, with an Aktionsart profile and a continuum.
* `Layer`, `Layer.merge`: the four prefix positions of (41) and the Secondary Imperfective, with
  their selectional requirements.
* `WellFormed`, `Perfective`: every requirement of a derivation is met; its predicate is
  perfective.
* `Stem`: a fragment verb with the verbalizer class the paper assigns it.
* `attested`, `starred`: the paper's analyses of the forms it accepts and rejects.

## Main results

* `wellFormed_iff`: the seven shapes of a well-formed derivation, whence `si_of_asp3`,
  `eq_of_perf`, `denotesInterval_of_si` and Svenonius's stacking generalization, `wellStacked`.
* `asp1Reading_iff_table2`: the readings of *po-* in Asp1 are those of Table 2.
* `attested_wellFormed`, `starred_not_wellFormed`, `attested_readings`: the analyses hold.
* `spells`: the analyses spell out the attested words.
* `stem_perfectivity`, `stem_vendlerClass`: the aspect and the Vendler class the fragment records
  for a stem are those the model derives for it.
* `phaseTests_judgment`, `presentTests_reading`: the perfectivity the model derives predicts the
  judgments of the paper's sentences with a phase verb and in the present tense, by the tests of
  Section 2.1.

## Implementation notes

* The Aktionsart profile of a bare stem is atelic throughout, the paper's unbounded bare stem;
  the semelfactive is the punctual class and the stative the non-dynamic one. The continuum,
  the telos and the adjectival base are the paper's own parameters.
* The semelfactive suffix values [uPerf] against Asp1, (47): a bare semelfactive is perfective,
  and a purely perfectivizing prefix over it is a vacuous viewpoint shift, (70), which Table 2
  hedges as "yes ???" (`wellFormed_perf_iff`). A lexical prefix on a semelfactive stays
  possible in principle, (79a) and fn. 20.
* With directed motion stems the purely perfectivizing position is filled by *do-* or *przy-*,
  Table 2 fn. c; the model records these stems as lacking a telos of their own.
* The "considerable change" reading is confined to *-ej-* stems: fn. 22 records that
  inchoative *-n-* stems lack it without deriving the gap. The inceptive *za-* of (53) reads an
  *-ej-* stem as a state and is recorded as a row only.
* (24) glosses *prze-* as perfectivizing before the positions of (41) are introduced; with (30) to
  (34) it is the lexical prefix of a stem that forms a Secondary Imperfective.
* In (77) the root of *gasnąć* is redirected to the *-aj-* verbalizer under the Secondary
  Imperfective, so the analysis is over a stem of its own (`gasac`). *pó-jść*, (50a), is not
  analysed, since neither the prefix nor the stem has its citation form there.
* Two forms part with the model, as the paper notes: *po-chadz-a-ć*, (56c), is a gap of the
  unproductive attenuative-frequentative (`gap56c_wellFormed`), and *gr-ywa-ć*, (60), forms a
  Secondary Imperfective without a prefix (`exception60_not_wellFormed`).

## References

* [jablonska-2004]
* [svenonius-2004]
* [demirdache-uribe-etxebarria-2000]
* [rothstein-2004]
-/

@[expose] public section

namespace Jablonska2004

open Morphology Polish.Verbs
open Data.Wordlist (Form)

/-! ### Verbalizers -/

/-- The verbalizer classes of Table 1 and Table 2. -/
inductive Verbalizer
  /-- The high processual verbalizers *-i/y-* and *-aj-*, with root insertion inside ν. -/
  | processual
  /-- The high instantaneous verbalizer, semelfactive *-n-*. -/
  | semelfactive
  /-- The low verbalizer *-ej-*, forming a degree achievement over an adjectival base, (2b). -/
  | degree
  /-- The low inchoative verbalizer *-n-*, (2a). -/
  | inchoative
  /-- A directed-motion stem, measuring movement along a path, (55). -/
  | directedMotion
  /-- A non-directed-motion stem, a high processual verbalizer, (49). -/
  | nonDirectedMotion
  /-- A stative stem. -/
  | stative
  deriving DecidableEq

/-- The continuum along which *po-* measures development, (40). -/
inductive Continuum
  | temporal
  | degree
  | path
  deriving DecidableEq

namespace Verbalizer

/-- The Aktionsart profile of a bare stem is atelic, lacking a right boundary, Section 2.3; it is
punctual for the semelfactive, Section 2.3.1, and stative for the statives, which lack a left
boundary, Section 5. -/
def profile : Verbalizer → Aspect.VendlerClass
  | semelfactive => .semelfactive
  | stative => .state
  | _ => .activity

/-- The continuum a verbalizer supplies; a semelfactive is a point and supplies none. -/
def continuum : Verbalizer → Option Continuum
  | processual | nonDirectedMotion | stative => some .temporal
  | degree | inchoative => some .degree
  | directedMotion => some .path
  | semelfactive => none

/-- A punctual stem has no continuum to measure along, (45). -/
def IsPunctual (v : Verbalizer) : Prop := v.profile.duration = .punctual

instance : DecidablePred IsPunctual := fun v ↦ inferInstanceAs (Decidable (v.profile.duration = _))

/-- Dynamic eventualities come with a left boundary, the preceding state at which the event does
not hold, Section 2.3; states do not. -/
def HasLeftBoundary (v : Verbalizer) : Prop := v.profile.dynamicity = .dynamic

instance : DecidablePred HasLeftBoundary :=
  fun v ↦ inferInstanceAs (Decidable (v.profile.dynamicity = _))

/-- The stem has a natural telos for a purely perfectivizing prefix to coincide with, (10), the
end of the scale of a gradable property or the change of state of the affected object of a
processual verb, Section 2.2. -/
def HasTelos (v : Verbalizer) : Prop := v = processual ∨ v = degree ∨ v = inchoative

instance : DecidablePred HasTelos := fun v ↦ inferInstanceAs (Decidable (v = _ ∨ v = _ ∨ v = _))

/-- The stem has an adjectival base in its derivational history, (2b) and (72), and so no Result
phrase. -/
def IsAdjectival (v : Verbalizer) : Prop := v = degree

instance : DecidablePred IsAdjectival := fun v ↦ inferInstanceAs (Decidable (v = _))

/-- Denotes a delimitable interval, the selectional requirement of the Secondary Imperfective,
(66): a temporal continuum and a left boundary. -/
def DenotesInterval (v : Verbalizer) : Prop := v.continuum = some .temporal ∧ v.HasLeftBoundary

instance : DecidablePred DenotesInterval :=
  fun v ↦ inferInstanceAs (Decidable (v.continuum = _ ∧ v.HasLeftBoundary))

@[simp] theorem isPunctual_iff (v : Verbalizer) : v.IsPunctual ↔ v = semelfactive := by
  cases v <;> decide

@[simp] theorem hasLeftBoundary_iff (v : Verbalizer) : v.HasLeftBoundary ↔ v ≠ stative := by
  cases v <;> decide

@[simp] theorem isAdjectival_iff (v : Verbalizer) : v.IsAdjectival ↔ v = degree := Iff.rfl

@[simp] theorem hasTelos_iff (v : Verbalizer) :
    v.HasTelos ↔ v = processual ∨ v = degree ∨ v = inchoative := Iff.rfl

@[simp] theorem denotesInterval_iff (v : Verbalizer) :
    v.DenotesInterval ↔ v = processual ∨ v = nonDirectedMotion := by
  cases v <;> decide

end Verbalizer

/-! ### Aspectual layers -/

/-- The aspectual level reached by a derivation, (41). -/
inductive Level
  | root
  | asp1
  | asp2
  | asp3
  deriving DecidableEq

/-- The aspectual profile of the predicate built so far records the highest projection merged,
whether it is [+Perf], bounded by a Reference Time AFTER its Event Time, and whether its delimited
subevents are changes of state of their participants, the contribution of a lexical prefix,
(30), so that iterated subevents can overlap and be S-summed, (36) and (37). -/
structure Profile where
  level : Level
  bounded : Bool
  resultative : Bool
  deriving DecidableEq

/-- The four prefix positions of (41) and the Secondary Imperfective. -/
inductive Layer
  /-- A lexical prefix in the complement of RP, valuing [uPerf] against Asp1. -/
  | lexical (m : Morph)
  /-- A superlexical prefix in Spec,Asp1P, a Reference Time AFTER the Event Time, (40). -/
  | asp1 (m : Morph)
  /-- A purely perfectivizing prefix in Spec,Asp2P, (68). -/
  | perf (m : Morph)
  /-- The Secondary Imperfective, Asp2 with the semantics WITHIN or OUTSIDE, (66). -/
  | si
  /-- *po-* in Spec,Asp3P, above the Secondary Imperfective, (26). -/
  | asp3 (m : Morph)
  deriving DecidableEq

namespace Layer

/-- Merging a layer over a bare stem of class `v` with profile `p`, when the layer's selectional
requirement is met. A lexical prefix needs a Result phrase, (72); *po-* in Asp1 needs a
continuum, (40); both value [uPerf] against Asp1 and cannot co-occur, (42). A purely
perfectivizing prefix in Asp2 needs a telos and an unbounded predicate, since a second Reference
Time AFTER the first is a vacuous viewpoint shift, (70), which also bars it from a semelfactive,
(47). The Secondary Imperfective selects a delimited interval, (32) and (66), in the Asp2 slot,
(68). *po-* in Asp3 selects a [-Perf] predicate, (25), whose iterated subevents are S-summable,
(36), which requires each to be a change of state of its participant, (37) and (61). -/
def merge (v : Verbalizer) : Layer → Profile → Option Profile
  | lexical _, ⟨.root, _, _⟩ => if v.IsAdjectival then none else some ⟨.asp1, true, true⟩
  | asp1 _, ⟨.root, _, _⟩ => if v.IsPunctual then none else some ⟨.asp1, true, false⟩
  | perf _, ⟨.root, _, r⟩ => if ¬ v.IsPunctual ∧ v.HasTelos then some ⟨.asp2, true, r⟩ else none
  | si, ⟨.asp1, _, r⟩ => if v.DenotesInterval then some ⟨.asp2, false, r⟩ else none
  | asp3 _, ⟨.asp2, false, true⟩ => some ⟨.asp3, true, true⟩
  | _, _ => none

/-- The prefix morph of a layer. -/
def prefix? : Layer → Option Morph
  | lexical m | asp1 m | perf m | asp3 m => some m
  | si => none

/-- A lexical prefix. -/
def IsLexical : Layer → Prop
  | lexical _ => True
  | _ => False

instance : DecidablePred IsLexical
  | lexical _ => isTrue trivial
  | asp1 _ | perf _ | si | asp3 _ => isFalse id

end Layer

/-! ### Derivations -/

/-- The profile after merging the layers `ls`, innermost first, in turn over profile `p`. -/
def profileFrom (v : Verbalizer) (p : Profile) (ls : List Layer) : Option Profile :=
  ls.foldlM (fun p l ↦ l.merge v p) p

@[simp] theorem profileFrom_nil (v : Verbalizer) (p : Profile) : profileFrom v p [] = some p :=
  rfl

@[simp] theorem profileFrom_cons (v : Verbalizer) (p : Profile) (l : Layer) (ls : List Layer) :
    profileFrom v p (l :: ls) = (l.merge v p).bind (profileFrom v · ls) :=
  rfl

/-- The profile of a derivation over a bare stem of class `v`. -/
def profile (v : Verbalizer) (ls : List Layer) : Option Profile :=
  profileFrom v ⟨.root, false, false⟩ ls

/-- A derivation is well-formed when every layer's selectional requirement is met. -/
def WellFormed (v : Verbalizer) (ls : List Layer) : Prop := (profile v ls).isSome

instance (v : Verbalizer) (ls : List Layer) : Decidable (WellFormed v ls) :=
  inferInstanceAs (Decidable (_ = true))

/-- The derived predicate is [+Perf]: bounded by a Reference Time, or a bare semelfactive, whose
suffix values [uPerf] against Asp1, (47). It is then no complement of a phasal verb and has no
present-tense interpretation, the tests of Section 2.1. -/
def Perfective (v : Verbalizer) (ls : List Layer) : Prop :=
  match profile v ls with
  | some p => p.bounded = true ∨ v.IsPunctual
  | none => False

instance (v : Verbalizer) (ls : List Layer) : Decidable (Perfective v ls) := by
  unfold Perfective; split <;> infer_instance

@[local simp] private theorem bind_ite_none_left {α β : Type*} {c : Prop} [Decidable c]
    {a : α} {f : α → Option β} : (if c then none else some a).bind f = if c then none else f a := by
  split_ifs <;> rfl

@[local simp] private theorem bind_ite_none_right {α β : Type*} {c : Prop} [Decidable c]
    {a : α} {f : α → Option β} : (if c then some a else none).bind f = if c then f a else none := by
  split_ifs <;> rfl

/-- A well-formed derivation has one of seven shapes: a bare stem; a lexical prefix, (30); *po-* in
Asp1, (27); a purely perfectivizing prefix, (67); a lexically prefixed or Asp1-delimited stem
under the Secondary Imperfective, (31a) and (56); and *po-* in Asp3 over a lexically prefixed
Secondary Imperfective, (34). -/
theorem wellFormed_iff {v : Verbalizer} {ls : List Layer} :
    WellFormed v ls ↔
      ls = [] ∨
      (∃ m, ls = [.lexical m] ∧ ¬ v.IsAdjectival) ∨
      (∃ m, ls = [.asp1 m] ∧ ¬ v.IsPunctual) ∨
      (∃ m, ls = [.perf m] ∧ ¬ v.IsPunctual ∧ v.HasTelos) ∨
      (∃ m, ls = [.lexical m, .si] ∧ ¬ v.IsAdjectival ∧ v.DenotesInterval) ∨
      (∃ m, ls = [.asp1 m, .si] ∧ ¬ v.IsPunctual ∧ v.DenotesInterval) ∨
      (∃ m m', ls = [.lexical m, .si, .asp3 m'] ∧ ¬ v.IsAdjectival ∧ v.DenotesInterval) := by
  constructor
  · intro h
    obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1 h
    clear h
    rcases ls with _ | ⟨a, ls⟩
    · exact Or.inl rfl
    cases a <;> simp_all [profile, Layer.merge] <;>
      rcases ls with _ | ⟨b, ls⟩ <;> simp_all [Layer.merge] <;>
      cases b <;> simp_all <;>
      rcases ls with _ | ⟨c, ls⟩ <;> simp_all [Layer.merge]
    cases c <;> simp_all
    rcases ls with _ | ⟨d, ls⟩ <;> simp_all [Layer.merge]
  · rintro (rfl | ⟨m, rfl, h⟩ | ⟨m, rfl, h⟩ | ⟨m, rfl, h₁, h₂⟩ | ⟨m, rfl, h₁, h₂⟩ |
        ⟨m, rfl, h₁, h₂⟩ | ⟨m, m', rfl, h₁, h₂⟩) <;>
      simp_all [WellFormed, profile, Layer.merge]

/-- The seven shapes, as a case split on a well-formedness hypothesis. -/
local macro "shapes" h:term : tactic =>
  `(tactic| rcases wellFormed_iff.1 $h with rfl | ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ | ⟨_, rfl, _, _⟩ |
      ⟨_, rfl, _, _⟩ | ⟨_, rfl, _, _⟩ | ⟨_, _, rfl, _, _⟩)

/-! ### The paper's generalizations -/

section Generalizations

variable {v : Verbalizer} {ls : List Layer} {m m' : Morph}

/-- A bare stem is perfective exactly when it is a semelfactive, (46). -/
theorem perfective_nil_iff : Perfective v [] ↔ v.IsPunctual := by
  simp [Perfective, profile]

/-- Stacking is contingent on the Secondary Imperfective, Section 5: *po-* in Asp3 stacks only
over a secondary imperfective, (24) and (42), and never over an attenuative-frequentative, (61). -/
theorem si_of_asp3 (h : WellFormed v ls) (hm : .asp3 m ∈ ls) :
    ∃ m', ls = [.lexical m', .si, .asp3 m] := by
  shapes h <;> simp_all

/-- A purely perfectivizing prefix stacks on nothing and nothing stacks on it, (70): it is in
complementary distribution with the Secondary Imperfective, (67), (69) and (68). -/
theorem eq_of_perf (h : WellFormed v ls) (hm : .perf m ∈ ls) : ls = [.perf m] := by
  shapes h <;> simp_all

/-- Only the interval-denoting classes, the processual and the non-directed motion stems, form
Secondary Imperfectives: not the degree achievements, (59) and (74), the inchoatives, (76), the
semelfactives, (48) and (79b), the directed motion stems, (80), or the statives. -/
theorem denotesInterval_of_si (h : WellFormed v ls) (hm : .si ∈ ls) : v.DenotesInterval := by
  shapes h <;> simp_all

/-- A lexical prefix and *po-* in Asp1 both value [uPerf] against Asp1, so they do not co-occur,
(42): no Multiple Agree. -/
theorem not_lexical_and_asp1 (h : WellFormed v ls) : ¬ (.lexical m ∈ ls ∧ .asp1 m' ∈ ls) := by
  shapes h <;> simp_all

/-- *po-* in Asp3 makes the derivation perfective, (33). -/
theorem perfective_of_asp3 (h : WellFormed v ls) (hm : .asp3 m ∈ ls) : Perfective v ls := by
  shapes h <;> cases v <;> simp_all [Perfective, profile, Layer.merge]

/-- A derivation closed by the Secondary Imperfective is imperfective: the
attenuative-frequentative forms, (56) and (64), are imperfectives, and Asp3 *po-* selects for
[-Perf], (25). -/
theorem not_perfective_of_getLast_si (h : WellFormed v ls) (hl : ls.getLast? = some .si) :
    ¬ Perfective v ls := by
  shapes h <;> cases v <;> simp_all [Perfective, profile, Layer.merge]

/-- The prefix sequence of a derivation, outermost first, under any classification `f` that
agrees with the lexical/superlexical split, is well-stacked in the sense of [svenonius-2004]:
the superlexical prefix is always outside the lexical one. -/
theorem wellStacked (h : WellFormed v ls) (f : Layer → Svenonius2004.PrefixClass)
    (hf : ∀ l, (f l).IsSuperlexical ↔ ¬ l.IsLexical) :
    Svenonius2004.WellStacked (ls.reverse.filterMap fun l ↦ l.prefix?.map (·, f l)) := by
  shapes h <;> simp_all [Svenonius2004.WellStacked, Layer.prefix?, Layer.IsLexical]

end Generalizations

/-! ### Table 2 -/

section Table2

variable (v : Verbalizer) (m : Morph)

/-- In the Asp2 column of Table 2, a purely perfectivizing prefix needs a telos, (10) and (67),
which the motion stems and the statives lack, and an unbounded stem, which the semelfactive is
not, (47), so the cell Table 2 hedges as "yes ???" is closed. -/
theorem wellFormed_perf_iff :
    WellFormed v [.perf m] ↔ v = .processual ∨ v = .degree ∨ v = .inchoative := by
  cases v <;> simp [wellFormed_iff]

/-- In the Secondary Imperfective column of Table 2, the stems that form one are the processual
and non-directed motion stems, which are also the classes on which *po-* stacks in Asp3, (43)
and (83). -/
theorem wellFormed_lexical_si_iff :
    WellFormed v [.lexical m, .si] ↔ v = .processual ∨ v = .nonDirectedMotion := by
  cases v <;> simp [wellFormed_iff]

end Table2

/-! ### Readings -/

/-- The readings of superlexical *po-*. -/
inductive Reading
  /-- *po-* 'for a while' sets an arbitrary Reference Time, short of any telos, (12) and (27). -/
  | delimitative
  /-- A degree of change short of the end of the scale, (11) and (22). -/
  | considerableChange
  /-- *po-* 'away' measures the ground covered along the path, (50). -/
  | centrifugal
  /-- A Reference Time after the last of the S-summed subevents, one per atom of the plural
  internal argument, each reaching its telos, (23) and (28). -/
  | distributive
  /-- A Reference Time BEFORE the Event Time, fixing the missing left boundary of a state,
  (54). -/
  | inceptive
  deriving DecidableEq

/-- The readings of *po-* in Spec,Asp1P on a stem of class `v`, `plural` the plurality of the
internal argument: the reading measures along the stem's continuum, (40); the distributive
reading S-sums one subevent per atom of a plural internal argument, each with its telos, (36);
and the inceptive reading fixes a left boundary the stem lacks, Section 2.4. -/
def Asp1Reading (v : Verbalizer) (plural : Bool) : Reading → Prop
  | .delimitative => v.continuum = some .temporal
  | .considerableChange => v = .degree
  | .centrifugal => v.continuum = some .path
  | .distributive => plural = true ∧ v.HasTelos
  | .inceptive => ¬ v.HasLeftBoundary

instance (v : Verbalizer) (plural : Bool) : DecidablePred (Asp1Reading v plural) := fun r ↦ by
  cases r <;> unfold Asp1Reading <;> infer_instance

/-- The reading of *po-* in Spec,Asp3P, (34), is delimitative when the third Reference Time falls
WITHIN the inherited first one, and distributive when it follows the last iterated subevent,
which needs a plural internal argument, (28e). -/
def Asp3Reading (plural : Bool) : Reading → Prop
  | .delimitative => True
  | .distributive => plural = true
  | _ => False

instance (plural : Bool) : DecidablePred (Asp3Reading plural) := fun r ↦ by
  cases r <;> unfold Asp3Reading <;> infer_instance

/-- The Asp1 column of Table 2. -/
def table2Asp1 : Verbalizer → List Reading
  | .processual => [.delimitative, .distributive]
  | .semelfactive => []
  | .degree => [.distributive, .considerableChange]
  | .inchoative => [.distributive]
  | .directedMotion => [.centrifugal]
  | .nonDirectedMotion => [.delimitative]
  | .stative => [.inceptive, .delimitative]

/-- The derived readings of *po-* in Asp1, with a plural internal argument, are those of
Table 2: no delimitative reading with the change-of-state stems, Section 5, and the inceptive
reading only with the statives, Section 2.4. -/
theorem asp1Reading_iff_table2 (v : Verbalizer) (r : Reading) :
    Asp1Reading v true r ↔ r ∈ table2Asp1 v := by
  cases v <;> cases r <;> decide

/-- Without a plural internal argument the distributive reading is gone: (28c) has only the
delimitative reading, the external argument being outside the scope of *po-*, (29). -/
theorem not_asp1Reading_distributive (v : Verbalizer) : ¬ Asp1Reading v false .distributive := by
  simp [Asp1Reading]

/-! ### Stems -/

/-- A stem of the analysis is a fragment verb with the verbalizer class the paper assigns it, so
that the class belongs to the stem and every analysis over the stem shares it. -/
structure Stem where
  /-- The fragment verb. -/
  verb : Verb
  /-- The verbalizer class of Table 1 and Table 2. -/
  verbalizer : Verbalizer

/-- *-gasać* is the *-aj-* stem of the root of *gasnąć*, the high processual verbalizer to which the
root is redirected under the Secondary Imperfective, (77). It occurs only prefixed, as in
*wy-gas-a-ć*, and so has no dictionary aspect of its own. -/
def gasac : Verb where
  morphs := [.root "gasać"]

namespace Stem

/-! The degree achievements in *-ej-*. -/

/-- *siwieć* 'turn grey'. -/
def siwiec : Stem := ⟨Polish.Verbs.siwiec, .degree⟩
/-- *jaśnieć* 'be bright'. -/
def jasniec : Stem := ⟨Polish.Verbs.jasniec, .degree⟩
/-- *ciemnieć* 'get dark'. -/
def ciemniec : Stem := ⟨Polish.Verbs.ciemniec, .degree⟩
/-- *drożeć* 'get expensive'. -/
def drozec : Stem := ⟨Polish.Verbs.drozec, .degree⟩
/-- *babieć* 'become effeminate'. -/
def babiec : Stem := ⟨Polish.Verbs.babiec, .degree⟩
/-- *smutnieć* 'get sad'. -/
def smutniec : Stem := ⟨Polish.Verbs.smutniec, .degree⟩
/-- *dziczeć* 'go wild'. -/
def dziczec : Stem := ⟨Polish.Verbs.dziczec, .degree⟩

/-! The inchoatives in *-n-*. -/

/-- *marznąć* 'freeze'. -/
def marznac : Stem := ⟨Polish.Verbs.marznac, .inchoative⟩
/-- *głuchnąć* 'go deaf'. -/
def gluchnac : Stem := ⟨Polish.Verbs.gluchnac, .inchoative⟩
/-- *więdnąć* 'wither'. -/
def wiednac : Stem := ⟨Polish.Verbs.wiednac, .inchoative⟩
/-- *ślepnąć* 'go blind'. -/
def slepnac : Stem := ⟨Polish.Verbs.slepnac, .inchoative⟩
/-- *gasnąć* 'go out'. -/
def gasnac : Stem := ⟨Polish.Verbs.gasnac, .inchoative⟩

/-! The semelfactives in *-n-*. -/

/-- *warknąć* 'snarl once'. -/
def warknac : Stem := ⟨Polish.Verbs.warknac, .semelfactive⟩
/-- *kopnąć* 'kick once'. -/
def kopnac : Stem := ⟨Polish.Verbs.kopnac, .semelfactive⟩
/-- *machnąć* 'wave once'. -/
def machnac : Stem := ⟨Polish.Verbs.machnac, .semelfactive⟩
/-- *miauknąć* 'meow once'. -/
def miauknac : Stem := ⟨Polish.Verbs.miauknac, .semelfactive⟩
/-- *szepnąć* 'whisper once'. -/
def szepnac : Stem := ⟨Polish.Verbs.szepnac, .semelfactive⟩

/-! The high processual verbalizers *-i/y-* and *-aj-*. -/

/-- *czytać* 'read'. -/
def czytac : Stem := ⟨Polish.Verbs.czytac, .processual⟩
/-- *grać* 'play'. -/
def grac : Stem := ⟨Polish.Verbs.grac, .processual⟩
/-- *palić* 'smoke'. -/
def palic : Stem := ⟨Polish.Verbs.palic, .processual⟩
/-- *chować* 'hide'. -/
def chowac : Stem := ⟨Polish.Verbs.chowac, .processual⟩
/-- *pisać* 'write'. -/
def pisac : Stem := ⟨Polish.Verbs.pisac, .processual⟩
/-- *śpiewać* 'sing'. -/
def spiewac : Stem := ⟨Polish.Verbs.spiewac, .processual⟩
/-- *kopać* 'dig'. -/
def kopac : Stem := ⟨Polish.Verbs.kopac, .processual⟩
/-- *dmuchać* 'blow'. -/
def dmuchac : Stem := ⟨Polish.Verbs.dmuchac, .processual⟩
/-- *szeptać* 'whisper', the non-semelfactive stem of the root of *szepnąć*, (79c). -/
def szeptac : Stem := ⟨Polish.Verbs.szeptac, .processual⟩
/-- *tracić* 'lose'. -/
def tracic : Stem := ⟨Polish.Verbs.tracic, .processual⟩
/-- *robić* 'make'. -/
def robic : Stem := ⟨Polish.Verbs.robic, .processual⟩
/-- *brudzić* 'dirty'. -/
def brudzic : Stem := ⟨Polish.Verbs.brudzic, .processual⟩
/-- *bić* 'beat'. -/
def bic : Stem := ⟨Polish.Verbs.bic, .processual⟩
/-- *chwalić* 'praise'. -/
def chwalic : Stem := ⟨Polish.Verbs.chwalic, .processual⟩
/-- *równać* 'level'. -/
def rownac : Stem := ⟨Polish.Verbs.rownac, .processual⟩
/-- *-gasać*, the root of *gasnąć* redirected to *-aj-*, (77). -/
def gasAj : Stem := ⟨gasac, .processual⟩

/-! The verbs of motion and the statives. -/

/-- *biec* 'run', directed. -/
def biec : Stem := ⟨Polish.Verbs.biec, .directedMotion⟩
/-- *lecieć* 'fly', directed. -/
def leciec : Stem := ⟨Polish.Verbs.leciec, .directedMotion⟩
/-- *ciągnąć* 'drag', directed. -/
def ciagnac : Stem := ⟨Polish.Verbs.ciagnac, .directedMotion⟩
/-- *chodzić* 'walk', non-directed. -/
def chodzic : Stem := ⟨Polish.Verbs.chodzic, .nonDirectedMotion⟩
/-- *biegać* 'run', non-directed. -/
def biegac : Stem := ⟨Polish.Verbs.biegac, .nonDirectedMotion⟩
/-- *latać* 'fly', non-directed. -/
def latac : Stem := ⟨Polish.Verbs.latac, .nonDirectedMotion⟩
/-- *ciągać* 'drag', non-directed. -/
def ciagac : Stem := ⟨Polish.Verbs.ciagac, .nonDirectedMotion⟩
/-- *pływać* 'swim', non-directed. -/
def plywac : Stem := ⟨Polish.Verbs.plywac, .nonDirectedMotion⟩
/-- *siedzieć* 'sit'. -/
def siedziec : Stem := ⟨Polish.Verbs.siedziec, .stative⟩
/-- *kochać* 'love'. -/
def kochac : Stem := ⟨Polish.Verbs.kochac, .stative⟩
/-- *lubić* 'like'. -/
def lubic : Stem := ⟨Polish.Verbs.lubic, .stative⟩

end Stem

/-! ### The paper's analyses -/

/-- An analysis of an attested form gives the form, its stem, the layers innermost first, the
plurality of the internal argument, and the paper's readings of the superlexical *po-*, if any. -/
structure Analysis where
  /-- The attested form. -/
  form : Form UD.MorphFeatures
  /-- The stem the layers are merged over. -/
  stem : Stem
  /-- The layers, innermost first. -/
  layers : List Layer
  /-- Whether the internal argument is plural. -/
  plural : Bool
  /-- The paper's readings of the superlexical *po-*. -/
  readings : List Reading

namespace Analysis

/-- The morphs of the analysed word are the prefixes, outermost first, then the stem. -/
def morphs (a : Analysis) : List Morph :=
  (a.layers.filterMap Layer.prefix?).reverse ++ a.stem.verb.morphs

/-- The reading is available to the superlexical *po-* of the analysis, at Asp3 when the
derivation is closed by *po-* there and at Asp1 otherwise. -/
def Available (a : Analysis) (r : Reading) : Prop :=
  match a.layers.getLast? with
  | some (.asp3 _) => Asp3Reading a.plural r
  | _ => Asp1Reading a.stem.verbalizer a.plural r

instance (a : Analysis) (r : Reading) : Decidable (a.Available r) := by
  unfold Available; split <;> infer_instance

end Analysis

/-- The attested forms are the degree achievements of (3), (8), (10) and (23), the processual stems
of (24), (27), (28), (30), (31), (34) and (43), the inchoatives of (39), the semelfactive of
(46), the motion verbs of (50), (51) and (80), the statives of (54) and fn. 21, the
attenuative-frequentatives of (56) and (65), the purely perfectivized stems of (67) and (69), the
inchoatives of (75), the class shift of (77), the semelfactive and its non-semelfactive stem of
(79), and the lexical *po-* of (81) to (83). -/
def attested : List Analysis :=
  [⟨Wordlist.f_3a, .siwiec, [.asp1 po], false, []⟩,
   ⟨Wordlist.f_3b, .jasniec, [.asp1 po], false, []⟩,
   ⟨Wordlist.f_3d, .smutniec, [.asp1 po], false, []⟩,
   ⟨Wordlist.f_8a, .drozec, [], false, []⟩,
   ⟨Wordlist.f_10a_po, .ciemniec, [.asp1 po], false, [.considerableChange]⟩,
   ⟨Wordlist.f_10a_z, .ciemniec, [.perf z], false, []⟩,
   ⟨Wordlist.f_10b_po, .drozec, [.asp1 po], false, [.considerableChange]⟩,
   ⟨Wordlist.f_10b_z, .drozec, [.perf z], false, []⟩,
   ⟨Wordlist.f_23a, .babiec, [.asp1 po], true, [.distributive]⟩,
   ⟨Wordlist.f_24a, .czytac, [.lexical prze, .si, .asp3 po], true, [.distributive]⟩,
   ⟨Wordlist.f_27a, .czytac, [.asp1 po], false, [.delimitative]⟩,
   ⟨Wordlist.f_27b, .grac, [.asp1 po], false, [.delimitative]⟩,
   ⟨Wordlist.f_27c, .chodzic, [.asp1 po], false, [.delimitative]⟩,
   ⟨Wordlist.f_27d, .palic, [.asp1 po], false, [.delimitative]⟩,
   ⟨Wordlist.f_28a, .chowac, [.asp1 po], true, [.distributive, .delimitative]⟩,
   ⟨Wordlist.f_28b, .pisac, [.lexical prze, .si, .asp3 po], true, [.distributive, .delimitative]⟩,
   ⟨Wordlist.f_28c, .spiewac, [.asp1 po], false, [.delimitative]⟩,
   ⟨Wordlist.f_28d, .chodzic, [.lexical w, .si, .asp3 po], true, [.distributive, .delimitative]⟩,
   ⟨Wordlist.f_30, .pisac, [.lexical prze], false, []⟩,
   ⟨Wordlist.f_31a, .pisac, [.lexical prze, .si], false, []⟩,
   ⟨Wordlist.f_34a, .pisac, [.lexical prze, .si, .asp3 po], true, [.delimitative]⟩,
   ⟨Wordlist.f_34a, .pisac, [.lexical prze, .si, .asp3 po], true, [.distributive]⟩,
   ⟨Wordlist.f_39a, .marznac, [.asp1 po], true, [.distributive]⟩,
   ⟨Wordlist.f_39b, .gluchnac, [.asp1 po], true, [.distributive]⟩,
   ⟨Wordlist.f_39c, .wiednac, [.asp1 po], true, [.distributive]⟩,
   ⟨Wordlist.f_39d, .slepnac, [.asp1 po], true, [.distributive]⟩,
   ⟨Wordlist.f_43a, .kopac, [.lexical ob, .si, .asp3 po], true, [.distributive, .delimitative]⟩,
   ⟨Wordlist.f_46b, .machnac, [], false, []⟩,
   ⟨Wordlist.f_50b, .biec, [.asp1 po], false, [.centrifugal]⟩,
   ⟨Wordlist.f_50c, .leciec, [.asp1 po], false, [.centrifugal]⟩,
   ⟨Wordlist.f_50d, .ciagnac, [.asp1 po], false, [.centrifugal]⟩,
   ⟨Wordlist.f_51b, .biegac, [.asp1 po], false, [.delimitative]⟩,
   ⟨Wordlist.f_51c, .latac, [.asp1 po], false, [.delimitative]⟩,
   ⟨Wordlist.f_51d, .ciagac, [.asp1 po], false, [.delimitative]⟩,
   ⟨Wordlist.f_54a, .kochac, [.asp1 po], false, [.inceptive]⟩,
   ⟨Wordlist.f_54b, .lubic, [.asp1 po], false, [.inceptive]⟩,
   ⟨Wordlist.fn21, .siedziec, [.asp1 po], false, [.delimitative]⟩,
   ⟨Wordlist.f_56b, .grac, [.asp1 po, .si], false, [.delimitative]⟩,
   ⟨Wordlist.f_56d, .palic, [.asp1 po, .si], false, [.delimitative]⟩,
   ⟨Wordlist.f_65a, .dmuchac, [.asp1 po, .si], false, [.delimitative]⟩,
   ⟨Wordlist.f_67a_pf, .tracic, [.perf s], false, []⟩,
   ⟨Wordlist.f_67b_pf, .robic, [.perf z], false, []⟩,
   ⟨Wordlist.f_67c_pf, .chowac, [.perf s], false, []⟩,
   ⟨Wordlist.f_69a_pf, .brudzic, [.perf po], false, []⟩,
   ⟨Wordlist.f_69b_pf, .bic, [.perf po], false, []⟩,
   ⟨Wordlist.f_69c_pf, .chwalic, [.perf po], false, []⟩,
   ⟨Wordlist.f_75a, .gasnac, [.lexical wy], false, []⟩,
   ⟨Wordlist.f_75b, .gasnac, [.perf z], false, []⟩,
   ⟨Wordlist.f_77, .gasAj, [.lexical wy, .si], false, []⟩,
   ⟨Wordlist.f_79a, .szepnac, [.lexical pod], false, []⟩,
   ⟨Wordlist.f_79c, .szeptac, [], false, []⟩,
   ⟨Wordlist.f_79d, .szeptac, [.lexical pod, .si], false, []⟩,
   ⟨Wordlist.f_80b, .plywac, [.lexical do_, .si], false, []⟩,
   ⟨Wordlist.f_81c, .rownac, [.lexical po], false, []⟩,
   ⟨Wordlist.f_82c, .rownac, [.lexical po, .si], false, []⟩,
   ⟨Wordlist.f_83a, .rownac, [.lexical po, .si, .asp3 po], true, [.distributive]⟩]

/-- The starred forms put *po-* in Asp3 over a perfective, (24b); form the Secondary Imperfective
of a bare stem, (32), of a semelfactive, (48) and (79b), of a purely perfectivized stem, (67),
(69), (73) and (78), of a degree achievement, (59) and (74), of a stative, (58c), and of an
inchoative, (76); and put *po-* with a lexical or purely perfectivizing prefix, (42), on a
semelfactive, (45) and (63b), or over an attenuative-frequentative, (61). -/
def starred : List Analysis :=
  [⟨Wordlist.f_24b, .czytac, [.lexical prze, .asp3 po], true, []⟩,
   ⟨Wordlist.f_32a, .robic, [.si], false, []⟩,
   ⟨Wordlist.f_42a, .tracic, [.perf s, .asp1 po], false, []⟩,
   ⟨Wordlist.f_42b, .kopac, [.lexical ob, .asp1 po], false, []⟩,
   ⟨Wordlist.f_45a, .warknac, [.asp1 po], false, []⟩,
   ⟨Wordlist.f_45b, .kopnac, [.asp1 po], false, []⟩,
   ⟨Wordlist.f_45c, .machnac, [.asp1 po], false, []⟩,
   ⟨Wordlist.f_48, .warknac, [.asp1 po, .si], false, []⟩,
   ⟨Wordlist.f_58c, .kochac, [.asp1 po, .si], false, []⟩,
   ⟨Wordlist.f_59a, .siwiec, [.asp1 po, .si], false, []⟩,
   ⟨Wordlist.f_61a, .grac, [.asp1 po, .si, .asp3 po], false, []⟩,
   ⟨Wordlist.f_61b, .palic, [.asp1 po, .si, .asp3 po], false, []⟩,
   ⟨Wordlist.f_63b, .miauknac, [.asp1 po], false, []⟩,
   ⟨Wordlist.f_67a_si, .tracic, [.perf s, .si], false, []⟩,
   ⟨Wordlist.f_67b_si, .robic, [.perf z, .si], false, []⟩,
   ⟨Wordlist.f_67c_si, .chowac, [.perf s, .si], false, []⟩,
   ⟨Wordlist.f_69a_si, .brudzic, [.perf po, .si], false, []⟩,
   ⟨Wordlist.f_69b_si, .bic, [.perf po, .si], false, []⟩,
   ⟨Wordlist.f_69c_si, .chwalic, [.perf po, .si], false, []⟩,
   ⟨Wordlist.f_73a, .dziczec, [.perf z, .si], false, []⟩,
   ⟨Wordlist.f_74, .siwiec, [.asp1 po, .si], false, []⟩,
   ⟨Wordlist.f_76_a, .gasnac, [.lexical wy, .si], false, []⟩,
   ⟨Wordlist.f_76_b, .gasnac, [.lexical wy, .si], false, []⟩,
   ⟨Wordlist.f_78, .gasnac, [.perf z, .si], false, []⟩,
   ⟨Wordlist.f_79b, .szepnac, [.lexical pod, .si], false, []⟩]

/-- The attested forms are accepted and the starred ones rejected. -/
theorem judgments :
    (∀ a ∈ attested, a.form.judgment = .acceptable) ∧
      ∀ a ∈ starred, a.form.judgment = .ungrammatical := by
  decide

/-- Every attested form is a well-formed derivation. -/
theorem attested_wellFormed : ∀ a ∈ attested, WellFormed a.stem.verbalizer a.layers := by decide

/-- Every starred form is excluded. -/
theorem starred_not_wellFormed : ∀ a ∈ starred, ¬ WellFormed a.stem.verbalizer a.layers := by
  decide

/-- The paper's readings of *po-* are the derived ones. -/
theorem attested_readings : ∀ a ∈ attested, ∀ r ∈ a.readings, a.Available r := by decide

/-- A prefixed attested form is imperfective exactly when the Secondary Imperfective closes it. -/
theorem attested_perfective :
    ∀ a ∈ attested, a.layers ≠ [] →
      (Perfective a.stem.verbalizer a.layers ↔ a.layers.getLast? ≠ some .si) := by
  decide

/-- The fragment's aspect of each stem is the perfectivity the model derives for the bare stem:
perfective exactly for the semelfactives, (46). -/
theorem stem_perfectivity : ∀ a ∈ attested ++ starred,
    (a.stem.verb.perfectivity = some .perfective ↔ Perfective a.stem.verbalizer []) := by
  decide

/-- The fragment's Vendler class of a stem, where it records one, is the profile of the stem's
verbalizer: the statives are states and the semelfactives semelfactive. -/
theorem stem_vendlerClass : ∀ a ∈ attested ++ starred,
    a.stem.verb.vendlerClass ∈ [none, some a.stem.verbalizer.profile] := by
  decide

/-- Every infinitive without the Secondary Imperfective spells out its form: the prefixes, outermost
first, and the stem are the morphs of the attested word, accepted or starred. The Secondary
Imperfective replaces the stem's verbalizer, which the fragment's citation forms do not
separate. -/
theorem spells : ∀ a ∈ attested ++ starred, a.form.cell = Wordlist.inf → .si ∉ a.layers →
    Svenonius2004.Spells a.morphs a.form.form := by
  decide

/-! ### The tests of Section 2.1

The paper tests (im)perfectivity in two ways: a phase verb takes only an imperfective complement,
and only an imperfective present-tense form has the actual present reading
(`Aspect.viewpointPrediction`). The perfectivity the model derives for a form predicts the
judgments of the sentences that test it. -/

/-- The perfectivity of the derived predicate. -/
def Analysis.perfectivity (a : Analysis) : Aspect.Perfectivity :=
  if Perfective a.stem.verbalizer a.layers then .perfective else .imperfective

/-- A sentence that tests the perfectivity of a verb form, with the analysis of the form. -/
structure Test where
  /-- The test sentence. -/
  sentence : Datum
  /-- The analysis of the tested form. -/
  verb : Analysis

/-- The phase-verb sentences, *zacząć* 'begin' with *po-prze-pis-ywa-ć*, (33a), and with
*mach-ną-ć*, (46a). -/
def phaseTests : List Test :=
  [⟨Examples.ex_33a, ⟨Wordlist.f_34a, .pisac, [.lexical prze, .si, .asp3 po], true, []⟩⟩,
   ⟨Examples.ex_46a, ⟨Wordlist.f_46a, .machnac, [], false, []⟩⟩]

/-- The present-tense sentences: *po-prze-pis-uj-e-sz*, (33b), and *mach-ni-e-sz*, (46b), read only
as futures, and *do-pływa*, (80b), read as an actual present. -/
def presentTests : List Test :=
  [⟨Examples.ex_33b, ⟨Wordlist.f_33b, .pisac, [.lexical prze, .si, .asp3 po], true, []⟩⟩,
   ⟨Examples.ex_46b, ⟨Wordlist.f_46b, .machnac, [], false, []⟩⟩,
   ⟨Examples.ex_80b, ⟨Wordlist.f_80b, .plywac, [.lexical do_, .si], false, []⟩⟩]

/-- The tested forms are well-formed derivations. -/
theorem tests_wellFormed :
    ∀ t ∈ phaseTests ++ presentTests, WellFormed t.verb.stem.verbalizer t.verb.layers := by
  decide

/-- A phase verb with its complement is accepted exactly when the model derives an imperfective
complement: *po-* in Asp3 and the semelfactive suffix make perfectives, (33a) and (46a). -/
theorem phaseTests_judgment : ∀ t ∈ phaseTests,
    (t.sentence.judgment = .acceptable ↔
      Aspect.viewpointPrediction t.verb.perfectivity = .accept) := by
  decide

/-- A present-tense form has the actual present reading exactly when the model derives an
imperfective: the perfectives of (33b) and (46b) are read as futures, the Secondary Imperfective
of (80b) as an actual present. -/
theorem presentTests_reading : ∀ t ∈ presentTests,
    (t.sentence.readings.lookup "actual present" = some .acceptable ↔
      Aspect.viewpointPrediction t.verb.perfectivity = .accept) := by
  decide

/-! ### The paper's limits

Two forms part with the model, as the paper notes: the attenuative-frequentative is not
productive, so a well-formed derivation can be a gap, and *gr-ywa-ć* is exceptional in forming a
Secondary Imperfective without a prefix. -/

/-- *po-chadz-a-ć*, (56c), which the paper rejects, has *po-* in Asp1 under the Secondary
Imperfective of a non-directed motion stem. -/
def gap56c : Analysis := ⟨Wordlist.f_56c, .chodzic, [.asp1 po, .si], false, []⟩

/-- *gr-ywa-ć*, (60), which the paper accepts, fn. 23, is the Secondary Imperfective of a bare
processual stem. -/
def exception60 : Analysis := ⟨Wordlist.f_60_bare, .grac, [.si], false, []⟩

/-- The gap (56c) is a well-formed derivation: attenuative-frequentative formation is not
productive, (56) to (58), and the paper gives no rule for which stems lack it. -/
theorem gap56c_wellFormed :
    gap56c.form.judgment = .ungrammatical ∧ WellFormed gap56c.stem.verbalizer gap56c.layers := by
  decide

/-- The exception (60) is excluded by the requirement of (32) that the Secondary Imperfective find
a delimited interval. -/
theorem exception60_not_wellFormed :
    exception60.form.judgment = .acceptable ∧
      ¬ WellFormed exception60.stem.verbalizer exception60.layers := by
  decide

end Jablonska2004
