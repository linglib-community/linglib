module

public import Linglib.Syntax.Case.Dependent
public import Linglib.Fragments.HindiUrdu.Case
public import Linglib.Data.Examples.Baker2015
public import Linglib.Data.Examples.Readers

/-!
# Baker 2015: dependent case

Structural case cannot in general be read off agreement with a functional head: ergative
languages let the finite verb agree with ergative and absolutive subjects alike, and the
subject must already be ergative before Agree applies. In Kewa and Burushaski the verb agrees
with both subjects alike, and only a rule reading the NP the transitive subject c-commands can
[mark the two apart](##ergative_independent_of_agreement). The book takes up Marantz's dependent
case instead. In a spell-out domain, an NP with lexically governed case keeps it; of two
distinct caseless NPs one of which c-commands the other, the lower is valued accusative or the
higher ergative — which of these a language does is its alignment parameter, and a tripartite
language does both; whatever remains is unmarked, nominative in the clause and genitive in the
noun phrase. Sakha, Shipibo and Nez Perce show the three settings on the simplest transitive
and intransitive clauses, and the twenty-odd languages the book studies in depth sort into
those columns together with marked-nominative and marked-absolutive systems, which differ in
how the unmarked case is realized.

## Main definitions

* `alignment?`: the book's sorting of its languages by alignment type.
* `Observed`, `Realizes`: the case a gloss shows, and when the algorithm's output realizes it.
* `rows_case`: the book's introductory clauses, each derived by `assignCases` from its
  alignment type.

## Implementation notes

The rows record no aspect. Urdu's alignment is split by aspect (`HindiUrdu.alignment`), and
both of its clauses (25) are perfective, glossed PRF, so they are read on the ergative side of
the split.

## References

* [baker-2015]
* [marantz-1991] — the disjunctive hierarchy and dependent case
* [baker-vinokurova-2010] — the c-command formulation
-/

@[expose] public section

namespace Baker2015

open Case DependentCase

/-- The book's languages of focus by alignment type: accusative Sakha, Tamil, Amharic, Cuzco
    Quechua, Korean and Finnish; ergative Shipibo, Burushaski, Chukchi, Lezgian, Ingush,
    Greenlandic, Kewa and Wardaman; tripartite Nez Perce, Coast Tsimshian, Semelai, Diyari and
    Warlpiri; and Urdu, split by aspect, in the perfective of its clauses (25). The
    marked-nominative and marked-absolutive languages differ in the realization of the unmarked
    case, which the algorithm does not fix. -/
def alignment? : String → Option Alignment.AlignmentType
  | "yaku1245" | "tami1289" | "amha1245" | "cusc1236" | "kore1280" | "finn1318" =>
    some .accusative
  | "ship1254" | "buru1296" | "chuk1273" | "lezg1247" | "ingu1240" | "kala1399" | "west2599"
  | "ward1246" => some .ergative
  | "nezp1238" | "coas1300" | "seme1247" | "dier1241" | "warl1254" => some .tripartite
  | "urdu1245" => some (HindiUrdu.alignment .perfective)
  | _ => none

/-- The case a gloss shows: a dependent case, or an unmarked form — nominative, absolutive,
    or no marking at all. -/
inductive Observed
  | erg
  | acc
  | unmarked
  deriving DecidableEq, Repr

/-- The gloss labels of the book's examples. -/
def Observed.parse? : String → Option Observed
  | "ERG" => some .erg
  | "ACC" => some .acc
  | "NOM" | "ABS" | "unmarked" => some .unmarked
  | _ => none

/-- An assigned case realizes an observed one: the dependent cases as themselves, and the
    unmarked case as whatever label the language gives it. -/
def Realizes (c : Case) (src : Mechanism) : Observed → Prop
  | .erg => c = .erg ∧ src = .dependent
  | .acc => c = .acc ∧ src = .dependent
  | .unmarked => src = .unmarked

instance (c : Case) (src : Mechanism) (o : Observed) : Decidable (Realizes c src o) := by
  cases o <;> simp only [Realizes] <;> infer_instance

/-- The arguments of a clause. -/
inductive Arg
  | subject
  | object
  deriving DecidableEq, Repr

/-- The feature a row records an argument's case under. -/
def Arg.feature : Arg → String
  | .subject => "subjectCase"
  | .object => "objectCase"

/-- The arguments of a row's clause, subject first: it c-commands the object. -/
def domain (r : Datum) : List Arg :=
  .subject :: if r.feature? "transitive" = some "yes" then [.object] else []

/-- The observed case of a row's argument. -/
def observed? (r : Datum) (np : Arg) : Option Observed :=
  (r.feature? np.feature).bind Observed.parse?

/-- Every clause the book introduces its languages with is derived by the algorithm from the
    language's alignment type: the ergative and accusative NPs are the dependent-case NPs and
    the nominative, absolutive and unmarked NPs the leftovers. -/
theorem rows_case :
    ∀ r ∈ Examples.all, ∀ lang ∈ alignment? r.language, ∀ np ∈ [Arg.subject, .object],
      ∀ o ∈ observed? r np, ∀ v ∈ (assignCases lang (fun _ ↦ none) (domain r)).valueOf np,
        Realizes v.1 v.2 o := by
  decide

-- (22), (23)
theorem subject_case_of_same_agreement : ∀ r ∈ Examples.all, ∀ r' ∈ Examples.all,
    r.feature? "transitive" = some "no" → r'.feature? "transitive" = some "yes" →
    r.language = r'.language → r.feature? "subjectAgreement" = some "yes" →
    r'.feature? "subjectAgreement" = some "yes" →
    observed? r .subject = some .unmarked ∧ observed? r' .subject = some .erg := by
  decide

private theorem valueOf_subject_of_high_eq_none {g : Rules} (hg : g.high = none) :
    (g.assign (fun _ : Arg ↦ none) [.subject, .object]).valueOf .subject =
      g.unmarked.map (·, .unmarked) := by
  obtain ⟨hi, lo, un⟩ := g
  dsimp only at hg
  subst hg
  cases lo <;> cases un <;> rfl

/-- Case is not read off agreement: where the verb agrees with an intransitive and a transitive
    subject alike, as in Kewa (22) and Burushaski (23), only the transitive subject is ergative,
    and no rules without a high case derive it: they give it the elsewhere case, marking it as
    they mark an intransitive subject (`Rules.marking_S_eq_marking_A_iff`). -/
theorem ergative_independent_of_agreement {r r' : Datum} (hr : r ∈ Examples.all)
    (hr' : r' ∈ Examples.all) (ht : r.feature? "transitive" = some "no")
    (ht' : r'.feature? "transitive" = some "yes") (hl : r.language = r'.language)
    (ha : r.feature? "subjectAgreement" = some "yes")
    (ha' : r'.feature? "subjectAgreement" = some "yes") {g : Rules} (hg : g.high = none) :
    observed? r .subject ≠ observed? r' .subject ∧
      ∀ o ∈ observed? r' .subject,
        ∀ v ∈ (g.assign (fun _ ↦ none) (domain r')).valueOf .subject, ¬ Realizes v.1 v.2 o := by
  obtain ⟨h, h'⟩ := subject_case_of_same_agreement r hr r' hr' ht ht' hl ha ha'
  refine ⟨by rw [h, h']; decide, fun o ho v hv hre ↦ ?_⟩
  rw [h', Option.mem_some_iff] at ho
  subst ho
  simp only [domain, ht', ↓reduceIte] at hv
  rw [valueOf_subject_of_high_eq_none hg, Option.mem_def] at hv
  obtain ⟨c, -, rfl⟩ := Option.map_eq_some_iff.1 hv
  simp [Realizes] at hre

end Baker2015
