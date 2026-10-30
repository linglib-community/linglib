module

public import Linglib.Data.Examples.AlokBhalla2026
public import Linglib.Fragments.Basque.Pronouns
public import Linglib.Fragments.Magahi.Pronouns
public import Linglib.Fragments.Romance.Galician.Pronouns
public import Linglib.Fragments.Tamil.Pronouns
public import Linglib.Syntax.Minimalist.Probe.Basic
public import Linglib.Data.Examples.Readers

/-!
# Alok and Bhalla (2026): allocutivity and the syntax of honorifics

Alok and Bhalla review allocutive markers, which encode features of the addressee on the verb,
and honorific features. A language marks the clause contexts at or above a threshold on a scale
of clause size, and the phrases where the addressee is represented reach every context it marks,
though in Souletin Basque, Korean and Tamil they reach further. Alok's relational [iHON] makes the
grades of a clause's phrases factor through their referents, which a single [status] per clause,
as in Portner, Pak and Zanuttini, cannot match.

## Implementation notes

* The speech-act phrase reaches embedded-root contexts, as in Miyagawa's account, which the review
  adopts for its first two types.
* The Japanese complementizers *koto*, *yooni* and *to* license or block the marker within finite
  non-root clauses (33). They are not contexts, so the Japanese addressee phrase reaches no clause
  type below the root and the Japanese threshold is Miyagawa's.
* Innovative Southern Basque has no glottocode of its own, so no row is keyed to it.
* The marker types the review reports are not recorded, since those of Basque and Japanese are
  contested. Each rests on the marker's identity with another morpheme, as in
  `Basque.allocutive_eq_ergative`, the Galician familiar dative clitics, the Tamil plural suffix
  `Tamil.Pronouns.ŋgæ` and `magahi_allocutive_fused`.
* The rows do not record the person of a subject, so a subject is taken to denote an individual of
  its own.

## References

* [alok-bhalla-2026]
* [alok-2020]
* [alok-2021]
* [alok-haddican-2022]
* [haddican-etxeberria-2022]
* [kaur-2020]
* [miyagawa-2017]
* [portner-pak-zanuttini-2019]
* [speas-tenny-2003]
* [dayal-2025]
-/

@[expose] public section

namespace AlokBhalla2026

open Morphology SocialMeaning

/-! ### Languages -/

/-- The allocutive languages the review discusses at the level of marker and distribution. -/
inductive Language where
  | souletinBasque
  | innovativeSouthernBasque
  | magahi
  | tamil
  | korean
  | japanese
  | galician
  deriving DecidableEq, Fintype, Repr

/-- The languages of the rows by glottocode. -/
def languages : List (String × Language) :=
  [("soul1243", .souletinBasque), ("maga1260", .magahi), ("tami1289", .tamil),
    ("kore1280", .korean), ("nucl1643", .japanese), ("gali1258", .galician)]

/-! ### The morphosyntax of the marker -/

theorem marker_rows :
    ∀ row ∈ Examples.all, ∀ m ∈ row.feature? "marker",
      (row.language = "soul1243" → ∃ g x, (Basque.Pronouns.allocutive g x).map toString = some m) ∧
      (row.language = "gali1258" → m ∈ Galician.Pronouns.allocutiveClitics.map (·.form)) ∧
      (row.language = "tami1289" → m = toString Tamil.Pronouns.ŋgæ) := by
  decide +kernel

/-- The Magahi grade a row's feature names. -/
def grades : List (String × Magahi.Grade) :=
  [("nh", .nonhonorific), ("h", .honorific), ("hh", .highHonorific)]

theorem magahi_fusion_rows :
    ∀ row ∈ Examples.all, row.language = "maga1260" → ∀ m ∈ row.feature? "marker",
      ∀ s ∈ row.parse? "subject" grades, ∀ a ∈ row.parse? "addressee" grades,
        toString (Magahi.Pronouns.allocutive s a) = m := by
  decide +kernel

theorem magahi_allocutive_fused :
    Magahi.Pronouns.allocutive .nonhonorific .nonhonorific ≠
      Magahi.Pronouns.allocutive .honorific .nonhonorific := by
  decide

/-! ### Distribution and loci -/

/-- Clause contexts, ordered by the size of their left periphery from nonfinite clauses up to root
clauses. The finite non-root contexts include complements of believing and perceiving and factive,
relative, noun-complement and *wh*-clauses, and the embedded-root contexts are complements of
saying and reason clauses. -/
inductive Context where
  | nonfinite
  | finiteNonRoot
  | embeddedRoot
  | root
  deriving DecidableEq, Fintype, Repr

instance : LinearOrder Context := LinearOrder.lift' Context.ctorIdx (by decide)

/-- The context an embedding feature names. -/
def contexts : List (String × Context) :=
  [("saying", .embeddedRoot), ("reason", .embeddedRoot), ("complement", .finiteNonRoot),
    ("believe", .finiteNonRoot), ("perceptual", .finiteNonRoot), ("relative", .finiteNonRoot),
    ("nounComplement", .finiteNonRoot), ("factive", .finiteNonRoot), ("wh", .finiteNonRoot),
    ("nonfinite", .nonfinite), ("infinitive", .nonfinite)]

/-- The least context in which a language has the marker. The review's three types are the
thresholds root (Souletin Basque, Korean), embedded root (Japanese, Tamil) and finite non-root
(Magahi, Innovative Southern Basque, Galician); Galician's infinitives (32) lower its threshold to
the nonfinite clauses. -/
def threshold : Language → Context
  | .souletinBasque | .korean => .root
  | .japanese | .tamil => .embeddedRoot
  | .magahi | .innovativeSouthernBasque => .finiteNonRoot
  | .galician => .nonfinite

/-- A marker in an embedded clause is grammatical exactly where the context is at least its
language's threshold (exx 9, 12–18, 21, 30–32). -/
theorem distribution_rows :
    ∀ row ∈ Examples.all, ∀ l ∈ languages.lookup row.language,
      ∀ c ∈ row.parse? "embedding" contexts, row.judgment = .acceptable ↔ threshold l ≤ c := by
  decide +kernel

theorem japanese_complementizer_rows :
    ∀ row ∈ Examples.all, row.language = "nucl1643" →
      ∀ c ∈ row.feature? "embedding", c ∈ ["koto", "yooni", "to"] →
        (row.judgment = .acceptable ↔ c ≠ "to") := by
  decide +kernel

/-- The phrases where the addressee is represented, from an applicative-like addressee phrase up
through the finiteness phrase to the speech-act phrase of [speas-tenny-2003]. -/
inductive Locus where
  | addr
  | fin
  | sa
  deriving DecidableEq, Fintype, Repr

/-- The loci the review's sources assign. Souletin Basque and Korean have the speech-act phrase,
Magahi the finiteness phrase ([alok-2021]), Tamil both for its two marker positions (31), Japanese
the speech-act and addressee phrases, and Galician and Innovative Southern Basque the addressee
phrase ([alok-haddican-2022], [haddican-etxeberria-2022]). -/
def loci : Language → Finset Locus
  | .souletinBasque | .korean => {.sa}
  | .magahi => {.fin}
  | .tamil => {.sa, .fin}
  | .japanese => {.sa, .addr}
  | .innovativeSouthernBasque | .galician => {.addr}

theorem loci_nonempty (l : Language) : (loci l).Nonempty := by
  cases l <;> decide

/-- The least context every clause of which hosts a locus. The speech-act phrase is in root and
embedded-root contexts ([miyagawa-2017]), and the finiteness phrase carries speaker and addressee
coordinates in every finite clause. The addressee phrase is licensed language by language, in
every Galician clause, infinitives included (32), in every finite clause of Innovative Southern
Basque, and in Japanese only under *koto* and *yooni* (33), so in no clause type below the root. -/
def lowest (l : Language) : Locus → Context
  | .sa => .embeddedRoot
  | .fin => .finiteNonRoot
  | .addr =>
    match l with
    | .galician => .nonfinite
    | .innovativeSouthernBasque => .finiteNonRoot
    | _ => .root

/-- The loci of a language reach every context in which it has the marker. -/
theorem loci_sound (l : Language) : (loci l).inf' (loci_nonempty l) (lowest l) ≤ threshold l := by
  cases l <;> decide

theorem embeddedRoot_le_threshold {l : Language} (h : loci l = {.sa}) :
    .embeddedRoot ≤ threshold l := by
  simpa [h, lowest] using loci_sound l

/-- The loci reach below the threshold exactly in Souletin Basque and Korean (ex 13, [dayal-2025])
and in Tamil. -/
theorem loci_incomplete :
    {l | (loci l).inf' (loci_nonempty l) (lowest l) ≠ threshold l} =
      {.souletinBasque, .korean, .tamil} := by
  ext l
  cases l <;> simp <;> decide

/-! ### Honorific features -/

/-- The ordering [iHON] presents between the speaker and a referent, ⟦iHON⟧ = λx. S ≺ x, with ≺
one of ≥, <, << (46), ordered by the deference it presents. -/
inductive Status where
  /-- The speaker is at least the referent's equal, S ≥ x. -/
  | atLeast
  /-- The speaker is below the referent, S < x. -/
  | below
  /-- The speaker is far below the referent, S << x. -/
  | farBelow
  deriving DecidableEq, Fintype, Repr

instance : LinearOrder Status := LinearOrder.lift' Status.ctorIdx (by decide)

/-- The Magahi grades present the three orderings in turn, the nonhonorific S ≥ x and the high
honorific S << x (47). -/
def gradeEquivStatus : Magahi.Grade ≃o Status where
  toFun
    | .nonhonorific => .atLeast
    | .honorific => .below
    | .highHonorific => .farBelow
  invFun
    | .atLeast => .nonhonorific
    | .below => .honorific
    | .farBelow => .highHonorific
  left_inv := by decide
  right_inv := by decide
  map_rel_iff' := by decide

/-- The status a row's feature names. -/
def statuses : List (String × Status) := [("ge", .atLeast), ("lt", .below), ("ll", .farBelow)]

/-- The formality a row's feature names. -/
def formalities : List (String × Register) := [("+", .formal), ("-", .informal)]

/-- [portner-pak-zanuttini-2019]'s Korean speech-style particles realize the speaker's status
toward the addressee and the formality of the discourse together (34). -/
def portnerParticle : Status → Register → Option Morph
  | .below, .formal => some (.suff "supnita")
  | .below, .informal => some (.suff "eyo")
  | .atLeast, .informal => some (.suff "e")
  | _, _ => none

theorem korean_particle_rows :
    ∀ row ∈ Examples.all, ∀ s ∈ row.parse? "status" statuses,
      ∀ r ∈ row.parse? "formal" formalities,
        (portnerParticle s r).map (·.form) = row.feature? "particle" := by
  decide +kernel

/-! ### Relational grades -/

section Relational

variable {D E G : Type*}

/-- The grades of a clause's phrases are relational when they factor through the phrases'
referents, each phrase presenting the speaker's relation to its referent ([alok-2020]). -/
def Relational (grade : D → G) (ref : D → E) : Prop := grade.FactorsThrough ref

/-- The grades come from a single source when the clause has one grade, the [status] on c of
[portner-pak-zanuttini-2019]. -/
def SingleSource (grade : D → G) : Prop := ∀ d d', grade d = grade d'

instance [Fintype D] [DecidableEq E] [DecidableEq G] {grade : D → G} {ref : D → E} :
    Decidable (Relational grade ref) :=
  inferInstanceAs (Decidable (∀ d d', ref d = ref d' → grade d = grade d'))

instance [Fintype D] [DecidableEq G] {grade : D → G} : Decidable (SingleSource grade) :=
  inferInstanceAs (Decidable (∀ d d', grade d = grade d'))

variable {grade : D → G} {ref : D → E}

theorem relational_iff_exists [Nonempty G] :
    Relational grade ref ↔ ∃ g : E → G, grade = g ∘ ref :=
  Function.factorsThrough_iff grade

theorem SingleSource.relational (h : SingleSource grade) (ref : D → E) : Relational grade ref :=
  fun d d' _ ↦ h d d'

end Relational

/-- The phrases of a Magahi clause that present a grade, namely the addressee of the marker, two
second person pronouns, the subject and two third person pronouns. -/
inductive Phrase where
  | addressee
  | pronoun2
  | pronoun2Other
  | subject
  | pronoun3
  | pronoun3Other
  deriving DecidableEq, Fintype, Repr

/-- The feature of a row that records a phrase's grade. -/
def Phrase.key : Phrase → String
  | .addressee => "addressee"
  | .pronoun2 => "pronoun2"
  | .pronoun2Other => "pronoun2Other"
  | .subject => "subject"
  | .pronoun3 => "pronoun3"
  | .pronoun3Other => "pronoun3Other"

/-- A second person pronoun denotes the addressee, and each other phrase an individual of its own,
as the third person pronouns of (45) denote the speaker's brother and father. -/
def Phrase.referent : Phrase → Phrase
  | .pronoun2 | .pronoun2Other => .addressee
  | p => p

theorem grade_eq_of_addressee {D G : Type*} {grade : D → G} {ref : D → Phrase}
    (h : Relational grade ref) {d d' : D} (hd : ref d = .addressee) (hd' : ref d' = .addressee) :
    grade d = grade d' :=
  h (hd.trans hd'.symm)

/-- The grade a row records for a phrase. -/
def gradeOf (row : Datum) (p : Phrase) : Option Magahi.Grade := row.parse? p.key grades

/-- The phrases to which a row assigns a grade. -/
abbrev Graded (row : Datum) : Type := {p : Phrase // (gradeOf row p).isSome}

/-- The grade of each graded phrase of a row. -/
def profile (row : Datum) (p : Graded row) : Magahi.Grade := (gradeOf row p.1).get p.2

/-- A Magahi root clause is grammatical exactly when its grades factor through referents (exx 2–6,
39–45); the ungrammatical (41) puts two grades on the addressee. -/
theorem rows_relational :
    ∀ row ∈ Examples.all, row.language = "maga1260" → row.feature? "embedding" = none →
      (row.judgment = .acceptable ↔ Relational (profile row) (Phrase.referent ∘ Subtype.val)) := by
  decide +kernel

/-- The grammatical (44b) and (45) carry several grades in one clause, which no single source
generates. -/
theorem singleSource_refuted :
    Examples.ex_44b.judgment = .acceptable ∧ ¬ SingleSource (profile Examples.ex_44b) ∧
      Examples.ex_45.judgment = .acceptable ∧ ¬ SingleSource (profile Examples.ex_45) := by
  decide +kernel

/-- The second person pronouns take their forms from the second person singular table and the
third person pronouns from the third person singular table. -/
def Phrase.table? : Phrase → Option (Magahi.Case → Magahi.Grade → PersonalPronoun)
  | .pronoun2 | .pronoun2Other => some Magahi.Pronouns.secondSingular
  | .pronoun3 | .pronoun3Other => some Magahi.Pronouns.thirdSingular
  | .addressee | .subject => none

theorem magahi_pronoun_rows :
    ∀ row ∈ Examples.all, row.language = "maga1260" → ∀ p : Phrase, ∀ t ∈ p.table?,
      ∀ g ∈ gradeOf row p, ∃ c,
        (t c g).form.toList ∈ row.surfaceTokens.map (·.toList.map Char.toLower) := by
  decide +kernel

theorem hindi_plural_rows :
    ∀ row ∈ Examples.all, row.language = "hind1269" →
      (row.feature? "agreement" = some "pl" ↔
        row.feature? "subjectNumber" = some "pl" ∨ row.feature? "subjectHon" = some "h") := by
  decide +kernel

/-! ### The person restriction -/

/-- The subject and, above it, the null addressee are the goals of [kaur-2020]'s allocutive
probe. -/
inductive Goal where
  | subject (p : Person)
  | addressee
  deriving DecidableEq, Repr

/-- The person of a goal; the addressee is second person. -/
def Goal.person : Goal → Person
  | .subject p => p
  | .addressee => .second

/-- [kaur-2020]'s probe seeks [participant] features, inspecting the subject and then the
addressee. -/
def kaurProbe : Minimalist.Probe Goal := .relativized fun g ↦ decide g.person.IsSAP

/-- The probe reaches the addressee exactly past a third person subject, so Punjabi allocutivity is
out with first and second person subjects. -/
theorem allocutive_iff_third (p : Person) :
    kaurProbe.goal [.subject p, .addressee] = some .addressee ↔ p = .third := by
  cases p <;> decide

end AlokBhalla2026
