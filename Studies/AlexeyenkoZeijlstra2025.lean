module

public import Linglib.Syntax.WordOrder
public import Studies.ZwickyPullum1983
public import Linglib.Fragments.Slavic.Russian.Agreement
public import Linglib.Data.Examples.AlexeyenkoZeijlstra2025

/-!
# Alexeyenko and Zeijlstra (2025): linearization of complex modifiers

The Head-Final Filter — prenominal modifiers contain no post-head material —
both overgenerates (Greek and Russian allow A–XP–N) and undergenerates (Basque,
Chácobo and Eastern Oromo bar the mirror order N–XP–A while Farsi, Atong and
Kalaallisut allow it). The paper's replacement, the Modifier-Noun Adjacency
Generalization, lets an XP separate an attributive adjective from its noun only
if the adjective's agreement marker is shared with the predicative form and
covers every nominal feature, or its attributivizer is morphophonologically
independent of the adjective.

Both conditions are derived here from the paper's analysis: direct modification
is available only to adjectives that are φ/κ-complete, some form of theirs being
used both attributively and predicatively with an overt marker specified for
every feature of the DP, case included (`Language.PhiKappaComplete`); every
other language needs an attributivizer, which forces adjacency exactly when it
is an adjectival affix, overt or null, under the Input Correspondence Principle
(`AttrStatus.Adjacent`). Russian's forms are the long and short adjectives of
the Fragment. The resulting `Language.Possible` encodes the decision trees and
agrees with the sample of Table 3 on every language the paper discusses. The
example rows carry only their lexical anchors (adjective, noun, dependent); the
linear orders are computed from token positions (`orderOf`) and checked against
the languages and the judgments.

## References

* [alexeyenko-zeijlstra-2025]
* [williams-1982]
* [greenberg-1963]
* [ackema-neeleman-2004]
* [zwicky-pullum-1983]
-/

@[expose] public section

namespace AlexeyenkoZeijlstra2025


/-! ### Agreement marking -/

/-- An adjectival form is used at some positions, and its agreement marker is specified for some
features, a bare form's for none. -/
structure Form where
  uses : Finset Agreement.Position
  features : Finset Agreement.Dimension
  deriving DecidableEq

/-- An adjectival target of the Russian fragment as a form, its marker specified for the
dimensions the target inflects for. -/
def form {F : Type*} (t : Agreement.Target Russian.Agreement.Value F) : Form :=
  ⟨t.positions, t.inflection⟩

/-! ### Attributivizers -/

/-- Morphophonological status of the attributivizer. -/
inductive AttrStatus
  | adjectivalAffix
  | null
  | clitic
  | freeWord
  | nominalAffix
  deriving DecidableEq

/-- An affix takes the head it selects as its host (the Input Correspondence Principle), and the
paper extends this to null affixes; clitics, free words and affixes on the noun leave the
adjective free. -/
def AttrStatus.Adjacent : AttrStatus → Prop
  | .adjectivalAffix | .null => True
  | _ => False

instance : DecidablePred AttrStatus.Adjacent := fun s ↦ by
  cases s <;> simp [AttrStatus.Adjacent] <;> infer_instance

/-- The Zwicky–Pullum cline the paper appeals to for the affix/clitic distinction. -/
def AttrStatus.ofMorphStatus : Morphology.Diagnostics.MorphStatus → AttrStatus
  | .freeWord => .freeWord
  | .simpleClitic | .specialClitic => .clitic
  | .inflAffix | .derivAffix => .adjectivalAffix

/-! ### The languages of the paper -/

/-- Side of the noun an attributive adjective occupies. -/
inductive Side
  | prenominal
  | postnominal
  deriving DecidableEq

/-- The AP-internal order that puts the dependent between adjective and noun. -/
def Side.intervening : Side → HeadDirection
  | .prenominal => .headInitial
  | .postnominal => .headFinal

/-- A language the paper discusses. -/
inductive Language
  | greek | russian | latin | kalaallisut | italian | german | dutch | english | icelandic
  | serboCroatian | mandarin | tagalog | farsi | atong | basque | japanese
  deriving DecidableEq, Repr, Fintype

namespace Language

/-- The sides of the noun a language's attributive adjectives occupy. -/
def sides : Language → Finset Side
  | .italian => {.prenominal, .postnominal}
  | .kalaallisut | .farsi | .atong | .basque => {.postnominal}
  | _ => {.prenominal}

/-- The AP-internal orders a language's predicative adjectives allow; Japanese APs are
strictly head-final, so the filter is obeyed trivially. -/
def apOrders : Language → Finset HeadDirection
  | .german | .dutch | .icelandic | .mandarin => {.headInitial, .headFinal}
  | .kalaallisut | .farsi | .atong | .basque | .japanese => {.headFinal}
  | _ => {.headInitial}

/-- Gender, number and case. -/
def φκ : Finset Agreement.Dimension := {.number, .gender, .case}

/-- A language's adjectival forms. Greek and Latin adjectives have one form, inflected for
gender, number and case in both uses, and Kalaallisut's affixal number and case agreement is
likewise shared; Russian's are the Fragment's long and short adjectives; Italian's one form
agrees in gender and number but never case. German and Dutch predicative adjectives are
bare, the attributive forms carrying gender, number and case or, in Dutch, a schwa sensitive
to gender, number and definiteness; Icelandic and Serbo-Croatian attributive forms add
definiteness to what the predicative forms carry. The rest have one uninflected form. -/
def forms : Language → Finset Form
  | .greek | .latin => {⟨{.attributive, .predicate}, φκ⟩}
  | .russian => {form Russian.Agreement.longAdjective, form Russian.Agreement.shortAdjective}
  | .kalaallisut => {⟨{.attributive, .predicate}, {.number, .case}⟩}
  | .italian => {⟨{.attributive, .predicate}, {.number, .gender}⟩}
  | .german => {⟨{.attributive}, φκ⟩, ⟨{.predicate}, ∅⟩}
  | .dutch => {⟨{.attributive}, {.number, .gender, .definiteness}⟩, ⟨{.predicate}, ∅⟩}
  | .icelandic | .serboCroatian => {⟨{.attributive}, insert .definiteness φκ⟩, ⟨{.predicate}, φκ⟩}
  | _ => {⟨{.attributive, .predicate}, ∅⟩}

/-- The φ-features of a language's DP. Case is not among them: the paper takes it to be
present in every DP whether or not it is realized. -/
def phi : Language → Finset Agreement.Dimension
  | .greek | .russian | .latin | .italian | .german => {.number, .gender}
  | .kalaallisut | .english => {.number}
  | .dutch | .icelandic | .serboCroatian => {.number, .gender, .definiteness}
  | _ => ∅

/-- A language's adjectives take no attributivizer, a null or overt adjectival affix, or a clitic
such as Mandarin *de*, the Tagalog linker or the Farsi ezafe. -/
def attributivizer : Language → Option AttrStatus
  | .greek | .russian | .latin | .kalaallisut => none
  | .italian | .english | .basque | .japanese => some .null
  | .german | .dutch | .icelandic | .serboCroatian => some .adjectivalAffix
  | .mandarin | .tagalog | .farsi | .atong => some .clitic

/-- A language's adjectives are φ/κ-complete, (34a): some form is used both attributively
and predicatively, and its overt marker is specified for every feature of the DP, case
included. -/
def PhiKappaComplete (l : Language) : Prop :=
  ∃ f ∈ l.forms, {.attributive, .predicate} ⊆ f.uses ∧ insert .case l.phi ⊆ f.features

instance (l : Language) : Decidable l.PhiKappaComplete := by
  unfold PhiKappaComplete; infer_instance

/-- Greek, Russian, Latin and Kalaallisut alone are φ/κ-complete: Italian lacks case,
German, Dutch, Icelandic and Serbo-Croatian share no form between the two uses, and the
rest are uninflected. -/
theorem phiKappaComplete_iff (l : Language) :
    l.PhiKappaComplete ↔ l = .greek ∨ l = .russian ∨ l = .latin ∨ l = .kalaallisut := by
  cases l <;> decide

/-- A language whose adjectives are not φ/κ-complete has an attributivizer. -/
theorem attributivizer_ne_none (l : Language) (h : ¬ l.PhiKappaComplete) :
    l.attributivizer ≠ none := by
  revert h; cases l <;> decide

/-- An XP may separate the adjective from the noun on the given side when the AP order creates
the configuration and either the adjectives are φ/κ-complete or the attributivizer does not need
to be adjacent to the adjective. -/
def Possible (l : Language) (s : Side) : Prop :=
  s.intervening ∈ l.apOrders ∧ (l.PhiKappaComplete ∨ ∃ a ∈ l.attributivizer, ¬ a.Adjacent)

instance (l : Language) (s : Side) : Decidable (l.Possible s) :=
  inferInstanceAs (Decidable (_ ∧ (_ ∨ ∃ a ∈ _, _)))

/-- The Modifier-Noun Adjacency Generalization: intervention only under φ/κ-complete
adjectives or an independent attributivizer. -/
theorem mag (l : Language) (s : Side) (h : l.Possible s) :
    l.PhiKappaComplete ∨ ∃ a ∈ l.attributivizer, ¬ a.Adjacent :=
  h.2

theorem japanese_trivial : ¬ japanese.Possible .prenominal := by decide

end Language

/-! ### Table 3 -/

/-- A language of the sample, with its name, its glottocode, the side of the noun its adjectives
occupy, and whether an XP can intervene. -/
structure Sample where
  name : String
  glottocode : String
  side : Side
  intervention : Bool

/-- The sample of Table 3. -/
def table3 : List Sample :=
  [ ⟨"Abkhaz", "abkh1244", .prenominal, true⟩, ⟨"Bulgarian", "bulg1262", .prenominal, true⟩,
    ⟨"Polish", "poli1260", .prenominal, true⟩, ⟨"Russian", "russ1263", .prenominal, true⟩,
    ⟨"Latin", "lati1261", .prenominal, true⟩, ⟨"Lithuanian", "lith1251", .prenominal, true⟩,
    ⟨"Mandarin", "mand1415", .prenominal, true⟩, ⟨"Modern Greek", "mode1248", .prenominal, true⟩,
    ⟨"St'át'imcets", "lill1248", .prenominal, true⟩, ⟨"Tagalog", "taga1270", .prenominal, true⟩,
    ⟨"Armenian", "nucl1235", .prenominal, false⟩, ⟨"Dutch", "dutc1256", .prenominal, false⟩,
    ⟨"English", "stan1293", .prenominal, false⟩, ⟨"German", "stan1295", .prenominal, false⟩,
    ⟨"Icelandic", "icel1247", .prenominal, false⟩, ⟨"Estonian", "esto1258", .prenominal, false⟩,
    ⟨"Finnish", "finn1318", .prenominal, false⟩, ⟨"Hungarian", "hung1274", .prenominal, false⟩,
    ⟨"French", "stan1290", .prenominal, false⟩, ⟨"Italian", "ital1282", .prenominal, false⟩,
    ⟨"Portuguese", "port1283", .prenominal, false⟩, ⟨"Romanian", "roma1327", .prenominal, false⟩,
    ⟨"Spanish", "stan1288", .prenominal, false⟩, ⟨"Georgian", "nucl1302", .prenominal, false⟩,
    ⟨"Serbo-Croatian", "sout1528", .prenominal, false⟩,
    ⟨"Atong", "aton1241", .postnominal, true⟩, ⟨"Farsi", "west2369", .postnominal, true⟩,
    ⟨"Kalaallisut", "kala1399", .postnominal, true⟩,
    ⟨"Basque", "basq1248", .postnominal, false⟩, ⟨"Chácobo", "chac1251", .postnominal, false⟩,
    ⟨"Eastern Oromo", "east2652", .postnominal, false⟩ ]

/-- The languages the paper discusses, by glottocode. -/
def languageOf : String → Option Language
  | "mode1248" => some .greek | "russ1263" => some .russian | "lati1261" => some .latin
  | "ital1282" => some .italian | "stan1295" => some .german | "dutc1256" => some .dutch
  | "stan1293" => some .english | "icel1247" => some .icelandic
  | "sout1528" => some .serboCroatian | "mand1415" => some .mandarin
  | "taga1270" => some .tagalog | "west2369" => some .farsi | "aton1241" => some .atong
  | "kala1399" => some .kalaallisut | "basq1248" => some .basque
  | _ => none

/-- On every language the paper discusses the generalization returns Table 3's verdict. -/
theorem table3_predicted :
    ∀ s ∈ table3, ∀ l ∈ languageOf s.glottocode, (l.Possible s.side ↔ s.intervention) := by
  decide +kernel

/-- The side of the noun alone decides nothing. Each block of the table holds both verdicts, so
no filter stated on the side, the Head-Final Filter or its mirror, fits the sample. -/
theorem side_insufficient (side : Side) :
    ∃ s ∈ table3, ∃ t ∈ table3, s.side = side ∧ t.side = side ∧ s.intervention ∧
      ¬ t.intervention := by
  cases side <;> decide

/-! ### The *enough* exception -/

/-- Hosts an attributivizer may attach to when a degree word closes the AP. -/
inductive Host
  | adjective
  | degreeWord

/-- A null affix attaches to the head of the phrase it selects, DegP included; an overt affix may
attach to a non-lexical head only if that head is itself an affix (the Affix Continuity
Constraint), which *enough* and *genoeg* are not. -/
def AttrStatus.MayHost : AttrStatus → Host → Prop
  | .null, _ => True
  | .adjectivalAffix, .adjective => True
  | .adjectivalAffix, .degreeWord => False
  | _, _ => True

instance : DecidableRel AttrStatus.MayHost := fun s h ↦ by
  cases s <;> cases h <;> simp [AttrStatus.MayHost] <;> infer_instance

/-! ### Rows -/

/-- The attributivizer a row reports. -/
def attributivizerOf (row : Datum) : Option AttrStatus :=
  match row.feature? "attributivizer" with
  | some "affix" => some .adjectivalAffix
  | some "null" => some .null
  | some "clitic" => some .clitic
  | _ => none

/-- Split on spaces. -/
def words : List Char → List (List Char)
  | [] => []
  | ' ' :: cs => words cs
  | c :: cs =>
    match words cs with
    | [] => [[c]]
    | w :: ws => if cs.head? = some ' ' then [c] :: w :: ws else (c :: w) :: ws

/-- A row's tokens, punctuation dropped. -/
def tokens (row : Datum) : List (List Char) :=
  (if row.glossedTokens = [] then words row.primaryText.toList
    else row.surfaceTokens.map String.toList).map (·.filter (· ∉ ['.', ',']))

/-- Position of the token a feature names. -/
def anchor (row : Datum) (key : String) : Option ℕ :=
  (row.feature? key).bind fun t ↦ (tokens row).findIdx? (· = t.toList)

/-- Linear order of adjective, dependent and noun, read off token positions. -/
inductive Order
  | bare
  | aXp
  | xpA
  | aN
  | nA
  | aXpN
  | xpAN
  | aNXp
  | nAXp
  | nXpA
  | aDegN
  deriving DecidableEq

/-- The order of a row is read off its anchors, the adjective, the modified noun (absent in
predicative use), the first word of the adjective's dependent, and a degree word. -/
def orderOf (row : Datum) : Option Order :=
  match anchor row "head", anchor row "noun", anchor row "dependent", anchor row "degree" with
  | some _, none, none, _ => some .bare
  | some h, none, some d, _ => some (if h < d then .aXp else .xpA)
  | some h, some n, some d, _ =>
    if h < n then some (if d < h then .xpAN else if d < n then .aXpN else .aNXp)
    else if d < n then none else some (if d < h then .nXpA else .nAXp)
  | some h, some n, none, deg =>
    if h < n then some (if ∃ g ∈ deg, h < g ∧ g < n then .aDegN else .aN) else some .nA
  | none, _, _, _ => none

example : orderOf Examples.az2025_1b = some .aXpN := by decide +kernel
example : orderOf Examples.az2025_2a = some .aXp := by decide +kernel
example : orderOf Examples.az2025_3a = some .xpA := by decide +kernel
example : orderOf Examples.az2025_4b = some .nXpA := by decide +kernel
example : orderOf Examples.az2025_36b = some .nAXp := by decide +kernel
example : orderOf Examples.az2025_41b = some .xpAN := by decide +kernel
example : orderOf Examples.az2025_71c = some .aDegN := by decide +kernel

/-- Every attributive row stands on a side of the noun the language allows, every predicative
order attested is in the language's AP orders, and every judgment on an intervening order is the
generalization's; relative-clause paraphrases are outside the generalization. -/
theorem rows_agree :
    ∀ row ∈ Examples.all, ∀ l ∈ languageOf row.language, row.feature? "construction" = none →
      ∀ o ∈ orderOf row,
        (o ∈ [.aN, .aXpN, .xpAN, .aDegN] → .prenominal ∈ l.sides) ∧
        (o ∈ [.nA, .nAXp, .nXpA] → .postnominal ∈ l.sides) ∧
        (o = .aXp → row.judgment = .acceptable → .headInitial ∈ l.apOrders) ∧
        (o = .xpA → row.judgment = .acceptable → .headFinal ∈ l.apOrders) ∧
        (o = .aXpN → (row.judgment = .acceptable ↔ l.Possible .prenominal)) ∧
        (o = .nXpA → (row.judgment = .acceptable ↔ l.Possible .postnominal)) := by
  decide +kernel

/-- A degree word between adjective and noun is tolerated exactly by a null
    attributivizer. -/
theorem degree_rows :
    ∀ row ∈ Examples.all, orderOf row = some .aDegN →
      ∀ s ∈ attributivizerOf row, (row.judgment = .acceptable ↔ s.MayHost .degreeWord) := by
  decide +kernel

end AlexeyenkoZeijlstra2025
