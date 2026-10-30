module

public import Linglib.Syntax.Agreement.Geometry
public import Linglib.Syntax.Minimalist.Probe.Basic
public import Linglib.Morphology.DistributedMorphology.Fission
public import Linglib.Morphology.DistributedMorphology.Impoverishment
public import Linglib.Fragments.Georgian.Agreement
public import Linglib.Data.Examples.McGinnis2013
public import Mathlib.Order.Prod.Lex.Basic
public import Linglib.Data.Examples.Readers

/-!
# McGinnis (2013): Agree and Fission in Georgian Plurals

McGinnis derives the number suffixes of the Georgian verb from one fused tense–aspect–mood node,
which agrees in number with at most one argument and fissions during Vocabulary Insertion. T's
number probe looks for [Group] first on the subject and then on a first- or second-person object
clitic, and Impoverishment removes the [Group] of a dative first-person plural, whose plurality
then shows only through [Multispeaker] in the prefix *gv-*. Each suffix discharges the features
it spells out, so the third-person plural screeve suffix leaves no [Group] for *-t*, and *-t*
leaves no [#] for the default *-s*.

## Implementation notes

* An item's contextual features are read off the fused node as it stands before insertion, so
  they are never discharged.
* Only the aorist and optative screeves are modelled, and the null second-person prefix without
  its *x-* allomorph.
* [DAT] is the feature the Set B prefixes spell out, borne by the argument that the Fragment's
  second-series pattern marks by Set B, though that pattern makes the direct object nominative.

## References

* [mcginnis-2013]
* [harley-ritter-2002]
* [bejar-2003]
* [gonzalez-poot-mcginnis-2006]
* [hewitt-1995]
* [anderson-1984]
-/

@[expose] public section

namespace McGinnis2013

open DistributedMorphology Phi.Geometry Georgian Morphology

/-! ### Features -/

/-- The features are the geometry nodes, dative case, and the interpretable TAM features, namely
aorist, optative, and the feature the optative shares with the present, future, and
conjunctive. -/
inductive Feature where
  | node (n : Node)
  | dat
  | aorist
  | optative
  | ftam
  deriving DecidableEq, Repr, Fintype

namespace Feature

/-- `f.toNode?` is the geometry node `f` is, if any. -/
def toNode? : Feature → Option Node
  | node n => some n
  | _ => none

/-- A feature lies under the node `a` when it is a node depending on `a`. The person features lie
under Participant and the number features under Individuation. -/
def IsUnder (a : Node) (f : Feature) : Prop := ∃ n ∈ f.toNode?, a ≤ n

instance (a : Node) : DecidablePred (IsUnder a) := fun f ↦ Option.decidableExistsMem f.toNode?

/-- The interpretable features are those of tense, aspect, and mood. -/
def IsInterpretable (f : Feature) : Prop := f = aorist ∨ f = optative ∨ f = ftam

instance : DecidablePred IsInterpretable := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

end Feature

/-- The site mentioning the nodes `ns` bears every node at or below them, since a dependent brings
what it depends on, and the further features `extra`. -/
def site (ns : List Node) (extra : Finset Feature) : Finset Feature :=
  ((ns.flatMap Node.below).map Feature.node).toFinset ∪ extra

theorem node_mem_site {a : Node} {ns : List Node} {extra : Finset Feature} :
    .node a ∈ site ns extra ↔ (∃ n ∈ ns, ⊥ < a ∧ a ≤ n) ∨ .node a ∈ extra := by
  simp [site, Node.mem_below]

theorem site_subset_site {a b : Node} (h : a ≤ b) (extra : Finset Feature) :
    site [a] extra ⊆ site [b] extra := by
  intro x hx
  simp only [site, List.flatMap_cons, List.flatMap_nil, List.append_nil, Finset.mem_union,
    List.mem_toFinset, List.mem_map] at hx ⊢
  exact hx.imp_left fun ⟨n, hn, hx⟩ ↦ ⟨n, Node.below_subset_below h hn, hx⟩

/-! ### Arguments -/

/-- An agreeing argument has a person and a number. -/
structure Argument where
  person : Person
  number : Number
  deriving DecidableEq, Repr

/-- Georgian activates neither Addressee nor Minimal ((4)), so a pronoun's first person is
Participant with Speaker, its plural adding Multispeaker, its second person is bare Participant,
its plural is Group under [#], and only its third person has Class. -/
def Argument.features (a : Argument) : Finset Feature :=
  let person : Finset Node := match a.person with
    | .first => {.participant, .speaker} ∪ if a.number = .plural then {.multispeaker} else ∅
    | .second => {.participant}
    | _ => ∅
  let number : Finset Node := insert .individuation
    ((if a.number = .plural then {.group} else ∅) ∪ if a.person = .third then {.nounClass} else ∅)
  (person ∪ number).image Feature.node

/-- A Set B marking spells out [DAT] ((9)), and a Set A marking no case. -/
def caseFeatures (m : Marking) : Finset Feature := if m.affixes = some .B then {.dat} else ∅

/-- The subject of a transitive verb in the second series bears its φ-features and the case of
its marking. -/
def Argument.asSubject (a : Argument) : Finset Feature :=
  a.features ∪ caseFeatures (pattern .transitive .aorist).subject

/-- The direct object of a transitive verb in the second series bears its φ-features and the
case of its marking. -/
def Argument.asObject (a : Argument) : Finset Feature :=
  a.features ∪ caseFeatures (pattern .transitive .aorist).directObject

/-- Impoverishment deletes the [Group] of a dative first-person pronoun at the spell-out of vP,
after case and before T's number probe ((8)). -/
def impoverishment : ImpoverishmentRule (Finset Feature) Feature :=
  .ofFocus (fun b ↦ .dat ∈ b ∧ .node .speaker ∈ b) (.node .group)

/-- `impoverish b` is the pronoun `b` after Impoverishment. -/
def impoverish (b : Finset Feature) : Finset Feature :=
  impoverishment.apply Finset.erase (.ofBundle b)

/-! ### Agree -/

/-- v's person probe is specified for [Participant]. -/
def personProbe : Minimalist.Probe (Finset Feature) :=
  .relativized (.node .participant ∈ ·)

/-- T's number probe is specified for [Group], so a goal without [Group] does not halt its search
and T probes again ([bejar-2003]). -/
def numberProbe : Minimalist.Probe (Finset Feature) := .relativized (.node .group ∈ ·)

/-- v's probe finds a participant object first, else a participant subject ((7), (9)), and its
agreement node copies the goal's person features and case. -/
def prefixNode (subj obj : Argument) : Finset Feature :=
  ((personProbe.search [obj.asObject, subj.asSubject]).map
    (·.filter fun f ↦ f.IsUnder .participant ∨ f = .dat)).getD ∅

/-- T's number probe searches the subject and then the object if it is a first- or second-person
clitic moved to T, both after Impoverishment; a third-person object stays below T ((6), (7)). -/
def numberGoals (subj obj : Argument) : List (Finset Feature) :=
  (subj.asSubject :: if obj.person = .third then [] else [obj.asObject]).map impoverish

/-- T copies the number content of its goal, and keeps the bare [#] when no goal bears [Group],
the probe's [Group] then deleting ((5)). -/
def numberContent (subj obj : Argument) : Finset Feature :=
  ((numberProbe.search (numberGoals subj obj)).map (·.filter (·.IsUnder .individuation))).getD
    {.node .individuation}

/-- The two screeves treated are the aorist (10) and the optative (13). -/
inductive Screeve where
  | aorist
  | optative
  deriving DecidableEq, Repr, Fintype

/-- A screeve bears its interpretable features. -/
def Screeve.features : Screeve → Finset Feature
  | .aorist => {.aorist}
  | .optative => {.ftam, .optative}

/-- The fused TAM node bears the screeve's features, the subject's person features, and the
number content T agreed with. -/
def tamNode (s : Screeve) (subj obj : Argument) : Finset Feature :=
  s.features ∪ subj.asSubject.filter (·.IsUnder .participant) ∪ numberContent subj obj

/-! ### Vocabulary -/

/-- The prefix items are those of (9). -/
def gv : VocabularyItem Feature String := site [.multispeaker] {.dat} ⟷ "gv"
def m : VocabularyItem Feature String := site [.speaker] {.dat} ⟷ "m"
def g : VocabularyItem Feature String := site [.participant] {.dat} ⟷ "g"
def v : VocabularyItem Feature String := site [.speaker] ∅ ⟷ "v"
def participantNull : VocabularyItem Feature String := site [.participant] ∅ ⟷ ""
def elsewhere : VocabularyItem Feature String := ∅ ⟷ ""

def prefixes : List (VocabularyItem Feature String) := [gv, m, g, v, participantNull, elsewhere]

/-- The plural suffix *-t* (13c) takes its [#] from the geometry. -/
def plural : VocabularyItem Feature String := site [.group] ∅ ⟷ "t"

/-- A null suffix (13d) realizes the [#] of a participant. -/
def participantNumber : VocabularyItem Feature String :=
  ⟨(site [.individuation] ∅).map (.sectR 0 _) ∪ {(-1, .ftam), (-1, .node .participant)}, ""⟩

/-- The suffix *-s* (13e) realizes [#] by default. -/
def defaultNumber : VocabularyItem Feature String :=
  ⟨(site [.individuation] ∅).map (.sectR 0 _) ∪ {(-1, .ftam)}, "s"⟩

/-- A screeve's Vocabulary lists the aorist items (10) or the optative items (13) in scansion
order. -/
def Screeve.vocabulary : Screeve → List (VocabularyItem Feature String)
  | .aorist =>
    [site [.group, .nounClass] {.aorist} ⟷ "es", site [.participant] {.aorist} ⟷ "e",
      {.aorist} ⟷ "a", plural, elsewhere]
  | .optative =>
    [{.ftam, .optative} ⟷ "o",
      ⟨(site [.group, .nounClass] ∅).map (.sectR 0 _) ∪ {(-1, .optative)}, "n"⟩, plural,
      participantNumber, defaultNumber, elsewhere]

/-- The person prefix wins Elsewhere competition at v's agreement node. -/
def personPrefix (subj obj : Argument) : Option String :=
  subsetPrinciple prefixes (prefixNode subj obj)

/-- Strict scansion with local Fission inserts these items at the fused node, whose own features
stand as context to every item. -/
def suffixItems (s : Screeve) (subj obj : Argument) : List (VocabularyItem Feature String) :=
  insertions s.vocabulary ⟨∅, [tamNode s subj obj], []⟩ [tamNode s subj obj]

/-- The overt suffixes are the inserted items' nonnull exponents. -/
def suffixes (s : Screeve) (subj obj : Argument) : List String :=
  ((suffixItems s subj obj).map (·.exponent)).filter (· ≠ "")

/-! ### The data pool -/

/-- A row records the arguments, screeve, attested prefix and suffixes, and judgment. -/
structure Row where
  subj : Argument
  obj : Argument
  screeve : Screeve
  prefix_ : String
  suffixes : List String
  judgment : Judgment
  deriving Repr

def Row.ofDatum (ex : Datum) : Option Row := do
  let person := [("1", Person.first), ("2", .second), ("3", .third)]
  let number := [("sg", Number.singular), ("pl", .plural)]
  pure ⟨⟨← ex.parse? "subjPerson" person, ← ex.parse? "subjNumber" number⟩,
    ⟨← ex.parse? "objPerson" person, ← ex.parse? "objNumber" number⟩,
    ← ex.parse? "screeve" [("aorist", .aorist), ("optative", .optative)], ← ex.feature? "prefix",
    ["suffix1", "suffix2", "suffix3"].filterMap ex.feature?, ex.judgment⟩

theorem row_ofDatum_isSome : ∀ ex ∈ Examples.all, (Row.ofDatum ex).isSome := by decide

/-- The rows are the forms of (2)–(6), (12), (15), (21)–(23), (26). -/
def rows : List Row := Examples.all.filterMap Row.ofDatum

/-- **Agree and Fission.** A form is grammatical iff its prefix is the Subset Principle's winner
and its suffixes are what scansion inserts, so a clause has one Group, no *-t* after *-es*, no
*-s* beside *-t*, and no *-t* for a dative first-person plural. -/
theorem rows_realized :
    ∀ r ∈ rows, r.judgment = .acceptable ↔
      personPrefix r.subj r.obj = some r.prefix_ ∧
        suffixes r.screeve r.subj r.obj = r.suffixes := by
  decide

/-! ### One exponent per feature -/

/-- The suffixes realize pairwise disjoint features of T, so no double plural marking occurs
(§3.3.1). -/
theorem one_exponent_per_feature (s : Screeve) (subj obj : Argument) :
    (suffixItems s subj obj).Pairwise fun i j ↦ Disjoint i.features j.features :=
  pairwise_disjoint_insertions (by simpa using (tamNode s subj obj).nodup)

/-- Fission alone does not exclude double plural marking, since T with two number matrices would
yield the starred (3b) (§3.3.1). -/
theorem fission_alone_allows_double_plural :
    let subjNum := Screeve.aorist.features ∪
      (⟨.third, .plural⟩ : Argument).features.filter (·.IsUnder .individuation)
    let objNum := (⟨.second, .plural⟩ : Argument).features.filter (·.IsUnder .individuation)
    ((insertions Screeve.aorist.vocabulary ⟨∅, [subjNum ∪ objNum], []⟩
        [subjNum, objNum]).map (·.exponent)).filter (· ≠ "") = ["es", "t"] := by
  decide

/-! ### The ranking -/

/-- An item ranks by the number of interpretable features it discharges, then by its Subset
Principle specificity, its intrinsic features leading and its contextual ones breaking ties. -/
def rank (i : VocabularyItem Feature String) : ℕ ×ₗ ℕ ×ₗ ℕ :=
  toLex ((i.features.filter (·.IsInterpretable)).card, i.specificity)

-- (10c), (13a), (20)
theorem vocabulary_ranked (s : Screeve) : s.vocabulary.Pairwise fun i j ↦ rank j < rank i := by
  cases s <;> decide

-- (13c), (13d), (13e)
theorem specificity_number :
    participantNumber.specificity < plural.specificity ∧
      defaultNumber.specificity < participantNumber.specificity := by
  decide

-- (9a), (9b), (9c), (9d), (9e), (9f)
theorem prefix_ranking :
    m.features ⊆ gv.features ∧ g.features ⊆ m.features ∧
      participantNull.features ⊆ v.features ∧ elsewhere.features ⊆ participantNull.features := by
  simp only [m, gv, g, v, participantNull, elsewhere, VocabularyItem.features_ofFeatures]
  exact ⟨site_subset_site (by decide) _, site_subset_site (by decide) _,
    site_subset_site (by decide) _, Finset.empty_subset _⟩

-- (13c)
theorem plural_site : plural.features = {.node .individuation, .node .group} := by decide

/-! ### The agreement sets -/

/-- An aorist clause's agreement affixes are its person prefix and plural *-t*, the affixes the
Fragment's agreement sets list. -/
def agreementAffixes (subj obj : Argument) : List Morph :=
  ((personPrefix subj obj).filter (· ≠ "")).toList.map .pref ++
    if plural ∈ suffixItems .aorist subj obj then [.suff plural.exponent] else []

/-- With a third-person singular subject each object receives its Set B affixes ([hewitt-1995]),
*gv-* without *-t* for the first person plural. -/
theorem setB_realize :
    ∀ p ∈ [Person.first, .second, .third], ∀ n ∈ [Number.singular, .plural],
      setB.realize (.personNumber p n) = some (agreementAffixes ⟨.third, .singular⟩ ⟨p, n⟩) := by
  decide

/-- With a third-person singular object each participant subject receives its Set A affixes. -/
theorem setA_realize :
    ∀ p ∈ [Person.first, .second], ∀ n ∈ [Number.singular, .plural],
      setA.realize (.personNumber p n) = some (agreementAffixes ⟨p, n⟩ ⟨.third, .singular⟩) := by
  decide

-- (3)
theorem setB_plural_from_T :
    setB.realize (.personNumber .second .plural) = some [.pref "g", .suff "t"] ∧
      agreementAffixes ⟨.third, .plural⟩ ⟨.second, .plural⟩ = [.pref "g"] := by
  decide

end McGinnis2013
