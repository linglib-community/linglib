module

public import Linglib.Data.Examples.SadakaneKoizumi1995
public import Linglib.Fragments.Japanese.Adpositions
public import Linglib.Fragments.Japanese.Case
public import Linglib.Syntax.Tree.Command

/-!
# Sadakane and Koizumi (1995)

Japanese particles after a noun phrase divide into case markers, which cliticize onto the noun
phrase, and postpositions, which head a phrase over it. The particle *ni* seems to behave as both.
Sadakane and Koizumi argue that it is four homophonous particles: the dative case marker, a
postposition, the *ni* inserted on a caseless subject, and a form of the copula. Three tests
separate them, a floating numeral quantifier and a cleft with and without the particle. The uses
of *ni* that pass all three are ambiguous between the case marker and the postposition, and the
paper ties the choice between the two to how affected the referent of the noun phrase is.

## Main definitions

* `Attachment`: whether a particle cliticizes onto its noun phrase or heads a phrase over it.
* `Particle`, `Test`, `Particle.Passes`: the four classes of particle, the three tests, and which
  classes pass which tests.
* `Position`: the argument positions of the affectedness hierarchy (45).

## Main statements

* `Attachment.hostsQuantifier_iff`: a numeral quantifier and its host c-command each other exactly
  when the particle cliticizes.
* `Particle.passes_caseMarker`, `Particle.passes_postposition`, `Particle.passes_insertion`,
  `Particle.not_passes_copula`: the tables (14), (29) and (32).
* `exists_passes_and_exists_passes_iff`: a use of *ni* passing both of the first two tests is
  ambiguous between the case marker and the postposition.
* `judgment_eq_acceptable_iff`: every test example is acceptable exactly when its particle passes
  the test.
* `judgment_eq_acceptable_iff_affected`: a floating quantifier goes with a *ni* phrase exactly when
  its referent may be affected.
* `Position.lt_iff_cCommands`: the hierarchy (45) orders the arguments of Koizumi's tree (44) by
  c-command.

## Implementation notes

* A test is passed when the paper marks it OK without qualification, so the postposition's cleft
  without the particle, `*/?/OK` in (14), fails. An example printed with two marks records the
  first as its judgment and the second as `alsoJudged`.
* The cleft with the particle follows Nakayama's account, which the paper offers for concreteness
  without adopting it.
* Martin's 31 uses of *ni* are the `category` labels of the examples, and the class the paper
  assigns each is a `particle` label, two for an ambiguous use.
* The judgments are those of the innovating variety (note 9). Morii's acquisition study, which
  the paper reports, is not formalized.

## References

* [sadakane-koizumi-1995]
* [kuroda-1965]
* [martin-1975]
* [miyagawa-1989]
* [nakayama-1989]
* [takezawa-1987]
* [koizumi-1994]
* [morii-1993]
-/

@[expose] public section

namespace SadakaneKoizumi1995

open PhraseStructure PhraseStructure.Tree Core.Order
open RoseTree (CCommands)

/-! ### Case markers and postpositions -/

/-- A particle either cliticizes onto the noun phrase it follows, as a case marker does,
`[NP John-ga]`, or takes the noun phrase as its complement and heads a phrase, as a postposition
does, `[PP [NP John] kara]` ((1)). -/
inductive Attachment where
  /-- The particle cliticizes onto the noun phrase. -/
  | clitic
  /-- The particle heads a phrase of part of speech `u` over the noun phrase. -/
  | head (u : UD.UPOS)
  deriving DecidableEq

/-- A category can bear Case when it is an NP or a PP; an AP cannot ((10)). -/
def CaseAssignable (c : Cat) : Prop := c = .N ∨ c = .P

instance : DecidablePred CaseAssignable := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

namespace Attachment

/-- `a.phrase` is the phrase a particle forms with its noun phrase. -/
def phrase : Attachment → Tree Cat Unit
  | clitic => .terminal .N ()
  | head u => .node (.lex u) [.terminal .N (), .terminal (.lex u) ()]

/-- In the clause of (6) and (7), the particle's phrase, a floating numeral quantifier and the
verb are sisters. -/
def quantifierTree (a : Attachment) : Tree Cat Unit :=
  .node .V [a.phrase, .terminal .Num (), .terminal .V ()]

/-- `a.host` is the position of the noun phrase in `a.quantifierTree`. -/
def host : Attachment → TreePath
  | clitic => ⟨[0]⟩
  | head _ => ⟨[0, 0]⟩

/-- A noun phrase hosts a floating numeral quantifier when the two c-command each other
([miyagawa-1989]), with c-command as note 4 defines it. -/
def HostsQuantifier (a : Attachment) : Prop :=
  CCommands a.quantifierTree a.host ⟨[1]⟩ ∧ CCommands a.quantifierTree ⟨[1]⟩ a.host

instance : DecidablePred HostsQuantifier := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- A noun phrase hosts a floating quantifier exactly when its particle cliticizes. A particle
that heads a phrase puts a branching node above the noun phrase that does not dominate the
quantifier, as "the PP node prevents the NP from c-commanding the numeral quantifier" (§2) and
the copula's VP does the same (§3). -/
theorem hostsQuantifier_iff {a : Attachment} : a.HostsQuantifier ↔ a = clitic := by
  cases a with
  | clitic => decide
  | head u =>
    refine iff_of_false (fun h ↦ ?_) nofun
    exact absurd (mem_commandRelation.1 h.1.1 ⟨[0]⟩ ⟨_, rfl, le_rfl⟩
        (show (⟨[0]⟩ : TreePath) < ⟨[0, 0]⟩ by decide))
      (show ¬ (⟨[0]⟩ : TreePath) ≤ ⟨[1]⟩ by decide)

/-- A particle's phrase can be the focus of a cleft when it can bear Case and bears none yet. On
[nakayama-1989]'s account the copula *da* assigns Case to its complement, so a case-marked NP
would be doubly case-marked ((8)) while a PP can be the focus ((9)). -/
def Focusable (a : Attachment) : Prop := CaseAssignable a.phrase.cat ∧ a ≠ clitic

instance : DecidablePred Focusable := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- No particle both lets its noun phrase host a floating quantifier and lets its phrase be the
focus of a cleft, so none behaves as a case marker and as a postposition at once (§4). -/
theorem not_hostsQuantifier_and_focusable (a : Attachment) :
    ¬ (a.HostsQuantifier ∧ a.Focusable) :=
  fun ⟨h, _, hne⟩ ↦ hne (hostsQuantifier_iff.1 h)

end Attachment

/-! ### The four particles -/

/-- The tests separate four classes of particle, [kuroda-1965]'s case markers and postpositions
together with the *ni* of *ni* insertion and the copula. -/
inductive Particle where
  /-- A case marker, such as *ga*, *o* and the dative *ni*. -/
  | caseMarker
  /-- A postposition, such as *kara*, *de* and the postposition *ni*. -/
  | postposition
  /-- The *ni* inserted on a caseless noun phrase ([takezawa-1987]). -/
  | insertion
  /-- The copula, one of whose forms is *ni*. -/
  | copula
  deriving DecidableEq, Fintype, Repr

/-- The paper tests a use of a particle in three constructions (§2). -/
inductive Test where
  /-- A floating numeral quantifier goes with the noun phrase ((6), (7)). -/
  | quantifierFloat
  /-- The noun phrase and its particle are the focus of a cleft ((8), (9)). -/
  | cleftWithParticle
  /-- The noun phrase without its particle is the focus of a cleft ((11), (12)). -/
  | cleftWithoutParticle
  deriving DecidableEq, Fintype, Repr

namespace Particle

/-- A case marker cliticizes. A postposition heads a PP, and so does the *ni* of *ni* insertion,
which is a postposition; the copula heads a VP (§3). -/
def attachment : Particle → Attachment
  | caseMarker => .clitic
  | postposition | insertion => .head .ADP
  | copula => .head .VERB

/-- The *ni* of *ni* insertion marks only a noun phrase in the subject position, Spec,IP (§3). -/
def MarksSubject : Particle → Prop
  | insertion => True
  | _ => False

instance : DecidablePred MarksSubject := fun p ↦ by
  cases p <;> unfold MarksSubject <;> infer_instance

/-- A particle passes a test when its noun phrase hosts a floating quantifier, when its phrase is
focusable and not confined to subjects, or, with the particle left out, when what the particle
contributes can be recovered. A case marker contributes nothing, and the noun phrase of the *ni*
of *ni* insertion is the subject, the most accessible relation of (13). -/
def Passes : Particle → Test → Prop
  | p, .quantifierFloat => p.attachment.HostsQuantifier
  | p, .cleftWithParticle => p.attachment.Focusable ∧ ¬ p.MarksSubject
  | p, .cleftWithoutParticle => p.attachment = .clitic ∨ p.MarksSubject

instance (p : Particle) : DecidablePred p.Passes := fun t ↦ by
  cases t <;> unfold Passes <;> infer_instance

theorem passes_quantifierFloat_iff {p : Particle} :
    p.Passes .quantifierFloat ↔ p = caseMarker := by
  decide +revert

theorem passes_cleftWithParticle_iff {p : Particle} :
    p.Passes .cleftWithParticle ↔ p = postposition := by
  decide +revert

/-- A case marker passes the numeral quantifier test and the cleft without the particle ((14)). -/
theorem passes_caseMarker {t : Test} : caseMarker.Passes t ↔ t ≠ .cleftWithParticle := by
  decide +revert

/-- A postposition passes only the cleft with the particle ((14)). -/
theorem passes_postposition {t : Test} : postposition.Passes t ↔ t = .cleftWithParticle := by
  decide +revert

/-- The *ni* of *ni* insertion passes only the cleft without the particle ((29)). -/
theorem passes_insertion {t : Test} : insertion.Passes t ↔ t = .cleftWithoutParticle := by
  decide +revert

/-- The copula passes none of the tests ((32)). -/
theorem not_passes_copula (t : Test) : ¬ copula.Passes t := by
  decide +revert

theorem passes_injective : Function.Injective Passes := by
  intro p q h
  have key (t : Test) : p.Passes t ↔ q.Passes t := by rw [h]
  cases p <;> cases q <;> first
    | rfl
    | exact absurd (key .quantifierFloat) (by decide)
    | exact absurd (key .cleftWithParticle) (by decide)
    | exact absurd (key .cleftWithoutParticle) (by decide)

end Particle

open Particle

/-! ### Ambiguity -/

/-- A use of *ni* that passes both the numeral quantifier test and the cleft with the particle
can be read both as the case marker and as the postposition. Such uses are what mislead the
view of *ni* as a third kind of particle (§4). -/
theorem exists_passes_and_exists_passes_iff {S : List Particle} :
    ((∃ p ∈ S, p.Passes .quantifierFloat) ∧ ∃ p ∈ S, p.Passes .cleftWithParticle) ↔
      caseMarker ∈ S ∧ postposition ∈ S := by
  simp only [passes_quantifierFloat_iff, passes_cleftWithParticle_iff, exists_eq_right]

/-- A use of *ni* that can be read as the case marker or as the postposition passes every test
((27)). -/
theorem exists_passes_of_ambiguous (t : Test) :
    ∃ p ∈ [caseMarker, postposition], p.Passes t := by
  cases t <;> decide

/-! ### Affectedness -/

/-- The paper reads the referent of a noun phrase as affected or not by the action the verb
denotes (§4). -/
inductive Reading where
  /-- The referent is affected, as a recipient who comes to possess something is. -/
  | affected
  /-- The referent is less affected, or not at all. -/
  | nonaffected
  deriving DecidableEq, Fintype, Repr

/-- The case marker *ni* marks a noun phrase whose referent is affected, and the postposition one
whose referent is less affected (§4). -/
def Reading.particle : Reading → Particle
  | .affected => caseMarker
  | .nonaffected => postposition

/-- The affectedness hierarchy (45) places a noun phrase in a PP below the dative, and the dative
below the upper and the lower accusative. -/
inductive Position where
  /-- A noun phrase in a PP, the least affected. -/
  | npInPP
  /-- The dative, the indirect object. -/
  | dative
  /-- The upper accusative, a nonaffected theme. -/
  | upperAccusative
  /-- The lower accusative, an affected theme. -/
  | lowerAccusative
  deriving DecidableEq, Fintype, Repr

namespace Position

/-- `p.rank` is the place of `p` in (45), counting from the least affected. -/
def rank : Position → Fin 4
  | npInPP => 0
  | dative => 1
  | upperAccusative => 2
  | lowerAccusative => 3

instance : LinearOrder Position := LinearOrder.lift' rank (by decide)

/-- Koizumi's tree (44) puts the affected goal above the nonaffected theme above the affected
theme, `[VP NP-dat [V' [VP NP-acc [V' NP-acc V]] V]]`. -/
def tree44 : Tree Unit Unit :=
  bin (leaf ()) (bin (bin (leaf ()) (bin (leaf ()) (leaf ()))) (leaf ()))

/-- `p.site?` is the position of the argument `p` in `tree44`; the noun phrase in a PP, which the
paper adds to Koizumi's hierarchy, has none. -/
def site? : Position → Option TreePath
  | npInPP => none
  | dative => some ⟨[0]⟩
  | upperAccusative => some ⟨[1, 0, 0]⟩
  | lowerAccusative => some ⟨[1, 0, 1, 0]⟩

/-- Of two arguments of (44), the less affected c-commands the more affected, since
[koizumi-1994] links an argument's structural height inversely to its affectedness (§4). -/
theorem lt_iff_cCommands :
    ∀ p q : Position, ∀ a ∈ p.site?, ∀ b ∈ q.site?, p < q ↔ CCommands tree44 a b := by
  decide

end Position

/-! ### The examples -/

/-- The examples name the four particles by their constructors. -/
def particleLabels : List (String × Particle) :=
  [("caseMarker", caseMarker), ("postposition", postposition), ("insertion", insertion),
    ("copula", copula)]

/-- The examples name the three tests by their constructors. -/
def testLabels : List (String × Test) :=
  [("quantifierFloat", .quantifierFloat), ("cleftWithParticle", .cleftWithParticle),
    ("cleftWithoutParticle", .cleftWithoutParticle)]

/-- The examples name the two readings by their constructors. -/
def readingLabels : List (String × Reading) :=
  [("affected", .affected), ("nonaffected", .nonaffected)]

/-- The examples of (10) name the category of the copula's complement. -/
def focusLabels : List (String × Cat) := [("NP", .N), ("AP", .Adj), ("PP", .P)]

/-- `particles x` lists the particles the paper reads in `x`, two for an ambiguous *ni*. -/
def particles (x : Datum) : List Particle :=
  (x.features "particle").filterMap (List.lookup · particleLabels)

/-- `readings x` lists the readings the paper gives the *ni* phrase of `x`. -/
def readings (x : Datum) : List Reading :=
  (x.features "reading").filterMap (List.lookup · readingLabels)

/-- `test? x` is the test the example `x` applies, if any. -/
def test? (x : Datum) : Option Test := x.parse? "test" testLabels

theorem judgment_eq_acceptable_iff :
    ∀ x ∈ Examples.all, ∀ t, test? x = some t →
      (x.judgment = .acceptable ↔ ∃ p ∈ particles x, p.Passes t) := by
  decide +kernel

/-- The copula *da* takes an NP or a PP but not an AP ((10)). -/
theorem judgment_eq_acceptable_iff_caseAssignable :
    ∀ x ∈ Examples.all, ∀ c, x.parse? "focus" focusLabels = some c →
      (x.judgment = .acceptable ↔ CaseAssignable c) := by
  decide +kernel

/-- Where the paper reads an example for affectedness, *ni* is the case marker on an affected
reading and the postposition on a nonaffected one ((35)–(38)). -/
theorem particles_eq_map_readings :
    ∀ x ∈ Examples.all, readings x ≠ [] → particles x = (readings x).map Reading.particle := by
  decide +kernel

/-- A *ni* phrase hosts a floating quantifier exactly when its referent may be affected ((24b),
(38b)). -/
theorem judgment_eq_acceptable_iff_affected {x : Datum} (hx : x ∈ Examples.all)
    (ht : test? x = some .quantifierFloat) (hr : readings x ≠ []) :
    x.judgment = .acceptable ↔ .affected ∈ readings x := by
  rw [judgment_eq_acceptable_iff x hx _ ht, particles_eq_map_readings x hx hr]
  simp only [List.mem_map, passes_quantifierFloat_iff]
  constructor
  · rintro ⟨_, ⟨r, hr, rfl⟩, h⟩
    cases r
    · exact hr
    · cases h
  · exact fun h ↦ ⟨_, ⟨_, h, rfl⟩, rfl⟩

theorem caseMarker_form :
    ∀ x ∈ Examples.all, ∀ s, x.feature? "form" = some s → caseMarker ∈ particles x →
      ∃ c : Japanese.Case, s ∈ c.exponents.map (·.form) := by
  decide +kernel

theorem postposition_form :
    ∀ x ∈ Examples.all, ∀ s, x.feature? "form" = some s → postposition ∈ particles x →
      s ∈ Japanese.Case.dat.exponents.map (·.form) ∨
        ∃ p ∈ Japanese.Adpositions.inventory, p.morphs.map (·.form) = [s] := by
  decide +kernel

end SadakaneKoizumi1995
