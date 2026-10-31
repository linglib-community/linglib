module

public import Linglib.Syntax.Minimalist.Ellipsis
public import Linglib.Semantics.Root.Defs
public import Linglib.Data.Examples.Kalyakin2026
public import Linglib.Data.Examples.Readers

/-!
# Kalyakin (2026): VP ellipsis and argument structure alternations in Muira Dargwa

A Muira Dargwa complex predicate pairs a light verb, the head v, with a non-verbal element, a bare
root, and ellipsis can silence the object with the root while the light verb stays. Kalyakin
analyses this as v-stranding VP-ellipsis, Merchant's [E] on v deleting its complement, and the
paper's judgments [single out that position](##rows_predicted_iff): the silent root puts [E] above
V, and the restitutive reading of *again*, which survives, puts it below Voice. A root naming a
manner adjoins to v itself, and antipassivization coerces every root into that position, so such
a root [strands with the light verb](##spares_rootSite_position_iff) and cannot be elided.
Light-verb mismatches, the causative alternation and causativization, are tolerated, and an
ellipsis tolerating them [tolerates voice mismatches too](##spares_v). Persian ellipsis
passes the same *again* test, so its ban on light-verb mismatches [needs Goldberg's Verbal
Identity Requirement](##persian_verbalIdentity) rather than a larger site.

## Implementation notes

* A root naming an end state merges with the direct object inside the complement of v, at the
  site of V; a root naming a manner adjoins to v and shares its site. The rows record the root's
  content in Beavers and Koontz-Garboden's kinds of entailment, `ArgumentStructure.Root.Kinds`.
* An example is read off its glosses: the light verbs of its two clauses, whether the
  antecedent's root is pronounced in the ellipsis clause, its object and whether it is
  antipassive. Only the root's content and a contrastive focus, which the paper marks in its
  translations, are recorded as the paper states them. A difference between the light verbs is a
  mismatch at v, tolerated when the ellipsis spares v (`Minimalist.Ellipsis.identical_update_iff`);
  the causative suffix of (78)–(80) heads a projection on top of vP or VoiceP, so it is located
  with the light verb at v, the lowest head it could occupy.
* The antecedent's construction plays no part, so (85) and (86) have one configuration, as the
  paper's account of them requires: the root of an antipassive is too high to be deleted, whatever
  the antecedent.
* (58) and (59) are marked ?? and count as not acceptable; the paper reports that the prediction
  for activity predicates is borne out only partially, two consultants finding them merely
  degraded.
* Bangla fails the restitutive half of the *again* test (94), which `eq_vpEllipsis_iff` turns into
  [E] on Voice.

## Errata

* The paper infers from the larger size of Bangla's ellipsis that its missing adjuncts are
  recovered (95), but on the attachment it assumes for low adjuncts, vP or VoiceP (p. 24), the
  vP ellipsis of (50) spares them as it spares repetitive *again*
  (`vpEllipsis_spares_low_adjuncts`); (95) needs the adjunct below vP.

## TODO

* The identity condition, E-GIVENness (61) with the denotations (65)–(71), and the surface
  anaphora diagnostics of §3.1–§3.5.

## References

* [kalyakin-2026]
* [merchant-2013]
* [toosarvandani-2009]
* [goldberg-2005]
* [sailor-2014]
* [beavers-koontz-garboden-2020]
-/

@[expose] public section

namespace Kalyakin2026

open ArgumentStructure Minimalist Minimalist.Ellipsis

/-! ### The position of a root -/

/-- The site of a non-verbal element on the clausal spine: a root merged with the direct object
lies inside the complement of v (13), (14), and a root adjoined to v is part of v (12), (56). -/
def rootSite : Root.Position → ClauseSpine.Site
  | .complement => .head .V
  | .adjoined => .head .v

/-- The position of a root by its content (§2.2): one naming a manner adjoins to v, one naming an
end state merges with the object. Antipassivization coerces every root into the position of a
manner (§5.3). -/
def position (r : Root) (antipassive : Bool) : Root.Position :=
  if .manner ∈ r.kinds ∨ antipassive = true then .adjoined else .complement

-- (56)
theorem spares_rootSite_iff (p : Root.Position) :
    vStrandingVPE.Spares (rootSite p) ↔ p = .adjoined := by
  cases p
  · exact iff_of_false (fun h ↦ h (by decide)) (by decide)
  · exact iff_of_true vStrandingVPE.spares_ePosition rfl

/-- A root survives v-stranding ellipsis exactly when it names a manner or the clause is
antipassive: it is then part of the head bearing [E] and strands with the light verb ((57)–(59),
(85), (86)). -/
theorem spares_rootSite_position_iff (r : Root) (antipassive : Bool) :
    vStrandingVPE.Spares (rootSite (position r antipassive)) ↔
      .manner ∈ r.kinds ∨ antipassive = true := by
  rw [spares_rootSite_iff, position]
  split_ifs with h <;> simp [h]

/-! ### The ellipsis clauses -/

/-- The object of an ellipsis clause. -/
inductive ObjectStatus
  /-- The predicate has none (57)–(59). -/
  | absent
  /-- Silent with the root (3). -/
  | silent
  /-- Pronounced in its base position (36c). -/
  | inSitu
  /-- Moved out of the site as a contrastive focus (29), (30a), (37). -/
  | focused
  /-- Moved out of the site without contrastive focus (30b). -/
  | moved
  /-- Raised to subject, as an inchoative's argument is (32), (76), (88). -/
  | raised
  deriving DecidableEq, Repr

/-- The object is pronounced. -/
def ObjectStatus.Pronounced : ObjectStatus → Prop
  | .absent | .silent => False
  | _ => True

/-- The object has left the site by licensed movement: A′-movement sanctioned by contrastive focus
(§3.4) or A-movement to subject. -/
def ObjectStatus.Escapes : ObjectStatus → Prop
  | .focused | .raised => True
  | _ => False

instance : DecidablePred ObjectStatus.Pronounced := fun o ↦ by
  cases o <;> unfold ObjectStatus.Pronounced <;> infer_instance

instance : DecidablePred ObjectStatus.Escapes := fun o ↦ by
  cases o <;> unfold ObjectStatus.Escapes <;> infer_instance

/-- The light verbs of the paper's examples (4): *-arq'* ~ *-irq'* 'make', *-Ø* ~ *-irh* 'become',
*-uq* 'move' and *-ik'* 'say'. -/
inductive LightVerbStem
  | make
  | become
  | move
  | say
  deriving DecidableEq, Repr

/-- A light verb, with or without the causative suffix *-iq* (§5.2). -/
structure LightVerb where
  stem : LightVerbStem
  causative : Bool
  deriving DecidableEq, Repr

/-- An ellipsis clause of the paper. -/
structure Clause where
  /-- The root of the non-verbal element. -/
  root : Root
  /-- The clause is antipassive (81b). -/
  antipassive : Bool
  /-- The non-verbal element is silent. -/
  rootSilent : Bool
  /-- The object. -/
  object : ObjectStatus
  /-- The reading of the pronounced *again*, if any (52). -/
  again : Option AgainReading
  /-- The light verbs of the antecedent and of the elided clause. -/
  lightVerbs : LightVerb × LightVerb

/-- The sites the elided clause must spare: v when its light verb differs from the antecedent's,
and the adjunction site of a pronounced *again*. -/
def Clause.sites (c : Clause) : List ClauseSpine.Site :=
  (if c.lightVerbs.1 = c.lightVerbs.2 then [] else [.head .v]) ++
    c.again.toList.map AgainReading.site

/-- The clause is licit under the ellipsis `e`. A silent root lies in the site, and a pronounced
object has left it (§3.6); a pronounced *again* lies outside the site (§4.1); and a mismatch with
the antecedent is in a head outside it (§5). A pronounced root leaves only the object silent,
which argument ellipsis does (36b). -/
def Licit (e : Ellipsis clausalSpine) (c : Clause) : Prop :=
  (c.rootSilent = true →
      e.Deletes (rootSite (position c.root c.antipassive)) ∧
        (c.object.Pronounced → c.object.Escapes)) ∧
    ∀ x ∈ c.sites, e.Spares x

instance (e : Ellipsis clausalSpine) : DecidablePred (Licit e) := fun _ ↦
  inferInstanceAs (Decidable (_ ∧ _))

/-! ### Reading the examples

An example is read off its glosses in the paper's notation. Angle brackets enclose the elided
material, and a coindexed trace inside them marks an argument moved out of the site (§3.4). The
light verb of a clause is the token whose gloss names one of (4), and the antecedent clause ends
at the punctuation after its light verb; the rest is the ellipsis clause. -/

/-- A glossed token, its form and its gloss. -/
abbrev Token := String × String

/-- The word `p` occurs in `l`. -/
def occurs (p l : List Char) : Bool := l.tails.any p.isPrefixOf

/-- The gloss names the morpheme `m`, written after a hyphen and before a period, as the stems of
the light verbs are. -/
def glossesStem (g : String) (m : String) : Bool := occurs ('-' :: m.toList ++ ['.']) g.toList

/-- The light verb a gloss names, with the causative suffix if it carries one. -/
def lightVerb? (g : String) : Option LightVerb :=
  ([("make", LightVerbStem.make), ("become", .become), ("move", .move), ("say", .say)].find?
    fun (m, _) ↦ glossesStem g m).map fun (_, st) ↦ ⟨st, occurs "-CAUS".toList g.toList⟩

/-- The token's gloss marks it ergative. -/
def Token.ergative (t : Token) : Bool := occurs "ERG".toList t.2.toList

/-- The token's gloss marks it absolutive. -/
def Token.absolutive (t : Token) : Bool := occurs "ABS".toList t.2.toList

/-- The form of a token without brackets, punctuation and indices. -/
def Token.form (t : Token) : List Char :=
  t.1.toList.filter (· ∉ ['⟨', '⟩', ',', '.', '?', 'ᵢ'])

/-- The token is a trace. -/
def Token.trace (t : Token) : Bool := t.form == ['t']

/-- The tokens of a clause outside the angle brackets, and those inside. -/
def pronounced : List Token → Bool → List Token × List Token
  | [], _ => ([], [])
  | t :: ts, inside =>
    let inn := inside || t.1.toList.head? == some '⟨'
    let (p, e) := pronounced ts (inn && t.1.toList.getLast? != some '⟩')
    if inn then (p, t :: e) else (t :: p, e)

/-- The antecedent clause, up to the punctuation after its light verb, and the ellipsis clause. -/
def splitClauses (toks : List Token) : List Token × List Token :=
  let pre := toks.takeWhile fun t ↦ (lightVerb? t.2).isNone
  let post := toks.dropWhile fun t ↦ (lightVerb? t.2).isNone
  let n := post.findIdx (fun t ↦ t.1.toList.getLast? ∈ [some ',', some '.', some '?']) + 1
  (pre ++ post.take n, post.drop n)

/-- The object of the ellipsis clause, read off its tokens. A trace in the site marks an argument
moved out of it: raised to subject under an inchoative light verb, moved as a contrastive focus if
the paper marks one, and moved without focus otherwise. Without a trace, a pronounced absolutive
beside a pronounced ergative subject is an object in situ, an ergative clause or elided material
has a silent object, and a clause with neither has none. -/
def objectStatus (target : List Token) (lv : LightVerb) (focus : Bool) : ObjectStatus :=
  let (p, e) := pronounced target false
  if target.any Token.trace then
    if lv.stem = .become then .raised else if focus then .focused else .moved
  else if p.any Token.ergative && p.any Token.absolutive then .inSitu
  else if target.any Token.ergative || !e.isEmpty then .silent
  else .absent

/-- An ellipsis clause of the paper with its judgment. -/
structure Row where
  clause : Clause
  judgment : Judgment

/-- The clause of an example. The root's content and a contrastive focus are the paper's
statements; the rest is read off the glosses: the light verbs of the two clauses, whether the
antecedent's root is pronounced in the ellipsis clause, the object, and antipassivization, an
elided argument marked ergative (81b). -/
def Row.ofDatum (ex : Datum) : Option Row := do
  let k ← ex.parse? "root" [("state", ({.state} : Root.Kinds)), ("manner", {.manner})]
  let focus := ex.feature? "contrastiveFocus" == some "yes"
  let (ante, target) := splitClauses ex.glossedTokens
  let la ← ante.findSome? (lightVerb? ·.2)
  let lt ← (target.reverse.findSome? (lightVerb? ·.2))
  let nv ← (ante.takeWhile fun t ↦ (lightVerb? t.2).isNone).getLast?
  let (p, e) := pronounced target false
  let silent := !p.any (·.form == nv.form)
  let a := ex.readings.findSome? fun (n, _) ↦
    [("repetitive", AgainReading.repetitive), ("restitutive", .restitutive)].lookup n
  pure ⟨⟨{ kinds := k }, e.any Token.ergative, silent, objectStatus target lt focus, a, (la, lt)⟩,
    ex.judgment⟩

def rows : List Row := Examples.all.filterMap Row.ofDatum

theorem length_rows : rows.length = Examples.all.length := by decide

theorem rows_predicted :
    ∀ r ∈ rows, (r.judgment = .acceptable ↔ Licit vStrandingVPE r.clause) := by
  decide

/-- The judgments single out [E] on v: v-stranding VP-ellipsis is the only ellipsis of the clausal
spine under which exactly the acceptable clauses are licit. The silent root of (3) puts [E] above
V, and restitutive *again* in (52b) puts it below Voice (§4.1). -/
theorem rows_predicted_iff (e : Ellipsis clausalSpine) :
    (∀ r ∈ rows, (r.judgment = .acceptable ↔ Licit e r.clause)) ↔ e = vStrandingVPE := by
  refine ⟨fun h ↦ eq_vStrandingVPE_iff.2 ⟨?_, ?_⟩, fun he ↦ he ▸ rows_predicted⟩
  · obtain ⟨r, hr, hs, hp, hj⟩ : ∃ r ∈ rows, r.clause.rootSilent = true ∧
        position r.clause.root r.clause.antipassive = .complement ∧ r.judgment = .acceptable := by
      decide
    have := (((h r hr).1 hj).1 hs).1
    rwa [hp] at this
  · obtain ⟨r, hr, ha, hj⟩ : ∃ r ∈ rows,
        AgainReading.restitutive.site ∈ r.clause.sites ∧ r.judgment = .acceptable := by
      decide
    exact ((h r hr).1 hj).2 _ ha

/-! ### Mismatches -/

/-- The predictions of §5.4: an ellipsis sparing v, and so tolerating mismatches there, spares
Voice, which lies above it, and by Sailor's generalization so does every lower ellipsis. -/
theorem spares_v {e e' : Ellipsis clausalSpine} (h : e.Spares (.head .v)) :
    e.Spares (.head .Voice) ∧ (e' ≤ e → e'.Spares (.head .v)) :=
  ⟨fun hV ↦ h (hV.of_rank_le (by decide)), h.of_le⟩

/-- Goldberg's Verbal Identity Requirement (92) on a verb-stranding ellipsis: the stranded verb,
the head bearing [E], must match its antecedent too, so a mismatch at a site is tolerated only
when the site is outside the deletion domain and is not the stranded head. -/
def ToleratesUnderVerbalIdentity (e : Ellipsis clausalSpine) (x : ClauseSpine.Site) : Prop :=
  e.Spares x ∧ x ≠ .head e.ePosition

instance (e : Ellipsis clausalSpine) (x : ClauseSpine.Site) :
    Decidable (ToleratesUnderVerbalIdentity e x) :=
  inferInstanceAs (Decidable (_ ∧ _))

-- (75), (76), (88)
theorem rows_violate_verbalIdentity : ∃ r ∈ rows, r.judgment = .acceptable ∧
    ∃ x ∈ r.clause.sites, ¬ ToleratesUnderVerbalIdentity vStrandingVPE x := by
  decide

/-- Persian (§6), after Toosarvandani. An ellipsis that silences the object with its root (89) and
spares restitutive *again* (90) is of Muira Dargwa's size and spares the light verb whose mismatch
(91) rejects; the Verbal Identity Requirement, which Toosarvandani rejects for Persian (p. 38),
bans it. -/
theorem persian_verbalIdentity {e : Ellipsis clausalSpine}
    (h89 : e.Deletes (rootSite .complement)) (h90 : e.Spares AgainReading.restitutive.site) :
    e.Spares (.head .v) ∧ ¬ ToleratesUnderVerbalIdentity e (.head .v) := by
  obtain rfl := eq_vStrandingVPE_iff.2 ⟨h89, h90⟩
  decide

-- p. 39 against p. 24 and (50)
theorem vpEllipsis_spares_low_adjuncts :
    vpEllipsis.Spares (.adjunct .v) ∧ vpEllipsis.Spares (.adjunct .Voice) := by
  decide

end Kalyakin2026
