module

public import Linglib.Syntax.Minimalist.Ellipsis
public import Linglib.Semantics.Root.Defs
public import Linglib.Data.Examples.Kalyakin2026

/-!
# Kalyakin (2026): VP ellipsis and argument structure alternations in Muira Dargwa

A Muira Dargwa complex predicate pairs a light verb, the head v, with a non-verbal element, a bare
root, and ellipsis can silence the object with the root while the light verb stays. Kalyakin
analyses this as v-stranding VP-ellipsis, Merchant's [E] on v deleting its complement, and the
paper's judgments [single out that position](##rows_predicted_iff): the silent root puts [E] above
V, and the restitutive reading of *again*, which survives, puts it below Voice. A root naming a
manner adjoins to v itself, and antipassivization coerces every root into that position, so such
a root [strands with the light verb](##spares_rootSite_position_iff) and cannot be elided.
Mismatches in v, the causative alternation and causativization, are tolerated, and an ellipsis
tolerating them [tolerates voice mismatches too](##tolerates_transitivity). Persian ellipsis
passes the same *again* test, so its ban on light-verb mismatches [needs Goldberg's Verbal
Identity Requirement](##persian_verbalIdentity) rather than a larger site.

## Implementation notes

* A root naming an end state merges with the direct object inside the complement of v, at the
  site of V; a root naming a manner adjoins to v and shares its site. The rows record the root's
  content in Beavers and Koontz-Garboden's kinds of entailment, `ArgumentStructure.Root.Kinds`.
* A row records the ellipsis clause, what it leaves silent, and how it differs from its
  antecedent. Causativization (78)–(80) is recorded as a transitivity mismatch: its causative head
  sits on top of vP or VoiceP, outside any site that spares v (`Tolerates.of_head_mem_below`).
* The antecedent's construction is not recorded, so (85) and (86) have one configuration, as the
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
  /-- The dimension in which the clause differs from its antecedent, if any. -/
  mismatch : Option Mismatch

/-- The clause is licit under the ellipsis `e`. A silent root lies in the site, and a pronounced
object has left it (§3.6); a pronounced *again* lies outside the site (§4.1); and a mismatch with
the antecedent is in a head outside it (§5). A pronounced root leaves only the object silent,
which argument ellipsis does (36b). -/
def Licit (e : Ellipsis clausalSpine) (c : Clause) : Prop :=
  (c.rootSilent = true →
      e.Deletes (rootSite (position c.root c.antipassive)) ∧
        (c.object.Pronounced → c.object.Escapes)) ∧
    (∀ r ∈ c.again, e.Spares r.site) ∧ ∀ m ∈ c.mismatch, e.Tolerates m

instance (e : Ellipsis clausalSpine) : DecidablePred (Licit e) := fun _ ↦
  inferInstanceAs (Decidable (_ ∧ _))

/-- An ellipsis clause of the paper with its judgment. -/
structure Row where
  clause : Clause
  judgment : Judgment

def Row.ofDatum (ex : Datum) : Option Row := do
  let k ← ex.parse? "root" [("state", ({.state} : Root.Kinds)), ("manner", {.manner})]
  let ap ← ex.parse? "antipassive" [("yes", true), ("no", false)]
  let s ← ex.parse? "rootSilent" [("yes", true), ("no", false)]
  let o ← ex.parse? "object"
    [("absent", ObjectStatus.absent), ("silent", .silent), ("inSitu", .inSitu),
      ("focused", .focused), ("moved", .moved), ("raised", .raised)]
  let a := ex.parse? "again"
    [("repetitive", AgainReading.repetitive), ("restitutive", .restitutive)]
  let m := ex.parse? "mismatch" [("transitivity", Mismatch.transitivity)]
  pure ⟨⟨{ kinds := k }, ap, s, o, a, m⟩, ex.judgment⟩

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
  refine ⟨fun h ↦ (eq_vStrandingVPE_iff e).2 ⟨?_, ?_⟩, fun he ↦ he ▸ rows_predicted⟩
  · obtain ⟨r, hr, hs, hp, hj⟩ : ∃ r ∈ rows, r.clause.rootSilent = true ∧
        position r.clause.root r.clause.antipassive = .complement ∧ r.judgment = .acceptable := by
      decide
    have := (((h r hr).1 hj).1 hs).1
    rwa [hp] at this
  · obtain ⟨r, hr, ha, hj⟩ : ∃ r ∈ rows,
        r.clause.again = some .restitutive ∧ r.judgment = .acceptable := by
      decide
    exact ((h r hr).1 hj).2.1 _ ha

/-! ### Mismatches -/

/-- The predictions of §5.4: an ellipsis tolerating transitivity mismatches tolerates voice
mismatches, Voice lying above v, and by Sailor's generalization so does every ellipsis whose [E]
sits lower. -/
theorem tolerates_transitivity {e e' : Ellipsis clausalSpine} (h : e.Tolerates .transitivity) :
    e.Tolerates .voice ∧
      (e'.ePosition ∈ clausalSpine.below e.ePosition → e'.Tolerates .transitivity) :=
  ⟨h.of_head_mem_below (by decide), h.of_mem_below⟩

/-- Goldberg's Verbal Identity Requirement (92) on a verb-stranding ellipsis: the stranded verb,
the head bearing [E], must match its antecedent too, so a mismatch is tolerated only when its head
is outside the site and is not the stranded head. -/
def ToleratesUnderVerbalIdentity (e : Ellipsis clausalSpine) (m : Mismatch) : Prop :=
  e.Tolerates m ∧ m.head ≠ e.ePosition

instance (e : Ellipsis clausalSpine) (m : Mismatch) :
    Decidable (ToleratesUnderVerbalIdentity e m) :=
  inferInstanceAs (Decidable (_ ∧ _))

-- (75), (76), (88)
theorem rows_violate_verbalIdentity : ∃ r ∈ rows, r.judgment = .acceptable ∧
    ∃ m ∈ r.clause.mismatch, ¬ ToleratesUnderVerbalIdentity vStrandingVPE m := by
  decide

/-- Persian (§6), after Toosarvandani. An ellipsis that silences the object with its root (89) and
spares restitutive *again* (90) is of Muira Dargwa's size and tolerates the light-verb mismatch
that (91) rejects; the Verbal Identity Requirement, which Toosarvandani rejects for Persian
(p. 38), bans it. -/
theorem persian_verbalIdentity {e : Ellipsis clausalSpine}
    (h89 : e.Deletes (rootSite .complement)) (h90 : e.Spares AgainReading.restitutive.site) :
    e.Tolerates .transitivity ∧ ¬ ToleratesUnderVerbalIdentity e .transitivity := by
  obtain rfl := (eq_vStrandingVPE_iff e).2 ⟨h89, h90⟩
  decide

-- p. 39 against p. 24 and (50)
theorem vpEllipsis_spares_low_adjuncts :
    vpEllipsis.Spares (.adjunct .v) ∧ vpEllipsis.Spares (.adjunct .Voice) := by
  decide

end Kalyakin2026
