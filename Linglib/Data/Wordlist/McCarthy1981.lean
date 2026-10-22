module

public import Linglib.Data.Wordlist.Schema

/-!
# `McCarthy1981`: word forms

Auto-generated from `Linglib/Data/Wordlist/McCarthy1981.json` by `scripts/gen_wordlist.py`. Do not
edit by hand; edit the JSON and re-run the generator. Declarations live in `namespace
McCarthy1981.Wordlist`.
-/

@[expose] public section

namespace McCarthy1981.Wordlist

open Data.Wordlist

/-- The values of `Binyan` the source distinguishes. -/
inductive Binyan where
  /-- Binyan I, `I` in the source. -/
  | i
  /-- Binyan II, `II` in the source. -/
  | ii
  /-- Binyan III, `III` in the source. -/
  | iii
  /-- Binyan IV, `IV` in the source. -/
  | iv
  /-- Binyan V, `V` in the source. -/
  | v
  /-- Binyan VI, `VI` in the source. -/
  | vi
  /-- Binyan VII, `VII` in the source. -/
  | vii
  /-- Binyan VIII, `VIII` in the source. -/
  | viii
  /-- Binyan IX, `IX` in the source. -/
  | ix
  /-- Binyan X, `X` in the source. -/
  | x
  /-- Binyan XI, `XI` in the source. -/
  | xi
  /-- Binyan XII, `XII` in the source. -/
  | xii
  /-- Binyan XIII, `XIII` in the source. -/
  | xiii
  /-- Binyan XIV, `XIV` in the source. -/
  | xiv
  /-- Binyan XV, `XV` in the source. -/
  | xv
  /-- Binyan QI, `QI` in the source. -/
  | qi
  /-- Binyan QII, `QII` in the source. -/
  | qii
  /-- Binyan QIII, `QIII` in the source. -/
  | qiii
  /-- Binyan QIV, `QIV` in the source. -/
  | qiv
  deriving DecidableEq, Repr

/-- A cell of the source's tables, by its Universal Dependencies features and the features UD
lacks. -/
structure Cell extends UD.MorphFeatures where
  /-- The `Binyan` feature. -/
  binyan : Flat Binyan := ⊥
  deriving DecidableEq, Repr

/-- The binyan I perfective active cell, `Aspect=Perf|Voice=Act|Binyan=I`. -/
def I_perf_act : Cell := { aspect := ↑UD.Aspect.Perf, voice := ↑UD.Voice.Act, binyan := ↑Binyan.i }

/-- The binyan I perfective passive cell, `Aspect=Perf|Voice=Pass|Binyan=I`. -/
def I_perf_pas : Cell := { aspect := ↑UD.Aspect.Perf, voice := ↑UD.Voice.Pass, binyan := ↑Binyan.i }

/-- The binyan I imperfective active cell, `Aspect=Imp|Voice=Act|Binyan=I`. -/
def I_impe_act : Cell := { aspect := ↑UD.Aspect.Imp, voice := ↑UD.Voice.Act, binyan := ↑Binyan.i }

/-- The binyan I imperfective passive cell, `Aspect=Imp|Voice=Pass|Binyan=I`. -/
def I_impe_pas : Cell := { aspect := ↑UD.Aspect.Imp, voice := ↑UD.Voice.Pass, binyan := ↑Binyan.i }

/-- The binyan I participle active cell, `VerbForm=Part|Voice=Act|Binyan=I`. -/
def I_part_act : Cell :=
  { verbForm := ↑UD.VerbForm.Part, voice := ↑UD.Voice.Act, binyan := ↑Binyan.i }

/-- The binyan I participle passive cell, `VerbForm=Part|Voice=Pass|Binyan=I`. -/
def I_part_pas : Cell :=
  { verbForm := ↑UD.VerbForm.Part, voice := ↑UD.Voice.Pass, binyan := ↑Binyan.i }

/-- The binyan II perfective active cell, `Aspect=Perf|Voice=Act|Binyan=II`. -/
def II_perf_act : Cell :=
  { aspect := ↑UD.Aspect.Perf, voice := ↑UD.Voice.Act, binyan := ↑Binyan.ii }

/-- The binyan II perfective passive cell, `Aspect=Perf|Voice=Pass|Binyan=II`. -/
def II_perf_pas : Cell :=
  { aspect := ↑UD.Aspect.Perf, voice := ↑UD.Voice.Pass, binyan := ↑Binyan.ii }

/-- The binyan II imperfective active cell, `Aspect=Imp|Voice=Act|Binyan=II`. -/
def II_impe_act : Cell := { aspect := ↑UD.Aspect.Imp, voice := ↑UD.Voice.Act, binyan := ↑Binyan.ii }

/-- The binyan II imperfective passive cell, `Aspect=Imp|Voice=Pass|Binyan=II`. -/
def II_impe_pas : Cell :=
  { aspect := ↑UD.Aspect.Imp, voice := ↑UD.Voice.Pass, binyan := ↑Binyan.ii }

/-- The binyan II participle active cell, `VerbForm=Part|Voice=Act|Binyan=II`. -/
def II_part_act : Cell :=
  { verbForm := ↑UD.VerbForm.Part, voice := ↑UD.Voice.Act, binyan := ↑Binyan.ii }

/-- The binyan II participle passive cell, `VerbForm=Part|Voice=Pass|Binyan=II`. -/
def II_part_pas : Cell :=
  { verbForm := ↑UD.VerbForm.Part, voice := ↑UD.Voice.Pass, binyan := ↑Binyan.ii }

/-- The binyan III perfective active cell, `Aspect=Perf|Voice=Act|Binyan=III`. -/
def III_perf_act : Cell :=
  { aspect := ↑UD.Aspect.Perf, voice := ↑UD.Voice.Act, binyan := ↑Binyan.iii }

/-- The binyan III perfective passive cell, `Aspect=Perf|Voice=Pass|Binyan=III`. -/
def III_perf_pas : Cell :=
  { aspect := ↑UD.Aspect.Perf, voice := ↑UD.Voice.Pass, binyan := ↑Binyan.iii }

/-- The binyan III imperfective active cell, `Aspect=Imp|Voice=Act|Binyan=III`. -/
def III_impe_act : Cell :=
  { aspect := ↑UD.Aspect.Imp, voice := ↑UD.Voice.Act, binyan := ↑Binyan.iii }

/-- The binyan III imperfective passive cell, `Aspect=Imp|Voice=Pass|Binyan=III`. -/
def III_impe_pas : Cell :=
  { aspect := ↑UD.Aspect.Imp, voice := ↑UD.Voice.Pass, binyan := ↑Binyan.iii }

/-- The binyan III participle active cell, `VerbForm=Part|Voice=Act|Binyan=III`. -/
def III_part_act : Cell :=
  { verbForm := ↑UD.VerbForm.Part, voice := ↑UD.Voice.Act, binyan := ↑Binyan.iii }

/-- The binyan III participle passive cell, `VerbForm=Part|Voice=Pass|Binyan=III`. -/
def III_part_pas : Cell :=
  { verbForm := ↑UD.VerbForm.Part, voice := ↑UD.Voice.Pass, binyan := ↑Binyan.iii }

/-- The binyan IV perfective active cell, `Aspect=Perf|Voice=Act|Binyan=IV`. -/
def IV_perf_act : Cell :=
  { aspect := ↑UD.Aspect.Perf, voice := ↑UD.Voice.Act, binyan := ↑Binyan.iv }

/-- The binyan IV perfective passive cell, `Aspect=Perf|Voice=Pass|Binyan=IV`. -/
def IV_perf_pas : Cell :=
  { aspect := ↑UD.Aspect.Perf, voice := ↑UD.Voice.Pass, binyan := ↑Binyan.iv }

/-- The binyan IV imperfective active cell, `Aspect=Imp|Voice=Act|Binyan=IV`. -/
def IV_impe_act : Cell := { aspect := ↑UD.Aspect.Imp, voice := ↑UD.Voice.Act, binyan := ↑Binyan.iv }

/-- The binyan IV imperfective passive cell, `Aspect=Imp|Voice=Pass|Binyan=IV`. -/
def IV_impe_pas : Cell :=
  { aspect := ↑UD.Aspect.Imp, voice := ↑UD.Voice.Pass, binyan := ↑Binyan.iv }

/-- The binyan IV participle active cell, `VerbForm=Part|Voice=Act|Binyan=IV`. -/
def IV_part_act : Cell :=
  { verbForm := ↑UD.VerbForm.Part, voice := ↑UD.Voice.Act, binyan := ↑Binyan.iv }

/-- The binyan IV participle passive cell, `VerbForm=Part|Voice=Pass|Binyan=IV`. -/
def IV_part_pas : Cell :=
  { verbForm := ↑UD.VerbForm.Part, voice := ↑UD.Voice.Pass, binyan := ↑Binyan.iv }

/-- The binyan V perfective active cell, `Aspect=Perf|Voice=Act|Binyan=V`. -/
def V_perf_act : Cell := { aspect := ↑UD.Aspect.Perf, voice := ↑UD.Voice.Act, binyan := ↑Binyan.v }

/-- The binyan V perfective passive cell, `Aspect=Perf|Voice=Pass|Binyan=V`. -/
def V_perf_pas : Cell := { aspect := ↑UD.Aspect.Perf, voice := ↑UD.Voice.Pass, binyan := ↑Binyan.v }

/-- The binyan V imperfective active cell, `Aspect=Imp|Voice=Act|Binyan=V`. -/
def V_impe_act : Cell := { aspect := ↑UD.Aspect.Imp, voice := ↑UD.Voice.Act, binyan := ↑Binyan.v }

/-- The binyan V imperfective passive cell, `Aspect=Imp|Voice=Pass|Binyan=V`. -/
def V_impe_pas : Cell := { aspect := ↑UD.Aspect.Imp, voice := ↑UD.Voice.Pass, binyan := ↑Binyan.v }

/-- The binyan V participle active cell, `VerbForm=Part|Voice=Act|Binyan=V`. -/
def V_part_act : Cell :=
  { verbForm := ↑UD.VerbForm.Part, voice := ↑UD.Voice.Act, binyan := ↑Binyan.v }

/-- The binyan V participle passive cell, `VerbForm=Part|Voice=Pass|Binyan=V`. -/
def V_part_pas : Cell :=
  { verbForm := ↑UD.VerbForm.Part, voice := ↑UD.Voice.Pass, binyan := ↑Binyan.v }

/-- The binyan VI perfective active cell, `Aspect=Perf|Voice=Act|Binyan=VI`. -/
def VI_perf_act : Cell :=
  { aspect := ↑UD.Aspect.Perf, voice := ↑UD.Voice.Act, binyan := ↑Binyan.vi }

/-- The binyan VI perfective passive cell, `Aspect=Perf|Voice=Pass|Binyan=VI`. -/
def VI_perf_pas : Cell :=
  { aspect := ↑UD.Aspect.Perf, voice := ↑UD.Voice.Pass, binyan := ↑Binyan.vi }

/-- The binyan VI imperfective active cell, `Aspect=Imp|Voice=Act|Binyan=VI`. -/
def VI_impe_act : Cell := { aspect := ↑UD.Aspect.Imp, voice := ↑UD.Voice.Act, binyan := ↑Binyan.vi }

/-- The binyan VI imperfective passive cell, `Aspect=Imp|Voice=Pass|Binyan=VI`. -/
def VI_impe_pas : Cell :=
  { aspect := ↑UD.Aspect.Imp, voice := ↑UD.Voice.Pass, binyan := ↑Binyan.vi }

/-- The binyan VI participle active cell, `VerbForm=Part|Voice=Act|Binyan=VI`. -/
def VI_part_act : Cell :=
  { verbForm := ↑UD.VerbForm.Part, voice := ↑UD.Voice.Act, binyan := ↑Binyan.vi }

/-- The binyan VI participle passive cell, `VerbForm=Part|Voice=Pass|Binyan=VI`. -/
def VI_part_pas : Cell :=
  { verbForm := ↑UD.VerbForm.Part, voice := ↑UD.Voice.Pass, binyan := ↑Binyan.vi }

/-- The binyan VII perfective active cell, `Aspect=Perf|Voice=Act|Binyan=VII`. -/
def VII_perf_act : Cell :=
  { aspect := ↑UD.Aspect.Perf, voice := ↑UD.Voice.Act, binyan := ↑Binyan.vii }

/-- The binyan VII perfective passive cell, `Aspect=Perf|Voice=Pass|Binyan=VII`. -/
def VII_perf_pas : Cell :=
  { aspect := ↑UD.Aspect.Perf, voice := ↑UD.Voice.Pass, binyan := ↑Binyan.vii }

/-- The binyan VII imperfective active cell, `Aspect=Imp|Voice=Act|Binyan=VII`. -/
def VII_impe_act : Cell :=
  { aspect := ↑UD.Aspect.Imp, voice := ↑UD.Voice.Act, binyan := ↑Binyan.vii }

/-- The binyan VII imperfective passive cell, `Aspect=Imp|Voice=Pass|Binyan=VII`. -/
def VII_impe_pas : Cell :=
  { aspect := ↑UD.Aspect.Imp, voice := ↑UD.Voice.Pass, binyan := ↑Binyan.vii }

/-- The binyan VII participle active cell, `VerbForm=Part|Voice=Act|Binyan=VII`. -/
def VII_part_act : Cell :=
  { verbForm := ↑UD.VerbForm.Part, voice := ↑UD.Voice.Act, binyan := ↑Binyan.vii }

/-- The binyan VII participle passive cell, `VerbForm=Part|Voice=Pass|Binyan=VII`. -/
def VII_part_pas : Cell :=
  { verbForm := ↑UD.VerbForm.Part, voice := ↑UD.Voice.Pass, binyan := ↑Binyan.vii }

/-- The binyan VIII perfective active cell, `Aspect=Perf|Voice=Act|Binyan=VIII`. -/
def VIII_perf_act : Cell :=
  { aspect := ↑UD.Aspect.Perf, voice := ↑UD.Voice.Act, binyan := ↑Binyan.viii }

/-- The binyan VIII perfective passive cell, `Aspect=Perf|Voice=Pass|Binyan=VIII`. -/
def VIII_perf_pas : Cell :=
  { aspect := ↑UD.Aspect.Perf, voice := ↑UD.Voice.Pass, binyan := ↑Binyan.viii }

/-- The binyan VIII imperfective active cell, `Aspect=Imp|Voice=Act|Binyan=VIII`. -/
def VIII_impe_act : Cell :=
  { aspect := ↑UD.Aspect.Imp, voice := ↑UD.Voice.Act, binyan := ↑Binyan.viii }

/-- The binyan VIII imperfective passive cell, `Aspect=Imp|Voice=Pass|Binyan=VIII`. -/
def VIII_impe_pas : Cell :=
  { aspect := ↑UD.Aspect.Imp, voice := ↑UD.Voice.Pass, binyan := ↑Binyan.viii }

/-- The binyan VIII participle active cell, `VerbForm=Part|Voice=Act|Binyan=VIII`. -/
def VIII_part_act : Cell :=
  { verbForm := ↑UD.VerbForm.Part, voice := ↑UD.Voice.Act, binyan := ↑Binyan.viii }

/-- The binyan VIII participle passive cell, `VerbForm=Part|Voice=Pass|Binyan=VIII`. -/
def VIII_part_pas : Cell :=
  { verbForm := ↑UD.VerbForm.Part, voice := ↑UD.Voice.Pass, binyan := ↑Binyan.viii }

/-- The binyan IX perfective active cell, `Aspect=Perf|Voice=Act|Binyan=IX`. -/
def IX_perf_act : Cell :=
  { aspect := ↑UD.Aspect.Perf, voice := ↑UD.Voice.Act, binyan := ↑Binyan.ix }

/-- The binyan IX imperfective active cell, `Aspect=Imp|Voice=Act|Binyan=IX`. -/
def IX_impe_act : Cell := { aspect := ↑UD.Aspect.Imp, voice := ↑UD.Voice.Act, binyan := ↑Binyan.ix }

/-- The binyan IX participle active cell, `VerbForm=Part|Voice=Act|Binyan=IX`. -/
def IX_part_act : Cell :=
  { verbForm := ↑UD.VerbForm.Part, voice := ↑UD.Voice.Act, binyan := ↑Binyan.ix }

/-- The binyan X perfective active cell, `Aspect=Perf|Voice=Act|Binyan=X`. -/
def X_perf_act : Cell := { aspect := ↑UD.Aspect.Perf, voice := ↑UD.Voice.Act, binyan := ↑Binyan.x }

/-- The binyan X perfective passive cell, `Aspect=Perf|Voice=Pass|Binyan=X`. -/
def X_perf_pas : Cell := { aspect := ↑UD.Aspect.Perf, voice := ↑UD.Voice.Pass, binyan := ↑Binyan.x }

/-- The binyan X imperfective active cell, `Aspect=Imp|Voice=Act|Binyan=X`. -/
def X_impe_act : Cell := { aspect := ↑UD.Aspect.Imp, voice := ↑UD.Voice.Act, binyan := ↑Binyan.x }

/-- The binyan X imperfective passive cell, `Aspect=Imp|Voice=Pass|Binyan=X`. -/
def X_impe_pas : Cell := { aspect := ↑UD.Aspect.Imp, voice := ↑UD.Voice.Pass, binyan := ↑Binyan.x }

/-- The binyan X participle active cell, `VerbForm=Part|Voice=Act|Binyan=X`. -/
def X_part_act : Cell :=
  { verbForm := ↑UD.VerbForm.Part, voice := ↑UD.Voice.Act, binyan := ↑Binyan.x }

/-- The binyan X participle passive cell, `VerbForm=Part|Voice=Pass|Binyan=X`. -/
def X_part_pas : Cell :=
  { verbForm := ↑UD.VerbForm.Part, voice := ↑UD.Voice.Pass, binyan := ↑Binyan.x }

/-- The binyan XI perfective active cell, `Aspect=Perf|Voice=Act|Binyan=XI`. -/
def XI_perf_act : Cell :=
  { aspect := ↑UD.Aspect.Perf, voice := ↑UD.Voice.Act, binyan := ↑Binyan.xi }

/-- The binyan XI imperfective active cell, `Aspect=Imp|Voice=Act|Binyan=XI`. -/
def XI_impe_act : Cell := { aspect := ↑UD.Aspect.Imp, voice := ↑UD.Voice.Act, binyan := ↑Binyan.xi }

/-- The binyan XI participle active cell, `VerbForm=Part|Voice=Act|Binyan=XI`. -/
def XI_part_act : Cell :=
  { verbForm := ↑UD.VerbForm.Part, voice := ↑UD.Voice.Act, binyan := ↑Binyan.xi }

/-- The binyan XII perfective active cell, `Aspect=Perf|Voice=Act|Binyan=XII`. -/
def XII_perf_act : Cell :=
  { aspect := ↑UD.Aspect.Perf, voice := ↑UD.Voice.Act, binyan := ↑Binyan.xii }

/-- The binyan XII imperfective active cell, `Aspect=Imp|Voice=Act|Binyan=XII`. -/
def XII_impe_act : Cell :=
  { aspect := ↑UD.Aspect.Imp, voice := ↑UD.Voice.Act, binyan := ↑Binyan.xii }

/-- The binyan XII participle active cell, `VerbForm=Part|Voice=Act|Binyan=XII`. -/
def XII_part_act : Cell :=
  { verbForm := ↑UD.VerbForm.Part, voice := ↑UD.Voice.Act, binyan := ↑Binyan.xii }

/-- The binyan XIII perfective active cell, `Aspect=Perf|Voice=Act|Binyan=XIII`. -/
def XIII_perf_act : Cell :=
  { aspect := ↑UD.Aspect.Perf, voice := ↑UD.Voice.Act, binyan := ↑Binyan.xiii }

/-- The binyan XIII imperfective active cell, `Aspect=Imp|Voice=Act|Binyan=XIII`. -/
def XIII_impe_act : Cell :=
  { aspect := ↑UD.Aspect.Imp, voice := ↑UD.Voice.Act, binyan := ↑Binyan.xiii }

/-- The binyan XIII participle active cell, `VerbForm=Part|Voice=Act|Binyan=XIII`. -/
def XIII_part_act : Cell :=
  { verbForm := ↑UD.VerbForm.Part, voice := ↑UD.Voice.Act, binyan := ↑Binyan.xiii }

/-- The binyan XIV perfective active cell, `Aspect=Perf|Voice=Act|Binyan=XIV`. -/
def XIV_perf_act : Cell :=
  { aspect := ↑UD.Aspect.Perf, voice := ↑UD.Voice.Act, binyan := ↑Binyan.xiv }

/-- The binyan XIV imperfective active cell, `Aspect=Imp|Voice=Act|Binyan=XIV`. -/
def XIV_impe_act : Cell :=
  { aspect := ↑UD.Aspect.Imp, voice := ↑UD.Voice.Act, binyan := ↑Binyan.xiv }

/-- The binyan XIV participle active cell, `VerbForm=Part|Voice=Act|Binyan=XIV`. -/
def XIV_part_act : Cell :=
  { verbForm := ↑UD.VerbForm.Part, voice := ↑UD.Voice.Act, binyan := ↑Binyan.xiv }

/-- The binyan XV perfective active cell, `Aspect=Perf|Voice=Act|Binyan=XV`. -/
def XV_perf_act : Cell :=
  { aspect := ↑UD.Aspect.Perf, voice := ↑UD.Voice.Act, binyan := ↑Binyan.xv }

/-- The binyan XV imperfective active cell, `Aspect=Imp|Voice=Act|Binyan=XV`. -/
def XV_impe_act : Cell := { aspect := ↑UD.Aspect.Imp, voice := ↑UD.Voice.Act, binyan := ↑Binyan.xv }

/-- The binyan XV participle active cell, `VerbForm=Part|Voice=Act|Binyan=XV`. -/
def XV_part_act : Cell :=
  { verbForm := ↑UD.VerbForm.Part, voice := ↑UD.Voice.Act, binyan := ↑Binyan.xv }

/-- The binyan QI perfective active cell, `Aspect=Perf|Voice=Act|Binyan=QI`. -/
def QI_perf_act : Cell :=
  { aspect := ↑UD.Aspect.Perf, voice := ↑UD.Voice.Act, binyan := ↑Binyan.qi }

/-- The binyan QI perfective passive cell, `Aspect=Perf|Voice=Pass|Binyan=QI`. -/
def QI_perf_pas : Cell :=
  { aspect := ↑UD.Aspect.Perf, voice := ↑UD.Voice.Pass, binyan := ↑Binyan.qi }

/-- The binyan QI imperfective active cell, `Aspect=Imp|Voice=Act|Binyan=QI`. -/
def QI_impe_act : Cell := { aspect := ↑UD.Aspect.Imp, voice := ↑UD.Voice.Act, binyan := ↑Binyan.qi }

/-- The binyan QI imperfective passive cell, `Aspect=Imp|Voice=Pass|Binyan=QI`. -/
def QI_impe_pas : Cell :=
  { aspect := ↑UD.Aspect.Imp, voice := ↑UD.Voice.Pass, binyan := ↑Binyan.qi }

/-- The binyan QI participle active cell, `VerbForm=Part|Voice=Act|Binyan=QI`. -/
def QI_part_act : Cell :=
  { verbForm := ↑UD.VerbForm.Part, voice := ↑UD.Voice.Act, binyan := ↑Binyan.qi }

/-- The binyan QI participle passive cell, `VerbForm=Part|Voice=Pass|Binyan=QI`. -/
def QI_part_pas : Cell :=
  { verbForm := ↑UD.VerbForm.Part, voice := ↑UD.Voice.Pass, binyan := ↑Binyan.qi }

/-- The binyan QII perfective active cell, `Aspect=Perf|Voice=Act|Binyan=QII`. -/
def QII_perf_act : Cell :=
  { aspect := ↑UD.Aspect.Perf, voice := ↑UD.Voice.Act, binyan := ↑Binyan.qii }

/-- The binyan QII perfective passive cell, `Aspect=Perf|Voice=Pass|Binyan=QII`. -/
def QII_perf_pas : Cell :=
  { aspect := ↑UD.Aspect.Perf, voice := ↑UD.Voice.Pass, binyan := ↑Binyan.qii }

/-- The binyan QII imperfective active cell, `Aspect=Imp|Voice=Act|Binyan=QII`. -/
def QII_impe_act : Cell :=
  { aspect := ↑UD.Aspect.Imp, voice := ↑UD.Voice.Act, binyan := ↑Binyan.qii }

/-- The binyan QII imperfective passive cell, `Aspect=Imp|Voice=Pass|Binyan=QII`. -/
def QII_impe_pas : Cell :=
  { aspect := ↑UD.Aspect.Imp, voice := ↑UD.Voice.Pass, binyan := ↑Binyan.qii }

/-- The binyan QII participle active cell, `VerbForm=Part|Voice=Act|Binyan=QII`. -/
def QII_part_act : Cell :=
  { verbForm := ↑UD.VerbForm.Part, voice := ↑UD.Voice.Act, binyan := ↑Binyan.qii }

/-- The binyan QII participle passive cell, `VerbForm=Part|Voice=Pass|Binyan=QII`. -/
def QII_part_pas : Cell :=
  { verbForm := ↑UD.VerbForm.Part, voice := ↑UD.Voice.Pass, binyan := ↑Binyan.qii }

/-- The binyan QIII perfective active cell, `Aspect=Perf|Voice=Act|Binyan=QIII`. -/
def QIII_perf_act : Cell :=
  { aspect := ↑UD.Aspect.Perf, voice := ↑UD.Voice.Act, binyan := ↑Binyan.qiii }

/-- The binyan QIII perfective passive cell, `Aspect=Perf|Voice=Pass|Binyan=QIII`. -/
def QIII_perf_pas : Cell :=
  { aspect := ↑UD.Aspect.Perf, voice := ↑UD.Voice.Pass, binyan := ↑Binyan.qiii }

/-- The binyan QIII imperfective active cell, `Aspect=Imp|Voice=Act|Binyan=QIII`. -/
def QIII_impe_act : Cell :=
  { aspect := ↑UD.Aspect.Imp, voice := ↑UD.Voice.Act, binyan := ↑Binyan.qiii }

/-- The binyan QIII imperfective passive cell, `Aspect=Imp|Voice=Pass|Binyan=QIII`. -/
def QIII_impe_pas : Cell :=
  { aspect := ↑UD.Aspect.Imp, voice := ↑UD.Voice.Pass, binyan := ↑Binyan.qiii }

/-- The binyan QIII participle active cell, `VerbForm=Part|Voice=Act|Binyan=QIII`. -/
def QIII_part_act : Cell :=
  { verbForm := ↑UD.VerbForm.Part, voice := ↑UD.Voice.Act, binyan := ↑Binyan.qiii }

/-- The binyan QIII participle passive cell, `VerbForm=Part|Voice=Pass|Binyan=QIII`. -/
def QIII_part_pas : Cell :=
  { verbForm := ↑UD.VerbForm.Part, voice := ↑UD.Voice.Pass, binyan := ↑Binyan.qiii }

/-- The binyan QIV perfective active cell, `Aspect=Perf|Voice=Act|Binyan=QIV`. -/
def QIV_perf_act : Cell :=
  { aspect := ↑UD.Aspect.Perf, voice := ↑UD.Voice.Act, binyan := ↑Binyan.qiv }

/-- The binyan QIV perfective passive cell, `Aspect=Perf|Voice=Pass|Binyan=QIV`. -/
def QIV_perf_pas : Cell :=
  { aspect := ↑UD.Aspect.Perf, voice := ↑UD.Voice.Pass, binyan := ↑Binyan.qiv }

/-- The binyan QIV imperfective active cell, `Aspect=Imp|Voice=Act|Binyan=QIV`. -/
def QIV_impe_act : Cell :=
  { aspect := ↑UD.Aspect.Imp, voice := ↑UD.Voice.Act, binyan := ↑Binyan.qiv }

/-- The binyan QIV imperfective passive cell, `Aspect=Imp|Voice=Pass|Binyan=QIV`. -/
def QIV_impe_pas : Cell :=
  { aspect := ↑UD.Aspect.Imp, voice := ↑UD.Voice.Pass, binyan := ↑Binyan.qiv }

/-- The binyan QIV participle active cell, `VerbForm=Part|Voice=Act|Binyan=QIV`. -/
def QIV_part_act : Cell :=
  { verbForm := ↑UD.VerbForm.Part, voice := ↑UD.Voice.Act, binyan := ↑Binyan.qiv }

/-- The binyan QIV participle passive cell, `VerbForm=Part|Voice=Pass|Binyan=QIV`. -/
def QIV_part_pas : Cell :=
  { verbForm := ↑UD.VerbForm.Part, voice := ↑UD.Voice.Pass, binyan := ↑Binyan.qiv }

def Lexemes.write : Lexeme :=
  { id := "write", languageId := "clas1259", parameterId := "write" }

def Lexemes.roll : Lexeme :=
  { id := "roll", languageId := "clas1259", parameterId := "roll" }

def Lexemes.poison : Lexeme :=
  { id := "poison", languageId := "clas1259", parameterId := "poison" }

def Lexemes.magnetize : Lexeme :=
  { id := "magnetize", languageId := "clas1259", parameterId := "magnetize" }

def ktb_I_perf_act : Form Cell :=
  { id := "mccarthy1981_ktb_I_perf_act"
    lexeme := Lexemes.write
    cell := I_perf_act
    form := "katab"
    segments := ["k", "a", "t", "a", "b"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def ktb_I_perf_pas : Form Cell :=
  { id := "mccarthy1981_ktb_I_perf_pas"
    lexeme := Lexemes.write
    cell := I_perf_pas
    form := "kutib"
    segments := ["k", "u", "t", "i", "b"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def ktb_I_impe_act : Form Cell :=
  { id := "mccarthy1981_ktb_I_impe_act"
    lexeme := Lexemes.write
    cell := I_impe_act
    form := "aktub"
    segments := ["a", "k", "t", "u", "b"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def ktb_I_impe_pas : Form Cell :=
  { id := "mccarthy1981_ktb_I_impe_pas"
    lexeme := Lexemes.write
    cell := I_impe_pas
    form := "uktab"
    segments := ["u", "k", "t", "a", "b"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def ktb_I_part_act : Form Cell :=
  { id := "mccarthy1981_ktb_I_part_act"
    lexeme := Lexemes.write
    cell := I_part_act
    form := "kaatib"
    segments := ["k", "a", "a", "t", "i", "b"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def ktb_I_part_pas : Form Cell :=
  { id := "mccarthy1981_ktb_I_part_pas"
    lexeme := Lexemes.write
    cell := I_part_pas
    form := "maktuub"
    segments := ["m", "a", "k", "t", "u", "u", "b"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def ktb_II_perf_act : Form Cell :=
  { id := "mccarthy1981_ktb_II_perf_act"
    lexeme := Lexemes.write
    cell := II_perf_act
    form := "kattab"
    segments := ["k", "a", "t", "t", "a", "b"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def ktb_II_perf_pas : Form Cell :=
  { id := "mccarthy1981_ktb_II_perf_pas"
    lexeme := Lexemes.write
    cell := II_perf_pas
    form := "kuttib"
    segments := ["k", "u", "t", "t", "i", "b"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def ktb_II_impe_act : Form Cell :=
  { id := "mccarthy1981_ktb_II_impe_act"
    lexeme := Lexemes.write
    cell := II_impe_act
    form := "ukattib"
    segments := ["u", "k", "a", "t", "t", "i", "b"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def ktb_II_impe_pas : Form Cell :=
  { id := "mccarthy1981_ktb_II_impe_pas"
    lexeme := Lexemes.write
    cell := II_impe_pas
    form := "ukattab"
    segments := ["u", "k", "a", "t", "t", "a", "b"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def ktb_II_part_act : Form Cell :=
  { id := "mccarthy1981_ktb_II_part_act"
    lexeme := Lexemes.write
    cell := II_part_act
    form := "mukattib"
    segments := ["m", "u", "k", "a", "t", "t", "i", "b"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def ktb_II_part_pas : Form Cell :=
  { id := "mccarthy1981_ktb_II_part_pas"
    lexeme := Lexemes.write
    cell := II_part_pas
    form := "mukattab"
    segments := ["m", "u", "k", "a", "t", "t", "a", "b"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def ktb_III_perf_act : Form Cell :=
  { id := "mccarthy1981_ktb_III_perf_act"
    lexeme := Lexemes.write
    cell := III_perf_act
    form := "kaatab"
    segments := ["k", "a", "a", "t", "a", "b"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def ktb_III_perf_pas : Form Cell :=
  { id := "mccarthy1981_ktb_III_perf_pas"
    lexeme := Lexemes.write
    cell := III_perf_pas
    form := "kuutib"
    segments := ["k", "u", "u", "t", "i", "b"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def ktb_III_impe_act : Form Cell :=
  { id := "mccarthy1981_ktb_III_impe_act"
    lexeme := Lexemes.write
    cell := III_impe_act
    form := "ukaatib"
    segments := ["u", "k", "a", "a", "t", "i", "b"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def ktb_III_impe_pas : Form Cell :=
  { id := "mccarthy1981_ktb_III_impe_pas"
    lexeme := Lexemes.write
    cell := III_impe_pas
    form := "ukaatab"
    segments := ["u", "k", "a", "a", "t", "a", "b"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def ktb_III_part_act : Form Cell :=
  { id := "mccarthy1981_ktb_III_part_act"
    lexeme := Lexemes.write
    cell := III_part_act
    form := "mukaatib"
    segments := ["m", "u", "k", "a", "a", "t", "i", "b"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def ktb_III_part_pas : Form Cell :=
  { id := "mccarthy1981_ktb_III_part_pas"
    lexeme := Lexemes.write
    cell := III_part_pas
    form := "mukaatab"
    segments := ["m", "u", "k", "a", "a", "t", "a", "b"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def ktb_IV_perf_act : Form Cell :=
  { id := "mccarthy1981_ktb_IV_perf_act"
    lexeme := Lexemes.write
    cell := IV_perf_act
    form := "ʔaktab"
    segments := ["ʔ", "a", "k", "t", "a", "b"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def ktb_IV_perf_pas : Form Cell :=
  { id := "mccarthy1981_ktb_IV_perf_pas"
    lexeme := Lexemes.write
    cell := IV_perf_pas
    form := "ʔuktib"
    segments := ["ʔ", "u", "k", "t", "i", "b"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def ktb_IV_impe_act : Form Cell :=
  { id := "mccarthy1981_ktb_IV_impe_act"
    lexeme := Lexemes.write
    cell := IV_impe_act
    form := "uʔaktib"
    segments := ["u", "ʔ", "a", "k", "t", "i", "b"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def ktb_IV_impe_pas : Form Cell :=
  { id := "mccarthy1981_ktb_IV_impe_pas"
    lexeme := Lexemes.write
    cell := IV_impe_pas
    form := "uʔaktab"
    segments := ["u", "ʔ", "a", "k", "t", "a", "b"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def ktb_IV_part_act : Form Cell :=
  { id := "mccarthy1981_ktb_IV_part_act"
    lexeme := Lexemes.write
    cell := IV_part_act
    form := "muʔaktib"
    segments := ["m", "u", "ʔ", "a", "k", "t", "i", "b"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def ktb_IV_part_pas : Form Cell :=
  { id := "mccarthy1981_ktb_IV_part_pas"
    lexeme := Lexemes.write
    cell := IV_part_pas
    form := "muʔaktab"
    segments := ["m", "u", "ʔ", "a", "k", "t", "a", "b"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def ktb_V_perf_act : Form Cell :=
  { id := "mccarthy1981_ktb_V_perf_act"
    lexeme := Lexemes.write
    cell := V_perf_act
    form := "takattab"
    segments := ["t", "a", "k", "a", "t", "t", "a", "b"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def ktb_V_perf_pas : Form Cell :=
  { id := "mccarthy1981_ktb_V_perf_pas"
    lexeme := Lexemes.write
    cell := V_perf_pas
    form := "tukuttib"
    segments := ["t", "u", "k", "u", "t", "t", "i", "b"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def ktb_V_impe_act : Form Cell :=
  { id := "mccarthy1981_ktb_V_impe_act"
    lexeme := Lexemes.write
    cell := V_impe_act
    form := "atakattab"
    segments := ["a", "t", "a", "k", "a", "t", "t", "a", "b"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def ktb_V_impe_pas : Form Cell :=
  { id := "mccarthy1981_ktb_V_impe_pas"
    lexeme := Lexemes.write
    cell := V_impe_pas
    form := "utakattab"
    segments := ["u", "t", "a", "k", "a", "t", "t", "a", "b"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def ktb_V_part_act : Form Cell :=
  { id := "mccarthy1981_ktb_V_part_act"
    lexeme := Lexemes.write
    cell := V_part_act
    form := "mutakattib"
    segments := ["m", "u", "t", "a", "k", "a", "t", "t", "i", "b"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def ktb_V_part_pas : Form Cell :=
  { id := "mccarthy1981_ktb_V_part_pas"
    lexeme := Lexemes.write
    cell := V_part_pas
    form := "mutakattab"
    segments := ["m", "u", "t", "a", "k", "a", "t", "t", "a", "b"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def ktb_VI_perf_act : Form Cell :=
  { id := "mccarthy1981_ktb_VI_perf_act"
    lexeme := Lexemes.write
    cell := VI_perf_act
    form := "takaatab"
    segments := ["t", "a", "k", "a", "a", "t", "a", "b"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def ktb_VI_perf_pas : Form Cell :=
  { id := "mccarthy1981_ktb_VI_perf_pas"
    lexeme := Lexemes.write
    cell := VI_perf_pas
    form := "tukuutib"
    segments := ["t", "u", "k", "u", "u", "t", "i", "b"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def ktb_VI_impe_act : Form Cell :=
  { id := "mccarthy1981_ktb_VI_impe_act"
    lexeme := Lexemes.write
    cell := VI_impe_act
    form := "atakaatab"
    segments := ["a", "t", "a", "k", "a", "a", "t", "a", "b"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def ktb_VI_impe_pas : Form Cell :=
  { id := "mccarthy1981_ktb_VI_impe_pas"
    lexeme := Lexemes.write
    cell := VI_impe_pas
    form := "utakaatab"
    segments := ["u", "t", "a", "k", "a", "a", "t", "a", "b"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def ktb_VI_part_act : Form Cell :=
  { id := "mccarthy1981_ktb_VI_part_act"
    lexeme := Lexemes.write
    cell := VI_part_act
    form := "mutakaatib"
    segments := ["m", "u", "t", "a", "k", "a", "a", "t", "i", "b"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def ktb_VI_part_pas : Form Cell :=
  { id := "mccarthy1981_ktb_VI_part_pas"
    lexeme := Lexemes.write
    cell := VI_part_pas
    form := "mutakaatab"
    segments := ["m", "u", "t", "a", "k", "a", "a", "t", "a", "b"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def ktb_VII_perf_act : Form Cell :=
  { id := "mccarthy1981_ktb_VII_perf_act"
    lexeme := Lexemes.write
    cell := VII_perf_act
    form := "nkatab"
    segments := ["n", "k", "a", "t", "a", "b"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def ktb_VII_perf_pas : Form Cell :=
  { id := "mccarthy1981_ktb_VII_perf_pas"
    lexeme := Lexemes.write
    cell := VII_perf_pas
    form := "nkutib"
    segments := ["n", "k", "u", "t", "i", "b"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def ktb_VII_impe_act : Form Cell :=
  { id := "mccarthy1981_ktb_VII_impe_act"
    lexeme := Lexemes.write
    cell := VII_impe_act
    form := "ankatib"
    segments := ["a", "n", "k", "a", "t", "i", "b"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def ktb_VII_impe_pas : Form Cell :=
  { id := "mccarthy1981_ktb_VII_impe_pas"
    lexeme := Lexemes.write
    cell := VII_impe_pas
    form := "unkatab"
    segments := ["u", "n", "k", "a", "t", "a", "b"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def ktb_VII_part_act : Form Cell :=
  { id := "mccarthy1981_ktb_VII_part_act"
    lexeme := Lexemes.write
    cell := VII_part_act
    form := "munkatib"
    segments := ["m", "u", "n", "k", "a", "t", "i", "b"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def ktb_VII_part_pas : Form Cell :=
  { id := "mccarthy1981_ktb_VII_part_pas"
    lexeme := Lexemes.write
    cell := VII_part_pas
    form := "munkatab"
    segments := ["m", "u", "n", "k", "a", "t", "a", "b"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def ktb_VIII_perf_act : Form Cell :=
  { id := "mccarthy1981_ktb_VIII_perf_act"
    lexeme := Lexemes.write
    cell := VIII_perf_act
    form := "ktatab"
    segments := ["k", "t", "a", "t", "a", "b"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def ktb_VIII_perf_pas : Form Cell :=
  { id := "mccarthy1981_ktb_VIII_perf_pas"
    lexeme := Lexemes.write
    cell := VIII_perf_pas
    form := "ktutib"
    segments := ["k", "t", "u", "t", "i", "b"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def ktb_VIII_impe_act : Form Cell :=
  { id := "mccarthy1981_ktb_VIII_impe_act"
    lexeme := Lexemes.write
    cell := VIII_impe_act
    form := "aktatib"
    segments := ["a", "k", "t", "a", "t", "i", "b"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def ktb_VIII_impe_pas : Form Cell :=
  { id := "mccarthy1981_ktb_VIII_impe_pas"
    lexeme := Lexemes.write
    cell := VIII_impe_pas
    form := "uktatab"
    segments := ["u", "k", "t", "a", "t", "a", "b"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def ktb_VIII_part_act : Form Cell :=
  { id := "mccarthy1981_ktb_VIII_part_act"
    lexeme := Lexemes.write
    cell := VIII_part_act
    form := "muktatib"
    segments := ["m", "u", "k", "t", "a", "t", "i", "b"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def ktb_VIII_part_pas : Form Cell :=
  { id := "mccarthy1981_ktb_VIII_part_pas"
    lexeme := Lexemes.write
    cell := VIII_part_pas
    form := "muktatab"
    segments := ["m", "u", "k", "t", "a", "t", "a", "b"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def ktb_IX_perf_act : Form Cell :=
  { id := "mccarthy1981_ktb_IX_perf_act"
    lexeme := Lexemes.write
    cell := IX_perf_act
    form := "ktabab"
    segments := ["k", "t", "a", "b", "a", "b"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def ktb_IX_impe_act : Form Cell :=
  { id := "mccarthy1981_ktb_IX_impe_act"
    lexeme := Lexemes.write
    cell := IX_impe_act
    form := "aktabib"
    segments := ["a", "k", "t", "a", "b", "i", "b"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def ktb_IX_part_act : Form Cell :=
  { id := "mccarthy1981_ktb_IX_part_act"
    lexeme := Lexemes.write
    cell := IX_part_act
    form := "muktabib"
    segments := ["m", "u", "k", "t", "a", "b", "i", "b"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def ktb_X_perf_act : Form Cell :=
  { id := "mccarthy1981_ktb_X_perf_act"
    lexeme := Lexemes.write
    cell := X_perf_act
    form := "staktab"
    segments := ["s", "t", "a", "k", "t", "a", "b"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def ktb_X_perf_pas : Form Cell :=
  { id := "mccarthy1981_ktb_X_perf_pas"
    lexeme := Lexemes.write
    cell := X_perf_pas
    form := "stuktib"
    segments := ["s", "t", "u", "k", "t", "i", "b"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def ktb_X_impe_act : Form Cell :=
  { id := "mccarthy1981_ktb_X_impe_act"
    lexeme := Lexemes.write
    cell := X_impe_act
    form := "astaktib"
    segments := ["a", "s", "t", "a", "k", "t", "i", "b"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def ktb_X_impe_pas : Form Cell :=
  { id := "mccarthy1981_ktb_X_impe_pas"
    lexeme := Lexemes.write
    cell := X_impe_pas
    form := "ustaktab"
    segments := ["u", "s", "t", "a", "k", "t", "a", "b"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def ktb_X_part_act : Form Cell :=
  { id := "mccarthy1981_ktb_X_part_act"
    lexeme := Lexemes.write
    cell := X_part_act
    form := "mustaktib"
    segments := ["m", "u", "s", "t", "a", "k", "t", "i", "b"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def ktb_X_part_pas : Form Cell :=
  { id := "mccarthy1981_ktb_X_part_pas"
    lexeme := Lexemes.write
    cell := X_part_pas
    form := "mustaktab"
    segments := ["m", "u", "s", "t", "a", "k", "t", "a", "b"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def ktb_XI_perf_act : Form Cell :=
  { id := "mccarthy1981_ktb_XI_perf_act"
    lexeme := Lexemes.write
    cell := XI_perf_act
    form := "ktaabab"
    segments := ["k", "t", "a", "a", "b", "a", "b"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def ktb_XI_impe_act : Form Cell :=
  { id := "mccarthy1981_ktb_XI_impe_act"
    lexeme := Lexemes.write
    cell := XI_impe_act
    form := "aktaabib"
    segments := ["a", "k", "t", "a", "a", "b", "i", "b"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def ktb_XI_part_act : Form Cell :=
  { id := "mccarthy1981_ktb_XI_part_act"
    lexeme := Lexemes.write
    cell := XI_part_act
    form := "muktaabib"
    segments := ["m", "u", "k", "t", "a", "a", "b", "i", "b"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def ktb_XII_perf_act : Form Cell :=
  { id := "mccarthy1981_ktb_XII_perf_act"
    lexeme := Lexemes.write
    cell := XII_perf_act
    form := "ktawtab"
    segments := ["k", "t", "a", "w", "t", "a", "b"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def ktb_XII_impe_act : Form Cell :=
  { id := "mccarthy1981_ktb_XII_impe_act"
    lexeme := Lexemes.write
    cell := XII_impe_act
    form := "aktawtib"
    segments := ["a", "k", "t", "a", "w", "t", "i", "b"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def ktb_XII_part_act : Form Cell :=
  { id := "mccarthy1981_ktb_XII_part_act"
    lexeme := Lexemes.write
    cell := XII_part_act
    form := "muktawtib"
    segments := ["m", "u", "k", "t", "a", "w", "t", "i", "b"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def ktb_XIII_perf_act : Form Cell :=
  { id := "mccarthy1981_ktb_XIII_perf_act"
    lexeme := Lexemes.write
    cell := XIII_perf_act
    form := "ktawwab"
    segments := ["k", "t", "a", "w", "w", "a", "b"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def ktb_XIII_impe_act : Form Cell :=
  { id := "mccarthy1981_ktb_XIII_impe_act"
    lexeme := Lexemes.write
    cell := XIII_impe_act
    form := "aktawwib"
    segments := ["a", "k", "t", "a", "w", "w", "i", "b"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def ktb_XIII_part_act : Form Cell :=
  { id := "mccarthy1981_ktb_XIII_part_act"
    lexeme := Lexemes.write
    cell := XIII_part_act
    form := "muktawwib"
    segments := ["m", "u", "k", "t", "a", "w", "w", "i", "b"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def ktb_XIV_perf_act : Form Cell :=
  { id := "mccarthy1981_ktb_XIV_perf_act"
    lexeme := Lexemes.write
    cell := XIV_perf_act
    form := "ktanbab"
    segments := ["k", "t", "a", "n", "b", "a", "b"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def ktb_XIV_impe_act : Form Cell :=
  { id := "mccarthy1981_ktb_XIV_impe_act"
    lexeme := Lexemes.write
    cell := XIV_impe_act
    form := "aktanbib"
    segments := ["a", "k", "t", "a", "n", "b", "i", "b"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def ktb_XIV_part_act : Form Cell :=
  { id := "mccarthy1981_ktb_XIV_part_act"
    lexeme := Lexemes.write
    cell := XIV_part_act
    form := "muktanbib"
    segments := ["m", "u", "k", "t", "a", "n", "b", "i", "b"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def ktb_XV_perf_act : Form Cell :=
  { id := "mccarthy1981_ktb_XV_perf_act"
    lexeme := Lexemes.write
    cell := XV_perf_act
    form := "ktanbay"
    segments := ["k", "t", "a", "n", "b", "a", "y"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def ktb_XV_impe_act : Form Cell :=
  { id := "mccarthy1981_ktb_XV_impe_act"
    lexeme := Lexemes.write
    cell := XV_impe_act
    form := "aktanbiy"
    segments := ["a", "k", "t", "a", "n", "b", "i", "y"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def ktb_XV_part_act : Form Cell :=
  { id := "mccarthy1981_ktb_XV_part_act"
    lexeme := Lexemes.write
    cell := XV_part_act
    form := "muktanbiy"
    segments := ["m", "u", "k", "t", "a", "n", "b", "i", "y"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def dhrj_QI_perf_act : Form Cell :=
  { id := "mccarthy1981_dhrj_QI_perf_act"
    lexeme := Lexemes.roll
    cell := QI_perf_act
    form := "daḥraj"
    segments := ["d", "a", "ḥ", "r", "a", "j"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def dhrj_QI_perf_pas : Form Cell :=
  { id := "mccarthy1981_dhrj_QI_perf_pas"
    lexeme := Lexemes.roll
    cell := QI_perf_pas
    form := "duḥrij"
    segments := ["d", "u", "ḥ", "r", "i", "j"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def dhrj_QI_impe_act : Form Cell :=
  { id := "mccarthy1981_dhrj_QI_impe_act"
    lexeme := Lexemes.roll
    cell := QI_impe_act
    form := "udaḥrij"
    segments := ["u", "d", "a", "ḥ", "r", "i", "j"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def dhrj_QI_impe_pas : Form Cell :=
  { id := "mccarthy1981_dhrj_QI_impe_pas"
    lexeme := Lexemes.roll
    cell := QI_impe_pas
    form := "udaḥraj"
    segments := ["u", "d", "a", "ḥ", "r", "a", "j"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def dhrj_QI_part_act : Form Cell :=
  { id := "mccarthy1981_dhrj_QI_part_act"
    lexeme := Lexemes.roll
    cell := QI_part_act
    form := "mudaḥrij"
    segments := ["m", "u", "d", "a", "ḥ", "r", "i", "j"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def dhrj_QI_part_pas : Form Cell :=
  { id := "mccarthy1981_dhrj_QI_part_pas"
    lexeme := Lexemes.roll
    cell := QI_part_pas
    form := "mudaḥraj"
    segments := ["m", "u", "d", "a", "ḥ", "r", "a", "j"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def dhrj_QII_perf_act : Form Cell :=
  { id := "mccarthy1981_dhrj_QII_perf_act"
    lexeme := Lexemes.roll
    cell := QII_perf_act
    form := "tadaḥraj"
    segments := ["t", "a", "d", "a", "ḥ", "r", "a", "j"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def dhrj_QII_perf_pas : Form Cell :=
  { id := "mccarthy1981_dhrj_QII_perf_pas"
    lexeme := Lexemes.roll
    cell := QII_perf_pas
    form := "tuduḥrij"
    segments := ["t", "u", "d", "u", "ḥ", "r", "i", "j"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def dhrj_QII_impe_act : Form Cell :=
  { id := "mccarthy1981_dhrj_QII_impe_act"
    lexeme := Lexemes.roll
    cell := QII_impe_act
    form := "atadaḥraj"
    segments := ["a", "t", "a", "d", "a", "ḥ", "r", "a", "j"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def dhrj_QII_impe_pas : Form Cell :=
  { id := "mccarthy1981_dhrj_QII_impe_pas"
    lexeme := Lexemes.roll
    cell := QII_impe_pas
    form := "utadaḥraj"
    segments := ["u", "t", "a", "d", "a", "ḥ", "r", "a", "j"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def dhrj_QII_part_act : Form Cell :=
  { id := "mccarthy1981_dhrj_QII_part_act"
    lexeme := Lexemes.roll
    cell := QII_part_act
    form := "mutadaḥrij"
    segments := ["m", "u", "t", "a", "d", "a", "ḥ", "r", "i", "j"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def dhrj_QII_part_pas : Form Cell :=
  { id := "mccarthy1981_dhrj_QII_part_pas"
    lexeme := Lexemes.roll
    cell := QII_part_pas
    form := "mutadaḥraj"
    segments := ["m", "u", "t", "a", "d", "a", "ḥ", "r", "a", "j"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def dhrj_QIII_perf_act : Form Cell :=
  { id := "mccarthy1981_dhrj_QIII_perf_act"
    lexeme := Lexemes.roll
    cell := QIII_perf_act
    form := "dḥanraj"
    segments := ["d", "ḥ", "a", "n", "r", "a", "j"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def dhrj_QIII_perf_pas : Form Cell :=
  { id := "mccarthy1981_dhrj_QIII_perf_pas"
    lexeme := Lexemes.roll
    cell := QIII_perf_pas
    form := "dḥunrij"
    segments := ["d", "ḥ", "u", "n", "r", "i", "j"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def dhrj_QIII_impe_act : Form Cell :=
  { id := "mccarthy1981_dhrj_QIII_impe_act"
    lexeme := Lexemes.roll
    cell := QIII_impe_act
    form := "adḥanrij"
    segments := ["a", "d", "ḥ", "a", "n", "r", "i", "j"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def dhrj_QIII_impe_pas : Form Cell :=
  { id := "mccarthy1981_dhrj_QIII_impe_pas"
    lexeme := Lexemes.roll
    cell := QIII_impe_pas
    form := "udḥanraj"
    segments := ["u", "d", "ḥ", "a", "n", "r", "a", "j"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def dhrj_QIII_part_act : Form Cell :=
  { id := "mccarthy1981_dhrj_QIII_part_act"
    lexeme := Lexemes.roll
    cell := QIII_part_act
    form := "mudḥanrij"
    segments := ["m", "u", "d", "ḥ", "a", "n", "r", "i", "j"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def dhrj_QIII_part_pas : Form Cell :=
  { id := "mccarthy1981_dhrj_QIII_part_pas"
    lexeme := Lexemes.roll
    cell := QIII_part_pas
    form := "mudḥanraj"
    segments := ["m", "u", "d", "ḥ", "a", "n", "r", "a", "j"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def dhrj_QIV_perf_act : Form Cell :=
  { id := "mccarthy1981_dhrj_QIV_perf_act"
    lexeme := Lexemes.roll
    cell := QIV_perf_act
    form := "dḥarjaj"
    segments := ["d", "ḥ", "a", "r", "j", "a", "j"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def dhrj_QIV_perf_pas : Form Cell :=
  { id := "mccarthy1981_dhrj_QIV_perf_pas"
    lexeme := Lexemes.roll
    cell := QIV_perf_pas
    form := "dḥurjij"
    segments := ["d", "ḥ", "u", "r", "j", "i", "j"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def dhrj_QIV_impe_act : Form Cell :=
  { id := "mccarthy1981_dhrj_QIV_impe_act"
    lexeme := Lexemes.roll
    cell := QIV_impe_act
    form := "adḥarjij"
    segments := ["a", "d", "ḥ", "a", "r", "j", "i", "j"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def dhrj_QIV_impe_pas : Form Cell :=
  { id := "mccarthy1981_dhrj_QIV_impe_pas"
    lexeme := Lexemes.roll
    cell := QIV_impe_pas
    form := "udḥarjaj"
    segments := ["u", "d", "ḥ", "a", "r", "j", "a", "j"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def dhrj_QIV_part_act : Form Cell :=
  { id := "mccarthy1981_dhrj_QIV_part_act"
    lexeme := Lexemes.roll
    cell := QIV_part_act
    form := "mudḥarjij"
    segments := ["m", "u", "d", "ḥ", "a", "r", "j", "i", "j"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def dhrj_QIV_part_pas : Form Cell :=
  { id := "mccarthy1981_dhrj_QIV_part_pas"
    lexeme := Lexemes.roll
    cell := QIV_part_pas
    form := "mudḥarjaj"
    segments := ["m", "u", "d", "ḥ", "a", "r", "j", "a", "j"]
    source := [
      ⟨"mccarthy-1981", "Table 1"⟩
    ] }

def poison_I_perf_act : Form Cell :=
  { id := "mccarthy1981_poison_I_perf_act"
    lexeme := Lexemes.poison
    cell := I_perf_act
    form := "samam"
    segments := ["s", "a", "m", "a", "m"]
    source := [
      ⟨"mccarthy-1981", "(33)"⟩
    ] }

def poison_II_perf_act : Form Cell :=
  { id := "mccarthy1981_poison_II_perf_act"
    lexeme := Lexemes.poison
    cell := II_perf_act
    form := "sammam"
    segments := ["s", "a", "m", "m", "a", "m"]
    source := [
      ⟨"mccarthy-1981", "(34a)"⟩
    ] }

def poison_V_perf_act : Form Cell :=
  { id := "mccarthy1981_poison_V_perf_act"
    lexeme := Lexemes.poison
    cell := V_perf_act
    form := "tasammam"
    segments := ["t", "a", "s", "a", "m", "m", "a", "m"]
    source := [
      ⟨"mccarthy-1981", "(34b)"⟩
    ] }

def magnetize_QI_perf_act : Form Cell :=
  { id := "mccarthy1981_magnetize_QI_perf_act"
    lexeme := Lexemes.magnetize
    cell := QI_perf_act
    form := "mağnaṭ"
    segments := ["m", "a", "ğ", "n", "a", "ṭ"]
    source := [
      ⟨"mccarthy-1981", "(38)"⟩
    ] }

/-- Every lexeme of the data. -/
def lexemes : List Lexeme := [Lexemes.write, Lexemes.roll, Lexemes.poison, Lexemes.magnetize]

/-- Every form the sources accept. -/
def all : List (Form Cell) := [ktb_I_perf_act, ktb_I_perf_pas, ktb_I_impe_act, ktb_I_impe_pas,
  ktb_I_part_act, ktb_I_part_pas, ktb_II_perf_act, ktb_II_perf_pas, ktb_II_impe_act,
  ktb_II_impe_pas, ktb_II_part_act, ktb_II_part_pas, ktb_III_perf_act, ktb_III_perf_pas,
  ktb_III_impe_act, ktb_III_impe_pas, ktb_III_part_act, ktb_III_part_pas, ktb_IV_perf_act,
  ktb_IV_perf_pas, ktb_IV_impe_act, ktb_IV_impe_pas, ktb_IV_part_act, ktb_IV_part_pas,
  ktb_V_perf_act, ktb_V_perf_pas, ktb_V_impe_act, ktb_V_impe_pas, ktb_V_part_act, ktb_V_part_pas,
  ktb_VI_perf_act, ktb_VI_perf_pas, ktb_VI_impe_act, ktb_VI_impe_pas, ktb_VI_part_act,
  ktb_VI_part_pas, ktb_VII_perf_act, ktb_VII_perf_pas, ktb_VII_impe_act, ktb_VII_impe_pas,
  ktb_VII_part_act, ktb_VII_part_pas, ktb_VIII_perf_act, ktb_VIII_perf_pas, ktb_VIII_impe_act,
  ktb_VIII_impe_pas, ktb_VIII_part_act, ktb_VIII_part_pas, ktb_IX_perf_act, ktb_IX_impe_act,
  ktb_IX_part_act, ktb_X_perf_act, ktb_X_perf_pas, ktb_X_impe_act, ktb_X_impe_pas, ktb_X_part_act,
  ktb_X_part_pas, ktb_XI_perf_act, ktb_XI_impe_act, ktb_XI_part_act, ktb_XII_perf_act,
  ktb_XII_impe_act, ktb_XII_part_act, ktb_XIII_perf_act, ktb_XIII_impe_act, ktb_XIII_part_act,
  ktb_XIV_perf_act, ktb_XIV_impe_act, ktb_XIV_part_act, ktb_XV_perf_act, ktb_XV_impe_act,
  ktb_XV_part_act, dhrj_QI_perf_act, dhrj_QI_perf_pas, dhrj_QI_impe_act, dhrj_QI_impe_pas,
  dhrj_QI_part_act, dhrj_QI_part_pas, dhrj_QII_perf_act, dhrj_QII_perf_pas, dhrj_QII_impe_act,
  dhrj_QII_impe_pas, dhrj_QII_part_act, dhrj_QII_part_pas, dhrj_QIII_perf_act, dhrj_QIII_perf_pas,
  dhrj_QIII_impe_act, dhrj_QIII_impe_pas, dhrj_QIII_part_act, dhrj_QIII_part_pas, dhrj_QIV_perf_act,
  dhrj_QIV_perf_pas, dhrj_QIV_impe_act, dhrj_QIV_impe_pas, dhrj_QIV_part_act, dhrj_QIV_part_pas,
  poison_I_perf_act, poison_II_perf_act, poison_V_perf_act, magnetize_QI_perf_act]

/-- Every form a source marks, as marginal, questionable, unacceptable or ungrammatical. -/
def marked : List (Form Cell) := []

/-- Every relation the sources assert between forms. -/
def relations : List (FormRelation (Form Cell)) := []

end McCarthy1981.Wordlist
