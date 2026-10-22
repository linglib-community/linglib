module

public import Linglib.Data.Wordlist.Schema

/-!
# `Qin2025`: word forms

Auto-generated from `Linglib/Data/Wordlist/Qin2025.json` by `scripts/gen_wordlist.py`. Do not edit
by hand; edit the JSON and re-run the generator. Declarations live in `namespace Qin2025.Wordlist`.
-/

@[expose] public section

namespace Qin2025.Wordlist

open Data.Wordlist

/-- The values of `Boundness` the source distinguishes. -/
inductive Boundness where
  /-- Free, `F` in the source. -/
  | free
  /-- Bound, `B` in the source. -/
  | bound
  deriving DecidableEq, Repr

/-- The values of `PositionalFlexibility` the source distinguishes. -/
inductive PositionalFlexibility where
  /-- Flexible position, `FLEX` in the source. -/
  | flexible
  /-- Fixed on the right, `SR` in the source. -/
  | right
  /-- Fixed on the left, `SL` in the source. -/
  | left
  deriving DecidableEq, Repr

/-- The values of `PhonologicalRichness` the source distinguishes. -/
inductive PhonologicalRichness where
  /-- One syllable, `1` in the source. -/
  | one
  /-- Toneless, `TL` in the source. -/
  | toneless
  deriving DecidableEq, Repr

/-- The values of `MeaningLexicality` the source distinguishes. -/
inductive MeaningLexicality where
  /-- Lexical meaning, `L` in the source. -/
  | lexical
  /-- Non-lexical meaning, `NL` in the source. -/
  | nonLexical
  deriving DecidableEq, Repr

/-- A cell of the source's tables, by its Universal Dependencies features and the features UD
lacks. -/
structure Cell extends UD.MorphFeatures where
  /-- The `Boundness` feature. -/
  boundness : Flat Boundness := ⊥
  /-- The `PositionalFlexibility` feature. -/
  positionalFlexibility : Flat PositionalFlexibility := ⊥
  /-- The `PhonologicalRichness` feature. -/
  phonologicalRichness : Flat PhonologicalRichness := ⊥
  /-- The `MeaningLexicality` feature. -/
  meaningLexicality : Flat MeaningLexicality := ⊥
  deriving DecidableEq, Repr

/-- The F FLEX 1 L cell,
`Boundness=F|PositionalFlexibility=FLEX|PhonologicalRichness=1|MeaningLexicality=L`. -/
def d_f_flex_1_l : Cell :=
  { boundness := ↑Boundness.free, positionalFlexibility := ↑PositionalFlexibility.flexible,
    phonologicalRichness := ↑PhonologicalRichness.one,
    meaningLexicality := ↑MeaningLexicality.lexical }

/-- The B FLEX 1 L cell,
`Boundness=B|PositionalFlexibility=FLEX|PhonologicalRichness=1|MeaningLexicality=L`. -/
def d_b_flex_1_l : Cell :=
  { boundness := ↑Boundness.bound, positionalFlexibility := ↑PositionalFlexibility.flexible,
    phonologicalRichness := ↑PhonologicalRichness.one,
    meaningLexicality := ↑MeaningLexicality.lexical }

/-- The F FLEX 1 NL cell,
`Boundness=F|PositionalFlexibility=FLEX|PhonologicalRichness=1|MeaningLexicality=NL`. -/
def d_f_flex_1_nl : Cell :=
  { boundness := ↑Boundness.free, positionalFlexibility := ↑PositionalFlexibility.flexible,
    phonologicalRichness := ↑PhonologicalRichness.one,
    meaningLexicality := ↑MeaningLexicality.nonLexical }

/-- The B SR 1 L cell,
`Boundness=B|PositionalFlexibility=SR|PhonologicalRichness=1|MeaningLexicality=L`. -/
def d_b_sr_1_l : Cell :=
  { boundness := ↑Boundness.bound, positionalFlexibility := ↑PositionalFlexibility.right,
    phonologicalRichness := ↑PhonologicalRichness.one,
    meaningLexicality := ↑MeaningLexicality.lexical }

/-- The B FLEX 1 NL cell,
`Boundness=B|PositionalFlexibility=FLEX|PhonologicalRichness=1|MeaningLexicality=NL`. -/
def d_b_flex_1_nl : Cell :=
  { boundness := ↑Boundness.bound, positionalFlexibility := ↑PositionalFlexibility.flexible,
    phonologicalRichness := ↑PhonologicalRichness.one,
    meaningLexicality := ↑MeaningLexicality.nonLexical }

/-- The B SL 1 L cell,
`Boundness=B|PositionalFlexibility=SL|PhonologicalRichness=1|MeaningLexicality=L`. -/
def d_b_sl_1_l : Cell :=
  { boundness := ↑Boundness.bound, positionalFlexibility := ↑PositionalFlexibility.left,
    phonologicalRichness := ↑PhonologicalRichness.one,
    meaningLexicality := ↑MeaningLexicality.lexical }

/-- The F SL 1 NL cell,
`Boundness=F|PositionalFlexibility=SL|PhonologicalRichness=1|MeaningLexicality=NL`. -/
def d_f_sl_1_nl : Cell :=
  { boundness := ↑Boundness.free, positionalFlexibility := ↑PositionalFlexibility.left,
    phonologicalRichness := ↑PhonologicalRichness.one,
    meaningLexicality := ↑MeaningLexicality.nonLexical }

/-- The B SL 1 NL cell,
`Boundness=B|PositionalFlexibility=SL|PhonologicalRichness=1|MeaningLexicality=NL`. -/
def d_b_sl_1_nl : Cell :=
  { boundness := ↑Boundness.bound, positionalFlexibility := ↑PositionalFlexibility.left,
    phonologicalRichness := ↑PhonologicalRichness.one,
    meaningLexicality := ↑MeaningLexicality.nonLexical }

/-- The B SR 1 NL cell,
`Boundness=B|PositionalFlexibility=SR|PhonologicalRichness=1|MeaningLexicality=NL`. -/
def d_b_sr_1_nl : Cell :=
  { boundness := ↑Boundness.bound, positionalFlexibility := ↑PositionalFlexibility.right,
    phonologicalRichness := ↑PhonologicalRichness.one,
    meaningLexicality := ↑MeaningLexicality.nonLexical }

/-- The B SR TL NL cell,
`Boundness=B|PositionalFlexibility=SR|PhonologicalRichness=TL|MeaningLexicality=NL`. -/
def d_b_sr_tl_nl : Cell :=
  { boundness := ↑Boundness.bound, positionalFlexibility := ↑PositionalFlexibility.right,
    phonologicalRichness := ↑PhonologicalRichness.toneless,
    meaningLexicality := ↑MeaningLexicality.nonLexical }

def Lexemes.bu : Lexeme :=
  { id := "bu", languageId := "mand1415", parameterId := "bu" }

def Lexemes.chang : Lexeme :=
  { id := "chang", languageId := "mand1415", parameterId := "chang" }

def Lexemes.dai : Lexeme :=
  { id := "dai", languageId := "mand1415", parameterId := "dai" }

def Lexemes.duo : Lexeme :=
  { id := "duo", languageId := "mand1415", parameterId := "duo" }

def Lexemes.fan : Lexeme :=
  { id := "fan", languageId := "mand1415", parameterId := "fan" }

def Lexemes.fang : Lexeme :=
  { id := "fang", languageId := "mand1415", parameterId := "fang" }

def Lexemes.fen : Lexeme :=
  { id := "fen", languageId := "mand1415", parameterId := "fen" }

def Lexemes.ge : Lexeme :=
  { id := "ge", languageId := "mand1415", parameterId := "ge" }

def Lexemes.guo : Lexeme :=
  { id := "guo", languageId := "mand1415", parameterId := "guo" }

def Lexemes.hu : Lexeme :=
  { id := "hu", languageId := "mand1415", parameterId := "hu" }

def Lexemes.jie : Lexeme :=
  { id := "jie", languageId := "mand1415", parameterId := "jie" }

def Lexemes.pai : Lexeme :=
  { id := "pai", languageId := "mand1415", parameterId := "pai" }

def Lexemes.qian : Lexeme :=
  { id := "qian", languageId := "mand1415", parameterId := "qian" }

def Lexemes.qun : Lexeme :=
  { id := "qun", languageId := "mand1415", parameterId := "qun" }

def Lexemes.ren : Lexeme :=
  { id := "ren", languageId := "mand1415", parameterId := "ren" }

def Lexemes.shi : Lexeme :=
  { id := "shi", languageId := "mand1415", parameterId := "shi" }

def Lexemes.shui : Lexeme :=
  { id := "shui", languageId := "mand1415", parameterId := "shui" }

def Lexemes.suo : Lexeme :=
  { id := "suo", languageId := "mand1415", parameterId := "suo" }

def Lexemes.wu : Lexeme :=
  { id := "wu", languageId := "mand1415", parameterId := "wu" }

def Lexemes.xing : Lexeme :=
  { id := "xing", languageId := "mand1415", parameterId := "xing" }

def Lexemes.xiu : Lexeme :=
  { id := "xiu", languageId := "mand1415", parameterId := "xiu" }

def Lexemes.you : Lexeme :=
  { id := "you", languageId := "mand1415", parameterId := "you" }

def Lexemes.ba : Lexeme :=
  { id := "ba", languageId := "mand1415", parameterId := "ba" }

def Lexemes.ban : Lexeme :=
  { id := "ban", languageId := "mand1415", parameterId := "ban" }

def Lexemes.bu_2 : Lexeme :=
  { id := "bu_2", languageId := "mand1415", parameterId := "bu_2" }

def Lexemes.ce : Lexeme :=
  { id := "ce", languageId := "mand1415", parameterId := "ce" }

def Lexemes.chang_2 : Lexeme :=
  { id := "chang_2", languageId := "mand1415", parameterId := "chang_2" }

def Lexemes.dan : Lexeme :=
  { id := "dan", languageId := "mand1415", parameterId := "dan" }

def Lexemes.fan_2 : Lexeme :=
  { id := "fan_2", languageId := "mand1415", parameterId := "fan_2" }

def Lexemes.fang_2 : Lexeme :=
  { id := "fang_2", languageId := "mand1415", parameterId := "fang_2" }

def Lexemes.gan : Lexeme :=
  { id := "gan", languageId := "mand1415", parameterId := "gan" }

def Lexemes.gong : Lexeme :=
  { id := "gong", languageId := "mand1415", parameterId := "gong" }

def Lexemes.hao : Lexeme :=
  { id := "hao", languageId := "mand1415", parameterId := "hao" }

def Lexemes.ji : Lexeme :=
  { id := "ji", languageId := "mand1415", parameterId := "ji" }

def Lexemes.ke : Lexeme :=
  { id := "ke", languageId := "mand1415", parameterId := "ke" }

def Lexemes.ke_2 : Lexeme :=
  { id := "ke_2", languageId := "mand1415", parameterId := "ke_2" }

def Lexemes.li : Lexeme :=
  { id := "li", languageId := "mand1415", parameterId := "li" }

def Lexemes.pin : Lexeme :=
  { id := "pin", languageId := "mand1415", parameterId := "pin" }

def Lexemes.qi : Lexeme :=
  { id := "qi", languageId := "mand1415", parameterId := "qi" }

def Lexemes.qi_2 : Lexeme :=
  { id := "qi_2", languageId := "mand1415", parameterId := "qi_2" }

def Lexemes.qin : Lexeme :=
  { id := "qin", languageId := "mand1415", parameterId := "qin" }

def Lexemes.sheng : Lexeme :=
  { id := "sheng", languageId := "mand1415", parameterId := "sheng" }

def Lexemes.ti : Lexeme :=
  { id := "ti", languageId := "mand1415", parameterId := "ti" }

def Lexemes.wei : Lexeme :=
  { id := "wei", languageId := "mand1415", parameterId := "wei" }

def Lexemes.wu_2 : Lexeme :=
  { id := "wu_2", languageId := "mand1415", parameterId := "wu_2" }

def Lexemes.xiang : Lexeme :=
  { id := "xiang", languageId := "mand1415", parameterId := "xiang" }

def Lexemes.xiao : Lexeme :=
  { id := "xiao", languageId := "mand1415", parameterId := "xiao" }

def Lexemes.xin : Lexeme :=
  { id := "xin", languageId := "mand1415", parameterId := "xin" }

def Lexemes.xing_2 : Lexeme :=
  { id := "xing_2", languageId := "mand1415", parameterId := "xing_2" }

def Lexemes.ye : Lexeme :=
  { id := "ye", languageId := "mand1415", parameterId := "ye" }

def Lexemes.ying : Lexeme :=
  { id := "ying", languageId := "mand1415", parameterId := "ying" }

def Lexemes.yuan : Lexeme :=
  { id := "yuan", languageId := "mand1415", parameterId := "yuan" }

def Lexemes.zheng : Lexeme :=
  { id := "zheng", languageId := "mand1415", parameterId := "zheng" }

def Lexemes.zhong : Lexeme :=
  { id := "zhong", languageId := "mand1415", parameterId := "zhong" }

def Lexemes.zi : Lexeme :=
  { id := "zi", languageId := "mand1415", parameterId := "zi" }

def Lexemes.zi_2 : Lexeme :=
  { id := "zi_2", languageId := "mand1415", parameterId := "zi_2" }

def Lexemes.zong : Lexeme :=
  { id := "zong", languageId := "mand1415", parameterId := "zong" }

def Lexemes.ba_2 : Lexeme :=
  { id := "ba_2", languageId := "mand1415", parameterId := "ba_2" }

def Lexemes.ban_2 : Lexeme :=
  { id := "ban_2", languageId := "mand1415", parameterId := "ban_2" }

def Lexemes.bie : Lexeme :=
  { id := "bie", languageId := "mand1415", parameterId := "bie" }

def Lexemes.chu : Lexeme :=
  { id := "chu", languageId := "mand1415", parameterId := "chu" }

def Lexemes.dao : Lexeme :=
  { id := "dao", languageId := "mand1415", parameterId := "dao" }

def Lexemes.ding : Lexeme :=
  { id := "ding", languageId := "mand1415", parameterId := "ding" }

def Lexemes.du : Lexeme :=
  { id := "du", languageId := "mand1415", parameterId := "du" }

def Lexemes.fa : Lexeme :=
  { id := "fa", languageId := "mand1415", parameterId := "fa" }

def Lexemes.fan_3 : Lexeme :=
  { id := "fan_3", languageId := "mand1415", parameterId := "fan_3" }

def Lexemes.fei : Lexeme :=
  { id := "fei", languageId := "mand1415", parameterId := "fei" }

def Lexemes.fei_2 : Lexeme :=
  { id := "fei_2", languageId := "mand1415", parameterId := "fei_2" }

def Lexemes.feng : Lexeme :=
  { id := "feng", languageId := "mand1415", parameterId := "feng" }

def Lexemes.fu : Lexeme :=
  { id := "fu", languageId := "mand1415", parameterId := "fu" }

def Lexemes.fu_2 : Lexeme :=
  { id := "fu_2", languageId := "mand1415", parameterId := "fu_2" }

def Lexemes.guan : Lexeme :=
  { id := "guan", languageId := "mand1415", parameterId := "guan" }

def Lexemes.gui : Lexeme :=
  { id := "gui", languageId := "mand1415", parameterId := "gui" }

def Lexemes.gun : Lexeme :=
  { id := "gun", languageId := "mand1415", parameterId := "gun" }

def Lexemes.han : Lexeme :=
  { id := "han", languageId := "mand1415", parameterId := "han" }

def Lexemes.hao_2 : Lexeme :=
  { id := "hao_2", languageId := "mand1415", parameterId := "hao_2" }

def Lexemes.jia : Lexeme :=
  { id := "jia", languageId := "mand1415", parameterId := "jia" }

def Lexemes.jian : Lexeme :=
  { id := "jian", languageId := "mand1415", parameterId := "jian" }

def Lexemes.jiang : Lexeme :=
  { id := "jiang", languageId := "mand1415", parameterId := "jiang" }

def Lexemes.jie_2 : Lexeme :=
  { id := "jie_2", languageId := "mand1415", parameterId := "jie_2" }

def Lexemes.ju : Lexeme :=
  { id := "ju", languageId := "mand1415", parameterId := "ju" }

def Lexemes.lei : Lexeme :=
  { id := "lei", languageId := "mand1415", parameterId := "lei" }

def Lexemes.ling : Lexeme :=
  { id := "ling", languageId := "mand1415", parameterId := "ling" }

def Lexemes.lun : Lexeme :=
  { id := "lun", languageId := "mand1415", parameterId := "lun" }

def Lexemes.lu : Lexeme :=
  { id := "lu", languageId := "mand1415", parameterId := "lu" }

def Lexemes.mang : Lexeme :=
  { id := "mang", languageId := "mand1415", parameterId := "mang" }

def Lexemes.mi : Lexeme :=
  { id := "mi", languageId := "mand1415", parameterId := "mi" }

def Lexemes.min : Lexeme :=
  { id := "min", languageId := "mand1415", parameterId := "min" }

def Lexemes.re : Lexeme :=
  { id := "re", languageId := "mand1415", parameterId := "re" }

def Lexemes.ruan : Lexeme :=
  { id := "ruan", languageId := "mand1415", parameterId := "ruan" }

def Lexemes.shi_2 : Lexeme :=
  { id := "shi_2", languageId := "mand1415", parameterId := "shi_2" }

def Lexemes.shi_3 : Lexeme :=
  { id := "shi_3", languageId := "mand1415", parameterId := "shi_3" }

def Lexemes.shi_4 : Lexeme :=
  { id := "shi_4", languageId := "mand1415", parameterId := "shi_4" }

def Lexemes.shou : Lexeme :=
  { id := "shou", languageId := "mand1415", parameterId := "shou" }

def Lexemes.tan : Lexeme :=
  { id := "tan", languageId := "mand1415", parameterId := "tan" }

def Lexemes.tu : Lexeme :=
  { id := "tu", languageId := "mand1415", parameterId := "tu" }

def Lexemes.xing_3 : Lexeme :=
  { id := "xing_3", languageId := "mand1415", parameterId := "xing_3" }

def Lexemes.xue : Lexeme :=
  { id := "xue", languageId := "mand1415", parameterId := "xue" }

def Lexemes.ya : Lexeme :=
  { id := "ya", languageId := "mand1415", parameterId := "ya" }

def Lexemes.yan : Lexeme :=
  { id := "yan", languageId := "mand1415", parameterId := "yan" }

def Lexemes.yi : Lexeme :=
  { id := "yi", languageId := "mand1415", parameterId := "yi" }

def Lexemes.you_2 : Lexeme :=
  { id := "you_2", languageId := "mand1415", parameterId := "you_2" }

def Lexemes.yuan_2 : Lexeme :=
  { id := "yuan_2", languageId := "mand1415", parameterId := "yuan_2" }

def Lexemes.zhang : Lexeme :=
  { id := "zhang", languageId := "mand1415", parameterId := "zhang" }

def Lexemes.zhang_2 : Lexeme :=
  { id := "zhang_2", languageId := "mand1415", parameterId := "zhang_2" }

def Lexemes.zhe : Lexeme :=
  { id := "zhe", languageId := "mand1415", parameterId := "zhe" }

def Lexemes.zhi : Lexeme :=
  { id := "zhi", languageId := "mand1415", parameterId := "zhi" }

def Lexemes.zhi_2 : Lexeme :=
  { id := "zhi_2", languageId := "mand1415", parameterId := "zhi_2" }

def Lexemes.zu : Lexeme :=
  { id := "zu", languageId := "mand1415", parameterId := "zu" }

def Lexemes.chao : Lexeme :=
  { id := "chao", languageId := "mand1415", parameterId := "chao" }

def Lexemes.ci : Lexeme :=
  { id := "ci", languageId := "mand1415", parameterId := "ci" }

def Lexemes.hua : Lexeme :=
  { id := "hua", languageId := "mand1415", parameterId := "hua" }

def Lexemes.lai : Lexeme :=
  { id := "lai", languageId := "mand1415", parameterId := "lai" }

def Lexemes.mian : Lexeme :=
  { id := "mian", languageId := "mand1415", parameterId := "mian" }

def Lexemes.nan : Lexeme :=
  { id := "nan", languageId := "mand1415", parameterId := "nan" }

def Lexemes.ran : Lexeme :=
  { id := "ran", languageId := "mand1415", parameterId := "ran" }

def Lexemes.shi_5 : Lexeme :=
  { id := "shi_5", languageId := "mand1415", parameterId := "shi_5" }

def Lexemes.xing_4 : Lexeme :=
  { id := "xing_4", languageId := "mand1415", parameterId := "xing_4" }

def Lexemes.yi_2 : Lexeme :=
  { id := "yi_2", languageId := "mand1415", parameterId := "yi_2" }

def Lexemes.zhun : Lexeme :=
  { id := "zhun", languageId := "mand1415", parameterId := "zhun" }

def Lexemes.bian : Lexeme :=
  { id := "bian", languageId := "mand1415", parameterId := "bian" }

def Lexemes.ge_2 : Lexeme :=
  { id := "ge_2", languageId := "mand1415", parameterId := "ge_2" }

def bu : Form Cell :=
  { id := "qin2025_bu"
    lexeme := Lexemes.bu
    cell := d_f_flex_1_l
    form := "部"
    segments := ["bù"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def chang : Form Cell :=
  { id := "qin2025_chang"
    lexeme := Lexemes.chang
    cell := d_f_flex_1_l
    form := "厂"
    segments := ["chǎng"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def dai : Form Cell :=
  { id := "qin2025_dai"
    lexeme := Lexemes.dai
    cell := d_f_flex_1_l
    form := "代"
    segments := ["dài"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def duo : Form Cell :=
  { id := "qin2025_duo"
    lexeme := Lexemes.duo
    cell := d_f_flex_1_l
    form := "多"
    segments := ["duō"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def fan : Form Cell :=
  { id := "qin2025_fan"
    lexeme := Lexemes.fan
    cell := d_f_flex_1_l
    form := "反"
    segments := ["fǎn"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def fang : Form Cell :=
  { id := "qin2025_fang"
    lexeme := Lexemes.fang
    cell := d_f_flex_1_l
    form := "房"
    segments := ["fáng"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def fen : Form Cell :=
  { id := "qin2025_fen"
    lexeme := Lexemes.fen
    cell := d_f_flex_1_l
    form := "分"
    segments := ["fēn"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def ge : Form Cell :=
  { id := "qin2025_ge"
    lexeme := Lexemes.ge
    cell := d_f_flex_1_l
    form := "哥"
    segments := ["gē"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def guo : Form Cell :=
  { id := "qin2025_guo"
    lexeme := Lexemes.guo
    cell := d_f_flex_1_l
    form := "国"
    segments := ["guó"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def hu : Form Cell :=
  { id := "qin2025_hu"
    lexeme := Lexemes.hu
    cell := d_f_flex_1_l
    form := "户"
    segments := ["hù"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def jie : Form Cell :=
  { id := "qin2025_jie"
    lexeme := Lexemes.jie
    cell := d_f_flex_1_l
    form := "姐"
    segments := ["jiě"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def pai : Form Cell :=
  { id := "qin2025_pai"
    lexeme := Lexemes.pai
    cell := d_f_flex_1_l
    form := "派"
    segments := ["pài"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def qian : Form Cell :=
  { id := "qin2025_qian"
    lexeme := Lexemes.qian
    cell := d_f_flex_1_l
    form := "钱"
    segments := ["qián"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def qun : Form Cell :=
  { id := "qin2025_qun"
    lexeme := Lexemes.qun
    cell := d_f_flex_1_l
    form := "群"
    segments := ["qún"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def ren : Form Cell :=
  { id := "qin2025_ren"
    lexeme := Lexemes.ren
    cell := d_f_flex_1_l
    form := "人"
    segments := ["rén"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def shi : Form Cell :=
  { id := "qin2025_shi"
    lexeme := Lexemes.shi
    cell := d_f_flex_1_l
    form := "事"
    segments := ["shì"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def shui : Form Cell :=
  { id := "qin2025_shui"
    lexeme := Lexemes.shui
    cell := d_f_flex_1_l
    form := "税"
    segments := ["shuì"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def suo : Form Cell :=
  { id := "qin2025_suo"
    lexeme := Lexemes.suo
    cell := d_f_flex_1_l
    form := "所"
    segments := ["suǒ"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def wu : Form Cell :=
  { id := "qin2025_wu"
    lexeme := Lexemes.wu
    cell := d_f_flex_1_l
    form := "无"
    segments := ["wú"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def xing : Form Cell :=
  { id := "qin2025_xing"
    lexeme := Lexemes.xing
    cell := d_f_flex_1_l
    form := "形"
    segments := ["xíng"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def xiu : Form Cell :=
  { id := "qin2025_xiu"
    lexeme := Lexemes.xiu
    cell := d_f_flex_1_l
    form := "秀"
    segments := ["xiù"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def you : Form Cell :=
  { id := "qin2025_you"
    lexeme := Lexemes.you
    cell := d_f_flex_1_l
    form := "有"
    segments := ["yǒu"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def ba : Form Cell :=
  { id := "qin2025_ba"
    lexeme := Lexemes.ba
    cell := d_b_flex_1_l
    form := "吧"
    segments := ["bā"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def ban : Form Cell :=
  { id := "qin2025_ban"
    lexeme := Lexemes.ban
    cell := d_b_flex_1_l
    form := "版"
    segments := ["bǎn"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def bu_2 : Form Cell :=
  { id := "qin2025_bu_2"
    lexeme := Lexemes.bu_2
    cell := d_f_flex_1_nl
    form := "不"
    segments := ["bù"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def ce : Form Cell :=
  { id := "qin2025_ce"
    lexeme := Lexemes.ce
    cell := d_b_flex_1_l
    form := "册"
    segments := ["cè"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def chang_2 : Form Cell :=
  { id := "qin2025_chang_2"
    lexeme := Lexemes.chang_2
    cell := d_b_flex_1_l
    form := "场"
    segments := ["chǎng"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def dan : Form Cell :=
  { id := "qin2025_dan"
    lexeme := Lexemes.dan
    cell := d_b_flex_1_l
    form := "单"
    segments := ["dān"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def fan_2 : Form Cell :=
  { id := "qin2025_fan_2"
    lexeme := Lexemes.fan_2
    cell := d_b_flex_1_l
    form := "泛"
    segments := ["fàn"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def fang_2 : Form Cell :=
  { id := "qin2025_fang_2"
    lexeme := Lexemes.fang_2
    cell := d_b_flex_1_l
    form := "方"
    segments := ["fāng"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def gan : Form Cell :=
  { id := "qin2025_gan"
    lexeme := Lexemes.gan
    cell := d_b_flex_1_l
    form := "感"
    segments := ["gǎn"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def gong : Form Cell :=
  { id := "qin2025_gong"
    lexeme := Lexemes.gong
    cell := d_b_flex_1_l
    form := "工"
    segments := ["gōng"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def hao : Form Cell :=
  { id := "qin2025_hao"
    lexeme := Lexemes.hao
    cell := d_f_flex_1_nl
    form := "好"
    segments := ["hǎo"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def ji : Form Cell :=
  { id := "qin2025_ji"
    lexeme := Lexemes.ji
    cell := d_b_flex_1_l
    form := "机"
    segments := ["jī"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def ke : Form Cell :=
  { id := "qin2025_ke"
    lexeme := Lexemes.ke
    cell := d_f_flex_1_nl
    form := "可"
    segments := ["kě"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def ke_2 : Form Cell :=
  { id := "qin2025_ke_2"
    lexeme := Lexemes.ke_2
    cell := d_b_flex_1_l
    form := "客"
    segments := ["kè"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def li : Form Cell :=
  { id := "qin2025_li"
    lexeme := Lexemes.li
    cell := d_b_flex_1_l
    form := "力"
    segments := ["lì"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def pin : Form Cell :=
  { id := "qin2025_pin"
    lexeme := Lexemes.pin
    cell := d_b_flex_1_l
    form := "品"
    segments := ["pǐn"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def qi : Form Cell :=
  { id := "qin2025_qi"
    lexeme := Lexemes.qi
    cell := d_b_flex_1_l
    form := "气"
    segments := ["qì"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def qi_2 : Form Cell :=
  { id := "qin2025_qi_2"
    lexeme := Lexemes.qi_2
    cell := d_b_flex_1_l
    form := "器"
    segments := ["qì"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def qin : Form Cell :=
  { id := "qin2025_qin"
    lexeme := Lexemes.qin
    cell := d_b_flex_1_l
    form := "亲"
    segments := ["qīn"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def sheng : Form Cell :=
  { id := "qin2025_sheng"
    lexeme := Lexemes.sheng
    cell := d_b_flex_1_l
    form := "生"
    segments := ["shēng"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def ti : Form Cell :=
  { id := "qin2025_ti"
    lexeme := Lexemes.ti
    cell := d_b_flex_1_l
    form := "体"
    segments := ["tǐ"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def wei : Form Cell :=
  { id := "qin2025_wei"
    lexeme := Lexemes.wei
    cell := d_b_flex_1_l
    form := "伪"
    segments := ["wěi"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def wu_2 : Form Cell :=
  { id := "qin2025_wu_2"
    lexeme := Lexemes.wu_2
    cell := d_b_flex_1_l
    form := "物"
    segments := ["wù"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def xiang : Form Cell :=
  { id := "qin2025_xiang"
    lexeme := Lexemes.xiang
    cell := d_b_flex_1_l
    form := "相"
    segments := ["xiāng"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def xiao : Form Cell :=
  { id := "qin2025_xiao"
    lexeme := Lexemes.xiao
    cell := d_f_flex_1_nl
    form := "小"
    segments := ["xiǎo"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def xin : Form Cell :=
  { id := "qin2025_xin"
    lexeme := Lexemes.xin
    cell := d_b_flex_1_l
    form := "心"
    segments := ["xīn"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def xing_2 : Form Cell :=
  { id := "qin2025_xing_2"
    lexeme := Lexemes.xing_2
    cell := d_b_flex_1_l
    form := "星"
    segments := ["xīng"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def ye : Form Cell :=
  { id := "qin2025_ye"
    lexeme := Lexemes.ye
    cell := d_b_flex_1_l
    form := "业"
    segments := ["yè"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def ying : Form Cell :=
  { id := "qin2025_ying"
    lexeme := Lexemes.ying
    cell := d_b_flex_1_l
    form := "影"
    segments := ["yǐng"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def yuan : Form Cell :=
  { id := "qin2025_yuan"
    lexeme := Lexemes.yuan
    cell := d_b_flex_1_l
    form := "园"
    segments := ["yuán"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def zheng : Form Cell :=
  { id := "qin2025_zheng"
    lexeme := Lexemes.zheng
    cell := d_b_flex_1_l
    form := "症"
    segments := ["zhèng"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def zhong : Form Cell :=
  { id := "qin2025_zhong"
    lexeme := Lexemes.zhong
    cell := d_b_flex_1_l
    form := "种"
    segments := ["zhǒng"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def zi : Form Cell :=
  { id := "qin2025_zi"
    lexeme := Lexemes.zi
    cell := d_b_flex_1_l
    form := "子"
    segments := ["zǐ"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def zi_2 : Form Cell :=
  { id := "qin2025_zi_2"
    lexeme := Lexemes.zi_2
    cell := d_b_flex_1_l
    form := "自"
    segments := ["zì"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def zong : Form Cell :=
  { id := "qin2025_zong"
    lexeme := Lexemes.zong
    cell := d_b_flex_1_l
    form := "总"
    segments := ["zǒng"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def ba_2 : Form Cell :=
  { id := "qin2025_ba_2"
    lexeme := Lexemes.ba_2
    cell := d_b_sr_1_l
    form := "霸"
    segments := ["bà"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def ban_2 : Form Cell :=
  { id := "qin2025_ban_2"
    lexeme := Lexemes.ban_2
    cell := d_b_flex_1_nl
    form := "半"
    segments := ["bàn"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def bie : Form Cell :=
  { id := "qin2025_bie"
    lexeme := Lexemes.bie
    cell := d_b_sr_1_l
    form := "别"
    segments := ["bié"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def chu : Form Cell :=
  { id := "qin2025_chu"
    lexeme := Lexemes.chu
    cell := d_b_sr_1_l
    form := "处"
    segments := ["chù"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def dao : Form Cell :=
  { id := "qin2025_dao"
    lexeme := Lexemes.dao
    cell := d_b_sr_1_l
    form := "道"
    segments := ["dào"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def ding : Form Cell :=
  { id := "qin2025_ding"
    lexeme := Lexemes.ding
    cell := d_b_sr_1_l
    form := "丁"
    segments := ["dīng"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def du : Form Cell :=
  { id := "qin2025_du"
    lexeme := Lexemes.du
    cell := d_b_sr_1_l
    form := "度"
    segments := ["dù"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def fa : Form Cell :=
  { id := "qin2025_fa"
    lexeme := Lexemes.fa
    cell := d_b_sr_1_l
    form := "法"
    segments := ["fǎ"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def fan_3 : Form Cell :=
  { id := "qin2025_fan_3"
    lexeme := Lexemes.fan_3
    cell := d_b_sr_1_l
    form := "犯"
    segments := ["fàn"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def fei : Form Cell :=
  { id := "qin2025_fei"
    lexeme := Lexemes.fei
    cell := d_b_flex_1_nl
    form := "非"
    segments := ["fēi"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def fei_2 : Form Cell :=
  { id := "qin2025_fei_2"
    lexeme := Lexemes.fei_2
    cell := d_b_sr_1_l
    form := "费"
    segments := ["fèi"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def feng : Form Cell :=
  { id := "qin2025_feng"
    lexeme := Lexemes.feng
    cell := d_b_sr_1_l
    form := "风"
    segments := ["fēng"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def fu : Form Cell :=
  { id := "qin2025_fu"
    lexeme := Lexemes.fu
    cell := d_b_sr_1_l
    form := "夫"
    segments := ["fū"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def fu_2 : Form Cell :=
  { id := "qin2025_fu_2"
    lexeme := Lexemes.fu_2
    cell := d_b_sl_1_l
    form := "副"
    segments := ["fù"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def guan : Form Cell :=
  { id := "qin2025_guan"
    lexeme := Lexemes.guan
    cell := d_b_sr_1_l
    form := "观"
    segments := ["guān"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def gui : Form Cell :=
  { id := "qin2025_gui"
    lexeme := Lexemes.gui
    cell := d_b_sr_1_l
    form := "鬼"
    segments := ["guǐ"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def gun : Form Cell :=
  { id := "qin2025_gun"
    lexeme := Lexemes.gun
    cell := d_b_sr_1_l
    form := "棍"
    segments := ["gùn"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def han : Form Cell :=
  { id := "qin2025_han"
    lexeme := Lexemes.han
    cell := d_b_sr_1_l
    form := "汉"
    segments := ["hàn"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def hao_2 : Form Cell :=
  { id := "qin2025_hao_2"
    lexeme := Lexemes.hao_2
    cell := d_b_sr_1_l
    form := "豪"
    segments := ["háo"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def jia : Form Cell :=
  { id := "qin2025_jia"
    lexeme := Lexemes.jia
    cell := d_b_sr_1_l
    form := "家"
    segments := ["jiā"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def jian : Form Cell :=
  { id := "qin2025_jian"
    lexeme := Lexemes.jian
    cell := d_b_sr_1_l
    form := "件"
    segments := ["jiàn"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def jiang : Form Cell :=
  { id := "qin2025_jiang"
    lexeme := Lexemes.jiang
    cell := d_b_sr_1_l
    form := "匠"
    segments := ["jiàng"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def jie_2 : Form Cell :=
  { id := "qin2025_jie_2"
    lexeme := Lexemes.jie_2
    cell := d_b_sr_1_l
    form := "界"
    segments := ["jiè"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def ju : Form Cell :=
  { id := "qin2025_ju"
    lexeme := Lexemes.ju
    cell := d_b_sr_1_l
    form := "具"
    segments := ["jù"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def lei : Form Cell :=
  { id := "qin2025_lei"
    lexeme := Lexemes.lei
    cell := d_b_sl_1_l
    form := "类"
    segments := ["lèi"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def ling : Form Cell :=
  { id := "qin2025_ling"
    lexeme := Lexemes.ling
    cell := d_f_sl_1_nl
    form := "零"
    segments := ["líng"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def lun : Form Cell :=
  { id := "qin2025_lun"
    lexeme := Lexemes.lun
    cell := d_b_sr_1_l
    form := "论"
    segments := ["lùn"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def lu : Form Cell :=
  { id := "qin2025_lu"
    lexeme := Lexemes.lu
    cell := d_b_sr_1_l
    form := "率"
    segments := ["lǜ"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def mang : Form Cell :=
  { id := "qin2025_mang"
    lexeme := Lexemes.mang
    cell := d_b_sr_1_l
    form := "盲"
    segments := ["máng"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def mi : Form Cell :=
  { id := "qin2025_mi"
    lexeme := Lexemes.mi
    cell := d_b_sr_1_l
    form := "迷"
    segments := ["mí"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def min : Form Cell :=
  { id := "qin2025_min"
    lexeme := Lexemes.min
    cell := d_b_sr_1_l
    form := "民"
    segments := ["mín"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def re : Form Cell :=
  { id := "qin2025_re"
    lexeme := Lexemes.re
    cell := d_b_sr_1_l
    form := "热"
    segments := ["rè"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def ruan : Form Cell :=
  { id := "qin2025_ruan"
    lexeme := Lexemes.ruan
    cell := d_b_sl_1_l
    form := "软"
    segments := ["ruǎn"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def shi_2 : Form Cell :=
  { id := "qin2025_shi_2"
    lexeme := Lexemes.shi_2
    cell := d_b_sr_1_l
    form := "师"
    segments := ["shī"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def shi_3 : Form Cell :=
  { id := "qin2025_shi_3"
    lexeme := Lexemes.shi_3
    cell := d_b_sr_1_l
    form := "士"
    segments := ["shì"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def shi_4 : Form Cell :=
  { id := "qin2025_shi_4"
    lexeme := Lexemes.shi_4
    cell := d_b_sr_1_l
    form := "式"
    segments := ["shì"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def shou : Form Cell :=
  { id := "qin2025_shou"
    lexeme := Lexemes.shou
    cell := d_b_sr_1_l
    form := "手"
    segments := ["shǒu"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def tan : Form Cell :=
  { id := "qin2025_tan"
    lexeme := Lexemes.tan
    cell := d_b_sr_1_l
    form := "坛"
    segments := ["tán"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def tu : Form Cell :=
  { id := "qin2025_tu"
    lexeme := Lexemes.tu
    cell := d_b_sr_1_l
    form := "徒"
    segments := ["tú"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def xing_3 : Form Cell :=
  { id := "qin2025_xing_3"
    lexeme := Lexemes.xing_3
    cell := d_b_sr_1_l
    form := "型"
    segments := ["xíng"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def xue : Form Cell :=
  { id := "qin2025_xue"
    lexeme := Lexemes.xue
    cell := d_b_sr_1_l
    form := "学"
    segments := ["xué"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def ya : Form Cell :=
  { id := "qin2025_ya"
    lexeme := Lexemes.ya
    cell := d_b_sl_1_l
    form := "亚"
    segments := ["yà"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def yan : Form Cell :=
  { id := "qin2025_yan"
    lexeme := Lexemes.yan
    cell := d_b_sr_1_l
    form := "炎"
    segments := ["yán"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def yi : Form Cell :=
  { id := "qin2025_yi"
    lexeme := Lexemes.yi
    cell := d_b_sr_1_l
    form := "仪"
    segments := ["yí"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def you_2 : Form Cell :=
  { id := "qin2025_you_2"
    lexeme := Lexemes.you_2
    cell := d_b_sr_1_l
    form := "友"
    segments := ["yǒu"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def yuan_2 : Form Cell :=
  { id := "qin2025_yuan_2"
    lexeme := Lexemes.yuan_2
    cell := d_b_sr_1_l
    form := "员"
    segments := ["yuán"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def zhang : Form Cell :=
  { id := "qin2025_zhang"
    lexeme := Lexemes.zhang
    cell := d_b_sr_1_l
    form := "张"
    segments := ["zhāng"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def zhang_2 : Form Cell :=
  { id := "qin2025_zhang_2"
    lexeme := Lexemes.zhang_2
    cell := d_b_sr_1_l
    form := "长"
    segments := ["zhǎng"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def zhe : Form Cell :=
  { id := "qin2025_zhe"
    lexeme := Lexemes.zhe
    cell := d_b_sr_1_l
    form := "者"
    segments := ["zhě"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def zhi : Form Cell :=
  { id := "qin2025_zhi"
    lexeme := Lexemes.zhi
    cell := d_b_sr_1_l
    form := "制"
    segments := ["zhì"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def zhi_2 : Form Cell :=
  { id := "qin2025_zhi_2"
    lexeme := Lexemes.zhi_2
    cell := d_b_sr_1_l
    form := "质"
    segments := ["zhì"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def zu : Form Cell :=
  { id := "qin2025_zu"
    lexeme := Lexemes.zu
    cell := d_b_sr_1_l
    form := "族"
    segments := ["zú"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def chao : Form Cell :=
  { id := "qin2025_chao"
    lexeme := Lexemes.chao
    cell := d_b_sl_1_nl
    form := "超"
    segments := ["chāo"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def ci : Form Cell :=
  { id := "qin2025_ci"
    lexeme := Lexemes.ci
    cell := d_b_sl_1_nl
    form := "次"
    segments := ["cì"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def hua : Form Cell :=
  { id := "qin2025_hua"
    lexeme := Lexemes.hua
    cell := d_b_sr_1_nl
    form := "化"
    segments := ["huà"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def lai : Form Cell :=
  { id := "qin2025_lai"
    lexeme := Lexemes.lai
    cell := d_b_sr_1_nl
    form := "来"
    segments := ["lái"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def mian : Form Cell :=
  { id := "qin2025_mian"
    lexeme := Lexemes.mian
    cell := d_b_sr_1_nl
    form := "面"
    segments := ["miàn"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def nan : Form Cell :=
  { id := "qin2025_nan"
    lexeme := Lexemes.nan
    cell := d_b_sl_1_nl
    form := "难"
    segments := ["nán"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def ran : Form Cell :=
  { id := "qin2025_ran"
    lexeme := Lexemes.ran
    cell := d_b_sr_1_nl
    form := "然"
    segments := ["rán"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def shi_5 : Form Cell :=
  { id := "qin2025_shi_5"
    lexeme := Lexemes.shi_5
    cell := d_b_sr_1_nl
    form := "是"
    segments := ["shì"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def xing_4 : Form Cell :=
  { id := "qin2025_xing_4"
    lexeme := Lexemes.xing_4
    cell := d_b_sr_1_nl
    form := "性"
    segments := ["xìng"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def yi_2 : Form Cell :=
  { id := "qin2025_yi_2"
    lexeme := Lexemes.yi_2
    cell := d_b_sl_1_nl
    form := "一"
    segments := ["yī"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def zhun : Form Cell :=
  { id := "qin2025_zhun"
    lexeme := Lexemes.zhun
    cell := d_b_sl_1_nl
    form := "准"
    segments := ["zhǔn"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def bian : Form Cell :=
  { id := "qin2025_bian"
    lexeme := Lexemes.bian
    cell := d_b_sr_tl_nl
    form := "边"
    segments := ["bian"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

def ge_2 : Form Cell :=
  { id := "qin2025_ge_2"
    lexeme := Lexemes.ge_2
    cell := d_b_sr_tl_nl
    form := "个"
    segments := ["ge"]
    source := [
      ⟨"qin-2025", "Appendix A"⟩
    ] }

/-- The source's analysis of a form, its parse rather than data. -/
structure Analysis where
  /-- The form analysed. -/
  form : Form Cell
  /-- The `Group` column, the group the paper assigns. -/
  group : String
  deriving DecidableEq, Repr

def bu.analysis : Analysis :=
  { form := bu,
    group := "1" }

def chang.analysis : Analysis :=
  { form := chang,
    group := "1" }

def dai.analysis : Analysis :=
  { form := dai,
    group := "1" }

def duo.analysis : Analysis :=
  { form := duo,
    group := "1" }

def fan.analysis : Analysis :=
  { form := fan,
    group := "1" }

def fang.analysis : Analysis :=
  { form := fang,
    group := "1" }

def fen.analysis : Analysis :=
  { form := fen,
    group := "1" }

def ge.analysis : Analysis :=
  { form := ge,
    group := "1" }

def guo.analysis : Analysis :=
  { form := guo,
    group := "1" }

def hu.analysis : Analysis :=
  { form := hu,
    group := "1" }

def jie.analysis : Analysis :=
  { form := jie,
    group := "1" }

def pai.analysis : Analysis :=
  { form := pai,
    group := "1" }

def qian.analysis : Analysis :=
  { form := qian,
    group := "1" }

def qun.analysis : Analysis :=
  { form := qun,
    group := "1" }

def ren.analysis : Analysis :=
  { form := ren,
    group := "1" }

def shi.analysis : Analysis :=
  { form := shi,
    group := "1" }

def shui.analysis : Analysis :=
  { form := shui,
    group := "1" }

def suo.analysis : Analysis :=
  { form := suo,
    group := "1" }

def wu.analysis : Analysis :=
  { form := wu,
    group := "1" }

def xing.analysis : Analysis :=
  { form := xing,
    group := "1" }

def xiu.analysis : Analysis :=
  { form := xiu,
    group := "1" }

def you.analysis : Analysis :=
  { form := you,
    group := "1" }

def ba.analysis : Analysis :=
  { form := ba,
    group := "2" }

def ban.analysis : Analysis :=
  { form := ban,
    group := "2" }

def bu_2.analysis : Analysis :=
  { form := bu_2,
    group := "2" }

def ce.analysis : Analysis :=
  { form := ce,
    group := "2" }

def chang_2.analysis : Analysis :=
  { form := chang_2,
    group := "2" }

def dan.analysis : Analysis :=
  { form := dan,
    group := "2" }

def fan_2.analysis : Analysis :=
  { form := fan_2,
    group := "2" }

def fang_2.analysis : Analysis :=
  { form := fang_2,
    group := "2" }

def gan.analysis : Analysis :=
  { form := gan,
    group := "2" }

def gong.analysis : Analysis :=
  { form := gong,
    group := "2" }

def hao.analysis : Analysis :=
  { form := hao,
    group := "2" }

def ji.analysis : Analysis :=
  { form := ji,
    group := "2" }

def ke.analysis : Analysis :=
  { form := ke,
    group := "2" }

def ke_2.analysis : Analysis :=
  { form := ke_2,
    group := "2" }

def li.analysis : Analysis :=
  { form := li,
    group := "2" }

def pin.analysis : Analysis :=
  { form := pin,
    group := "2" }

def qi.analysis : Analysis :=
  { form := qi,
    group := "2" }

def qi_2.analysis : Analysis :=
  { form := qi_2,
    group := "2" }

def qin.analysis : Analysis :=
  { form := qin,
    group := "2" }

def sheng.analysis : Analysis :=
  { form := sheng,
    group := "2" }

def ti.analysis : Analysis :=
  { form := ti,
    group := "2" }

def wei.analysis : Analysis :=
  { form := wei,
    group := "2" }

def wu_2.analysis : Analysis :=
  { form := wu_2,
    group := "2" }

def xiang.analysis : Analysis :=
  { form := xiang,
    group := "2" }

def xiao.analysis : Analysis :=
  { form := xiao,
    group := "2" }

def xin.analysis : Analysis :=
  { form := xin,
    group := "2" }

def xing_2.analysis : Analysis :=
  { form := xing_2,
    group := "2" }

def ye.analysis : Analysis :=
  { form := ye,
    group := "2" }

def ying.analysis : Analysis :=
  { form := ying,
    group := "2" }

def yuan.analysis : Analysis :=
  { form := yuan,
    group := "2" }

def zheng.analysis : Analysis :=
  { form := zheng,
    group := "2" }

def zhong.analysis : Analysis :=
  { form := zhong,
    group := "2" }

def zi.analysis : Analysis :=
  { form := zi,
    group := "2" }

def zi_2.analysis : Analysis :=
  { form := zi_2,
    group := "2" }

def zong.analysis : Analysis :=
  { form := zong,
    group := "2" }

def ba_2.analysis : Analysis :=
  { form := ba_2,
    group := "3" }

def ban_2.analysis : Analysis :=
  { form := ban_2,
    group := "3" }

def bie.analysis : Analysis :=
  { form := bie,
    group := "3" }

def chu.analysis : Analysis :=
  { form := chu,
    group := "3" }

def dao.analysis : Analysis :=
  { form := dao,
    group := "3" }

def ding.analysis : Analysis :=
  { form := ding,
    group := "3" }

def du.analysis : Analysis :=
  { form := du,
    group := "3" }

def fa.analysis : Analysis :=
  { form := fa,
    group := "3" }

def fan_3.analysis : Analysis :=
  { form := fan_3,
    group := "3" }

def fei.analysis : Analysis :=
  { form := fei,
    group := "3" }

def fei_2.analysis : Analysis :=
  { form := fei_2,
    group := "3" }

def feng.analysis : Analysis :=
  { form := feng,
    group := "3" }

def fu.analysis : Analysis :=
  { form := fu,
    group := "3" }

def fu_2.analysis : Analysis :=
  { form := fu_2,
    group := "3" }

def guan.analysis : Analysis :=
  { form := guan,
    group := "3" }

def gui.analysis : Analysis :=
  { form := gui,
    group := "3" }

def gun.analysis : Analysis :=
  { form := gun,
    group := "3" }

def han.analysis : Analysis :=
  { form := han,
    group := "3" }

def hao_2.analysis : Analysis :=
  { form := hao_2,
    group := "3" }

def jia.analysis : Analysis :=
  { form := jia,
    group := "3" }

def jian.analysis : Analysis :=
  { form := jian,
    group := "3" }

def jiang.analysis : Analysis :=
  { form := jiang,
    group := "3" }

def jie_2.analysis : Analysis :=
  { form := jie_2,
    group := "3" }

def ju.analysis : Analysis :=
  { form := ju,
    group := "3" }

def lei.analysis : Analysis :=
  { form := lei,
    group := "3" }

def ling.analysis : Analysis :=
  { form := ling,
    group := "3" }

def lun.analysis : Analysis :=
  { form := lun,
    group := "3" }

def lu.analysis : Analysis :=
  { form := lu,
    group := "3" }

def mang.analysis : Analysis :=
  { form := mang,
    group := "3" }

def mi.analysis : Analysis :=
  { form := mi,
    group := "3" }

def min.analysis : Analysis :=
  { form := min,
    group := "3" }

def re.analysis : Analysis :=
  { form := re,
    group := "3" }

def ruan.analysis : Analysis :=
  { form := ruan,
    group := "3" }

def shi_2.analysis : Analysis :=
  { form := shi_2,
    group := "3" }

def shi_3.analysis : Analysis :=
  { form := shi_3,
    group := "3" }

def shi_4.analysis : Analysis :=
  { form := shi_4,
    group := "3" }

def shou.analysis : Analysis :=
  { form := shou,
    group := "3" }

def tan.analysis : Analysis :=
  { form := tan,
    group := "3" }

def tu.analysis : Analysis :=
  { form := tu,
    group := "3" }

def xing_3.analysis : Analysis :=
  { form := xing_3,
    group := "3" }

def xue.analysis : Analysis :=
  { form := xue,
    group := "3" }

def ya.analysis : Analysis :=
  { form := ya,
    group := "3" }

def yan.analysis : Analysis :=
  { form := yan,
    group := "3" }

def yi.analysis : Analysis :=
  { form := yi,
    group := "3" }

def you_2.analysis : Analysis :=
  { form := you_2,
    group := "3" }

def yuan_2.analysis : Analysis :=
  { form := yuan_2,
    group := "3" }

def zhang.analysis : Analysis :=
  { form := zhang,
    group := "3" }

def zhang_2.analysis : Analysis :=
  { form := zhang_2,
    group := "3" }

def zhe.analysis : Analysis :=
  { form := zhe,
    group := "3" }

def zhi.analysis : Analysis :=
  { form := zhi,
    group := "3" }

def zhi_2.analysis : Analysis :=
  { form := zhi_2,
    group := "3" }

def zu.analysis : Analysis :=
  { form := zu,
    group := "3" }

def chao.analysis : Analysis :=
  { form := chao,
    group := "4" }

def ci.analysis : Analysis :=
  { form := ci,
    group := "4" }

def hua.analysis : Analysis :=
  { form := hua,
    group := "4" }

def lai.analysis : Analysis :=
  { form := lai,
    group := "4" }

def mian.analysis : Analysis :=
  { form := mian,
    group := "4" }

def nan.analysis : Analysis :=
  { form := nan,
    group := "4" }

def ran.analysis : Analysis :=
  { form := ran,
    group := "4" }

def shi_5.analysis : Analysis :=
  { form := shi_5,
    group := "4" }

def xing_4.analysis : Analysis :=
  { form := xing_4,
    group := "4" }

def yi_2.analysis : Analysis :=
  { form := yi_2,
    group := "4" }

def zhun.analysis : Analysis :=
  { form := zhun,
    group := "4" }

def bian.analysis : Analysis :=
  { form := bian,
    group := "5" }

def ge_2.analysis : Analysis :=
  { form := ge_2,
    group := "5" }

/-- Every lexeme of the data. -/
def lexemes : List Lexeme := [Lexemes.bu, Lexemes.chang, Lexemes.dai, Lexemes.duo, Lexemes.fan,
  Lexemes.fang, Lexemes.fen, Lexemes.ge, Lexemes.guo, Lexemes.hu, Lexemes.jie, Lexemes.pai,
  Lexemes.qian, Lexemes.qun, Lexemes.ren, Lexemes.shi, Lexemes.shui, Lexemes.suo, Lexemes.wu,
  Lexemes.xing, Lexemes.xiu, Lexemes.you, Lexemes.ba, Lexemes.ban, Lexemes.bu_2, Lexemes.ce,
  Lexemes.chang_2, Lexemes.dan, Lexemes.fan_2, Lexemes.fang_2, Lexemes.gan, Lexemes.gong,
  Lexemes.hao, Lexemes.ji, Lexemes.ke, Lexemes.ke_2, Lexemes.li, Lexemes.pin, Lexemes.qi,
  Lexemes.qi_2, Lexemes.qin, Lexemes.sheng, Lexemes.ti, Lexemes.wei, Lexemes.wu_2, Lexemes.xiang,
  Lexemes.xiao, Lexemes.xin, Lexemes.xing_2, Lexemes.ye, Lexemes.ying, Lexemes.yuan, Lexemes.zheng,
  Lexemes.zhong, Lexemes.zi, Lexemes.zi_2, Lexemes.zong, Lexemes.ba_2, Lexemes.ban_2, Lexemes.bie,
  Lexemes.chu, Lexemes.dao, Lexemes.ding, Lexemes.du, Lexemes.fa, Lexemes.fan_3, Lexemes.fei,
  Lexemes.fei_2, Lexemes.feng, Lexemes.fu, Lexemes.fu_2, Lexemes.guan, Lexemes.gui, Lexemes.gun,
  Lexemes.han, Lexemes.hao_2, Lexemes.jia, Lexemes.jian, Lexemes.jiang, Lexemes.jie_2, Lexemes.ju,
  Lexemes.lei, Lexemes.ling, Lexemes.lun, Lexemes.lu, Lexemes.mang, Lexemes.mi, Lexemes.min,
  Lexemes.re, Lexemes.ruan, Lexemes.shi_2, Lexemes.shi_3, Lexemes.shi_4, Lexemes.shou, Lexemes.tan,
  Lexemes.tu, Lexemes.xing_3, Lexemes.xue, Lexemes.ya, Lexemes.yan, Lexemes.yi, Lexemes.you_2,
  Lexemes.yuan_2, Lexemes.zhang, Lexemes.zhang_2, Lexemes.zhe, Lexemes.zhi, Lexemes.zhi_2,
  Lexemes.zu, Lexemes.chao, Lexemes.ci, Lexemes.hua, Lexemes.lai, Lexemes.mian, Lexemes.nan,
  Lexemes.ran, Lexemes.shi_5, Lexemes.xing_4, Lexemes.yi_2, Lexemes.zhun, Lexemes.bian,
  Lexemes.ge_2]

/-- Every form the sources accept. -/
def all : List (Form Cell) := [bu, chang, dai, duo, fan, fang, fen, ge, guo, hu, jie, pai, qian,
  qun, ren, shi, shui, suo, wu, xing, xiu, you, ba, ban, bu_2, ce, chang_2, dan, fan_2, fang_2, gan,
  gong, hao, ji, ke, ke_2, li, pin, qi, qi_2, qin, sheng, ti, wei, wu_2, xiang, xiao, xin, xing_2,
  ye, ying, yuan, zheng, zhong, zi, zi_2, zong, ba_2, ban_2, bie, chu, dao, ding, du, fa, fan_3,
  fei, fei_2, feng, fu, fu_2, guan, gui, gun, han, hao_2, jia, jian, jiang, jie_2, ju, lei, ling,
  lun, lu, mang, mi, min, re, ruan, shi_2, shi_3, shi_4, shou, tan, tu, xing_3, xue, ya, yan, yi,
  you_2, yuan_2, zhang, zhang_2, zhe, zhi, zhi_2, zu, chao, ci, hua, lai, mian, nan, ran, shi_5,
  xing_4, yi_2, zhun, bian, ge_2]

/-- Every form a source marks, as marginal, questionable, unacceptable or ungrammatical. -/
def marked : List (Form Cell) := []

/-- Every relation the sources assert between forms. -/
def relations : List (FormRelation (Form Cell)) := []

/-- Every analysis of the data. -/
def analyses : List Analysis := [bu.analysis, chang.analysis, dai.analysis, duo.analysis,
  fan.analysis, fang.analysis, fen.analysis, ge.analysis, guo.analysis, hu.analysis, jie.analysis,
  pai.analysis, qian.analysis, qun.analysis, ren.analysis, shi.analysis, shui.analysis,
  suo.analysis, wu.analysis, xing.analysis, xiu.analysis, you.analysis, ba.analysis, ban.analysis,
  bu_2.analysis, ce.analysis, chang_2.analysis, dan.analysis, fan_2.analysis, fang_2.analysis,
  gan.analysis, gong.analysis, hao.analysis, ji.analysis, ke.analysis, ke_2.analysis, li.analysis,
  pin.analysis, qi.analysis, qi_2.analysis, qin.analysis, sheng.analysis, ti.analysis, wei.analysis,
  wu_2.analysis, xiang.analysis, xiao.analysis, xin.analysis, xing_2.analysis, ye.analysis,
  ying.analysis, yuan.analysis, zheng.analysis, zhong.analysis, zi.analysis, zi_2.analysis,
  zong.analysis, ba_2.analysis, ban_2.analysis, bie.analysis, chu.analysis, dao.analysis,
  ding.analysis, du.analysis, fa.analysis, fan_3.analysis, fei.analysis, fei_2.analysis,
  feng.analysis, fu.analysis, fu_2.analysis, guan.analysis, gui.analysis, gun.analysis,
  han.analysis, hao_2.analysis, jia.analysis, jian.analysis, jiang.analysis, jie_2.analysis,
  ju.analysis, lei.analysis, ling.analysis, lun.analysis, lu.analysis, mang.analysis, mi.analysis,
  min.analysis, re.analysis, ruan.analysis, shi_2.analysis, shi_3.analysis, shi_4.analysis,
  shou.analysis, tan.analysis, tu.analysis, xing_3.analysis, xue.analysis, ya.analysis,
  yan.analysis, yi.analysis, you_2.analysis, yuan_2.analysis, zhang.analysis, zhang_2.analysis,
  zhe.analysis, zhi.analysis, zhi_2.analysis, zu.analysis, chao.analysis, ci.analysis, hua.analysis,
  lai.analysis, mian.analysis, nan.analysis, ran.analysis, shi_5.analysis, xing_4.analysis,
  yi_2.analysis, zhun.analysis, bian.analysis, ge_2.analysis]

end Qin2025.Wordlist
