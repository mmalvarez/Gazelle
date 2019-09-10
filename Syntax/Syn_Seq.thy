theory Syn_Seq imports "../Syntax_Utils"
begin

type_synonym ('sq, 'xb, 'xa) syn_seq =
  "('xb + 'sq + 'xa)"

type_synonym ('sq, 'xb, 'xa, 'o) syn_seq_disc =
  "('xb * ('sq \<Rightarrow> 'o) * 'xa)"

fun syn_seq_cases ::
  "('sq, 'xb, 'xa) syn_seq \<Rightarrow> ('sq, 'xb \<Rightarrow> 'o, 'xa \<Rightarrow> 'o, 'o) syn_seq_disc \<Rightarrow> 'o" where
  "syn_seq_cases s d = disc3 s d"

(* may run into issues with phantom type variables here *)
definition LSeq :: "'sq \<Rightarrow> ('sq, 'xb, 'xa) syn_seq" where
    "LSeq x = snth2h x"


type_synonym ('sq, 'xb, 'xa) dat_seq =
  "('xb * 'sq * 'xa)"

(* scoping, used in Elle *)
type_synonym ('sqb, 'sqa, 'xb, 'xa) syn_seq_scope =
  "((nat list option, 'sqb, 'sqa) dat_seq, 'xb, 'xa) syn_seq"

end
