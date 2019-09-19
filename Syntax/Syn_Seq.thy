theory Syn_Seq imports "../Syntax_Utils" "MiniPack"
begin

type_synonym ('sq, 'xp, 'xs) syn_seq =
  "('sq, 'xp, 'xs) mpack"

type_synonym ('sq, 'xb, 'xa, 'o) syn_seq_disc =
  "('sq, 'xb, 'xa, 'o) mp_disc"

(*
fun syn_seq_cases ::
  "('sq, 'xb, 'xa) syn_seq \<Rightarrow> 
   ('sq, 'xb \<Rightarrow> 'o, 'xa \<Rightarrow> 'o, 'o) syn_seq_disc \<Rightarrow> 'o" where
  "syn_seq_cases s d = disc3 s d"
*)

(* may run into issues with phantom type variables here *)
definition LSeq :: "'sq \<Rightarrow> 'xp \<Rightarrow> ('sq, 'xp, 'xs) syn_seq" where
    "LSeq sq xp = mp_constr sq xp"

(* scoping, used in Elle *)
type_synonym ('xp1, 'xs1, 'xp2, 'xs2) syn_seq_scope =
  "((nat list option, 'xp1, 'xs1) mpack, 'xp2, 'xs2) mpack"

end
