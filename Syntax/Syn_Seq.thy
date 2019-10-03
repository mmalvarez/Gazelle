theory Syn_Seq imports "Syntax"
begin


locale Syn_Seq =
  fixes rxsq :: "'sq \<Rightarrow> reified"
  fixes dxsq :: "reified \<Rightarrow> 'sq"
  fixes rxp :: "'xp \<Rightarrow> reified"
  fixes dxp :: "reified \<Rightarrow> 'xp"
  fixes othercases :: "char list \<Rightarrow> reified \<Rightarrow> (char list * 'xp * 'xs) option"

begin


definition C' ::
  "char list  \<Rightarrow> reified \<Rightarrow>
    (char list \<Rightarrow> reified \<Rightarrow> (char list * 'xp * 'xs) option) \<Rightarrow>
    ('sq, 'xp, 'xs) mpackf option" where
"C' s xpsq others =
  docons ''Seq'' s xpsq (rsplit dxp dxsq) others"

definition C ::
  "char list  \<Rightarrow> reified \<Rightarrow> reified \<Rightarrow>
    ('sq, 'xp, 'xs) mpackf option" where
"C s xp sq  =
  C' s (rpair xp sq) othercases"

(* may run into issues with phantom type variables here *)
definition LSeq :: "'xp \<Rightarrow> 'sq \<Rightarrow> ('sq, 'xp, 'xs) mpackf" where
    "LSeq xp sq = force (C ''Seq'' (rxp xp) (rxsq sq))"

(* scoping, used in Elle *)
(*
type_synonym ('xp1, 'xs1, 'xp2, 'xs2) syn_seq_scope =
  "((nat list option, 'xp1, 'xs1) mpack, 'xp2, 'xs2) mpack"
*)
end

end