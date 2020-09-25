theory Merge_Syntax_Full imports "Syntax"
begin

locale Syn_Merge_Full =
fixes rxl :: "'l \<Rightarrow> reified"
fixes dxl :: "reified \<Rightarrow> 'l"
fixes rxr :: "'r \<Rightarrow> reified"
fixes dxr :: "reified \<Rightarrow> 'r"
fixes rxp :: "'xp \<Rightarrow> reified"
fixes dxp :: "reified \<Rightarrow> 'xp"

fixes C'l ::
  "char list \<Rightarrow> reified  \<Rightarrow>
    (char list \<Rightarrow> reified \<Rightarrow> (char list * 'xp * 'xsl) option) \<Rightarrow>
     ('l, 'xp, 'xsl) mpackf option"

(* need "others" or just inline? *)
fixes othersl ::
"(char list \<Rightarrow> reified \<Rightarrow> (char list * 'xp * 'xsl) option)"

fixes C'r ::
  "char list \<Rightarrow> reified  \<Rightarrow> 
  (char list \<Rightarrow> reified \<Rightarrow> (char list * 'xp * 'xsr) option) \<Rightarrow>
  ('r, 'xp, 'xsr) mpackf option"

fixes othersr ::
"(char list \<Rightarrow> reified \<Rightarrow> (char list * 'xp * 'xsr) option)"
begin

(* generalizations over Merge_Syntax:
   - combined product type, convertible into either output product
   - left side is more general, subsumes right side
      (all? part?)
*)

definition C' ::
  "char list \<Rightarrow> reified \<Rightarrow> 
    (char list \<Rightarrow> reified \<Rightarrow> (char list * 'xp * ('xsl + 'xsr)) option) \<Rightarrow>
    ('l, 'xp, ('r, 'xsl + 'xsr) mmpack) mpackf option" where

end
end