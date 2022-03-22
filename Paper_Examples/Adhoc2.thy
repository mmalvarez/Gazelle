theory Adhoc2
  imports "../Lifter/Lifter" "../Lifter/Auto_Lifter" "HOL-Library.Adhoc_Overloading"
begin

class noname

instantiation bool :: noname
begin
instance proof qed
end

instantiation char :: noname
begin
instance proof qed
end

(* we need to have imported "HOL-Library.Adhoc_Overloading" for this to work *)
consts tyname :: "'a itself \<Rightarrow> char list"

definition tyn_unit :: "unit itself \<Rightarrow> char list" where
"tyn_unit _ = ''UNIT''"

definition tyn_nat :: "nat itself \<Rightarrow> char list" where
"tyn_nat _ = ''NAT''"
(* check the output for nat *)

text_raw \<open>%Snippet paper_examples__adhoc2__tyname\<close>
definition tyn_option_bad ::
  "('a option itself \<Rightarrow> char list)" where
"tyn_option_bad _ =
  (tyname (TYPE('a))) @ '' OPTION''"

adhoc_overloading tyname
  tyn_unit
  tyn_nat
  tyn_option_bad

(* this produces a type error *)
(* value [nbe] "tyname (TYPE (unit option))" *)
text_raw \<open>%EndSnippet\<close>

end