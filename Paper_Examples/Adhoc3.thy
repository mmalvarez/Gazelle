theory Adhoc3
  imports "../Lifter/Lifter" "../Lifter/Auto_Lifter" "HOL-Library.Adhoc_Overloading"
begin

(* we need to have imported "HOL-Library.Adhoc_Overloading" for this to work *)
consts tyname :: "'a itself \<Rightarrow> char list"

definition tyn_unit :: "unit itself \<Rightarrow> char list" where
"tyn_unit _ = ''UNIT''"

definition tyn_nat :: "nat itself \<Rightarrow> char list" where
"tyn_nat _ = ''NAT''"

value [nbe] "tyname (TYPE (nat))"

text_raw \<open>%Snippet paper_examples__adhoc3__tyname\<close>
definition tyn_option ::
  "('a itself \<Rightarrow> char list) \<Rightarrow> ('a option itself \<Rightarrow> char list)" where
"tyn_option t _ =
  (t (TYPE( 'a))) @ '' OPTION''"

adhoc_overloading tyname
  tyn_unit
  tyn_nat
 "tyn_option tyname"

value [nbe] "tyname (TYPE (unit option))"
\<comment> \<open>Result:\<close>
text \<open>@{value "tyname (TYPE (unit option))"}\<close>

value [nbe] "tyname (TYPE (unit option option))"
\<comment> \<open>Result:\<close>
text \<open>@{value "tyname (TYPE (unit option option))"}\<close>
text_raw \<open>%EndSnippet\<close>

end