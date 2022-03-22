theory Adhoc5
  imports "../Lifter/Lifter" "../Lifter/Auto_Lifter" "HOL-Library.Adhoc_Overloading"
begin

text_raw \<open>%Snippet paper_examples__adhoc5__noname\<close>
class noname

instantiation bool :: noname
begin
instance proof qed
end

instantiation char :: noname
begin
instance proof qed
end
text_raw \<open>%EndSnippet\<close>

consts tyname :: "'a itself \<Rightarrow> char list"

definition tyn_unit :: "unit itself \<Rightarrow> char list" where
"tyn_unit _ = ''UNIT''"

definition tyn_nat :: "nat itself \<Rightarrow> char list" where
"tyn_nat _ = ''NAT''"

definition tyn_option ::
  "('a itself \<Rightarrow> char list) \<Rightarrow> ('a option itself \<Rightarrow> char list)" where
"tyn_option t _ =
  (t (TYPE( 'a))) @ '' OPTION''"

text_raw \<open>%Snippet paper_examples__adhoc5__tyname\<close>
definition tyn_noname :: "('a :: noname) itself \<Rightarrow> char list" where
"tyn_noname _ = ''UHOH''"

adhoc_overloading tyname
  tyn_unit
  tyn_nat
  tyn_noname
 "tyn_option tyname"

value [nbe] "tyname(TYPE (bool))"
value [nbe] "tyname(TYPE (bool option))"
text_raw \<open>%EndSnippet\<close>

end