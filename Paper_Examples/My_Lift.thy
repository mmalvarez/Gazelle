theory My_Lift
  imports "../Lifter/Lifter" "../Lifter/Auto_Lifter" "HOL-Library.Adhoc_Overloading"
begin

text_raw \<open>%Snippet paper_examples__my_lift__my_lift_manual\<close>
definition my_lift_manual :: "
('x, 'a1 :: Bogus, 'b1 :: Mergeableb) lifting \<Rightarrow>
('x, 'a2 :: Bogus, 'b2 :: Mergeableb) lifting \<Rightarrow>
('x, 'a3 :: Bogus, 'b3 :: Mergeableb) lifting \<Rightarrow>
('x, ('a1 * ('a2 * 'a3)), (('b2 * 'b1) * ('b3 * ('b4 :: Mergeableb)))) lifting"  where
"my_lift_manual l1 l2 l3 =
  (merge_l (fst_l (snd_l l1)) (merge_l (fst_l (fst_l l2)) (snd_l (fst_l l3))))"
text_raw \<open>%EndSnippet\<close>

text_raw \<open>%Snippet paper_examples__my_lift__my_lift\<close>
definition my_lift :: "
('x, 'a1 :: Bogus, 'b1 :: Mergeableb) lifting \<Rightarrow>
('x, 'a2 :: Bogus, 'b2 :: Mergeableb) lifting \<Rightarrow>
('x, 'a3 :: Bogus, 'b3 :: Mergeableb) lifting \<Rightarrow>
('x, ('a1 * ('a2 * 'a3)), (('b2 * 'b1) * ('b3 * ('b4 :: Mergeableb)))) lifting"  where
"my_lift l1 l2 l3 =
	schem_lift (SP NA (SP NB NC)) 
		(SP (SP (SINJ l2 NB) (SINJ l1 NA)) (SP (SINJ l3 NC) NX))"
text_raw \<open>%EndSnippet\<close>

class noname

instantiation bool :: noname
begin
instance proof qed
end

instantiation char :: noname
begin
instance proof qed
end

text_raw \<open>%Snippet paper_examples__my_lift__tyname\<close>
(* we need to have imported "HOL-Library.Adhoc_Overloading" for this to work *)
consts tyname :: "'a itself \<Rightarrow> char list"

definition tyn_unit :: "unit itself \<Rightarrow> char list" where
"tyn_unit _ = ''UNIT''"

definition tyn_nat :: "nat itself \<Rightarrow> char list" where
"tyn_nat _ = ''NAT''"

value [nbe] "tyname (TYPE (nat))"

text_raw \<open>%EndSnippet\<close>

definition tyn_noname :: "('a :: noname) itself \<Rightarrow> char list" where
"tyn_noname _ = ''UHOH''"

definition tyn_noname_bad :: "'a itself \<Rightarrow> char list" where
"tyn_noname_bad _ = ''UHOH''"


definition tyn_option_bad ::
  "('a option itself \<Rightarrow> char list)" where
"tyn_option_bad _ =
  (tyname (TYPE('a))) @ '' OPTION''"

definition tyn_option ::
  "('a itself \<Rightarrow> char list) \<Rightarrow> ('a option itself \<Rightarrow> char list)" where
"tyn_option t _ =
  (t (TYPE( 'a))) @ '' OPTION''"


adhoc_overloading tyname
  tyn_unit
  tyn_nat
  (*tyn_option_bad*)
  (*tyn_noname_bad*)
  tyn_noname
 "tyn_option tyname"


value [nbe] "tyname (TYPE (nat))"
value [nbe] "tyname (TYPE (unit option option))"
value [nbe] "tyname(TYPE (bool option))"

end