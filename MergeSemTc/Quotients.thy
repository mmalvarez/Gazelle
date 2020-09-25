theory Quotients imports Main "../MergeableTc/MergeableInstances" HOL.Lifting 

begin

datatype 'a bloo =
  Bloo 'a

definition oprj :: "'a option \<Rightarrow> 'a " where
"oprj x = (case x of Some x' \<Rightarrow> x')"
term "Some"


lemma type_definition_bloo :
  "type_definition (case_bloo id) Bloo  UNIV"
  apply(rule type_definition.intro)
    apply(auto  split:bloo.splits)
  done

setup_lifting type_definition_bloo

datatype calc =
  Cadd int
  | Csub int
  | Cmul int
  | Cdiv int
  | Creset int

definition calc_sem :: "calc \<Rightarrow> int \<Rightarrow> int" where
"calc_sem syn st = 
  (case syn of
     (Cadd i) \<Rightarrow> st + i
    |(Csub i) \<Rightarrow> st - i
    |(Cmul i) \<Rightarrow> st * i
    |(Cdiv i) \<Rightarrow> divide_int_inst.divide_int st i)"

(*
lemma prio_triv_Q :
  "Quotient (\<lambda> (a :: int md_triv) b . 
                    (case (a, b) of
                         (mdt a', mdt b') \<Rightarrow> a' = b'))
                (\<lambda> x . case (x) of (mdt x') \<Rightarrow> x')
                (\<lambda> x . mdt  x)
                (\<lambda> x x' . (case x of mdt x'' \<Rightarrow> x' = x''))"
  apply(rule QuotientI)
     apply(auto  split:md_triv.splits)
  done
*)


typedef 'a triv' = "UNIV :: 'a set" by auto

lemma triv_Q :
  "Quotient (\<lambda> (a :: 'a md_triv) b . 
                    (case (a, b) of
                         (mdt a', mdt b') \<Rightarrow> a' = b'))
                (\<lambda> x . case (x) of (mdt x') \<Rightarrow> x')
                mdt
                (\<lambda> x x' . (case x of mdt x'' \<Rightarrow> x' = x''))"
  apply(rule QuotientI)
     apply(auto  split:md_triv.splits)
  done


setup_lifting prod.type_definition_prod

setup_lifting type_definition_triv'


definition wow :: int where
"wow = 0"



typedef 'a myopt = "UNIV :: ('a + unit) set"
  apply(auto)
  done

typedef 'a myopt2 = "UNIV :: 'a option set" by auto 

term "case_option (Abs_myopt (Inr ())) (Abs_myopt o Inl)"
term "(case_sum (Some) (\<lambda> _ . None)) o Rep_myopt"


lemma type_definition_myopt' :
  "type_definition (case_option (Abs_myopt (Inr ())) (Abs_myopt o Inl)) 
                   ((case_sum (Some) (\<lambda> _ . None)) o Rep_myopt) UNIV"
  apply(rule type_definition.intro)
    apply(simp split:option.splits sum.splits)
   apply(auto split:option.splits sum.splits simp add: Abs_myopt_inverse)

   apply(drule_tac f = Abs_myopt in arg_cong)
   apply(simp add:Rep_myopt_inverse)
   apply(drule_tac f = Abs_myopt in arg_cong)
  apply(simp add:Rep_myopt_inverse)

  done

setup_lifting type_definition_myopt

(*
lemma type_definition_opt :
  "type_definition (case_option undefined id) Some (UNIV)"
  apply(rule type_definition.intro)
  apply(auto)
  sorry
*)

lemma type_definition_opt3 :
  "type_definition (Some :: 'a bloo \<Rightarrow> 'a bloo option) (case_option undefined id)  (Some ` UNIV)"
  apply(rule type_definition.intro)
  apply(auto)
  done

setup_lifting type_definition_opt3

lift_definition wow' :: "int bloo option" is wow

end