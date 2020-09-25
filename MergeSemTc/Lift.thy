theory Lift imports Compose "../MergeableTc/MergeableInstances" "../MergeableTc/SplittableInstances" HOL.Lifting HOL.Lifting_Set

begin

datatype calc =
  Cadd int
  | Csub int
  | Cmul int
  | Cdiv int
  | Creset int

(*
datatype calc_st = CSi int
*)
definition calc_sem :: "calc \<Rightarrow> int \<Rightarrow> int" where
"calc_sem syn st = 
  (case syn of
     (Cadd i) \<Rightarrow> st + i
    |(Csub i) \<Rightarrow> st - i
    |(Cmul i) \<Rightarrow> st * i
    |(Cdiv i) \<Rightarrow> divide_int_inst.divide_int st i)"

type_synonym ('a, 'b, 'c, 'd) synlift =
  "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'd \<Rightarrow> ('b \<Rightarrow> 'c)" 

definition syn_lift_triv :: "('a, 'b, 'c, 'a md_triv) synlift" where
"syn_lift_triv = case_md_triv"

(* here we are assuming no syntax = no-op
   another option would be to return \<bottom> (b, c different; c being a Pordb) *)
(*
definition syn_lift_option :: "('a, 'b, 'b, 'a option) synlift" where
"syn_lift_option =
  case_option id"
*)
type_synonym ('a, 'b, 'c, 'd) semlift =
  "('a \<Rightarrow> 'b) \<Rightarrow> ('c \<Rightarrow> 'd)"
                              
definition sem_lift_triv :: "('a, 'b, 'a md_triv, 'b md_triv) semlift" where
"sem_lift_triv = map_md_triv"

definition sem_lift_option :: "('a, 'b, 'c, 'd) semlift \<Rightarrow> ('a, 'b, 'c option, 'd option) semlift" where
"sem_lift_option l = map_option o l"

definition sem_lift_prio_keep :: "('a, 'b, 'c, 'd) semlift \<Rightarrow> ('a, 'b, 'c md_prio, 'd md_prio) semlift" where
"sem_lift_prio_keep l = map_md_prio o l"

definition prio_inc :: "'a md_prio \<Rightarrow> 'a md_prio" where
"prio_inc = case_md_prio (\<lambda> n x . mdp (1 + n) x)"

definition sem_lift_prio_inc :: "('a, 'b, 'c, 'd) semlift \<Rightarrow> ('a, 'b, 'c md_prio, 'd md_prio) semlift" where
"sem_lift_prio_inc l f = (prio_inc o sem_lift_prio_keep l f)"

(* idea: uncurry *)

(*
definition sem_lift_fst ::
  "('a1, 'b1, 'c1, 'd1) semlift \<Rightarrow>
   ('a1 * 'a2, 'b1 * 'b2, 'c1 * 'c2, 'd1 * 'd2) semlift" where
"sem_lift_fst l f x =
  (case x of
    (c1, c2) \<Rightarrow>
      l1 (\<lambda> a1 . _) c1)"
*)
(*
definition sem_lift_prod ::
  "('a1, 'b1, 'c1, 'd1) semlift \<Rightarrow>
   ('a2, 'b1 * 'b2, 'c2, 'd1) semlift \<Rightarrow>
   ('a1 * 'a2, 'b1 * 'b2, 'c1 * 'c2, 'd1 * 'd2) semlift" where
"sem_lift_prod l1 l2 f x =
  (case x of
    (c1, c2) \<Rightarrow>
      l1 (\<lambda> a1 . (l2 (\<lambda> a2 . f (a1, a2)) c2)) c1)"
*)