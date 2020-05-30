theory MergeableTests imports Mergeable
begin

fun test0_lleq :: "nat option \<Rightarrow> nat option \<Rightarrow> bool" where
"test0_lleq None _ = True"
| "test0_lleq x y = (x = y)"

fun test0_aug_lleq :: "nat option \<Rightarrow> nat option \<Rightarrow> bool" where
"test0_aug_lleq None _ = True"
| "test0_aug_lleq x y = (x = y)"

fun test0_bsup :: "nat option \<Rightarrow> nat option \<Rightarrow> nat option" where
"test0_bsup None r = r"
| "test0_bsup l r = l"
  

value "test0_bsup None (Some 2)"
value "test0_bsup (Some 2) (None)"
term "Mergeable_Spec"



interpretation Test0 : Mergeable_Spec test0_lleq test0_bsup
  apply(unfold_locales)
     apply(case_tac a; clarsimp) 
    apply(case_tac a; clarsimp)
   apply(case_tac a; clarsimp)
              apply(case_tac b; clarsimp)

(* completeness *)

        apply(simp add:Pord.has_ub_def Pord.is_ub_def
Pord.has_sup_def Pord.is_sup_def Pord.is_least_def)

     apply(case_tac a; clarsimp) 
    apply(case_tac b; clarsimp)
        apply(rule_tac x = None in exI)
        apply(simp add:All_def)
  apply(rule_tac ext; auto)


(* end completeness *)

     apply(case_tac a; clarsimp) 
    apply(case_tac a; clarsimp)
   apply(case_tac a; clarsimp)
  apply(auto)

apply(simp add:Aug_Pord.l_pleq_def)
  apply(simp add:Aug_Pord.l_pleq_def)

  apply(simp add: Aug_Pord.is_bsup_def Aug_Pord.is_bub_def Pord.is_least_def Pord.is_sup_def Pord.is_ub_def)
  
  apply(auto)
apply(simp add:Aug_Pord.l_pleq_def)
    apply(case_tac a; clarsimp)

   apply(case_tac a; clarsimp) 

   apply(case_tac a; clarsimp) 

  apply(case_tac b; clarsimp)
  apply(drule_tac x = "Some a" in spec) apply(auto)
apply(simp add:Aug_Pord.l_pleq_def)
  done


type_synonym t1 = "nat option * nat"

type_synonym t1a = "nat option * nat option"

(*
definition test_lleq :: "t1 \<Rightarrow> t1 \<Rightarrow> bool" where 
"test_lleq l r =    (case (l, r) of
         ((None, l2), (None, r2)) \<Rightarrow> l2 = r2
       | ((None, l2), (Some r1, r2)) \<Rightarrow> l2 = r2
       | ((Some _, _), (None, _)) \<Rightarrow> False
       | ((Some l1, l2 ), (Some r1, r2)) \<Rightarrow> l1 = r1 \<and> l2 = r2)"
*)

definition test_lleq :: "t1a \<Rightarrow> t1a \<Rightarrow> bool" where 
"test_lleq l r = 
   (case (l, r) of
         ((None, None), (_, _)) \<Rightarrow> True
         | ((None, Some x2), (_, Some y2)) \<Rightarrow> x2 = y2
         | ((Some x1, None), (Some y1, _)) \<Rightarrow> x1 = y1
         | ((Some x1, Some x2), (Some y1, Some y2)) \<Rightarrow> x1 = y1 \<and> x2 = y2
         | (_, _) \<Rightarrow> False)"

definition test_bsup :: "t1 \<Rightarrow> t1 \<Rightarrow> t1" where
"test_bsup = (\<lambda> l r .
    (case (l, r) of
            ((None, l2), (None, r2)) \<Rightarrow> (None, l2)
            |((None, l2), (Some r1, r2)) \<Rightarrow> (Some r1, l2)
            |((Some l1, l2), (None, r2)) \<Rightarrow> (Some l1, l2)
            |((Some l1, l2), (Some r1, r2)) \<Rightarrow> (Some l1, l2)))"

definition test_aug :: "t1 \<Rightarrow> t1a" where
"test_aug t =
  (case t of
    (x1, x2) \<Rightarrow> (x1, Some x2))"

definition test_deaug :: "t1a \<Rightarrow> t1 option" where
"test_deaug ta =
  (case ta of
    (x1, Some x2) \<Rightarrow> Some (x1, x2)
    | _ \<Rightarrow> None)"


interpretation Test : Aug_Mergeable_Spec test_lleq test_aug test_deaug test_bsup

  apply(unfold_locales)
              apply(simp add: test_lleq_def split:prod.splits option.splits)
  apply(simp add: test_lleq_def split:prod.splits option.splits)
         apply(simp add: test_lleq_def split:prod.splits option.splits)

(* completeness *)

        apply(simp add:Pord.has_ub_def Pord.is_ub_def
Pord.has_sup_def Pord.is_sup_def Pord.is_least_def)

        apply(clarsimp)
        apply(simp add:test_lleq_def)
        apply(simp split:option.splits; (clarsimp; force))

(* end completeness *)

       apply(simp add: test_deaug_def test_aug_def test_lleq_def split:prod.splits option.splits)
      apply(simp add: test_deaug_def test_aug_def test_lleq_def split:prod.splits option.splits)
       apply(clarsimp)

      apply(simp add: Aug_Pord.l_pleq_def test_lleq_def test_aug_def test_deaug_def split:prod.splits option.splits)
      apply(simp add: Aug_Pord.l_pleq_def test_lleq_def test_aug_def test_deaug_def split:prod.splits option.splits)
     apply(clarsimp) apply(fastforce)
      apply(simp add: Aug_Pord.l_pleq_def test_lleq_def test_aug_def test_deaug_def split:prod.splits option.splits)

  apply(simp add: Aug_Pord.l_pleq_def Aug_Pord.is_bsup_def Aug_Pord.is_bub_def Pord.is_least_def Pord.is_sup_def Pord.is_ub_def)
  apply(simp add: test_deaug_def test_aug_def test_lleq_def test_bsup_def)


  apply(case_tac a; clarsimp)
  apply(case_tac aaa; clarsimp)
   apply(case_tac aa; clarsimp)
  apply(case_tac a; clarsimp)
    apply(case_tac b; clarsimp)
      apply(case_tac bb; clarsimp)
      apply(case_tac ab; clarsimp) 
       apply(drule_tac x = None in spec) apply(drule_tac x = "Some a" in spec)
        apply(clarsimp)

  apply(case_tac bb; clarsimp)
       apply(case_tac ab; clarsimp) 

       apply(drule_tac x = None in spec) apply(drule_tac x = "Some a" in spec)
        apply(clarsimp)

  apply(case_tac bb; clarsimp)
       apply(case_tac ab; clarsimp) 
    apply(case_tac b; clarsimp)

   apply(rule_tac conjI)

  apply(clarsimp)
    apply(case_tac ab; clarsimp)
    apply(case_tac aa; clarsimp)

    apply(case_tac b; clarsimp)
       apply(case_tac bb; clarsimp)
      apply(case_tac bb; clarsimp)
     apply(case_tac bb; clarsimp)
    apply(case_tac aa; clarsimp)
     apply(case_tac bb; clarsimp)
    apply(case_tac b; clarsimp)

       apply(drule_tac x = "None"  in spec) apply(drule_tac x = "Some aa" in spec)
        apply(clarsimp)
  
       apply(drule_tac x = "None"  in spec) apply(drule_tac x = "Some aa" in spec)
       apply(clarsimp)

      apply(case_tac b; clarsimp)
     apply(case_tac bb; clarsimp)
    apply(case_tac bb; clarsimp)

  apply(clarsimp)
  apply(simp cong:option.case_cong)
  apply(case_tac aa; clarsimp)
  apply(simp cong:option.case_cong)

       apply(drule_tac x = "Some a" in spec) apply(clarsimp)
       apply(drule_tac x = "None" in spec)
       apply(clarsimp)

       apply(drule_tac x = "Some a" in spec) apply(drule_tac x = "Some baa" in spec)
      apply(clarsimp)
    apply(case_tac b; clarsimp) apply(case_tac a; clarsimp)
     apply(case_tac aa; clarsimp)
apply(case_tac aa; clarsimp)

       apply(drule_tac x = "Some a" in spec) apply(clarsimp)
       apply(drule_tac x = "None" in spec)
   apply(clarsimp)

  apply(simp split:option.splits) apply(clarsimp)


  apply(case_tac aa; clarsimp)
   apply(case_tac ab; clarsimp)
   apply(case_tac b; clarsimp)
   apply(case_tac ac; clarsimp)
     apply(simp  split:option.splits)

   apply(case_tac ac; clarsimp)
    apply(simp  split:option.splits)


   apply(case_tac ac; clarsimp)
   apply(simp  split:option.splits)

   apply(case_tac b; clarsimp)
   apply(case_tac ac; clarsimp)
apply(case_tac ad; clarsimp)
    apply(simp  split:option.splits)
apply(case_tac ad; clarsimp)
  apply(simp  split:option.splits)

   apply(case_tac ac; clarsimp)
apply(case_tac ad; clarsimp)
    apply(simp  split:option.splits)
apply(case_tac ad; clarsimp)
  apply(simp  split:option.splits)

  done
(* ok, so this seems to work - but is rather ugly. *)


end