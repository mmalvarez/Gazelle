theory Prod_Merge imports "Lens"

begin

record ('s1, 's2, 'c) prod_merge_parms =
  lens1 :: "('s1, 'c) lens_parms"
  lens2 :: "('s2, 'c) lens_parms"

locale Prod_Merge' =
  fixes Prod_Merge_Parms :: "('a, 'b, 'c) prod_merge_parms" 

locale Prod_Merge = Prod_Merge' +
  L1 : Lens "prod_merge_parms.lens1 Prod_Merge_Parms" +
  L2 : Lens "prod_merge_parms.lens2 Prod_Merge_Parms"
begin

print_context

definition upd1 :: "('a * 'c \<Rightarrow> 'c)" where
"upd1 = L1.upd"

definition upd2 :: "('b * 'c \<Rightarrow> 'c)" where
"upd2 = L2.upd"

definition proj1 :: "('c \<Rightarrow> 'a)" where
"proj1 = L1.proj"

definition proj2 :: "('c \<Rightarrow> 'b)" where
"proj2 = L2.proj"

(*
definition lift1p :: "('a \<Rightarrow> 'x) \<Rightarrow> ('c \<Rightarrow> 'x)" where
"lift1p = L1.liftp"

definition lift2p :: "('b \<Rightarrow> 'x) \<Rightarrow> ('c \<Rightarrow> 'x)" where
"lift2p = L2.liftp"

definition lower1p :: "('a \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'm1)" where
"lower1p f x = proj1 (f x)"

definition lower2p :: "('a \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'm2)" where
"lower2p f x = proj2 (f x)"

(* these are not fully concrete *)
(* also i am not fully convinced these definitions
are dual *)
definition lift1s :: "('a \<Rightarrow> 'm1) \<Rightarrow> ('a \<Rightarrow> 'c)" where
"lift1s f x =
  upd1 (SOME x' . fst x' = f x)"

definition lift2s :: "('a \<Rightarrow> 'm2) \<Rightarrow> ('a \<Rightarrow> 'c)" where
"lift2s f x =
  upd2 (SOME x' . fst x' = f x)"

definition lower1s :: "('c \<Rightarrow> 'a) \<Rightarrow> ('m1 \<Rightarrow> 'a)" where
"lower1s f x =
  f (upd1 (SOME x' . fst x' = x ))"

definition lower2s :: "('c \<Rightarrow> 'a) \<Rightarrow> ('m2 \<Rightarrow> 'a)" where
"lower2s f x =
  f (upd2 (SOME x' . fst x' = x ))"
*)
end

locale Prod_Merge_Spec = Prod_Merge +
  SL1 : Lens_Spec "
  assumes Hprod1 : "\<And> m1c . proj1 (upd1 m1c) = fst m1c"
  assumes Hprod2 : "\<And> m2c . proj2 (upd2 m2c) = fst m2c"
  assumes Hupd12 : "\<And> (c :: 'b) (c' :: 'b) .
    upd1 (pmap2 (id, upd2) (pmap3 (proj1, proj2, (const c')) (pfan3 c))) = c"
assumes Hupd21 : "\<And> (c :: 'b) (c' :: 'b) .
    upd2 (pmap2 (id, upd1) (pcomm3_1_2 (pmap3 (proj1, proj2, (const c')) (pfan3 c)))) = c"

begin

lemma putGet1 :
  fixes c
  shows "upd1 (pmap2 (proj1, id) (pfan2 c)) = c"
  apply(simp)
  apply(insert Hupd12[of _ c]) 
  apply(insert Hupd21[of _ c])
  apply(simp)
  apply(drule_tac allI)
  apply(drule_tac x = "upd1 (proj1 c, c)" in spec)
  apply(simp)
  done

lemma putGet2 :
  fixes c
  shows "upd2 (pmap2 (proj2, id) (pfan2 c)) = c"
  sorry

(*
lemma updCong2 :
  "upd2 (proj2 (upd1 (m1, upd1 (m1', mc))), mc) = upd2 (proj2 (upd1 (m1, mc)), mc)
*)
lemma total :
  fixes c1 c2
  shows "proj1 c1 = proj1 c2 \<Longrightarrow> proj2 c1 = proj2 c2 \<Longrightarrow> c1 = c2" 

  apply(insert Hupd21[of _ c1]) apply(simp)
  apply(insert Hupd12[of _ c2]) apply(simp)
  apply(subgoal_tac "? cx . upd1 (proj1 c2, upd2 (proj2 c2, cx)) = c2") apply(clarify)
   apply(drule_tac allI) apply(drule_tac x = " upd2 (proj2 c2, cx)" in spec)
   apply(simp add:Hprod1 Hprod2)
  apply(insert putGet2) apply(simp)

  apply(auto)
  done

lemma total'1 :
  shows "upd1 (c1, c1') = upd1 (c2, c2') \<Longrightarrow>
         c1 = c2"
  sorry

lemma total'2 :
  shows "upd2 (c1, c1') = upd2 (c2, c2') \<Longrightarrow>
         c1 = c2"
  sorry

lemma putTwice1 :
  shows "upd1 (m1, upd1 (m1, c)) = upd1 (m1, c)"
  sorry

lemma putTwice2 :
  shows "upd2 (m2, upd2 (m2, c)) = upd2 (m2, c)"
  sorry

print_context

definition m1u :: "'b \<Rightarrow> 'a set" where
"m1u c = { (m1 :: 'a) . (\<exists> m2 . proj1 (upd2 (m2, c)) = m1) }"

definition m2u :: "'b \<Rightarrow> 'c set" where
"m2u c = { (m2 :: 'c) . (\<exists> m1 . proj2 (upd1 (m1, c)) = m2) }"

lemma m2u_spec :
  shows "m2u c = m2u c' \<Longrightarrow> upd2 (proj2 c, cx) = upd2 (proj2 c', cx)"
  apply(simp add:m2u_def)
  apply(frule_tac x = "proj2 c" in Set.eqset_imp_iff)
  apply(drule_tac x = "proj2 c'" in Set.eqset_imp_iff) apply(clarsimp)

  apply(case_tac " (\<exists>m1. proj2 (upd1 (m1, c)) = proj2 c)")
  apply(case_tac "(\<exists>m1. proj2 (upd1 (m1, c)) = proj2 c')")
   apply(clarsimp) 

lemma putPut1 :
  fixes m1 m1' mc
  shows "upd1 (pmap2 (id, upd1) (m1, m1', mc)) = upd1 (m1, mc)"

  apply(simp)
(*  apply(insert Hupd12 [of _ "upd1 (m1', mc)"]) *)
(* apply(insert Hupd12 [of _ "mc"])
  apply(simp)   apply(simp add:Hprod1)
*)

  apply(rule_tac total)
   apply(simp add: Hprod1)

  apply(subgoal_tac "? huh2 . (upd1 (m1', mc)) = upd2 huh2")
   apply(subgoal_tac "? huh1 . (upd1 (m1, mc) = upd2 huh1)")
    apply(clarsimp) apply(simp add:Hprod2)

      apply(drule_tac f = proj1 in arg_cong) apply(simp add:Hprod1)
    apply(drule_tac f = proj2 in arg_cong) apply(simp add:Hprod2)

    apply(insert Hupd12[of mc "upd1 (m1', mc)"] )
    apply(simp add: Hprod1 Hprod2)
    apply(insert Hupd21 ) apply(simp)
  apply(rule_tac total'2) apply(simp)
  apply(drule_tac allI)
apply(insert Hupd21 ) apply(simp)


  apply(drule_tac 

  apply(subgoal_tac

  apply(insert Hupd21[of "upd1 (m1', mc)"  "upd1 (m1, mc)"]) apply(simp) apply(simp add:Hprod1 Hprod2)
      apply(drule_tac f = proj1 in arg_cong) apply(simp add:Hprod1)

  apply(insert Hupd12[of mc "upd2 (proj2 (upd1 (m1, mc)), upd1 (m1, upd1 (m1', mc)))"]) apply(simp add:Hprod2)
  apply(drule_tac f = proj2 in arg_cong) apply(simp add:Hprod2)

  apply(insert Hupd12[of "upd1 (m1', mc)"  "upd1 (m1, mc)"]) apply(simp add:Hprod1 Hprod2)


apply(insert Hupd21[of mc  "upd1 (m1, mc)"]) apply(simp add:Hprod1 Hprod2)
  apply(insert Hupd12[of mc "upd1 (m1, mc)"]) apply(simp add:Hprod1 Hprod2)
(*apply(insert Hupd21[of "upd1 (m1', mc)"  "upd1 (m1, mc)"]) apply(simp add:Hprod1 Hprod2)*)
  apply(insert Hupd12[of "upd1 (m1', mc)" "upd1 (m1, mc)"]) apply(simp add:Hprod1 Hprod2)

(**)
apply(insert Hupd21) apply(simp)
  apply(insert Hupd12) apply(simp)

(*
*)


  apply(rule_tac c2' = "upd1 (m1, mc)" and c1' = "upd1 (m1, mc)" in total'2)



  apply(rule_tac total)
  defer
   apply(simp add: Hprod2)


  apply(insert Hupd21[of mc "upd1 (m1, upd1 (m1', mc))"]) apply(simp)
apply(simp add:Hprod1 Hprod2)
apply(insert Hupd12[of mc "upd1 (m1', mc)"]) apply(simp)
apply(insert Hupd21) apply(simp)

  apply(insert Hupd12[of _ "upd1 (m1, mc)"]) apply(simp) apply(simp add:Hprod1 Hprod2)
  apply(insert Hupd21[of mc "upd1 (m1, upd1 (m1', mc))"]) apply(simp)
  apply(simp add:Hprod1 Hprod2)

  apply(insert Hupd21) apply(simp)

apply(insert Hupd12[of mc "upd1 (m1, upd1 (m1', mc))"]) apply(simp) apply(simp add:Hprod1 Hprod2)

  apply(insert Hupd21[of mc "upd1 (m1, mc)"]) apply(simp) apply(simp add:Hprod1 Hprod2)
  apply(insert Hupd21[of mc "upd1 (m1, upd1 (m1', mc))"]) apply(simp) apply(simp add:Hprod1 Hprod2)


  apply(subgoal_tac "? huh2 . (upd1 (m1, upd1 (m1', mc))) = upd2 huh2")
  apply(subgoal_tac "? huh1 . (upd1 (m1, mc) = upd2 huh1)")

    apply(clarsimp)
    apply(simp add:Hprod2)
    apply(drule_tac f = proj1 in arg_cong) apply(simp add:Hprod1)
apply(drule_tac f = proj2 in arg_cong) apply(simp add:Hprod2)

  apply(insert Hupd12) apply(insert Hupd21[of _ "upd1 (m1, mc)"]) apply(simp add: Hprod1 Hprod2)

    apply(frule_tac f = proj1 in arg_cong) apply(simp add:Hprod1)
apply(frule_tac f = proj2 in arg_cong) apply(simp add:Hprod1)

  apply(insert putGet2) apply(simp)

  apply(insert Hupd21[of mc "upd1 (m1, upd1 (m1', mc))"]) apply(simp add:Hprod1)

  apply(insert Hupd12) apply(insert Hupd21) apply(simp)


  apply(insert Hupd21[of mc "upd1 (m1, upd1 (m1', mc))"]) apply(simp add:Hprod1)
  apply(insert putGet2[of "(upd1 (m1, upd1 (m1', mc)))"]) apply(simp)

  apply(insert Hupd12) apply(insert Hupd21) apply(simp)

  apply(insert Hupd12[of mc "upd1 (m1, mc)"]) apply(simp add: Hprod1) 
  
  apply(insert Hupd21[of mc "upd1 (m1, upd1 (m1', mc))"]) apply(simp add:Hprod1)

  apply(subgoal_tac
" proj2 ( upd2 (proj2 (upd1 (m1, upd1 (m1', mc))), upd1 (m1, mc))) = proj2 (upd1 (m1, upd2 (proj2 (upd1 (m1, mc)), mc)))")
   apply(simp)
  apply(simp add:Hprod2)

  apply(subgoal_tac 
"proj2 ( upd2 (proj2 (upd1 (m1, upd1 (m1', mc))), upd1 (m1, mc))) = proj2 (upd1 (m1, mc))") apply(simp)
  apply(simp add:Hprod2)
(*[of mc " (upd1 (m1, upd1 (m1', mc)))"]) apply(simp) *)
  apply(simp add:Hprod1)

(* i think we need to generalize this somehow *)


  apply(subgoal_tac "? mcx . upd2 (proj2 (upd1 (m1, upd1 (m1', mc))), mcx) = upd2 (proj2 (upd1 (m1, mc)), mcx)")

(*
  apply(subgoal_tac 
"proj2 (upd1 (m1, upd1 (m1', mc))) = proj2 ( upd2 (proj2 (upd1 (m1, mc)), upd1 (m1, upd1 (m1', mc))))")
   apply(simp add:Hprod2)
  apply(simp add:Hprod2)
     apply(drule_tac f = proj2 in arg_cong) apply(simp add:Hprod2)

  apply(insert Hupd12) apply(insert Hupd21) apply(simp)

*)
  apply(clarsimp)

  apply(insert Hupd21[of mc "(upd1 (m1, (upd1 (m1', mc))))"]) apply(simp)
  apply(simp add: Hprod1)
   apply(drule_tac f = proj2 in arg_cong) apply(simp add:Hprod2)

  apply(thin_tac "upd2
     (pmap2 (id, upd1)
       (pcomm3_1_2
         (pmap3 (proj1, proj2, const mc)
           (pfan3 (upd1 (m1, upd1 (m1', mc))))))) =
    upd1 (m1, upd1 (m1', mc))")
(*
  apply(insert Hupd12[of "upd1 (m1', mc)" "upd1 (m1, mc)"]) apply(simp) apply(simp add:Hprod1) *)

  apply(rule_tac x = "upd2 (proj2 (upd1 (m1, mc)), mc)" in exI) apply(simp)
   apply(rule_tac total)
   defer
  apply(simp add:Hprod2)

   apply(insert Hupd21[of mc "(upd1 (m1, mc))"]) apply(simp add:Hprod1)
  apply(subgoal_tac 
"proj2 (upd1 (m1, upd1 (m1', mc))) = proj2 (upd2 (proj2 (upd1 (m1, mc)), upd1 (m1, mc)))")
    apply(simp add:Hprod2)
apply(simp add:Hprod2)
   apply(drule_tac f = proj1 in arg_cong) apply(simp add:Hprod1)

  apply(insert Hupd12) apply(simp)
  apply(rule_tac x = "upd1 (m1, mc)" in exI) apply(simp)
  apply(insert Hupd21[of "mc" "upd1 (m1, mc)"]) apply(simp) apply(simp add:Hprod1)
  apply(subgoal_tac " ? mcx . upd2 (proj2 (upd1 (m1, upd1 (m1', mc))), mcx) =
                              upd2 (proj2 (upd2 (proj2 (upd1 (m1, mc)), upd1 (m1, mc))), mcx)")
   apply(clarsimp)

  apply(simp add:Hprod2)


  apply(insert Hupd21[of "upd1 (m1', mc)" "upd1 (m1, mc)"]) apply(simp) apply(simp add:Hprod1)
  apply(rule_tac x = " upd1 (m1', mc)" in exI)
  
  apply(subgoal_tac
"upd2 (proj2 (upd1 (m1, upd1 (m1', mc))), mc) =
    upd2 (proj2 (upd2 (proj2 (upd1 (m1, mc)), upd1 (m1, upd1 (m1', mc)))), mc)")
   apply(simp add:Hprod2)
  apply(simp)
  apply(drule_tac allI) apply(drule_tac spec) apply(clarsimp)

   apply(drule_tac f = proj2 in arg_cong) apply(simp add:Hprod2)

(*
  apply(insert Hupd12) apply(insert Hupd21) apply(simp)
*)
(*  apply(insert Hupd12[of _ "(upd1 (m1, (upd1 (m1', mc))))"]) apply(simp) *)
apply(insert Hupd12[of _ "(upd1 (m1', mc))"])
  apply(simp add: Hprod1)
  apply(drule_tac allI) apply(drule_tac x = mc in spec) apply(drule_tac f = proj1 in arg_cong) apply(simp add:Hprod1)
    

(*  apply(insert Hupd12[of _ "(upd1 (m1, upd1 (m1', mc)))"] ) *)
  apply(insert Hupd12[of _ "(m1, upd1 (m1', mc))"]) apply(simp)
  apply(simp)
  apply(drule_tac allI)
  apply(simp add:Hprod1)

  apply(insert Hupd12 [of  ])
  apply(simp)   apply(simp add:Hprod1)


apply(insert Hupd21 [of  _ "upd1 (m1', mc)"])
  apply(simp)   
  apply(simp add:Hprod1)

  apply(insert Hupd12 [of _ "]) apply(simp)
  apply(simp add:Hprod1)
  apply(rotate_tac -1)
  apply(drule_tac allI)
  apply(drule_tac x = " upd1 (m1, upd1 (m1', mc))" in spec)
  apply(simp)

  apply(simp add:Hprod2)
(* idea: subgoal, manufacture an appropriate c', then plug second eqn into first *)
  apply(subgoal_tac "? c' . upd2 (proj2 (upd1 (m1', mc)), upd1 (m1', c')) =
           upd1 (m1', mc)")
  apply(clarify)
   apply(rotate_tac -1) apply(drule_tac allI)
  apply(drule_tac x = c' in spec) apply(clarsimp)
  
  apply(insert Hupd12 [of _ "mc"]) 
  apply(simp add:Hprod1)
    apply(drule_tac allI)

  apply(insert Hupd12 [of _ "upd1 (m1, mc)"])
  apply(simp)  apply(simp add:Hprod1)
  apply(drule_tac allI)
  apply(rotate_tac -1)
  apply(drule_tac x = "upd1 (m1, upd1 (m1', mc))" in spec)
  apply (simp)

end