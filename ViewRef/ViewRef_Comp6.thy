theory ViewRef_Comp5 imports ViewRef5

begin

(* vertical composition of view refs *)

record ('d, 'r1, 'r2) view_ref_comp_parms =
  v1 :: "('d, 'r1) view_ref_parms"
  v2 :: "('r1, 'r2) view_ref_parms"

declare view_ref_comp_parms.defs[simp]

locale View_Comp'  =
  fixes View_Comp_parms :: "('d, 'r1, 'r2) view_ref_comp_parms"

locale View_Comp_Spec = View_Comp' +
  V1 : View_Ref_Spec "v1 View_Comp_parms" +
  V2 : View_Ref_Spec "v2 View_Comp_parms" +
  assumes Hagree : "V1.refnr = V2.refnd"

begin


(* change this?
i think we need to be updating r2 even in the non projectable case (?)
*)
(*
fun inj' :: "('a * 'c) \<Rightarrow> 'c" where
  "inj' (d, r2) =
    (case V2.prj r2 of
      Inl r1 \<Rightarrow> (case V1.prj (V1.inj (d, r1)) of
          Inl _ \<Rightarrow> V2.inj (V1.inj (d, r1), r2)
          | Inr _ \<Rightarrow> r2)
      | Inr r2 \<Rightarrow> r2)"
*)

fun inj' :: "('a * 'c) \<Rightarrow> 'c" where
  "inj' (d, r2) =
    (case V2.prj r2 of
      Inl r1 \<Rightarrow> (case V1.prj r1 of
          Inl _ \<Rightarrow> V2.inj (V1.inj (d, r1), r2)
          | Inr _ \<Rightarrow> r2)
      | Inr r2 \<Rightarrow> r2)"

(* huh, maybe this is wrong?

*)
fun prj' :: "'c \<Rightarrow> ('a + 'c)" where
  "prj' r2 =
    (case V2.prj r2 of
      Inl r1 \<Rightarrow> (case V1.prj r1 of
        Inl d \<Rightarrow> Inl d
        | Inr r1 \<Rightarrow> Inr r2)
      | Inr r2 \<Rightarrow> Inr r2)"    

abbreviation vp :: "('a, 'c) view_ref_parms" where
"vp \<equiv> \<lparr> inj = inj', prj = prj', refnd = (V1.refnd), refnr = (V2.refnr) \<rparr>"

lemma HagreeL : "\<And> a b . V1.refnr a b \<Longrightarrow> V2.refnd a b"
  apply(simp add:Hagree)
  done

lemma HagreeR : "\<And> a b . V2.refnd a b \<Longrightarrow> V1.refnr a b"
  apply(simp add:Hagree)
  done

end

sublocale View_Comp_Spec \<subseteq> View_Ref_Spec vp
  apply(unfold_locales)
(* 
  ordering correctness
*)
  apply(simp add:V1.DO.leq_refl)
             apply(simp add:V1.DO.leq_trans)
apply(simp add:V1.DO.leq_antisym)
           apply(simp add:V2.RO.leq_refl)
  apply(simp)
             apply(drule_tac V2.RO.leq_trans) apply(simp) apply(simp)
         apply(simp add:V2.RO.leq_antisym)

(*
  RefnInjD
*)
        apply(clarsimp)
  apply(simp split:sum.splits) apply(safe)
          apply(drule_tac r = x1 in V1.RefnInjD)
  apply(simp add:Hagree)

           apply(drule_tac r = r in V2.RefnInjD)
              apply(simp)
           apply(rule_tac V2.RO.leq_refl)
           apply(rule_tac V2.RO.leq_refl)


(* 
  RefnPrj1
*)
       apply(simp split:sum.splits) apply(safe)
         apply(drule_tac V2.RefnPrj1) apply(simp) apply(clarsimp)
         apply(drule_tac HagreeR)
         apply(drule_tac V1.RefnPrj1) apply(simp) apply(clarsimp)

         apply(drule_tac V2.RefnPrj1) apply(simp) apply(clarsimp)
         apply(drule_tac HagreeR)
        apply(drule_tac V1.RefnPrj2) apply(simp) apply(clarsimp)
       apply(drule_tac V2.RefnPrj2) apply(simp) apply(clarsimp)

(*
  RefnPrj2
*)
       apply(simp split:sum.splits) apply(safe)
         apply(drule_tac V2.RefnPrj1) apply(simp) apply(clarsimp)
         apply(drule_tac HagreeR)
         apply(drule_tac V1.RefnPrj1) apply(simp) apply(clarsimp)
  apply(frule_tac V2.PrjInj2) apply(simp)

       apply(drule_tac V2.RefnPrj2) apply(simp) apply(clarsimp)
  apply(frule_tac r' = x2a in V2.PrjInj2) apply(simp)

(*
  RefnPrj3
*)
     defer (* this one is gnarly - and maybe not needed? *)

(* PrjInj1 *)

     apply(simp split:sum.splits) apply(clarsimp)
     apply(drule_tac V1.PrjInj1)
     apply(drule_tac V2.PrjInj1) apply(clarsimp)

(* InjPrj1 *)
     apply(simp split:sum.splits) apply(clarsimp)
     apply(drule_tac V2.InjPrj1)
     apply(drule_tac HagreeR)

     apply(case_tac "V1.prj (V1.inj (d, x1a))")
      apply(drule_tac V1.RefnPrj1) apply(simp) apply(clarsimp)
      apply(drule_tac V1.InjPrj1) apply(rule_tac V1.DO.leq_trans) apply(simp)
      apply(simp)

  apply(frule_tac r = x1 in V1.PrjInj1) 
     apply(cut_tac r = x1a and r' = x1a in V1.RefnPrj3)
       apply(rule_tac V1.RO.leq_refl) apply(simp)
  

    apply(clarsimp)
  apply(frule_tac 
  apply(drule_tac 

  apply(cut_tac d = d and r = x1a and ro = b in V1.RefnPrj3) apply(simp)
       apply(drule_tac V1.RefnPrj1) apply(simp) apply(clarsimp)

      apply(frule_tac d = a in V1.PrjInj1) 
  apply(cut_tac d = d and r = x1a in V1.InjPrj1)

  apply(drule_tac V1.InjPrj1)
  apply(drule_tac V2.PrjInj1) apply(clarsimp)

     apply(safe)
                      apply(drule_tac V2.InjPrj1)
                      apply(drule_tac V2.InjPrj1)
                      apply(drule_tac HagreeR)apply(drule_tac HagreeR)
  apply(drule_tac 
                apply(frule_tac d = x1 in V2.RefnPrj1) apply(clarsimp)
  apply(clarsimp)
                apply(rule_tac V2.RefnInj')
                 apply(rule_tac HagreeL)
                 apply(rule_tac V1.RefnInjR)
                 apply(rule_tac HagreeR) apply(simp)
  apply(simp)
               apply(drule_tac V2.RefnPrj1) apply(simp) apply(clarsimp)
              apply(drule_tac HagreeR)
              apply(drule_tac V1.RefnPrj2) apply(simp) apply(simp)


             apply(drule_tac V2.RefnPrj2) apply(simp) apply(simp)

            apply(drule_tac V2.RefnPrj1) apply(simp) apply(clarsimp)
  
            apply(drule_tac HagreeR) apply(drule_tac d' = d in V1.RefnPrj3) apply(simp) apply(clarsimp)

           apply(drule_tac V2.RefnPrj2) apply(clarsimp) apply(simp) apply(clarsimp)
  apply(frule_tac V2.PrjInj2) apply(clarsimp)

          apply(case_tac "V2.prj (V2.inj (V1.inj (d, x1), x2))")
  apply(drule_tac d = "V1.inj (d, x1)" in V2.RefnInjR)
           apply(drule_tac V2.RefnPrj2) apply(clarsimp) apply(simp)



             apply(subgoal_tac "V2.refnr (V2.inj (x1, r)) (V2.inj (V1.inj (d, x1a), r))")
              defer
              apply(rule_tac V2.RefnInj')
  apply(rule_tac HagreeL)
             defer
  apply(rule_tac V2.RefnInj')

            apply(frule_tac r = x1 in V1.RefnInjD)
  apply(drule_tac HagreeL)


            apply(drule_tac d' = d' in V1.InjPrj2) apply(simp)

           apply(simp add:V2.RO.leq_refl)
apply(simp add:V2.RO.leq_refl)

  apply(simp split:sum.splits) apply(safe)
                apply(frule_tac d = x1 in V2.RefnPrj1) apply(clarsimp)
                apply(clarsimp)
                apply(drule_tac HagreeR)
                apply(drule_tac d = d in V1.RefnInjR)
                apply(drule_tac HagreeL)
  apply(rule_tac V2.RefnInj') apply(simp)  apply(simp)

                apply(frule_tac d = x1 in V2.RefnPrj1) apply(clarsimp)
                apply(clarsimp)
                apply(drule_tac HagreeR)
               apply(drule_tac d = d in V1.RefnInjR)
               apply(drule_tac ro = x2 in V1.RefnPrj2) apply(simp) apply(simp)

              apply(drule_tac ro = x2 in V2.RefnPrj2) apply(simp) apply(simp)

             apply(frule_tac d = x1 in V2.PrjInj1) 
  apply(cut_tac
    d = x1 and d' = "V1.inj (d, x1a)" and r = r and r' = r' in
    V2.RefnInj')

                apply(frule_tac d = x1 in V2.RefnPrj1) apply(clarsimp)
                apply(clarsimp)
                apply(drule_tac HagreeR)
             apply(drule_tac d = d in V1.RefnInjR)
  apply(drule_tac HagreeL)
               apply(drule_tac ro = x2 in V1.RefnPrj2) apply(simp) apply(simp)

                apply(drule_tac HagreeL)
  apply(rule_tac V2.RefnInj') apply(simp)  apply(simp)

(*
         apply(simp add:V2.RO.leq_refl)
          apply(simp add:V2.RO.leq_refl)

       apply(simp split:sum.splits) apply(safe)
                apply(frule_tac d = x1 in V2.RefnPrj1) apply(simp)
                apply(clarsimp)
                apply(drule_tac HagreeR)
  apply(rule_tac V2.RefnInj')
                 apply(drule_tac d = d in V1.RefnInjR) 
                 apply(drule_tac HagreeL) apply(simp) apply(simp)

               apply(frule_tac d = x1 in V2.RefnPrj1) apply(simp)
               apply(clarsimp)
               apply(drule_tac HagreeR)
               apply(drule_tac V1.RefnPrj2) apply(simp) apply(simp)

              apply(drule_tac V2.RefnPrj2) apply(simp) apply(simp)
*)

(*
             apply(frule_tac d = x1 in V2.RefnPrj1) apply(simp) apply(clarsimp)
  apply(drule_tac HagreeR)

             apply(drule_tac d = d in V1.RefnInjR)
             apply(case_tac "V1.prj (V1.inj (d, x1))")
              apply(frule_tac d = a in V1.RefnPrj1) apply(simp)
              apply(clarsimp)
  

  apply(drule_tac V2.RefnInj')
*)
(* idea: injecting back into x1 still gives x1
so this should allow us to finish the proof. *)

             apply(frule_tac d = x1 in V2.PrjInj1) 
  apply(cut_tac d = x1 and d' = "V1.inj (d, x1a)" and r = r and r' = r' in V2.RefnInj')
               apply(drule_tac V2.RefnPrj1) apply(simp) apply(clarsimp)

(* im confused about why this issue is only showing up now.
is the "r" refinement rule not true after all?
it does imply the "d + r" refinement rule which seemed fishy to me,
but on the other hand it does seem reasonable on its own
it could also be that my definitions need to be changed
now that we are in an information ordering sensitive context.
this seems possibly most likely. *)
  apply(drule_tac HagreeR)
             apply(case_tac "V1.prj (V1.inj (d, x1))")
              apply(frule_tac d = a in V1.RefnPrj1) apply(simp)
              apply(clarsimp)


                apply(frule_tac d = x1b in V2.PrjInj1) 
  apply(cut_tac a = "V1.inj (d, x1b)" and b = "x1b" and c = r' in V2.InjInj)

       apply(simp split:sum.splits) apply(safe)
         apply(frule_tac d = x1 in V2.RefnPrj1) apply(simp) apply(clarsimp)
         apply(drule_tac HagreeR)
         apply(drule_tac d = d in V1.RefnPrj1) apply(simp) apply(clarsimp)

             apply(frule_tac d = x1 in V2.RefnPrj1) apply(simp) apply(clarsimp)
         apply(drule_tac HagreeR)
         apply(drule_tac d = d in V1.RefnPrj1) apply(simp) apply(clarsimp)

             apply(frule_tac d = x1 in V2.RefnPrj1) apply(simp) apply(clarsimp)

       apply(simp split:sum.splits) apply(clarsimp) apply(safe)
          apply(drule_tac d = x1a in V2.RefnPrj1) apply(simp) 
           apply(clarsimp)
          apply(drule_tac HagreeR)
          apply(drule_tac ro = x2 in V1.RefnPrj2) apply(simp) apply(simp)

         apply(drule_tac V2.PrjInj2) apply(simp)

        apply(drule_tac ro = ro in V2.RefnPrj2) apply(simp) apply(simp)

       apply(drule_tac r = r in V2.PrjInj2) apply(simp)

apply(simp split:sum.splits) apply(clarsimp)
      apply(simp add:V1.PrjInj1) apply(simp add:V2.PrjInj1)

     apply(simp split:sum.splits) apply(simp add:V2.PrjInj2)

    apply(simp split:sum.splits) apply(clarsimp)

     apply(frule_tac V2.InjPrj1) apply(drule_tac HagreeR)
  apply(case_tac "V1.prj (V1.inj (d, x1a))")
      apply(drule_tac d = a in V1.RefnPrj1)  apply(simp)
      apply(clarsimp)
      apply(drule_tac V1.InjPrj1) apply(frule_tac x = d and y = a in V1.DO.leq_trans)
       apply(simp) apply(simp)

  apply(frule_tac r = x1a in V1.PrjInj1) 
     apply(frule_tac d' = x1c in V1.InjPrj2) apply(simp)

    apply(clarsimp)
    apply(frule_tac V2.PrjInj2) apply(simp)

   apply(simp split:sum.splits) apply(clarsimp) apply(safe)
           apply(frule_tac V2.InjPrj1)  apply(drule_tac HagreeR)
  apply(frule_tac d' = x1c in V2.InjPrj1) apply(drule_tac HagreeR) 
           apply(drule_tac ro = x2 in V1.RefnPrj2) apply(simp)
  apply(frule_tac r = x1a in V1.PrjInj1)
           apply(drule_tac d' = x1b in V1.InjPrj2) apply(clarsimp)

           apply(frule_tac d' = x1c in V2.InjPrj1)  apply(drule_tac HagreeR)
  apply(drule_tac ro = x2a in V1.RefnPrj2) apply(clarsimp)
          apply(frule_tac d = x1b in V1.PrjInj1)
  apply(frule_tac d' = x1b in V1.InjPrj2)
  apply(clarsimp)

         apply(frule_tac d' = "(V1.inj (d, x1a))" in V2.InjPrj2) 
         apply(simp)

        apply(simp)

       apply(frule_tac V2.PrjInj2) apply(simp)

      apply(frule_tac d' = "V1.inj (d', x1)" in V2.InjPrj2) apply(simp)
  
     apply(frule_tac d' = "V1.inj (d', x1)" in V2.InjPrj2) apply(simp)

    apply(frule_tac V2.PrjInj2) apply(clarsimp)
    apply(frule_tac d' = "V1.inj (d', x1)" in V2.InjPrj2)
    apply(clarsimp)

  apply(frule_tac r' = x2a in V2.PrjInj2) apply(clarsimp)

  apply(simp split:sum.splits)
  apply(safe)
        apply(frule_tac V2.InjPrj1)
        apply(drule_tac HagreeR)
  apply(cut_tac a = "V1.inj (a, x1)" and b = "V1.inj (b, x1)" and  c = c in V2.InjInj)

(* i think if we can show that inj (a, x1) is less informantive than (a, x1b)
then we should be good, but we may have issues with threading
through the injectors *)
        apply(case_tac "V1.prj (V1.inj (b, x1))")
(* idea: we need to show some kind of refinement among the V1 stuff
   then we can apply InjInj for V2 *)
(* to show this refinement we use InjInj for V1, showing that inj (a, inj (b, x1))
have a refinement relationship *)
         apply(drule_tac d = aa in V1.RefnPrj1) apply(simp)
  apply(clarsimp)
  apply(cut_tac V2.RefnInj)
  apply(rule_tac V2.RefnInj)
  apply(rule_tac V2.InjInj)

  apply(frule_tac d' = x2a in V2.InjPrj1)

end