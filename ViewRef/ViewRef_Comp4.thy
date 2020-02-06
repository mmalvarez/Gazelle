theory ViewRef_Comp4 imports ViewRef4

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


fun inj' :: "'a \<Rightarrow>'c \<Rightarrow> 'c" where
  "inj' d r2 = V2.inj (V1.inj d (V2.prj r2)) r2"
(*
fun inj' :: "('a * 'c) \<Rightarrow> 'c" where
  "inj' (d, r2) =
    (case V2.prj r2 of
      Inl r1 \<Rightarrow> (case V1.prj r1 of
          Inl _ \<Rightarrow> V2.inj (V1.inj (d, r1), r2)
          | Inr _ \<Rightarrow> r2)
      | Inr r2 \<Rightarrow> r2)"
*)
(* huh, maybe this is wrong?

*)
fun prj' :: "'c \<Rightarrow> ('a)" where
  "prj' r2 =
    V1.prj (V2.prj r2)"

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
  apply(simp add:V1.DO.leq_refl)
             apply(simp add:V1.DO.leq_trans)
apply(simp add:V1.DO.leq_antisym)
         apply(simp add:V2.RO.leq_refl)

  apply(simp)
             apply(drule_tac V2.RO.leq_trans) apply(simp) apply(simp)
         apply(simp add:V2.RO.leq_antisym)

      apply(clarsimp)
      apply(frule_tac r = "V2.prj r" in V1.RefnInjD)
      apply(drule_tac HagreeL)
      apply(drule_tac r = r in V2.RefnInjD)
      apply(simp)

      apply(simp)
      apply(rule_tac V2.RefnInj')
       apply(rule_tac HagreeL) apply(rule_tac V1.RefnInjR)
       apply(rule_tac HagreeR) apply(rule_tac V2.RefnPrj)
       apply(simp) apply(simp)

     apply(simp)
     apply(rule_tac V1.RefnPrj) apply(rule_tac HagreeR)
     apply(rule_tac V2.RefnPrj) apply(simp)

    apply(simp)
    apply(simp add: V1.PrjInj V2.PrjInj)

   apply(simp)

   apply(cut_tac d = "(V1.inj d (V2.prj r))" and r = r in V2.InjPrj)
   apply(drule_tac HagreeR)
   apply(drule_tac V1.RefnPrj)
   apply(cut_tac d = d and r = "(V2.prj r)" in V1.InjPrj)
   apply(rule_tac V1.DO.leq_trans) apply(simp) apply(simp)

  apply(simp)

(* idea: eliminate inj(prj) pair
then use v1.injinj and v2.injinj *)
  apply(cut_tac d = "(V1.inj b (V2.prj c))" and r = c in V2.InjPrj)
  apply(drule_tac HagreeR)


(* this may be the only place where we need RefnInjR *)

(* original proof *)
  apply(drule_tac d = a in V1.RefnInjR)


  apply(cut_tac
        a = "(V1.inj a (V2.prj (V2.inj (V1.inj b (V2.prj c)) c)))"
        and b = " (V1.inj b (V2.prj c))"
        and c = c in V2.InjInj)

  apply(rule_tac y = "(V2.inj (V1.inj a (V2.prj (V2.inj (V1.inj b (V2.prj c)) c))) c)" in V2.RO.leq_trans)
   defer
   apply(simp)

  apply(drule_tac HagreeL)

  apply(cut_tac a = a and b = b and c = "V2.prj c" in V1.InjInj)


  apply(drule_tac r = c in V2.RefnInjD)
  apply(drule_tac HagreeL)
  apply(drule_tac r = c in V2.RefnInjD)

  apply(rule_tac y = "(V2.inj (V1.inj a (V1.inj b (V2.prj c))) c)" in V2.RO.leq_trans)
  apply(simp)
  apply(simp)

  done

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