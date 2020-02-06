theory ViewRef_Comp3 imports ViewRef3

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
  assumes Hagree12 :
    "\<And> d1 d1' d2x d2' . V1.refn d1 d1' \<Longrightarrow>
        V2.refn d2x d2' \<Longrightarrow>
        V2.refn (V1.inj d1 d2x) (V1.inj d1' d2')"
  assumes Hagree21 :
    "\<And> d2 d2' . V2.refn d2 d2' \<Longrightarrow>
        V1.refn (V1.prj d2) (V1.prj d2')"

begin

lemma Hagree12' :
    "\<And> d1 d1' d2x  . V1.refn d1 d1' \<Longrightarrow>
        V2.refn (V1.inj d1 d2x) (V1.inj d1' d2x)"
  apply(drule_tac d2x = d2x and d2' = d2x in Hagree12)
   apply(rule_tac V2.DO.leq_refl)
  apply(simp)
  done


fun inj' :: "'a \<Rightarrow> 'c \<Rightarrow> 'c" where
  "inj' d r2 =
    V2.inj (V1.inj d (V2.prj r2)) r2"

fun prj' :: "'c \<Rightarrow> 'a" where
  "prj' r2 =
    V1.prj (V2.prj r2)"

abbreviation vp :: "('a, 'c) view_ref_parms" where
"vp \<equiv> \<lparr> inj = inj', prj = prj', refn = (V1.refn) \<rparr>"


end

sublocale View_Comp_Spec \<subseteq> View_Ref_Spec vp
  apply(unfold_locales)
  apply(simp add:V1.DO.leq_refl)
             apply(simp add:V1.DO.leq_trans)
apply(simp add:V1.DO.leq_antisym)
    apply(simp)
    apply(simp add: V1.PrjInj) apply(simp add:V2.PrjInj')

   apply(simp)
   apply(cut_tac r = r and d = "(V1.inj d (V2.prj r))" and d' = "(V1.inj d' (V2.prj r))" in V2.InjPrj)
    apply(cut_tac r = "(V2.prj r)" and d = d and d' = d' in V1.InjPrj)
     apply(simp)
  apply(frule_tac Hagree12') apply(simp)

   apply(drule_tac Hagree21)
   apply(cut_tac r = "V2.prj r" and d = d in V1.InjPrj')
   apply(drule_tac x = d and y = "(V1.prj (V1.inj d (V2.prj r)))" in V1.DO.leq_trans) 
    apply(simp) apply(simp)

  apply(clarsimp)
  apply(cut_tac 
a =  "(V1.inj a (V2.prj (V2.inj (V1.inj b (V2.prj c)) c)))"
and b = "(V1.inj b (V2.prj c))" and c = c in V2.InjInj)
  apply(clarsimp)


  apply(cut_tac a = a and b = b and c = "V2.prj c" in V1.InjInj)
  apply(clarsimp)

  apply(rule_tac x = aba in exI)
  apply(clarsimp)
  apply(safe)

  apply(frule_tac Hagree21)
  apply(cut_tac d = a and r = "(V2.prj (V2.inj (V1.inj b (V2.prj c)) c))"
in V1.InjPrj')

  apply(rule_tac x = "V1.prj ab" in exI)

  apply(safe)
  apply(frule_tac Hagree21)
  apply(cut_tac d = a and r = "(V2.prj (V2.inj (V1.inj b (V2.prj c)) c))"
in V1.InjPrj')
   apply(rule_tac V1.DO.leq_trans) apply(simp) apply(simp)

   apply(cut_tac d = " (V1.inj (V1.prj ab) (V2.prj c))" and r = c in V2.InjPrj')
  apply(rotate_tac -1)
  apply(frule_tac Hagree21)


   apply(subgoal_tac "V2.prj (V2.inj (V1.inj (V1.prj ab) (V2.prj c)) c) = ab")
    defer

 
  apply(frule_tac V1.PrjInj)

  

  apply(subgoal_tac 
"V2.inj (V1.inj (V1.prj ab) (V2.prj c)) c = 
 V2.inj (V1.inj a (V2.prj (V2.inj (V1.inj b (V2.prj c)) c))) (V2.inj (V1.inj b (V2.prj c)) c)")
    defer

  apply(simp add: V2.InjInj)
  apply(simp add:V2.PrjInj)

    apply(simp add: V1.PrjInj) apply(simp add:V2.PrjInj)

  apply(simp add: V2.PrjInj)
      apply(simp split:sum.splits) apply(safe)
      apply(simp add:V1.PrjInj1 V2.PrjInj1)
     apply(simp split:sum.splits) apply(simp add:V2.PrjInj2)
    apply(simp split:sum.splits)       
  apply(frule_tac V2.InjPrj1) apply(clarsimp)

  apply(subgoal_tac
" V2.refnd (V1.inj (d, x1)) (V1.inj (d', x1)) ")

           apply(drule_tac r = r in V2.RefnInj)
  apply(simp)

end