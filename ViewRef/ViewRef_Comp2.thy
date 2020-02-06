theory ViewRef_Comp2 imports ViewRef2

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
  assumes Hagree1 :
    "\<And> d1 d1' d2 . V1.refn d1 d1' \<Longrightarrow>
        V2.refn (V1.inj (d1, d2)) (V1.inj (d1', d2))"
  assumes Hagree2 :
    "\<And> d2 d2' . V2.refn d2 d2' \<Longrightarrow>
        V1.refn ()"

begin

fun inj' :: "('a * 'c) \<Rightarrow> 'c" where
  "inj' (d, r2) =
    (case V2.prj r2 of
      Inl r1 \<Rightarrow> (case V1.prj r1 of
          Inl _ \<Rightarrow> V2.inj (V1.inj (d, r1), r2)
          | Inr _ \<Rightarrow> r2)
      | Inr r2 \<Rightarrow> r2)"

fun prj' :: "'c \<Rightarrow> ('a + 'c)" where
  "prj' r2 =
    (case V2.prj r2 of
      Inl r1 \<Rightarrow> (case V1.prj r1 of
        Inl d \<Rightarrow> Inl d
        | Inr r1 \<Rightarrow> Inr r2)
      | Inr r2 \<Rightarrow> Inr r2)"    

abbreviation vp :: "('a, 'c) view_ref_parms" where
"vp \<equiv> \<lparr> inj = inj', prj = prj', refn = (V1.refn) \<rparr>"


end

sublocale View_Comp_Spec \<subseteq> View_Ref_Spec vp
  apply(unfold_locales)
  apply(simp add:V1.DO.leq_refl)
             apply(simp add:V1.DO.leq_trans)
apply(simp add:V1.DO.leq_antisym)
  apply(simp)
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