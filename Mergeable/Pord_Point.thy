theory Pord_Point imports Pord

begin

(* idea: instead of defining an ordering on our type,
   we synthesize the ordering from a "pointed" one,
   which (should be) more informative *)

locale Aug_Ord' =
  Pord +
  (* lowered order - the one we will actually use*)
  fixes aug :: "'b \<Rightarrow> 'a"
  fixes deaug :: "'a \<Rightarrow> 'b option"

locale AugOrd =
  AugOrd' 

begin

definition l_lleq :: "'b \<Rightarrow> 'b \<Rightarrow> bool" where
"l_lleq a b =
  lleq (aug a) (aug b)"

end

locale AugOrd_Spec =
  AugOrd +
  LatticeLike_Spec lleq +
  assumes aug_deaug :
  "\<And> a . deaug (aug a) = Some a"

assumes deaug_aug :
  "\<And> b a . deaug b = Some a \<Longrightarrow> aug a = b"

assumes leq_aug_leq :
  "\<And> a a'. l_lleq a a' \<Longrightarrow>  lleq (aug a) (aug a')"

assumes aug_leq_leq1 :
  "\<And> b b' a . l_leq b b' \<Longrightarrow>
              deaug b = Some a \<Longrightarrow> 
              (\<exists> a' . deaug b' = Some a' \<and> l_lleq a a')"

assumes aug_leq_leq2 :
  "\<And> b b' . lleq b b' \<Longrightarrow>
              deaug b' = None \<Longrightarrow> 
              deaug b = None"


sublocale AugOrd_Spec \<subseteq> LLl : LatticeLike_Spec "l_lleq"
  apply(unfold_locales)
    apply(simp add:l_lleq_def)
    apply(simp add:leq_refl) 


    apply(simp add:l_lleq_def)
   apply(drule_tac a = "aug a" and b = "aug b" and c = "aug c" in leq_trans)
    apply(simp) apply(simp)

    apply(simp add:l_lleq_def)
  apply(cut_tac a = "aug a" and b = "aug b" in leq_antisym)
    apply(simp)
   apply(simp)

  apply(clarsimp)
  apply(cut_tac a = a in aug_deaug)
  apply(clarsimp)
  apply(cut_tac a = b in aug_deaug)
  apply(thin_tac 
"lleq (aug b)
            (aug b)")
  apply(thin_tac " aug a = aug b")
  apply(clarsimp)
  done

end