theory Iso imports Main

begin

locale Iso =
  fixes Iso_parm :: "('l \<Rightarrow> 'r) * ('r \<Rightarrow> 'l)"

begin

abbreviation to_r :: _ where
"to_r \<equiv> fst Iso_parm"

abbreviation to_l :: _ where
"to_l \<equiv> snd Iso_parm"

fun lift_l :: "('l \<Rightarrow> 'o) \<Rightarrow> ('r \<Rightarrow> 'o)" where
  "lift_l fl = (\<lambda> r . fl (to_l r))"

fun lift_r :: "('r \<Rightarrow> 'o) \<Rightarrow> ('l \<Rightarrow> 'o)" where
  "lift_r fr = (\<lambda> l . fr (to_r l))"

end


locale Iso_Spec = Iso +
  assumes Hisol : "\<And> l . to_l (to_r l) = l"
  assumes Hisor : "\<And> r . to_r (to_l r) = r"

begin

lemma iso_lift_fr : "\<And> fr . lift_r (lift_l fr) = fr"
  apply(clarsimp)
  apply(simp add:Hisol)
  done

lemma iso_lift_fl : "\<And> fl . lift_l (lift_r fl) = fl"
  apply(clarsimp)
  apply(simp add:Hisor)
  done

lemma iso_lift_pred_r :
  "P r \<Longrightarrow> lift_r P (to_l r)"
  apply(clarsimp)
  apply(simp add:Hisor)
  done

lemma iso_lift_pred_l :
  "P l \<Longrightarrow> lift_l P (to_r l)"
  apply(clarsimp)
  apply(simp add:Hisol)
  done

end

end