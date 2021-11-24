theory Lift_Triv
  imports "../Lifter"

begin

(*
 * triv
 *)
definition triv_l ::
  "('x, 'a :: Bogus, 'a md_triv) lifting" where
"triv_l =
  LMake (\<lambda> s a _ . mdt a) (\<lambda> s b . (case b of (mdt b') \<Rightarrow> b')) (\<lambda> s . mdt bogus)"

interpretation triv_l : 
  lifting_valid_weak "(triv_l :: ('x, 'a :: Bogus, 'a md_triv) lifting)" "\<lambda> _ . UNIV"
proof
  fix s :: 'x
  fix a :: 'a
  fix b
  show "LOut (triv_l) s (LUpd (triv_l) s a b) = a"
    by(auto simp add:triv_l_def split:md_triv.splits)
next
  fix s :: 'x
  fix b :: "'a md_triv"

  show "b <[ LUpd triv_l s (LOut triv_l s b) b"
   by(auto simp add:triv_l_def triv_pleq
          split:md_triv.splits)
next
  fix s :: 'x
  fix a :: "'a"
  fix b :: "'a md_triv"
  show "LUpd triv_l s a b \<in> UNIV" by auto
qed


interpretation triv_l:
  lifting_valid_ok_ext "(triv_l :: ('x, 'a :: {Bogus, Okay}, 'a md_triv) lifting')" "\<lambda> _ . UNIV"
proof
  show "\<And> S . ok_S \<subseteq> UNIV" by auto
next
  fix s a b
  show "b \<in> ok_S \<Longrightarrow> LUpd triv_l s a b \<in> ok_S"
    by(auto simp add: triv_l_def triv_ok_S)
qed


interpretation triv_l :
  lifting_valid_pres_ext "(triv_l :: ('x, 'a :: {Bogus}, 'a md_triv) lifting')" "\<lambda> _ . UNIV"
proof
next
  fix v :: "'a md_triv"
  fix V 
  fix supr :: "'a md_triv"
  fix s 
  fix f

  assume Nemp : "v \<in> V"
  assume H : "is_sup V supr"

  show "is_sup (LMap triv_l f s ` V) (LMap triv_l f s supr)"
  proof(rule is_supI)
    fix x

    assume "x \<in> LMap triv_l f s ` V"

    then obtain x0 where X0 : "x0 \<in> V" "LMap triv_l f s x0 = x"
      by(auto)

    obtain x0' where X0' : "x0 = mdt x0'"
      by(cases x0; auto)

    obtain supr' where Supr' : "supr = mdt supr'"
      by(cases supr; auto)

    have Eq : "x0' = supr'"
      using is_supD1[OF H X0(1)] X0' Supr'
      by(auto simp add: triv_pleq)

    show "x <[ LMap triv_l f s supr"
      using X0' X0 Eq Supr'
      by(auto simp add: triv_pleq)
  next
    fix y
    assume Ub : "is_ub (LMap triv_l f s ` V) y"

    obtain y' where Y' : "y = mdt y'" by(cases y; auto)

    obtain v' where V' : "v = mdt v'" by(cases v; auto)

    have Eq1 : "y = LMap triv_l f s v"
      using is_ubE[OF Ub, of "LMap triv_l f s v"] Nemp
      by(auto simp add: triv_pleq)

    have  "supr = v"
      using is_supD1[OF H Nemp] by(auto simp add: triv_pleq)

    hence Eq2 : "LMap triv_l f s supr = LMap triv_l f s v" by simp

    show "LMap triv_l f s supr <[ y"
      using Eq1 Eq2
      by(simp add: triv_pleq)
  qed
qed

interpretation triv_l : lifting_valid_pairwise_ext "\<lambda> _ . (UNIV :: 'a md_triv set)"
proof
  fix x1 x2 x3 s12 s23 s13 s123 :: "'a md_triv"

  show "s123 \<in> UNIV"
    by auto
qed


end