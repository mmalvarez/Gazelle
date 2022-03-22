theory Lift_Triv
  imports "../Lifter"

begin

(*
 * triv
 *)
(* we are revisiting this because automation seems to be having
 * problems with triv in the presence of certain kinds of polymorphism.
 * i wonder if we need an explicit type paramete?
 *)
text_raw \<open>%Snippet gazelle__lifter__instances__lift_triv__triv_l\<close>
definition triv_l ::
  "('x, 'a :: Bogus, 'a md_triv) lifting" where
"triv_l =
  LMake (\<lambda> s a _ . mdt a) (\<lambda> s b . (case b of (mdt b') \<Rightarrow> b')) (\<lambda> s . mdt bogus)"
text_raw \<open>%EndSnippet\<close>

text_raw \<open>%Snippet gazelle__lifter__instances__lift_triv__triv_l_S\<close>
definition triv_l_S :: "'x \<Rightarrow> 'a md_triv set" where
"triv_l_S = (\<lambda>   _ . UNIV)"
text_raw \<open>%EndSnippet\<close>

locale triv_l_valid_weak =
  fixes T :: "('a :: Bogus) itself"

sublocale triv_l_valid_weak \<subseteq>
  out : lifting_valid_weak "triv_l :: ('b, 'a, 'a md_triv) lifting" "(\<lambda> _ . UNIV)"
proof
  fix s :: 'b
  fix a :: "'a :: Bogus"
  fix b :: "'a md_triv"
  show "LOut (triv_l) s (LUpd (triv_l) s a b) = a"
    by(auto simp add:triv_l_def split:md_triv.splits)
next
  fix s :: 'b
  fix b :: "'a md_triv"

  show "b <[ LUpd triv_l s (LOut triv_l s b) b"
   by(auto simp add:triv_l_def triv_pleq
          split:md_triv.splits)
next
  fix s :: 'b
  fix a :: "'a"
  fix b :: "'a md_triv"
  show "LUpd triv_l s a b \<in> UNIV" by auto
qed

lemma (in triv_l_valid_weak) ax :
  shows "lifting_valid_weak (triv_l :: ('b, 'a, 'a md_triv) lifting) (\<lambda> _ :: 'b . UNIV)"
  using out.lifting_valid_weak_axioms
  by auto

lemma (in triv_l_valid_weak) ax_g :
  assumes "S' = (\<lambda> _ . UNIV)"
  shows "lifting_valid_weak (triv_l :: ('b, 'a, 'a md_triv) lifting) S'"
  using out.lifting_valid_weak_axioms assms
  by auto

locale triv_l_valid_ok_ext =
  fixes T :: "('a :: Bogus) itself"

sublocale triv_l_valid_ok_ext \<subseteq>
  out : lifting_valid_ok_ext "(triv_l :: ('b, 'a, 'a md_triv) lifting)" "(\<lambda> _ :: 'b . UNIV)"
proof
  show "\<And> S . ok_S \<subseteq> UNIV" by auto
next
  fix s :: 'b
  fix a :: 'a
  fix b :: "'a md_triv"
  show "b \<in> ok_S \<Longrightarrow> LUpd triv_l s a b \<in> ok_S"
    by(auto simp add: triv_l_def triv_ok_S)
qed

lemma (in triv_l_valid_ok_ext) ax :
  shows "lifting_valid_ok_ext (triv_l :: ('b, 'a, 'a md_triv) lifting) (\<lambda> _ :: 'b . UNIV)"
  using out.lifting_valid_ok_ext_axioms
  by auto

lemma (in triv_l_valid_ok_ext) ax_g :
  assumes "S' = (\<lambda> _ . UNIV)"
  shows "lifting_valid_ok_ext (triv_l :: ('b, 'a, 'a md_triv) lifting) S'"
  using assms out.lifting_valid_ok_ext_axioms
  by auto

locale triv_l_valid_pres_ext =
  fixes T :: "('a :: Bogus) itself"

sublocale triv_l_valid_pres_ext \<subseteq>
  out : lifting_valid_pres_ext "(triv_l :: ('b, 'a, 'a md_triv) lifting)" "\<lambda> (_ :: 'b) . UNIV"

proof
  fix v :: "'a md_triv"
  fix V :: "'a md_triv set"
  fix supr :: "'a md_triv"
  fix s :: 'b
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

lemma (in triv_l_valid_pres_ext) ax :
  shows "lifting_valid_pres_ext (triv_l :: ('b, 'a, 'a md_triv) lifting) (\<lambda> _ . UNIV)"
  using out.lifting_valid_pres_ext_axioms
  by auto

lemma (in triv_l_valid_pres_ext) ax_g :
  assumes "S' = (\<lambda> _ . UNIV)"
  shows "lifting_valid_pres_ext (triv_l :: ('b, 'a, 'a md_triv) lifting) S'"
  using assms out.lifting_valid_pres_ext_axioms
  by auto

locale triv_l_valid_pairwise_ext =
  fixes T :: "'a itself"

sublocale triv_l_valid_pairwise_ext \<subseteq>
  out : lifting_valid_pairwise_ext "\<lambda> (_ :: 'b) . (UNIV :: 'a md_triv set)"
proof
  fix x1 x2 x3 s12 s23 s13 s123 :: "'a md_triv"

  show "s123 \<in> UNIV"
    by auto
qed

lemma (in triv_l_valid_pairwise_ext) ax :
  shows "lifting_valid_pairwise_ext (\<lambda> (_ :: 'b) . (UNIV :: 'a md_triv set))"
  using out.lifting_valid_pairwise_ext_axioms
  by auto

lemma (in triv_l_valid_pairwise_ext) ax_g :
  assumes "S' = (\<lambda> (_ :: 'b) . (UNIV :: 'a md_triv set))"
  shows "lifting_valid_pairwise_ext S'"
  using assms out.lifting_valid_pairwise_ext_axioms
  by auto

locale triv_l_valid_oc_ext =
  fixes T :: "('a :: Bogus) itself"

sublocale triv_l_valid_oc_ext \<subseteq>
  out: lifting_valid_oc_ext "(triv_l :: ('b, 'a, 'a md_triv) lifting)" "\<lambda> (_ :: 'b) . (UNIV :: 'a md_triv set)"
proof
  fix x2 Xs 
  fix supr :: "'a md_triv" 
  fix s :: 'b
  fix r :: 'a
  fix w :: "'a md_triv"
  assume W: "w \<in> Xs"
  assume Supr : "is_sup Xs supr"
  assume Compat :
    "(\<And>x. x \<in> Xs \<Longrightarrow>
             LOut triv_l s x = r)"

  have Supr_W : "supr = w"
    using is_supD1[OF Supr W]
    by(auto simp add: triv_pleq)

  hence "w = mdt r"
    using Compat[OF W]
    by(cases w; auto simp add: triv_pleq triv_l_def)

  then show "LOut triv_l s supr = r"
    using Supr_W
    by(auto simp add: triv_l_def)
qed

lemma (in triv_l_valid_oc_ext) ax :
  shows "lifting_valid_oc_ext (triv_l :: ('b, 'a, 'a md_triv) lifting)"
  using out.lifting_valid_oc_ext_axioms
  by auto

end