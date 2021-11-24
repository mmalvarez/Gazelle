theory LangCompFunOrd
imports LangCompSimple MergeableFun
begin


definition scross :: "('a \<Rightarrow> 'b) set \<Rightarrow> 'a set \<Rightarrow> 'b set" where
"scross Fs Xs =
  { x . \<exists> f y . f \<in> Fs \<and> y \<in> Xs \<and> x = f y }"

lemma scross_inI :
  assumes Hf : "f \<in> Fs"
  assumes Hx : "x \<in> Xs"
  assumes Heq : "res = f x"
  shows "res \<in> scross Fs Xs" using assms
  unfolding scross_def
  by blast

lemma scross_inD  :
  assumes "res \<in> scross Fs Xs"
  shows "\<exists> f y . f \<in> Fs \<and> y \<in> Xs \<and> res = f y" using assms
  unfolding scross_def
  by blast


definition sups_pres ::
  "('a \<Rightarrow> ('b :: Mergeableb) \<Rightarrow> 'b) set \<Rightarrow> bool"
  where
"sups_pres Fs =
  (\<forall> x sup syn Xs .
    x \<in> Xs \<longrightarrow>
    finite Xs \<longrightarrow>
    is_sup Xs sup \<longrightarrow>
    (\<exists> fsup . is_sup Fs fsup \<and> is_sup (scross ((\<lambda> f . f syn) ` Fs) Xs) (fsup syn sup)))"

lemma sups_presI [intro] :
  assumes "\<And> x sup syn Xs  . 
           x \<in> Xs \<Longrightarrow>
           finite Xs \<Longrightarrow> 
           is_sup Xs sup \<Longrightarrow>
          (\<exists> fsup . is_sup Fs fsup \<and> is_sup (scross ((\<lambda> f . f syn) ` Fs) Xs) (fsup syn sup))"
  shows "sups_pres Fs"
  using assms unfolding sups_pres_def by blast


lemma sups_presD :
  assumes "sups_pres Fs"
  assumes "x \<in> Xs"
  assumes "finite Xs"
  assumes "is_sup Xs sp"
  shows "(\<exists> fsup . is_sup Fs fsup \<and> is_sup (scross ((\<lambda> f . f syn) ` Fs) Xs) (fsup syn sp))" using assms
  unfolding sups_pres_def 
  by blast

lemma scross_subset :
  assumes HF : "Fs1 \<subseteq> Fs2"
  assumes HX : "Xs1 \<subseteq> Xs2"
  shows "scross Fs1 Xs1 \<subseteq> scross Fs2 Xs2"
proof
  fix res
  assume Hres : "res \<in> scross Fs1 Xs1"

  obtain f x where
    F : "f \<in> Fs1" and
    X : "x \<in> Xs1" and
    Res : "res = f x" using scross_inD[OF Hres] by blast

  show "res \<in> scross Fs2 Xs2"
  proof(rule scross_inI)
    show "f \<in> Fs2"
      using F HF by blast
    show "x \<in> Xs2"
      using X HX by blast
    show "res = f x" using Res by auto
  qed
qed

definition scross_alt :: "('a \<Rightarrow> 'b) set \<Rightarrow> 'a set \<Rightarrow> 'b set" where
"scross_alt Fs Xs =
  (\<lambda> fx . (case fx of (f, x) \<Rightarrow> f x)) ` (Fs \<times> Xs)"

lemma scross_alt_eq :
  "scross_alt Fs Xs = scross Fs Xs"
  unfolding scross_def scross_alt_def
  by(auto)

lemma scross_finite :
  assumes HF : "finite Fs"
  assumes HX : "finite Xs"
  shows "finite (scross Fs Xs)" 
  unfolding sym[OF scross_alt_eq] scross_alt_def
  using finite_cartesian_product[OF HF HX]
  by blast

lemma sups_pres_subset :
  fixes Fs :: "('a \<Rightarrow> ('b :: Mergeableb) \<Rightarrow> 'b) set"
  assumes H : "sups_pres Fs"
  assumes Hfin : "finite Fs"
  assumes Hsub : "Fs' \<subseteq> Fs"
  assumes Hnemp : "f \<in> Fs'"
  shows "sups_pres Fs'"
proof(rule sups_presI)
  fix el :: "'b"
  fix sup1 :: "'b"
  fix syn 
  fix Xs :: "'b set"
  fix Fs_sub :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) set"

  assume Hfin_Xs : "finite Xs"
  assume H' : "is_sup Xs sup1"
  assume Hnemp_Xs : "el \<in> Xs"

  obtain Rest where Rest : "Fs' \<union> Rest = Fs" using Hsub by blast
  have Rfin : "finite Rest" using Rest Hfin by auto

  obtain supr where Supr1 : 
    "is_sup Fs supr" and
    Supr2 : 
    "is_sup (scross ((\<lambda>f. f syn) ` Fs) Xs) (supr syn sup1)"
    unfolding Rest
    using sups_presD[OF H Hnemp_Xs Hfin_Xs H']
    unfolding has_sup_def
    by(auto)

  have Subset' : "(\<lambda>f. f syn) ` Fs' \<subseteq> (\<lambda>f. f syn) ` Fs"
    unfolding sym[OF Rest] by blast

  have Subset : "(scross ((\<lambda>f. f syn) ` (Fs')) Xs)  \<subseteq> (scross ((\<lambda>f. f syn) ` (Fs' \<union> Rest)) Xs)"    
    using scross_subset[OF Subset', of Xs Xs]
    unfolding Rest
    by blast

  have Subset2: "(\<lambda>f. f syn sup1) ` Fs' \<subseteq> (\<lambda>f. f syn sup1) ` (Fs' \<union> Rest)"
    by blast

  have Nemp : "(f syn el) \<in> scross ((\<lambda>f. f syn) ` Fs') Xs"
    using Hnemp Hnemp_Xs
    unfolding scross_def by auto

  have Nemp2 : "f syn sup1 \<in> (\<lambda>f. f syn sup1) ` Fs'"
    using Hnemp by auto

  have Hfin_full' : "finite ((\<lambda>f. f syn) ` (Fs))"
    using Hfin by blast

  have Fin_full : "finite (scross ((\<lambda>f. f syn) ` (Fs)) Xs)"
    using scross_finite[OF Hfin_full' Hfin_Xs]
    by auto

  have Fin_full2 : "finite ((\<lambda>f. f syn sup1) ` ((Fs' \<union> Rest)))"
    using Hfin
    sorry

  obtain fsup where Fsup : "is_sup Fs' fsup"
    using has_sup_subset[OF Hfin Supr1 Hsub Hnemp]
    unfolding has_sup_def by auto

  have "is_sup (scross ((\<lambda>f. f syn) ` Fs') Xs) (fsup syn sup1)"
  proof(rule is_sup_intro)
    fix xy
    assume Xy : "xy \<in> scross ((\<lambda>f. f syn) ` Fs') Xs" 

    obtain fxy xxy 
      where Fxy' : "fxy \<in> (\<lambda>f. f syn) ` Fs'" and Xxy' : "xxy \<in> Xs" and Xy_eq : "xy = fxy xxy"
      using scross_inD[OF Xy]
      by auto

    obtain fxy2 where Fxy2 : "fxy2 \<in> Fs'" and
      Fxy2_eq : "fxy = fxy2 syn"
      using Fxy'
      by(blast)

    show "xy <[ fsup syn sup1"
      using is_sup_unfold1[OF Fsup Fxy2]
      unfolding Xy_eq Fxy2_eq fun_pleq
      apply(step) apply(step)



(* same problem? we can derive a sup for Fs', but we don't actually know anything about what
happens to cross product when we remove some functions...

new sup <[ overall sup (obvious).

*)

  show "\<exists> fsup .
    is_sup Fs' fsup \<and> is_sup (scross ((\<lambda>f. f syn) ` Fs') Xs) (fsup syn sup1)"

  obtain sup2 where Sup2 : "is_sup (scross ((\<lambda>f. f syn) ` Fs') Xs) sup2"
    using has_sup_subset[OF _ Supr1 Subset ] Fin_full unfolding Rest has_sup_def
    by auto

  obtain sup2' where Sup2' : "is_sup ((\<lambda>f. f syn sup1) ` (Fs')) sup2'"
    using has_sup_subset[OF Fin_full2 Supr2 Subset2 Nemp2]  unfolding Rest has_sup_def
    by auto

  show "\<exists>sup'. is_sup ((\<lambda>f. f syn sup1) ` Fs') sup' \<and> is_sup (scross ((\<lambda>f. f syn) ` Fs') Xs) sup'"
    using has_sup_subset[OF _ Supr Subset Nemp] Fin_full unfolding Rest
    by auto

end