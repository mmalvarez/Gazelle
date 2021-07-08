theory Composition
imports Composition_Core
begin

(* This file extends the definitions in Composition_Core.thy to a fully general implementation
 * of composition of language semantics. In particular, it does so while requiring
 * a weaker condition than Composition_Simple.thy does on the semantics being composed.
 * For this reason we consider it preferable to use the definitions here in practice,
 * even if the ones in Composition_Simple are more straightforward. *)

(* 
 * sups_pres ("SUPremumS are PREServed") 
 *
 *
 * Note that unlike Scott continuity, we don't have the "closure" property
 * here (that the set is closed under LUBs) - this doesn't seem to be a problem, but
 * puzzling through the implications of this is a TODO.
 *
 *The type of the syntax involved in the languages being merged is assumed to be the same
 * here - it should be easy to apply the appropriate syntax-translation function before
 * using sups_pres.
*)

(* TODO: do we really need the nonemptiness requirement for Fs' here? *)
definition sups_pres :: 
  "('a \<Rightarrow> ('b :: Mergeable) \<Rightarrow> 'b) set \<Rightarrow> bool" where
"sups_pres Fs =
  (\<forall> x sup syn Xs Fs' f .
    x \<in> Xs \<longrightarrow>
    finite Xs \<longrightarrow>
    is_sup Xs sup \<longrightarrow>
    Fs' \<subseteq> Fs \<longrightarrow>
    f \<in> Fs' \<longrightarrow>
    (\<exists> sup' . is_sup ((\<lambda> f . f syn sup) ` Fs') sup' \<and>
     is_sup (scross ((\<lambda> f . f syn) ` Fs') Xs) sup'))"

lemma sups_presI [intro] :
  assumes "\<And> x sup syn Xs Fs' f . 
           x \<in> Xs \<Longrightarrow>
           finite Xs \<Longrightarrow> 
           is_sup Xs sup \<Longrightarrow>
          Fs' \<subseteq> Fs \<Longrightarrow>
          f \<in> Fs' \<Longrightarrow>
          (\<exists> sup' . is_sup ((\<lambda> f . f syn sup) ` Fs') sup' \<and>
           is_sup (scross ((\<lambda> f . f syn) ` Fs') Xs) sup')"
  shows "sups_pres Fs"
  using assms unfolding sups_pres_def by blast

lemma sups_presD :
  assumes "sups_pres Fs"
  assumes "x \<in> Xs"
  assumes "finite Xs"
  assumes "is_sup Xs sp"
  assumes "Fs' \<subseteq> Fs"
  assumes "f \<in> Fs'"

  shows "(\<exists> sup' . is_sup ((\<lambda> f . f syn sp) ` Fs') sup' \<and>
           is_sup (scross ((\<lambda> f . f syn) ` Fs') Xs) sup')" using assms
  unfolding sups_pres_def 
  by blast

(* Helper lemmas for scross *)
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

(*
 * sups_pres being closed under subset is important both as a "sanity-check" on the
 * definition, as well as being useful directly as an ingredient in proving later lemmas.
 *)
lemma sups_pres_subset :
  fixes Fs :: "('a \<Rightarrow> ('b :: Mergeable) \<Rightarrow> 'b) set"
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
  fix f

  assume Hnemp_Xs : "el \<in> Xs"
  assume Hfin_Xs : "finite Xs"
  assume H' : "is_sup Xs sup1"
  assume Hfs_sub : "Fs_sub \<subseteq> Fs'"
  assume Hnemp_Fs_sub : "f \<in> Fs_sub"

  obtain Rest where Rest : "Fs' \<union> Rest = Fs" using Hsub by blast

  have Rfin : "finite Rest" using Rest Hfin by auto

  show  "\<exists>sup'.
          is_sup ((\<lambda>f. f syn sup1) ` Fs_sub) sup' \<and>
          is_sup (scross ((\<lambda>f. f syn) ` Fs_sub) Xs) sup'"
    using sups_presD[OF H Hnemp_Xs Hfin_Xs H', of Fs_sub f] Hfs_sub Hnemp_Fs_sub Hsub
    unfolding has_sup_def
    by(auto)

qed

lemma sups_pres_pair :
  assumes Hf : "sups_pres {f1, f2}"
  assumes Hx : "has_sup {x1, x2}"
  shows "has_sup {f1 syn x1, f2 syn x2}"
proof-

  obtain s where S : "is_sup {x1, x2} s"
    using Hx unfolding has_sup_def by auto

  obtain sup' where Sup' : "is_sup ((\<lambda>f. f syn s) ` {f1, f2}) sup'"
    and Sup'_full : "is_sup (scross ((\<lambda>f. f syn) ` {f1, f2}) {x1, x2}) sup'"
    using sups_presD[OF Hf _ _ S _ _, of x1 "{f1, f2}"]
    by auto

  then obtain z where Z: "is_sup (scross ((\<lambda>f. f syn) ` {f1, f2}) {x1, x2}) z"
    unfolding has_sup_def by auto

  have Scross_eq : 
    "(scross ((\<lambda>f. f syn) ` {f1, f2}) {x1, x2}) =
      { f1 syn x1, f1 syn x2, f2 syn x1, f2 syn x2 }"
    unfolding scross_def by blast

  have Sub : "{f1 syn x1, f2 syn x2} \<subseteq> { f1 syn x1, f1 syn x2, f2 syn x1, f2 syn x2 }"
    by blast

  show "has_sup {f1 syn x1, f2 syn x2}"
    using has_sup_subset[OF _ Z, of "{f1 syn x1, f2 syn x2}" "f1 syn x1"]
    unfolding Scross_eq
    by blast
qed

lemma scross_singleton1 :
"scross {f} Xs = f ` Xs"
  unfolding scross_def
  by blast

lemma scross_singleton2 :
"scross Fs {x} = (\<lambda> f . f x) ` Fs"
  unfolding scross_def
  by blast

(*
 * The function calculated by pcomps is "pointwise" the least upper bound of its constituent
 * functions - that is, if we pass the _same_ input (sem) to all f \<in> Fs, the result we get is <[
 * pcomps l syn sem
 *)
lemma sups_pres_pcomps_sup :
  assumes Hp : "sups_pres (set l)"
  assumes Hnemp : "l \<noteq> []"
  shows "is_sup ((\<lambda> f . f syn sem) ` (set l)) (pcomps l syn sem)" using assms
proof (induction l arbitrary: syn sem)
  case Nil
  then show ?case by auto
next
  case (Cons h1 t1)
  show ?case 
  proof(cases t1)
    case Nil' : Nil
    then show ?thesis by(auto simp add: sup_singleton)
  next
    case Cons' : (Cons h2 t2)

    have SP : "sups_pres (set t1)"
      using sups_pres_subset[OF Cons.prems(1), of "set t1"] Cons' by auto

    have Sup : "is_sup ((\<lambda>f. f syn sem) ` set t1) (pcomps t1 syn sem)"
      using Cons.IH[OF SP, of syn sem] Cons' by( auto)

    have HSup : "is_sup {h1 syn sem} (h1 syn sem)" using sup_singleton by auto

    have Conc' : "has_sup {h1 syn sem, pcomps t1 syn sem}"
    proof-

      have Eq3 : "(\<lambda>f. f sem) ` (\<lambda>f. f syn) ` set (h1 # t1) = {h1 syn sem} \<union> (\<lambda>f. f syn sem) ` set t1"
        by auto

      have Sing : "is_sup {sem} sem"
        using sup_singleton[of sem] by(auto simp add: has_sup_def)

      obtain sup' where
"is_sup ((\<lambda>f. f syn sem) ` set (h1 # t1)) sup' \<and>
     is_sup (scross ((\<lambda>f. f syn) ` set (h1 # t1)) {sem}) sup'"
        using sups_presD[OF Cons.prems(1) _ _ Sing, of sem "set (h1#t1)" "h1" "syn"]
        by auto

      then obtain s where S: "is_sup (scross ((\<lambda>f. f syn) ` set (h1 # t1)) {sem}) s"
        by(auto simp add: has_sup_def)

      have Union : "is_sup ({h1 syn sem} \<union> (\<lambda>f. f syn sem) ` set t1) s" using S 
        unfolding scross_singleton2 Eq3
        by auto

      show ?thesis using sup_union2[OF HSup Sup Union]
        by(auto simp add: has_sup_def)
    qed

    then obtain s' where S' : "is_sup {h1 syn sem, pcomps t1 syn sem} s'"
      by(auto simp add: has_sup_def)

    have Conc'' : "is_sup {h1 syn sem, pcomps t1 syn sem} [^ h1 syn sem, pcomps (h2 # t2) syn sem ^]"
      using bsup_sup[OF S' bsup_spec] unfolding Cons'  by auto

    have Eqn :
  "(insert (h2 syn sem) (insert (h1 syn sem) ((\<lambda>x. x syn sem) ` set t2))) = 
   (insert (h1 syn sem) (insert (h2 syn sem) ((\<lambda>x. x syn sem) ` set t2)))"
      by auto

    show ?thesis 
      using sup_union1[OF HSup Sup Conc'']
      by(auto simp add: Cons' Eqn)
  qed
qed

(*
 * Another key theorem, both for understanding the correctness of the specification,
 * and for practical reasons. We should expect that pcomps will be associative when
 * sups_pres holds (since then it will be calculating a "real" least upper bound in some
 * sense, and LUBs associate: sup {sup S1, x} = sup (S1 \<union> {x})
 *)
lemma pcomps_assoc :
  assumes H : "sups_pres (set l1 \<union> set l2)"
  assumes Nemp1 : "l1 \<noteq> []"
  assumes Nemp2 : "l2 \<noteq> []"
  shows "pcomps (l1 @ l2) = pcomps [pcomps l1, pcomps l2]" 
proof(rule ext; rule ext)
  fix syn sem

  obtain f1 where F1 : "f1 \<in> set l1" using Nemp1 by(cases l1; auto)

  have H1 : "sups_pres (set l1)"
    using sups_pres_subset[OF H _ _ F1]  by auto

  have Sup1: "is_sup ((\<lambda> f . f syn sem) ` (set l1)) (pcomps l1 syn sem)"
    using sups_pres_pcomps_sup[OF H1 Nemp1] by auto

  obtain f2 where F2 : "f2 \<in> set l2" using Nemp2 by(cases l2; auto)

  have H2 : "sups_pres (set l2)"
    using sups_pres_subset[OF H _ _ F2]  by auto

  have Sup2: "is_sup ((\<lambda> f . f syn sem) ` (set l2)) (pcomps l2 syn sem)"
    using sups_pres_pcomps_sup[OF H2 Nemp2] by auto

  have Unions : "set (l1 @ l2) = set l1 \<union> set l2" by auto

  have SupAll1 : "is_sup ((\<lambda> f . f syn sem) ` (set (l1 @ l2))) (pcomps (l1 @ l2) syn sem)"
    using sups_pres_pcomps_sup[of "l1 @ l2"] H Nemp1
    unfolding Unions by(auto)

  have SupAll2 : "is_sup ((\<lambda> f . f syn sem) ` ({pcomps l1, pcomps l2})) (pcomps (l1 @ l2) syn sem)"
    unfolding pcomps.simps
    using sup_union2[OF Sup1 Sup2, of "(pcomps (l1 @ l2) syn sem)"] SupAll1 
    unfolding Unions Set.image_Un
    by(auto)

  hence SupAll2' : "is_sup {pcomps l1 syn sem, pcomps l2 syn sem} (pcomps (l1 @ l2) syn sem)" by auto

  have Conc' : "[^ pcomps l1 syn sem, pcomps l2 syn sem ^] = (pcomps (l1 @ l2) syn sem)"
    using is_sup_unique[OF SupAll2' bsup_sup[OF SupAll2' bsup_spec]] by auto

  thus "pcomps (l1 @ l2) syn sem = pcomps [pcomps l1, pcomps l2] syn sem"
    unfolding pcomps.simps Conc' by auto
qed

(* 
 * The most general form of the theorem relating pcomps to sups_pres.
 * Informally, if sups_pres holds on the set of functions in a (nonempty) list l,
 * then for any nonempty set of inputs Xs with a supremum xsup,
 * the least upper bound of the _entire_ cross product of functions and inputs (Fs, Xs)
 * is given by applying pcomps l to xsup (the inputs' supremum).
 *)
lemma sups_pres_pcomps_gen :
  assumes H : "sups_pres (set l)"
  assumes Hf : "f \<in> set l"
  assumes Hxs : "finite Xs"
  assumes Hx : "x \<in> Xs"
  assumes Hsup : "is_sup Xs xsup"
  shows "is_sup (scross ((\<lambda> f . f syn) ` (set l)) Xs) (pcomps l syn xsup)" using assms

proof(induction l arbitrary: f x Xs xsup)
  case Nil
  then show ?case by auto
next
  case (Cons fh1 ft1)

  have Xs_has_sup : "has_sup Xs"
    using Cons.prems(5)
    unfolding has_sup_def
    by auto

  show ?case
  proof(cases ft1)
    case Nil' : Nil

    obtain sup' where Sup'1 : "is_sup ((\<lambda>f. f syn xsup) ` {fh1}) sup'" and
      Sup'2 : "is_sup (scross ((\<lambda>f. f syn) ` {fh1}) Xs) sup'"
      using sups_presD[OF Cons.prems(1) Cons.prems(4) Cons.prems(3) Cons.prems(5), of "{fh1}" fh1 syn]
      by auto

    have Sup'1_alt : "is_sup ((\<lambda>f. f syn xsup) ` {fh1}) (fh1 syn xsup)"
      using sup_singleton[of "(fh1 syn xsup)"] Sup'1 by auto

    hence Sup'1_eq : "sup' = (fh1 syn xsup)"
      using is_sup_unique[OF Sup'1 Sup'1_alt]
      by auto

    have Sup'2_alt : "is_sup (fh1 syn ` Xs) (fh1 syn xsup)"
      using Sup'2
      unfolding  Sup'1_eq
      by(auto simp add: scross_singleton1)

    then show ?thesis using Nil'
      by(auto simp add: scross_singleton1)
  next
    case Cons' : (Cons fh2 ft2)

    have SP : "sups_pres (set ft1)"
      using sups_pres_subset[OF Cons.prems(1), of "set ft1"] Cons' by auto

    have Tsup : "is_sup (scross ((\<lambda>f. f syn) ` set ft1) Xs) (pcomps ft1 syn xsup)"
      using Cons.IH[OF SP _ Cons.prems(3) Cons.prems(4) Cons.prems(5)]
      Cons' 
      unfolding has_sup_def
      by( auto)

    have Xs_has_sup : "has_sup Xs" using Cons.prems(5)
      unfolding has_sup_def by auto

    obtain hsup1 where Hsup1 : "is_sup (scross ((\<lambda>f. f syn) ` set (fh1 # ft1)) Xs) hsup1"
      and Hsup1_0 : "is_sup ((\<lambda>f. f syn xsup) ` set (fh1 # ft1)) hsup1"
      using sups_presD[OF Cons.prems(1) Cons.prems(4) Cons.prems(3) Cons.prems(5),of "set (fh1 # ft1)" fh1] Cons.prems
      unfolding has_sup_def by auto

    have Hd_subset : "{fh1 syn} \<subseteq> ((\<lambda>f. f syn) ` set (fh1 # ft1))"
      by auto

    have Hd_cross_subset : "scross {fh1 syn} Xs \<subseteq> (scross ((\<lambda>f. f syn) ` set (fh1 # ft1)) Xs)"
      using scross_subset[OF Hd_subset, of Xs Xs]
      by auto

    have Hd_finite : "finite (scross ((\<lambda>f. f syn) ` set (fh1 # ft1)) Xs)"
      using scross_finite[OF _ Cons.prems(3), of "((\<lambda>f. f syn) ` set (fh1 # ft1))"]
      by blast

    have Hd_nemp : "fh1 syn x \<in> scross {fh1 syn} Xs"
      using Cons.prems(4)
      unfolding scross_singleton1
      by auto

    obtain hsup2' where Hsup2'1 : "is_sup ((\<lambda>f. f syn xsup) ` {fh1}) hsup2'" and Hsup2'2 : "is_sup (scross ((\<lambda>f. f syn) ` {fh1}) Xs) hsup2'"
      using sups_presD[OF Cons.prems(1) Cons.prems(4) Cons.prems(3) Cons.prems(5), of "{fh1}" fh1 syn] Cons.prems
      by auto

    hence Hsup2'2_alt : "is_sup (scross {fh1 syn} Xs) hsup2'"
      by(auto)

    have Xsup_sup : "is_sup ((\<lambda>f. f syn xsup) ` {fh1}) (fh1 syn xsup)"
      using sup_singleton
      by auto

    have Hsup2_Xsup : "hsup2' = (fh1 syn xsup)"
      using is_sup_unique[OF Hsup2'1 Xsup_sup] by auto

    have Cross_fact : 
      "(scross ((\<lambda>f. f syn) ` set (fh1 # ft1)) Xs) =
       (scross {fh1 syn} Xs) \<union> 
       (scross ((\<lambda>f. f syn) ` set (ft1)) Xs)"
      unfolding scross_def
      by(simp; blast)

    have Hsup1' :
      "is_sup ((scross {fh1 syn} Xs) \<union> 
       (scross ((\<lambda>f. f syn) ` set (ft1)) Xs)) hsup1"
      using Hsup1 unfolding Cross_fact by auto

    have Conc' : "is_sup {hsup2', pcomps ft1 syn xsup} hsup1"
      using sup_union2[OF Hsup2'2_alt Tsup Hsup1'] Hsup2'1
      by auto

    have Conc'' : "is_sup {hsup2', pcomps ft1 syn xsup} [^ hsup2', pcomps ft1 syn xsup^]"
      using bsup_sup[OF Conc' bsup_spec] unfolding Cons'  by auto

    have Cross_fact : "(scross {fh1 syn} Xs \<union> scross (insert (fh2 syn) ((\<lambda>x. x syn) ` set ft2)) Xs) =
                       (scross (insert (fh1 syn) (insert (fh2 syn) ((\<lambda>x. x syn) ` set ft2))) Xs)"
      by(auto simp add: scross_def)

    show ?thesis
      using sup_union1[OF Hsup2'2_alt Tsup Conc''] Cons' Hsup2_Xsup Cross_fact
      by(auto)
  qed
qed

lemma sups_pres_mono :
  assumes H : "sups_pres S"
  assumes Hf : "f \<in> S"
  assumes Hxy : "x <[ y"
  shows "f syn x <[ f syn y"
proof-

  have Ysup : "is_sup {x, y} y" using Hxy
    unfolding is_sup_def is_least_def is_ub_def
    by(auto simp add: leq_refl)

  obtain supr where
    Supr1 : "is_sup ((\<lambda>f. f syn y) ` {f}) supr" and Supr2 : "is_sup (scross ((\<lambda>f. f syn) ` {f}) {x, y}) supr"
    using sups_presD[OF H _ _ Ysup, of x "{f}" f syn] Hf
    by auto

  have Supr_eq : "supr = f syn y" using Supr1
      is_sup_unique[OF sup_singleton[of "f syn y"], of supr]
    by(simp)

  have Supr_leq : "f syn x <[ supr"
    using is_supD1[OF Supr2, of "f syn x"]
    by(simp add: scross_singleton1)

  show ?thesis
    using Supr_leq unfolding Supr_eq
    by auto
qed

lemma pcomps_mono :
  assumes H : "sups_pres (set l)"
  assumes Hnemp : "f \<in> set l"
  assumes Hxy : "x <[ y"
  shows "pcomps l syn x <[ pcomps l syn y" using assms
proof(induction l arbitrary: f x y syn)
  case Nil
  then show ?case by auto
next
  case (Cons fh1 ft1)

  then show ?case 
  proof(cases ft1)
    case Nil' : Nil
    then show ?thesis using sups_pres_mono[OF Cons.prems(1) _ Cons.prems(3), of fh1 syn]
      by(auto)
  next
    case Cons' : (Cons fh2 ft2)

    have SP' : "sups_pres (set ft1)"
      using sups_pres_subset[OF Cons.prems(1), of "set ft1" fh2] unfolding Cons'
      by auto

    have Ind : "pcomps ft1 syn x <[ pcomps ft1 syn y"
      using Cons.IH[OF SP' _ Cons.prems(3), of fh2 syn] unfolding Cons'
      by auto

    have Mono : "fh1 syn x <[ fh1 syn y"
      using sups_pres_mono[OF Cons.prems(1) _ Cons.prems(3), of fh1 syn]
      by auto

    have SupX :
      "is_sup
        (scross ((\<lambda>f. f syn) ` set (fh1 # ft1)) {x})
        (pcomps (fh1 # ft1) syn x)"
      using sups_pres_pcomps_gen[OF Cons.prems(1) _ _ _ sup_singleton[of x], of fh1  x syn]
      by(auto)
  
    have SupX_tail :  "is_sup
        (scross ((\<lambda>f. f syn) ` set (ft1)) {x})
        (pcomps (ft1) syn x)"
      using sups_pres_pcomps_gen[OF SP' _ _ _ sup_singleton[of x], of fh2  x syn] unfolding Cons'
      by(auto)
  
    have RewriteX : "(scross ((\<lambda>f. f syn) ` set (fh1 # ft1)) {x}) = 
                      ({fh1 syn x} \<union> ((\<lambda> f . f syn x) ` set ft1))"
      unfolding scross_singleton2 by auto
  
    have SupX2 : "is_sup {fh1 syn x, pcomps ft1 syn x} (pcomps (fh1 # ft1) syn x)"
      using sup_union2[OF sup_singleton[of "fh1 syn x"] SupX_tail] SupX unfolding RewriteX scross_singleton2
      by(auto)
  
    have SupY :
      "is_sup
        (scross ((\<lambda>f. f syn) ` set (fh1 # ft1)) {y})
        (pcomps (fh1 # ft1) syn y)"
      using sups_pres_pcomps_gen[OF Cons.prems(1) _ _ _ sup_singleton[of y], of fh1 y syn]
      by(auto)
  
    have SupY_tail :  "is_sup
        (scross ((\<lambda>f. f syn) ` set (ft1)) {y})
        (pcomps (ft1) syn y)"
      using sups_pres_pcomps_gen[OF SP' _ _ _ sup_singleton[of y], of fh2  y syn] unfolding Cons'
      by(auto)
  
    have RewriteY : "(scross ((\<lambda>f. f syn) ` set (fh1 # ft1)) {y}) = 
                      ({fh1 syn y} \<union> ((\<lambda> f . f syn y) ` set ft1))"
      unfolding scross_singleton2 by auto
  
    have SupY2 : "is_sup {fh1 syn y, pcomps ft1 syn y} (pcomps (fh1 # ft1) syn y)"
      using sup_union2[OF sup_singleton[of "fh1 syn y"] SupY_tail] SupY unfolding RewriteY scross_singleton2
      by(auto)
  
    have Ub_conc : "is_ub {fh1 syn x, pcomps ft1 syn x} (pcomps (fh1 # ft1) syn y)"
    proof-
      have Leq1 : "fh1 syn x <[ (pcomps (fh1 # ft1) syn y)"
        using leq_trans[OF Mono, of "pcomps (fh1 # ft1) syn y"] is_supD1[OF SupY2, of "fh1 syn y"]
        by auto

      have Leq2 : "pcomps ft1 syn x <[ (pcomps (fh1 # ft1) syn y)"
        using leq_trans[OF Ind, of "(pcomps (fh1 # ft1) syn y)"]
          is_supD1[OF SupY2, of "pcomps ft1 syn y"]
        by auto

      show ?thesis
        unfolding is_ub_def using Leq1 Leq2
        by auto
    qed

    show ?thesis using is_supD2[OF SupX2 Ub_conc]
      by auto
  qed
qed

end