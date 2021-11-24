theory LangCompFullAlt
imports LangCompSimple
begin

(* need a convenient way to map a set of functions
over inputs drawn from another set *)

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

(* NB: we strengthen this by addding subsets of functions Fs' *)
(* TODO: do we really need the nonemptiness requirement for Fs'? *)
definition sups_pres :: 
  "('a \<Rightarrow> ('b :: Mergeable) \<Rightarrow> 'b) set \<Rightarrow> bool" where
"sups_pres Fs =
  (\<forall> x syn Xs Fs' f .
    x \<in> Xs \<longrightarrow>
    finite Xs \<longrightarrow>
    has_sup Xs \<longrightarrow>
    Fs' \<subseteq> Fs \<longrightarrow>
    f \<in> Fs' \<longrightarrow>
    has_sup (scross ((\<lambda> f . f syn) ` Fs') Xs))"

(* for this version, syntaxes are assumed to match.
   i think this will always be the case...
*)


lemma sups_presI [intro] :
  assumes "\<And> x syn Xs Fs' f . has_sup Xs \<Longrightarrow> finite Xs \<Longrightarrow> x \<in> Xs \<Longrightarrow>  Fs' \<subseteq> Fs \<Longrightarrow> f \<in> Fs' \<Longrightarrow>
   has_sup (scross ((\<lambda> f . f syn) ` Fs') Xs)"
  shows "sups_pres Fs"
  using assms unfolding sups_pres_def by blast

(* should we require that mapping fs preserves the upper bound?
or just its existence? 

the former would look more like Scott continuity.  but we neeed to make sure that
it is realistic for  the kinds of cases we care about
*)
lemma sups_presD :
  assumes "sups_pres Fs"
  assumes "has_sup Xs"
  assumes "finite Xs"
  assumes "x \<in> Xs"
  assumes "Fs' \<subseteq> Fs"
  assumes "f \<in> Fs'"
  shows "has_sup (scross ((\<lambda> f . f syn) ` Fs') Xs)" using assms
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
  fixes Fs :: "('a \<Rightarrow> ('b :: Mergeable) \<Rightarrow> 'b) set"
  assumes H : "sups_pres Fs"
  assumes Hfin : "finite Fs"
  assumes Hsub : "Fs' \<subseteq> Fs"
  assumes Hnemp : "f \<in> Fs'"
  shows "sups_pres Fs'"
proof(rule sups_presI)
  fix syn 
  fix Xs :: "'b set"
  fix el :: "'b"
  fix Fs_sub :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) set"
  fix g :: "'a \<Rightarrow> 'b \<Rightarrow> 'b"

  assume H' : "has_sup Xs"
  assume Hfin_Xs : "finite Xs"
  assume Hnemp_Xs : "el \<in> Xs"
  assume HFs_sub : "Fs_sub \<subseteq> Fs'"
  assume HFs_nemp : "g \<in> Fs_sub"

  have HFs_sub_sub : "Fs_sub \<subseteq> Fs" using HFs_sub Hsub by auto

  obtain Rest where Rest : "Fs_sub \<union> Rest = Fs" using HFs_sub_sub by blast

  have El' : "g \<in> Fs" using HFs_sub Hsub HFs_nemp by auto

  have Rfin : "finite Rest" using Rest Hfin by auto

  have Conc' : "has_sup (scross ((\<lambda>f. f syn) ` (Fs_sub \<union> Rest)) Xs)" unfolding Rest
    using sups_presD[OF H H' Hfin_Xs Hnemp_Xs _ El'] by auto

  then obtain supr where Supr :
    "is_sup (scross ((\<lambda>f. f syn) ` (Fs_sub \<union> Rest)) Xs) supr"
    by(auto simp add: has_sup_def)

  have Subset' : "(\<lambda>f. f syn) ` Fs_sub \<subseteq> (\<lambda>f. f syn) ` Fs"
    unfolding sym[OF Rest] by blast

  have Subset : "(scross ((\<lambda>f. f syn) ` (Fs_sub)) Xs)  \<subseteq> (scross ((\<lambda>f. f syn) ` (Fs_sub \<union> Rest)) Xs)"    
    using scross_subset[OF Subset', of Xs Xs]
    unfolding Rest
    by blast

  have Nemp : "(g syn el) \<in> scross ((\<lambda>f. f syn) ` Fs_sub) Xs"
    using HFs_nemp Hnemp_Xs
    unfolding scross_def by auto

  have Hfin_full' : "finite ((\<lambda>f. f syn) ` (Fs))"
    using Hfin by blast

  have Fin_full : "finite (scross ((\<lambda>f. f syn) ` (Fs)) Xs)"
    using scross_finite[OF Hfin_full' Hfin_Xs]
    by auto

  show "has_sup (scross ((\<lambda>f. f syn) ` Fs_sub) Xs)"
    using has_sup_subset[OF _ Supr Subset Nemp] Fin_full unfolding Rest
    by auto
qed

lemma sups_pres_pair :
  assumes Hf : "sups_pres {f1, f2}"
  assumes Hx : "has_sup {x1, x2}"
  shows "has_sup {f1 syn x1, f2 syn x2}"
proof-

  have "has_sup (scross ((\<lambda>f. f syn) ` {f1, f2}) {x1, x2})"
    (* using sups_presD[OF Hf Hx, of x1 syn] *)
    using sups_presD[OF Hf Hx _ _, of x1 "{f1, f2}" f1]
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

(* do we need to generalize this using a set of states?
   - take a bunch of states having a LUB
   - cross (?)
   - hmm... what do we actually need from this?
     - pcomps associativity?
     - in Hoare logic we need to show that, when starting from states having a LUB,
       (in particular, sub lanugage L's state st is less than merged LUB language L' (st'))
       we eventually end up (?) in a state (st1 / st1') where st1 is less than st1'
 *)
lemma sups_pres_pcomps_sup :
  assumes Hp : "sups_pres (set l)"
  assumes Hnemp : "l \<noteq> []"
  shows "is_sup ((\<lambda> f . f syn sem) ` (set l)) (pcomps' l syn sem)" using assms
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

    have Sup : "is_sup ((\<lambda>f. f syn sem) ` set t1) (pcomps' t1 syn sem)"
      using Cons.IH[OF SP, of syn sem] Cons' by( auto)

    have HSup : "is_sup {h1 syn sem} (h1 syn sem)" using sup_singleton by auto

    have Conc' : "has_sup {h1 syn sem, pcomps' t1 syn sem}"
    proof-

      have Eq3 : "(\<lambda>f. f sem) ` (\<lambda>f. f syn) ` set (h1 # t1) = {h1 syn sem} \<union> (\<lambda>f. f syn sem) ` set t1"
        by auto

      have Sing : "has_sup {sem}"
        using sup_singleton[of sem] by(auto simp add: has_sup_def)

      have "has_sup (scross ((\<lambda>f. f syn) ` set (h1 # t1)) {sem})"
        using sups_presD[OF Cons.prems(1) Sing, of sem "set (h1#t1)" "h1" "syn"]
        by(auto)

      then obtain s where S: "is_sup (scross ((\<lambda>f. f syn) ` set (h1 # t1)) {sem}) s"
        by(auto simp add: has_sup_def)

      have Union : "is_sup ({h1 syn sem} \<union> (\<lambda>f. f syn sem) ` set t1) s" using S 
        unfolding scross_singleton2 Eq3
        by auto

      show ?thesis using sup_union2[OF HSup Sup Union]
        by(auto simp add: has_sup_def)
    qed

    then obtain s' where S' : "is_sup {h1 syn sem, pcomps' t1 syn sem} s'"
      by(auto simp add: has_sup_def)

    have Conc'' : "is_sup {h1 syn sem, pcomps' t1 syn sem} [^ h1 syn sem, pcomps' (h2 # t2) syn sem ^]"
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

lemma pcomps_assoc :
  assumes H : "sups_pres (set l1 \<union> set l2)"
  assumes Nemp1 : "l1 \<noteq> []"
  assumes Nemp2 : "l2 \<noteq> []"
  shows "pcomps' (l1 @ l2) = pcomps' [pcomps' l1, pcomps' l2]" 
proof(rule ext; rule ext)
  fix syn sem

  obtain f1 where F1 : "f1 \<in> set l1" using Nemp1 by(cases l1; auto)

  have H1 : "sups_pres (set l1)"
    using sups_pres_subset[OF H _ _ F1]  by auto

  have Sup1: "is_sup ((\<lambda> f . f syn sem) ` (set l1)) (pcomps' l1 syn sem)"
    using sups_pres_pcomps_sup[OF H1 Nemp1] by auto

  obtain f2 where F2 : "f2 \<in> set l2" using Nemp2 by(cases l2; auto)

  have H2 : "sups_pres (set l2)"
    using sups_pres_subset[OF H _ _ F2]  by auto

  have Sup2: "is_sup ((\<lambda> f . f syn sem) ` (set l2)) (pcomps' l2 syn sem)"
    using sups_pres_pcomps_sup[OF H2 Nemp2] by auto

  have Unions : "set (l1 @ l2) = set l1 \<union> set l2" by auto

  have SupAll1 : "is_sup ((\<lambda> f . f syn sem) ` (set (l1 @ l2))) (pcomps' (l1 @ l2) syn sem)"
    using sups_pres_pcomps_sup[of "l1 @ l2"] H Nemp1
    unfolding Unions by(auto)

  have SupAll2 : "is_sup ((\<lambda> f . f syn sem) ` ({pcomps' l1, pcomps' l2})) (pcomps' (l1 @ l2) syn sem)"
    unfolding pcomps'.simps
    using sup_union2[OF Sup1 Sup2, of "(pcomps' (l1 @ l2) syn sem)"] SupAll1 
    unfolding Unions Set.image_Un
    by(auto)

  hence SupAll2' : "is_sup {pcomps' l1 syn sem, pcomps' l2 syn sem} (pcomps' (l1 @ l2) syn sem)" by auto

  have Conc' : "[^ pcomps' l1 syn sem, pcomps' l2 syn sem ^] = (pcomps' (l1 @ l2) syn sem)"
    using is_sup_unique[OF SupAll2' bsup_sup[OF SupAll2' bsup_spec]] by auto

  thus "pcomps' (l1 @ l2) syn sem = pcomps' [pcomps' l1, pcomps' l2] syn sem"
    unfolding pcomps'.simps Conc' by auto
qed

(* has_sup of pcomps' l syn applied to xs? *)
lemma sups_pres_pcomps'_gen :
  assumes H : "sups_pres (set l)"
  assumes Hf : "f \<in> set l"
  assumes Hxs : "finite Xs"
  assumes Hx : "x \<in> Xs"
  assumes Hsup : "is_sup Xs xsup"
  shows "has_sup (pcomps' l syn ` Xs)" using assms
proof(induction l arbitrary: f x)
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
    then show ?thesis 
      using sups_presD[OF Cons.prems(1) Xs_has_sup Cons.prems(3) Cons.prems(4)
                      , of "{fh1}" fh1]
      unfolding has_sup_def
      by(auto simp add: scross_singleton1)
  next
    case Cons' : (Cons fh2 ft2)

    have SP : "sups_pres (set ft1)"
      using sups_pres_subset[OF Cons.prems(1), of "set ft1"] Cons' by auto

    obtain tsup where Tsup : "is_sup (pcomps' ft1 syn ` Xs) tsup"
      using Cons.IH[OF SP _ Hxs Hx Hsup, of fh2] Cons' 
      unfolding has_sup_def
      by( auto)

    have Xs_has_sup : "has_sup Xs" using Cons.prems(5)
      unfolding has_sup_def by auto

    obtain hsup1 where Hsup1 : "is_sup (scross ((\<lambda>f. f syn) ` set (fh1 # ft1)) Xs) hsup1"
      using sups_presD[OF Cons.prems(1) Xs_has_sup Cons.prems(3) Cons.prems(4)
                      ,of "set (fh1 # ft1)" fh1]
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

    obtain hsup2 where Hsup2 : "is_sup (scross {fh1 syn} Xs) hsup2"
      using has_sup_subset[OF Hd_finite Hsup1 Hd_cross_subset Hd_nemp]
      unfolding has_sup_def by auto

    have Cross_fact : 
      "(scross ((\<lambda>f. f syn) ` set (fh1 # ft1)) Xs) =
       (scross {fh1 syn} Xs) \<union> 
       (scross ((\<lambda>f. f syn) ` set (ft1)) Xs)"
      unfolding scross_def
      by(simp; blast)

    

    have Conc' : "has_sup ({hsup2, tsup})" sorry
(*
    proof-
(*
      have Eq3 : "(\<lambda>f. f sem) ` (\<lambda>f. f syn) ` set (h1 # t1) = {h1 syn sem} \<union> (\<lambda>f. f syn sem) ` set t1"
        by auto

      have Sing : "has_sup {sem}"
        using sup_singleton[of sem] by(auto simp add: has_sup_def)

      have "has_sup (scross ((\<lambda>f. f syn) ` set (h1 # t1)) {sem})"
        using sups_presD[OF Cons.prems(1)] Sing
        by(auto)

      then obtain s where S: "is_sup (scross ((\<lambda>f. f syn) ` set (h1 # t1)) {sem}) s"
        by(auto simp add: has_sup_def)

      have Union : "is_sup ({h1 syn sem} \<union> (\<lambda>f. f syn sem) ` set t1) s" using S 
        unfolding scross_singleton2 Eq3
        by auto

      show ?thesis using sup_union2[OF HSup Sup Union]
        by(auto simp add: has_sup_def)
*)

      have Test0 : "has_sup (scross ((\<lambda>f. f syn) ` set (fh1 # ft1)) Xs)"
        sorry

      have Test1 : "finite (scross ((\<lambda>f. f syn) ` set (fh1 # ft1)) Xs)"
        using scross_finite[OF _  Hxs, of "(\<lambda>f. f syn) ` set (fh1 # ft1)"]
        by auto

      have Test2 : "fh1 syn x \<in> scross ((\<lambda>f. f syn) ` set (fh1 # ft1)) Xs"
        unfolding sym[OF scross_alt_eq] scross_alt_def
        using Cons.prems(4)
        by(auto)

      have Test3 : "set (fh1 # ft1) \<subseteq> set (fh1 # ft1)"
        by auto

      have Test4 : "fh1 \<in> set (fh1 # ft1)" by auto

*)

    obtain cx where Cx : "is_sup ({hsup2, tsup}) cx"
      using Conc'
      unfolding has_sup_def
      by auto

    have Thing : "is_sup ((scross {fh1 syn} Xs) \<union> (pcomps' ft1 syn ` Xs)) cx"
      using sup_union1[OF Hsup2 Tsup Cx] by auto


      have Reassoc : "(scross {fh1 syn} Xs \<union> (pcomps' ft1 syn ` Xs)) =
                      (scross ((\<lambda>f. f syn) ` set (fh1 # ft1)) Xs)" 
        unfolding sym[OF scross_alt_eq] scross_alt_def
        sorry
(*      proof
        show "(\<lambda>(f, y). f y) ` ({fh1 syn} \<times> Xs) \<union> pcomps' ft1 syn ` Xs
    \<subseteq> (\<lambda>(f, y). f y) ` ((\<lambda>f. f syn) ` set (fh1 # ft1) \<times> Xs)"
          sorry
      qed
*)

      obtain final where Conc'' : "is_sup ({hsup2, tsup}) final"
        using Conc'
        unfolding has_sup_def
        by auto

      show ?thesis using (*sups_presD[OF Cons.prems(1) (*Test0 Test1 Test2 Test3 Test4*)] *)
        sup_union1[OF Hsup2 Tsup Conc''] Hsup1
        unfolding Reassoc has_sup_def
        using Cons'
        apply(simp add: pcomps'.simps)
        by auto


    then obtain s' where S' : "is_sup {hsup2, tsup} s'"
      by(auto simp add: has_sup_def)

  have Test :
  "(\<lambda>x. [^ fh1 syn x, pcomps' (ft1) syn x ^]) ` Xs \<subseteq>
    (scross {fh1 syn} Xs \<union> pcomps' (ft1) syn ` Xs)"
    sorry

  have Conc_help : "is_sup (scross {fh1 syn} Xs \<union> pcomps' ft1 syn ` Xs) s'"
    using sup_union1[OF Hsup2 Tsup]
    by auto

  have Fin_help : "finite (scross {fh1 syn} Xs \<union> pcomps' ft1 syn ` Xs)"
    sorry

  obtain ne where Ne_help : "ne \<in> ((\<lambda>x. [^ fh1 syn x, pcomps' ft1 syn x ^]) ` Xs)"
    sorry

(*
    have "\<And> x . x \<in> Xs \<Longrightarrow>
          scross {fh1 syn} Xs \<union> pcomps' ft1 syn ` Xs)"
*)
(*
    have Conc'' : "is_sup {h1 syn sem, pcomps' t1 syn sem} [^ h1 syn sem, pcomps' (h2 # t2) syn sem ^]"
      using bsup_sup[OF S' bsup_spec] unfolding Cons' 
*)
(*
    have Eqn :
  "(insert (h2 syn sem) (insert (h1 syn sem) ((\<lambda>x. x syn sem) ` set t2))) = 
   (insert (h1 syn sem) (insert (h2 syn sem) ((\<lambda>x. x syn sem) ` set t2)))"
      by auto
*)
    show ?thesis using has_sup_subset[OF Fin_help Conc_help Test Ne_help]
      by(auto simp add: Cons')
  qed
qed


    have SP : "sups_pres (set ft)"
      using sups_pres_subset[OF Cons.prems(1), of "set ft"] Cons' by auto
  
    have Sup : "is_sup ((\<lambda>f. f syn sem) ` set t1) (pcomps' t1 syn sem)"
      using Cons.IH[OF SP, of syn sem] Cons' by( auto)
  
    have HSup : "is_sup {h1 syn sem} (h1 syn sem)" using sup_singleton by auto

qed

(*
proof(rule is_sup_intro)
  fix y
  assume Y_in : "y \<in> scross ((\<lambda>f. f syn) ` set l) Xs"

  have Hsup' : "has_sup Xs" using Hsup
    unfolding has_sup_def by auto

  show "y <[ pcomps' l syn xsup"
    using sups_presD[OF H Hsup' Hxs Hx, of syn]
*)  

(*
  Would a more general version of this be useful?
  This one should be sufficient to prove the Hoare rule.
*)
(*
lemma sups_pres_step :
  assumes H : "sups_pres (set l)"
  assumes Hf : "f \<in> set l"
  assumes Hleq : "x1 <[ x2"
  shows "f syn x1 <[ pcomps' l syn x2" 
proof-

  have "is_sup {x1, x2} x2"
  proof(rule is_sup_intro)
    fix x
    show "x \<in> {x1, x2} \<Longrightarrow> x <[ x2"
      using Hleq leq_refl[of x2] by auto
  next
    fix x'
    show "is_ub {x1, x2} x' \<Longrightarrow> x2 <[ x'"
      unfolding is_ub_def
      by auto
  qed

  hence Sup : "has_sup {x1, x2}" unfolding has_sup_def by auto

  have Sup1 : "has_sup (scross ((\<lambda>f. f syn) ` set l) {x1, x2})"
    using sups_presD[OF H Sup]
    by auto
    *)


end