theory LangCompFull
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

(* TODO: do we really need the nonemptiness requirement for Fs'? *)
(* TODO: unlike scott continuity, we don't have the "closure" property
   here (that the set is closed under LUBs 
*)
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

(* for this version, syntaxes are assumed to match.
   i think this will always be the case...
*)


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

(* should we require that mapping fs preserves the upper bound?
or just its existence? 

the former would look more like Scott continuity.  but we neeed to make sure that
it is realistic for  the kinds of cases we care about
*)
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
    (* using sups_presD[OF Hf Hx, of x1 syn] *)
(*    using sups_presD[OF Hf Hx _ _, of x1 "{f1, f2}" f1]*)
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

(* maybe we need a different generalization... *)
(* conclusion should not talk about pcomps' on both sides. *)
(*
lemma sups_pres_pcomps'_gen :
  assumes H : "sups_pres (set l)"
  assumes Hf : "f \<in> set l"
  assumes Hxs : "finite Xs"
  assumes Hx : "x \<in> Xs"
  assumes Hsup : "is_sup Xs xsup"
  shows "is_sup (pcomps' l syn ` Xs) (pcomps' l syn xsup)" using assms
*)
lemma sups_pres_pcomps'_gen :
  assumes H : "sups_pres (set l)"
  assumes Hf : "f \<in> set l"
  assumes Hxs : "finite Xs"
  assumes Hx : "x \<in> Xs"
  assumes Hsup : "is_sup Xs xsup"
  shows "is_sup (scross ((\<lambda> f . f syn) ` (set l)) Xs) (pcomps' l syn xsup)" using assms

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

    have Tsup : "is_sup (scross ((\<lambda>f. f syn) ` set ft1) Xs) (pcomps' ft1 syn xsup)"
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

(* re attempting old proof *)
    have Conc' : "is_sup {hsup2', pcomps' ft1 syn xsup} hsup1"
      using sup_union2[OF Hsup2'2_alt Tsup Hsup1'] Hsup2'1
      by auto

    have Conc'' : "is_sup {hsup2', pcomps' ft1 syn xsup} [^ hsup2', pcomps' ft1 syn xsup^]"
      using bsup_sup[OF Conc' bsup_spec] unfolding Cons'  by auto
(* fh1 syn xsup = Hsup2? *)

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
    using is_sup_unfold1[OF Supr2, of "f syn x"]
    by(simp add: scross_singleton1)

  show ?thesis
    using Supr_leq unfolding Supr_eq
    by auto
qed

(* all or any? *)
(*
lemma sups_pres_monoc :
  assumes H : "sups_pres S"
  assumes Hf : "f \<in> S"
  assumes "f syn x <[ f syn y"
  shows Hxy : "x <[ y"
proof-
*)


lemma pcomps'_mono :
  assumes H : "sups_pres (set l)"
  assumes Hnemp : "f \<in> set l"
  assumes Hxy : "x <[ y"
  shows "pcomps' l syn x <[ pcomps' l syn y" using assms
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

    have SP' : "LangCompFull.sups_pres (set ft1)"
      using sups_pres_subset[OF Cons.prems(1), of "set ft1" fh2] unfolding Cons'
      by auto

    have Ind : "pcomps' ft1 syn x <[ pcomps' ft1 syn y"
      using Cons.IH[OF SP' _ Cons.prems(3), of fh2 syn] unfolding Cons'
      by auto

    have Mono : "fh1 syn x <[ fh1 syn y"
      using sups_pres_mono[OF Cons.prems(1) _ Cons.prems(3), of fh1 syn]
      by auto

    have SupX :
      "is_sup
        (scross ((\<lambda>f. f syn) ` set (fh1 # ft1)) {x})
        (pcomps' (fh1 # ft1) syn x)"
      using sups_pres_pcomps'_gen[OF Cons.prems(1) _ _ _ sup_singleton[of x], of fh1  x syn]
      by(auto)
  
    have SupX_tail :  "is_sup
        (scross ((\<lambda>f. f syn) ` set (ft1)) {x})
        (pcomps' (ft1) syn x)"
      using sups_pres_pcomps'_gen[OF SP' _ _ _ sup_singleton[of x], of fh2  x syn] unfolding Cons'
      by(auto)
  
    have RewriteX : "(scross ((\<lambda>f. f syn) ` set (fh1 # ft1)) {x}) = 
                      ({fh1 syn x} \<union> ((\<lambda> f . f syn x) ` set ft1))"
      unfolding scross_singleton2 by auto
  
    have SupX2 : "is_sup {fh1 syn x, pcomps' ft1 syn x} (pcomps' (fh1 # ft1) syn x)"
      using sup_union2[OF sup_singleton[of "fh1 syn x"] SupX_tail] SupX unfolding RewriteX scross_singleton2
      by(auto)
  
    have SupY :
      "is_sup
        (scross ((\<lambda>f. f syn) ` set (fh1 # ft1)) {y})
        (pcomps' (fh1 # ft1) syn y)"
      using sups_pres_pcomps'_gen[OF Cons.prems(1) _ _ _ sup_singleton[of y], of fh1 y syn]
      by(auto)
  
    have SupY_tail :  "is_sup
        (scross ((\<lambda>f. f syn) ` set (ft1)) {y})
        (pcomps' (ft1) syn y)"
      using sups_pres_pcomps'_gen[OF SP' _ _ _ sup_singleton[of y], of fh2  y syn] unfolding Cons'
      by(auto)
  
    have RewriteY : "(scross ((\<lambda>f. f syn) ` set (fh1 # ft1)) {y}) = 
                      ({fh1 syn y} \<union> ((\<lambda> f . f syn y) ` set ft1))"
      unfolding scross_singleton2 by auto
  
    have SupY2 : "is_sup {fh1 syn y, pcomps' ft1 syn y} (pcomps' (fh1 # ft1) syn y)"
      using sup_union2[OF sup_singleton[of "fh1 syn y"] SupY_tail] SupY unfolding RewriteY scross_singleton2
      by(auto)
  
    have Ub_conc : "is_ub {fh1 syn x, pcomps' ft1 syn x} (pcomps' (fh1 # ft1) syn y)"
    proof-
      have Leq1 : "fh1 syn x <[ (pcomps' (fh1 # ft1) syn y)"
        using leq_trans[OF Mono, of "pcomps' (fh1 # ft1) syn y"] is_sup_unfold1[OF SupY2, of "fh1 syn y"]
        by auto

      have Leq2 : "pcomps' ft1 syn x <[ (pcomps' (fh1 # ft1) syn y)"
        using leq_trans[OF Ind, of "(pcomps' (fh1 # ft1) syn y)"]
          is_sup_unfold1[OF SupY2, of "pcomps' ft1 syn y"]
        by auto

      show ?thesis
        unfolding is_ub_def using Leq1 Leq2
        by auto
    qed

    show ?thesis using is_sup_unfold2[OF SupX2 Ub_conc]
      by auto
  qed
qed

definition dominant ::
  "('a \<Rightarrow> ('b :: Mergeable) \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> ('b :: Mergeable) \<Rightarrow> 'b) set \<Rightarrow> 'a \<Rightarrow> bool"
("_ \<downharpoonleft> _ _")
where
"(f \<downharpoonleft> S x) =
 (\<forall> b . is_sup ((\<lambda> g . g x b) ` S) (f x b))"

lemma dominantI [intro] :
  assumes "\<And> b . is_sup ((\<lambda> g . g x b) ` S) (f x b)"
  shows "(f \<downharpoonleft> S x)" using assms
  unfolding dominant_def by auto

lemma dominantE [elim] :
  assumes "(f \<downharpoonleft> S x)"
  shows "is_sup ((\<lambda> g . g x b) ` S) (f x b)" using assms
  unfolding dominant_def by auto

lemma dominant_pcomps' :
  assumes Hpres : "sups_pres (set l)"
  assumes Hne : "z \<in> set l"
  assumes H : "(f \<downharpoonleft> (set l) x)"
  shows "pcomps' l x b = f x b"
proof-

  have B : "is_sup {b} b"
    using sup_singleton by auto

  have Sup1 : "is_sup (scross ((\<lambda>f. f x) ` set l) {b}) (pcomps' l x b)"
    using sups_pres_pcomps'_gen[OF Hpres Hne, of "{b}" b b x] B
    by auto

  have Rewrite1 : "(\<lambda>f. f b) ` (\<lambda>f. f x) ` set l = (\<lambda> f . f x b) ` set l"
    by blast

  have Sup2 : "is_sup ((\<lambda>f. f x b) ` set l) (pcomps' l x b)"
    using Sup1
    unfolding scross_singleton2 Rewrite1
    by auto

  have Sup2' : "is_sup ((\<lambda>f. f x b) ` set l) (f x b)"
    using dominantE[OF H, of b]
    by auto

  show ?thesis using is_sup_unique[OF Sup2 Sup2'] by auto
qed

(* has_sup of pcomps' l syn applied to xs? *)
(* do we need this? i think the idea here is to say that
pcomps' preserves sup ( ? )
*)

(*
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
      using sups_presD[OF Cons.prems(1) Cons.prems(4) Cons.prems(3) Cons.prems(5), of "{fh1}" fh1]
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
*)

end