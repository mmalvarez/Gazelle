theory Composition
imports Composition_Core "../Lifter/Lifter"
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
(* Original definition. We are generalizing it here to allow talking about sups_pres
 * restricted to specific subsets of the input space (e.g. ok_S) *)

(* YOU ARE HERE
 * TODO: we need to further restrict sups_pres to allow the "S" set to depend on syntax.
 *)
(*
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
*)

(*
definition sups_pres ::
  "('a \<Rightarrow> ('b :: Mergeable) \<Rightarrow> 'b) set \<Rightarrow> ('b :: Mergeable) set \<Rightarrow> bool" where
"sups_pres Fs S =
  (\<forall> x sup syn Xs Fs' f .
    x \<in> Xs \<longrightarrow>
    Xs \<subseteq> S \<longrightarrow>
    finite Xs \<longrightarrow>
    is_sup Xs sup \<longrightarrow>
    sup \<in> S \<longrightarrow>
    Fs' \<subseteq> Fs \<longrightarrow>
    f \<in> Fs' \<longrightarrow>
    (\<exists> sup' . is_sup ((\<lambda> f . f syn sup) ` Fs') sup' \<and>
     is_sup (scross ((\<lambda> f . f syn) ` Fs') Xs) sup' \<and>
     sup' \<in> S))"
*)

definition sups_pres ::
  "('a \<Rightarrow> ('b :: Mergeable) \<Rightarrow> 'b) set \<Rightarrow> ('a \<Rightarrow> ('b :: Mergeable) set) \<Rightarrow> bool" where
"sups_pres Fs S =
  (\<forall> x sup syn Xs Fs' f .
    x \<in> Xs \<longrightarrow>
    Xs \<subseteq> S syn \<longrightarrow>
    finite Xs \<longrightarrow>
    is_sup Xs sup \<longrightarrow>
    sup \<in> S syn \<longrightarrow>
    Fs' \<subseteq> Fs \<longrightarrow>
    f \<in> Fs' \<longrightarrow>
    (\<exists> sup' . is_sup ((\<lambda> f . f syn sup) ` Fs') sup' \<and>
     is_sup (scross ((\<lambda> f . f syn) ` Fs') Xs) sup' \<and>
     sup' \<in> S syn))"


lemma sups_presI [intro] :
  assumes "\<And> x sup syn Xs Fs' f . 
           x \<in> Xs \<Longrightarrow>
           Xs \<subseteq> S syn \<Longrightarrow>
           finite Xs \<Longrightarrow> 
           is_sup Xs sup \<Longrightarrow>
           sup \<in> S syn \<Longrightarrow>
          Fs' \<subseteq> Fs \<Longrightarrow>
          f \<in> Fs' \<Longrightarrow>
          (\<exists> sup' . is_sup ((\<lambda> f . f syn sup) ` Fs') sup' \<and>
     is_sup (scross ((\<lambda> f . f syn) ` Fs') Xs) sup' \<and>
     sup' \<in> S syn)"
  shows "sups_pres Fs S"
  using assms unfolding sups_pres_def by blast

lemma sups_presD :
  assumes "sups_pres Fs S"
  assumes "x \<in> Xs"
  assumes "Xs \<subseteq> S syn"
  assumes "finite Xs"
  assumes "is_sup Xs sp"
  assumes "sp \<in> S syn"
  assumes "Fs' \<subseteq> Fs"
  assumes "f \<in> Fs'"

  shows "(\<exists> sup' . is_sup ((\<lambda> f . f syn sp) ` Fs') sup' \<and>
           is_sup (scross ((\<lambda> f . f syn) ` Fs') Xs) sup' \<and>
     sup' \<in> S syn)" using assms
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
(* TODO: what about subsetting of S? supersetting of S?
   something tells me that one isn't true though.
*)
lemma sups_pres_subset :
  fixes Fs :: "('a \<Rightarrow> ('b :: Mergeable) \<Rightarrow> 'b) set"
  assumes H : "sups_pres Fs S"
  assumes Hfin : "finite Fs"
  assumes Hsub : "Fs' \<subseteq> Fs"
  assumes Hnemp : "f \<in> Fs'"
  shows "sups_pres Fs' S"
proof(rule sups_presI)
  fix el :: "'b"
  fix sup1 :: "'b"
  fix syn 
  fix Xs :: "'b set"
  fix Fs_sub :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) set"
  fix f

  assume Hnemp_Xs : "el \<in> Xs"
  assume Subs : "Xs \<subseteq> S syn"
  assume Hfin_Xs : "finite Xs"
  assume H' : "is_sup Xs sup1"
  assume H'' : "sup1 \<in> S syn"
  assume Hfs_sub : "Fs_sub \<subseteq> Fs'"
  assume Hnemp_Fs_sub : "f \<in> Fs_sub"

  obtain Rest where Rest : "Fs' \<union> Rest = Fs" using Hsub by blast

  have Rfin : "finite Rest" using Rest Hfin by auto

  show  "\<exists>sup'.
          is_sup ((\<lambda>f. f syn sup1) ` Fs_sub) sup' \<and>
          is_sup (scross ((\<lambda>f. f syn) ` Fs_sub) Xs) sup' \<and> sup' \<in> S syn"
    using sups_presD[OF H Hnemp_Xs Subs Hfin_Xs H', of Fs_sub f] Hfs_sub Hnemp_Fs_sub Hsub H''
    unfolding has_sup_def
    by(auto)
qed

(* TODO: we weren't using this lemma, but the fact that
 * we couldn't prove it under our new definition may be a bad sign.
 *)
(*
lemma sups_pres_pair :
  assumes Hf : "sups_pres {f1, f2} S"
  assumes Hsup : "is_sup {x1, x2} sp"
  assumes Hsup_in : "sp \<in> S"
  assumes Hx1 : "x1 \<in> S"
  assumes Hx2 : "x2 \<in> S"
  shows "\<exists> sp' . is_sup {f1 syn x1, f2 syn x2} sp' \<and> sp' \<in> S"
proof-

  have Hx12 : "{x1, x2} \<subseteq> S"
    using Hx1 Hx2 by auto

  obtain sup' where Sup' : "is_sup ((\<lambda>f. f syn sp) ` {f1, f2}) sup'"
    and Sup'_full : "is_sup (scross ((\<lambda>f. f syn) ` {f1, f2}) {x1, x2}) sup'"
    and Sup'_S : "sup' \<in> S"
    using sups_presD[OF Hf _ Hx12 _ Hsup Hsup_in, of x1 "{f1, f2}"]
    by auto

  then obtain z where Z: "is_sup (scross ((\<lambda>f. f syn) ` {f1, f2}) {x1, x2}) z"
    unfolding has_sup_def by auto

  have Scross_eq : 
    "(scross ((\<lambda>f. f syn) ` {f1, f2}) {x1, x2}) =
      { f1 syn x1, f1 syn x2, f2 syn x1, f2 syn x2 }"
    unfolding scross_def by blast

  have Sub : "{f1 syn x1, f2 syn x2} \<subseteq> { f1 syn x1, f1 syn x2, f2 syn x1, f2 syn x2 }"
    by blast
(* stronger closure property needed here? or can we play around with another piece of the thm
*)
  show "\<exists>sp'. is_sup {f1 syn x1, f2 syn x2} sp' \<and> sp' \<in> S"
(*
    using has_sup_subset[OF _ Z, of "{f1 syn x1, f2 syn x2}" "f1 syn x1"] *)
    using Sup'_full
    unfolding Scross_eq
    by blast
qed
*)

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

lemma sups_pres_pcomps_sup' :
  assumes Hp : "sups_pres (set l) S"
  assumes Hnemp : "l \<noteq> []"
  assumes Hsem : "sem \<in> S syn"
  shows "is_sup ((\<lambda> f . f syn sem) ` (set l)) (pcomps l syn sem) \<and> (pcomps l syn sem) \<in> S syn" using assms
proof (induction l arbitrary: syn sem)
  case Nil
  then show ?case by auto
next
  case (Cons h1 t1)
  show ?case 
  proof(cases t1)
    case Nil' : Nil

    have SP : "sups_pres ({h1}) S"
      using sups_pres_subset[OF Cons.prems(1), of "set t1"] Cons.prems Nil'
      by auto

    obtain sup' where Sup' : "is_sup ((\<lambda>f. f syn sem) ` {h1}) sup'" 
       "is_sup (scross ((\<lambda>f. f syn) ` {h1}) {sem}) sup'"
       "sup' \<in> S syn"
      using Cons.prems sups_presD[OF SP, of "sem" "{sem}" syn "sem" "{h1}" "h1"]
      by(auto simp add: sup_singleton)

    have Eq : "sup' = h1 syn sem"
      
      using is_sup_unique[OF Sup'(2)] sup_singleton[of "h1 syn sem"]
      by(auto simp add: scross_def)

    then show ?thesis using Nil' Cons.prems Sup'(3)
      by(auto simp add: sup_singleton scross_def)
  next
    case Cons' : (Cons h2 t2)

    have SP : "sups_pres (set t1) S"
      using sups_pres_subset[OF Cons.prems(1), of "set t1"] Cons' by auto

    have Sup : "is_sup ((\<lambda>f. f syn sem) ` set t1) (pcomps t1 syn sem)"
      using Cons.IH[OF SP] Cons.prems Cons' by( auto)

    have HSup : "is_sup {h1 syn sem} (h1 syn sem)" using sup_singleton by auto


    have Eq3 : "(\<lambda>f. f sem) ` (\<lambda>f. f syn) ` set (h1 # t1) = {h1 syn sem} \<union> (\<lambda>f. f syn sem) ` set t1"
      by auto

    have Sing : "is_sup {sem} sem"
      using sup_singleton[of sem] by(auto simp add: has_sup_def)

    have Sing_sem : "{sem} \<subseteq> S syn" using Cons.prems by auto

    obtain sup' where Sup' :
      "is_sup ((\<lambda>f. f syn sem) ` set (h1 # t1)) sup'"
       "is_sup (scross ((\<lambda>f. f syn) ` set (h1 # t1)) {sem}) sup'"
       "sup' \<in> S syn"
      using sups_presD[OF Cons.prems(1) _ Sing_sem _ Sing, of sem "set (h1#t1)" "h1"] Hsem Cons.prems
      by auto

    then obtain s where S: "is_sup (scross ((\<lambda>f. f syn) ` set (h1 # t1)) {sem}) s"
      by(auto simp add: has_sup_def)

    have Union : "is_sup ({h1 syn sem} \<union> (\<lambda>f. f syn sem) ` set t1) s" using S 
      unfolding scross_singleton2 Eq3
      by auto

    have Conc' : "has_sup {h1 syn sem, pcomps t1 syn sem}"
      using sup_union2[OF HSup Sup Union]
      by(auto simp add: has_sup_def)

    then obtain s' where S' : "is_sup {h1 syn sem, pcomps t1 syn sem} s'"
      by(auto simp add: has_sup_def)

    have Conc'' : "is_sup {h1 syn sem, pcomps t1 syn sem} [^ h1 syn sem, pcomps (h2 # t2) syn sem ^]"
      using bsup_sup[OF S' bsup_spec] unfolding Cons'  by auto

    have Eqn :
  "(insert (h2 syn sem) (insert (h1 syn sem) ((\<lambda>x. x syn sem) ` set t2))) = 
   (insert (h1 syn sem) (insert (h2 syn sem) ((\<lambda>x. x syn sem) ` set t2)))"
      by auto

    have Conc1 : "is_sup ((\<lambda>f. f syn sem) ` set (h1 # t1)) (pcomps (h1 # t1) syn sem)"
      using sup_union1[OF HSup Sup Conc'']
      by(auto simp add: Cons' Eqn)


    have Conc2 : "pcomps (h1 # t1) syn sem \<in> S syn"
      using is_sup_unique[OF Sup'(1) Conc1] Sup'(3)
      by(auto)

    show ?thesis using Conc1 Conc2 by auto
  qed
qed


lemma sups_pres_pcomps_sup1 :
  assumes Hp : "sups_pres (set l) S"
  assumes Hnemp : "l \<noteq> []"
  assumes Hsem : "sem \<in> S syn"
  shows "is_sup ((\<lambda> f . f syn sem) ` (set l)) (pcomps l syn sem)" using assms
    sups_pres_pcomps_sup'
  by fast

lemma sups_pres_pcomps_sup2 :
  assumes Hp : "sups_pres (set l) S"
  assumes Hnemp : "l \<noteq> []"
  assumes Hsem : "sem \<in> S syn"
  shows "(pcomps l syn sem) \<in> S syn" using assms
    sups_pres_pcomps_sup'
  by fast

(*
 * Another key theorem, both for understanding the correctness of the specification,
 * and for practical reasons. We should expect that pcomps will be associative when
 * sups_pres holds (since then it will be calculating a "real" least upper bound in some
 * sense, and LUBs associate: sup {sup S1, x} = sup (S1 \<union> {x})
 *)
lemma pcomps_assoc :
  assumes H : "sups_pres (set l1 \<union> set l2) S"
  assumes Nemp1 : "l1 \<noteq> []"
  assumes Nemp2 : "l2 \<noteq> []"
  assumes X : "x \<in> S syn"
  shows "pcomps (l1 @ l2) syn x = pcomps [pcomps l1, pcomps l2] syn x" 
(*proof(rule ext; rule ext) *)
proof-

  obtain f1 where F1 : "f1 \<in> set l1" using Nemp1 by(cases l1; auto)

  have H1 : "sups_pres (set l1) S"
    using sups_pres_subset[OF H _ _ F1]  by auto

  have Sup1: "is_sup ((\<lambda> f . f syn x) ` (set l1)) (pcomps l1 syn x)"
    "(pcomps l1 syn x) \<in> S syn"
    using sups_pres_pcomps_sup'[OF H1 Nemp1 X] by auto

  obtain f2 where F2 : "f2 \<in> set l2" using Nemp2 by(cases l2; auto)

  have H2 : "sups_pres (set l2) S"
    using sups_pres_subset[OF H _ _ F2]  by auto

  have Sup2: "is_sup ((\<lambda> f . f syn x) ` (set l2)) (pcomps l2 syn x)" "(pcomps l2 syn x) \<in> S syn"
    using sups_pres_pcomps_sup'[OF H2 Nemp2 X] by auto

  have Unions : "set (l1 @ l2) = set l1 \<union> set l2" by auto

  have SupAll1 : "is_sup ((\<lambda> f . f syn x) ` (set (l1 @ l2))) (pcomps (l1 @ l2) syn x)"
    "(pcomps (l1 @ l2) syn x) \<in> S syn"
    using sups_pres_pcomps_sup'[of "l1 @ l2"] H Nemp1 X
    unfolding Unions by(auto)

  have SupAll2 : "is_sup ((\<lambda> f . f syn x) ` ({pcomps l1, pcomps l2})) (pcomps (l1 @ l2) syn x)"
    unfolding pcomps.simps
    using sup_union2[OF Sup1(1) Sup2(1), of "(pcomps (l1 @ l2) syn x)"] SupAll1 X
    unfolding Unions Set.image_Un
    by(auto)

  hence SupAll2' : "is_sup {pcomps l1 syn x, pcomps l2 syn x} (pcomps (l1 @ l2) syn x)" by auto

  have Conc' : "[^ pcomps l1 syn x, pcomps l2 syn x ^] = (pcomps (l1 @ l2) syn x)"
    using is_sup_unique[OF SupAll2' bsup_sup[OF SupAll2' bsup_spec]] by auto

  thus "pcomps (l1 @ l2) syn x = pcomps [pcomps l1, pcomps l2] syn x"
    unfolding pcomps.simps Conc' by auto
qed

(* 
 * The most general form of the theorem relating pcomps to sups_pres.
 * Informally, if sups_pres holds on the set of functions in a (nonempty) list l,
 * then for any nonempty set of inputs Xs with a supremum xsup,
 * the least upper bound of the _entire_ cross product of functions and inputs (Fs, Xs)
 * is given by applying pcomps l to xsup (the inputs' supremum).
 *)
lemma sups_pres_pcomps_gen' :
  assumes H : "sups_pres (set l) S"
  assumes Hf : "f \<in> set l"
  assumes Hxs : "finite Xs"
  assumes Hx : "x \<in> Xs"
  assumes Hsub : "Xs \<subseteq> S syn"
  assumes Hsup : "is_sup Xs xsup"
  assumes Hsup_in : "xsup \<in> S syn"
  shows "is_sup (scross ((\<lambda> f . f syn) ` (set l)) Xs) (pcomps l syn xsup) \<and> pcomps l syn xsup \<in> S syn" using assms

proof(induction l arbitrary: f x Xs xsup)
  case Nil
  then show ?case by auto
next
  case (Cons fh1 ft1)

  have Xs_has_sup : "has_sup Xs"
    using Cons.prems(6)
    unfolding has_sup_def
    by auto

  show ?case
  proof(cases ft1)
    case Nil' : Nil

    obtain sup' where Sup'1 : "is_sup ((\<lambda>f. f syn xsup) ` {fh1}) sup'" and
      Sup'2 : "is_sup (scross ((\<lambda>f. f syn) ` {fh1}) Xs) sup'" and
      Sup'3 : "sup' \<in> S syn"
      using sups_presD[OF Cons.prems(1) Cons.prems(4) Cons.prems(5) Cons.prems(3) Cons.prems(6) Cons.prems(7), of "{fh1}" fh1]
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

    then show ?thesis using Nil' Sup'3 Sup'1_eq
      by(auto simp add: scross_singleton1)
  next
    case Cons' : (Cons fh2 ft2)

    have SP : "sups_pres (set ft1) S"
      using sups_pres_subset[OF Cons.prems(1), of "set ft1"] Cons' by auto

    have Tsup : "is_sup (scross ((\<lambda>f. f syn) ` set ft1) Xs) (pcomps ft1 syn xsup)" and Tsup_in : "pcomps ft1 syn xsup \<in> S syn"
      using Cons.IH[OF SP _ Cons.prems(3) Cons.prems(4) Cons.prems(5) Cons.prems(6) Cons.prems(7)]
      Cons' 
      unfolding has_sup_def
      by( auto)

    have Xs_has_sup : "has_sup Xs" using Cons.prems(6)
      unfolding has_sup_def by auto

    obtain hsup1 where Hsup1 : "is_sup (scross ((\<lambda>f. f syn) ` set (fh1 # ft1)) Xs) hsup1"
      and Hsup1_0 : "is_sup ((\<lambda>f. f syn xsup) ` set (fh1 # ft1)) hsup1"
      using sups_presD[OF Cons.prems(1) Cons.prems(4) Cons.prems(5) Cons.prems(3) Cons.prems(6),of "set (fh1 # ft1)" fh1] Cons.prems
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
      and Hsup2'_3 : "hsup2' \<in> S syn"
      using sups_presD[OF Cons.prems(1) Cons.prems(4) Cons.prems(5) Cons.prems(3) Cons.prems(6), of "{fh1}" fh1] Cons.prems
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

    have Conc1 : "is_sup (scross ((\<lambda>f. f syn) ` set (fh1 # ft1)) Xs)
     (pcomps (fh1 # ft1) syn xsup)"
      using sup_union1[OF Hsup2'2_alt Tsup Conc''] Cons' Hsup2_Xsup Cross_fact
      by auto

    obtain sup' where Sup' :
      "is_sup (scross ((\<lambda>f. f syn) ` set (fh1 # ft1)) Xs) sup'" and
      Sup'_In : "sup' \<in> S syn"
      using sups_presD[OF Cons.prems(1) Cons.prems(4) Cons.prems(5) Cons.prems(3) Cons.prems(6) Cons.prems(7), of "set (fh1 # ft1)" fh1]
      by auto

    have Sup'_Eq :
      "sup' =  (pcomps (fh1 # ft1) syn xsup)"
      using is_sup_unique[OF Conc1 Sup']
      by auto

    have Conc2 : "pcomps (fh1 # ft1) syn xsup \<in> S syn"
      using Sup'_In Sup'_Eq
      by auto

    show ?thesis
      using Conc1 Conc2
      by(auto)
  qed
qed

lemma sups_pres_pcomps_gen1 :
  assumes H : "sups_pres (set l) S"
  assumes Hf : "f \<in> set l"
  assumes Hxs : "finite Xs"
  assumes Hx : "x \<in> Xs"
  assumes Hsub : "Xs \<subseteq> S syn"
  assumes Hsup : "is_sup Xs xsup"
  assumes Hsup_in : "xsup \<in> S syn"
  shows "is_sup (scross ((\<lambda> f . f syn) ` (set l)) Xs) (pcomps l syn xsup)"
  using assms sups_pres_pcomps_gen'[OF H Hf Hxs Hx Hsub Hsup]
  by auto

lemma sups_pres_pcomps_gen2 :
  assumes H : "sups_pres (set l) S"
  assumes Hf : "f \<in> set l"
  assumes Hxs : "finite Xs"
  assumes Hx : "x \<in> Xs"
  assumes Hsub : "Xs \<subseteq> S syn"
  assumes Hsup : "is_sup Xs xsup"
  assumes Hsup_in : "xsup \<in> S syn"
  shows "pcomps l syn xsup \<in> S syn" using assms
  using assms sups_pres_pcomps_gen'[OF H Hf Hxs Hx Hsub Hsup]
  by auto

lemma sups_pres_mono :
  assumes H : "sups_pres Fs S"
  assumes Hf : "f \<in> Fs"
  assumes Hx_in : "x \<in> S syn"
  assumes Hy_in : "y \<in> S syn"
  assumes Hxy : "x <[ y"
  shows "f syn x <[ f syn y"
proof-

  have Ysup : "is_sup {x, y} y" using Hxy
    unfolding is_sup_def is_least_def is_ub_def
    by(auto simp add: leq_refl)

  obtain supr where
    Supr1 : "is_sup ((\<lambda>f. f syn y) ` {f}) supr" and Supr2 : "is_sup (scross ((\<lambda>f. f syn) ` {f}) {x, y}) supr"
    using sups_presD[OF H _ _ _ Ysup, of x syn "{f}"] Hf Hx_in Hy_in
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
  assumes H : "sups_pres (set l) S"
  assumes Hnemp : "f \<in> set l"
  assumes Hx_in : "x \<in> S syn"
  assumes Hy_in : "y \<in> S syn"
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
    then show ?thesis 
      using sups_pres_mono[OF Cons.prems(1) _ Cons.prems(3) Cons.prems(4), of fh1] Cons.prems
      by(auto)
  next
    case Cons' : (Cons fh2 ft2)

    have SP' : "sups_pres (set ft1) S"
      using sups_pres_subset[OF Cons.prems(1), of "set ft1" fh2] unfolding Cons'
      by auto

    have Ind : "pcomps ft1 syn x <[ pcomps ft1 syn y"
      using Cons.IH[OF SP' _ Cons.prems(3) Cons.prems(4), of fh2] Cons.prems unfolding Cons' 
      by auto

    have Mono : "fh1 syn x <[ fh1 syn y"
      using sups_pres_mono[OF Cons.prems(1) _ Cons.prems(3) Cons.prems(4) Cons.prems(5), of fh1]
      by auto

    have SupX :
      "is_sup
        (scross ((\<lambda>f. f syn) ` set (fh1 # ft1)) {x})
        (pcomps (fh1 # ft1) syn x)"
      using sups_pres_pcomps_gen1[OF Cons.prems(1) _ _ _ _ sup_singleton[of x], of fh1 x syn]
        Cons.prems(3)
      by(auto)
  
    have SupX_tail :  "is_sup
        (scross ((\<lambda>f. f syn) ` set (ft1)) {x})
        (pcomps (ft1) syn x)"
      using sups_pres_pcomps_gen1[OF SP' _ _ _ _ sup_singleton[of x], of fh2  x syn] Cons.prems(3) unfolding Cons'
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
      using sups_pres_pcomps_gen1[OF Cons.prems(1) _ _ _ _ sup_singleton[of y], of fh1 y syn]
        Cons.prems(4)
      by(auto)
  
    have SupY_tail :  "is_sup
        (scross ((\<lambda>f. f syn) ` set (ft1)) {y})
        (pcomps (ft1) syn y)"
      using sups_pres_pcomps_gen1[OF SP' _ _ _ _ sup_singleton[of y], of fh2  y syn]
        Cons.prems(4)
      unfolding Cons'
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


lemma pcomps_comm' :
  assumes H : "sups_pres {f1, f2} S"
  assumes Hx : "x \<in> S syn"
  shows "pcomps [f1, f2] syn x = pcomps [f2, f1] syn x" 
proof-

  have H0 : "sups_pres (set [f1, f2]) S" using H
    by simp

  have Comm : "set [f1, f2] = set [f2, f1]"
    by(auto)

  have H1 : "sups_pres (set [f2, f1]) S" using H Comm
    by(simp)

  have SupAll1 : "is_sup ((\<lambda> f . f syn x) ` (set [f1, f2])) (pcomps [f1, f2] syn x)"
    using sups_pres_pcomps_sup'[OF H0, of x syn] Hx
    by auto

  have SupAll2 : "is_sup ((\<lambda> f . f syn x) ` (set [f2, f1])) (pcomps [f2, f1] syn x)"
    using sups_pres_pcomps_sup'[OF H1, of x syn] Hx
    by auto

  hence SupAll2' : "is_sup ((\<lambda> f . f syn x) ` (set [f1, f2])) (pcomps [f2, f1] syn x)"
    unfolding Comm by simp

  thus "(pcomps [f1, f2] syn x) = (pcomps [f2, f1] syn x)"
    using is_sup_unique[OF SupAll1 SupAll2'] by simp
qed

lemma sups_pres_pcomps_fuse :
  assumes H : "sups_pres (set l1 \<union> set l2) S"
  assumes Hnemp1 : "l1 \<noteq> []"
  assumes Hnemp2 : "l2 \<noteq> []"
  shows "sups_pres {pcomps l1, pcomps l2} S"
proof(rule sups_presI)
  fix el :: "'b"
  fix sup1 :: "'b"
  fix syn 
  fix Xs :: "'b set"
  fix Fs_sub :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) set"
  fix f

  assume Hnemp_Xs : "el \<in> Xs"
  assume HXs_S : "Xs \<subseteq> S syn"
  assume Hfin_Xs : "finite Xs"
  assume H' : "is_sup Xs sup1"
  assume H'_in : "sup1 \<in> S syn"
  assume Hfs_sub : "Fs_sub \<subseteq> {pcomps l1, pcomps l2}"
  assume Hnemp_Fs_sub : "f \<in> Fs_sub"

  have Pres' : "sups_pres (set (l1 @ l2)) S" using H by simp

  obtain f1 where F1 : "f1 \<in> set l1" using Hnemp1
    by(cases l1; auto)

  have Pres1 : "sups_pres (set l1) S"
    using sups_pres_subset[OF H _ _ F1] by auto

  obtain f2 where F2: "f2 \<in> set l2" using Hnemp2
    by(cases l2; auto)

  have Pres2 : "sups_pres (set l2) S"
    using sups_pres_subset[OF H _ _ F2] by auto

  obtain g where Nemp' : "g \<in> set (l1 @ l2)"
    using Hnemp1 by(cases l1; auto)

  have Sup : "is_sup
     (scross ((\<lambda>f. f syn) ` set (l1 @ l2)) Xs)
     (pcomps (l1 @ l2) syn sup1)"
    using sups_pres_pcomps_gen1[OF Pres' Nemp' Hfin_Xs Hnemp_Xs HXs_S H' H'_in]
    by simp

  have Scross_eq : 
    "(scross ((\<lambda>f. f syn) ` set (l1 @ l2)) Xs) =
     ((scross ((\<lambda>f. f syn) ` (set l1)) Xs) \<union> (scross ((\<lambda>f. f syn) ` (set l2)) Xs))"
    unfolding scross_def
    by(auto)

  have Sup_alt : "is_sup
     ((scross ((\<lambda>f. f syn) ` (set l1)) Xs) \<union> (scross ((\<lambda>f. f syn) ` (set l2)) Xs))
     (pcomps (l1 @ l2) syn sup1)" using Sup unfolding Scross_eq
    by simp

  have Eq: "\<And> z' . z' \<in> S syn \<Longrightarrow> pcomps (l1 @ l2) syn z' = pcomps [pcomps l1, pcomps l2] syn z'"
    using pcomps_assoc[OF H Hnemp1 Hnemp2] by simp

  have Sup1 : "is_sup (scross ((\<lambda>f. f syn) ` set l1) Xs) (pcomps l1 syn sup1)"
    using sups_pres_pcomps_gen1[OF Pres1 F1 Hfin_Xs Hnemp_Xs HXs_S H' H'_in]
    by auto

  have Sup1_in : "(pcomps l1 syn sup1) \<in> S syn"
    using sups_pres_pcomps_gen2[OF Pres1 F1 Hfin_Xs Hnemp_Xs HXs_S H' H'_in]
    by auto

  have Sup2 : "is_sup (scross ((\<lambda>f. f syn) ` set l2) Xs) (pcomps l2 syn sup1)"
    using sups_pres_pcomps_gen1[OF Pres2 F2 Hfin_Xs Hnemp_Xs HXs_S H' H'_in]
    by auto

  have Sup2_in : "(pcomps l2 syn sup1) \<in> S syn"
    using sups_pres_pcomps_gen2[OF Pres2 F2 Hfin_Xs Hnemp_Xs HXs_S H' H'_in]
    by auto

  have Sup12 : "is_sup ((\<lambda>f. f syn sup1) ` {pcomps l1, pcomps l2}) (pcomps (l1 @ l2) syn sup1)"
    using sup_union2[OF Sup1 Sup2 Sup_alt] sup_union2[OF _ _ Sup_alt]
    by simp

  consider (Emp) "Fs_sub = {}" |
           (L1) "Fs_sub = {pcomps l1}" |
           (L2) "Fs_sub = {pcomps l2}" |
           (L1_2) "Fs_sub = {pcomps l1, pcomps l2}"
    using Hfs_sub by blast
  then show "\<exists>sup'.
          is_sup ((\<lambda>f. f syn sup1) ` Fs_sub) sup' \<and>
          is_sup (scross ((\<lambda>f. f syn) ` Fs_sub) Xs) sup' \<and> sup' \<in> S syn"
  proof cases
    case Emp
    then show ?thesis using Hnemp_Fs_sub by auto
  next
(* TODO: this should be a lemma *)
    case L1

    have C1 : "is_sup ((\<lambda>f. f syn sup1) ` Fs_sub) (pcomps l1 syn sup1)"
      using sup_singleton unfolding L1 by auto

    have Pcomps_singleton : "(\<lambda>f. f syn) ` {pcomps l1} = {pcomps l1 syn}"
      by auto

    have L1' : "(scross ((\<lambda>f. f syn) ` Fs_sub) Xs) = pcomps l1 syn ` Xs"
      unfolding L1 Pcomps_singleton scross_singleton1 by simp

    have C2 : "is_sup ((pcomps l1 syn) ` Xs) (pcomps l1 syn sup1)"
    proof(rule is_supI)
      fix y
      assume Y: "y \<in> pcomps l1 syn ` Xs"

      then obtain x where Xin : "x \<in> Xs" and Xy : "pcomps l1 syn x = y"
        by blast

      have Xin' : "x \<in> S syn" using HXs_S Xin by auto

      have Leq1 : "x <[ sup1" using is_supD1[OF H' Xin] by simp

      show "y <[ pcomps l1 syn sup1"
        using pcomps_mono[OF Pres1 F1 Xin' H'_in Leq1]
        unfolding sym[OF Xy] by simp
    next
      fix y'

      assume Y' : "is_ub (pcomps l1 syn ` Xs) y'"

      have Ub' : "is_ub (scross ((\<lambda>f. f syn) ` set l1) Xs) y'"
      proof
        fix z'
        assume Z': "z' \<in> scross ((\<lambda>f. f syn) ` set l1) Xs"

        obtain fz z where Zin : "z \<in> Xs" and Fzin : "fz \<in> set l1" and Cross : "z' = fz syn z"
          using Z' unfolding scross_def by blast

        have Leq1 : "z <[ sup1" using is_supD1[OF H' Zin] by simp

        have PresX : "sups_pres (set [fz]) S"
          using sups_pres_subset[OF Pres1, of "set [fz]"] Fzin
          by(auto)

        have Fzin' : "fz \<in> set [fz]" by simp

        have Fz_sup : "is_sup (scross ((\<lambda>f. f syn) ` set [fz]) Xs) (pcomps [fz] syn sup1)"
          using sups_pres_pcomps_gen'[OF PresX Fzin' Hfin_Xs Hnemp_Xs HXs_S H' H'_in] 
          by simp

        have Uncross : "(scross ((\<lambda>f. f syn) ` set [fz]) Xs) = (fz syn) ` Xs"
          using scross_singleton1[of "fz syn" Xs] unfolding scross_def by auto

        have Fz_sup' : "is_sup ((fz syn) ` Xs) (pcomps [fz] syn sup1)"
          using Fz_sup unfolding Uncross by simp

        have Fz_leq1: "fz syn z <[ (pcomps [fz] syn sup1)"
          using is_supD1[OF Fz_sup', of "fz syn z"] Zin
          by blast

        have Zin' : "z \<in> S syn"
          using Zin HXs_S by auto

        have Fz_sup'' : "is_sup ((\<lambda>f. f syn z) ` set l1) (pcomps l1 syn z)"
          using sups_pres_pcomps_gen'[OF Pres1 Fzin, of "{z}" z syn z] sup_singleton[of z] Fzin Zin'
          unfolding scross_singleton2 image_comp
          by(auto)

        have Fz_leq2 : "(pcomps [fz] syn z) <[ pcomps l1 syn z"
          using is_supD1[OF Fz_sup'', of "fz syn z"]  Fzin
          by auto

        have Leq_final1 : "fz syn z <[ pcomps l1 syn z"
          using Fz_leq2 unfolding pcomps.simps by auto

        have Leq_final2 : "pcomps l1 syn z <[ y'"
          using is_ubE[OF Y', of "pcomps l1 syn z"] Zin
          by auto

        show "z' <[ y'" 
          using leq_trans[OF Leq_final1 Leq_final2] unfolding Cross by simp
      qed

      show "pcomps l1 syn sup1 <[ y'"
        using is_supD2[OF Sup1 Ub'] by simp
    qed

    show ?thesis using C1 C2 L1' Sup1_in by auto
  next
    case L2

    have C1 : "is_sup ((\<lambda>f. f syn sup1) ` Fs_sub) (pcomps l2 syn sup1)"
      using sup_singleton unfolding L2 by auto

    have Pcomps_singleton : "(\<lambda>f. f syn) ` {pcomps l2} = {pcomps l2 syn}"
      by auto

    have L2' : "(scross ((\<lambda>f. f syn) ` Fs_sub) Xs) = pcomps l2 syn ` Xs"
      unfolding L2 Pcomps_singleton scross_singleton1 by simp

    have C2 : "is_sup ((pcomps l2 syn) ` Xs) (pcomps l2 syn sup1)"
    proof(rule is_supI)
      fix y
      assume Y: "y \<in> pcomps l2 syn ` Xs"

      then obtain x where Xin : "x \<in> Xs" and Xy : "pcomps l2 syn x = y"
        by blast

      have Xin' : "x \<in> S syn" using HXs_S Xin by auto

      have Leq1 : "x <[ sup1" using is_supD1[OF H' Xin] by simp

      show "y <[ pcomps l2 syn sup1"
        using pcomps_mono[OF Pres2 F2 Xin' H'_in Leq1] unfolding sym[OF Xy] by simp
    next
      fix y'

      assume Y' : "is_ub (pcomps l2 syn ` Xs) y'"

      have Ub' : "is_ub (scross ((\<lambda>f. f syn) ` set l2) Xs) y'"
      proof
        fix z'
        assume Z': "z' \<in> scross ((\<lambda>f. f syn) ` set l2) Xs"

        obtain fz z where Zin : "z \<in> Xs" and Fzin : "fz \<in> set l2" and Cross : "z' = fz syn z"
          using Z' unfolding scross_def by blast

        have Leq1 : "z <[ sup1" using is_supD1[OF H' Zin] by simp

        have PresX : "sups_pres (set [fz]) S"
          using sups_pres_subset[OF Pres2, of "set [fz]"] Fzin
          by(auto)

        have Fzin' : "fz \<in> set [fz]" by simp

        have Fz_sup : "is_sup (scross ((\<lambda>f. f syn) ` set [fz]) Xs) (pcomps [fz] syn sup1)"
            using sups_pres_pcomps_gen'[OF PresX Fzin' Hfin_Xs Hnemp_Xs HXs_S H' H'_in] 
          by simp

        have Uncross : "(scross ((\<lambda>f. f syn) ` set [fz]) Xs) = (fz syn) ` Xs"
          using scross_singleton1[of "fz syn" Xs] unfolding scross_def by auto

        have Fz_sup' : "is_sup ((fz syn) ` Xs) (pcomps [fz] syn sup1)"
          using Fz_sup unfolding Uncross by simp

        have Fz_leq1: "fz syn z <[ (pcomps [fz] syn sup1)"
          using is_supD1[OF Fz_sup', of "fz syn z"] Zin
          by blast

        have Zin' : "z \<in> S syn"
          using Zin HXs_S by auto

        have Fz_sup'' : "is_sup ((\<lambda>f. f syn z) ` set l2) (pcomps l2 syn z)"
          using sups_pres_pcomps_gen'[OF Pres2 Fzin, of "{z}" z syn z] sup_singleton[of z] Fzin Zin'
          unfolding scross_singleton2 image_comp
          by(auto)

        have Fz_leq2 : "(pcomps [fz] syn z) <[ pcomps l2 syn z"
          using is_supD1[OF Fz_sup'', of "fz syn z"]  Fzin
          by auto

        have Leq_final1 : "fz syn z <[ pcomps l2 syn z"
          using Fz_leq2 unfolding pcomps.simps by auto

        have Leq_final2 : "pcomps l2 syn z <[ y'"
          using is_ubE[OF Y', of "pcomps l2 syn z"] Zin
          by auto

        show "z' <[ y'" 
          using leq_trans[OF Leq_final1 Leq_final2] unfolding Cross by simp
      qed

      show "pcomps l2 syn sup1 <[ y'"
        using is_supD2[OF Sup2 Ub'] by simp
    qed

    show ?thesis using C1 C2 L2' Sup2_in by auto
  next
    case L1_2

    have C1 : "is_sup ((\<lambda>f. f syn sup1) ` Fs_sub) (pcomps (l1 @ l2) syn sup1)"
      using Sup12 unfolding L1_2 by auto

    have Pcomps_duo : "(\<lambda>f. f syn) ` {pcomps l1, pcomps l2} = {pcomps l1 syn, pcomps l2 syn}"
      by auto

    have Pcomps_duo' : "scross ((\<lambda>f. f syn) ` {pcomps l1, pcomps l2}) Xs = 
      (pcomps l1 syn ` Xs \<union> pcomps l2 syn ` Xs)"
      unfolding Pcomps_duo scross_def
      by blast

    have C2 : "is_sup (pcomps l1 syn ` Xs \<union> pcomps l2 syn ` Xs) (pcomps (l1 @ l2) syn sup1)"
    proof(rule is_supI)
      fix y
      assume Y: "y \<in> pcomps l1 syn ` Xs \<union> pcomps l2 syn ` Xs"

      consider (Y1) x where "x \<in> Xs" and "pcomps l1 syn x = y" |
               (Y2) x where "x \<in> Xs" and "pcomps l2 syn x = y"
        using Y by blast

      then show "y <[ pcomps (l1 @ l2) syn sup1"
      proof cases
        case Y1
        have Leq1 : "x <[ sup1" using is_supD1[OF H' Y1(1)] by simp

        have Xin : "x \<in> S syn"
          using Y1 HXs_S by auto

        have Leq2 : "pcomps (l1 @ l2) syn x <[ pcomps (l1 @ l2) syn sup1"
          using pcomps_mono[OF Pres' Nemp' Xin H'_in Leq1] by simp

        have Xsup :"is_sup (scross ((\<lambda>f. f syn) ` set (l1 @ l2)) {x}) (pcomps (l1 @ l2) syn x)"
          using sups_pres_pcomps_gen'[OF Pres' Nemp' _ _ _ sup_singleton[of "x"], of x syn] Xin
          by simp

        have Subset : "scross ((\<lambda>f. f syn) ` set l1) {x} \<subseteq> scross ((\<lambda>f. f syn) ` set (l1 @ l2)) {x}"
          using scross_subset[of "(\<lambda>f. f syn) ` set (l1)" "(\<lambda>f. f syn) ` set (l1 @ l2)" "{x}" "{x}"]
          by auto

        have Xub : "is_ub (scross ((\<lambda>f. f syn) ` set (l1)) {x}) (pcomps (l1 @ l2) syn x)"
          using sup_subset_ub[OF Xsup Subset] by simp

        have Xsup_ub : "is_sup (scross ((\<lambda>f. f syn) ` set (l1)) {x}) (pcomps l1 syn x)"
          using sups_pres_pcomps_gen'[OF Pres1 F1 _ _ _ sup_singleton[of "x"], of x syn] Xin
          by simp

        have Leq3 : "pcomps l1 syn x <[ pcomps (l1 @ l2) syn x"
          using is_supD2[OF Xsup_ub Xub] by simp            

        show "y <[ pcomps (l1 @ l2) syn sup1"
          using leq_trans[OF Leq3 Leq2] Y1(2)
          by simp
      next
        case Y2

        have Leq1 : "x <[ sup1" using is_supD1[OF H' Y2(1)] by simp

        have Xin : "x \<in> S syn"
          using Y2 HXs_S by auto

        have Leq2 : "pcomps (l1 @ l2) syn x <[ pcomps (l1 @ l2) syn sup1"
          using pcomps_mono[OF Pres' Nemp' Xin H'_in Leq1] by simp

        have Xsup :"is_sup (scross ((\<lambda>f. f syn) ` set (l1 @ l2)) {x}) (pcomps (l1 @ l2) syn x)"
          using sups_pres_pcomps_gen'[OF Pres' Nemp' _ _ _ sup_singleton[of "x"], of x syn] Xin
          by simp

        have Subset : "scross ((\<lambda>f. f syn) ` set l2) {x} \<subseteq> scross ((\<lambda>f. f syn) ` set (l1 @ l2)) {x}"
          using scross_subset[of "(\<lambda>f. f syn) ` set (l2)" "(\<lambda>f. f syn) ` set (l1 @ l2)" "{x}" "{x}"]
          by auto

        have Xub : "is_ub (scross ((\<lambda>f. f syn) ` set (l2)) {x}) (pcomps (l1 @ l2) syn x)"
          using sup_subset_ub[OF Xsup Subset] by simp

        have Xsup_ub : "is_sup (scross ((\<lambda>f. f syn) ` set (l2)) {x}) (pcomps l2 syn x)"
          using sups_pres_pcomps_gen'[OF Pres2 F2 _ _ _ sup_singleton[of "x"], of x syn] Xin
          by simp

        have Leq3 : "pcomps l2 syn x <[ pcomps (l1 @ l2) syn x"
          using is_supD2[OF Xsup_ub Xub] by simp            

        show "y <[ pcomps (l1 @ l2) syn sup1"
          using leq_trans[OF Leq3 Leq2] Y2(2)
          by simp
      qed
    next

      fix y'
      assume Y' : "is_ub (pcomps l1 syn ` Xs \<union> pcomps l2 syn ` Xs) y'"

      have Ub' : "is_ub (scross ((\<lambda>f. f syn) ` set l1) Xs \<union> scross ((\<lambda>f. f syn) ` set l2) Xs) y'"
      proof
        fix z'
        assume Z': "z' \<in> scross ((\<lambda>f. f syn) ` set l1) Xs \<union>
             scross ((\<lambda>f. f syn) ` set l2) Xs"

        consider (Z1) "z' \<in> scross ((\<lambda>f. f syn) ` set l1) Xs" |
                 (Z2) "z' \<in> scross ((\<lambda>f. f syn) ` set l2) Xs"
          using Z' by auto

        then show "z' <[ y'"
        proof cases
          case Z1

          obtain fz z where Zin : "z \<in> Xs" and Fzin : "fz \<in> set l1" and Cross : "z' = fz syn z"
            using Z1 unfolding scross_def by blast
  
          have Leq1 : "z <[ sup1" using is_supD1[OF H' Zin] by simp
  
          have PresX : "sups_pres (set [fz]) S"
            using sups_pres_subset[OF Pres1, of "set [fz]"] Fzin
            by(auto)
  
          have Fzin' : "fz \<in> set [fz]" by simp
  
          have Fz_sup : "is_sup (scross ((\<lambda>f. f syn) ` set [fz]) Xs) (pcomps [fz] syn sup1)"
            using sups_pres_pcomps_gen'[OF PresX Fzin' Hfin_Xs Hnemp_Xs HXs_S H' H'_in]  
            by simp
  
          have Uncross : "(scross ((\<lambda>f. f syn) ` set [fz]) Xs) = (fz syn) ` Xs"
            using scross_singleton1[of "fz syn" Xs] unfolding scross_def by auto
  
          have Fz_sup' : "is_sup ((fz syn) ` Xs) (pcomps [fz] syn sup1)"
            using Fz_sup unfolding Uncross by simp
  
          have Fz_leq1: "fz syn z <[ (pcomps [fz] syn sup1)"
            using is_supD1[OF Fz_sup', of "fz syn z"] Zin
            by blast

          have Zin_S : "z \<in> S syn"
            using HXs_S Zin by auto
  
          have Fz_sup'' : "is_sup ((\<lambda>f. f syn z) ` set l1) (pcomps l1 syn z)"
            using sups_pres_pcomps_gen'[OF Pres1 Fzin _ _ _ sup_singleton[of z] Zin_S, of z] Fzin Zin_S
            unfolding scross_singleton2 image_comp
            by(auto)
  
          have Fz_leq2 : "(pcomps [fz] syn z) <[ pcomps l1 syn z"
            using is_supD1[OF Fz_sup'', of "fz syn z"]  Fzin
            by auto
  
          have TestX : "fz syn z <[ pcomps l1 syn z"
            using Fz_leq2 unfolding pcomps.simps by auto
  
          have Test2X : "pcomps l1 syn z <[ y'"
            using is_ubE[OF Y', of "pcomps l1 syn z"] Zin
            by auto
  
          show "z' <[ y'" 
            using leq_trans[OF TestX Test2X] unfolding Cross by simp
        next

          case Z2

          obtain fz z where Zin : "z \<in> Xs" and Fzin : "fz \<in> set l2" and Cross : "z' = fz syn z"
            using Z2 unfolding scross_def by blast
  
          have Leq1 : "z <[ sup1" using is_supD1[OF H' Zin] by simp
  
          have PresX : "sups_pres (set [fz]) S"
            using sups_pres_subset[OF Pres2, of "set [fz]"] Fzin
            by(auto)
  
          have Fzin' : "fz \<in> set [fz]" by simp

          have Zin_S : "z \<in> S syn"
            using HXs_S Zin by auto
  

          have Fz_sup : "is_sup (scross ((\<lambda>f. f syn) ` set [fz]) Xs) (pcomps [fz] syn sup1)"
            using sups_pres_pcomps_gen'[OF PresX Fzin' Hfin_Xs Hnemp_Xs HXs_S H' H'_in] 
            by simp
  
          have Uncross : "(scross ((\<lambda>f. f syn) ` set [fz]) Xs) = (fz syn) ` Xs"
            using scross_singleton1[of "fz syn" Xs] unfolding scross_def by auto
  
          have Fz_sup' : "is_sup ((fz syn) ` Xs) (pcomps [fz] syn sup1)"
            using Fz_sup unfolding Uncross by simp
  
          have Fz_leq1: "fz syn z <[ (pcomps [fz] syn sup1)"
            using is_supD1[OF Fz_sup', of "fz syn z"] Zin
            by blast
  
          have Fz_sup'' : "is_sup ((\<lambda>f. f syn z) ` set l2) (pcomps l2 syn z)"
            using sups_pres_pcomps_gen'[OF Pres2 Fzin _ _ _ sup_singleton[of z] Zin_S, of z] Fzin Zin_S
            unfolding scross_singleton2 image_comp
            by(auto)
  
          have Fz_leq2 : "(pcomps [fz] syn z) <[ pcomps l2 syn z"
            using is_supD1[OF Fz_sup'', of "fz syn z"]  Fzin
            by auto
  
          have Leq_final1 : "fz syn z <[ pcomps l2 syn z"
            using Fz_leq2 unfolding pcomps.simps by auto
  
          have Leq_final2 : "pcomps l2 syn z <[ y'"
            using is_ubE[OF Y', of "pcomps l2 syn z"] Zin
            by auto
  
          show "z' <[ y'" 
            using leq_trans[OF Leq_final1 Leq_final2] unfolding Cross by simp
        qed
      qed

      show "pcomps (l1 @ l2) syn sup1 <[ y'"
        using is_supD2[OF Sup_alt Ub'] by simp
    qed

    have L1_2' : "(pcomps l1 syn ` Xs \<union> pcomps l2 syn ` Xs) = (scross ((\<lambda>f. f syn) ` {pcomps l1, pcomps l2}) Xs)" 
      unfolding scross_def
      by auto

  (* finally, show membership in S *)
    obtain f_arb where F_arb : "f_arb \<in> set (l1 @ l2)"
      using Hnemp1 Hnemp2
      by(cases l1; cases l2; auto)

    have Conc_In :
      "(pcomps (l1 @ l2) syn sup1) \<in> S syn"
      using sups_pres_pcomps_gen'[OF Pres' F_arb Hfin_Xs Hnemp_Xs HXs_S H' H'_in]
      by simp
  
    show ?thesis using C1 C2 Conc_In unfolding L1_2' L1_2 Conc_In by blast
  qed
qed

lemma pcomps_comm : 
  assumes H : "sups_pres (set l1 \<union> set l2) S"
  assumes Nemp1 : "l1 \<noteq> []"
  assumes Nemp2 : "l2 \<noteq> []"
  assumes Hx : "x \<in> S syn"
  shows "pcomps (l1 @ l2) syn x = pcomps (l2 @ l1) syn x" 
proof-

  have Assoc: "pcomps (l1 @ l2) syn x = pcomps [pcomps l1, pcomps l2] syn x"
    using pcomps_assoc[OF H Nemp1 Nemp2 Hx] by auto

  have H_alt : "sups_pres (set (l1 @ l2)) S"
    using H by auto

  have Pres' : "sups_pres {pcomps l1, pcomps l2} S"
    using sups_pres_pcomps_fuse[OF H Nemp1 Nemp2] by simp

  have Comm : "pcomps [pcomps l1, pcomps l2] syn x = pcomps [pcomps l2, pcomps l1] syn x"
    using pcomps_comm'[OF Pres' Hx] by auto

  have Pres'' : "sups_pres (set l2 \<union> set l1) S" 
    using H unfolding Un_commute[of "set l1" "set l2"] by simp

  have Conc' : "pcomps [pcomps l2, pcomps l1] syn x = pcomps (l2 @ l1) syn x"
    using pcomps_assoc[OF Pres'' Nemp2 Nemp1 Hx] by auto

  show "pcomps (l1 @ l2) syn x = pcomps (l2 @ l1) syn x"
    using Assoc Comm Conc' by simp
qed

lemma pcomps_set_eq1 :
  assumes H : "sups_pres Fs S"
  assumes Hf : "f \<in> Fs"
  assumes Hl1 : "set l1 = Fs"
  assumes Hx : "x \<in> S syn"
  shows "pcomps (f # l1) syn x = pcomps l1 syn x"
  using assms
proof(induction l1 arbitrary: f Fs)
  case Nil
  then show ?case by auto
next
  case (Cons l1h l1t)

  show ?case
  proof(cases l1t)
    case Nil' : Nil

    then have L1h_eq : "l1h = f"
      using Cons.prems by auto

    then show ?thesis
      using bsup_idem 
      unfolding L1h_eq Nil' pcomps.simps
      by auto
  next
    case Cons' : (Cons l2h l2t)

    have S_eq : "(set [f, l1h] \<union> set l1t) = Fs"
      using Cons.prems Cons'
      by(auto)

    have Pres' : "sups_pres (set [f, l1h] \<union> set l1t) S"
      using Cons.prems(1) unfolding S_eq by simp

    have Assoc : "pcomps (f # l1h # l1t) syn x = pcomps [pcomps [f, l1h], pcomps l1t] syn x"
      using pcomps_assoc[OF Pres' _ _ Hx] Cons' H
      by auto

    have Pres_h : "sups_pres {f, l1h} S"
      using sups_pres_subset[OF Cons.prems(1), of "{f, l1h}" f] Cons.prems
      by(auto)
      
    have Comm : "pcomps [f, l1h] syn x = pcomps [l1h, f] syn x"
      using pcomps_comm'[OF Pres_h Hx] by simp

    have S_eq' : "(set [l1h, f] \<union> set l1t) = Fs"
      using Cons.prems Cons'
      by(auto)

    have Pres'' : "sups_pres (set [l1h, f] \<union> set l1t) S"
      using Cons.prems(1) unfolding S_eq' by simp

    have Assoc' : "pcomps [pcomps [l1h, f], pcomps l1t] syn x = pcomps (l1h#f#l1t) syn x"
      using sym[OF pcomps_assoc[OF Pres'' _ _ Hx]] Cons' by auto

    have Rewritten1 :
      "pcomps (f # l1h # l1t) syn x = pcomps [pcomps [l1h, f], pcomps l1t] syn x"
      using Assoc Comm Assoc'
      by auto

    have Pres''' : "sups_pres (set [f] \<union> set l1t) S"
      using sups_pres_subset[OF Pres', of "set [f] \<union> set l1t" ]
      by(auto)

    have Rewritten2 :
      "pcomps (f # l1h # l1t) syn x = pcomps (l1h#f#l1t) syn x"
      unfolding Rewritten1 Assoc' by simp

    show ?thesis
    proof(cases "f = l1h")
      case True

      have Eq : "pcomps [l1h, f] = pcomps [f]" unfolding True pcomps.simps
        using bsup_idem
        by blast

      have Conc' :
        "pcomps [pcomps [f], pcomps l1t] syn x = pcomps (f # l1t) syn x"
        using pcomps_assoc[OF Pres'''] Cons' by auto

      then show ?thesis using True unfolding Rewritten1 Eq
        by auto
    next
      case False

      then have F_in_t : "f \<in> set l1t"
        using Cons.prems
        by auto

      have Pres_t : "sups_pres (set l1t) S"
        using sups_pres_subset[OF Cons.prems(1) _ _ F_in_t] Cons.prems
        by auto

      have IH_spec : "pcomps (f # l1t) syn x = pcomps l1t syn x"
        using Cons.IH[OF Pres_t F_in_t _ Hx] 
        by auto

      show ?thesis using F_in_t unfolding Rewritten2 unfolding pcomps.simps unfolding IH_spec
        by(cases l1t; auto)
    qed
  qed
qed

lemma pcomps_singleton :
  assumes Pres : "sups_pres {f} S"
  assumes H : "set l = {f}"
  assumes Hx : "x \<in> S syn"
  shows "pcomps l syn x = f syn x" using assms
proof(induction l arbitrary: f)
  case Nil
  then show ?case by auto
next
  case (Cons l1h l1t)

  then have L1h : "l1h = f" by auto

  show ?case
  proof(cases l1t)
    case Nil' : Nil

    then show ?thesis using L1h Cons
      by auto
  next

    case Cons' : (Cons l2h l2t)

    have L1t : "set l1t = {f}"
      using Cons Cons'
      by auto

    have Conc' : "pcomps (f # l1t) syn x = pcomps l1t syn x"
      using pcomps_set_eq1[OF Cons.prems(1) _ L1t Hx]
      by(auto)

    then show ?thesis using Cons.IH[OF Cons.prems(1) L1t Hx]
      unfolding L1h
      by auto
  qed
qed

lemma pcomps_swap :
  assumes H : "sups_pres (set (f1 # f2 # l1)) S"
  assumes Hx : "x \<in> S syn"
  shows "pcomps (f1 # f2 # l1) syn x = pcomps (f2 # f1 # l1) syn x"
proof(cases l1)
  case Nil

  have Pres' : "sups_pres {f1, f2} S"
    using sups_pres_subset[OF H, of "{f1, f2}" f1]
    by auto

  have Comm: "pcomps [f1, f2] syn x = pcomps [f2, f1] syn x"
    using pcomps_comm'[OF Pres' Hx]
    by simp

  then show ?thesis using Nil
    by auto
next
  case (Cons l1h l1t)

  have Pres' : "sups_pres {f1, f2} S"
    using sups_pres_subset[OF H, of "{f1, f2}" f1]
    by auto

  have Eq1: "set (f1 # f2 # l1) = (set [f1, f2] \<union> set (l1))"
    by auto

  then have Assoc1 : "pcomps ([f1, f2] @ l1) syn x = pcomps [pcomps [f1, f2], pcomps (l1)] syn x"
    using pcomps_assoc[of "[f1, f2]" "l1"] H Cons Hx
    by(auto)

  have Comm: "pcomps [f1, f2] syn x = pcomps [f2, f1] syn x"
    using pcomps_comm'[OF Pres' Hx]
    by simp

  have Set_comm : "set (f2 # f1 # l1) = set (f1 # f2 # l1)"
    by auto

  have H' : "sups_pres (set (f2 # f1 # l1)) S"
    using H unfolding Set_comm
    by auto

  have Eq2: "set (f2 # f1 # l1) = (set [f2, f1] \<union> set (l1))"
    by auto
    
  then have Assoc2 : "pcomps ([f2, f1] @ l1) syn x = pcomps [pcomps [f2, f1], pcomps l1] syn x"
    using pcomps_assoc[of "[f2, f1]" "l1"] H' Cons Hx
    by(auto)

  show ?thesis using Assoc1 Assoc2 Comm
    by(auto)
qed

lemma pcomps_removeAll' :
  assumes H : "sups_pres Fs S"
  assumes Hf : "f \<in> Fs"
  assumes Hl1 : "set l1 = Fs"
  assumes Hx : "x \<in> S syn"
  shows "pcomps (f # l1) syn x = pcomps (f # (removeAll f l1)) syn x"
  using assms
proof(induction l1 arbitrary: f Fs)
  case Nil
  then show ?case by auto
next
  case (Cons l1h l1t)

  show ?case
  proof(cases l1t)
    case Nil' : Nil
    show ?thesis
    proof(cases "f = l1h")
      case True

      have Conc' : "(\<lambda>a b. [^ l1h a b, l1h a b ^]) = l1h"
      proof(rule ext; rule ext)
        fix a b

        show "[^ l1h a b, l1h a b ^] = l1h a b"
          using bsup_idem[of "l1h a b"] by simp
      qed

      hence Conc'' : "[^ l1h syn x, l1h syn x ^] = l1h syn x"
        using fun_cong[OF fun_cong[OF Conc']] by auto

      show ?thesis using Cons.prems Nil' Conc''
        by simp
    next
      case False
      then show ?thesis using Cons Nil'
        by(simp)
    qed
  next
    case Cons' : (Cons l1h2 l1t2)

    have Pres' : "sups_pres (set l1t) S"
      using sups_pres_subset[OF Cons.prems(1) _, of "set l1t" l1h2]
        Cons.prems
      unfolding  Cons'
      by auto

    show ?thesis
    proof(cases "f \<in> set l1t")
      case True

      show ?thesis
      proof(cases "f = l1h")
        case True' : True

        have IndHyp : "pcomps (f # l1t) syn x = pcomps (f # removeAll f l1t) syn x"
          using Cons.IH[OF Pres' True] Cons.prems
          by simp

        show ?thesis
          using pcomps_cons_same[of l1h l1t] IndHyp True'
          by(auto)
      next
        case False' : False


        have Pres1 : "sups_pres (set (f # l1h # l1t)) S"
          using sups_pres_subset[OF Cons.prems(1), of "set (f # l1h # l1t)" f] Cons' Cons.prems
          by auto

        have Swap: "pcomps (f # l1h # l1t) syn x = pcomps (l1h # f # l1t) syn x"
          using pcomps_swap[OF Pres1] Cons.prems
          by simp

        have IndHyp : "pcomps (f # l1t) syn x = pcomps (f # removeAll f l1t) syn x"
          using Cons.IH[OF Pres' True] Cons.prems
          by simp

        have Subset2 : "set (f # l1h # removeAll f l1t) \<subseteq> Fs"
          using Cons.prems Cons' False'
          by(auto)

        have Pres2 : "sups_pres (set (f # l1h # removeAll f l1t)) S"
          using sups_pres_subset[OF Cons.prems(1) _ Subset2, of f] Cons.prems
          by auto

        have SetEq : "set (l1h # f # removeAll f l1t) = set (f # l1h # removeAll f l1t)"
          by auto

        then have Pres2' : "sups_pres (set (l1h # f # removeAll f l1t)) S"
          using Pres2 by auto

        have SetEq' : "set (l1h # f # removeAll f l1t) = (set [l1h] \<union> set (f # removeAll f l1t))"
          by auto

        then have Pres2'' : "sups_pres (set [l1h] \<union> set (f # removeAll f l1t)) S"
          using Pres2' by auto

        have Swap' : "pcomps (f # l1h # removeAll f l1t) syn x = pcomps (l1h#f#removeAll f l1t) syn x"
          using pcomps_swap[OF Pres2] Cons.prems by simp

        have Assoc1 : "pcomps (l1h # f # l1t) syn x = pcomps [pcomps [l1h], pcomps (f#l1t)] syn x"
          using pcomps_assoc[of "[l1h]" "f#l1t" S x syn] Pres1 Cons.prems
          by auto

        have Assoc2 : "pcomps (l1h#f#removeAll f l1t) syn x = pcomps [pcomps [l1h], pcomps (f# removeAll f l1t)] syn x"
          using pcomps_assoc[of "[l1h]" "f#removeAll f l1t"] Pres2''
          by auto

        show ?thesis
          using Swap Assoc1 Swap' Assoc2 IndHyp False'
          by(auto)
      qed
    next
      case False

      show ?thesis
      proof(cases "f = l1h")
        case True' : True

        show ?thesis using False True' pcomps_cons_same[of l1h l1t]
          by(auto)

      next
        case False' : False

        have Noop : "removeAll f (l1h # l1t) = l1h # l1t"
          using False  False'
          by auto

        show ?thesis using Noop by simp
      qed
    qed
  qed
qed

lemma pcomps_removeAll :
  assumes H : "sups_pres Fs S"
  assumes Hf : "f \<in> Fs"
  assumes Hl1 : "set l1 = Fs"
  assumes Hx : "x \<in> S syn"
  shows "pcomps (l1) syn x = pcomps (f # (removeAll f l1)) syn x"
  using pcomps_set_eq1[OF H Hf Hl1 Hx]
    pcomps_removeAll'[OF H Hf Hl1 Hx]
  by auto

lemma pcomps_set_eq :
  assumes H : "sups_pres Fs S"
  assumes Hf : "f \<in> Fs"
  assumes Hl1 : "set l1 = Fs"
  assumes Hl2 : "set l2 = Fs"
  assumes Hx : "x \<in> S syn"
  shows "pcomps l1 syn x = pcomps l2 syn x"
  using assms
proof(induction l1 arbitrary: Fs f l2)
  case Nil1_1 : Nil
  then show ?case 
    by(cases l2; auto)
next
  case Cons1_1 : (Cons l1h1 l1t1)

  show ?case
  proof(cases l1t1)
    case Nil1_2 : Nil

    show ?thesis
    proof(cases l2)
      case Nil2_1 : Nil
      then show ?thesis 
        using Cons1_1 Nil1_2
        by(auto)
    next
      case Cons2_1 : (Cons l2h1 l2t)

      then have L2 : "set l2 = {l1h1}"
        using Cons1_1.prems Nil1_2
        by(auto)

      have L1h1_pres : "sups_pres {l1h1} S"
        using sups_pres_subset[OF Cons1_1.prems(1), of "{l1h1}" l1h1] Cons1_1.prems
        by auto

      have L2_eq : "pcomps l2 syn x = l1h1 syn x"
        using pcomps_singleton[OF L1h1_pres L2] Cons1_1.prems
        by simp

      then show ?thesis
        unfolding L2_eq Nil1_2
        by simp
    qed
  next

    case Cons1_2 : (Cons l1h2 l1t2)
    show ?thesis
    proof(cases l2)
      case Nil2_1 : Nil
      then show ?thesis 
        using Cons1_2 Cons1_1.prems
        by(auto)
    next
      case Cons2_1 : (Cons l2h1 l2t)

      have Pres' : "sups_pres (set (l1h2 # l1t2)) S"
        using sups_pres_subset[OF Cons1_1.prems(1), of "set (l1h2 # l1t2)" l1h2]
          Cons1_1.prems(3)
        unfolding Cons1_2
        by(auto)

      show ?thesis
      proof(cases "l1h1 \<in> set l1t1")
        case True

        hence True' : "pcomps l1t1 syn x = pcomps (l1h1#l1t1) syn x"
          using pcomps_set_eq1[OF Pres', of l1h1 "(l1h2#l1t2)"] Cons1_1.prems
          unfolding Cons1_2 by auto

        have Set : "set l1t1 = Fs"
          using True Cons1_1.prems unfolding Cons1_2
          by auto

        then show ?thesis using Cons1_1.IH[OF Cons1_1.prems(1) Cons1_1.prems(2) Set Cons1_1.prems(4)] Cons1_1.prems
          unfolding True'
          by simp
      next
        case False

        have Removed : "pcomps l2 syn x = pcomps (l1h1 # removeAll l1h1 l2) syn x" 
          using pcomps_removeAll[of "set l2" "S" "l1h1" "l2"]
            Cons1_1.prems Cons2_1
          by auto

        have Set_eq : "set (removeAll l1h1 l2) = set l1t1"
          using False Cons1_1.prems
          by auto

        have Ind_hyp : "pcomps l1t1 syn x = pcomps (removeAll l1h1 l2) syn x"
          using Cons1_1.IH[OF _ _ _ Set_eq] Pres' Cons1_2 Cons1_1.prems
          by auto

        have Eq1 : "set (l1h1 # l1t1) = set [l1h1] \<union> set l1t1"
          by auto

        have Pres1 : "sups_pres (set [l1h1] \<union> set l1t1) S"
          using Cons1_1.prems Eq1
          by auto

        have Assoc1 : "pcomps (l1h1 # l1t1) syn x = pcomps [ pcomps [l1h1], pcomps l1t1] syn x"
          using pcomps_assoc[OF Pres1] Cons1_2
          by auto

        have Eq2 : "set (l1h1 # removeAll l1h1 l2) = set [l1h1] \<union> set (removeAll l1h1 l2)"
          by auto

        have Pres2 : "sups_pres (set [l1h1] \<union> set (removeAll l1h1 l2)) S"
          using Cons1_1.prems Eq1
          by auto

        show ?thesis
        proof(cases "set l1t1 = {l1h1}")
          case True' : True

          then have False using False by auto

          then show ?thesis by auto
        next
          case False' : False

          then obtain new where New_set : "new \<in> set l1t1" and New_noteq : "new \<noteq> l1h1"
            using Cons1_2
            by auto

          have New_set' : "new \<in> set l2" using Cons1_1.prems New_set
            by auto

          have New_in_2 : "new \<in> set (removeAll l1h1 l2)"
            using Cons1_1.prems New_set' New_noteq set_removeAll[of l1h1 l2]
            by auto

          then have Not_empty2 : "removeAll l1h1 l2 \<noteq> []"
            by(cases "removeAll l1h1 l2"; auto)

          have Assoc2 : "pcomps (l1h1 # removeAll l1h1 l2) syn x = pcomps [ pcomps [l1h1], pcomps (removeAll l1h1 l2)] syn x"
            using pcomps_assoc[OF Pres2 _ Not_empty2] Cons1_1.prems
            by auto
  
          show ?thesis using Ind_hyp Removed Assoc1 Assoc2
            by(auto)
        qed
      qed
    qed
  qed
qed
end