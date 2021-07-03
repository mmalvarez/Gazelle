theory LangCompSimple imports LiftUtils LangComp
begin

(* Simplification of langcomp.
   Instead of showing semantics preserve LUBs,
   we show that the already-lifted semantics have LUB, if the
   starting states are equal (stronger than just having LUB) *)

(* TODO: how does sup_l fit into this?
   the reason i thought we needed the (stronger) statement
   that LUBs are preserved (rather than
   just "inputs are equal \<Rightarrow> outputs have LUBs) was that
   it seemed like you needed this to be able to relate
   the Base elements of liftings
*)

type_synonym ('a, 'b) langcomps =
  "('a \<Rightarrow> 'b \<Rightarrow> 'b) list"

(* idea: commutativity should mean that the ordering of composition doesn't matter *)
(*
fun pcomps :: "('a, 'b :: Mergeable) langcomps \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'b)" where
"pcomps [] a b = b"
| "pcomps [lh] a b = [^ lh a b, b ^]"
| "pcomps [l1, l2] a b =
  [^ [^ l1 a b, l2 a b ^], b^]"
| "pcomps (lh#lt) a b =
   [^ [^ lh a b, pcomps lt a b ^], b ^]"
*)

definition sups_pres :: "('a \<Rightarrow> ('b :: Mergeable) \<Rightarrow> 'b) set \<Rightarrow> bool" where
"sups_pres Fs =
  (\<forall> syn st .
    has_sup ( (\<lambda> f . f syn st) ` Fs))"

lemma sups_presD :
  assumes "sups_pres Fs"
  shows "has_sup ( (\<lambda> f . f syn st) ` Fs)" using assms by (auto simp add: sups_pres_def)

lemma sups_presI :
  assumes "\<And> syn st . has_sup ( (\<lambda> f . f syn st) ` Fs)"
  shows "sups_pres Fs" using assms by (auto simp add: sups_pres_def)

lemma sups_pres_subset :
  fixes Fs :: "('a \<Rightarrow> ('b :: Mergeable) \<Rightarrow> 'b) set"
  assumes H : "sups_pres Fs"
  assumes Hfin : "finite Fs"
  assumes Hsub : "Fs' \<subseteq> Fs"
  assumes Hnemp : "f \<in> Fs'"
  shows "sups_pres Fs'"
proof(rule sups_presI)
  fix syn st
  obtain Rest where Rest : "Fs' \<union> Rest = Fs" using Hsub by blast

  have Rfin : "finite Rest" using Rest Hfin by auto

(*
  have Fin' : "finite (Fsx' \<union> (\<lambda>x. (x, a)) ` Rest)" using Hfin' Rfin
    unfolding image_Un
    by(auto)

  hence Fin'' : "finite ((\<lambda>(f, y). f syn y) ` (Fsx' \<union> (\<lambda>x. (x, a)) ` Rest))" by auto
*)
  have Conc' : "has_sup ((\<lambda>f . f syn st) ` (Fs' \<union> Rest))" unfolding Rest
    using sups_presD[OF H] by auto

  then obtain supr where Supr :
    "is_sup ((\<lambda> f . f syn st) ` (Fs' \<union> Rest)) supr"
    by(auto simp add: has_sup_def)

  have Subset : "(\<lambda> f . f syn st) ` (Fs') \<subseteq> (\<lambda> f . f syn st) ` (Fs' \<union>  Rest)"
    unfolding image_comp by auto

  have Nemp : "(f syn st) \<in> (\<lambda> f . f syn st) ` Fs'"
    using Hnemp by auto

  show "has_sup ((\<lambda>f. f syn st) ` Fs')"
    using has_sup_subset[OF _ Supr Subset Nemp] Hfin unfolding Rest
    by auto
qed

lemma sups_pres_pair :
  assumes Hp : "sups_pres {x1, x2}"
  shows "has_sup {x1 syn state, x2 syn state}" using Hp
  unfolding sups_pres_def by auto

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
      have Eq3 : "(\<lambda>(f, y). f syn y) ` set (map (\<lambda>f. (f, sem)) (h1 # t1)) =
                  {h1 syn sem} \<union> (\<lambda>f. f syn sem) ` set t1" 
        by(auto)

      have Sing : "has_sup {sem}"
        using sup_singleton[of sem] by(auto simp add: has_sup_def)

      have "has_sup ((\<lambda> f. f syn sem) ` set  (h1 # t1))"
        using sups_presD[OF Cons.prems(1)] Sing
        by(auto)

      then obtain s where S: "is_sup ((\<lambda> f. f syn sem) ` set  (h1 # t1)) s"
        by(auto simp add: has_sup_def)

      have Union : "is_sup ({h1 syn sem} \<union> (\<lambda>f. f syn sem) ` set t1) s" using S unfolding Eq3
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


(* sup_l captures the idea that liftings "preserve" suprema*)

(* problem: suppose we have standard wrapping
   (md_prio wrapping option wrapping md_triv) (lifting A)
   inside of a pair (fst = standard wrapping, snd = say int option) (lifting B)

   then LBase of the fst lifting (lifting A) will be
   (mdp 0 \<bottom>, \<bottom>)

   LBase of the second will be (\<bottom>, \<bottom>)

   so we actually do need to be general over inputs
*)

end